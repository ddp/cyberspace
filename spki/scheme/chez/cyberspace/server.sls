;;; server.sls - HTTP status server for Cyberspace
;;;
;;; Simple HTTP server for status/metrics only.
;;; For REPL access, use SSH or native GUI app with PTY.
;;;
;;; Port: 4321 (default)
;;;
;;; Endpoints:
;;;   GET /           - Status page
;;;   GET /api/*      - JSON metrics (vault, keys, info)

(library (cyberspace server)
  (export
    start-server
    server-port
    server-host)

  (import (rnrs)
          (rnrs mutable-strings)
          (rnrs eval)
          (only (chezscheme)
                printf format fprintf with-output-to-string
                file-directory? directory-list
                current-directory getenv
                fork-thread sleep
                system open-process-ports
                make-time current-time time-second
                void sort)
          (cyberspace tcp)
          (cyberspace chicken-compatibility blob)
          (cyberspace chicken-compatibility chicken))

  ;; ============================================================
  ;; Configuration
  ;; ============================================================

  (define *server-port* 4321)
  (define *server-host* "127.0.0.1")
  (define *static-dir* #f)

  ;; R6RS can't export assigned variables
  (define (server-port) *server-port*)
  (define (server-host) *server-host*)

  ;; ============================================================
  ;; String Helpers
  ;; ============================================================

  (define (string-prefix? prefix str)
    (let ((plen (string-length prefix))
          (slen (string-length str)))
      (and (<= plen slen)
           (string=? prefix (substring str 0 plen)))))

  (define (string-suffix? suffix str)
    (let ((xlen (string-length suffix))
          (slen (string-length str)))
      (and (<= xlen slen)
           (string=? suffix (substring str (- slen xlen) slen)))))

  (define (string-contains haystack needle)
    (let ((nlen (string-length needle))
          (hlen (string-length haystack)))
      (let loop ((i 0))
        (cond
          ((> (+ i nlen) hlen) #f)
          ((string=? needle (substring haystack i (+ i nlen))) i)
          (else (loop (+ i 1)))))))

  (define (string-trim-both str)
    (let* ((len (string-length str))
           (start (let loop ((i 0))
                    (if (or (>= i len) (not (char-whitespace? (string-ref str i))))
                        i (loop (+ i 1)))))
           (end (let loop ((i (- len 1)))
                  (if (or (< i start) (not (char-whitespace? (string-ref str i))))
                      (+ i 1) (loop (- i 1))))))
      (substring str start end)))

  (define (pathname-extension path)
    (let ((len (string-length path)))
      (let loop ((i (- len 1)))
        (cond
          ((< i 0) #f)
          ((char=? (string-ref path i) #\.) (substring path (+ i 1) len))
          ((char=? (string-ref path i) #\/) #f)
          (else (loop (- i 1)))))))

  ;; ============================================================
  ;; MIME Types
  ;; ============================================================

  (define *mime-types*
    '(("html" . "text/html; charset=utf-8")
      ("css"  . "text/css; charset=utf-8")
      ("js"   . "application/javascript; charset=utf-8")
      ("json" . "application/json")
      ("png"  . "image/png")
      ("svg"  . "image/svg+xml")
      ("ico"  . "image/x-icon")
      ("woff2" . "font/woff2")))

  (define (get-mime-type path)
    (let* ((ext (pathname-extension path))
           (pair (and ext (assoc ext *mime-types*))))
      (if pair (cdr pair) "application/octet-stream")))

  ;; ============================================================
  ;; Binary Port Text I/O
  ;; ============================================================
  ;; Server uses binary ports throughout. These helpers read/write
  ;; text over binary ports for uniform I/O handling.

  (define (bin-get-line in)
    "Read a line from binary port, return string (without \\n). Strips \\r."
    (let loop ((acc '()))
      (let ((b (get-u8 in)))
        (cond
          ((eof-object? b)
           (if (null? acc) b (utf8->string (u8-list->bytevector (reverse acc)))))
          ((= b 10)  ; \n
           (utf8->string (u8-list->bytevector (reverse acc))))
          ((= b 13)  ; \r — skip, will be followed by \n
           (loop acc))
          (else (loop (cons b acc)))))))

  (define (bin-put-string out str)
    "Write a string to a binary port as UTF-8."
    (put-bytevector out (string->utf8 str)))

  (define (bin-flush out)
    (flush-output-port out))

  ;; ============================================================
  ;; HTTP Response Helpers
  ;; ============================================================

  (define (http-response out status headers body)
    (bin-put-string out (format #f "HTTP/1.1 ~a\r\n" status))
    (for-each (lambda (h)
                (bin-put-string out (format #f "~a: ~a\r\n" (car h) (cdr h))))
              headers)
    (bin-put-string out "\r\n")
    (when body
      (bin-put-string out body))
    (bin-flush out))

  (define (http-ok out content-type body)
    (http-response out "200 OK"
      `(("Content-Type" . ,content-type)
        ("Content-Length" . ,(string-length body))
        ("Cache-Control" . "no-cache")
        ("Connection" . "close"))
      body))

  (define (http-not-found out)
    (http-response out "404 Not Found"
      '(("Content-Type" . "text/plain")
        ("Connection" . "close"))
      "Not Found"))

  (define (http-error out msg)
    (http-response out "500 Internal Server Error"
      '(("Content-Type" . "text/plain")
        ("Connection" . "close"))
      msg))

  ;; ============================================================
  ;; HTTP Request Parser
  ;; ============================================================

  (define (parse-request-line line)
    (let ((sp1 (string-contains line " ")))
      (if sp1
          (let ((rest (substring line (+ sp1 1) (string-length line))))
            (let ((sp2 (string-contains rest " ")))
              (values (substring line 0 sp1)
                      (if sp2 (substring rest 0 sp2) rest))))
          (values #f #f))))

  (define (parse-headers in)
    (let loop ((headers '()))
      (let ((line (bin-get-line in)))
        (if (or (eof-object? line) (string=? line ""))
            (reverse headers)
            (let ((colon (string-contains line ":")))
              (if colon
                  (loop (cons (cons (string-downcase (string-trim-both (substring line 0 colon)))
                                    (string-trim-both (substring line (+ colon 1) (string-length line))))
                              headers))
                  (loop headers)))))))

  ;; ============================================================
  ;; Static File Serving
  ;; ============================================================

  (define (serve-static out path)
    (let ((file-path (string-append *static-dir* "/" path)))
      (if (and (file-exists? file-path)
               (not (file-directory? file-path)))
          (let ((content (call-with-input-file file-path
                           (lambda (p) (get-string-all p))))
                (mime (get-mime-type file-path)))
            (http-ok out mime content))
          (http-not-found out))))

  ;; ============================================================
  ;; API Endpoints
  ;; ============================================================

  (define (api-vault-list)
    (let ((dir ".vault/objects"))
      (if (and (file-exists? dir) (file-directory? dir))
          (let* ((files (filter (lambda (f) (not (string-prefix? "." f)))
                                (directory-list dir)))
                 (limited (if (> (length files) 100)
                              (let loop ((i 0) (fs files) (acc '()))
                                (if (or (null? fs) (>= i 100)) (reverse acc)
                                    (loop (+ i 1) (cdr fs) (cons (car fs) acc))))
                              files)))
            (format #f "{\"objects\":[~a]}"
                    (apply string-append
                      (let loop ((fs limited) (first #t))
                        (if (null? fs) '()
                            (cons (format #f "~a{\"hash\":\"~a\"}"
                                          (if first "" ",") (car fs))
                                  (loop (cdr fs) #f)))))))
          "{\"objects\":[]}")))

  (define (api-keys-list)
    (let ((dir ".vault/keys"))
      (if (and (file-exists? dir) (file-directory? dir))
          (let ((files (filter (lambda (f)
                                 (or (string-suffix? ".pub" f)
                                     (string-suffix? ".cert" f)
                                     (string-suffix? ".key" f)))
                               (directory-list dir))))
            (format #f "{\"keys\":[~a]}"
                    (apply string-append
                      (let loop ((fs files) (first #t))
                        (if (null? fs) '()
                            (cons (format #f "~a{\"name\":\"~a\"}"
                                          (if first "" ",") (car fs))
                                  (loop (cdr fs) #f)))))))
          "{\"keys\":[]}")))

  ;; ============================================================
  ;; Main Request Handler
  ;; ============================================================

  (define (handle-request in out)
    (let ((request-line (bin-get-line in)))
      (if (or (not request-line) (eof-object? request-line))
          #f
          (let ((clean request-line))
            (let-values (((method path) (parse-request-line clean)))
              (let ((headers (parse-headers in)))
                (printf "[http] ~a ~a~%" method path)
                (cond
                  ;; Main page - status only
                  ((or (equal? path "/") (equal? path "/index.html"))
                   (http-ok out "text/html; charset=utf-8" (status-html)))

                  ;; API: system info
                  ((equal? path "/api/info")
                   (http-ok out "application/json"
                     (format #f "{\"version\":\"0.9.12\",\"name\":\"Cyberspace\",\"port\":~a}"
                             *server-port*)))

                  ;; API: vault objects
                  ((equal? path "/api/vault")
                   (http-ok out "application/json" (api-vault-list)))

                  ;; API: keys
                  ((equal? path "/api/keys")
                   (http-ok out "application/json" (api-keys-list)))

                  ;; API: federation peers
                  ((equal? path "/api/peers")
                   (http-ok out "application/json" "{\"peers\":[]}"))

                  ;; API: preferences
                  ((equal? path "/api/preferences")
                   (http-ok out "application/json"
                     "{\"fontName\":\"SF Mono\",\"fontSize\":13,\"theme\":\"dark\"}"))

                  ;; Static files
                  ((string-prefix? "/static/" path)
                   (serve-static out (substring path 8 (string-length path))))

                  ;; Favicon
                  ((equal? path "/favicon.ico")
                   (http-not-found out))

                  (else
                   (http-not-found out)))))))))

  ;; ============================================================
  ;; Status Page (Static HTML - No JavaScript, No WebSocket)
  ;; ============================================================

  (define (status-html)
    (string-append
"<!DOCTYPE html><html><head><meta charset='UTF-8'>
<title>Cyberspace Status</title>
<style>
*{margin:0;padding:0;box-sizing:border-box}
body{font-family:system-ui,-apple-system,sans-serif;background:#fafafa;color:#2e3436;
     max-width:800px;margin:40px auto;padding:0 20px;line-height:1.6}
h1{color:#1a1a1a;font-size:2em;margin-bottom:0.5em}
h2{color:#3a3a3a;font-size:1.3em;margin-top:1.5em;margin-bottom:0.5em;border-bottom:2px solid #e0e0e0;padding-bottom:0.3em}
pre{background:#f5f5f5;padding:12px;border-radius:4px;overflow-x:auto;font-size:0.9em}
code{background:#f5f5f5;padding:2px 6px;border-radius:3px;font-family:'SF Mono',Monaco,monospace}
.box{background:white;border:1px solid #e0e0e0;border-radius:6px;padding:20px;margin:20px 0;box-shadow:0 1px 3px rgba(0,0,0,0.1)}
.status{color:#2e7d32}
.api{color:#1976d2}
a{color:#1976d2;text-decoration:none}
a:hover{text-decoration:underline}
</style></head><body>
<h1>Cyberspace</h1>
<div class='box'>
<p><strong class='status'>✓ Server Running</strong></p>
<p>Port: " (number->string *server-port*) "</p>
<p>Version: 0.9.12</p>
</div>

<h2>REPL Access</h2>
<div class='box'>
<p><strong>Terminal (Recommended):</strong></p>
<pre>ssh user@" *server-host* "
cs --boot=gate</pre>

<p><strong>Local GUI App:</strong></p>
<p>Use native macOS/Linux app with PTY connection (no WebSocket)</p>
</div>

<h2>API Endpoints</h2>
<div class='box'>
<p class='api'><a href='/api/info'>GET /api/info</a> - System information</p>
<p class='api'><a href='/api/vault'>GET /api/vault</a> - Vault objects</p>
<p class='api'><a href='/api/keys'>GET /api/keys</a> - Key list</p>
<p class='api'><a href='/api/peers'>GET /api/peers</a> - Federation peers</p>
</div>

<h2>Architecture</h2>
<div class='box'>
<p><strong>No WebSockets.</strong> This server provides HTTP status/metrics only.</p>
<p>For REPL interaction, use:</p>
<ul style='margin-left:20px;margin-top:10px'>
<li>SSH + terminal (universal)</li>
<li>Native GUI app with PTY (macOS/Linux)</li>
<li>Direct terminal: <code>cs --boot=gate</code></li>
</ul>
</div>

<p style='margin-top:40px;color:#757575;font-size:0.9em'>
Library of Cyberspace · <a href='https://www.yoyodyne.com/ddp/cyberspace/'>Documentation</a>
</p>
</body></html>"))

  ;; ============================================================
  ;; Server Main Loop
  ;; ============================================================

  (define (start-server . opts)
    (let ((port (get-opt opts 0 *server-port*)))
      (set! *server-port* port)
      (set! *static-dir* (or (getenv "CYBERSPACE_STATIC")
                             (string-append (current-directory) "/static")))

      (printf "~%  Cyberspace HTTP Status Server~%")
      (printf "  Port: ~a~%"  port)
      (printf "  Status page: http://~a:~a/~%" *server-host* port)
      (printf "  For REPL: use SSH or native GUI app~%")
      (printf "~%")

      (let ((listener (tcp-listen port)))
        (printf "  Listening on http://~a:~a/~%~%" *server-host* port)
        (flush-output-port (current-output-port))

        (let loop ()
          (let-values (((in out) (tcp-accept-binary listener)))
            (fork-thread
              (lambda ()
                (guard (exn
                        [#t (printf "[error] ~a~%"
                              (if (message-condition? exn)
                                  (condition-message exn)
                                  "unknown error"))
                            (close-port in)
                            (close-port out)])
                  (handle-request in out)
                  (close-port in)
                  (close-port out))))
            (loop))))))

) ; end library
