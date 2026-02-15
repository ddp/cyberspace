;;; server.scm - HTTP status server for Cyberspace
;;;
;;; Simple HTTP server for status/metrics only.
;;; For REPL access, use SSH or native GUI app with PTY.
;;;
;;; Port: 4321 (default)
;;;
;;; Endpoints:
;;;   GET /           - Status page
;;;   GET /api/*      - JSON metrics (vault, keys, info)

(module server
  (start-server
   server-port
   server-host)

  (import scheme
          (chicken base)
          (chicken io)
          (chicken port)
          (chicken format)
          (chicken string)
          (chicken tcp)
          (chicken time)
          (chicken time posix)
          (chicken file)
          (chicken pathname)
          (chicken process-context)
          (chicken condition)
          srfi-1
          srfi-13
          srfi-18
          srfi-69)

  ;; ============================================================
  ;; Configuration
  ;; ============================================================

  (define *server-port* 4321)
  (define *server-host* "127.0.0.1")
  (define *static-dir* #f)

  (define (server-port) *server-port*)
  (define (server-host) *server-host*)

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
  ;; HTTP Response Helpers
  ;; ============================================================

  (define (http-response out status headers body)
    (display (sprintf "HTTP/1.1 ~a\r\n" status) out)
    (for-each (lambda (h)
                (display (sprintf "~a: ~a\r\n" (car h) (cdr h)) out))
              headers)
    (display "\r\n" out)
    (when body
      (display body out))
    (flush-output-port out))

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
    (let ((parts (string-split line " ")))
      (if (>= (length parts) 2)
          (values (car parts) (cadr parts))
          (values #f #f))))

  (define (parse-headers in)
    (let loop ((headers '()))
      (let ((line (read-line in)))
        (if (or (eof-object? line) (string=? line "") (string=? line "\r"))
            (reverse headers)
            (let ((colon (string-contains line ":")))
              (if colon
                  (loop (cons (cons (string-downcase (string-trim-both (substring line 0 colon)))
                                    (string-trim-both (substring line (+ colon 1))))
                              headers))
                  (loop headers)))))))

  ;; ============================================================
  ;; Static File Serving
  ;; ============================================================

  (define (serve-static out path)
    (let ((file-path (string-append *static-dir* "/" path)))
      (if (and (file-exists? file-path)
               (not (directory-exists? file-path)))
          (let ((content (with-input-from-file file-path read-string))
                (mime (get-mime-type file-path)))
            (http-ok out mime content))
          (http-not-found out))))

  ;; ============================================================
  ;; API Endpoints
  ;; ============================================================

  (define (api-vault-list)
    (let ((dir ".vault/objects"))
      (if (and (file-exists? dir) (directory-exists? dir))
          (let* ((files (filter (lambda (f) (not (string-prefix? "." f)))
                                (directory dir)))
                 (limited (take files (min 100 (length files)))))
            (sprintf "{\"objects\":[~a]}"
                    (string-intersperse
                      (map (lambda (f) (sprintf "{\"hash\":\"~a\"}" f))
                           limited)
                      ",")))
          "{\"objects\":[]}")))

  (define (api-keys-list)
    (let ((dir ".vault/keys"))
      (if (and (file-exists? dir) (directory-exists? dir))
          (let ((files (filter (lambda (f)
                                 (or (string-suffix? ".pub" f)
                                     (string-suffix? ".cert" f)
                                     (string-suffix? ".key" f)))
                               (directory dir))))
            (sprintf "{\"keys\":[~a]}"
                    (string-intersperse
                      (map (lambda (f) (sprintf "{\"name\":\"~a\"}" f))
                           files)
                      ",")))
          "{\"keys\":[]}")))

  ;; ============================================================
  ;; Main Request Handler
  ;; ============================================================

  (define (handle-request in out)
    (let ((request-line (read-line in)))
      (when (and request-line (not (eof-object? request-line)))
        (let-values (((method path) (parse-request-line request-line)))
          (let ((headers (parse-headers in)))
            (printf "[http] ~a ~a~%" method path)
            (cond
              ;; Main page - status only
              ((or (equal? path "/") (equal? path "/index.html"))
               (http-ok out "text/html; charset=utf-8" (status-html)))

              ;; API: system info
              ((equal? path "/api/info")
               (http-ok out "application/json"
                 (sprintf "{\"version\":\"0.9.12\",\"name\":\"Cyberspace\",\"port\":~a}"
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
               (serve-static out (substring path 8)))

              ;; Favicon
              ((equal? path "/favicon.ico")
               (http-not-found out))

              (else
               (http-not-found out))))))))

  ;; ============================================================
  ;; Status Page (Static HTML)
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
<p><strong class='status'>Server Running</strong></p>
<p>Port: " (number->string *server-port*) "</p>
<p>Version: 0.9.12</p>
</div>

<h2>REPL Access</h2>
<div class='box'>
<p><strong>Terminal (Recommended):</strong></p>
<pre>ssh user@" *server-host* "
cs --boot=gate</pre>

<p><strong>Local GUI App:</strong></p>
<p>Use native macOS/Linux app with PTY connection</p>
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
<p>This server provides HTTP status/metrics only.</p>
<p>For REPL interaction, use:</p>
<ul style='margin-left:20px;margin-top:10px'>
<li>SSH + terminal (universal)</li>
<li>Native GUI app with PTY (macOS/Linux)</li>
<li>Direct terminal: <code>cs --boot=gate</code></li>
</ul>
</div>

<p style='margin-top:40px;color:#757575;font-size:0.9em'>
Library of Cyberspace &middot; <a href='https://www.yoyodyne.com/ddp/cyberspace/'>Documentation</a>
</p>
</body></html>"))

  ;; ============================================================
  ;; Server Main Loop
  ;; ============================================================

  (define (start-server . opts)
    (let ((port (if (pair? opts) (car opts) *server-port*)))
      (set! *server-port* port)
      (set! *static-dir* (or (get-environment-variable "CYBERSPACE_STATIC")
                             (string-append (current-directory) "/static")))

      (printf "~%  Cyberspace HTTP Status Server~%")
      (printf "  Port: ~a~%"  port)
      (printf "  Status page: http://~a:~a/~%" *server-host* port)
      (printf "  For REPL: use SSH or native GUI app~%")
      (printf "~%")

      (let ((listener (tcp-listen port)))
        (printf "  Listening on http://~a:~a/~%~%" *server-host* port)

        (let loop ()
          (receive (in out) (tcp-accept listener)
            (thread-start!
              (make-thread
                (lambda ()
                  (handle-exceptions exn
                    (begin
                      (printf "[error] ~a~%"
                              (if (condition? exn)
                                  ((condition-property-accessor 'exn 'message "unknown error") exn)
                                  "unknown error"))
                      (close-input-port in)
                      (close-output-port out))
                    (handle-request in out)
                    (close-input-port in)
                    (close-output-port out))))))
          (loop)))))

) ;; end module
