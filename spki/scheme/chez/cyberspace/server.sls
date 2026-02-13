;;; server.sls - HTTP/WebSocket server for Cyberspace
;;;
;;; Serves the web UI and provides WebSocket bridge to Scheme REPL.
;;; Lightweight embedded server for the native macOS application.
;;;
;;; Port: 4321 (default)
;;;
;;; Endpoints:
;;;   GET /           - Main UI (index.html)
;;;   GET /static/*   - Static assets (CSS, JS)
;;;   WS  /ws         - WebSocket REPL connection

(library (cyberspace server)
  (export
    start-server
    server-port
    server-host)

  (import (rnrs)
          (rnrs mutable-strings)
          (only (chezscheme)
                printf format with-output-to-string
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
  ;; HTTP Response Helpers
  ;; ============================================================

  (define (http-response out status headers body)
    (put-string out (format #f "HTTP/1.1 ~a\r\n" status))
    (for-each (lambda (h)
                (put-string out (format #f "~a: ~a\r\n" (car h) (cdr h))))
              headers)
    (put-string out "\r\n")
    (when body
      (put-string out body))
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
    (let ((sp1 (string-contains line " ")))
      (if sp1
          (let ((rest (substring line (+ sp1 1) (string-length line))))
            (let ((sp2 (string-contains rest " ")))
              (values (substring line 0 sp1)
                      (if sp2 (substring rest 0 sp2) rest))))
          (values #f #f))))

  (define (parse-headers in)
    (let loop ((headers '()))
      (let ((line (get-line in)))
        (if (or (eof-object? line)
                (string=? line "")
                (string=? line "\r"))
            (reverse headers)
            ;; Strip trailing \r
            (let* ((clean (if (and (> (string-length line) 0)
                                   (char=? (string-ref line (- (string-length line) 1)) #\return))
                              (substring line 0 (- (string-length line) 1))
                              line))
                   (colon (string-contains clean ":")))
              (if colon
                  (loop (cons (cons (string-downcase (string-trim-both (substring clean 0 colon)))
                                    (string-trim-both (substring clean (+ colon 1) (string-length clean))))
                              headers))
                  (loop headers)))))))

  ;; ============================================================
  ;; WebSocket Support
  ;; ============================================================

  (define *ws-magic* "258EAFA5-E914-47DA-95CA-C5AB0DC85B11")

  (define (ws-accept-key key)
    (let ((combined (string-append key *ws-magic*)))
      (let-values (((to-stdin from-stdout from-stderr pid)
                    (open-process-ports
                      "printf '%s' | openssl sha1 -binary | openssl base64"
                      (buffer-mode block)
                      (make-transcoder (utf-8-codec)))))
        (put-string to-stdin combined)
        (close-port to-stdin)
        (let ((result (get-line from-stdout)))
          (close-port from-stdout)
          (close-port from-stderr)
          (if (eof-object? result) "" result)))))

  (define (handle-websocket in out headers)
    (printf "[ws] Upgrading connection~%")
    (let* ((key-pair (assoc "sec-websocket-key" headers))
           (key (if key-pair (cdr key-pair) "")))
      (let ((accept (ws-accept-key key)))
        (put-string out "HTTP/1.1 101 Switching Protocols\r\n")
        (put-string out "Upgrade: websocket\r\n")
        (put-string out "Connection: Upgrade\r\n")
        (put-string out (format #f "Sec-WebSocket-Accept: ~a\r\n" accept))
        (put-string out "\r\n")
        (flush-output-port out)
        (ws-loop in out))))

  (define (ws-loop in out)
    (guard (exn
            [#t (printf "[ws] Loop error: ~a~%" (condition-message exn))])
      (let loop ()
        (let ((b1 (get-u8 in)))
          (when (and (not (eof-object? b1)))
            (let* ((opcode (bitwise-and b1 #x0f))
                   (b2 (get-u8 in))
                   (masked (bitwise-and b2 #x80))
                   (len (bitwise-and b2 #x7f)))
              (let ((payload-len
                     (cond
                       ((= len 126)
                        (+ (bitwise-arithmetic-shift-left (get-u8 in) 8) (get-u8 in)))
                       ((= len 127)
                        (let ploop ((i 8) (n 0))
                          (if (zero? i) n
                              (ploop (- i 1)
                                     (+ (bitwise-arithmetic-shift-left n 8) (get-u8 in))))))
                       (else len))))

                (let ((mask-key
                       (if (> masked 0)
                           (list (get-u8 in) (get-u8 in) (get-u8 in) (get-u8 in))
                           #f)))

                  (let* ((payload-bv (get-bytevector-n in payload-len))
                         (payload (if (bytevector? payload-bv)
                                      (utf8->string payload-bv)
                                      ""))
                         (unmasked
                          (if mask-key
                              (list->string
                                (let uloop ((i 0) (chars (string->list payload)))
                                  (if (null? chars) '()
                                      (cons (integer->char
                                              (bitwise-xor (char->integer (car chars))
                                                           (list-ref mask-key (mod i 4))))
                                            (uloop (+ i 1) (cdr chars))))))
                              payload)))

                    (case opcode
                      ((1)  ; Text frame
                       (ws-handle-message unmasked out)
                       (loop))
                      ((8)  ; Close
                       (ws-send-close out))
                      ((9)  ; Ping
                       (ws-send-pong out unmasked)
                       (loop))
                      (else (loop))))))))))))

  (define (ws-send-frame out opcode payload)
    ;; WebSocket frame: write header bytes as characters (ports are transcoded)
    ;; then write payload string directly
    (let ((len (string-length payload)))
      (put-char out (integer->char (bitwise-ior #x80 opcode)))
      (cond
        ((< len 126)
         (put-char out (integer->char len)))
        ((< len 65536)
         (put-char out (integer->char 126))
         (put-char out (integer->char (bitwise-arithmetic-shift-right len 8)))
         (put-char out (integer->char (bitwise-and len #xff))))
        (else
         (put-char out (integer->char 127))
         (do ((i 7 (- i 1)))
             ((< i 0))
           (put-char out (integer->char
                           (bitwise-and (bitwise-arithmetic-shift-right len (* 8 i)) #xff))))))
      (put-string out payload)
      (flush-output-port out)))

  (define (ws-send-text out msg)
    (guard (exn [#t (printf "[ws] Send failed~%") #f])
      (ws-send-frame out 1 msg)
      #t))

  (define (ws-send-close out)
    (ws-send-frame out 8 ""))

  (define (ws-send-pong out data)
    (ws-send-frame out 10 data))

  ;; ============================================================
  ;; WebSocket Message Handling
  ;; ============================================================

  (define (ws-handle-message msg out)
    (printf "[ws] Received: ~a~%" msg)
    (let* ((type (extract-json-field "type" msg))
           (data (extract-json-field "data" msg)))
      (cond
        ((equal? type "eval")
         (let ((expr (extract-json-field "expression" msg)))
           (when expr
             (ws-send-text out
               (format #f "{\"type\":\"result\",\"value\":\"eval not yet connected\"}")))))
        (else
         (ws-send-text out (format #f "{\"type\":\"echo\",\"data\":~s}" msg))))))

  (define (extract-json-field field json-str)
    (let ((pattern (format #f "\"~a\":\"" field)))
      (let ((start (string-contains json-str pattern)))
        (if start
            (let* ((val-start (+ start (string-length pattern)))
                   (rest (substring json-str val-start (string-length json-str)))
                   (end (find-json-string-end rest)))
              (if end (substring rest 0 end) #f))
            #f))))

  (define (find-json-string-end str)
    (let loop ((i 0) (escaped #f))
      (if (>= i (string-length str)) #f
          (let ((c (string-ref str i)))
            (cond
              (escaped (loop (+ i 1) #f))
              ((char=? c #\\) (loop (+ i 1) #t))
              ((char=? c #\") i)
              (else (loop (+ i 1) #f)))))))

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
    (let ((request-line (get-line in)))
      (if (or (not request-line) (eof-object? request-line))
          #f
          ;; Strip \r
          (let ((clean (if (and (> (string-length request-line) 0)
                                (char=? (string-ref request-line
                                          (- (string-length request-line) 1)) #\return))
                           (substring request-line 0 (- (string-length request-line) 1))
                           request-line)))
            (let-values (((method path) (parse-request-line clean)))
              (let ((headers (parse-headers in)))
                (printf "[http] ~a ~a~%" method path)
                (cond
                  ;; WebSocket upgrade
                  ((and (equal? path "/ws")
                        (assoc "upgrade" headers)
                        (string-ci=? (cdr (assoc "upgrade" headers)) "websocket"))
                   (handle-websocket in out headers)
                   'websocket)

                  ;; Main page
                  ((or (equal? path "/") (equal? path "/index.html"))
                   (http-ok out "text/html; charset=utf-8" (index-html)))

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
  ;; Embedded UI (index.html) — abbreviated for boot
  ;; ============================================================

  (define (index-html)
    (string-append
      "<!DOCTYPE html><html><head><meta charset='UTF-8'>"
      "<title>Cyberspace</title>"
      "<style>"
      "body{font-family:monospace;background:#000;color:#0f0;margin:20px}"
      "h1{font-size:18px}pre{white-space:pre-wrap}"
      "</style></head><body>"
      "<h1>CYBERSPACE</h1>"
      "<p>Library of Cyberspace v0.9.12</p>"
      "<p>WebSocket REPL at /ws</p>"
      "<p>API: /api/info, /api/vault, /api/keys, /api/peers</p>"
      "</body></html>"))

  ;; ============================================================
  ;; Server Main Loop
  ;; ============================================================

  (define (start-server . opts)
    (let ((port (get-opt opts 0 *server-port*)))
      (set! *server-port* port)
      (set! *static-dir* (or (getenv "CYBERSPACE_STATIC")
                             (string-append (current-directory) "/static")))

      (printf "~%  Cyberspace Server~%")
      (printf "  Port: ~a~%"  port)
      (printf "  Static: ~a~%" *static-dir*)
      (printf "~%")

      (let ((listener (tcp-listen port)))
        (printf "  Listening on http://~a:~a/~%~%" *server-host* port)
        (flush-output-port (current-output-port))

        (let loop ()
          (let-values (((in out) (tcp-accept listener)))
            (fork-thread
              (lambda ()
                (guard (exn
                        [#t (printf "[error] ~a~%"
                              (if (message-condition? exn)
                                  (condition-message exn)
                                  "unknown error"))
                            (close-port in)
                            (close-port out)])
                  (let ((keep-alive (handle-request in out)))
                    (unless (eq? keep-alive 'websocket)
                      (close-port in)
                      (close-port out))))))
            (loop))))))

) ; end library
