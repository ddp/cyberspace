;;; http.sls - Minimal HTTP/1.1 server for Cyberspace
;;; Library of Cyberspace - Chez Port
;;;
;;; Pure Scheme implementation using TCP sockets.
;;; Serves static files, designed for memo/documentation portal.
;;;
;;; (http-serve 'port: 8080 'doc-root: "/path/to/docs")
;;;
;;; Ported from Chicken's http.scm.
;;; Changes: module -> library, #!key -> get-key, (chicken tcp) -> (cyberspace tcp),
;;;          string-split/string-prefix?/pathname inlined.

(library (cyberspace http)
  (export
    http-serve
    http-stop
    http-response
    mime-type)

  (import (rnrs)
          (only (chezscheme)
                printf format system
                current-time time-second
                file-directory?)
          (cyberspace tcp)
          (cyberspace chicken-compatibility chicken))

  ;; ============================================================
  ;; Helpers
  ;; ============================================================

  (define (string-prefix? prefix str)
    (and (>= (string-length str) (string-length prefix))
         (string=? (substring str 0 (string-length prefix)) prefix)))

  (define (string-suffix? suffix str)
    (and (>= (string-length str) (string-length suffix))
         (string=? (substring str (- (string-length str) (string-length suffix))
                              (string-length str))
                   suffix)))

  (define (string-contains haystack needle)
    (let ((hlen (string-length haystack))
          (nlen (string-length needle)))
      (let loop ((i 0))
        (cond
          ((> (+ i nlen) hlen) #f)
          ((string=? (substring haystack i (+ i nlen)) needle) i)
          (else (loop (+ i 1)))))))

  (define (string-trim s)
    ;; Trim leading/trailing whitespace
    (let* ((len (string-length s))
           (start (let loop ((i 0))
                    (if (or (>= i len) (not (char-whitespace? (string-ref s i)))) i (loop (+ i 1)))))
           (end (let loop ((i (- len 1)))
                  (if (or (< i start) (not (char-whitespace? (string-ref s i)))) (+ i 1) (loop (- i 1))))))
      (substring s start end)))

  (define (string-replace str old new)
    ;; Replace all occurrences of old with new
    (let ((olen (string-length old))
          (nlen (string-length new))
          (slen (string-length str)))
      (if (= olen 0) str
          (let loop ((i 0) (acc '()))
            (cond
              ((> (+ i olen) slen)
               (apply string-append (reverse (cons (substring str i slen) acc))))
              ((string=? (substring str i (+ i olen)) old)
               (loop (+ i olen) (cons new acc)))
              (else
               (loop (+ i 1) (cons (string (string-ref str i)) acc))))))))

  (define (pathname-extension path)
    ;; Get file extension (without dot), or #f
    (let loop ((i (- (string-length path) 1)))
      (cond
        ((< i 0) #f)
        ((char=? (string-ref path i) #\.)
         (substring path (+ i 1) (string-length path)))
        ((char=? (string-ref path i) #\/) #f)
        (else (loop (- i 1))))))

  (define (directory-exists? path)
    (and (file-exists? path) (file-directory? path)))

  (define (current-seconds)
    (time-second (current-time)))

  (define (string-join lst sep)
    (if (null? lst) ""
        (let loop ((rest (cdr lst)) (acc (car lst)))
          (if (null? rest) acc
              (loop (cdr rest) (string-append acc sep (car rest)))))))

  (define (read-line port)
    (let loop ((chars '()))
      (let ((c (read-char port)))
        (cond
          ((eof-object? c)
           (if (null? chars) #f (list->string (reverse chars))))
          ((char=? c #\newline)
           (list->string (reverse chars)))
          ((char=? c #\return) (loop chars))
          (else (loop (cons c chars)))))))

  ;; ============================================================
  ;; MIME Types
  ;; ============================================================

  (define *mime-types*
    '(("html" . "text/html; charset=utf-8")
      ("htm"  . "text/html; charset=utf-8")
      ("txt"  . "text/plain; charset=utf-8")
      ("scm"  . "text/plain; charset=utf-8")
      ("sls"  . "text/plain; charset=utf-8")
      ("css"  . "text/css; charset=utf-8")
      ("js"   . "application/javascript")
      ("json" . "application/json")
      ("pdf"  . "application/pdf")
      ("ps"   . "application/postscript")
      ("svg"  . "image/svg+xml")
      ("png"  . "image/png")
      ("jpg"  . "image/jpeg")
      ("jpeg" . "image/jpeg")
      ("gif"  . "image/gif")
      ("ico"  . "image/x-icon")
      ("woff" . "font/woff")
      ("woff2" . "font/woff2")))

  (define (mime-type path)
    (let* ((ext (pathname-extension path))
           (ext (if ext (string-downcase ext) ""))
           (entry (assoc ext *mime-types*)))
      (if entry (cdr entry) "application/octet-stream")))

  ;; ============================================================
  ;; HTTP Protocol
  ;; ============================================================

  (define (parse-request in)
    ;; Parse HTTP request line and headers
    (let ((line (read-line in)))
      (if (not line)
          #f
          (let ((parts (string-split line " ")))
            (if (< (length parts) 3)
                #f
                (let ((method (car parts))
                      (path (cadr parts))
                      (headers (parse-headers in)))
                  `((method . ,method)
                    (path . ,path)
                    (headers . ,headers))))))))

  (define (parse-headers in)
    (let loop ((headers '()))
      (let ((line (read-line in)))
        (if (or (not line) (= 0 (string-length line)))
            (reverse headers)
            (let ((colon (string-contains line ":")))
              (if colon
                  (loop (cons (cons (string-downcase (string-trim (substring line 0 colon)))
                                    (string-trim (substring line (+ colon 1) (string-length line))))
                              headers))
                  (loop headers)))))))

  (define (http-response status . opts)
    ;; Build HTTP response
    (let ((content-type (get-key opts 'content-type: "text/plain"))
          (body (get-key opts 'body: ""))
          (headers (get-key opts 'headers: '())))
      (let ((status-text (case status
                           ((200) "OK")
                           ((301) "Moved Permanently")
                           ((302) "Found")
                           ((304) "Not Modified")
                           ((400) "Bad Request")
                           ((403) "Forbidden")
                           ((404) "Not Found")
                           ((405) "Method Not Allowed")
                           ((500) "Internal Server Error")
                           (else "Unknown"))))
        (string-append
         (format #f "HTTP/1.1 ~a ~a\r\n" status status-text)
         (format #f "Server: Cyberspace/1.0\r\n")
         (format #f "Content-Type: ~a\r\n" content-type)
         (format #f "Content-Length: ~a\r\n" (string-length body))
         "Connection: close\r\n"
         (string-join (map (lambda (h) (format #f "~a: ~a\r\n" (car h) (cdr h))) headers) "")
         "\r\n"
         body))))

  ;; ============================================================
  ;; Static File Server
  ;; ============================================================

  (define (serve-file path doc-root)
    (let* ((clean-path (if (string=? path "/") "/index.html" path))
           (clean-path (if (string-suffix? "/" clean-path)
                           (string-append clean-path "index.html")
                           clean-path))
           ;; Prevent directory traversal
           (clean-path (string-replace (string-replace clean-path "/../" "/") "/./" "/"))
           (full-path (string-append doc-root clean-path)))
      (cond
       ;; Security: reject paths with ..
       ((string-contains full-path "..")
        (http-response 403 'body: "Forbidden"))
       ;; File doesn't exist
       ((not (file-exists? full-path))
        (http-response 404 'body: (format #f "Not Found: ~a" path)))
       ;; Directory without trailing slash
       ((and (directory-exists? full-path) (not (string-suffix? "/" path)))
        (http-response 301 'headers: `(("Location" . ,(string-append path "/")))))
       ;; Serve file
       (else
        (guard (exn [#t (http-response 500 'body: "Internal Server Error")])
          (let ((content (with-input-from-file full-path
                           (lambda () (get-string-all (current-input-port)))))
                (ctype (mime-type full-path)))
            (http-response 200
                           'content-type: ctype
                           'body: content)))))))

  ;; ============================================================
  ;; Connection Handling
  ;; ============================================================

  (define (handle-connection in out doc-root)
    (guard (exn [#t
                 (guard (exn2 [#t #f])
                   (display (http-response 500 'body: "Internal Server Error") out))
                 (close-port in)
                 (close-port out)])
      (let ((request (parse-request in)))
        (if (not request)
            (display (http-response 400 'body: "Bad Request") out)
            (let ((method (alist-ref 'method request))
                  (path (alist-ref 'path request)))
              ;; Basic URL decoding
              (let ((decoded-path (string-replace (string-replace path "%20" " ") "%2F" "/")))
                (cond
                 ((not (or (string=? method "GET") (string=? method "HEAD")))
                  (display (http-response 405 'body: "Method Not Allowed") out))
                 (else
                  (let ((response (serve-file decoded-path doc-root)))
                    (display response out))))))))
      (close-port in)
      (close-port out)))

  ;; ============================================================
  ;; Server
  ;; ============================================================

  (define *server-listener* #f)
  (define *server-running* #f)

  (define (http-serve . opts)
    ;; Start HTTP server
    ;; (http-serve 'port: 8080 'doc-root: ".")
    (let ((port (get-key opts 'port: 8080))
          (doc-root (get-key opts 'doc-root: ".")))
      (printf "Cyberspace HTTP serving ~a on port ~a~%" doc-root port)
      (set! *server-listener* (tcp-listen port))
      (set! *server-running* #t)
      (let loop ()
        (when *server-running*
          (guard (exn [#t
                       (when *server-running*
                         (printf "Accept error~%")
                         (loop))])
            (let-values (((in out) (tcp-accept *server-listener*)))
              (handle-connection in out doc-root)
              (loop)))))))

  (define (http-stop)
    ;; Stop HTTP server
    (set! *server-running* #f)
    (when *server-listener*
      (tcp-close *server-listener*)
      (set! *server-listener* #f))
    (print "HTTP server stopped"))

) ;; end library
