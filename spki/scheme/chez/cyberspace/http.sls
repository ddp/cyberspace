;;; http.sls - Minimal HTTP/1.1 server for Cyberspace (Chez Port)
;;; Library of Cyberspace
;;;
;;; Pure Scheme implementation using TCP sockets.
;;; Serves static files, designed for memo/documentation portal.
;;;
;;; Ported from http.scm.
;;; Copyright (c) 2026 Yoyodyne. See LICENSE.

(library (cyberspace http)
  (export
    http-serve
    http-stop
    http-response
    mime-type)

  (import (except (rnrs) file-exists? flush-output-port find string-downcase)
          (only (chezscheme)
                printf format void system
                file-exists?
                current-directory
                with-output-to-string
                flush-output-port
                open-file-input-port)
          (cyberspace chicken-compatibility chicken)
          (cyberspace chicken-compatibility tcp)
          (cyberspace os))

  ;; ============================================================
  ;; Path Utilities (replaces chicken pathname)
  ;; ============================================================

  (define (pathname-extension path)
    "Extract file extension (without dot), or #f."
    (let ((dot-pos (let loop ((i (- (string-length path) 1)))
                     (cond ((< i 0) #f)
                           ((char=? (string-ref path i) #\.) i)
                           ((char=? (string-ref path i) #\/) #f)
                           (else (loop (- i 1)))))))
      (and dot-pos
           (< (+ dot-pos 1) (string-length path))
           (substring path (+ dot-pos 1) (string-length path)))))

  (define (pathname-strip-directory path)
    "Extract filename from path."
    (let loop ((i (- (string-length path) 1)))
      (cond ((< i 0) path)
            ((char=? (string-ref path i) #\/)
             (substring path (+ i 1) (string-length path)))
            (else (loop (- i 1))))))

  (define (normalize-pathname path)
    "Basic path normalization - resolve . and .."
    ;; Simple implementation: just clean up double slashes
    (let loop ((p path))
      (let ((new (string-replace-all p "//" "/")))
        (if (string=? new p) p (loop new)))))

  (define (string-replace-all str old new)
    "Replace all occurrences of old with new in str."
    (let ((old-len (string-length old))
          (new-len (string-length new)))
      (let loop ((start 0) (acc ""))
        (let ((pos (string-find str old start)))
          (if (not pos)
              (string-append acc (substring str start (string-length str)))
              (loop (+ pos old-len)
                    (string-append acc (substring str start pos) new)))))))

  (define (string-find str pattern start)
    "Find pattern in str starting at start. Returns index or #f."
    (let ((slen (string-length str))
          (plen (string-length pattern)))
      (let loop ((i start))
        (cond ((> (+ i plen) slen) #f)
              ((string=? (substring str i (+ i plen)) pattern) i)
              (else (loop (+ i 1)))))))

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

  (define (string-downcase str)
    (list->string (map char-downcase (string->list str))))

  ;; ============================================================
  ;; HTTP Date (RFC 7231)
  ;; ============================================================

  (define (http-date . rest)
    "HTTP date string. Uses shell date for formatting."
    (or (shell-command "date -u '+%a, %d %b %Y %H:%M:%S GMT'")
        "Thu, 01 Jan 1970 00:00:00 GMT"))

  ;; ============================================================
  ;; HTTP Request Parsing
  ;; ============================================================

  (define (parse-request in)
    (let ((line (get-line in)))
      (if (or (eof-object? line) (string=? line ""))
          #f
          (let ((parts (string-split line)))
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
      (let ((line (get-line in)))
        (if (or (eof-object? line) (string=? line "") (string=? line "\r"))
            (reverse headers)
            (let ((colon (string-contains line ":")))
              (if colon
                  (loop (cons (cons (string-downcase
                                     (string-trim-both (substring line 0 colon)))
                                    (string-trim-both
                                     (substring line (+ colon 1)
                                                (string-length line))))
                              headers))
                  (loop headers)))))))

  ;; ============================================================
  ;; HTTP Response Building
  ;; ============================================================

  (define (http-response status . rest)
    "Build HTTP response string.
     Optional keywords: content-type: body: headers:"
    (let ((content-type (get-key rest 'content-type: "text/plain"))
          (body (get-key rest 'body: ""))
          (extra-headers (get-key rest 'headers: '())))
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
         "HTTP/1.1 " (number->string status) " " status-text "\r\n"
         "Date: " (http-date) "\r\n"
         "Server: Cyberspace/1.0\r\n"
         "Content-Type: " content-type "\r\n"
         "Content-Length: " (number->string (string-length body)) "\r\n"
         "Connection: close\r\n"
         (apply string-append
                (map (lambda (h)
                       (string-append (car h) ": " (cdr h) "\r\n"))
                     extra-headers))
         "\r\n"
         body))))

  ;; ============================================================
  ;; File Serving
  ;; ============================================================

  (define (read-file-as-string path)
    "Read entire file contents as a string."
    (guard (exn [#t ""])
      (let ((port (open-file-input-port path)))
        (let loop ((chars '()))
          (let ((b (get-u8 port)))
            (if (eof-object? b)
                (begin
                  (close-port port)
                  (list->string (reverse chars)))
                (loop (cons (integer->char b) chars))))))))

  (define (file-readable? path)
    "Check if file exists and is readable."
    (and (file-exists? path) (not (directory-exists? path))))

  (define (url-decode path)
    "Basic URL decoding for common characters."
    (string-replace-all
     (string-replace-all path "%20" " ")
     "%2F" "/"))

  (define (sanitize-path path)
    "Remove directory traversal attempts."
    (let loop ((p path))
      (let ((new (string-replace-all
                  (string-replace-all p "/../" "/")
                  "/./" "/")))
        (if (string=? new p) p (loop new)))))

  (define (serve-file path doc-root)
    (let* ((clean-path (if (string=? path "/") "/index.html" path))
           (clean-path (if (string-suffix? "/" clean-path)
                           (string-append clean-path "index.html")
                           clean-path))
           (clean-path (sanitize-path clean-path))
           (full-path (string-append doc-root clean-path)))
      (cond
       ;; Security: ensure path stays within doc-root
       ((not (string-prefix? doc-root (normalize-pathname full-path)))
        (http-response 403 'body: "Forbidden"))
       ;; File doesn't exist
       ((not (file-exists? full-path))
        (http-response 404 'body: (string-append "Not Found: " path)))
       ;; Directory without trailing slash - redirect
       ((and (directory-exists? full-path) (not (string-suffix? "/" path)))
        (http-response 301 'headers: `(("Location" . ,(string-append path "/")))))
       ;; Serve file
       ((file-readable? full-path)
        (let ((content (read-file-as-string full-path))
              (ctype (mime-type full-path)))
          (http-response 200
                         'content-type: ctype
                         'body: content
                         'headers: (if (or (string-contains ctype "pdf")
                                           (string-contains ctype "postscript"))
                                       '(("Content-Disposition" . "inline"))
                                       '()))))
       (else
        (http-response 403 'body: "Forbidden")))))

  ;; ============================================================
  ;; Connection Handler
  ;; ============================================================

  (define (handle-connection in out doc-root)
    (guard (exn [#t
      (guard (exn2 [#t (void)])
        (put-string out (http-response 500 'body: "Internal Server Error"))
        (flush-output-port out))
      (close-port in)
      (close-port out)])
      (let ((request (parse-request in)))
        (if (not request)
            (put-string out (http-response 400 'body: "Bad Request"))
            (let ((method (cdr (assq 'method request)))
                  (path (cdr (assq 'path request))))
              (let ((decoded-path (url-decode path)))
                (cond
                 ((not (member method '("GET" "HEAD")))
                  (put-string out (http-response 405 'body: "Method Not Allowed")))
                 (else
                  (put-string out (serve-file decoded-path doc-root))))))))
      (flush-output-port out)
      (close-port in)
      (close-port out)))

  ;; ============================================================
  ;; Server
  ;; ============================================================

  (define *server-listener* #f)
  (define *server-running* #f)

  (define (http-serve . rest)
    "Start HTTP server.
     Optional keywords: port: N (default 8080), doc-root: path (default \".\")"
    (let* ((port (get-key rest 'port: 8080))
           (root (get-key rest 'doc-root: "."))
           (doc-root (normalize-pathname
                      (string-append (current-directory) "/" root))))
      (printf "Cyberspace HTTP serving ~a on port ~a~%" doc-root port)
      (set! *server-listener* (tcp-listen port))
      (set! *server-running* #t)
      (let loop ()
        (when *server-running*
          (guard (exn [#t
            (unless (not *server-running*)
              (printf "Accept error: ~a~%"
                      (if (message-condition? exn)
                          (condition-message exn) "?"))
              (loop))])
            (let-values (((in out) (tcp-accept *server-listener*)))
              (handle-connection in out doc-root)
              (loop)))))))

  (define (http-stop)
    "Stop HTTP server."
    (set! *server-running* #f)
    (when *server-listener*
      (tcp-close *server-listener*)
      (set! *server-listener* #f))
    (print "HTTP server stopped"))

) ;; end library
