;;; http.scm - Minimal HTTP/1.1 server for Cyberspace
;;;
;;; Pure Scheme implementation using TCP sockets.
;;; Serves static files, designed for memo/documentation portal.
;;;
;;; (http-serve port: 8080 doc-root: "/path/to/docs")

(module http
  (http-serve
   http-stop
   http-response
   mime-type)

  (import scheme
          (chicken base)
          (chicken string)
          (chicken io)
          (chicken file)
          (chicken pathname)
          (chicken format)
          (chicken time)
          (chicken time posix)
          (chicken port)
          (chicken tcp)
          (chicken condition)
          (chicken process)
          (chicken process-context)
          (srfi 13))

  ;; Export mode: open PS/PDF locally instead of serving
  (define *export-mode* #t)

  ;; MIME types for common file extensions
  (define *mime-types*
    '(("html" . "text/html; charset=utf-8")
      ("htm"  . "text/html; charset=utf-8")
      ("txt"  . "text/plain; charset=utf-8")
      ("scm"  . "text/plain; charset=utf-8")
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

  ;; HTTP date format (RFC 7231)
  (define (http-date #!optional (time (current-seconds)))
    (time->string (seconds->utc-time time) "%a, %d %b %Y %H:%M:%S GMT"))

  ;; Parse HTTP request line and headers
  (define (parse-request in)
    (let ((line (read-line in)))
      (if (or (eof-object? line) (string=? line ""))
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
        (if (or (eof-object? line) (string=? line "") (string=? line "\r"))
            (reverse headers)
            (let ((colon (substring-index ":" line)))
              (if colon
                  (loop (cons (cons (string-downcase (string-trim-both (substring line 0 colon)))
                                    (string-trim-both (substring line (+ colon 1))))
                              headers))
                  (loop headers)))))))

  ;; Build HTTP response
  (define (http-response status #!key
                         (content-type "text/plain")
                         (body "")
                         (headers '()))
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
       (sprintf "HTTP/1.1 ~A ~A\r\n" status status-text)
       (sprintf "Date: ~A\r\n" (http-date))
       (sprintf "Server: Cyberspace/1.0\r\n")
       (sprintf "Content-Type: ~A\r\n" content-type)
       (sprintf "Content-Length: ~A\r\n" (string-length body))
       (sprintf "Connection: close\r\n")
       (string-join (map (lambda (h) (sprintf "~A: ~A\r\n" (car h) (cdr h))) headers) "")
       "\r\n"
       body)))

  ;; Serve a static file
  (define (serve-file path doc-root)
    (let* ((clean-path (if (string=? path "/") "/index.html" path))
           (clean-path (if (string-suffix? "/" clean-path)
                           (string-append clean-path "index.html")
                           clean-path))
           ;; Prevent directory traversal
           (clean-path (let loop ((p clean-path))
                         (let ((new (string-translate* p '(("/../" . "/") ("/./" . "/")))))
                           (if (string=? new p) p (loop new)))))
           (full-path (make-pathname doc-root clean-path)))
      (cond
       ;; Security: ensure path stays within doc-root
       ((not (string-prefix? doc-root (normalize-pathname full-path)))
        (http-response 403 body: "Forbidden"))
       ;; File doesn't exist
       ((not (file-exists? full-path))
        (http-response 404 body: (sprintf "Not Found: ~A" path)))
       ;; Directory without trailing slash - redirect
       ((and (directory-exists? full-path) (not (string-suffix? "/" path)))
        (http-response 301 headers: `(("Location" . ,(string-append path "/")))))
       ;; Export mode: open PS/PDF locally via Preview
       ;; PS files converted to PDF first (macOS Preview dropped native PS support)
       ((and *export-mode*
             (file-readable? full-path)
             (let ((ext (pathname-extension full-path)))
               (and ext (member (string-downcase ext) '("ps" "pdf")))))
        (let* ((ext (string-downcase (pathname-extension full-path)))
               (tmp-pdf "/tmp/cyberspace-export.pdf")
               (cmd (if (string=? ext "ps")
                        (sprintf "ps2pdf '~A' '~A' && open '~A'" full-path tmp-pdf tmp-pdf)
                        (sprintf "open '~A'" full-path))))
          (printf "EXPORT: ~A~%" cmd)
          (system cmd))
        (http-response 200
                       content-type: "text/html; charset=utf-8"
                       body: (sprintf "<html><body><p>Opened: ~A</p><script>history.back()</script></body></html>"
                                      (pathname-strip-directory full-path))))
       ;; Serve file
       ((file-readable? full-path)
        (let ((content (with-input-from-file full-path read-string))
              (ctype (mime-type full-path)))
          (http-response 200
                         content-type: ctype
                         body: content
                         headers: (if (or (string-contains ctype "pdf")
                                          (string-contains ctype "postscript"))
                                      '(("Content-Disposition" . "inline"))
                                      '()))))
       (else
        (http-response 403 body: "Forbidden")))))

  ;; Handle a single connection
  (define (handle-connection in out doc-root)
    (handle-exceptions exn
        (begin
          (display (http-response 500 body: "Internal Server Error") out)
          (close-input-port in)
          (close-output-port out))
      (let ((request (parse-request in)))
        (if (not request)
            (display (http-response 400 body: "Bad Request") out)
            (let ((method (alist-ref 'method request))
                  (path (alist-ref 'path request)))
              ;; Decode URL path (basic - spaces and common chars)
              (let ((decoded-path (string-translate* path '(("%20" . " ")
                                                            ("%2F" . "/")))))
                (cond
                 ((not (member method '("GET" "HEAD")))
                  (display (http-response 405 body: "Method Not Allowed") out))
                 (else
                  (let ((response (serve-file decoded-path doc-root)))
                    (display response out))))))))
      (close-input-port in)
      (close-output-port out)))

  ;; Server state
  (define *server-listener* #f)
  (define *server-running* #f)

  ;; Start HTTP server
  (define (http-serve #!key (port 8080) (doc-root "."))
    (let ((doc-root (normalize-pathname (make-pathname (current-directory) doc-root))))
      (printf "Cyberspace HTTP serving ~A on port ~A~%" doc-root port)
      (set! *server-listener* (tcp-listen port))
      (set! *server-running* #t)
      (let loop ()
        (when *server-running*
          (handle-exceptions exn
              (unless (not *server-running*)
                (printf "Accept error: ~A~%" (get-condition-property exn 'exn 'message))
                (loop))
            (let-values (((in out) (tcp-accept *server-listener*)))
              (handle-connection in out doc-root)
              (loop)))))))

  ;; Stop HTTP server
  (define (http-stop)
    (set! *server-running* #f)
    (when *server-listener*
      (tcp-close *server-listener*)
      (set! *server-listener* #f))
    (print "HTTP server stopped"))

) ; end module
