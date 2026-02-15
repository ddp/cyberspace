;;; mdns.sls - Local Network Discovery (mDNS/Bonjour) (Memo-044)
;;;
;;; Provides local network discovery for node enrollment.
;;; Uses "mDNS" as the generic term; procedure names use "bonjour-*"
;;; since we call Apple's dns-sd tool.
;;;
;;; Service type: _cyberspace._tcp

(library (cyberspace mdns)
  (export
    ;; Constants
    mdns-port
    enrollment-port
    cyberspace-service
    ;; Bonjour registration
    bonjour-register
    bonjour-unregister
    cleanup-stale-bonjour
    ;; Bonjour discovery
    bonjour-browse
    bonjour-resolve
    ;; Legacy announcement
    announce-enrollment
    stop-announcement
    ;; Discovery (master side)
    listen-for-enrollments
    stop-listening
    ;; TCP enrollment channel
    enrollment-accept
    enrollment-connect
    enrollment-send
    enrollment-receive
    enrollment-close
    ;; Lifecycle
    mdns-shutdown!
    mdns-status
    ;; Verbosity
    mdns-verbose?
    mdns-verbose!)

  (import (rnrs)
          (only (chezscheme)
                printf format void
                with-output-to-string with-input-from-string
                file-directory? mkdir
                system open-process-ports process
                current-transcoder
                fork-thread sleep make-time
                time-second current-time
                parameterize)
          (cyberspace tcp)
          (cyberspace os))

  ;; ============================================================
  ;; Inlined helpers
  ;; ============================================================

  (define (current-seconds) (time-second (current-time)))

  (define (string-contains s1 s2)
    (let ((len1 (string-length s1))
          (len2 (string-length s2)))
      (if (> len2 len1) #f
          (let loop ((i 0))
            (cond ((> (+ i len2) len1) #f)
                  ((string=? s2 (substring s1 i (+ i len2))) i)
                  (else (loop (+ i 1))))))))

  (define (string-trim-both s)
    (let* ((len (string-length s))
           (start (let loop ((i 0))
                    (if (or (= i len) (not (char-whitespace? (string-ref s i)))) i
                        (loop (+ i 1)))))
           (end (let loop ((i (- len 1)))
                  (if (or (< i start) (not (char-whitespace? (string-ref s i)))) (+ i 1)
                      (loop (- i 1))))))
      (substring s start end)))

  (define (string-split str sep-char)
    (let ((len (string-length str)))
      (let loop ((i 0) (start 0) (acc '()))
        (cond
          ((= i len)
           (reverse (if (= start i) acc (cons (substring str start i) acc))))
          ((char=? (string-ref str i) sep-char)
           (loop (+ i 1) (+ i 1)
                 (if (= start i) acc (cons (substring str start i) acc))))
          (else (loop (+ i 1) start acc))))))

  (define (filter-map proc lst)
    (let loop ((l lst) (acc '()))
      (if (null? l) (reverse acc)
          (let ((v (proc (car l))))
            (loop (cdr l) (if v (cons v acc) acc))))))

  (define (directory-exists? path)
    (and (file-exists? path) (file-directory? path)))

  (define (read-line port)
    (get-line port))

  ;; ============================================================
  ;; Constants
  ;; ============================================================

  (define mdns-port 5353)
  (define enrollment-port 7654)
  (define cyberspace-service "_cyberspace._tcp")
  (define announce-interval 2)
  (define bonjour-pid-file ".vault/pids/bonjour")

  ;; ============================================================
  ;; PID File Management
  ;; ============================================================

  (define (ensure-pids-dir)
    (unless (directory-exists? ".vault/pids")
      (when (directory-exists? ".vault")
        (guard (exn [#t #f])
          (mkdir ".vault/pids" #o755)))))

  (define (write-pid-file path pid)
    (ensure-pids-dir)
    (when (directory-exists? ".vault/pids")
      (let ((p (open-file-output-port path
                 (file-options no-fail)
                 (buffer-mode block)
                 (native-transcoder))))
        (put-datum p pid)
        (newline p)
        (close-port p))))

  (define (read-pid-file path)
    (if (file-exists? path)
        (guard (exn [#t #f])
          (let ((p (open-file-input-port path
                     (file-options)
                     (buffer-mode block)
                     (native-transcoder))))
            (let ((v (get-datum p)))
              (close-port p)
              (if (eof-object? v) #f v))))
        #f))

  (define (remove-pid-file path)
    (when (file-exists? path)
      (delete-file path)))

  ;; ============================================================
  ;; Internal State
  ;; ============================================================

  (define *announcement-running* #f)
  (define *listener* #f)
  (define *listener-running* #f)
  (define *bonjour-pid* #f)
  (define *mdns-verbose* #f)

  (define (mdns-verbose?) *mdns-verbose*)
  (define (mdns-verbose! on) (set! *mdns-verbose* on))

  ;; ============================================================
  ;; Bonjour Registration (via dns-sd)
  ;; ============================================================

  (define (bonjour-register name . opts)
    (let ((port (let loop ((r opts))
                  (cond ((null? r) 7656)
                        ((and (eq? (car r) 'port:) (pair? (cdr r))) (cadr r))
                        (else (loop (cdr r)))))))
      (cleanup-stale-bonjour)
      (bonjour-unregister)
      (let ((name-str (if (symbol? name) (symbol->string name) name)))
        (guard (exn [#t
                     (printf "[bonjour] Registration failed: ~a~n"
                             (if (message-condition? exn)
                                 (condition-message exn) "unknown"))
                     #f])
          ;; Use system to run dns-sd in background
          (let ((cmd (format "/usr/bin/dns-sd -R ~a ~a local ~a &"
                             name-str cyberspace-service port)))
            (system cmd)
            (when *mdns-verbose*
              (printf "[bonjour] Registered '~a' on ~a port ~a~n"
                      name-str cyberspace-service port))
            #t)))))

  (define (bonjour-unregister)
    (when *bonjour-pid*
      (guard (exn [#t #f])
        (system (format "kill ~a 2>/dev/null" *bonjour-pid*)))
      (set! *bonjour-pid* #f)
      (remove-pid-file bonjour-pid-file)))

  (define (cleanup-stale-bonjour)
    (let ((old-pid (read-pid-file bonjour-pid-file)))
      (when old-pid
        (guard (exn [#t #f])
          (system (format "kill ~a 2>/dev/null" old-pid)))
        (remove-pid-file bonjour-pid-file))))

  ;; ============================================================
  ;; Bonjour Discovery (via dns-sd)
  ;; ============================================================

  (define (bonjour-browse . opts)
    (let ((timeout (let loop ((r opts))
                     (cond ((null? r) 5)
                           ((and (eq? (car r) 'timeout:) (pair? (cdr r))) (cadr r))
                           (else (loop (cdr r))))))
          (self (let loop ((r opts))
                  (cond ((null? r) #f)
                        ((and (eq? (car r) 'self:) (pair? (cdr r))) (cadr r))
                        (else (loop (cdr r)))))))
      (guard (exn [#t '()])
        ;; Run dns-sd -B with timeout
        (let ((cmd (format "timeout ~a /usr/bin/dns-sd -B ~a local 2>/dev/null"
                           timeout cyberspace-service)))
          (let-values (((to-stdin from-stdout from-stderr pid)
                        (open-process-ports cmd 'line (current-transcoder))))
            (close-port to-stdin)
            (let ((results '()))
              (let loop ()
                (let ((line (read-line from-stdout)))
                  (when (and (string? line) (not (eof-object? line)))
                    (when (and (string-contains line "Add")
                               (string-contains line "_cyberspace"))
                      (let ((parts (string-split line #\space)))
                        (when (>= (length parts) 7)
                          (let ((name (list-ref parts 6)))
                            (unless (assoc name results)
                              (when *mdns-verbose*
                                (printf "[bonjour] Found: ~a~n" name))
                              (set! results (cons (list name #f #f) results)))))))
                    (loop))))
              (guard (exn [#t #f])
                (close-port from-stdout)
                (close-port from-stderr))
              ;; Resolve discovered services (skip self)
              (let ((self-str (and self (if (symbol? self) (symbol->string self) self))))
                (filter-map
                  (lambda (entry)
                    (if (and self-str (string-contains (car entry) self-str))
                        #f
                        (bonjour-resolve (car entry))))
                  results))))))))

  (define (bonjour-resolve name . opts)
    (let ((timeout (let loop ((r opts))
                     (cond ((null? r) 3)
                           ((and (eq? (car r) 'timeout:) (pair? (cdr r))) (cadr r))
                           (else (loop (cdr r)))))))
      (guard (exn [#t #f])
        (let ((cmd (format "timeout ~a /usr/bin/dns-sd -L ~a ~a local 2>/dev/null"
                           timeout name cyberspace-service)))
          (let-values (((to-stdin from-stdout from-stderr pid)
                        (open-process-ports cmd 'line (current-transcoder))))
            (close-port to-stdin)
            (let ((host #f) (port #f))
              (let loop ()
                (when (not (and host port))
                  (let ((line (read-line from-stdout)))
                    (when (and (string? line) (not (eof-object? line)))
                      (let ((reach-pos (string-contains line "can be reached at")))
                        (when reach-pos
                          (let* ((after (substring line (+ reach-pos 18)
                                                  (string-length line)))
                                 (parts (string-split after #\:)))
                            (when (>= (length parts) 2)
                              (set! host (string-trim-both (car parts)))
                              (set! port (string->number
                                           (car (string-split (cadr parts) #\space))))))))
                      (loop)))))
              (guard (exn [#t #f])
                (close-port from-stdout)
                (close-port from-stderr))
              (if (and host port)
                  (list name host port)
                  #f)))))))

  ;; ============================================================
  ;; TCP Enrollment Channel
  ;; ============================================================

  (define (enrollment-accept listener)
    (guard (exn [#t (values #f #f)])
      (tcp-accept listener)))

  (define (enrollment-connect host port)
    (guard (exn [#t (values #f #f)])
      (tcp-connect host port)))

  (define (enrollment-send out data)
    (write data out)
    (newline out)
    (flush-output-port out))

  (define (enrollment-receive in)
    (guard (exn [#t #f])
      (let ((data (read in)))
        data)))

  (define (enrollment-close in out)
    (guard (exn [#t #f]) (when in (close-port in)))
    (guard (exn [#t #f]) (when out (close-port out))))

  ;; ============================================================
  ;; Announcement (Node Side)
  ;; ============================================================

  (define (make-announcement-packet name pubkey-b64)
    (with-output-to-string
      (lambda ()
        (write `(enrollment-request
                  (service ,cyberspace-service)
                  (name ,name)
                  (pubkey ,pubkey-b64)
                  (port ,enrollment-port)
                  (timestamp ,(current-seconds)))))))

  (define (announce-enrollment name pubkey-b64 . opts)
    (let ((port (let loop ((r opts))
                  (cond ((null? r) enrollment-port)
                        ((and (eq? (car r) 'port:) (pair? (cdr r))) (cadr r))
                        (else (loop (cdr r)))))))
      (when *announcement-running* (stop-announcement))
      (let ((listener (tcp-listen port)))
        (set! *announcement-running* #t)
        (fork-thread
          (lambda ()
            (let ((packet (make-announcement-packet name pubkey-b64)))
              (let loop ()
                (when *announcement-running*
                  (for-each
                    (lambda (host)
                      (guard (exn [#t #f])
                        (let-values (((in out) (tcp-connect host enrollment-port)))
                          (display packet out)
                          (close-port out)
                          (close-port in)
                          (session-stat! 'mdns-messages))))
                    (local-broadcast-targets))
                  (sleep (make-time 'time-duration 0 announce-interval))
                  (loop))))))
        listener)))

  (define (local-broadcast-targets)
    '("192.168.1.1" "192.168.0.1" "10.0.0.1" "172.16.0.1"))

  (define (stop-announcement)
    (set! *announcement-running* #f))

  ;; ============================================================
  ;; Discovery (Master Side)
  ;; ============================================================

  (define (listen-for-enrollments handler . opts)
    (let ((port (let loop ((r opts))
                  (cond ((null? r) enrollment-port)
                        ((and (eq? (car r) 'port:) (pair? (cdr r))) (cadr r))
                        (else (loop (cdr r)))))))
      (when *listener-running* (stop-listening))
      (let ((listener (tcp-listen port)))
        (set! *listener* listener)
        (set! *listener-running* #t)
        (fork-thread
          (lambda ()
            (let loop ()
              (when *listener-running*
                (guard (exn [#t
                             (display "[enroll] accept error") (newline)
                             (sleep (make-time 'time-duration 0 1))
                             (loop)])
                  (let-values (((in out) (tcp-accept listener)))
                    (display "[enroll] connection accepted") (newline)
                    (guard (exn [#t
                                 (display "[enroll] read error") (newline)
                                 (close-port in)
                                 (close-port out)])
                      (let ((data (get-string-all in)))
                        (close-port in)
                        (close-port out)
                        (when (and data (> (string-length data) 0))
                          (guard (exn [#t (display "[enroll] parse error") (newline)])
                            (let ((request (with-input-from-string data read)))
                              (session-stat! 'mdns-messages)
                              (when (and (pair? request)
                                         (eq? (car request) 'enrollment-request))
                                (let* ((fields (cdr request))
                                       (name (cadr (assq 'name fields)))
                                       (pubkey (cadr (assq 'pubkey fields)))
                                       (req-port (cadr (assq 'port fields))))
                                  (handler name pubkey "local" req-port))))))))))
                (loop)))))
        listener)))

  (define (stop-listening)
    (set! *listener-running* #f)
    (when *listener*
      (guard (exn [#t #f])
        (tcp-close *listener*))
      (set! *listener* #f)))

  ;; ============================================================
  ;; Lifecycle
  ;; ============================================================

  (define (mdns-shutdown!)
    (bonjour-unregister)
    (stop-listening)
    (stop-announcement))

  (define (mdns-status)
    `((bonjour-registered . ,(if *bonjour-pid* *bonjour-pid* #f))
      (listener-active . ,*listener-running*)
      (announcement-active . ,*announcement-running*)))

  ;; Register cleanup hook
  (register-cleanup-hook! 'mdns mdns-shutdown!)

) ;; end library
