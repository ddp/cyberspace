;;; SPKI Scheme - Local Network Discovery (mDNS-lite)
;;;
;;; Provides local network discovery for node enrollment (Memo-044).
;;; Uses UDP broadcast for announcements and TCP for enrollment protocol.
;;;
;;; This is a minimal mDNS-compatible implementation focused on
;;; the enrollment use case. For full mDNS, use dns-sd/avahi.
;;;
;;; Protocol:
;;;   1. New node broadcasts enrollment request via UDP multicast
;;;   2. Master sees broadcast, displays verification words
;;;   3. Human verifies words match on both screens
;;;   4. Master approves, sends SPKI certificate via TCP
;;;   5. Node stores certificate, enrollment complete

(module mdns
  (;; Constants
   mdns-port
   enrollment-port
   cyberspace-service
   ;; Announcement (node side)
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
   enrollment-close)

  (import scheme
          (chicken base)
          (chicken io)
          (chicken port)    ; with-output-to-string, with-input-from-string
          (chicken format)
          (chicken tcp)
          (chicken blob)
          (chicken time)
          (chicken process-context)
          (chicken condition)
          srfi-1      ; list utilities
          srfi-18     ; threads
          srfi-4      ; u8vectors
          os)         ; for session-stat!

  ;; ============================================================
  ;; Constants
  ;; ============================================================

  ;; Standard mDNS multicast address and port
  ;; (We use broadcast for simplicity in this minimal implementation)
  (define mdns-port 5353)

  ;; Our enrollment service port
  (define enrollment-port 7654)

  ;; Service type for cyberspace enrollment
  (define cyberspace-service "_cyberspace-enroll._tcp")

  ;; Announcement interval (seconds)
  (define announce-interval 2)

  ;; ============================================================
  ;; Internal State
  ;; ============================================================

  ;; Active announcement thread
  (define *announcement-thread* #f)
  (define *announcement-running* #f)

  ;; Active listener
  (define *listener* #f)
  (define *listener-running* #f)

  ;; ============================================================
  ;; UDP Announcement (Node Side)
  ;; ============================================================

  (define (make-announcement-packet name pubkey-b64)
    "Create announcement packet as s-expression"
    (with-output-to-string
      (lambda ()
        (write `(enrollment-request
                  (service ,cyberspace-service)
                  (name ,name)
                  (pubkey ,pubkey-b64)
                  (port ,enrollment-port)
                  (timestamp ,(current-seconds)))))))

  (define (announce-enrollment name pubkey-b64 #!key (port enrollment-port))
    "Begin announcing enrollment request on local network.
     Returns the TCP listener for enrollment responses.

     name: proposed node name (symbol or string)
     pubkey-b64: base64-encoded public key"

    ;; Stop any existing announcement
    (when *announcement-running*
      (stop-announcement))

    ;; Create TCP listener for enrollment responses
    (let ((listener (tcp-listen port)))

      ;; Start announcement thread
      (set! *announcement-running* #t)
      (set! *announcement-thread*
        (thread-start!
          (make-thread
            (lambda ()
              (let ((packet (make-announcement-packet name pubkey-b64)))
                ;; Announce via TCP connection attempts to well-known port
                ;; (Master will have TCP listener on enrollment-port)
                (let loop ()
                  (when *announcement-running*
                    (handle-exceptions exn
                      #f  ; Ignore connection failures (master not ready)
                      ;; Try to connect to common local addresses
                      (for-each
                        (lambda (host)
                          (handle-exceptions exn #f
                            (let-values (((in out) (tcp-connect host enrollment-port)))
                              (display packet out)
                              (close-output-port out)
                              (close-input-port in)
                              (session-stat! 'mdns-messages))))
                        (local-broadcast-targets)))
                    (thread-sleep! announce-interval)
                    (loop))))))))

      listener))

  (define (local-broadcast-targets)
    "Get list of local network addresses to try.
     For local enrollment, we try common patterns."
    ;; In practice, we'd scan the local subnet
    ;; For now, common local addresses
    '("192.168.1.1" "192.168.0.1" "10.0.0.1" "172.16.0.1"))

  (define (stop-announcement)
    "Stop announcing enrollment request"
    (set! *announcement-running* #f)
    (when *announcement-thread*
      (handle-exceptions exn #f
        (thread-terminate! *announcement-thread*))
      (set! *announcement-thread* #f)))

  ;; ============================================================
  ;; Discovery (Master Side)
  ;; ============================================================

  (define (listen-for-enrollments handler #!key (port enrollment-port))
    "Listen for enrollment requests on local network.

     handler: called with (name pubkey-b64 host port) for each request
     Returns: listener object (use stop-listening to stop)"

    (when *listener-running*
      (stop-listening))

    (let ((listener (tcp-listen port)))
      (set! *listener* listener)
      (set! *listener-running* #t)

      ;; Start listener thread
      (thread-start!
        (make-thread
          (lambda ()
            (let loop ()
              (when *listener-running*
                (handle-exceptions exn
                  (begin
                    (print "[enroll] accept error: " (get-condition-property exn 'exn 'message "?"))
                    (thread-sleep! 0.1)
                    (loop))
                  (let-values (((in out) (tcp-accept listener)))
                    (print "[enroll] connection accepted")
                    (handle-exceptions exn
                      (begin
                        (print "[enroll] read error: " (get-condition-property exn 'exn 'message "?"))
                        (close-input-port in)
                        (close-output-port out))
                      (let ((data (read-string #f in)))
                        (print "[enroll] received " (if data (string-length data) 0) " bytes")
                        (close-input-port in)
                        (close-output-port out)
                        (when (and data (> (string-length data) 0))
                          (handle-exceptions exn
                            (print "[enroll] parse error: " (get-condition-property exn 'exn 'message "?"))
                            (let ((request (with-input-from-string data read)))
                              (print "[enroll] parsed request: " (if (pair? request) (car request) request))
                              (session-stat! 'mdns-messages)  ; Track received mDNS message
                              (when (and (pair? request)
                                        (eq? (car request) 'enrollment-request))
                                (let* ((fields (cdr request))
                                       (name (cadr (assq 'name fields)))
                                       (pubkey (cadr (assq 'pubkey fields)))
                                       (req-port (cadr (assq 'port fields))))
                                  (print "[enroll] calling handler for " name)
                                  (handler name pubkey "local" req-port))))))))
                    ;; Yield to other threads (cooperative threading)
                    (thread-yield!)
                    (loop))))))))

      listener))

  (define (stop-listening)
    "Stop listening for enrollment requests"
    (set! *listener-running* #f)
    (when *listener*
      (handle-exceptions exn #f
        (tcp-close *listener*))
      (set! *listener* #f)))

  ;; ============================================================
  ;; TCP Enrollment Channel
  ;; ============================================================

  (define (enrollment-accept listener)
    "Accept an enrollment connection.
     Returns: (values input-port output-port) or #f on timeout"
    (handle-exceptions exn
      (values #f #f)
      (tcp-accept listener)))

  (define (enrollment-connect host port)
    "Connect to master for enrollment.
     Returns: (values input-port output-port) or #f on failure"
    (handle-exceptions exn
      (values #f #f)
      (tcp-connect host port)))

  (define (enrollment-send out data)
    "Send enrollment data (s-expression)"
    (write data out)
    (newline out)
    (flush-output out))

  (define (enrollment-receive in)
    "Receive enrollment data (s-expression)"
    (handle-exceptions exn
      #f
      (read in)))

  (define (enrollment-close in out)
    "Close enrollment connection"
    (handle-exceptions exn #f
      (when in (close-input-port in)))
    (handle-exceptions exn #f
      (when out (close-output-port out))))

) ;; end module

;;;
;;; Example: Node requesting enrollment
;;;
;;;   (import mdns)
;;;
;;;   ;; Start announcing
;;;   (let ((listener (announce-enrollment 'starlight "base64-pubkey...")))
;;;     ;; Wait for master to connect with certificate
;;;     (let-values (((in out) (enrollment-accept listener)))
;;;       (when in
;;;         (let ((response (enrollment-receive in)))
;;;           (when (eq? (car response) 'enrollment-approved)
;;;             (display "Enrolled!\n")
;;;             (let ((cert (cadr (assq 'certificate (cdr response)))))
;;;               ;; Store certificate...
;;;               ))))))
;;;
;;; Example: Master approving enrollment
;;;
;;;   (import mdns)
;;;
;;;   (listen-for-enrollments
;;;     (lambda (name pubkey host port)
;;;       (printf "Enrollment request from ~a~n" name)
;;;       (printf "Pubkey: ~a~n" pubkey)
;;;       ;; Display verification words, get human approval
;;;       ;; If approved, connect back and send certificate
;;;       ))
;;;
