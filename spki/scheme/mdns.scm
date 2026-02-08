;;; SPKI Scheme - Local Network Discovery (mDNS/Bonjour)
;;;
;;; Provides local network discovery for node enrollment (Memo-044).
;;;
;;; Terminology (see Memo-044 for details):
;;;   mDNS      - Multicast DNS protocol (RFC 6762)
;;;   DNS-SD    - DNS Service Discovery layer (RFC 6763)
;;;   Bonjour   - Apple's implementation of mDNS + DNS-SD
;;;   dns-sd    - macOS command-line tool for Bonjour operations
;;;
;;; This module uses "mDNS" as the generic term for the capability.
;;; Procedure names use "bonjour-*" since we call Apple's dns-sd tool.
;;; Portable implementations would use Avahi on Linux.
;;;
;;; Service type: _cyberspace._tcp
;;;
;;; Protocol:
;;;   1. Listener registers _cyberspace._tcp service via dns-sd
;;;   2. Joining nodes browse for _cyberspace._tcp services
;;;   3. Connect to discovered hosts for enrollment
;;;   4. Certificate exchange via TCP

(module mdns
  (;; Constants
   mdns-port
   enrollment-port
   cyberspace-service
   ;; Bonjour registration (listener side)
   bonjour-register
   bonjour-unregister
   cleanup-stale-bonjour
   ;; Bonjour discovery (joiner side)
   bonjour-browse
   bonjour-resolve
   ;; Legacy announcement (node side)
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
   *mdns-verbose*)

  (import scheme
          (chicken base)
          (chicken io)
          (chicken port)    ; with-output-to-string, with-input-from-string
          (chicken format)
          (chicken tcp)
          (chicken blob)
          (chicken time)
          (chicken process)           ; process, process-wait
          (chicken process-context)
          (chicken file)              ; file-exists?, directory-exists?, etc.
          (chicken condition)
          (chicken string)            ; string-split
          srfi-1      ; list utilities
          srfi-13     ; string-contains, string-trim-both
          srfi-18     ; threads
          srfi-4      ; u8vectors
          os)         ; session-stat!, register-cleanup-hook!

  ;; ============================================================
  ;; Constants
  ;; ============================================================

  ;; Standard mDNS multicast address and port
  ;; (We use broadcast for simplicity in this minimal implementation)
  (define mdns-port 5353)

  ;; Our enrollment service port
  (define enrollment-port 7654)

  ;; Service type for cyberspace realm discovery
  (define cyberspace-service "_cyberspace._tcp")

  ;; Announcement interval (seconds)
  (define announce-interval 2)

  ;; PID file for tracking child processes
  (define bonjour-pid-file ".vault/pids/bonjour")

  ;; ============================================================
  ;; PID File Management
  ;; ============================================================

  (define (ensure-pids-dir)
    "Create .vault/pids directory if needed"
    (unless (directory-exists? ".vault/pids")
      (when (directory-exists? ".vault")
        (create-directory ".vault/pids"))))

  (define (write-pid-file path pid)
    "Write PID to file for tracking"
    (ensure-pids-dir)
    (when (directory-exists? ".vault/pids")
      (with-output-to-file path
        (lambda () (write pid) (newline)))))

  (define (read-pid-file path)
    "Read PID from file, or #f if not found"
    (if (file-exists? path)
        (handle-exceptions exn #f
          (with-input-from-file path read))
        #f))

  (define (remove-pid-file path)
    "Remove PID file"
    (when (file-exists? path)
      (delete-file path)))

  (define (pid-alive? pid)
    "Check if process with given PID is still running"
    (handle-exceptions exn #f
      (receive (p normal status) (process-wait pid #t)  ; nohang = #t
        (not p))))  ; #f if process exited, pid if still running

  (define (cleanup-stale-bonjour)
    "Kill stale Bonjour process from previous session if found"
    (let ((old-pid (read-pid-file bonjour-pid-file)))
      (when old-pid
        (handle-exceptions exn #f
          (process-signal old-pid))
        (remove-pid-file bonjour-pid-file))))

  ;; ============================================================
  ;; Internal State
  ;; ============================================================

  ;; Active announcement thread
  (define *announcement-thread* #f)
  (define *announcement-running* #f)

  ;; Active listener
  (define *listener* #f)
  (define *listener-running* #f)

  ;; Bonjour registration process
  (define *bonjour-pid* #f)

  ;; Verbose logging (controls Bonjour lifecycle messages)
  (define *mdns-verbose* #f)

  ;; ============================================================
  ;; Bonjour Registration (via dns-sd)
  ;; ============================================================

  (define (bonjour-register name #!key (port 7656))
    "Register a _cyberspace._tcp service via Bonjour.
     name: service instance name (e.g., 'fluffy')
     port: TCP port the service listens on

     Returns: pid of dns-sd process (or #f on failure)"
    (cleanup-stale-bonjour)  ; Kill orphaned process from previous session
    (bonjour-unregister)     ; Clean up any existing registration in this session
    (let ((name-str (if (symbol? name) (symbol->string name) name)))
      (handle-exceptions exn
        (begin
          (printf "[bonjour] Registration failed: ~a~n"
                  (get-condition-property exn 'exn 'message "unknown"))
          #f)
        ;; dns-sd -R <name> <type> <domain> <port>
        ;; Use process-run instead of process* - no pipes means dns-sd won't
        ;; exit prematurely due to pipe handling issues
        (let ((pid (process-run "/usr/bin/dns-sd"
                                (list "-R" name-str cyberspace-service "local" (number->string port)))))
          (set! *bonjour-pid* pid)
          (write-pid-file bonjour-pid-file pid)  ; Persist for crash recovery
          (when *mdns-verbose*
            (printf "[bonjour] Registered '~a' on ~a port ~a (pid ~a)~n" name-str cyberspace-service port pid))
          pid))))

  (define (bonjour-unregister)
    "Stop Bonjour service registration"
    (when *bonjour-pid*
      (handle-exceptions exn #f
        (process-signal *bonjour-pid*))
      (set! *bonjour-pid* #f)
      (remove-pid-file bonjour-pid-file)))

  ;; ============================================================
  ;; Bonjour Discovery (via dns-sd)
  ;; ============================================================

  (define (bonjour-browse #!key (timeout 5) (self #f))
    "Browse for _cyberspace._tcp services on local network.
     timeout: seconds to wait for responses
     self: our own service name to skip during resolve (avoids wasted resolve)

     Returns: list of (name host port) for discovered services"
    (let ((results '())
          (deadline (+ (current-seconds) timeout)))
      (handle-exceptions exn
        (begin
          ;; dns-sd exiting is normal (timeout, no peers) - only log real errors
          (let ((msg (get-condition-property exn 'exn 'message "")))
            (when (and (not (string-contains msg "abnormal"))
                       (not (string-contains msg "process"))
                       (> (string-length msg) 0))
              (printf "[bonjour] Browse error: ~a~n" msg)))
          '())
        ;; dns-sd -B <type> <domain> - browse for services
        (let-values (((stdout stdin pid stderr)
                      (process* "/usr/bin/dns-sd"
                                (list "-B" cyberspace-service "local"))))
          (close-output-port stdin)
          (when *mdns-verbose*
            (printf "[bonjour] Browse started (pid ~a)~n" pid))
          ;; Read output for timeout seconds
          (let loop ()
            (when (and (< (current-seconds) deadline)
                       (char-ready? stdout))
              (let ((line (read-line stdout)))
                (when (and (string? line) (not (eof-object? line)))
                  ;; Parse: "Timestamp  A/R  Flags  IF  Domain  Type  Name"
                  ;; We want lines with "Add" that have our service type
                  (when (and (string-contains line "Add")
                             (string-contains line "_cyberspace"))
                    (let ((parts (string-split line)))
                      (when (>= (length parts) 7)
                        (let ((name (list-ref parts 6)))
                          (unless (assoc name results)
                            (when *mdns-verbose*
                              (printf "[bonjour] Found: ~a~n" name))
                            (set! results (cons (list name #f #f) results)))))))
                  (loop))))
            (when (< (current-seconds) deadline)
              (thread-sleep! 0.1)
              (loop)))
          ;; Clean up - wrap close-input-port to avoid "abnormal process exit"
          (handle-exceptions exn #f
            (process-signal pid)
            (when *mdns-verbose*
              (printf "[bonjour] Browse stopped (pid ~a)~n" pid))
            (close-input-port stdout)
            (close-input-port stderr))))
      ;; Resolve each discovered service (skip self)
      (let ((self-str (and self (if (symbol? self) (symbol->string self) self))))
        (filter-map
          (lambda (entry)
            (cond
              ((and self-str (string-contains (car entry) self-str))
               (when *mdns-verbose*
                 (printf "[bonjour] Skipping self: ~a~n" (car entry)))
               #f)
              (else (bonjour-resolve (car entry)))))
          results))))

  (define (bonjour-resolve name #!key (timeout 3))
    "Resolve a Bonjour service name to host and port.
     Returns: (name host port) or #f"
    (handle-exceptions exn
      (begin
        (when *mdns-verbose*
          (printf "[bonjour] Resolve failed for ~a: ~a~n"
                  name (get-condition-property exn 'exn 'message "unknown")))
        #f)
      ;; dns-sd -L <name> <type> <domain>
      (let-values (((stdout stdin pid stderr)
                    (process* "/usr/bin/dns-sd"
                              (list "-L" name cyberspace-service "local"))))
        (close-output-port stdin)
        (when *mdns-verbose*
          (printf "[bonjour] Resolve started for ~a (pid ~a)~n" name pid))
        (let ((deadline (+ (current-seconds) timeout))
              (host #f)
              (port #f))
          (let loop ()
            (when (and (< (current-seconds) deadline)
                       (not (and host port)))
              (when (char-ready? stdout)
                (let ((line (read-line stdout)))
                  (when (and (string? line) (not (eof-object? line)))
                    ;; Look for "can be reached at <host>:<port>"
                    (let ((reach-pos (string-contains line "can be reached at")))
                      (when reach-pos
                        (let* ((after (substring line (+ reach-pos 18)))
                               (parts (string-split after ":")))
                          (when (>= (length parts) 2)
                            (set! host (string-trim-both (car parts)))
                            (set! port (string->number
                                        (car (string-split (cadr parts)))))))))
                    (loop))))
              (thread-sleep! 0.1)
              (loop)))
          ;; Clean up - wrap everything so "abnormal process exit" from
          ;; close-input-port (triggered by process-wait on killed child)
          ;; doesn't discard resolved host/port values
          (handle-exceptions exn #f
            (process-signal pid)
            (when *mdns-verbose*
              (printf "[bonjour] Resolve stopped (pid ~a)~n" pid))
            (close-input-port stdout)
            (close-input-port stderr))
          (if (and host port)
              (list name host port)
              #f)))))

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
      (begin
        (when *mdns-verbose*
          (printf "[enrollment-receive] Error: ~a~n"
                  (get-condition-property exn 'exn 'message "unknown"))
          (flush-output))
        #f)
      (let ((data (read in)))
        (when (and *mdns-verbose* (eof-object? data))
          (printf "[enrollment-receive] Got EOF~n")
          (flush-output))
        data)))

  (define (enrollment-close in out)
    "Close enrollment connection"
    (handle-exceptions exn #f
      (when in (close-input-port in)))
    (handle-exceptions exn #f
      (when out (close-output-port out))))

  ;; ============================================================
  ;; Lifecycle Management
  ;; ============================================================

  (define (mdns-shutdown!)
    "Shutdown all mDNS services. Called on REPL exit."
    (bonjour-unregister)
    (stop-listening)
    (stop-announcement))

  (define (mdns-status)
    "Return status of mDNS services for introspection."
    `((bonjour-registered . ,(if *bonjour-pid* *bonjour-pid* #f))
      (listener-active . ,*listener-running*)
      (announcement-active . ,*announcement-running*)))

  ;; Register cleanup hook (runs on exit)
  (register-cleanup-hook! 'mdns mdns-shutdown!)

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
