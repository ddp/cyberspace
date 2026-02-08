;;; SPKI Scheme - Local Network Discovery (mDNS/Bonjour)
;;; Library of Cyberspace - Chez Port
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
;;;
;;; Port note: Process management uses shell-command from os.sls.
;;; TCP uses the tcp.sls compat layer for (chicken tcp) API.
;;; Threads require Chez's native threading (fork-thread).

(library (cyberspace mdns)
  (export
    ;; Constants
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
    ;; TCP enrollment channel
    enrollment-accept
    enrollment-connect
    enrollment-send
    enrollment-receive
    enrollment-close
    ;; Lifecycle
    mdns-shutdown!
    mdns-status)

  (import (except (rnrs) with-input-from-file with-output-to-file file-exists? delete-file flush-output-port find)
          (only (chezscheme)
                printf format void
                with-output-to-string
                with-input-from-file with-output-to-file
                file-exists? delete-file
                open-process-ports native-transcoder
                process
                sleep
                fork-thread
                flush-output-port)
          (cyberspace chicken-compatibility chicken)
          (cyberspace chicken-compatibility tcp)
          (cyberspace os))

  ;; ============================================================
  ;; Constants
  ;; ============================================================

  ;; Standard mDNS multicast address and port
  (define mdns-port 5353)

  ;; Our enrollment service port
  (define enrollment-port 7654)

  ;; Service type for cyberspace realm discovery
  (define cyberspace-service "_cyberspace._tcp")

  ;; PID file for tracking child processes
  (define bonjour-pid-file ".vault/pids/bonjour")

  ;; ============================================================
  ;; PID File Management
  ;; ============================================================

  (define (ensure-pids-dir)
    "Create .vault/pids directory if needed"
    (unless (file-exists? ".vault/pids")
      (when (file-exists? ".vault")
        (shell-command "mkdir -p .vault/pids"))))

  (define (write-pid-file path pid)
    "Write PID to file for tracking"
    (ensure-pids-dir)
    (when (file-exists? ".vault/pids")
      (with-output-to-file path
        (lambda () (write pid) (newline)))))

  (define (read-pid-file path)
    "Read PID from file, or #f if not found"
    (if (file-exists? path)
        (guard (exn (#t #f))
          (with-input-from-file path read))
        #f))

  (define (remove-pid-file path)
    "Remove PID file"
    (when (file-exists? path)
      (delete-file path)))

  (define (kill-process pid)
    "Send SIGTERM to process"
    (guard (exn (#t #f))
      (shell-command (string-append "kill " (number->string pid)))))

  (define (cleanup-stale-bonjour)
    "Kill stale Bonjour process from previous session if found"
    (let ((old-pid (read-pid-file bonjour-pid-file)))
      (when old-pid
        (kill-process old-pid)
        (remove-pid-file bonjour-pid-file))))

  ;; ============================================================
  ;; Internal State
  ;; ============================================================

  ;; Bonjour registration process
  (define *bonjour-pid* #f)

  ;; Listener state
  (define *listener* #f)
  (define *listener-running* #f)

  ;; ============================================================
  ;; Bonjour Registration (via dns-sd)
  ;; ============================================================

  (define (bonjour-register name . rest)
    "Register a _cyberspace._tcp service via Bonjour.
     name: service instance name (e.g., 'fluffy')
     Optional: port (default 7656)

     Returns: pid of dns-sd process (or #f on failure)"
    (let ((port (if (null? rest) 7656 (car rest))))
      (cleanup-stale-bonjour)
      (bonjour-unregister)
      (let ((name-str (if (symbol? name) (symbol->string name) name)))
        (guard (exn (#t
                     (printf "[bonjour] Registration failed: ~a~%"
                             (condition-message exn))
                     #f))
          ;; Launch dns-sd in background via shell
          (let* ((cmd (string-append
                        "/usr/bin/dns-sd -R "
                        name-str " " cyberspace-service " local "
                        (number->string port) " &"))
                 ;; Get PID of background process
                 (pid-str (shell-command
                            (string-append cmd " echo $!"))))
            (let ((pid (and pid-str (string->number pid-str))))
              (when pid
                (set! *bonjour-pid* pid)
                (write-pid-file bonjour-pid-file pid)
                (printf "[bonjour] Registered '~a' on ~a port ~a (pid ~a)~%"
                        name-str cyberspace-service port pid))
              pid))))))

  (define (bonjour-unregister)
    "Stop Bonjour service registration"
    (when *bonjour-pid*
      (kill-process *bonjour-pid*)
      (set! *bonjour-pid* #f)
      (remove-pid-file bonjour-pid-file)))

  ;; ============================================================
  ;; Bonjour Discovery (via dns-sd)
  ;; ============================================================

  (define (bonjour-browse . rest)
    "Browse for _cyberspace._tcp services on local network.
     Optional: timeout in seconds (default 5)

     Returns: list of (name host port) for discovered services"
    (let ((timeout (if (null? rest) 5 (car rest))))
      (guard (exn (#t '()))
        ;; Use dns-sd with timeout
        (let* ((cmd (string-append
                      "timeout " (number->string timeout)
                      " /usr/bin/dns-sd -B " cyberspace-service
                      " local 2>/dev/null || true"))
               (lines (shell-lines cmd)))
          ;; Parse output for "Add" lines with _cyberspace
          (let ((results '()))
            (for-each
              (lambda (line)
                (when (and (string-contains line "Add")
                           (string-contains line "_cyberspace"))
                  (let ((parts (string-split line)))
                    (when (>= (length parts) 7)
                      (let ((name (list-ref parts 6)))
                        (unless (assoc name results)
                          (set! results (cons (list name #f #f) results))))))))
              (or lines '()))
            ;; Resolve each discovered service
            (map (lambda (entry)
                   (let ((resolved (bonjour-resolve (car entry))))
                     (if resolved resolved entry)))
                 results))))))

  (define (bonjour-resolve name . rest)
    "Resolve a Bonjour service name to host and port.
     Returns: (name host port) or #f"
    (let ((timeout (if (null? rest) 3 (car rest))))
      (guard (exn (#t #f))
        (let* ((cmd (string-append
                      "timeout " (number->string timeout)
                      " /usr/bin/dns-sd -L "
                      name " " cyberspace-service
                      " local 2>/dev/null || true"))
               (lines (shell-lines cmd))
               (host #f)
               (port #f))
          ;; Look for "can be reached at" in output
          (when lines
            (for-each
              (lambda (line)
                (let ((reach-pos (string-contains line "can be reached at")))
                  (when reach-pos
                    (let* ((after (substring line (+ reach-pos 18)
                                            (string-length line)))
                           (parts (string-split after ":")))
                      (when (>= (length parts) 2)
                        (set! host (string-trim-both (car parts)))
                        (set! port (string->number
                                     (car (string-split (cadr parts))))))))))
              lines))
          (if (and host port)
              (list name host port)
              #f)))))

  ;; ============================================================
  ;; TCP Enrollment Channel
  ;; ============================================================

  (define (enrollment-accept listener)
    "Accept an enrollment connection.
     Returns: (values input-port output-port) or (values #f #f)"
    (guard (exn (#t (values #f #f)))
      (tcp-accept listener)))

  (define (enrollment-connect host port)
    "Connect to master for enrollment.
     Returns: (values input-port output-port) or (values #f #f)"
    (guard (exn (#t (values #f #f)))
      (tcp-connect host port)))

  (define (enrollment-send out data)
    "Send enrollment data (s-expression)"
    (write data out)
    (newline out)
    (flush-output-port out))

  (define (enrollment-receive in)
    "Receive enrollment data (s-expression)"
    (guard (exn (#t #f))
      (read in)))

  (define (enrollment-close in out)
    "Close enrollment connection"
    (guard (exn (#t (void)))
      (when in (close-port in)))
    (guard (exn (#t (void)))
      (when out (close-port out))))

  ;; ============================================================
  ;; Lifecycle Management
  ;; ============================================================

  (define (mdns-shutdown!)
    "Shutdown all mDNS services. Called on REPL exit."
    (bonjour-unregister)
    (when *listener*
      (guard (exn (#t (void)))
        (tcp-close *listener*))
      (set! *listener* #f)
      (set! *listener-running* #f)))

  (define (mdns-status)
    "Return status of mDNS services for introspection."
    `((bonjour-registered . ,(if *bonjour-pid* *bonjour-pid* #f))
      (listener-active . ,*listener-running*)))

  ;; Register cleanup hook (runs on exit)
  (register-cleanup-hook! 'mdns mdns-shutdown!)

) ;; end library
