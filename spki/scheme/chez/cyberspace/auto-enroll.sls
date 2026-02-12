;;; auto-enroll.sls - Automated Enrollment with Capability Election
;;; Library of Cyberspace - Chez Scheme Port
;;;
;;; Automates the enrollment process using capability-based master election.
;;; "Most capable wins the realm" - nodes exchange hardware info, elect
;;; the most capable (!mobile preferred) as master.
;;;
;;; Uses mDNS (via mdns.sls) for local network discovery.
;;;
;;; Protocol:
;;;   1. Nodes discover each other via mDNS (Bonjour on macOS)
;;;   2. Exchange hardware introspection (includes mobile flag)
;;;   3. Compute capability scores (mobile penalized 10x)
;;;   4. Most capable node becomes master
;;;   5. Master generates realm key, issues certificates
;;;   6. Compute dynamic scaling factors for gossip
;;;
;;; Ported from Chicken's auto-enroll.scm.
;;; Changes: module -> library, srfi-18 threads -> fork-thread,
;;;          thread-terminate! -> cooperative flags, #!key -> get-key,
;;;          handle-exceptions -> guard, thread-sleep! -> sleep.

(library (cyberspace auto-enroll)
  (export
    ;; Main entry points
    auto-enroll-realm
    join-realm
    ;; Master-side join listener
    start-join-listener
    stop-join-listener
    ;; Election
    discover-and-elect
    ;; Configuration
    configure-gossip-from-scaling
    ;; Status
    realm-status
    enrollment-status
    ;; Lifecycle
    auto-enroll-status
    ;; Persistence
    restore-realm-state
    reconnect-to-master
    ;; Verbosity
    realm-verbose?
    realm-verbose!
    ;; Diagnostics
    join-listener-diag
    ;; Testing support
    reset-enrollment-state!)

  (import (rnrs)
          (only (chezscheme)
                printf format
                fork-thread sleep make-time
                current-time time-second)
          (cyberspace enroll)
          (cyberspace capability)
          (cyberspace mdns)
          (except (cyberspace gossip) stop-announcement announce-presence)
          (cyberspace crypto-ffi)
          (cyberspace os)
          (cyberspace tcp)
          (only (cyberspace vault)
                store-membership-cert!
                store-enrollment-keypair! load-enrollment-keypair
                store-realm-state! load-realm-state
                realm-membership-cert cert-valid?)
          (cyberspace chicken-compatibility chicken))

  ;; ============================================================
  ;; Inlined Helpers
  ;; ============================================================

  (define (current-seconds) (time-second (current-time)))

  (define (flush) (flush-output-port (current-output-port)))

  ;; Use remp from (rnrs lists) instead of Chicken's remove

  ;; ============================================================
  ;; Constants
  ;; ============================================================

  (define *discovery-port* 7656)
  (define *discovery-timeout* 10)
  (define *election-delay* 2)

  ;; ============================================================
  ;; State
  ;; ============================================================

  (define *realm-verbose* #f)
  (define *realm-master* #f)
  (define *realm-members* '())
  (define *scaling-factors* #f)
  (define *my-role* #f)

  (define *my-name* #f)
  (define *my-pubkey* #f)
  (define *my-privkey* #f)

  (define *join-listener* #f)
  (define *join-running* #f)

  (define *join-in-progress* #f)
  (define *pending-proposals* '())

  ;; Accessors (R6RS: can't export set! variables)
  (define (realm-verbose?) *realm-verbose*)

  (define (realm-verbose! . rest)
    (let ((on (if (null? rest) #t (car rest))))
      (set! *realm-verbose* on)
      (mdns-verbose! on)
      (flush)
      (if on "realm verbose on" "realm verbose off")))

  ;; ============================================================
  ;; Realm State Persistence
  ;; ============================================================

  (define (save-realm-snapshot!)
    (when (and *realm-master* *my-name* *my-role*)
      (store-realm-state! *realm-master* *my-role* *my-name* *realm-members*)
      (when (and *my-pubkey* *my-privkey*)
        (store-enrollment-keypair! *my-pubkey* *my-privkey*))
      (when *realm-verbose*
        (printf "[realm] Saved realm snapshot: ~a role=~a master=~a~n"
                *my-name* *my-role* *realm-master*))))

  (define (restore-realm-state)
    (let ((state (load-realm-state))
          (keypair (load-enrollment-keypair))
          (cert (realm-membership-cert)))
      (if (and state keypair (cert-valid? cert))
          (let* ((fields (cdr state))
                 (master (cadr (assq 'master fields)))
                 (role (cadr (assq 'role fields)))
                 (my-name (cadr (assq 'my-name fields)))
                 (members (cadr (assq 'members fields))))
            (set! *my-name* my-name)
            (set! *my-role* role)
            (set! *realm-master* master)
            (set! *my-pubkey* (car keypair))
            (set! *my-privkey* (cadr keypair))
            (set! *realm-members*
              (map (lambda (n) (cons n #f)) members))
            (let ((my-hw (introspect-hardware)))
              (set! *realm-members*
                (cons (cons my-name my-hw)
                      (remp (lambda (m) (eq? (car m) my-name)) *realm-members*))))
            (set! *scaling-factors* (compute-scaling-factor *realm-members*))
            (when *realm-verbose*
              (printf "[realm] Restored: ~a role=~a master=~a members=~a~n"
                      my-name role master (length *realm-members*)))
            `((restored . #t)
              (name . ,my-name)
              (role . ,role)
              (master . ,master)
              (pubkey . ,*my-pubkey*)
              (privkey . ,*my-privkey*)))
          (begin
            (when *realm-verbose*
              (printf "[realm] Cannot restore: state=~a keys=~a cert-valid=~a~n"
                      (if state #t #f)
                      (if keypair #t #f)
                      (if (cert-valid? cert) #t #f)))
            #f))))

  (define (reconnect-to-master)
    (let ((master-name (and *realm-master* (symbol->string *realm-master*)))
          (max-retries 5)
          (backoff-schedule '(2 4 8 16 30)))
      (when master-name
        (fork-thread
          (lambda ()
            (let retry ((attempt 0))
              (if (>= attempt max-retries)
                  (begin
                    (printf "[realm] Master ~a unreachable after ~a retries, re-enrolling~n"
                            master-name max-retries)
                    (reset-enrollment-state!)
                    (let ((name (string->symbol (hostname))))
                      (start-join-listener name)
                      (auto-enroll-realm name)))
                  (begin
                    (when *realm-verbose*
                      (printf "[realm] Reconnect attempt ~a/~a for ~a~n"
                              (+ attempt 1) max-retries master-name))
                    (let ((resolved (guard (exn [#t #f])
                                     (bonjour-resolve master-name))))
                      (if resolved
                          (begin
                            (when *realm-verbose*
                              (printf "[realm] Found master ~a at ~a:~a~n"
                                      master-name (cadr resolved) (caddr resolved)))
                            (printf "[realm] Reconnected to master ~a~n" master-name))
                          (begin
                            (sleep (make-time 'time-duration 0
                                    (list-ref backoff-schedule
                                              (min attempt (- (length backoff-schedule) 1)))))
                            (retry (+ attempt 1)))))))))))))

  ;; ============================================================
  ;; Master-Side Join Listener
  ;; ============================================================

  (define (start-join-listener name . opts)
    (let ((port (get-key opts 'port: *discovery-port*))
          (keypair (get-key opts 'keypair: #f)))

      (when *join-running*
        (stop-join-listener))

      (set! *my-name* name)
      (let ((kp (or keypair (ed25519-keypair))))
        (set! *my-pubkey* (car kp))
        (set! *my-privkey* (cadr kp)))

      (cond
        ((null? *realm-members*)
         (set! *realm-master* name)
         (set! *my-role* 'master)
         (let ((my-hw (introspect-hardware)))
           (set! *realm-members* `((,name . ,my-hw)))
           (set! *scaling-factors* (compute-scaling-factor *realm-members*)))
         (let ((cert (create-enrollment-cert name *my-pubkey* *my-privkey* 'role: 'master)))
           (store-membership-cert! cert))
         (save-realm-snapshot!))

        ((assq name *realm-members*)
         (unless *my-role*
           (set! *my-role* 'member)))

        (else
         (set! *my-role* 'member)))

      (set! *join-listener* (tcp-listen port))
      (set! *join-running* #t)

      (bonjour-register name 'port: port)

      (when *realm-verbose*
        (printf "[join-listener] Listening for join requests on port ~a~n" port))

      (fork-thread
        (lambda ()
          (join-listener-loop)))

      `(join-listener-started
        (name ,name)
        (port ,port)
        (members ,(length *realm-members*)))))

  (define (stop-join-listener)
    (set! *join-running* #f)
    (bonjour-unregister)
    (when *join-listener*
      (guard (exn [#t #f])
        (tcp-close *join-listener*))
      (set! *join-listener* #f))
    (when *realm-verbose*
      (printf "[join-listener] Stopped~n"))
    'stopped)

  (define (join-listener-loop)
    (when *realm-verbose*
      (printf "[join-listener] Loop started, waiting for connections...~n")
      (flush))
    (let loop ()
      (when (and *join-running* *join-listener*)
        (guard (exn [#t
                     (printf "[join-listener] Accept error: ~a~n"
                             (if (message-condition? exn)
                                 (condition-message exn) "unknown"))
                     (flush)
                     (sleep (make-time 'time-duration 0 1))
                     (loop)])
          (let-values (((in out) (tcp-accept *join-listener*)))
            (when *realm-verbose*
              (printf "[join-listener] Connection accepted~n")
              (flush))
            (fork-thread
              (lambda ()
                (guard (exn [#t
                             (printf "[join-listener] Handler error: ~a~n"
                                     (if (message-condition? exn)
                                         (condition-message exn) "unknown"))])
                  (handle-join-connection in out))
                (enrollment-close in out)))
            (loop))))))

  (define (handle-join-connection in out)
    (when *realm-verbose*
      (printf "[join-handler] Reading request...~n")
      (flush))
    (let ((request (enrollment-receive in)))
      (when *realm-verbose*
        (printf "[join-handler] Got: ~a~n" (if (pair? request) (car request) request))
        (flush))
      (cond
        ;; Capability exchange
        ((and (pair? request) (eq? (car request) 'capability-exchange))
         (let* ((fields (cdr request))
                (peer-name (cadr (assq 'name fields)))
                (peer-hw (cadr (assq 'hardware fields))))
           (when *realm-verbose*
             (printf "[join-listener] Capability exchange with: ~a~n" peer-name))
           (let ((my-hw (introspect-hardware)))
             (enrollment-send out
               `(capability-response
                  (name ,*my-name*)
                  (hardware ,my-hw))))))

        ;; Join request
        ((and (pair? request) (eq? (car request) 'join-request))
         (let* ((fields (cdr request))
                (node-name (cadr (assq 'name fields)))
                (node-hw (cadr (assq 'hardware fields)))
                (pubkey (or (and (assq 'pubkey fields)
                                 (cadr (assq 'pubkey fields)))
                            (car (ed25519-keypair))))
                (reason (and (assq 'reason fields) (cadr (assq 'reason fields)))))

           (when *realm-verbose*
             (printf "[join-listener] Join request from: ~a~n" node-name)
             (printf "[join-listener]   Hardware: ~a cores, ~a GB RAM, mobile: ~a~n"
                     (cadr (assq 'cores (cdr node-hw)))
                     (cadr (assq 'memory-gb (cdr node-hw)))
                     (cadr (assq 'mobile (cdr node-hw))))
             (when reason
               (printf "[join-listener]   Reason: ~a~n" reason)))

           (let* ((master-hw (cdr (assq *realm-master* *realm-members*)))
                  (comparison (compare-capabilities master-hw node-hw)))
             (if (and (eq? *my-role* 'master)
                      (eq? comparison 'second))
                 (handle-master-handoff node-name node-hw pubkey out)
                 (begin
                   (set! *realm-members*
                     (cons (cons node-name node-hw) *realm-members*))
                   (set! *scaling-factors* (compute-scaling-factor *realm-members*))
                   (let ((cert (create-enrollment-cert
                                 node-name pubkey *my-privkey*
                                 'role: 'full)))
                     (when *realm-verbose*
                       (printf "[join-listener] Approved ~a, issuing certificate~n" node-name)
                       (printf "[join-listener] Membership will be gossiped to realm~n"))
                     (enrollment-send out
                       `(join-accepted
                         (certificate ,cert)
                         (scaling ,*scaling-factors*)
                         (master ,*realm-master*)
                         (sponsor ,*my-name*)
                         (sponsor-pubkey ,*my-pubkey*)
                         (members ,(length *realm-members*))
                         (member-list ,(map car *realm-members*))))
                     (save-realm-snapshot!)))))))

        ;; Invalid request
        (else
         (printf "[join-listener] Invalid request: ~a~n" request)
         (enrollment-send out
           `(join-rejected
             (reason "Invalid request format")))))))

  (define (handle-master-handoff new-master-name new-master-hw new-master-pubkey out)
    (let ((old-master *realm-master*))
      (set! *realm-master* new-master-name)
      (set! *my-role* 'member)
      (set! *realm-members*
        (cons (cons new-master-name new-master-hw) *realm-members*))
      (set! *scaling-factors* (compute-scaling-factor *realm-members*))
      (enrollment-send out
        `(master-handoff
          (new-master ,new-master-name)
          (old-master ,old-master)
          (old-master-pubkey ,*my-pubkey*)
          (members ,(map car *realm-members*))
          (member-hardware ,*realm-members*)
          (scaling ,*scaling-factors*)
          (timestamp ,(current-seconds))))
      (printf "[master-handoff] ~a -> ~a (more capable)~n" old-master new-master-name)
      (let ((gossip-cfg (configure-gossip-from-scaling *scaling-factors*)))
        (configure-from-scaling!
          (cdr (assq 'my-scale gossip-cfg))
          (cdr (assq 'effective-capacity *scaling-factors*))
          (cdr (assq 'batch-size gossip-cfg))
          (cdr (assq 'gossip-interval gossip-cfg))))
      (save-realm-snapshot!)))

  ;; ============================================================
  ;; Main Entry: Auto-Enroll a Realm
  ;; ============================================================

  (define (auto-enroll-realm name . opts)
    (let ((timeout (get-key opts 'timeout: *discovery-timeout*)))
      (if *join-in-progress*
          (begin
            (printf "[auto-enroll] Join operation already in progress~n")
            `((status . busy) (reason . "join in progress")))

          (begin
            (set! *join-in-progress* #t)
            (dynamic-wind
              (lambda () #f)
              (lambda ()
                (when *realm-verbose*
                  (printf "~n[auto-enroll] Starting realm discovery as '~a'...~n" name))
                (let ((my-hw (introspect-hardware)))
                  (when *realm-verbose*
                    (printf "[auto-enroll] Hardware: ~a cores, ~a GB RAM, mobile: ~a~n"
                            (cadr (assq 'cores (cdr my-hw)))
                            (cadr (assq 'memory-gb (cdr my-hw)))
                            (cadr (assq 'mobile (cdr my-hw)))))
                  (let ((members (discover-and-elect name my-hw 'timeout: timeout)))
                    (if (null? members)
                        (begin
                          (when *realm-verbose*
                            (printf "[auto-enroll] No peers found. Establishing single-node realm.~n"))
                          (set! *realm-master* name)
                          (set! *my-role* 'master)
                          (set! *realm-members* `((,name . ,my-hw)))
                          (set! *scaling-factors* (compute-scaling-factor *realm-members*))
                          (configure-from-scaling! 1.0 1.0 100 30)
                          (when *realm-verbose*
                            (printf "[auto-enroll] Gossip configured: interval=30s, batch=100~n"))
                          (save-realm-snapshot!)
                          (make-realm-result name 'master *realm-members* *scaling-factors*))

                        (let-values (((winner score all-scores) (elect-master members)))
                          (when *realm-verbose*
                            (printf "[auto-enroll] Election results:~n")
                            (for-each (lambda (s)
                                        (printf "  ~a: ~a~a~n"
                                                (car s)
                                                (cdr s)
                                                (if (eq? (car s) winner) " <- WINNER" "")))
                                      all-scores))
                          (set! *realm-master* winner)
                          (set! *realm-members* members)
                          (set! *my-role* (if (eq? winner name) 'master 'node))
                          (set! *scaling-factors* (compute-scaling-factor members))
                          (let ((gossip-cfg (configure-gossip-from-scaling *scaling-factors*)))
                            (configure-from-scaling!
                              (cdr (assq 'my-scale gossip-cfg))
                              (cdr (assq 'effective-capacity *scaling-factors*))
                              (cdr (assq 'batch-size gossip-cfg))
                              (cdr (assq 'gossip-interval gossip-cfg)))
                            (when *realm-verbose*
                              (printf "[auto-enroll] Gossip configured: interval=~as, batch=~a~n"
                                      (cdr (assq 'gossip-interval gossip-cfg))
                                      (cdr (assq 'batch-size gossip-cfg)))))
                          (when *realm-verbose*
                            (printf "[auto-enroll] Master: ~a (this node: ~a)~n" winner *my-role*))
                          (save-realm-snapshot!)
                          (make-realm-result winner *my-role* members *scaling-factors*))))))
              (lambda () (set! *join-in-progress* #f)))))))

  (define (make-realm-result master role members scaling)
    `((master . ,master)
      (role . ,role)
      (member-count . ,(length members))
      (members . ,(cdr (assq 'members scaling)))
      (reference-score . ,(cdr (assq 'reference-score scaling)))
      (effective-capacity . ,(cdr (assq 'effective-capacity scaling)))
      (recommended-replication . ,(cdr (assq 'recommended-replication scaling)))
      (scaling . ,scaling)))

  ;; ============================================================
  ;; Join Existing Realm
  ;; ============================================================

  (define (join-realm name master-host . opts)
    (let ((port (get-key opts 'port: *discovery-port*))
          (reason (get-key opts 'reason: #f)))

      (when *join-in-progress*
        (printf "[join-realm] Preempting background auto-enroll~n"))

      (set! *join-in-progress* #t)
      (dynamic-wind
        (lambda () #f)
        (lambda ()
          (when *realm-verbose*
            (printf "[join-realm] Connecting to master at ~a:~a...~n" master-host port))

          (let* ((my-hw (introspect-hardware))
                 (keypair (ed25519-keypair))
                 (pubkey (car keypair))
                 (privkey (cadr keypair)))

            (when *realm-verbose*
              (printf "[join-realm] Generated keypair for ~a~n" name)
              (printf "[join-realm] Hardware: ~a cores, ~a GB RAM, mobile: ~a~n"
                      (cadr (assq 'cores (cdr my-hw)))
                      (cadr (assq 'memory-gb (cdr my-hw)))
                      (cadr (assq 'mobile (cdr my-hw)))))

            (guard (exn [#t
                         (printf "[join-realm] Failed to connect: ~a~n"
                                 (if (message-condition? exn)
                                     (condition-message exn) "unknown"))
                         `((status . error)
                           (message . "Could not connect to master"))])

              (let-values (((in out) (tcp-connect master-host port)))
                (dynamic-wind
                  (lambda () #f)
                  (lambda ()
                    (when *realm-verbose*
                      (printf "[join-realm] Sending join request...~n"))
                    (enrollment-send out
                      `(join-request
                        (name ,name)
                        (hardware ,my-hw)
                        (pubkey ,pubkey)
                        (timestamp ,(current-seconds))
                        ,@(if reason `((reason ,reason)) '())))

                    (let ((response (enrollment-receive in)))
                      (cond
                        ;; Normal join acceptance
                        ((and (pair? response)
                              (eq? (car response) 'join-accepted))
                         (let* ((fields (cdr response))
                                (cert (cadr (assq 'certificate fields)))
                                (scaling (cadr (assq 'scaling fields)))
                                (master (and (assq 'master fields)
                                             (cadr (assq 'master fields))))
                                (sponsor (and (assq 'sponsor fields)
                                              (cadr (assq 'sponsor fields))))
                                (member-count (and (assq 'members fields)
                                                   (cadr (assq 'members fields))))
                                (member-list (and (assq 'member-list fields)
                                                  (cadr (assq 'member-list fields)))))

                           (set! *my-name* name)
                           (set! *my-pubkey* pubkey)
                           (set! *my-privkey* privkey)
                           (set! *my-role* 'member)
                           (set! *realm-master* master)
                           (set! *scaling-factors* scaling)

                           (when member-list
                             (set! *realm-members*
                               (map (lambda (n) (cons n #f)) member-list))
                             (set! *realm-members*
                               (cons (cons name my-hw) *realm-members*)))

                           (let ((gossip-cfg (configure-gossip-from-scaling scaling)))
                             (configure-from-scaling!
                               (cdr (assq 'my-scale gossip-cfg))
                               (cdr (assq 'effective-capacity scaling))
                               (cdr (assq 'batch-size gossip-cfg))
                               (cdr (assq 'gossip-interval gossip-cfg)))
                             (when *realm-verbose*
                               (printf "[join-realm] Gossip configured: interval=~as, batch=~a~n"
                                       (cdr (assq 'gossip-interval gossip-cfg))
                                       (cdr (assq 'batch-size gossip-cfg)))))

                           (printf "[join-realm] Joined realm! Sponsor: ~a, Members: ~a~n"
                                   sponsor member-count)

                           (store-membership-cert! cert)
                           (save-realm-snapshot!)

                           ;; Auto-start join listener
                           (when *realm-verbose*
                             (printf "[join-realm] Starting own listener (any member can sponsor joins)~n"))
                           (guard (exn [#t
                                        (when *realm-verbose*
                                          (printf "[join-realm] Listener start delayed~n"))
                                        (sleep (make-time 'time-duration 0 1))
                                        (guard (exn2 [#t
                                                      (when *realm-verbose*
                                                        (printf "[join-realm] Listener start failed~n"))])
                                          (start-join-listener name 'keypair: (list pubkey privkey)))])
                             (start-join-listener name 'keypair: (list pubkey privkey)))

                           `((status . joined)
                             (master . ,master)
                             (sponsor . ,sponsor)
                             (certificate . ,cert)
                             (scaling . ,scaling)
                             (pubkey . ,pubkey)
                             (privkey . ,privkey))))

                        ;; Master handoff
                        ((and (pair? response)
                              (eq? (car response) 'master-handoff))
                         (let* ((fields (cdr response))
                                (old-master (cadr (assq 'old-master fields)))
                                (member-hardware (cadr (assq 'member-hardware fields)))
                                (scaling (cadr (assq 'scaling fields))))

                           (set! *my-name* name)
                           (set! *my-pubkey* pubkey)
                           (set! *my-privkey* privkey)
                           (set! *my-role* 'master)
                           (set! *realm-master* name)
                           (set! *realm-members* member-hardware)
                           (set! *scaling-factors* scaling)

                           (let ((cert (create-enrollment-cert name pubkey privkey 'role: 'master)))
                             (store-membership-cert! cert))
                           (save-realm-snapshot!)

                           (let ((gossip-cfg (configure-gossip-from-scaling scaling)))
                             (configure-from-scaling!
                               (cdr (assq 'my-scale gossip-cfg))
                               (cdr (assq 'effective-capacity scaling))
                               (cdr (assq 'batch-size gossip-cfg))
                               (cdr (assq 'gossip-interval gossip-cfg)))
                             (when *realm-verbose*
                               (printf "[join-realm] Gossip configured: interval=~as, batch=~a~n"
                                       (cdr (assq 'gossip-interval gossip-cfg))
                                       (cdr (assq 'batch-size gossip-cfg)))))

                           (guard (exn [#t
                                        (when *realm-verbose*
                                          (printf "[join-realm] Listener start delayed~n"))
                                        (sleep (make-time 'time-duration 0 1))
                                        (guard (exn2 [#t
                                                      (when *realm-verbose*
                                                        (printf "[join-realm] Listener start failed~n"))])
                                          (start-join-listener name 'keypair: (list pubkey privkey)))])
                             (start-join-listener name 'keypair: (list pubkey privkey)))

                           (printf "[join-realm] Became master (more capable than ~a)~n" old-master)

                           `((status . master-handoff)
                             (role . master)
                             (old-master . ,old-master)
                             (scaling . ,scaling))))

                        ;; Rejected
                        (else
                         (printf "[join-realm] Join rejected: ~a~n" response)
                         `((status . rejected)
                           (response . ,response))))))
                  (lambda ()
                    (enrollment-close in out)))))))
        (lambda () (set! *join-in-progress* #f)))))

  ;; ============================================================
  ;; Discovery and Election
  ;; ============================================================

  (define (discover-and-elect my-name my-hw . opts)
    (let ((timeout (get-key opts 'timeout: *discovery-timeout*)))
      (when *realm-verbose*
        (printf "[discover] Browsing Bonjour for _cyberspace._tcp services...~n"))

      (let ((services (bonjour-browse 'timeout: timeout 'self: my-name))
            (discovered '()))

        (for-each
          (lambda (svc)
            (let ((svc-name (car svc))
                  (host (cadr svc))
                  (port (caddr svc)))
              (when (and host port
                         (not (equal? svc-name (symbol->string my-name))))
                (when *realm-verbose*
                  (printf "[discover] Found peer via Bonjour: ~a at ~a:~a~n" svc-name host port))
                (guard (exn [#t
                             (when *realm-verbose*
                               (printf "[discover] Could not exchange capabilities with ~a~n" svc-name))])
                  (let-values (((in out) (tcp-connect host port)))
                    (enrollment-send out
                      `(capability-exchange
                         (name ,my-name)
                         (hardware ,my-hw)))
                    (let ((response (enrollment-receive in)))
                      (enrollment-close in out)
                      (when (and (pair? response)
                                 (eq? (car response) 'capability-response))
                        (let* ((fields (cdr response))
                               (peer-name (cadr (assq 'name fields)))
                               (peer-hw (cadr (assq 'hardware fields))))
                          (when *realm-verbose*
                            (printf "[discover] Got capabilities from ~a (mobile: ~a)~n"
                                    peer-name
                                    (cadr (assq 'mobile (cdr peer-hw)))))
                          (set! discovered
                            (cons (cons peer-name peer-hw) discovered))))))))))
          services)

        (cons (cons my-name my-hw) discovered))))

  ;; ============================================================
  ;; Gossip Configuration from Scaling
  ;; ============================================================

  (define (assq-ref alist key)
    (let ((pair (assq key alist)))
      (and pair (cdr pair))))

  (define (configure-gossip-from-scaling scaling)
    (let* ((my-scale (or (assq-ref (cdr (assq 'members scaling)) *my-role*)
                         1.0))
           (effective (cdr (assq 'effective-capacity scaling)))
           (replication (cdr (assq 'recommended-replication scaling))))

      (let* ((base-interval 30)
             (my-interval (exact (round (/ base-interval (max my-scale 0.1)))))
             (base-batch 10)
             (my-batch (exact (round (* base-batch my-scale effective))))
             (max-connections (min 5 replication)))

        `((gossip-interval . ,(min 300 (max 10 my-interval)))
          (batch-size . ,(min 500 (max 10 my-batch)))
          (max-connections . ,max-connections)
          (replication-target . ,replication)
          (my-scale . ,my-scale)))))

  ;; ============================================================
  ;; Status
  ;; ============================================================

  (define (realm-status)
    `((master . ,*realm-master*)
      (role . ,*my-role*)
      (member-count . ,(length *realm-members*))
      (scaling . ,*scaling-factors*)))

  (define (enrollment-status)
    (if *realm-master*
        `((enrolled . #t)
          (master . ,*realm-master*)
          (role . ,*my-role*))
        '((enrolled . #f))))

  (define (auto-enroll-status)
    `((join-listener-active . ,*join-running*)
      (join-listener-port . ,(if *join-listener* *discovery-port* #f))
      (my-name . ,*my-name*)
      (my-role . ,*my-role*)
      (realm-master . ,*realm-master*)
      (member-count . ,(length *realm-members*))
      (verbose . ,*realm-verbose*)))

  ;; ============================================================
  ;; Diagnostics
  ;; ============================================================

  (define (join-listener-diag)
    (printf "~n=== Join Listener Diagnostics ===~n")
    (printf "  *join-running*:   ~a~n" *join-running*)
    (printf "  *join-listener*:  ~a~n" (if *join-listener* "active" "#f"))
    (printf "  *my-name*:        ~a~n" *my-name*)
    (printf "  *my-role*:        ~a~n" *my-role*)
    (printf "  *realm-master*:   ~a~n" *realm-master*)
    (printf "  *join-in-progress*: ~a~n" *join-in-progress*)
    (printf "  member-count:     ~a~n" (length *realm-members*))
    (printf "================================~n")
    (flush)
    `((join-running . ,*join-running*)
      (listener . ,(if *join-listener* 'active 'none))
      (name . ,*my-name*)
      (role . ,*my-role*)
      (master . ,*realm-master*)
      (join-in-progress . ,*join-in-progress*)))

  ;; ============================================================
  ;; Testing Support
  ;; ============================================================

  (define (reset-enrollment-state!)
    (stop-join-listener)
    (set! *realm-master* #f)
    (set! *realm-members* '())
    (set! *scaling-factors* #f)
    (set! *my-role* #f)
    (set! *my-name* #f)
    (set! *my-pubkey* #f)
    (set! *my-privkey* #f)
    (set! *pending-proposals* '())
    'reset)

  ;; Register cleanup hook
  (register-cleanup-hook! 'auto-enroll
    (lambda ()
      (save-realm-snapshot!)
      (stop-join-listener)))

) ;; end library
