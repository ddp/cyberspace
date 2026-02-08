;;; SPKI Scheme - Automated Enrollment with Capability Election
;;; Library of Cyberspace - Chez Port
;;;
;;; Automates the enrollment process using capability-based master election.
;;; "Most capable wins the realm" - nodes exchange hardware info, elect
;;; the most capable (!mobile preferred) as master.
;;;
;;; Uses mDNS (via mdns.sls) for local network discovery.
;;; See mdns.sls header for mDNS/Bonjour/dns-sd terminology.
;;;
;;; Protocol:
;;;   1. Nodes discover each other via mDNS (Bonjour on macOS)
;;;   2. Exchange hardware introspection (includes mobile flag)
;;;   3. Compute capability scores (mobile penalized 10x)
;;;   4. Most capable node becomes master
;;;   5. Master generates realm key, issues certificates
;;;   6. Compute dynamic scaling factors for gossip
;;;
;;; Design:
;;;   - Prefer !mobile (servers/desktops over laptops)
;;;   - Normalize to capable (scaling relative to master)
;;;
;;; Ported from auto-enroll.scm.
;;; Copyright (c) 2026 Yoyodyne. See LICENSE.

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
    ;; Verbosity
    *realm-verbose*
    realm-verbose!
    ;; Testing support
    reset-enrollment-state!)

  (import (except (rnrs) flush-output-port find)
          (only (chezscheme)
                printf format void
                flush-output-port
                with-output-to-string)
          (cyberspace chicken-compatibility chicken)
          (cyberspace chicken-compatibility tcp)
          (cyberspace chicken-compatibility thread)
          (cyberspace enroll)
          (cyberspace capability)
          (cyberspace mdns)
          (except (cyberspace gossip) announce-presence)
          (cyberspace crypto-ffi)
          (cyberspace os)
          (cyberspace vault))

  ;; ============================================================
  ;; Constants
  ;; ============================================================

  (define *discovery-port* 7656)      ; capability exchange port
  (define *discovery-timeout* 10)     ; seconds to wait for peers
  (define *election-delay* 2)         ; seconds after discovery before election

  ;; ============================================================
  ;; State
  ;; ============================================================

  (define *realm-verbose-box* (vector #f))  ; verbose logging (default off)
  (define-syntax *realm-verbose*
    (identifier-syntax
      [id (vector-ref *realm-verbose-box* 0)]
      [(set! id val) (vector-set! *realm-verbose-box* 0 val)]))
  (define *realm-master* #f)          ; master node name (or #f, legacy)
  (define *realm-members* '())        ; list of (name . hardware)
  (define *scaling-factors* #f)       ; computed scaling factors
  (define *my-role* #f)               ; 'master or 'member

  ;; This node's identity
  (define *my-name* #f)               ; this node's name
  (define *my-pubkey* #f)             ; this node's public key
  (define *my-privkey* #f)            ; this node's private key (for signing)

  ;; Join listener state (any member can run this)
  (define *join-listener* #f)         ; TCP listener socket
  (define *join-listener-thread* #f)  ; listener thread
  (define *join-running* #f)          ; listener running flag

  ;; Pending membership proposals (for voting, future)
  (define *pending-proposals* '())    ; list of (name timestamp proposer)

  ;; ============================================================
  ;; Master-Side Join Listener
  ;; ============================================================

  (define (start-join-listener name . rest)
    "Start listening for join requests. Any realm member can do this.

     name: this node's name
     Optional keywords: port: N, keypair: (pub priv)

     Any member can accept new nodes. New membership gets gossiped.

     Example (founding a new realm):
       (start-join-listener 'fluffy)

     Example (existing member, already has keys):
       (start-join-listener 'starlight 'keypair: (list my-pub my-priv))"

    (let ((port (get-key rest 'port: *discovery-port*))
          (keypair (get-key rest 'keypair: #f)))

      (when *join-running*
        (stop-join-listener))

      ;; Set up identity
      (set! *my-name* name)
      (let ((kp (or keypair (ed25519-keypair))))
        (set! *my-pubkey* (car kp))
        (set! *my-privkey* (cadr kp)))

      ;; Determine role based on realm state
      (cond
        ;; No realm exists yet - we're founding it
        ((null? *realm-members*)
         (set! *realm-master* name)
         (set! *my-role* 'master)
         (let ((my-hw (introspect-hardware)))
           (set! *realm-members* `((,name . ,my-hw)))
           (set! *scaling-factors* (compute-scaling-factor *realm-members*)))
         ;; Store self-signed membership cert (Memo-050)
         (let ((cert (create-enrollment-cert name *my-pubkey* *my-privkey*
                                              'role: 'master)))
           (store-membership-cert! cert)))

        ;; Already a member - just starting/restarting listener
        ((assq name *realm-members*)
         (unless *my-role*
           (set! *my-role* 'member)))

        ;; Not a member yet but realm exists (shouldn't happen via this path)
        (else
         (set! *my-role* 'member)))

      ;; Start TCP listener
      (set! *join-listener* (tcp-listen port))
      (set! *join-running* #t)

      ;; Register with Bonjour so others can discover us
      (bonjour-register name port)

      (when *realm-verbose*
        (printf "[join-listener] Listening for join requests on port ~a~%" port))

      ;; Start listener thread
      (set! *join-listener-thread*
        (thread-start!
          (make-thread
            (lambda ()
              (join-listener-loop)))))

      `(join-listener-started
        (name ,name)
        (port ,port)
        (members ,(length *realm-members*)))))

  (define (stop-join-listener)
    "Stop listening for join requests."
    (set! *join-running* #f)
    ;; Unregister from Bonjour
    (bonjour-unregister)
    (when *join-listener*
      (guard (exn [#t (void)])
        (tcp-close *join-listener*))
      (set! *join-listener* #f))
    (when *join-listener-thread*
      (guard (exn [#t (void)])
        (thread-terminate! *join-listener-thread*))
      (set! *join-listener-thread* #f))
    (when *realm-verbose*
      (printf "[join-listener] Stopped~%"))
    'stopped)

  (define (join-listener-loop)
    "Accept and handle incoming join requests."
    (let loop ()
      (when (and *join-running* *join-listener*)
        (guard (exn [#t
          ;; Log but continue on errors
          (thread-sleep! 0.5)
          (loop)])

          (let-values (((in out) (tcp-accept *join-listener*)))
            (thread-start!
              (make-thread
                (lambda ()
                  (guard (exn [#t
                    (when *realm-verbose*
                      (printf "[join-listener] Error: ~a~%"
                              (if (message-condition? exn)
                                  (condition-message exn)
                                  "unknown")))])
                    (handle-join-connection in out))
                  (enrollment-close in out))))
            (loop))))))

  (define (handle-join-connection in out)
    "Handle one incoming connection (join request or capability exchange)."
    (let ((request (enrollment-receive in)))
      (cond
        ;; Capability exchange (for discovery phase)
        ((and (pair? request) (eq? (car request) 'capability-exchange))
         (let* ((fields (cdr request))
                (peer-name (cadr (assq 'name fields)))
                (peer-hw (cadr (assq 'hardware fields))))
           (when *realm-verbose*
             (printf "[join-listener] Capability exchange with: ~a~%" peer-name))
           ;; Respond with our capabilities
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
                            ;; Generate temporary pubkey if not provided
                            (car (ed25519-keypair))))
                (reason (and (assq 'reason fields) (cadr (assq 'reason fields)))))

           (when *realm-verbose*
             (printf "[join-listener] Join request from: ~a~%" node-name)
             (printf "[join-listener]   Hardware: ~a cores, ~a GB RAM, mobile: ~a~%"
                     (cadr (assq 'cores (cdr node-hw)))
                     (cadr (assq 'memory-gb (cdr node-hw)))
                     (cadr (assq 'mobile (cdr node-hw))))
             (when reason
               (printf "[join-listener]   Reason: ~a~%" reason)))

           ;; Check if joiner is more capable than current master (handoff check)
           (let* ((master-hw (cdr (assq *realm-master* *realm-members*)))
                  (comparison (compare-capabilities master-hw node-hw)))
             (if (and (eq? *my-role* 'master)
                      (eq? comparison 'second))
                 ;; Joiner is more capable - hand off master role
                 (handle-master-handoff node-name node-hw pubkey out)

                 ;; Normal join - existing logic
                 (begin
                   ;; Add to realm members
                   (set! *realm-members*
                     (cons (cons node-name node-hw) *realm-members*))

                   ;; Recompute scaling factors
                   (set! *scaling-factors* (compute-scaling-factor *realm-members*))

                   ;; Create enrollment certificate (any member can sign)
                   (let ((cert (create-enrollment-cert
                                 node-name pubkey *my-privkey*
                                 'role: 'full)))

                     (when *realm-verbose*
                       (printf "[join-listener] Approved ~a, issuing certificate~%" node-name)
                       (printf "[join-listener] Membership will be gossiped to realm~%"))

                     ;; Send acceptance with sponsoring member info
                     (enrollment-send out
                       `(join-accepted
                         (certificate ,cert)
                         (scaling ,*scaling-factors*)
                         (master ,*realm-master*)
                         (sponsor ,*my-name*)
                         (sponsor-pubkey ,*my-pubkey*)
                         (members ,(length *realm-members*))
                         (member-list ,(map car *realm-members*))))))))))

        ;; Invalid request
        (else
         (printf "[join-listener] Invalid request: ~a~%" request)
         (enrollment-send out
           `(join-rejected
             (reason "Invalid request format")))))))

  (define (handle-master-handoff new-master-name new-master-hw new-master-pubkey out)
    "Hand off master role to a more capable joining node."
    (let ((old-master *realm-master*))
      ;; 1. Update local state
      (set! *realm-master* new-master-name)
      (set! *my-role* 'member)

      ;; 2. Add new master to members
      (set! *realm-members*
        (cons (cons new-master-name new-master-hw) *realm-members*))

      ;; 3. Recompute scaling (new master becomes reference)
      (set! *scaling-factors* (compute-scaling-factor *realm-members*))

      ;; 4. Send handoff message
      (enrollment-send out
        `(master-handoff
          (new-master ,new-master-name)
          (old-master ,old-master)
          (old-master-pubkey ,*my-pubkey*)
          (members ,(map car *realm-members*))
          (member-hardware ,*realm-members*)
          (scaling ,*scaling-factors*)
          (timestamp ,(current-seconds))))

      ;; 5. Log transition
      (printf "[master-handoff] ~a -> ~a (more capable)~%" old-master new-master-name)

      ;; 6. Reconfigure gossip for member role
      (let ((gossip-cfg (configure-gossip-from-scaling *scaling-factors*)))
        (configure-from-scaling!
          (cdr (assq 'my-scale gossip-cfg))
          (cdr (assq 'effective-capacity *scaling-factors*))
          (cdr (assq 'batch-size gossip-cfg))
          (cdr (assq 'gossip-interval gossip-cfg))))))

  ;; ============================================================
  ;; Main Entry: Auto-Enroll a Realm
  ;; ============================================================

  (define (auto-enroll-realm name . rest)
    "Automatically discover peers and establish a realm.
     Most capable (!mobile preferred) becomes master.

     name: this node's name (symbol)
     Optional keyword: timeout: N (default 10)

     Returns: realm configuration with master and scaling factors"

    (let ((timeout (get-key rest 'timeout: *discovery-timeout*)))

      (when *realm-verbose*
        (printf "~%[auto-enroll] Starting realm discovery as '~a'...~%" name))

      ;; Step 1: Gather our hardware info
      (let ((my-hw (introspect-hardware)))
        (when *realm-verbose*
          (printf "[auto-enroll] Hardware: ~a cores, ~a GB RAM, mobile: ~a~%"
                  (cadr (assq 'cores (cdr my-hw)))
                  (cadr (assq 'memory-gb (cdr my-hw)))
                  (cadr (assq 'mobile (cdr my-hw)))))

        ;; Step 2: Discover peers and exchange capabilities
        (let ((members (discover-and-elect name my-hw 'timeout: timeout)))

          (if (null? members)
              ;; No peers found - we are the sole master
              (begin
                (printf "[auto-enroll] No peers found. Establishing single-node realm.~%")
                (set! *realm-master* name)
                (set! *my-role* 'master)
                (set! *realm-members* `((,name . ,my-hw)))
                (set! *scaling-factors* (compute-scaling-factor *realm-members*))

                ;; Configure gossip for single node (default settings)
                (configure-from-scaling! 1.0 1.0 100 30)
                (printf "[auto-enroll] Gossip configured: interval=30s, batch=100~%")

                (make-realm-result name 'master *realm-members* *scaling-factors*))

              ;; Peers found - run election
              (let-values (((winner score all-scores) (elect-master members)))
                (printf "[auto-enroll] Election results:~%")
                (for-each (lambda (s)
                            (printf "  ~a: ~a~a~%"
                                    (car s)
                                    (cdr s)
                                    (if (eq? (car s) winner) " <- WINNER" "")))
                          all-scores)

                (set! *realm-master* winner)
                (set! *realm-members* members)
                (set! *my-role* (if (eq? winner name) 'master 'node))
                (set! *scaling-factors* (compute-scaling-factor members))

                ;; Configure gossip from scaling factors
                (let ((gossip-cfg (configure-gossip-from-scaling *scaling-factors*)))
                  (configure-from-scaling!
                    (cdr (assq 'my-scale gossip-cfg))
                    (cdr (assq 'effective-capacity *scaling-factors*))
                    (cdr (assq 'batch-size gossip-cfg))
                    (cdr (assq 'gossip-interval gossip-cfg)))
                  (printf "[auto-enroll] Gossip configured: interval=~as, batch=~a~%"
                          (cdr (assq 'gossip-interval gossip-cfg))
                          (cdr (assq 'batch-size gossip-cfg))))

                (printf "[auto-enroll] Master: ~a (this node: ~a)~%" winner *my-role*)
                (make-realm-result winner *my-role* members *scaling-factors*)))))))

  (define (make-realm-result master role members scaling)
    "Build realm configuration result"
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

  (define (join-realm name master-host . rest)
    "Join an existing realm by connecting to master.

     name: this node's name
     master-host: hostname/IP of realm master
     Optional keywords: port: N, reason: str

     Returns: enrollment result with certificate and keypair"

    (let ((port (get-key rest 'port: *discovery-port*))
          (reason (get-key rest 'reason: #f)))

      (when *realm-verbose*
        (printf "[join-realm] Connecting to master at ~a:~a...~%" master-host port))

      (let* ((my-hw (introspect-hardware))
             ;; Generate keypair for this node
             (keypair (ed25519-keypair))
             (pubkey (car keypair))
             (privkey (cadr keypair)))

        (when *realm-verbose*
          (printf "[join-realm] Generated keypair for ~a~%" name)
          (printf "[join-realm] Hardware: ~a cores, ~a GB RAM, mobile: ~a~%"
                  (cadr (assq 'cores (cdr my-hw)))
                  (cadr (assq 'memory-gb (cdr my-hw)))
                  (cadr (assq 'mobile (cdr my-hw)))))

        (guard (exn [#t
          (printf "[join-realm] Failed to connect: ~a~%"
                  (if (message-condition? exn)
                      (condition-message exn)
                      "unknown"))
          `((status . error)
            (message . "Could not connect to master"))])

          (let-values (((in out) (tcp-connect master-host port)))
            (dynamic-wind
              (lambda () (void))
              (lambda ()
                ;; Send join request with hardware and pubkey
                (when *realm-verbose*
                  (printf "[join-realm] Sending join request...~%"))
                (enrollment-send out
                  `(join-request
                    (name ,name)
                    (hardware ,my-hw)
                    (pubkey ,pubkey)
                    (timestamp ,(current-seconds))
                    ,@(if reason `((reason ,reason)) '())))

                ;; Wait for response
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

                       ;; Update local state
                       (set! *my-name* name)
                       (set! *my-pubkey* pubkey)
                       (set! *my-privkey* privkey)
                       (set! *my-role* 'member)
                       (set! *realm-master* master)
                       (set! *scaling-factors* scaling)

                       ;; Initialize member list from response
                       (when member-list
                         (set! *realm-members*
                           (map (lambda (n) (cons n #f)) member-list))
                         ;; Add ourselves with hardware
                         (set! *realm-members*
                           (cons (cons name my-hw) *realm-members*)))

                       ;; Configure gossip from scaling
                       (let ((gossip-cfg (configure-gossip-from-scaling scaling)))
                         (configure-from-scaling!
                           (cdr (assq 'my-scale gossip-cfg))
                           (cdr (assq 'effective-capacity scaling))
                           (cdr (assq 'batch-size gossip-cfg))
                           (cdr (assq 'gossip-interval gossip-cfg)))
                         (printf "[join-realm] Gossip configured: interval=~as, batch=~a~%"
                                 (cdr (assq 'gossip-interval gossip-cfg))
                                 (cdr (assq 'batch-size gossip-cfg))))

                       (printf "[join-realm] Joined realm! Sponsor: ~a, Members: ~a~%"
                               sponsor member-count)

                       ;; Store membership cert (Memo-050)
                       (store-membership-cert! cert)

                       ;; Auto-start our own join listener (any member can accept joins)
                       (printf "[join-realm] Starting own listener (any member can sponsor joins)~%")
                       (start-join-listener name 'keypair: (list pubkey privkey))

                       `((status . joined)
                         (master . ,master)
                         (sponsor . ,sponsor)
                         (certificate . ,cert)
                         (scaling . ,scaling)
                         (pubkey . ,pubkey)
                         (privkey . ,privkey))))

                    ;; Master handoff - we're more capable, assume master role
                    ((and (pair? response)
                          (eq? (car response) 'master-handoff))
                     (let* ((fields (cdr response))
                            (old-master (cadr (assq 'old-master fields)))
                            (member-hardware (cadr (assq 'member-hardware fields)))
                            (scaling (cadr (assq 'scaling fields))))

                       ;; Assume master role
                       (set! *my-name* name)
                       (set! *my-pubkey* pubkey)
                       (set! *my-privkey* privkey)
                       (set! *my-role* 'master)
                       (set! *realm-master* name)
                       (set! *realm-members* member-hardware)
                       (set! *scaling-factors* scaling)

                       ;; Create self-signed master cert
                       (let ((cert (create-enrollment-cert name pubkey privkey
                                                            'role: 'master)))
                         (store-membership-cert! cert))

                       ;; Configure gossip from scaling (as new master)
                       (let ((gossip-cfg (configure-gossip-from-scaling scaling)))
                         (configure-from-scaling!
                           (cdr (assq 'my-scale gossip-cfg))
                           (cdr (assq 'effective-capacity scaling))
                           (cdr (assq 'batch-size gossip-cfg))
                           (cdr (assq 'gossip-interval gossip-cfg)))
                         (printf "[join-realm] Gossip configured: interval=~as, batch=~a~%"
                                 (cdr (assq 'gossip-interval gossip-cfg))
                                 (cdr (assq 'batch-size gossip-cfg))))

                       ;; Start listening as new master
                       (start-join-listener name 'keypair: (list pubkey privkey))

                       (printf "[join-realm] Became master (more capable than ~a)~%" old-master)

                       `((status . master-handoff)
                         (role . master)
                         (old-master . ,old-master)
                         (scaling . ,scaling))))

                    ;; Rejected or unknown response
                    (else
                     (printf "[join-realm] Join rejected: ~a~%" response)
                     `((status . rejected)
                       (response . ,response))))))
              (lambda ()
                (enrollment-close in out))))))))

  ;; ============================================================
  ;; Discovery and Election
  ;; ============================================================

  (define (discover-and-elect my-name my-hw . rest)
    "Discover peers on local network via Bonjour and collect their capabilities.

     Returns: list of (name . hardware) pairs including self"

    (let ((timeout (get-key rest 'timeout: *discovery-timeout*)))

      (when *realm-verbose*
        (printf "[discover] Browsing Bonjour for _cyberspace._tcp services...~%"))

      ;; Use Bonjour to find peers
      (let ((services (bonjour-browse timeout))
            (discovered '()))

        ;; For each discovered service, connect and exchange capabilities
        (for-each
          (lambda (svc)
            (let ((svc-name (car svc))
                  (host (cadr svc))
                  (port (caddr svc)))
              (when (and host port
                         (not (equal? svc-name (symbol->string my-name))))
                (printf "[discover] Found peer via Bonjour: ~a at ~a:~a~%" svc-name host port)
                (guard (exn [#t
                  (printf "[discover] Could not exchange capabilities with ~a: ~a~%"
                          svc-name
                          (if (message-condition? exn)
                              (condition-message exn)
                              "?"))])
                  ;; Connect and exchange hardware info
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
                          (printf "[discover] Got capabilities from ~a (mobile: ~a)~%"
                                  peer-name
                                  (cadr (assq 'mobile (cdr peer-hw))))
                          (set! discovered
                            (cons (cons peer-name peer-hw) discovered))))))))))
          services)

        ;; Return all members including self
        (cons (cons my-name my-hw) discovered))))

  ;; ============================================================
  ;; Gossip Configuration from Scaling
  ;; ============================================================

  (define (configure-gossip-from-scaling scaling)
    "Configure gossip daemon parameters based on scaling factors.

     Returns: gossip configuration alist

     Uses scaling to determine:
       - Gossip interval (less capable nodes sync less often)
       - Batch sizes (proportional to capability)
       - Replication targets"

    (let* ((my-scale (or (assq-ref (cdr (assq 'members scaling)) *my-role*)
                         1.0))
           (effective (cdr (assq 'effective-capacity scaling)))
           (replication (cdr (assq 'recommended-replication scaling))))

      ;; Base interval is 30s, scale inversely with capability
      ;; More capable nodes sync more often
      (let* ((base-interval 30)
             (my-interval (exact
                           (round (/ base-interval (max my-scale 0.1)))))
             ;; Batch size scales with capability
             (base-batch 10)
             (my-batch (exact
                        (round (* base-batch my-scale effective))))
             ;; Connection limit based on member count
             (max-connections (min 5 replication)))

        `((gossip-interval . ,(min 300 (max 10 my-interval)))
          (batch-size . ,(min 500 (max 10 my-batch)))
          (max-connections . ,max-connections)
          (replication-target . ,replication)
          (my-scale . ,my-scale)))))

  (define (assq-ref alist key)
    "Get value from alist or #f"
    (let ((pair (assq key alist)))
      (and pair (cdr pair))))

  ;; ============================================================
  ;; Status
  ;; ============================================================

  (define (realm-status)
    "Get current realm status"
    `((master . ,*realm-master*)
      (role . ,*my-role*)
      (member-count . ,(length *realm-members*))
      (scaling . ,*scaling-factors*)))

  (define (enrollment-status)
    "Get enrollment status"
    (if *realm-master*
        `((enrolled . #t)
          (master . ,*realm-master*)
          (role . ,*my-role*))
        '((enrolled . #f))))

  (define (auto-enroll-status)
    "Return status of auto-enroll services for introspection."
    `((join-listener-active . ,*join-running*)
      (join-listener-port . ,(if *join-listener* *discovery-port* #f))
      (my-name . ,*my-name*)
      (my-role . ,*my-role*)
      (realm-master . ,*realm-master*)
      (member-count . ,(length *realm-members*))
      (verbose . ,*realm-verbose*)))

  (define (realm-verbose! . rest)
    "Enable/disable verbose realm logging."
    (let ((on (if (null? rest) #t (car rest))))
      (set! *realm-verbose* on)
      (flush-output-port (current-output-port))
      (if on "realm verbose on" "realm verbose off")))

  ;; ============================================================
  ;; Testing Support
  ;; ============================================================

  (define (reset-enrollment-state!)
    "Reset all enrollment state. Used for testing in single-process scenarios."
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

  ;; Register cleanup hook (runs on exit)
  ;; stop-join-listener already calls bonjour-unregister
  (register-cleanup-hook! 'auto-enroll stop-join-listener)

) ;; end library
