;;; SPKI Scheme - Automated Enrollment with Capability Election
;;;
;;; Automates the enrollment process using capability-based master election.
;;; "Most capable wins the realm" - nodes exchange hardware info, elect
;;; the most capable (!mobile preferred) as master.
;;;
;;; Protocol:
;;;   1. Nodes discover each other via mDNS
;;;   2. Exchange hardware introspection (includes mobile flag)
;;;   3. Compute capability scores (mobile penalized 10x)
;;;   4. Most capable node becomes master
;;;   5. Master generates realm key, issues certificates
;;;   6. Compute dynamic scaling factors for gossip
;;;
;;; Design:
;;;   - Prefer !mobile (servers/desktops over laptops)
;;;   - Normalize to capable (scaling relative to master)

(module auto-enroll
  (;; Main entry points
   auto-enroll-realm
   join-realm
   ;; Election
   discover-and-elect
   ;; Configuration
   configure-gossip-from-scaling
   ;; Status
   realm-status
   enrollment-status)

  (import scheme
          (chicken base)
          (chicken io)
          (chicken port)
          (chicken format)
          (chicken tcp)
          (chicken time)
          (chicken condition)
          srfi-1      ; list utilities
          srfi-18     ; threads
          enroll
          capability
          mdns
          gossip      ; for configure-from-scaling!
          crypto-ffi)

  ;; ============================================================
  ;; Constants
  ;; ============================================================

  (define *discovery-port* 7656)      ; capability exchange port
  (define *discovery-timeout* 10)     ; seconds to wait for peers
  (define *election-delay* 2)         ; seconds after discovery before election

  ;; ============================================================
  ;; State
  ;; ============================================================

  (define *realm-master* #f)          ; master node name (or #f)
  (define *realm-members* '())        ; list of (name . hardware)
  (define *scaling-factors* #f)       ; computed scaling factors
  (define *my-role* #f)               ; 'master or 'node

  ;; ============================================================
  ;; Main Entry: Auto-Enroll a Realm
  ;; ============================================================

  (define (auto-enroll-realm name #!key (timeout *discovery-timeout*))
    "Automatically discover peers and establish a realm.
     Most capable (!mobile preferred) becomes master.

     name: this node's name (symbol)
     timeout: seconds to wait for peer discovery

     Returns: realm configuration with master and scaling factors

     Example:
       (auto-enroll-realm 'fluffy)
       => ((master . fluffy)
           (role . master)
           (members . ((fluffy . 1.0) (starlight . 0.032)))
           (scaling . ...))"

    (printf "~n[auto-enroll] Starting realm discovery as '~a'...~n" name)

    ;; Step 1: Gather our hardware info
    (let ((my-hw (introspect-hardware)))
      (printf "[auto-enroll] Hardware: ~a cores, ~a GB RAM, mobile: ~a~n"
              (cadr (assq 'cores (cdr my-hw)))
              (cadr (assq 'memory-gb (cdr my-hw)))
              (cadr (assq 'mobile (cdr my-hw))))

      ;; Step 2: Discover peers and exchange capabilities
      (let ((members (discover-and-elect name my-hw timeout: timeout)))

        (if (null? members)
            ;; No peers found - we are the sole master
            (begin
              (printf "[auto-enroll] No peers found. Establishing single-node realm.~n")
              (set! *realm-master* name)
              (set! *my-role* 'master)
              (set! *realm-members* `((,name . ,my-hw)))
              (set! *scaling-factors* (compute-scaling-factor *realm-members*))

              ;; Configure gossip for single node (default settings)
              (configure-from-scaling! 1.0 1.0 100 30)
              (printf "[auto-enroll] Gossip configured: interval=30s, batch=100~n")

              (make-realm-result name 'master *realm-members* *scaling-factors*))

            ;; Peers found - run election
            (let-values (((winner score all-scores) (elect-master members)))
              (printf "[auto-enroll] Election results:~n")
              (for-each (lambda (s)
                          (printf "  ~a: ~a~a~n"
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
                (printf "[auto-enroll] Gossip configured: interval=~as, batch=~a~n"
                        (cdr (assq 'gossip-interval gossip-cfg))
                        (cdr (assq 'batch-size gossip-cfg))))

              (printf "[auto-enroll] Master: ~a (this node: ~a)~n" winner *my-role*)
              (make-realm-result winner *my-role* members *scaling-factors*))))))

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

  (define (join-realm name master-host #!key (port *discovery-port*))
    "Join an existing realm by connecting to master.

     name: this node's name
     master-host: hostname/IP of realm master

     Returns: enrollment result"

    (printf "[join-realm] Connecting to master at ~a...~n" master-host)

    (let ((my-hw (introspect-hardware)))
      (handle-exceptions exn
        (begin
          (printf "[join-realm] Failed to connect: ~a~n"
                  (get-condition-property exn 'exn 'message "unknown"))
          `((status . error)
            (message . "Could not connect to master")))

        (let-values (((in out) (tcp-connect master-host port)))
          (dynamic-wind
            (lambda () #f)
            (lambda ()
              ;; Send join request with hardware
              (enrollment-send out
                `(join-request
                  (name ,name)
                  (hardware ,my-hw)
                  (timestamp ,(current-seconds))))

              ;; Wait for response
              (let ((response (enrollment-receive in)))
                (if (and (pair? response)
                         (eq? (car response) 'join-accepted))
                    (let* ((fields (cdr response))
                           (cert (cadr (assq 'certificate fields)))
                           (scaling (cadr (assq 'scaling fields))))
                      (set! *my-role* 'node)
                      (set! *scaling-factors* scaling)
                      (printf "[join-realm] Joined successfully.~n")
                      `((status . joined)
                        (certificate . ,cert)
                        (scaling . ,scaling)))

                    (begin
                      (printf "[join-realm] Join rejected: ~a~n" response)
                      `((status . rejected)
                        (response . ,response))))))
            (lambda ()
              (enrollment-close in out)))))))

  ;; ============================================================
  ;; Discovery and Election
  ;; ============================================================

  (define (discover-and-elect my-name my-hw #!key (timeout *discovery-timeout*))
    "Discover peers on local network and collect their capabilities.

     Returns: list of (name . hardware) pairs including self"

    (printf "[discover] Broadcasting capability announcement...~n")

    (let ((discovered '())
          (listener #f))

      ;; Start listening for peer announcements
      (set! listener (tcp-listen *discovery-port*))

      ;; Broadcast our capabilities
      (thread-start!
        (make-thread
          (lambda ()
            (broadcast-capability my-name my-hw timeout))))

      ;; Listen for incoming capabilities
      (let ((deadline (+ (current-seconds) timeout)))
        (let loop ()
          (when (< (current-seconds) deadline)
            (handle-exceptions exn
              (begin
                (thread-sleep! 0.5)
                (loop))

              ;; Accept connection with timeout
              (let-values (((in out) (tcp-accept listener)))
                (handle-exceptions exn
                  (begin
                    (enrollment-close in out)
                    (loop))

                  (let ((data (enrollment-receive in)))
                    (enrollment-close in out)

                    (when (and (pair? data)
                               (eq? (car data) 'capability-announce))
                      (let* ((fields (cdr data))
                             (peer-name (cadr (assq 'name fields)))
                             (peer-hw (cadr (assq 'hardware fields))))
                        (unless (eq? peer-name my-name)
                          (printf "[discover] Found peer: ~a (mobile: ~a)~n"
                                  peer-name
                                  (cadr (assq 'mobile (cdr peer-hw))))
                          (set! discovered
                            (cons (cons peer-name peer-hw) discovered))))))
                  (loop)))))))

      ;; Clean up
      (handle-exceptions exn #f
        (tcp-close listener))

      ;; Return all members including self
      (cons (cons my-name my-hw) discovered)))

  (define (broadcast-capability name hw timeout)
    "Broadcast our capability to local network"
    (let ((packet `(capability-announce
                     (name ,name)
                     (hardware ,hw)
                     (timestamp ,(current-seconds))))
          (targets (local-network-targets))
          (deadline (+ (current-seconds) timeout)))

      (let loop ()
        (when (< (current-seconds) deadline)
          (for-each
            (lambda (host)
              (handle-exceptions exn #f
                (let-values (((in out) (tcp-connect host *discovery-port*)))
                  (enrollment-send out packet)
                  (enrollment-close in out))))
            targets)
          (thread-sleep! 2)
          (loop)))))

  (define (local-network-targets)
    "Get local network addresses to broadcast to"
    ;; Common local network patterns
    ;; In production, would scan actual subnet
    (let ((net (introspect-network)))
      (let ((gateway (cadr (assq 'gateway (cdr net)))))
        (if gateway
            ;; Derive likely peers from gateway
            (let ((prefix (gateway->prefix gateway)))
              (map (lambda (i)
                     (string-append prefix (number->string i)))
                   '(1 2 10 11 20 100 101 200)))
            ;; Fallback to common ranges
            '("192.168.1.1" "192.168.1.2" "192.168.1.10"
              "192.168.0.1" "192.168.0.2" "192.168.0.10"
              "10.0.0.1" "10.0.0.2" "10.0.1.1")))))

  (define (gateway->prefix gateway)
    "Extract network prefix from gateway IP"
    (let ((parts (string-split gateway ".")))
      (if (>= (length parts) 3)
          (string-append (car parts) "."
                        (cadr parts) "."
                        (caddr parts) ".")
          "192.168.1.")))

  (define (string-split str delim)
    "Split string by character delimiter"
    (let ((dchar (if (string? delim) (string-ref delim 0) delim)))
      (let loop ((chars (string->list str))
                 (current '())
                 (result '()))
        (cond
          ((null? chars)
           (reverse (cons (list->string (reverse current)) result)))
          ((char=? (car chars) dchar)
           (loop (cdr chars)
                 '()
                 (cons (list->string (reverse current)) result)))
          (else
           (loop (cdr chars)
                 (cons (car chars) current)
                 result))))))

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
             (my-interval (inexact->exact
                           (round (/ base-interval (max my-scale 0.1)))))
             ;; Batch size scales with capability
             (base-batch 10)
             (my-batch (inexact->exact
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

) ;; end module

;;;
;;; Example: Auto-enroll on startup
;;;
;;;   (import auto-enroll gossip)
;;;
;;;   ;; Discover peers and elect master (most capable wins)
;;;   (define realm (auto-enroll-realm 'fluffy))
;;;
;;;   ;; Example output:
;;;   ;; [auto-enroll] Starting realm discovery as 'fluffy'...
;;;   ;; [auto-enroll] Hardware: 14 cores, 128 GB RAM, mobile: #f
;;;   ;; [discover] Broadcasting capability announcement...
;;;   ;; [discover] Found peer: starlight (mobile: #t)
;;;   ;; [auto-enroll] Election results:
;;;   ;;   starlight: 16.8
;;;   ;;   fluffy: 520.0 <- WINNER
;;;   ;; [auto-enroll] Master: fluffy (this node: master)
;;;
;;;   realm
;;;   ;; => ((master . fluffy)
;;;   ;;     (role . master)
;;;   ;;     (member-count . 2)
;;;   ;;     (members . ((fluffy . 1.0) (starlight . 0.032)))
;;;   ;;     (reference-score . 520.0)
;;;   ;;     (effective-capacity . 1.032)
;;;   ;;     (recommended-replication . 2)
;;;   ;;     (scaling . ...))
;;;
;;; Example: Configure gossip from scaling
;;;
;;;   (define gossip-config
;;;     (configure-gossip-from-scaling (cdr (assq 'scaling realm))))
;;;
;;;   gossip-config
;;;   ;; => ((gossip-interval . 30)    ; master syncs every 30s
;;;   ;;     (batch-size . 52)          ; ~50 objects per batch
;;;   ;;     (max-connections . 2)
;;;   ;;     (replication-target . 2)
;;;   ;;     (my-scale . 1.0))
;;;
;;;   ;; On starlight (mobile, scale 0.032):
;;;   ;; => ((gossip-interval . 300)   ; sync less often (5 min)
;;;   ;;     (batch-size . 10)          ; smaller batches
;;;   ;;     (max-connections . 2)
;;;   ;;     (replication-target . 2)
;;;   ;;     (my-scale . 0.032))
;;;
;;; Example: Join existing realm
;;;
;;;   (import auto-enroll)
;;;
;;;   ;; On a new node wanting to join fluffy's realm:
;;;   (join-realm 'newnode "192.168.1.100")
;;;   ;; => ((status . joined)
;;;   ;;     (certificate . ...)
;;;   ;;     (scaling . ...))
;;;
