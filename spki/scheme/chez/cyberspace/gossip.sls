;;; SPKI Scheme - Anti-Entropy Gossip Protocol
;;; Library of Cyberspace - Chez Scheme Port
;;;
;;; Implements epidemic protocol for federation convergence.
;;; Nodes gossip periodically to discover and sync missing objects.
;;;
;;; Three-Layer Convergence (Memo-010 compliant):
;;;   Layer 1: Bloom filter exchange (fast, approximate)
;;;   Layer 2: Merkle tree diff (precise, logarithmic)
;;;   Layer 3: Object transfer (actual data)
;;;
;;; Post-Quantum: All hashes use SHA-256 (128-bit quantum security).
;;; Ready for SHAKE256 migration per Memo-042/043.
;;;
;;; Ported from Chicken's gossip.scm (1,190 lines, 40 exports).
;;; Changes: module -> library, SRFI-9 records -> R6RS records,
;;;          SRFI-18 threads -> Chez fork-thread/mutex,
;;;          (chicken tcp) -> (cyberspace tcp) via libtcp-bridge,
;;;          #!key/#!optional -> get-key/get-opt,
;;;          process-run/signal -> open-process-ports/system kill.

(library (cyberspace gossip)
  (export
    ;; Gossip daemon
    start-gossip-daemon
    stop-gossip-daemon
    gossip-status
    ;; Gossip listener (server-side)
    start-gossip-listener
    stop-gossip-listener
    ;; Single round operations
    gossip-round
    gossip-with-peer
    ;; Peer management
    add-peer
    remove-peer
    list-peers
    get-peer-status
    set-peer-trust-level!
    set-peer-role!
    ;; mDNS discovery (Memo-0012)
    announce-presence
    stop-announcement
    discover-peers-mdns
    ;; Convergence protocol
    sync-bloom-exchange
    sync-merkle-diff
    sync-object-transfer
    ;; Lamport-timestamped I/O
    gossip-write-timestamped
    gossip-read-timestamped
    ;; Scaling configuration (from auto-enroll)
    configure-from-scaling!
    ;; Statistics
    gossip-stats
    reset-stats!
    ;; Epidemic broadcast (Memo-012)
    make-gossip-envelope gossip-envelope?
    gossip-envelope-origin gossip-envelope-hop-count
    gossip-envelope-ttl gossip-envelope-seen gossip-envelope-payload
    gossip-forward!
    *gossip-fanout* *gossip-ttl* *gossip-dedup-window*
    ;; Robustness (Memo-012)
    gossip-verbose?
    gossip-verbose!
    peer-available?
    peer-dead?
    peer-reset-failures!)

  (import (rnrs)
          (only (chezscheme)
                printf format with-output-to-string
                fork-thread make-mutex mutex-acquire mutex-release
                sleep make-time
                open-process-ports process system
                make-transcoder utf-8-codec
                current-time time-second
                sort)
          (cyberspace tcp)
          (cyberspace bloom)
          (cyberspace catalog)
          (cyberspace crypto-ffi)
          (cyberspace os)
          (only (cyberspace vault)
                lamport-send lamport-receive! lamport-save!
                capability-add!)
          (cyberspace chicken-compatibility blob)
          (cyberspace chicken-compatibility chicken)
          (cyberspace chicken-compatibility hash-table))

  ;; ============================================================
  ;; Inlined Helpers (SRFI-1, SRFI-13 subsets)
  ;; ============================================================

  (define (current-seconds) (time-second (current-time)))

  (define (filter-map proc lst)
    (let loop ((rest lst) (acc '()))
      (if (null? rest)
          (reverse acc)
          (let ((result (proc (car rest))))
            (loop (cdr rest)
                  (if result (cons result acc) acc))))))

  (define (take lst n)
    (if (or (<= n 0) (null? lst)) '()
        (cons (car lst) (take (cdr lst) (- n 1)))))

  (define (drop lst n)
    (if (or (<= n 0) (null? lst)) lst
        (drop (cdr lst) (- n 1))))

  (define (string-contains s1 s2)
    (let ((len1 (string-length s1))
          (len2 (string-length s2)))
      (if (> len2 len1) #f
          (let loop ((i 0))
            (cond
              ((> (+ i len2) len1) #f)
              ((string=? (substring s1 i (+ i len2)) s2) i)
              (else (loop (+ i 1))))))))

  (define (string-prefix? prefix str)
    (and (>= (string-length str) (string-length prefix))
         (string=? prefix (substring str 0 (string-length prefix)))))

  (define (string-trim-both str)
    (let* ((len (string-length str))
           (start (let loop ((i 0))
                    (if (and (< i len) (char-whitespace? (string-ref str i)))
                        (loop (+ i 1))
                        i)))
           (end (let loop ((i len))
                  (if (and (> i start) (char-whitespace? (string-ref str (- i 1))))
                      (loop (- i 1))
                      i))))
      (substring str start end)))

  ;; Read all lines from a textual port
  (define (read-lines-from-port port)
    (let loop ((lines '()))
      (let ((line (get-line port)))
        (if (eof-object? line)
            (reverse lines)
            (loop (cons line lines))))))

  ;; Run a shell command and return output lines
  (define (pipe-lines cmd)
    (let-values (((to-stdin from-stdout from-stderr)
                  (open-process-ports cmd 'line (make-transcoder (utf-8-codec)))))
      (close-port to-stdin)
      (let ((lines (read-lines-from-port from-stdout)))
        (close-port from-stdout)
        (close-port from-stderr)
        lines)))

  ;; Blob/bytevector helpers (local to avoid vault import cycle)
  (define (blob->hex bv)
    (let ((len (bytevector-length bv)))
      (let loop ((i 0) (acc '()))
        (if (= i len)
            (apply string-append (reverse acc))
            (loop (+ i 1)
                  (cons (number->string (bytevector-u8-ref bv i) 16)
                        acc))))))

  (define (blob-equal? a b)
    (bytevector=? a b))

  ;; ============================================================
  ;; Configuration
  ;; ============================================================

  (define *gossip-interval* 30)        ; seconds between rounds
  (define *gossip-port* 7655)          ; default gossip port
  (define *bloom-error-rate* 0.01)     ; 1% false positive rate
  (define *max-transfer-batch* 100)    ; max objects per transfer

  ;; Robustness configuration
  (define *connect-timeout* 5)         ; seconds to wait for connection
  (define *read-timeout* 10)           ; seconds to wait for read
  (define *max-consecutive-failures* 5) ; failures before marking peer dead
  (define *base-backoff* 30)           ; initial backoff seconds
  (define *max-backoff* 3600)          ; maximum backoff (1 hour)
  (define *gossip-verbose* #f)         ; log gossip errors when #t

  ;; Scaling-aware configuration (set by auto-enroll)
  (define *node-scale* 1.0)            ; this node's capability scale (1.0 = reference)
  (define *effective-capacity* 1.0)    ; confederation total in reference units

  (define (configure-from-scaling! scale effective-capacity batch-size interval)
    "Configure gossip from capability scaling factors.
     Called by auto-enroll after master election."
    (set! *node-scale* scale)
    (set! *effective-capacity* effective-capacity)
    (set! *max-transfer-batch* batch-size)
    (set! *gossip-interval* interval)
    `(gossip-configured
      (scale ,scale)
      (effective-capacity ,effective-capacity)
      (batch-size ,batch-size)
      (interval ,interval)))

  ;; ============================================================
  ;; State
  ;; ============================================================

  (define *gossip-thread* #f)
  (define *gossip-running* #f)
  (define *gossip-listener* #f)
  (define *peers* (make-hash-table string=?))
  (define *local-catalog* #f)
  (define *local-bloom* #f)
  (define *object-getter* #f)
  (define *object-storer* #f)

  ;; Statistics
  (define *stats*
    `((rounds . 0)
      (objects-sent . 0)
      (objects-received . 0)
      (bytes-sent . 0)
      (bytes-received . 0)
      (bloom-exchanges . 0)
      (merkle-diffs . 0)
      (false-positives . 0)
      (hash-mismatches . 0)
      (sync-completed . 0)
      (last-round . #f)))

  (define (stat-inc! key . rest)
    (let ((amount (get-opt rest 0 1)))
      (set! *stats*
        (map (lambda (pair)
               (if (eq? (car pair) key)
                   (cons key (+ (cdr pair) amount))
                   pair))
             *stats*))))

  (define (stat-set! key value)
    (set! *stats*
      (map (lambda (pair)
             (if (eq? (car pair) key)
                 (cons key value)
                 pair))
           *stats*)))

  (define (gossip-stats)
    "Return current gossip statistics."
    *stats*)

  (define (reset-stats!)
    "Reset gossip statistics."
    (set! *stats*
      `((rounds . 0)
        (objects-sent . 0)
        (objects-received . 0)
        (bytes-sent . 0)
        (bytes-received . 0)
        (bloom-exchanges . 0)
        (merkle-diffs . 0)
        (false-positives . 0)
        (hash-mismatches . 0)
        (sync-completed . 0)
        (last-round . #f))))

  ;; ============================================================
  ;; Byte-Counted I/O
  ;; ============================================================

  (define (gossip-write data out)
    "Write data and track bytes sent."
    (let* ((str (with-output-to-string (lambda () (write data))))
           (len (string-length str)))
      (display str out)
      (newline out)
      (flush-output-port out)
      (stat-inc! 'bytes-sent (+ len 1))  ; +1 for newline
      (session-stat! 'bytes-out (+ len 1))
      len))

  (define (gossip-read in)
    "Read data and track bytes received."
    (let* ((data (read in))
           (str (with-output-to-string (lambda () (write data))))
           (len (string-length str)))
      (stat-inc! 'bytes-received len)
      (session-stat! 'bytes-in len)
      data))

  (define (track-connection-type host)
    "Track IPv4 vs IPv6 based on host address."
    (if (string-contains host ":")
        (session-stat! 'packets-ipv6)
        (session-stat! 'packets-ipv4)))

  ;; ============================================================
  ;; Lamport-Timestamped Messaging (Memo-0012)
  ;; ============================================================

  (define (gossip-write-timestamped data out)
    "Write data with Lamport timestamp attached."
    (let ((timestamped (lamport-send data)))
      (gossip-write timestamped out)))

  (define (gossip-read-timestamped in)
    "Read data and update local Lamport clock."
    (let ((msg (gossip-read in)))
      (if (and (pair? msg)
               (assq 'lamport-time msg)
               (assq 'payload msg))
          ;; Timestamped message - update clock and extract payload
          (lamport-receive! msg)
          ;; Not timestamped - return as-is for backward compat
          msg)))

  ;; ============================================================
  ;; Peer Management
  ;; ============================================================

  ;; Trust levels (Memo-0012):
  ;;   unknown  - Never seen, reject by default
  ;;   known    - Key registered, manual approval required
  ;;   verified - Signature chain verified via SPKI
  ;;   trusted  - Full automatic sync

  ;; Peer roles:
  ;;   publisher  - I push releases to them
  ;;   subscriber - I pull releases from them
  ;;   peer       - Bidirectional sync

  (define-record-type (peer make-peer-internal peer?)
    (fields
      (immutable host)
      (immutable port)
      (mutable last-seen)
      (mutable status)
      (mutable bloom-hash)
      (mutable trust-level)
      (mutable role)
      (mutable public-key)
      (mutable failure-count)
      (mutable last-failure)
      (mutable backoff-until)))

  (define (add-peer host . opts)
    "Add a peer to gossip with.

     trust-level: unknown | known | verified | trusted
     role: publisher | subscriber | peer
     public-key: SPKI public key for verification (optional)"
    (let ((port (get-key opts 'port: *gossip-port*))
          (trust-level (get-key opts 'trust-level: 'unknown))
          (role (get-key opts 'role: 'peer))
          (public-key (get-key opts 'public-key: #f)))
      (let ((key (string-append host ":" (number->string port))))
        (hash-table-set! *peers* key
                        (make-peer-internal host port (current-seconds)
                                           'unknown #f
                                           trust-level role public-key
                                           0 0 0))
        key)))

  (define (peer-record-failure! peer)
    "Record a connection failure for peer. Updates backoff timing."
    (let* ((failures (+ 1 (peer-failure-count peer)))
           (now (current-seconds))
           (backoff (min *max-backoff*
                         (* *base-backoff* (expt 2 (- (min failures 10) 1))))))
      (peer-failure-count-set! peer failures)
      (peer-last-failure-set! peer now)
      (peer-backoff-until-set! peer (+ now backoff))
      (when *gossip-verbose*
        (printf "[gossip] Peer ~a:~a failed (~a consecutive), backoff ~as~n"
                (peer-host peer) (peer-port peer) failures backoff))))

  (define (peer-record-success! peer)
    "Record a successful connection. Resets failure count."
    (peer-failure-count-set! peer 0)
    (peer-backoff-until-set! peer 0)
    (peer-last-seen-set! peer (current-seconds)))

  (define (peer-available? peer)
    "Check if peer is available for gossip (not in backoff, not dead)."
    (and (< (peer-failure-count peer) *max-consecutive-failures*)
         (>= (current-seconds) (peer-backoff-until peer))))

  (define (peer-dead? peer)
    "Check if peer has exceeded max consecutive failures."
    (>= (peer-failure-count peer) *max-consecutive-failures*))

  (define (peer-reset-failures! host . opts)
    "Reset failure count for a peer. Use to revive a 'dead' peer."
    (let* ((port (get-key opts 'port: *gossip-port*))
           (key (string-append host ":" (number->string port)))
           (p (hash-table-ref/default *peers* key #f)))
      (when p
        (peer-failure-count-set! p 0)
        (peer-backoff-until-set! p 0)
        (peer-status-set! p 'unknown)
        #t)))

  (define (gossip-verbose?)
    "Return whether verbose gossip logging is enabled."
    *gossip-verbose*)

  (define (gossip-verbose! . rest)
    "Enable/disable verbose gossip logging."
    (let ((on (get-opt rest 0 #t)))
      (set! *gossip-verbose* on)
      (if on "[gossip] Verbose logging enabled" "[gossip] Verbose logging disabled")))

  (define (set-peer-trust-level! host trust-level . opts)
    "Update trust level for a peer.
     trust-level: unknown | known | verified | trusted"
    (let* ((port (get-key opts 'port: *gossip-port*))
           (key (string-append host ":" (number->string port)))
           (p (hash-table-ref/default *peers* key #f)))
      (when p
        (peer-trust-level-set! p trust-level)
        trust-level)))

  (define (set-peer-role! host role . opts)
    "Update role for a peer.
     role: publisher | subscriber | peer"
    (let* ((port (get-key opts 'port: *gossip-port*))
           (key (string-append host ":" (number->string port)))
           (p (hash-table-ref/default *peers* key #f)))
      (when p
        (peer-role-set! p role)
        role)))

  (define (remove-peer host . opts)
    "Remove a peer."
    (let* ((port (get-key opts 'port: *gossip-port*))
           (key (string-append host ":" (number->string port))))
      (hash-table-delete! *peers* key)))

  (define (list-peers)
    "List all known peers with trust and role information."
    (hash-table-map *peers*
                   (lambda (key p)
                     `(,key
                       (host ,(peer-host p))
                       (port ,(peer-port p))
                       (status ,(peer-status p))
                       (last-seen ,(peer-last-seen p))
                       (trust-level ,(peer-trust-level p))
                       (role ,(peer-role p))
                       (has-key ,(if (peer-public-key p) #t #f))))))

  (define (get-peer-status host . opts)
    "Get status of specific peer including trust level."
    (let* ((port (get-key opts 'port: *gossip-port*))
           (key (string-append host ":" (number->string port)))
           (p (hash-table-ref/default *peers* key #f)))
      (and p
           `((host ,(peer-host p))
             (port ,(peer-port p))
             (status ,(peer-status p))
             (last-seen ,(peer-last-seen p))
             (trust-level ,(peer-trust-level p))
             (role ,(peer-role p))
             (has-key ,(if (peer-public-key p) #t #f))))))

  ;; ============================================================
  ;; Gossip Daemon
  ;; ============================================================

  (define (start-gossip-daemon local-objects . opts)
    "Start background gossip daemon.

     local-objects: procedure returning list of local object hashes
     interval: seconds between gossip rounds
     port: listening port for incoming gossip
     object-getter: (lambda (hash) content) to retrieve objects
     object-storer: (lambda (hash content) void) to store objects
     listen: if #t, also start listener for incoming connections"
    (let ((interval (get-key opts 'interval: *gossip-interval*))
          (port (get-key opts 'port: *gossip-port*))
          (object-getter (get-key opts 'object-getter: #f))
          (object-storer (get-key opts 'object-storer: #f))
          (listen (get-key opts 'listen: #t)))

      (when *gossip-running*
        (stop-gossip-daemon))

      ;; Store callbacks
      (set! *object-getter* object-getter)
      (set! *object-storer* object-storer)

      ;; Register gossip capabilities (lazy, at daemon start)
      (capability-add! 'gossip-protocol)
      (capability-add! 'bloom-filter)
      (capability-add! 'merkle-diff)
      (capability-add! 'object-transfer)

      ;; Initialize local state
      (set! *local-catalog* (make-catalog))
      (for-each (lambda (h) (catalog-add! *local-catalog* h))
                (local-objects))

      (set! *local-bloom*
        (make-inventory-bloom (local-objects) 'error-rate: *bloom-error-rate*))

      (set! *gossip-running* #t)
      (set! *gossip-thread*
        (fork-thread
          (lambda ()
            (gossip-main-loop local-objects interval port))))

      ;; Optionally start listener for incoming connections
      (when listen
        (start-gossip-listener port local-objects object-getter))

      `(gossip-daemon-started
        (interval ,interval)
        (port ,port)
        (listening ,listen)
        (peers ,(hash-table-size *peers*))
        (local-objects ,(catalog-size *local-catalog*)))))

  (define (stop-gossip-daemon)
    "Stop gossip daemon and listener."
    (set! *gossip-running* #f)
    (stop-gossip-listener)
    ;; Thread will exit naturally when *gossip-running* becomes #f
    (set! *gossip-thread* #f)
    ;; Persist Lamport clock on shutdown
    (lamport-save!)
    'stopped)

  (define (gossip-status)
    "Get current gossip daemon status with peer health info."
    (let* ((all-peers (hash-table-values *peers*))
           (available (filter peer-available? all-peers))
           (dead (filter peer-dead? all-peers))
           (in-backoff (filter (lambda (p)
                                 (and (not (peer-dead? p))
                                      (not (peer-available? p))))
                               all-peers)))
      `(gossip-status
        (running ,*gossip-running*)
        (peers ,(hash-table-size *peers*))
        (peers-available ,(length available))
        (peers-dead ,(length dead))
        (peers-backoff ,(length in-backoff))
        (local-objects ,(if *local-catalog* (catalog-size *local-catalog*) 0))
        (stats ,*stats*))))

  (define (gossip-main-loop local-objects interval port)
    "Main gossip loop."
    (let loop ()
      (when *gossip-running*
        ;; Update local state
        (let ((current-objects (local-objects)))
          ;; Rebuild bloom and catalog if objects changed
          (when (not (= (length current-objects)
                       (catalog-size *local-catalog*)))
            (set! *local-catalog* (make-catalog))
            (for-each (lambda (h) (catalog-add! *local-catalog* h))
                      current-objects)
            (set! *local-bloom*
              (make-inventory-bloom current-objects
                                   'error-rate: *bloom-error-rate*))))

        ;; Do one gossip round
        (guard (exn [#t #f])
          (gossip-round))

        (stat-inc! 'rounds)
        (stat-set! 'last-round (current-seconds))

        ;; Sleep until next round
        (sleep (make-time 'time-duration 0 interval))
        (loop))))

  ;; ============================================================
  ;; Epidemic Broadcast (Memo-012)
  ;; ============================================================

  ;; Epidemic configuration
  (define *gossip-fanout* 3)          ; peers per forward
  (define *gossip-ttl* 5)            ; max hops
  (define *gossip-dedup-window* 3600) ; seconds before dedup entry expires

  ;; Gossip envelope record
  (define-record-type gossip-envelope
    (fields
      (immutable origin)
      (immutable hop-count)
      (immutable ttl)
      (immutable seen)
      (immutable payload)))

  ;; Dedup cache: message-hash → timestamp
  (define *dedup-cache* (make-hash-table string=?))
  (define *dedup-mutex* (make-mutex))

  (define (dedup-seen? msg-hash)
    "Check if message hash has been seen recently (thread-safe)."
    (mutex-acquire *dedup-mutex*)
    (let ((result (hash-table-exists? *dedup-cache* msg-hash)))
      (mutex-release *dedup-mutex*)
      result))

  (define (dedup-record! msg-hash)
    "Record message hash in dedup cache (thread-safe)."
    (mutex-acquire *dedup-mutex*)
    (hash-table-set! *dedup-cache* msg-hash (current-seconds))
    (mutex-release *dedup-mutex*))

  (define (dedup-gc!)
    "Evict stale entries from dedup cache (thread-safe)."
    (mutex-acquire *dedup-mutex*)
    (let ((cutoff (- (current-seconds) *gossip-dedup-window*)))
      (hash-table-walk *dedup-cache*
        (lambda (k v)
          (when (< v cutoff)
            (hash-table-delete! *dedup-cache* k)))))
    (mutex-release *dedup-mutex*))

  (define (take-random lst n)
    "Select up to n random elements from lst without replacement."
    (if (or (null? lst) (<= n 0))
        '()
        (let ((len (length lst)))
          (if (<= len n)
              lst
              ;; Fisher-Yates partial shuffle: pick n from lst
              (let ((vec (list->vector lst)))
                (do ((i 0 (+ i 1)))
                    ((= i n)
                     (let loop ((j 0) (acc '()))
                       (if (= j n)
                           acc
                           (loop (+ j 1) (cons (vector-ref vec j) acc)))))
                  (let* ((j (+ i (mod (random-u32) (- len i))))
                         (tmp (vector-ref vec i)))
                    (vector-set! vec i (vector-ref vec j))
                    (vector-set! vec j tmp))))))))

  (define (gossip-forward! envelope my-node-id)
    "Forward a gossip envelope via epidemic broadcast."
    (let ((msg-hash (blob->hex (blake2b-hash
                                 (string->blob
                                   (with-output-to-string
                                     (lambda () (write (gossip-envelope-payload envelope))))))))
          (hop (gossip-envelope-hop-count envelope))
          (ttl (gossip-envelope-ttl envelope))
          (seen (gossip-envelope-seen envelope)))

      (cond
       ;; Check TTL
       ((>= hop ttl)
        (when *gossip-verbose*
          (printf "[gossip] Dropping envelope: TTL exceeded (~a/~a)~n" hop ttl)))

       ;; Check dedup
       ((dedup-seen? msg-hash)
        (when *gossip-verbose*
          (printf "[gossip] Dropping envelope: duplicate~n")))

       (else
        ;; Record in dedup cache
        (dedup-record! msg-hash)

        ;; Filter peers and forward
        (let* ((all-peers (hash-table-values *peers*))
               (eligible (filter
                           (lambda (p)
                             (and (peer-available? p)
                                  (memq (peer-trust-level p) '(known verified trusted))
                                  (not (member (string-append (peer-host p) ":"
                                                (number->string (peer-port p)))
                                               seen))))
                           all-peers))
               (targets (take-random eligible *gossip-fanout*))
               (new-seen (cons my-node-id seen))
               (new-envelope (make-gossip-envelope
                               (gossip-envelope-origin envelope)
                               (+ hop 1)
                               ttl
                               new-seen
                               (gossip-envelope-payload envelope))))
          ;; Forward to each target
          (for-each
            (lambda (peer)
              (guard (exn
                [#t (peer-record-failure! peer)
                    (when *gossip-verbose*
                      (printf "[gossip] Forward to ~a:~a failed~n"
                              (peer-host peer) (peer-port peer)))])
                (let-values (((in out) (tcp-connect (peer-host peer) (peer-port peer))))
                  (dynamic-wind
                    (lambda () (values))
                    (lambda ()
                      (gossip-write-timestamped
                        `(gossip-forward
                          (origin ,(gossip-envelope-origin new-envelope))
                          (hop-count ,(gossip-envelope-hop-count new-envelope))
                          (ttl ,(gossip-envelope-ttl new-envelope))
                          (seen ,(gossip-envelope-seen new-envelope))
                          (payload ,(gossip-envelope-payload new-envelope)))
                        out)
                      (peer-record-success! peer))
                    (lambda ()
                      (close-port in)
                      (close-port out))))))
            targets))))))

  ;; ============================================================
  ;; Single Gossip Round
  ;; ============================================================

  (define (gossip-round)
    "Execute one round of anti-entropy gossip."
    (dedup-gc!)
    (let* ((all-peers (hash-table-values *peers*))
           (available (filter peer-available? all-peers))
           (targets (take-random available (min *gossip-fanout* (length available)))))
      (for-each gossip-with-peer targets)))

  (define (gossip-with-peer peer)
    "Gossip with specific peer. Returns sync result or #f on failure."
    (if (not (peer-available? peer))
        (begin
          (when *gossip-verbose*
            (printf "[gossip] Skipping ~a:~a (in backoff or dead)~n"
                    (peer-host peer) (peer-port peer)))
          #f)
        (guard (exn
          [#t (peer-status-set! peer 'unreachable)
              (peer-record-failure! peer)
              (when *gossip-verbose*
                (printf "[gossip] Connection to ~a:~a failed: ~a~n"
                        (peer-host peer) (peer-port peer)
                        (if (message-condition? exn)
                            (condition-message exn)
                            "unknown")))
              #f])
          (let-values (((in out) (tcp-connect (peer-host peer) (peer-port peer))))
            ;; Track connection protocol
            (track-connection-type (peer-host peer))
            (dynamic-wind
              (lambda () (values))
              (lambda ()
                ;; Success - reset failure count
                (peer-record-success! peer)
                (peer-status-set! peer 'connected)

                ;; Layer 1: Bloom filter exchange
                (let ((candidates (sync-bloom-exchange in out)))
                  (stat-inc! 'bloom-exchanges)

                  (if (null? candidates)
                      ;; Synchronized
                      (begin
                        (peer-status-set! peer 'synchronized)
                        '(synchronized))

                      ;; Layer 2: Merkle diff for candidates
                      (let ((missing (sync-merkle-diff in out candidates)))
                        (stat-inc! 'merkle-diffs)

                        (if (null? missing)
                            ;; All candidates were false positives
                            (begin
                              (stat-inc! 'false-positives (length candidates))
                              (peer-status-set! peer 'synchronized)
                              `(synchronized (false-positives . ,(length candidates))))

                            ;; Layer 3: Transfer missing objects
                            (let ((received (sync-object-transfer in out missing)))
                              (stat-inc! 'objects-received (length received))
                              (peer-status-set! peer 'synchronized)
                              `(synced (objects-received . ,(length received)))))))))
              (lambda ()
                (close-port in)
                (close-port out)))))))

  ;; ============================================================
  ;; Layer 1: Bloom Filter Exchange
  ;; ============================================================

  (define (sync-bloom-exchange in out)
    "Exchange Bloom filters and hash lists, return candidate hashes to sync."
    (let ((local-hashes (catalog->list *local-catalog*)))
      ;; Send our Bloom filter and hash list
      (gossip-write-timestamped
        `(bloom-exchange
          (bloom ,(blocked-bloom-serialize *local-bloom*))
          (hashes ,local-hashes)
          (count ,(length local-hashes)))
        out)

      ;; Receive remote Bloom filter and hash list
      (let ((response (gossip-read-timestamped in)))
        (if (and (pair? response)
                 (eq? (car response) 'bloom-exchange))
            (let* ((remote-bloom-data (cadr (assq 'bloom (cdr response))))
                   (remote-hashes (cadr (assq 'hashes (cdr response))))
                   (remote-bloom (blocked-bloom-deserialize remote-bloom-data)))
              ;; Find hashes remote has that we don't have locally
              (filter
                (lambda (hash)
                  (not (catalog-contains? *local-catalog* hash)))
                remote-hashes))
            ;; Protocol mismatch - return empty (no sync)
            '()))))

  ;; ============================================================
  ;; Layer 2: Merkle Tree Diff
  ;; ============================================================

  (define (sync-merkle-diff in out candidates)
    "Perform Merkle diff to precisely identify missing objects."
    ;; Send our Merkle root
    (gossip-write-timestamped
      `(merkle-root ,(catalog-root *local-catalog*))
      out)

    ;; Receive remote Merkle root
    (let ((response (gossip-read-timestamped in)))
      (if (and (pair? response)
               (eq? (car response) 'merkle-root))
          (let ((remote-root (cadr response))
                (local-root (catalog-root *local-catalog*)))
            (cond
              ;; Both empty - synchronized
              ((and (not local-root) (not remote-root))
               '())

              ;; Roots match - synchronized
              ((and local-root remote-root
                    (blob-equal? local-root remote-root))
               '())

              ;; Roots differ - verify candidates
              ((null? candidates)
               '())

              (else
               (sync-verify-candidates in out candidates))))

          ;; Protocol error - return candidates as-is
          candidates)))

  (define (sync-verify-candidates in out candidates)
    "Ask remote to verify which candidates they actually have."
    (gossip-write-timestamped
      `(verify-candidates ,candidates)
      out)

    (let ((response (gossip-read-timestamped in)))
      (if (and (pair? response)
               (eq? (car response) 'verified-missing))
          (cadr response)
          candidates)))

  ;; ============================================================
  ;; Layer 3: Object Transfer
  ;; ============================================================

  (define (sync-object-transfer in out missing-hashes)
    "Request and receive missing objects."
    (if (null? missing-hashes)
        '()
        (let ((batch (take missing-hashes
                           (min (length missing-hashes)
                                *max-transfer-batch*))))
          ;; Request this batch
          (gossip-write-timestamped
            `(request-objects ,batch)
            out)

          ;; Receive objects
          (let ((response (gossip-read-timestamped in)))
            (if (and (pair? response)
                     (eq? (car response) 'objects))
                (let* ((objects (cdr response))
                       (verified (filter-map verify-and-store-object objects)))
                  ;; Update local catalog with verified hashes
                  (for-each
                    (lambda (hash)
                      (catalog-add! *local-catalog* hash))
                    verified)
                  ;; Recurse for remaining hashes
                  (if (> (length missing-hashes) *max-transfer-batch*)
                      (append verified
                              (sync-object-transfer
                                in out
                                (drop missing-hashes *max-transfer-batch*)))
                      verified))
                '())))))

  (define (verify-and-store-object obj)
    "Verify object hash matches content, store if valid."
    (let* ((hash (car obj))
           (content (cadr obj))
           (content-blob (if (bytevector? content)
                             content
                             (string->blob content)))
           (computed (blob->hex (sha256-hash content-blob)))
           (expected-hash (if (string-prefix? "sha256:" hash)
                              (substring hash 7 (string-length hash))
                              hash)))
      (if (string=? expected-hash computed)
          (begin
            ;; Store object if callback is set
            (when *object-storer*
              (*object-storer* hash content-blob))
            hash)
          (begin
            (stat-inc! 'hash-mismatches)
            #f))))

  ;; ============================================================
  ;; Server-Side Handler (Incoming Connections)
  ;; ============================================================

  (define (start-gossip-listener port local-objects-proc object-getter)
    "Start listening for incoming gossip connections."
    (set! *object-getter* object-getter)
    (set! *gossip-listener* (tcp-listen port))
    (fork-thread
      (lambda ()
        (gossip-listener-loop local-objects-proc)))
    `(gossip-listener-started (port ,port)))

  (define (stop-gossip-listener)
    "Stop listening for incoming connections."
    (when *gossip-listener*
      (tcp-close *gossip-listener*)
      (set! *gossip-listener* #f))
    'stopped)

  (define (gossip-listener-loop local-objects-proc)
    "Accept and handle incoming gossip connections."
    (let loop ()
      (when (and *gossip-running* *gossip-listener*)
        (guard (exn [#t #f])
          (let-values (((in out) (tcp-accept *gossip-listener*)))
            (fork-thread
              (lambda ()
                (guard (exn [#t #f])
                  (handle-gossip-session in out local-objects-proc))
                (close-port in)
                (close-port out)))))
        (loop))))

  (define (handle-gossip-session in out local-objects-proc)
    "Handle one incoming gossip session."
    (let* ((local-hashes (local-objects-proc))
           (local-bloom (make-inventory-bloom local-hashes
                                              'error-rate: *bloom-error-rate*))
           (local-cat (make-catalog)))
      ;; Build local catalog
      (for-each (lambda (h) (catalog-add! local-cat h)) local-hashes)

      ;; Read first message — dispatch on type
      (let ((request (gossip-read-timestamped in)))
        ;; Handle epidemic forward messages
        (when (and (pair? request) (eq? (car request) 'gossip-forward))
          (let* ((origin    (cadr (assq 'origin (cdr request))))
                 (hop-count (cadr (assq 'hop-count (cdr request))))
                 (ttl       (cadr (assq 'ttl (cdr request))))
                 (seen      (cadr (assq 'seen (cdr request))))
                 (payload   (cadr (assq 'payload (cdr request))))
                 (envelope  (make-gossip-envelope origin hop-count ttl seen payload))
                 (my-id     (format #f "local:~a" *gossip-port*)))
            (gossip-forward! envelope my-id)))

        ;; Layer 1: Respond to Bloom exchange
        (when (and (pair? request) (eq? (car request) 'bloom-exchange))
          ;; Send our bloom and hashes
          (gossip-write-timestamped
            `(bloom-exchange
              (bloom ,(blocked-bloom-serialize local-bloom))
              (hashes ,local-hashes)
              (count ,(length local-hashes)))
            out)

          ;; Layer 2: Respond to Merkle root request
          (let ((request2 (gossip-read-timestamped in)))
            (when (and (pair? request2) (eq? (car request2) 'merkle-root))
              (gossip-write-timestamped
                `(merkle-root ,(catalog-root local-cat))
                out)

              ;; Handle verify-candidates request
              (let ((request3 (gossip-read-timestamped in)))
                (when (and (pair? request3) (eq? (car request3) 'verify-candidates))
                  (let* ((candidates (cadr request3))
                         (verified (filter
                                     (lambda (h) (member h local-hashes))
                                     candidates)))
                    (gossip-write-timestamped
                      `(verified-missing ,verified)
                      out)

                    ;; Layer 3: Respond to object requests
                    (let ((request4 (gossip-read-timestamped in)))
                      (when (and (pair? request4)
                                 (eq? (car request4) 'request-objects))
                        (let* ((requested (cadr request4))
                               (objects (filter-map
                                          (lambda (hash)
                                            (and *object-getter*
                                                 (let ((content (*object-getter* hash)))
                                                   (and content (list hash content)))))
                                          requested)))
                          (gossip-write-timestamped
                            `(objects ,@objects)
                            out)
                          (stat-inc! 'objects-sent (length objects))
                          (stat-inc! 'sync-completed)))))))))))))

  ;; ============================================================
  ;; mDNS Discovery (Memo-0012)
  ;; ============================================================
  ;;
  ;; Uses dns-sd on macOS, avahi on Linux for local network discovery.
  ;; Service type: _cyberspace._tcp

  (define *mdns-service-type* "_cyberspace._tcp")
  (define *mdns-process* #f)
  (define *mdns-ports* #f)  ; keep ports alive for background process

  (define (announce-presence node-name . opts)
    "Announce this node via mDNS for local network discovery."
    (let ((port (get-key opts 'port: *gossip-port*)))
      (guard (exn
        [#t `(mdns-error ,(if (message-condition? exn)
                              (condition-message exn)
                              "unknown error"))])
        (let ((name (if (symbol? node-name)
                        (symbol->string node-name)
                        node-name)))
          ;; Stop any existing announcement
          (stop-announcement)
          ;; Start dns-sd registration (macOS)
          (let-values (((from-stdout to-stdin pid)
                        (process (format #f "dns-sd -R ~a ~a local. ~a"
                                         name *mdns-service-type* port))))
            (set! *mdns-process* pid)
            (set! *mdns-ports* (list from-stdout to-stdin)))
          `(mdns-announced
            (name ,name)
            (type ,*mdns-service-type*)
            (port ,port))))))

  (define (stop-announcement)
    "Stop mDNS announcement."
    (when *mdns-process*
      (guard (exn [#t #f])
        (system (format #f "kill -15 ~a" *mdns-process*)))
      (when *mdns-ports*
        (for-each (lambda (p) (guard (exn [#t #f]) (close-port p)))
                  *mdns-ports*)
        (set! *mdns-ports* #f))
      (set! *mdns-process* #f))
    'stopped)

  (define (discover-peers-mdns . opts)
    "Discover Cyberspace peers on local network via mDNS."
    (let ((timeout (get-key opts 'timeout: 3)))
      (guard (exn
        [#t `(mdns-error ,(if (message-condition? exn)
                              (condition-message exn)
                              "unknown error"))])
        (let* ((results '())
               (cmd (format #f "timeout ~a dns-sd -B ~a local. 2>/dev/null || true"
                            timeout *mdns-service-type*))
               (output (pipe-lines cmd)))
          ;; Parse dns-sd browse output
          (for-each
            (lambda (line)
              (when (string-contains line *mdns-service-type*)
                (let ((fields (string-split line)))
                  (when (>= (length fields) 6)
                    (let ((name (list-ref fields (- (length fields) 1))))
                      (let ((resolved (resolve-mdns-service name)))
                        (when resolved
                          (set! results (cons resolved results)))))))))
            output)
          ;; Auto-add discovered peers with 'known' trust level
          (for-each
            (lambda (peer-info)
              (let ((host (car peer-info))
                    (port (cadr peer-info))
                    (name (caddr peer-info)))
                (add-peer host 'port: port 'trust-level: 'known)))
            results)
          results))))

  (define (resolve-mdns-service name)
    "Resolve mDNS service name to host:port. Returns (host port name) or #f."
    (guard (exn [#t #f])
      (let* ((cmd (format #f "timeout 2 dns-sd -L '~a' ~a local. 2>/dev/null | head -5 || true"
                          name *mdns-service-type*))
             (output (pipe-lines cmd)))
        (let loop ((lines output))
          (if (null? lines)
              #f
              (let ((line (car lines)))
                (cond
                  ((string-contains line " port:")
                   (let* ((port-match (string-contains line "port:"))
                          (port-str (and port-match
                                        (substring line (+ port-match 5)
                                                   (string-length line))))
                          (port (and port-str
                                    (string->number (car (string-split port-str))))))
                     (let ((host-match (string-contains line ".local.")))
                       (if (and host-match port)
                           (let ((host (substring line 0 (+ host-match 7))))
                             (let ((clean-host (string-trim-both host)))
                               (list clean-host port name)))
                           (loop (cdr lines))))))
                  (else (loop (cdr lines))))))))))

) ;; end library
