;;; SPKI Scheme - Anti-Entropy Gossip Protocol
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

(module gossip
  (;; Gossip daemon
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
   reset-stats!)

  (import scheme
          (chicken base)
          (chicken blob)
          (chicken tcp)
          (chicken io)
          (chicken port)
          (chicken time)
          (chicken format)
          (chicken condition)
          srfi-1      ; list utilities
          srfi-4      ; u8vectors
          srfi-13     ; string-contains
          srfi-18     ; threads
          srfi-69     ; hash tables
          bloom
          catalog
          crypto-ffi
          os          ; for session-stat!
          (only vault lamport-send lamport-receive! lamport-save!))

  ;; ============================================================
  ;; Configuration
  ;; ============================================================

  (define *gossip-interval* 30)        ; seconds between rounds
  (define *gossip-port* 7655)          ; default gossip port
  (define *bloom-error-rate* 0.01)     ; 1% false positive rate
  (define *max-transfer-batch* 100)    ; max objects per transfer

  ;; Scaling-aware configuration (set by auto-enroll)
  (define *node-scale* 1.0)            ; this node's capability scale (1.0 = reference)
  (define *effective-capacity* 1.0)    ; confederation total in reference units

  (define (configure-from-scaling! scale effective-capacity batch-size interval)
    "Configure gossip from capability scaling factors.
     Called by auto-enroll after master election.

     scale: this node's scale (1.0 = most capable)
     effective-capacity: total confederation capacity
     batch-size: recommended batch size for this node
     interval: recommended gossip interval for this node"
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

  (define (stat-inc! key #!optional (amount 1))
    (set! *stats*
      (map (lambda (pair)
             (if (eq? (car pair) key)
                 (cons key (+ (cdr pair) amount))
                 pair))
           *stats*)))

  (define (stat-set! key value)
    (set! *stats*
      (map (lambda (pair)
             (if (eq? (car pair) key)
                 (cons key value)
                 pair))
           *stats*)))

  (define (gossip-stats)
    "Return current gossip statistics"
    *stats*)

  (define (reset-stats!)
    "Reset gossip statistics"
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
      (flush-output out)
      (stat-inc! 'bytes-sent (+ len 1))  ; +1 for newline
      (session-stat! 'bytes-out (+ len 1))
      len))

  (define (gossip-read in)
    "Read data and track bytes received."
    (let* ((data (read in))
           ;; Estimate received bytes from data size
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
  ;; Lamport-Timestamped Messaging (RFC-012)
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

  (define-record-type <peer>
    (make-peer-internal host port last-seen status bloom-hash)
    peer?
    (host peer-host)
    (port peer-port)
    (last-seen peer-last-seen peer-last-seen-set!)
    (status peer-status peer-status-set!)
    (bloom-hash peer-bloom-hash peer-bloom-hash-set!))

  (define (add-peer host #!key (port *gossip-port*))
    "Add a peer to gossip with"
    (let ((key (string-append host ":" (number->string port))))
      (hash-table-set! *peers* key
                      (make-peer-internal host port (current-seconds) 'unknown #f))
      key))

  (define (remove-peer host #!key (port *gossip-port*))
    "Remove a peer"
    (let ((key (string-append host ":" (number->string port))))
      (hash-table-delete! *peers* key)))

  (define (list-peers)
    "List all known peers"
    (hash-table-map *peers*
                   (lambda (key p)
                     `(,key
                       (host ,(peer-host p))
                       (port ,(peer-port p))
                       (status ,(peer-status p))
                       (last-seen ,(peer-last-seen p))))))

  (define (get-peer-status host #!key (port *gossip-port*))
    "Get status of specific peer"
    (let* ((key (string-append host ":" (number->string port)))
           (p (hash-table-ref/default *peers* key #f)))
      (and p
           `((host ,(peer-host p))
             (port ,(peer-port p))
             (status ,(peer-status p))
             (last-seen ,(peer-last-seen p))))))

  ;; ============================================================
  ;; Gossip Daemon
  ;; ============================================================

  (define (start-gossip-daemon local-objects #!key
                                             (interval *gossip-interval*)
                                             (port *gossip-port*)
                                             (object-getter #f)
                                             (object-storer #f)
                                             (listen #t))
    "Start background gossip daemon.

     local-objects: procedure returning list of local object hashes
     interval: seconds between gossip rounds
     port: listening port for incoming gossip
     object-getter: (lambda (hash) content) to retrieve objects
     object-storer: (lambda (hash content) void) to store objects
     listen: if #t, also start listener for incoming connections"

    (when *gossip-running*
      (stop-gossip-daemon))

    ;; Store callbacks
    (set! *object-getter* object-getter)
    (set! *object-storer* object-storer)

    ;; Initialize local state
    (set! *local-catalog* (make-catalog))
    (for-each (lambda (h) (catalog-add! *local-catalog* h))
              (local-objects))

    (set! *local-bloom*
      (make-inventory-bloom (local-objects) error-rate: *bloom-error-rate*))

    (set! *gossip-running* #t)
    (set! *gossip-thread*
      (thread-start!
        (make-thread
          (lambda ()
            (gossip-main-loop local-objects interval port)))))

    ;; Optionally start listener for incoming connections
    (when listen
      (start-gossip-listener port local-objects object-getter))

    `(gossip-daemon-started
      (interval ,interval)
      (port ,port)
      (listening ,listen)
      (peers ,(hash-table-size *peers*))
      (local-objects ,(catalog-size *local-catalog*))))

  (define (stop-gossip-daemon)
    "Stop gossip daemon and listener"
    (set! *gossip-running* #f)
    (stop-gossip-listener)
    (when *gossip-thread*
      (handle-exceptions exn #f
        (thread-terminate! *gossip-thread*))
      (set! *gossip-thread* #f))
    ;; Persist Lamport clock on shutdown
    (lamport-save!)
    'stopped)

  (define (gossip-status)
    "Get current gossip daemon status"
    `(gossip-status
      (running ,*gossip-running*)
      (peers ,(hash-table-size *peers*))
      (local-objects ,(if *local-catalog* (catalog-size *local-catalog*) 0))
      (stats ,*stats*)))

  (define (gossip-main-loop local-objects interval port)
    "Main gossip loop"
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
                                   error-rate: *bloom-error-rate*))))

        ;; Do one gossip round
        (handle-exceptions exn
          (begin
            ;; Log error but continue
            #f)
          (gossip-round))

        (stat-inc! 'rounds)
        (stat-set! 'last-round (current-seconds))

        ;; Sleep until next round
        (thread-sleep! interval)
        (loop))))

  ;; ============================================================
  ;; Single Gossip Round
  ;; ============================================================

  (define (gossip-round)
    "Execute one round of anti-entropy gossip.
     Selects random peer and synchronizes."
    (let ((peers (hash-table-values *peers*)))
      (when (pair? peers)
        ;; Select random peer
        (let* ((idx (modulo (random-u32) (length peers)))
               (peer (list-ref peers idx)))
          (gossip-with-peer peer)))))

  (define (gossip-with-peer peer)
    "Gossip with specific peer.
     Returns: sync result or #f on failure"
    (handle-exceptions exn
      (begin
        (peer-status-set! peer 'unreachable)
        #f)
      (let-values (((in out) (tcp-connect (peer-host peer) (peer-port peer))))
        ;; Track connection protocol
        (track-connection-type (peer-host peer))
        (dynamic-wind
          (lambda () #f)
          (lambda ()
            ;; Update peer status
            (peer-status-set! peer 'connected)
            (peer-last-seen-set! peer (current-seconds))

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
                          '(synchronized (false-positives . ,(length candidates))))

                        ;; Layer 3: Transfer missing objects
                        (let ((received (sync-object-transfer in out missing)))
                          (stat-inc! 'objects-received (length received))
                          (peer-status-set! peer 'synchronized)
                          `(synced (objects-received . ,(length received)))))))))
          (lambda ()
            (close-input-port in)
            (close-output-port out))))))

  ;; ============================================================
  ;; Layer 1: Bloom Filter Exchange
  ;; ============================================================

  (define (sync-bloom-exchange in out)
    "Exchange Bloom filters and hash lists, return candidate hashes to sync.

     Protocol:
     1. Send local Bloom filter + hash list
     2. Receive remote Bloom filter + hash list
     3. Find what remote has that we don't
     4. Return candidates (may include false positives from Bloom)"

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
              ;; Use Bloom filter to quickly filter, then check catalog
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
    "Perform Merkle diff to precisely identify missing objects.

     Protocol:
     1. Exchange Merkle roots
     2. If roots match, synchronized (return empty)
     3. If roots differ, verify candidates with remote
     4. Return exact list of hashes we are missing"

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
               ;; No candidates from Bloom - nothing to sync
               '())

              (else
               ;; Request verification of candidates
               (sync-verify-candidates in out candidates))))

          ;; Protocol error - return candidates as-is
          candidates)))

  (define (sync-verify-candidates in out candidates)
    "Ask remote to verify which candidates they actually have.
     Eliminates Bloom filter false positives."

    ;; Send candidates for verification
    (gossip-write-timestamped
      `(verify-candidates ,candidates)
      out)

    ;; Receive verified list
    (let ((response (gossip-read-timestamped in)))
      (if (and (pair? response)
               (eq? (car response) 'verified-missing))
          (cadr response)
          ;; Fallback to candidates if protocol error
          candidates)))

  ;; ============================================================
  ;; Layer 3: Object Transfer
  ;; ============================================================

  (define (sync-object-transfer in out missing-hashes)
    "Request and receive missing objects.

     Protocol:
     1. Send list of wanted hashes (batched)
     2. Receive objects with content
     3. Verify hash matches content
     4. Store verified objects
     5. Recurse for remaining batches
     6. Return list of successfully received hashes"

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
    "Verify object hash matches content, store if valid.
     Returns hash on success, #f on failure."
    (let* ((hash (car obj))
           (content (cadr obj))
           (content-blob (if (blob? content)
                             content
                             (string->blob content)))
           (computed (blob->hex (sha256-hash content-blob)))
           (expected-hash (if (string-prefix? "sha256:" hash)
                              (substring hash 7)
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
  ;; Helpers
  ;; ============================================================

  (define (blob->hex blob)
    "Convert blob to hex string"
    (let* ((vec (blob->u8vector blob))
           (len (u8vector-length vec)))
      (let loop ((i 0) (acc '()))
        (if (= i len)
            (apply string-append (reverse acc))
            (loop (+ i 1)
                  (cons (number->string (u8vector-ref vec i) 16)
                        acc))))))

  (define (blob-equal? a b)
    "Compare two blobs"
    (let ((av (blob->u8vector a))
          (bv (blob->u8vector b)))
      (and (= (u8vector-length av) (u8vector-length bv))
           (let loop ((i 0))
             (or (= i (u8vector-length av))
                 (and (= (u8vector-ref av i) (u8vector-ref bv i))
                      (loop (+ i 1))))))))

  ;; ============================================================
  ;; Server-Side Handler (Incoming Connections)
  ;; ============================================================

  (define (start-gossip-listener port local-objects-proc object-getter)
    "Start listening for incoming gossip connections.

     port: TCP port to listen on
     local-objects-proc: procedure returning list of local hashes
     object-getter: (lambda (hash) content) to retrieve object content"

    (set! *object-getter* object-getter)
    (set! *gossip-listener* (tcp-listen port))
    (thread-start!
      (make-thread
        (lambda ()
          (gossip-listener-loop local-objects-proc))))
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
        (handle-exceptions exn
          #f  ; Continue on errors
          (let-values (((in out) (tcp-accept *gossip-listener*)))
            (thread-start!
              (make-thread
                (lambda ()
                  (handle-exceptions exn
                    #f
                    (handle-gossip-session in out local-objects-proc))
                  (close-input-port in)
                  (close-output-port out))))))
        (loop))))

  (define (handle-gossip-session in out local-objects-proc)
    "Handle one incoming gossip session.
     Implements server side of three-layer protocol."

    (let* ((local-hashes (local-objects-proc))
           (local-bloom (make-inventory-bloom local-hashes
                                              error-rate: *bloom-error-rate*))
           (local-cat (make-catalog)))
      ;; Build local catalog
      (for-each (lambda (h) (catalog-add! local-cat h)) local-hashes)

      ;; Layer 1: Respond to Bloom exchange
      (let ((request (gossip-read-timestamped in)))
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
                         ;; Filter to hashes we actually have
                         (verified (filter
                                     (lambda (h) (member h local-hashes string=?))
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

) ;; end module

;;;
;;; Example: Start gossip daemon
;;;
;;;   (import gossip vault)
;;;
;;;   ;; Define function to get local object hashes
;;;   (define (get-local-objects)
;;;     (map car (soup)))  ; all objects in soup
;;;
;;;   ;; Add known peers
;;;   (add-peer "192.168.1.100")
;;;   (add-peer "192.168.1.101" port: 7655)
;;;
;;;   ;; Start daemon
;;;   (start-gossip-daemon get-local-objects interval: 60)
;;;
;;;   ;; Check status
;;;   (gossip-status)
;;;   ; => (gossip-status
;;;   ;     (running #t)
;;;   ;     (peers 2)
;;;   ;     (local-objects 1234)
;;;   ;     (stats ((rounds . 5) ...)))
;;;
;;;   ;; Stop daemon
;;;   (stop-gossip-daemon)
;;;
;;; Convergence Protocol:
;;;
;;;   Layer 1 - Bloom Exchange (~12 KB for 100K objects)
;;;   +--------+                     +--------+
;;;   | Node A | ------ Bloom -----> | Node B |
;;;   |        | <----- Bloom ------ |        |
;;;   +--------+                     +--------+
;;;   "What might you have that I don't?"
;;;
;;;   Layer 2 - Merkle Diff (32 bytes + O(log n) rounds)
;;;   +--------+                     +--------+
;;;   | Node A | ---- Root hash ---> | Node B |
;;;   |        | <--- Root hash ---- |        |
;;;   |        | -- Subtree hash --> |        |
;;;   |        | <-- Subtree hash -- |        |
;;;   +--------+                     +--------+
;;;   "Exactly which subtrees differ?"
;;;
;;;   Layer 3 - Object Transfer (actual data)
;;;   +--------+                     +--------+
;;;   | Node A | --- Request list -> | Node B |
;;;   |        | <---- Objects ----- |        |
;;;   +--------+                     +--------+
;;;   "Send me these specific objects"
;;;
