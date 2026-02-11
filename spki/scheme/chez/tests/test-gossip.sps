;;; Gossip Protocol Tests - Chez Scheme Port
;;; Tests peer management, epidemic broadcast, stats, convergence helpers.

(import (rnrs)
        (only (chezscheme) printf format)
        (cyberspace test)
        (cyberspace gossip)
        (cyberspace crypto-ffi))

;; Initialize libsodium
(sodium-init)

(printf "~n=== Gossip Protocol Tests ===~n~n")

;; --- Peer Management ---

(test "add-peer returns key"
  (lambda ()
    (let ((key (add-peer "10.0.0.1")))
      (string=? key "10.0.0.1:7655"))))

(test "add-peer with custom port"
  (lambda ()
    (let ((key (add-peer "10.0.0.2" 'port: 9000)))
      (string=? key "10.0.0.2:9000"))))

(test "list-peers returns added peers"
  (lambda ()
    (let ((peers (list-peers)))
      (>= (length peers) 2))))

(test "get-peer-status returns alist"
  (lambda ()
    (let ((status (get-peer-status "10.0.0.1")))
      (and status
           (assq 'host status)
           (assq 'trust-level status)))))

(test "set-peer-trust-level! changes trust"
  (lambda ()
    (set-peer-trust-level! "10.0.0.1" 'verified)
    (let ((status (get-peer-status "10.0.0.1")))
      (eq? 'verified (cadr (assq 'trust-level status))))))

(test "set-peer-role! changes role"
  (lambda ()
    (set-peer-role! "10.0.0.1" 'publisher)
    (let ((status (get-peer-status "10.0.0.1")))
      (eq? 'publisher (cadr (assq 'role status))))))

(test "remove-peer removes peer"
  (lambda ()
    (remove-peer "10.0.0.2" 'port: 9000)
    (not (get-peer-status "10.0.0.2" 'port: 9000))))

;; --- Statistics ---

(test "gossip-stats returns alist"
  (lambda ()
    (let ((stats (gossip-stats)))
      (and (assq 'rounds stats)
           (assq 'objects-sent stats)
           (assq 'bytes-sent stats)))))

(test "reset-stats! zeros counters"
  (lambda ()
    (reset-stats!)
    (let ((stats (gossip-stats)))
      (= 0 (cdr (assq 'rounds stats))))))

;; --- Gossip Status ---

(test "gossip-status reports not running"
  (lambda ()
    (let ((status (gossip-status)))
      (and (eq? (car status) 'gossip-status)
           (not (cadr (assq 'running (cdr status))))))))

;; --- Verbose Toggle ---

(test "gossip-verbose! enables verbose"
  (lambda ()
    (gossip-verbose! #t)
    (gossip-verbose?)))

(test "gossip-verbose! disables verbose"
  (lambda ()
    (gossip-verbose! #f)
    (not (gossip-verbose?))))

;; --- Configure From Scaling ---

(test "configure-from-scaling! returns config"
  (lambda ()
    (let ((result (configure-from-scaling! 0.5 2.0 75 20)))
      (and (eq? (car result) 'gossip-configured)
           (= 0.5 (cadr (assq 'scale (cdr result))))))))

;; --- Gossip Envelope (Epidemic Broadcast) ---

(test "make-gossip-envelope creates envelope"
  (lambda ()
    (let ((env (make-gossip-envelope "origin-node" 0 5 '() '(test-data))))
      (gossip-envelope? env))))

(test "gossip-envelope accessors"
  (lambda ()
    (let ((env (make-gossip-envelope "node-A" 2 7 '("node-B") '(payload 123))))
      (and (string=? "node-A" (gossip-envelope-origin env))
           (= 2 (gossip-envelope-hop-count env))
           (= 7 (gossip-envelope-ttl env))
           (equal? '("node-B") (gossip-envelope-seen env))
           (equal? '(payload 123) (gossip-envelope-payload env))))))

(test "gossip-envelope? rejects non-envelopes"
  (lambda ()
    (not (gossip-envelope? '(not an envelope)))))

;; --- Peer Availability ---

(test "peer-reset-failures! revives dead peer"
  (lambda ()
    (add-peer "10.0.0.99" 'trust-level: 'known)
    (peer-reset-failures! "10.0.0.99")
    (let ((status (get-peer-status "10.0.0.99")))
      (and status (eq? 'unknown (cadr (assq 'status status)))))))

;; --- Cleanup ---
(remove-peer "10.0.0.1")
(remove-peer "10.0.0.99")

(test-summary)
