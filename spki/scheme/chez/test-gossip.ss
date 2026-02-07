;;; Gossip Protocol Test Suite
;;; Library of Cyberspace - Chez Port
;;;
;;; Tests the gossip protocol data structures, peer management,
;;; statistics, Lamport-timestamped I/O, and convergence helpers.
;;;
;;; Note: Full network integration tests require two running nodes.
;;; This suite tests the unit-level components that don't need TCP.

(import (rnrs)
        (only (chezscheme) printf format void)
        (cyberspace chicken-compatibility chicken)
        (cyberspace chicken-compatibility hashtable)
        (cyberspace chicken-compatibility blob)
        (cyberspace crypto-ffi)
        (cyberspace bloom)
        (cyberspace catalog)
        (cyberspace vault)
        (cyberspace gossip))

;; ============================================================
;; Test harness
;; ============================================================

(define *pass* 0)
(define *fail* 0)

(define (check name ok?)
  (if ok?
      (begin
        (printf "  pass ~a\n" name)
        (set! *pass* (+ *pass* 1)))
      (begin
        (printf "  FAIL ~a\n" name)
        (set! *fail* (+ *fail* 1)))))

(printf "\n=== Gossip Protocol Test Suite ===\n\n")

;; Init sodium
(sodium-init)

;; ============================================================
;; Peer Management
;; ============================================================

(printf "--- Peer Management ---\n")

(let ((key (add-peer "192.168.1.100")))
  (check "add-peer returns key" (string? key))
  (check "add-peer key format" (string=? key "192.168.1.100:7655")))

(let ((key (add-peer "192.168.1.101" 'port: 8080)))
  (check "add-peer custom port" (string=? key "192.168.1.101:8080")))

(let ((peers (list-peers)))
  (check "list-peers" (>= (length peers) 2))
  (check "peer has host" (assq 'host (cdr (car peers)))))

(let ((status (get-peer-status "192.168.1.100")))
  (check "get-peer-status" (pair? status))
  (check "status trust-level" (eq? (cadr (assq 'trust-level status)) 'unknown))
  (check "status role" (eq? (cadr (assq 'role status)) 'peer)))

;; Trust levels
(set-peer-trust-level! "192.168.1.100" 'verified)
(let ((status (get-peer-status "192.168.1.100")))
  (check "set trust level" (eq? (cadr (assq 'trust-level status)) 'verified)))

;; Roles
(set-peer-role! "192.168.1.100" 'publisher)
(let ((status (get-peer-status "192.168.1.100")))
  (check "set role" (eq? (cadr (assq 'role status)) 'publisher)))

;; Remove peer
(remove-peer "192.168.1.101" 'port: 8080)
(check "remove-peer" (not (get-peer-status "192.168.1.101" 'port: 8080)))

;; Reset all peers for clean state
(remove-peer "192.168.1.100")

(printf "\n--- Peer Failure Tracking ---\n")

;; Test peer availability and backoff logic
(add-peer "10.0.0.1")
(let ((status (get-peer-status "10.0.0.1")))
  (check "new peer has status" (pair? status)))

;; Clean up
(remove-peer "10.0.0.1")

;; ============================================================
;; Statistics
;; ============================================================

(printf "\n--- Statistics ---\n")

(reset-stats!)
(let ((stats (gossip-stats)))
  (check "stats is alist" (pair? stats))
  (check "rounds = 0" (= (cdr (assq 'rounds stats)) 0))
  (check "objects-sent = 0" (= (cdr (assq 'objects-sent stats)) 0))
  (check "bloom-exchanges = 0" (= (cdr (assq 'bloom-exchanges stats)) 0)))

;; ============================================================
;; Gossip Status (without running daemon)
;; ============================================================

(printf "\n--- Gossip Status ---\n")

(let ((status (gossip-status)))
  (check "gossip-status" (pair? status))
  (check "status running" (eq? (car status) 'gossip-status))
  (check "not running" (not (cadr (assq 'running (cdr status))))))

;; ============================================================
;; Verbose Toggle
;; ============================================================

(printf "\n--- Verbose ---\n")

(let ((msg (gossip-verbose! #t)))
  (check "verbose enable" (string? msg))
  (check "verbose flag" *gossip-verbose*))

(gossip-verbose! #f)
(check "verbose disable" (not *gossip-verbose*))

;; ============================================================
;; Scaling Configuration
;; ============================================================

(printf "\n--- Scaling Configuration ---\n")

(let ((result (configure-from-scaling! 0.8 2.5 50 45)))
  (check "configure-from-scaling" (pair? result))
  (check "config result" (eq? (car result) 'gossip-configured)))

;; ============================================================
;; Bytevector->hex Helper (used in object verification)
;; ============================================================

(printf "\n--- Hex Conversion ---\n")

;; Test via SHA-256 hash and format
(let* ((data (string->utf8 "hello"))
       (hash (sha256-hash data)))
  (check "sha256 produces bytevector" (bytevector? hash))
  (check "sha256 length" (= (bytevector-length hash) 32)))

;; ============================================================
;; Chicken Compat Utilities (used by gossip)
;; ============================================================

(printf "\n--- Utility Functions ---\n")

;; filter-map
(check "filter-map"
  (equal? (filter-map (lambda (x) (and (> x 2) (* x 10)))
                      '(1 2 3 4 5))
          '(30 40 50)))

;; take
(check "take" (equal? (take '(a b c d e) 3) '(a b c)))
(check "take 0" (null? (take '(a b c) 0)))
(check "take all" (equal? (take '(a b) 5) '(a b)))

;; drop
(check "drop" (equal? (drop '(a b c d e) 2) '(c d e)))
(check "drop 0" (equal? (drop '(a b c) 0) '(a b c)))

;; string-contains
(check "string-contains found" (= (string-contains "hello world" "world") 6))
(check "string-contains not found" (not (string-contains "hello" "xyz")))

;; string-prefix?
(check "string-prefix? yes" (string-prefix? "sha256:" "sha256:abc123"))
(check "string-prefix? no" (not (string-prefix? "sha512:" "sha256:abc123")))

;; string-trim-both
(check "string-trim-both" (string=? (string-trim-both "  hello  ") "hello"))
(check "string-trim-both tabs" (string=? (string-trim-both "\t hi \n") "hi"))

;; current-seconds
(let ((t (current-seconds)))
  (check "current-seconds" (and (integer? t) (> t 0))))

;; ============================================================
;; Lamport Clock Integration
;; ============================================================

(printf "\n--- Lamport Clock Integration ---\n")

(let* ((t0 (lamport-time))
       (msg (lamport-send '(test-data)))
       (t1 (lamport-time)))
  (check "lamport-send increments" (> t1 t0))
  (check "lamport-send returns alist"
    (and (pair? msg) (assq 'lamport-time msg) (assq 'payload msg)))
  (check "lamport-send payload"
    (equal? (cdr (assq 'payload msg)) '(test-data))))

;; ============================================================
;; Bloom + Catalog Integration
;; ============================================================

(printf "\n--- Bloom + Catalog Integration ---\n")

(let* ((hashes '("sha256:abc" "sha256:def" "sha256:ghi"))
       (cat (make-catalog))
       (bloom (make-inventory-bloom hashes)))
  (for-each (lambda (h) (catalog-add! cat h)) hashes)
  (check "catalog size" (= (catalog-size cat) 3))
  (check "catalog contains" (catalog-contains? cat "sha256:abc"))
  (check "bloom contains" (blocked-bloom-contains? bloom "sha256:abc")))

;; ============================================================
;; Capability Registration
;; ============================================================

(printf "\n--- Capabilities ---\n")

(check "has ed25519-sign" (capability? 'ed25519-sign))
(check "has sha256-hash" (capability? 'sha256-hash))
(check "has lamport-clock" (capability? 'lamport-clock))

;; ============================================================
;; Results
;; ============================================================

(printf "\n=== Results: ~a passed, ~a failed ===\n\n" *pass* *fail*)

(if (= *fail* 0)
    (printf "Gossip: GO\n\n")
    (begin
      (printf "Gossip: FAIL\n\n")
      (exit 1)))
