#!/usr/bin/env csi -s
;;; test-gossip.scm - Gossip protocol tests for federation
;;;
;;; Tests peer management, state tracking, and convergence protocol
;;; components. Network tests use local connections.

(import scheme
        (chicken base)
        (chicken blob)
        (chicken format)
        (chicken condition)
        (chicken time)
        srfi-1
        srfi-4
        srfi-18
        gossip
        bloom
        catalog
        crypto-ffi)

;; Initialize libsodium
(sodium-init)

;; ============================================================
;; Test Framework
;; ============================================================

(define *tests-run* 0)
(define *tests-passed* 0)
(define *tests-failed* '())

(define (test name thunk)
  (set! *tests-run* (+ 1 *tests-run*))
  (handle-exceptions exn
    (begin
      (printf "FAIL: ~a~n" name)
      (printf "      ~a~n" (get-condition-property exn 'exn 'message "unknown error"))
      (set! *tests-failed* (cons name *tests-failed*)))
    (let ((result (thunk)))
      (if result
          (begin
            (printf "PASS: ~a~n" name)
            (set! *tests-passed* (+ 1 *tests-passed*)))
          (begin
            (printf "FAIL: ~a (returned #f)~n" name)
            (set! *tests-failed* (cons name *tests-failed*)))))))

(define (assert-equal expected actual)
  (or (equal? expected actual)
      (error (sprintf "expected ~s, got ~s" expected actual))))

(define (assert-true val)
  (or val (error "expected truthy value")))

;; ============================================================
;; Peer Management Tests
;; ============================================================

(printf "~n=== Gossip Protocol Tests ===~n~n")
(printf "--- Peer Management ---~n")

(test "add-peer creates peer entry"
  (lambda ()
    (let ((key (add-peer "192.168.1.100")))
      (assert-true key)
      (string=? key "192.168.1.100:7655"))))

(test "add-peer with custom port"
  (lambda ()
    (let ((key (add-peer "192.168.1.101" port: 9000)))
      (string=? key "192.168.1.101:9000"))))

(test "list-peers returns added peers"
  (lambda ()
    (let ((peers (list-peers)))
      (> (length peers) 0))))

(test "get-peer-status returns info for known peer"
  (lambda ()
    (add-peer "192.168.1.102")
    (let ((status (get-peer-status "192.168.1.102")))
      (and status
           (assq 'host status)
           (assq 'status status)))))

(test "get-peer-status returns #f for unknown peer"
  (lambda ()
    (not (get-peer-status "192.168.1.255"))))

(test "remove-peer removes entry"
  (lambda ()
    (add-peer "192.168.1.103")
    (remove-peer "192.168.1.103")
    (not (get-peer-status "192.168.1.103"))))

;; ============================================================
;; Statistics Tests
;; ============================================================

(printf "~n--- Statistics ---~n")

(test "gossip-stats returns initial state"
  (lambda ()
    (reset-stats!)
    (let ((stats (gossip-stats)))
      (and (assq 'rounds stats)
           (assq 'objects-sent stats)
           (assq 'objects-received stats)))))

(test "reset-stats! clears counters"
  (lambda ()
    (reset-stats!)
    (let ((stats (gossip-stats)))
      (and (= 0 (cdr (assq 'rounds stats)))
           (= 0 (cdr (assq 'objects-sent stats)))))))

;; ============================================================
;; Gossip Status Tests
;; ============================================================

(printf "~n--- Gossip Status ---~n")

(test "gossip-status reports not running initially"
  (lambda ()
    (stop-gossip-daemon)
    (let* ((status (gossip-status))
           (alist (cdr status)))  ; skip 'gossip-status symbol
      (and (assq 'running alist)
           (not (cadr (assq 'running alist)))))))

(test "gossip-status includes peer count"
  (lambda ()
    (let* ((status (gossip-status))
           (alist (cdr status)))  ; skip 'gossip-status symbol
      (assq 'peers alist))))

;; ============================================================
;; Convergence Protocol Component Tests
;; ============================================================

(printf "~n--- Convergence Protocol Components ---~n")

;; Test Bloom filter creation for inventory
(test "inventory bloom creation works"
  (lambda ()
    (let* ((hashes '("sha256:abc" "sha256:def" "sha256:ghi"))
           (bloom (make-inventory-bloom hashes)))
      (and (blocked-bloom-contains? bloom (string->blob "sha256:abc"))
           (blocked-bloom-contains? bloom (string->blob "sha256:def"))
           (blocked-bloom-contains? bloom (string->blob "sha256:ghi"))))))

;; Test catalog creation for Merkle root
(test "catalog root for convergence"
  (lambda ()
    (let ((cat (make-catalog)))
      (catalog-add! cat "sha256:aaa")
      (catalog-add! cat "sha256:bbb")
      (blob? (catalog-root cat)))))

;; Test bloom serialization for network transfer
(test "bloom serialization for network transfer"
  (lambda ()
    (let* ((hashes '("sha256:test1" "sha256:test2"))
           (bloom (make-inventory-bloom hashes))
           (serialized (blocked-bloom-serialize bloom))
           (restored (blocked-bloom-deserialize serialized)))
      (and (blocked-bloom-contains? restored (string->blob "sha256:test1"))
           (blocked-bloom-contains? restored (string->blob "sha256:test2"))))))

;; Test catalog serialization for network transfer
(test "catalog serialization for network transfer"
  (lambda ()
    (let ((cat (make-catalog)))
      (catalog-add! cat "sha256:aaa")
      (catalog-add! cat "sha256:bbb")
      (let* ((serialized (catalog-serialize cat))
             (restored (catalog-deserialize serialized)))
        (and (catalog-contains? restored "sha256:aaa")
             (catalog-contains? restored "sha256:bbb"))))))

;; ============================================================
;; Simulated Sync Scenario Tests
;; ============================================================

(printf "~n--- Simulated Sync Scenarios ---~n")

(test "simulated: nodes with same inventory converge"
  (lambda ()
    (let ((node-a-hashes '("sha256:file1" "sha256:file2"))
          (node-b-hashes '("sha256:file1" "sha256:file2")))
      (let ((cat-a (make-catalog))
            (cat-b (make-catalog)))
        (for-each (lambda (h) (catalog-add! cat-a h)) node-a-hashes)
        (for-each (lambda (h) (catalog-add! cat-b h)) node-b-hashes)
        ;; Same roots should indicate synchronized
        (let ((root-a (blob->u8vector (catalog-root cat-a)))
              (root-b (blob->u8vector (catalog-root cat-b))))
          (equal? (u8vector->list root-a) (u8vector->list root-b)))))))

(test "simulated: nodes with different inventory detect difference"
  (lambda ()
    (let ((node-a-hashes '("sha256:file1" "sha256:file2"))
          (node-b-hashes '("sha256:file1" "sha256:file3")))
      (let ((cat-a (make-catalog))
            (cat-b (make-catalog)))
        (for-each (lambda (h) (catalog-add! cat-a h)) node-a-hashes)
        (for-each (lambda (h) (catalog-add! cat-b h)) node-b-hashes)
        ;; Different roots indicate need for sync
        (let ((root-a (blob->u8vector (catalog-root cat-a)))
              (root-b (blob->u8vector (catalog-root cat-b))))
          (not (equal? (u8vector->list root-a) (u8vector->list root-b))))))))

(test "simulated: bloom filter detects potential missing items"
  (lambda ()
    (let ((local-hashes '("sha256:local1" "sha256:shared"))
          (remote-hashes '("sha256:remote1" "sha256:shared")))
      (let ((local-bloom (make-inventory-bloom local-hashes))
            (remote-bloom (make-inventory-bloom remote-hashes)))
        ;; Remote has remote1 which local doesn't have
        (and (blocked-bloom-contains? remote-bloom (string->blob "sha256:remote1"))
             (not (blocked-bloom-contains? local-bloom (string->blob "sha256:remote1"))))))))

(test "simulated: convergence after merge"
  (lambda ()
    (let ((node-a-hashes '("sha256:file1" "sha256:file2"))
          (node-b-hashes '("sha256:file2" "sha256:file3")))
      (let ((cat-a (make-catalog))
            (cat-b (make-catalog)))
        (for-each (lambda (h) (catalog-add! cat-a h)) node-a-hashes)
        (for-each (lambda (h) (catalog-add! cat-b h)) node-b-hashes)

        ;; Simulate sync: A gets B's items, B gets A's items
        (catalog-merge-diff cat-a '("sha256:file3"))
        (catalog-merge-diff cat-b '("sha256:file1"))

        ;; Now both should have all items
        (and (= 3 (catalog-size cat-a))
             (= 3 (catalog-size cat-b))
             (let ((root-a (blob->u8vector (catalog-root cat-a)))
                   (root-b (blob->u8vector (catalog-root cat-b))))
               (equal? (u8vector->list root-a) (u8vector->list root-b))))))))

;; ============================================================
;; Three-Layer Convergence Simulation
;; ============================================================

(printf "~n--- Three-Layer Convergence Simulation ---~n")

(test "layer 1: bloom exchange identifies candidates"
  (lambda ()
    ;; Node A has {1,2,3}, Node B has {2,3,4}
    (let ((a-hashes '("sha256:1" "sha256:2" "sha256:3"))
          (b-hashes '("sha256:2" "sha256:3" "sha256:4")))
      (let ((a-bloom (make-inventory-bloom a-hashes))
            (b-bloom (make-inventory-bloom b-hashes)))
        ;; B's bloom should contain sha256:4 (which A doesn't have)
        ;; This is the candidate A needs to check
        (blocked-bloom-contains? b-bloom (string->blob "sha256:4"))))))

(test "layer 2: merkle root comparison"
  (lambda ()
    ;; Same items = same root
    (let ((cat1 (make-catalog))
          (cat2 (make-catalog)))
      (catalog-add! cat1 "sha256:same")
      (catalog-add! cat2 "sha256:same")
      (let-values (((missing extra) (catalog-diff cat1 (catalog-root cat2))))
        (and (null? missing) (null? extra))))))

(test "layer 3: object transfer simulation"
  (lambda ()
    ;; Simulate receiving objects and verifying hashes
    (let* ((object-data "the actual content of the object")
           (computed-hash (sha256-hash (string->blob object-data)))
           (expected-hash (sha256-hash (string->blob object-data))))
      ;; Verify hash matches
      (let ((c (blob->u8vector computed-hash))
            (e (blob->u8vector expected-hash)))
        (equal? (u8vector->list c) (u8vector->list e))))))

;; ============================================================
;; Edge Cases
;; ============================================================

(printf "~n--- Edge Cases ---~n")

(test "empty inventory bloom filter"
  (lambda ()
    (let ((bloom (make-inventory-bloom '())))
      bloom)))

(test "single item inventory"
  (lambda ()
    (let ((bloom (make-inventory-bloom '("sha256:only"))))
      (blocked-bloom-contains? bloom (string->blob "sha256:only")))))

(test "large inventory (10K items)"
  (lambda ()
    (let ((hashes (map (lambda (i) (sprintf "sha256:~a" i)) (iota 10000))))
      (let ((bloom (make-inventory-bloom hashes error-rate: 0.01)))
        (and (blocked-bloom-contains? bloom (string->blob "sha256:0"))
             (blocked-bloom-contains? bloom (string->blob "sha256:9999")))))))

;; ============================================================
;; Summary
;; ============================================================

(printf "~n=== Results ===~n")
(printf "Passed: ~a/~a~n" *tests-passed* *tests-run*)
(when (> (length *tests-failed*) 0)
  (printf "Failed:~n")
  (for-each (lambda (n) (printf "  - ~a~n" n)) (reverse *tests-failed*)))
(newline)

;; Exit with error code if tests failed
(when (> (length *tests-failed*) 0)
  (exit 1))
