#!/usr/bin/env csi -s
;;; test-catalog.scm - Merkle catalog tests for federation convergence
;;;
;;; Tests Merkle tree construction, diff detection, and proof verification.

(import scheme
        (chicken base)
        (chicken blob)
        (chicken format)
        (chicken condition)
        srfi-1
        srfi-4
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

(define (assert-false val)
  (or (not val) (error "expected falsy value")))

;; ============================================================
;; Basic Catalog Operations
;; ============================================================

(printf "~n=== Merkle Catalog Tests ===~n~n")
(printf "--- Basic Operations ---~n")

(test "make-catalog creates empty catalog"
  (lambda ()
    (let ((cat (make-catalog)))
      (and (assert-equal 0 (catalog-size cat))
           (not (catalog-root cat))))))

(test "catalog-add! adds items"
  (lambda ()
    (let ((cat (make-catalog)))
      (catalog-add! cat "sha256:abc123")
      (assert-equal 1 (catalog-size cat)))))

(test "catalog-add! is idempotent"
  (lambda ()
    (let ((cat (make-catalog)))
      (catalog-add! cat "sha256:abc123")
      (catalog-add! cat "sha256:abc123")
      (catalog-add! cat "sha256:abc123")
      (assert-equal 1 (catalog-size cat)))))

(test "catalog-contains? finds added items"
  (lambda ()
    (let ((cat (make-catalog)))
      (catalog-add! cat "sha256:abc123")
      (catalog-add! cat "sha256:def456")
      (and (catalog-contains? cat "sha256:abc123")
           (catalog-contains? cat "sha256:def456")
           (not (catalog-contains? cat "sha256:unknown"))))))

(test "catalog-remove! removes items"
  (lambda ()
    (let ((cat (make-catalog)))
      (catalog-add! cat "sha256:abc123")
      (catalog-add! cat "sha256:def456")
      (catalog-remove! cat "sha256:abc123")
      (and (not (catalog-contains? cat "sha256:abc123"))
           (catalog-contains? cat "sha256:def456")
           (= 1 (catalog-size cat))))))

(test "catalog->list returns sorted items"
  (lambda ()
    (let ((cat (make-catalog)))
      (catalog-add! cat "sha256:zzz")
      (catalog-add! cat "sha256:aaa")
      (catalog-add! cat "sha256:mmm")
      (equal? (catalog->list cat)
              '("sha256:aaa" "sha256:mmm" "sha256:zzz")))))

;; ============================================================
;; Merkle Root Tests
;; ============================================================

(printf "~n--- Merkle Root ---~n")

(test "empty catalog has no root"
  (lambda ()
    (let ((cat (make-catalog)))
      (not (catalog-root cat)))))

(test "single item catalog has root"
  (lambda ()
    (let ((cat (make-catalog)))
      (catalog-add! cat "sha256:only")
      (blob? (catalog-root cat)))))

(test "root changes when items added"
  (lambda ()
    (let ((cat (make-catalog)))
      (catalog-add! cat "sha256:first")
      (let ((root1 (catalog-root cat)))
        (catalog-add! cat "sha256:second")
        (let ((root2 (catalog-root cat)))
          (not (equal? root1 root2)))))))

(test "root is deterministic for same items"
  (lambda ()
    (let ((cat1 (make-catalog))
          (cat2 (make-catalog)))
      ;; Add in different order
      (catalog-add! cat1 "sha256:aaa")
      (catalog-add! cat1 "sha256:bbb")
      (catalog-add! cat1 "sha256:ccc")
      (catalog-add! cat2 "sha256:ccc")
      (catalog-add! cat2 "sha256:aaa")
      (catalog-add! cat2 "sha256:bbb")
      ;; Roots should match (sorted internally)
      (let ((r1 (blob->u8vector (catalog-root cat1)))
            (r2 (blob->u8vector (catalog-root cat2))))
        (equal? (u8vector->list r1) (u8vector->list r2))))))

(test "different items have different roots"
  (lambda ()
    (let ((cat1 (make-catalog))
          (cat2 (make-catalog)))
      (catalog-add! cat1 "sha256:aaa")
      (catalog-add! cat2 "sha256:bbb")
      (let ((r1 (blob->u8vector (catalog-root cat1)))
            (r2 (blob->u8vector (catalog-root cat2))))
        (not (equal? (u8vector->list r1) (u8vector->list r2)))))))

;; ============================================================
;; Merkle Diff Tests
;; ============================================================

(printf "~n--- Merkle Diff ---~n")

(test "catalog-diff with both empty"
  (lambda ()
    (let ((cat (make-catalog)))
      (let-values (((missing extra) (catalog-diff cat #f)))
        (and (null? missing) (null? extra))))))

(test "catalog-diff with matching roots"
  (lambda ()
    (let ((cat1 (make-catalog))
          (cat2 (make-catalog)))
      (catalog-add! cat1 "sha256:same")
      (catalog-add! cat2 "sha256:same")
      (let-values (((missing extra) (catalog-diff cat1 (catalog-root cat2))))
        (and (null? missing) (null? extra))))))

(test "catalog-diff detects remote empty"
  (lambda ()
    (let ((cat (make-catalog)))
      (catalog-add! cat "sha256:local")
      (let-values (((missing extra) (catalog-diff cat #f)))
        (equal? extra '("sha256:local"))))))

(test "catalog-diff detects local empty"
  (lambda ()
    (let ((cat (make-catalog))
          (remote-cat (make-catalog)))
      (catalog-add! remote-cat "sha256:remote")
      (let-values (((missing extra) (catalog-diff cat (catalog-root remote-cat))))
        (eq? missing 'need-full-sync)))))

(test "catalog-diff detects differences"
  (lambda ()
    (let ((local (make-catalog))
          (remote (make-catalog)))
      (catalog-add! local "sha256:local-only")
      (catalog-add! remote "sha256:remote-only")
      (let-values (((missing extra) (catalog-diff local (catalog-root remote))))
        ;; When roots differ, indicates sync needed
        (eq? missing 'subtree-diff-needed)))))

;; ============================================================
;; Merkle Proof Tests
;; ============================================================

(printf "~n--- Merkle Proofs ---~n")

(test "catalog-proof returns #f for missing item"
  (lambda ()
    (let ((cat (make-catalog)))
      (catalog-add! cat "sha256:exists")
      (not (catalog-proof cat "sha256:missing")))))

(test "catalog-proof returns proof for existing item"
  (lambda ()
    (let ((cat (make-catalog)))
      (catalog-add! cat "sha256:exists")
      (let ((proof (catalog-proof cat "sha256:exists")))
        (list? proof)))))

(test "catalog-verify-proof validates correct proof"
  (lambda ()
    (let ((cat (make-catalog)))
      (catalog-add! cat "sha256:aaa")
      (catalog-add! cat "sha256:bbb")
      (catalog-add! cat "sha256:ccc")
      (let ((proof (catalog-proof cat "sha256:bbb")))
        (catalog-verify-proof (catalog-root cat) "sha256:bbb" proof)))))

(test "catalog-verify-proof rejects wrong item"
  (lambda ()
    (let ((cat (make-catalog)))
      (catalog-add! cat "sha256:aaa")
      (catalog-add! cat "sha256:bbb")
      (let ((proof (catalog-proof cat "sha256:aaa")))
        ;; Proof for aaa should not verify bbb
        (not (catalog-verify-proof (catalog-root cat) "sha256:bbb" proof))))))

(test "catalog-verify-proof rejects tampered root"
  (lambda ()
    (let ((cat (make-catalog))
          (other-cat (make-catalog)))
      (catalog-add! cat "sha256:target")
      (catalog-add! other-cat "sha256:different")
      (let ((proof (catalog-proof cat "sha256:target")))
        ;; Proof should not verify against different root
        (not (catalog-verify-proof (catalog-root other-cat) "sha256:target" proof))))))

;; ============================================================
;; Serialization Tests
;; ============================================================

(printf "~n--- Serialization ---~n")

(test "catalog-serialize produces s-expression"
  (lambda ()
    (let ((cat (make-catalog)))
      (catalog-add! cat "sha256:test")
      (let ((ser (catalog-serialize cat)))
        (and (list? ser)
             (eq? (car ser) 'catalog))))))

(test "catalog-serialize/deserialize roundtrips"
  (lambda ()
    (let ((cat (make-catalog)))
      (catalog-add! cat "sha256:aaa")
      (catalog-add! cat "sha256:bbb")
      (catalog-add! cat "sha256:ccc")
      (let* ((ser (catalog-serialize cat))
             (cat2 (catalog-deserialize ser)))
        (and (= (catalog-size cat) (catalog-size cat2))
             (equal? (catalog->list cat) (catalog->list cat2)))))))

(test "catalog-merge-diff adds missing items"
  (lambda ()
    (let ((cat (make-catalog)))
      (catalog-add! cat "sha256:existing")
      (catalog-merge-diff cat '("sha256:new1" "sha256:new2"))
      (and (catalog-contains? cat "sha256:existing")
           (catalog-contains? cat "sha256:new1")
           (catalog-contains? cat "sha256:new2")
           (= 3 (catalog-size cat))))))

;; ============================================================
;; Hash Combine Tests
;; ============================================================

(printf "~n--- Hash Operations ---~n")

(test "hash-combine is deterministic"
  (lambda ()
    (let* ((h1 (sha256-hash (string->blob "left")))
           (h2 (sha256-hash (string->blob "right")))
           (combined1 (hash-combine h1 h2))
           (combined2 (hash-combine h1 h2)))
      (let ((c1 (blob->u8vector combined1))
            (c2 (blob->u8vector combined2)))
        (equal? (u8vector->list c1) (u8vector->list c2))))))

(test "hash-combine is order-sensitive"
  (lambda ()
    (let* ((h1 (sha256-hash (string->blob "left")))
           (h2 (sha256-hash (string->blob "right")))
           (lr (hash-combine h1 h2))
           (rl (hash-combine h2 h1)))
      (let ((lr-vec (blob->u8vector lr))
            (rl-vec (blob->u8vector rl)))
        (not (equal? (u8vector->list lr-vec) (u8vector->list rl-vec)))))))

;; ============================================================
;; Sorted Hash Tree Tests
;; ============================================================

(printf "~n--- Sorted Hash Tree ---~n")

(test "sorted-hash-tree handles empty list"
  (lambda ()
    (not (sorted-hash-tree '()))))

(test "sorted-hash-tree handles single item"
  (lambda ()
    (let ((tree (sorted-hash-tree '("single"))))
      tree)))

(test "sorted-hash-tree handles multiple items"
  (lambda ()
    (let ((tree (sorted-hash-tree '("aaa" "bbb" "ccc" "ddd"))))
      tree)))

;; ============================================================
;; Large Catalog Tests
;; ============================================================

(printf "~n--- Large Catalog ---~n")

(test "catalog handles 1000 items"
  (lambda ()
    (let ((cat (make-catalog)))
      (do ((i 0 (+ i 1)))
          ((= i 1000))
        (catalog-add! cat (sprintf "sha256:hash~a" i)))
      (and (= 1000 (catalog-size cat))
           (blob? (catalog-root cat))
           (catalog-contains? cat "sha256:hash0")
           (catalog-contains? cat "sha256:hash999")))))

(test "catalog proof works for large catalog"
  (lambda ()
    (let ((cat (make-catalog)))
      (do ((i 0 (+ i 1)))
          ((= i 100))
        (catalog-add! cat (sprintf "sha256:hash~a" i)))
      (let ((proof (catalog-proof cat "sha256:hash50")))
        (and proof
             (catalog-verify-proof (catalog-root cat) "sha256:hash50" proof))))))

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
