;;; Bloom Filter Tests - Chez Scheme Port
;;; Tests standard, blocked, and counting Bloom filters.

(import (rnrs)
        (only (chezscheme) printf format)
        (cyberspace chicken-compatibility blob)
        (cyberspace test)
        (cyberspace bloom)
        (cyberspace crypto-ffi))

;; Initialize libsodium
(sodium-init)

;; Helper
(define (iota n)
  (let loop ((i 0) (acc '()))
    (if (= i n) (reverse acc) (loop (+ i 1) (cons i acc)))))

(printf "~n=== Bloom Filter Tests ===~n~n")
(printf "--- Standard Bloom Filter ---~n")

(test "make-bloom creates filter with correct parameters"
  (lambda ()
    (let ((bf (make-bloom 'capacity: 1000 'error-rate: 0.01)))
      (assert-true bf)
      (assert-equal 0 (bloom-count bf)))))

(test "bloom-add! increments count"
  (lambda ()
    (let ((bf (make-bloom 'capacity: 100)))
      (bloom-add! bf (string->blob "test1"))
      (assert-equal 1 (bloom-count bf))
      (bloom-add! bf (string->blob "test2"))
      (assert-equal 2 (bloom-count bf)))))

(test "bloom-contains? finds added elements"
  (lambda ()
    (let ((bf (make-bloom 'capacity: 100)))
      (bloom-add! bf (string->blob "hello"))
      (bloom-add! bf (string->blob "world"))
      (and (bloom-contains? bf (string->blob "hello"))
           (bloom-contains? bf (string->blob "world"))))))

(test "bloom-contains? rejects unknown elements (probabilistic)"
  (lambda ()
    (let ((bf (make-bloom 'capacity: 1000 'error-rate: 0.001)))
      (bloom-add! bf (string->blob "known"))
      (let ((fp-count 0))
        (do ((i 0 (+ i 1)))
            ((= i 100))
          (when (bloom-contains? bf (string->blob (format #f "unknown-~a" i)))
            (set! fp-count (+ fp-count 1))))
        (< fp-count 5)))))

(test "bloom-merge! combines two filters"
  (lambda ()
    (let ((bf1 (make-bloom 'capacity: 100))
          (bf2 (make-bloom 'capacity: 100)))
      (bloom-add! bf1 (string->blob "from-bf1"))
      (bloom-add! bf2 (string->blob "from-bf2"))
      (bloom-merge! bf1 bf2)
      (and (bloom-contains? bf1 (string->blob "from-bf1"))
           (bloom-contains? bf1 (string->blob "from-bf2"))))))

(test "bloom-serialize/deserialize roundtrips"
  (lambda ()
    (let* ((bf (make-bloom 'capacity: 100))
           (_ (bloom-add! bf (string->blob "test")))
           (serialized (bloom-serialize bf))
           (bf2 (bloom-deserialize serialized)))
      (and (bloom-contains? bf2 (string->blob "test"))
           (= (bloom-count bf) (bloom-count bf2))))))

;; Blocked Bloom Filter
(printf "~n--- Blocked Bloom Filter ---~n")

(test "make-blocked-bloom creates filter"
  (lambda ()
    (let ((bf (make-blocked-bloom 'capacity: 1000 'error-rate: 0.01)))
      (assert-true bf))))

(test "blocked-bloom-add!/contains? works"
  (lambda ()
    (let ((bf (make-blocked-bloom 'capacity: 1000)))
      (blocked-bloom-add! bf (string->blob "hello"))
      (blocked-bloom-add! bf (string->blob "world"))
      (and (blocked-bloom-contains? bf (string->blob "hello"))
           (blocked-bloom-contains? bf (string->blob "world"))))))

(test "blocked-bloom-contains? rejects unknown (probabilistic)"
  (lambda ()
    (let ((bf (make-blocked-bloom 'capacity: 10000 'error-rate: 0.001)))
      (blocked-bloom-add! bf (string->blob "known"))
      (let ((fp-count 0))
        (do ((i 0 (+ i 1)))
            ((= i 100))
          (when (blocked-bloom-contains? bf (string->blob (format #f "unknown-~a" i)))
            (set! fp-count (+ fp-count 1))))
        (< fp-count 5)))))

(test "blocked-bloom-serialize/deserialize roundtrips"
  (lambda ()
    (let* ((bf (make-blocked-bloom 'capacity: 100))
           (_ (blocked-bloom-add! bf (string->blob "test")))
           (serialized (blocked-bloom-serialize bf))
           (bf2 (blocked-bloom-deserialize serialized)))
      (blocked-bloom-contains? bf2 (string->blob "test")))))

;; Counting Bloom Filter
(printf "~n--- Counting Bloom Filter ---~n")

(test "make-counting-bloom creates filter"
  (lambda ()
    (let ((bf (make-counting-bloom 'capacity: 1000 'error-rate: 0.01)))
      (assert-true bf)
      (assert-equal 0 (counting-bloom-count bf)))))

(test "counting-bloom-add!/contains? works"
  (lambda ()
    (let ((bf (make-counting-bloom 'capacity: 1000)))
      (counting-bloom-add! bf (string->blob "hello"))
      (counting-bloom-contains? bf (string->blob "hello")))))

(test "counting-bloom-remove! removes elements"
  (lambda ()
    (let ((bf (make-counting-bloom 'capacity: 1000)))
      (counting-bloom-add! bf (string->blob "temp"))
      (assert-true (counting-bloom-contains? bf (string->blob "temp")))
      (counting-bloom-remove! bf (string->blob "temp"))
      (not (counting-bloom-contains? bf (string->blob "temp"))))))

(test "counting-bloom handles multiple adds of same element"
  (lambda ()
    (let ((bf (make-counting-bloom 'capacity: 1000)))
      (counting-bloom-add! bf (string->blob "multi"))
      (counting-bloom-add! bf (string->blob "multi"))
      (counting-bloom-add! bf (string->blob "multi"))
      (assert-true (counting-bloom-contains? bf (string->blob "multi")))
      (counting-bloom-remove! bf (string->blob "multi"))
      (assert-true (counting-bloom-contains? bf (string->blob "multi")))
      (counting-bloom-remove! bf (string->blob "multi"))
      (counting-bloom-remove! bf (string->blob "multi"))
      (not (counting-bloom-contains? bf (string->blob "multi"))))))

;; Inventory Operations
(printf "~n--- Inventory Operations ---~n")

(test "make-inventory-bloom creates from hash list"
  (lambda ()
    (let* ((hashes '("sha256:abc123" "sha256:def456" "sha256:ghi789"))
           (bloom (make-inventory-bloom hashes)))
      (and (blocked-bloom-contains? bloom (string->blob "sha256:abc123"))
           (blocked-bloom-contains? bloom (string->blob "sha256:def456"))
           (blocked-bloom-contains? bloom (string->blob "sha256:ghi789"))))))

(test "make-inventory-bloom handles empty list"
  (lambda ()
    (let ((bloom (make-inventory-bloom '())))
      (assert-true bloom))))

(test "make-inventory-bloom handles large list"
  (lambda ()
    (let* ((hashes (map (lambda (i) (format #f "sha256:hash~a" i)) (iota 10000)))
           (bloom (make-inventory-bloom hashes 'error-rate: 0.01)))
      (and (blocked-bloom-contains? bloom (string->blob "sha256:hash0"))
           (blocked-bloom-contains? bloom (string->blob "sha256:hash5000"))
           (blocked-bloom-contains? bloom (string->blob "sha256:hash9999"))))))

;; Optimal Parameters
(printf "~n--- Optimal Parameters ---~n")

(test "optimal-bloom-size calculates correctly"
  (lambda ()
    (let ((size (optimal-bloom-size 10000 0.01)))
      (and (> size 90000) (< size 100000)))))

(test "optimal-hash-count calculates correctly"
  (lambda ()
    (let* ((m 95851)
           (n 10000)
           (k (optimal-hash-count m n)))
      (and (>= k 6) (<= k 8)))))

(test "bloom-false-positive-rate estimates correctly"
  (lambda ()
    (let ((rate (bloom-false-positive-rate 95851 10000 7)))
      (and (> rate 0.005) (< rate 0.02)))))

(test-summary)
