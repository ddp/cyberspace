;;; SPKI Scheme - Blocked Bloom Filters for Federation Convergence
;;;
;;; Provides space-efficient probabilistic set membership for:
;;; - Fast detection of missing objects during sync
;;; - Inventory exchange between federation peers
;;; - Content-addressed storage existence checking
;;;
;;; Implements blocked Bloom filters (cache-line aligned) for
;;; better CPU performance, plus counting Bloom for deletion support.

(module bloom
  (;; Standard Bloom filter
   make-bloom
   bloom-add!
   bloom-contains?
   bloom-count
   bloom-merge!
   bloom-serialize
   bloom-deserialize
   ;; Blocked Bloom filter (cache-optimized)
   make-blocked-bloom
   blocked-bloom-add!
   blocked-bloom-contains?
   blocked-bloom-serialize
   blocked-bloom-deserialize
   ;; Counting Bloom filter (supports deletion)
   make-counting-bloom
   counting-bloom-add!
   counting-bloom-remove!
   counting-bloom-contains?
   counting-bloom-count
   ;; Utilities
   optimal-bloom-size
   optimal-hash-count
   bloom-false-positive-rate
   ;; Inventory operations
   make-inventory-bloom
   inventory-diff)

  (import scheme
          (chicken base)
          (chicken blob)
          (chicken bitwise)
          (chicken format)
          srfi-1      ; list utilities
          srfi-4      ; u8vectors
          crypto-ffi) ; sha256-hash, blake2b-hash

  ;; ============================================================
  ;; Bloom Filter Theory
  ;; ============================================================
  ;;
  ;; False positive rate: p = (1 - e^(-kn/m))^k
  ;; Where:
  ;;   m = number of bits
  ;;   n = number of elements
  ;;   k = number of hash functions
  ;;
  ;; Optimal k = (m/n) * ln(2) ~ 0.693 * (m/n)
  ;; Optimal m = -n * ln(p) / (ln(2))^2
  ;;
  ;; For 1% false positive rate with 100K elements:
  ;;   m = 958,506 bits (~117 KB)
  ;;   k = 7 hash functions

  (define (optimal-bloom-size n p)
    "Calculate optimal bit array size for n elements with false positive rate p"
    (inexact->exact
     (ceiling (- (/ (* n (log p))
                    (* (log 2) (log 2)))))))

  (define (optimal-hash-count m n)
    "Calculate optimal number of hash functions"
    (max 1 (inexact->exact
            (round (* (/ m n) (log 2))))))

  (define (bloom-false-positive-rate m n k)
    "Calculate actual false positive rate"
    (expt (- 1 (exp (- (/ (* k n) m)))) k))

  ;; ============================================================
  ;; Standard Bloom Filter
  ;; ============================================================

  (define-record-type <bloom-filter>
    (make-bloom-internal bits size hash-count element-count)
    bloom-filter?
    (bits bloom-bits)
    (size bloom-size)
    (hash-count bloom-hash-count)
    (element-count bloom-element-count bloom-element-count-set!))

  (define (make-bloom #!key (capacity 10000) (error-rate 0.01))
    "Create a Bloom filter with given capacity and error rate"
    (let* ((m (optimal-bloom-size capacity error-rate))
           (k (optimal-hash-count m capacity))
           (byte-size (quotient (+ m 7) 8))
           (bits (make-u8vector byte-size 0)))
      (make-bloom-internal bits m k 0)))

  (define (bloom-hash-indices bloom data)
    "Generate k hash indices for data using double hashing"
    (let* ((h1-blob (sha256-hash data))
           (h2-blob (blake2b-hash data))
           (h1-vec (blob->u8vector h1-blob))
           (h2-vec (blob->u8vector h2-blob))
           (h1 (bytes->integer h1-vec 0 4))
           (h2 (bytes->integer h2-vec 0 4))
           (m (bloom-size bloom))
           (k (bloom-hash-count bloom)))
      (let loop ((i 0) (indices '()))
        (if (= i k)
            (reverse indices)
            (loop (+ i 1)
                  (cons (modulo (+ h1 (* i h2)) m) indices))))))

  (define (bytes->integer vec start len)
    "Convert bytes to integer (little-endian)"
    (let loop ((i 0) (acc 0))
      (if (= i len)
          acc
          (loop (+ i 1)
                (+ acc (arithmetic-shift
                        (u8vector-ref vec (+ start i))
                        (* i 8)))))))

  (define (bloom-set-bit! bits index)
    "Set bit at index in u8vector"
    (let* ((byte-idx (quotient index 8))
           (bit-idx (modulo index 8))
           (mask (arithmetic-shift 1 bit-idx)))
      (u8vector-set! bits byte-idx
                     (bitwise-ior (u8vector-ref bits byte-idx) mask))))

  (define (bloom-get-bit bits index)
    "Get bit at index in u8vector"
    (let* ((byte-idx (quotient index 8))
           (bit-idx (modulo index 8))
           (mask (arithmetic-shift 1 bit-idx)))
      (not (zero? (bitwise-and (u8vector-ref bits byte-idx) mask)))))

  (define (bloom-add! bloom data)
    "Add element to Bloom filter"
    (let ((indices (bloom-hash-indices bloom data))
          (bits (bloom-bits bloom)))
      (for-each (lambda (idx) (bloom-set-bit! bits idx)) indices)
      (bloom-element-count-set! bloom (+ 1 (bloom-element-count bloom)))))

  (define (bloom-contains? bloom data)
    "Check if element might be in Bloom filter"
    (let ((indices (bloom-hash-indices bloom data))
          (bits (bloom-bits bloom)))
      (every (lambda (idx) (bloom-get-bit bits idx)) indices)))

  (define (bloom-count bloom)
    "Return approximate element count"
    (bloom-element-count bloom))

  (define (bloom-merge! bloom1 bloom2)
    "Merge bloom2 into bloom1 (union)"
    (unless (= (bloom-size bloom1) (bloom-size bloom2))
      (error "Cannot merge Bloom filters of different sizes"))
    (let ((bits1 (bloom-bits bloom1))
          (bits2 (bloom-bits bloom2)))
      (do ((i 0 (+ i 1)))
          ((= i (u8vector-length bits1)))
        (u8vector-set! bits1 i
                       (bitwise-ior (u8vector-ref bits1 i)
                                    (u8vector-ref bits2 i))))))

  (define (bloom-serialize bloom)
    "Serialize Bloom filter for network transfer"
    `(bloom-filter
      (version 1)
      (size ,(bloom-size bloom))
      (hash-count ,(bloom-hash-count bloom))
      (element-count ,(bloom-element-count bloom))
      (bits ,(u8vector->blob (bloom-bits bloom)))))

  (define (bloom-deserialize sexp)
    "Deserialize Bloom filter"
    (let* ((size (cadr (assq 'size (cdr sexp))))
           (hash-count (cadr (assq 'hash-count (cdr sexp))))
           (element-count (cadr (assq 'element-count (cdr sexp))))
           (bits-blob (cadr (assq 'bits (cdr sexp)))))
      (make-bloom-internal (blob->u8vector bits-blob)
                          size hash-count element-count)))

  ;; ============================================================
  ;; Blocked Bloom Filter (Cache-Line Optimized)
  ;; ============================================================
  ;;
  ;; Standard Bloom filters have poor cache behavior - each hash
  ;; may access a different cache line. Blocked Bloom filters
  ;; constrain all k hash probes to a single cache-line block.
  ;;
  ;; Block size = 64 bytes (512 bits) = typical cache line

  (define *block-size* 64)  ; bytes per block (cache line)
  (define *block-bits* 512) ; bits per block

  (define-record-type <blocked-bloom>
    (make-blocked-bloom-internal blocks block-count hash-count element-count)
    blocked-bloom?
    (blocks blocked-bloom-blocks)
    (block-count blocked-bloom-block-count)
    (hash-count blocked-bloom-hash-count)
    (element-count blocked-bloom-element-count blocked-bloom-element-count-set!))

  (define (make-blocked-bloom #!key (capacity 10000) (error-rate 0.01))
    "Create a blocked Bloom filter (cache-optimized)"
    (let* ((m (optimal-bloom-size capacity error-rate))
           (k (min 8 (optimal-hash-count m capacity)))  ; max 8 for block
           (num-blocks (quotient (+ m *block-bits* -1) *block-bits*))
           (blocks (make-u8vector (* num-blocks *block-size*) 0)))
      (make-blocked-bloom-internal blocks num-blocks k 0)))

  (define (blocked-bloom-add! bloom data)
    "Add element to blocked Bloom filter"
    (let* ((hash-blob (sha256-hash data))
           (hash-vec (blob->u8vector hash-blob))
           (block-idx (modulo (bytes->integer hash-vec 0 4)
                              (blocked-bloom-block-count bloom)))
           (block-offset (* block-idx *block-size*))
           (blocks (blocked-bloom-blocks bloom))
           (k (blocked-bloom-hash-count bloom)))
      ;; All k probes within same block
      (do ((i 0 (+ i 1)))
          ((= i k))
        (let* ((bit-idx (modulo (bytes->integer hash-vec (+ 4 (* i 2)) 2)
                                *block-bits*))
               (byte-idx (+ block-offset (quotient bit-idx 8)))
               (bit-pos (modulo bit-idx 8))
               (mask (arithmetic-shift 1 bit-pos)))
          (u8vector-set! blocks byte-idx
                         (bitwise-ior (u8vector-ref blocks byte-idx) mask))))
      (blocked-bloom-element-count-set! bloom
                                        (+ 1 (blocked-bloom-element-count bloom)))))

  (define (blocked-bloom-contains? bloom data)
    "Check if element might be in blocked Bloom filter"
    (let* ((hash-blob (sha256-hash data))
           (hash-vec (blob->u8vector hash-blob))
           (block-idx (modulo (bytes->integer hash-vec 0 4)
                              (blocked-bloom-block-count bloom)))
           (block-offset (* block-idx *block-size*))
           (blocks (blocked-bloom-blocks bloom))
           (k (blocked-bloom-hash-count bloom)))
      (let loop ((i 0))
        (if (= i k)
            #t  ; all bits set
            (let* ((bit-idx (modulo (bytes->integer hash-vec (+ 4 (* i 2)) 2)
                                    *block-bits*))
                   (byte-idx (+ block-offset (quotient bit-idx 8)))
                   (bit-pos (modulo bit-idx 8))
                   (mask (arithmetic-shift 1 bit-pos)))
              (if (zero? (bitwise-and (u8vector-ref blocks byte-idx) mask))
                  #f  ; bit not set
                  (loop (+ i 1))))))))

  (define (blocked-bloom-serialize bloom)
    "Serialize blocked Bloom filter"
    `(blocked-bloom
      (version 1)
      (block-count ,(blocked-bloom-block-count bloom))
      (hash-count ,(blocked-bloom-hash-count bloom))
      (element-count ,(blocked-bloom-element-count bloom))
      (blocks ,(u8vector->blob (blocked-bloom-blocks bloom)))))

  (define (blocked-bloom-deserialize sexp)
    "Deserialize blocked Bloom filter"
    (let* ((block-count (cadr (assq 'block-count (cdr sexp))))
           (hash-count (cadr (assq 'hash-count (cdr sexp))))
           (element-count (cadr (assq 'element-count (cdr sexp))))
           (blocks-blob (cadr (assq 'blocks (cdr sexp)))))
      (make-blocked-bloom-internal (blob->u8vector blocks-blob)
                                   block-count hash-count element-count)))

  ;; ============================================================
  ;; Counting Bloom Filter (Supports Deletion)
  ;; ============================================================
  ;;
  ;; Uses 4-bit counters instead of single bits, allowing deletion.
  ;; Counter overflow saturates at 15 (doesn't wrap).

  (define-record-type <counting-bloom>
    (make-counting-bloom-internal counters size hash-count element-count)
    counting-bloom?
    (counters counting-bloom-counters)
    (size counting-bloom-size)
    (hash-count counting-bloom-hash-count)
    (element-count counting-bloom-element-count counting-bloom-element-count-set!))

  (define (make-counting-bloom #!key (capacity 10000) (error-rate 0.01))
    "Create a counting Bloom filter (supports deletion)"
    (let* ((m (optimal-bloom-size capacity error-rate))
           (k (optimal-hash-count m capacity))
           ;; 4 bits per counter, 2 counters per byte
           (byte-size (quotient (+ m 1) 2))
           (counters (make-u8vector byte-size 0)))
      (make-counting-bloom-internal counters m k 0)))

  (define (counting-bloom-get counters index)
    "Get 4-bit counter value at index"
    (let* ((byte-idx (quotient index 2))
           (nibble (modulo index 2))
           (byte-val (u8vector-ref counters byte-idx)))
      (if (= nibble 0)
          (bitwise-and byte-val #x0F)
          (arithmetic-shift byte-val -4))))

  (define (counting-bloom-set! counters index value)
    "Set 4-bit counter value at index"
    (let* ((byte-idx (quotient index 2))
           (nibble (modulo index 2))
           (byte-val (u8vector-ref counters byte-idx))
           (clamped (min 15 (max 0 value))))  ; clamp to 4 bits
      (u8vector-set! counters byte-idx
                     (if (= nibble 0)
                         (bitwise-ior (bitwise-and byte-val #xF0) clamped)
                         (bitwise-ior (bitwise-and byte-val #x0F)
                                      (arithmetic-shift clamped 4))))))

  (define (counting-bloom-hash-indices bloom data)
    "Generate k hash indices for counting Bloom"
    (let* ((h1-blob (sha256-hash data))
           (h2-blob (blake2b-hash data))
           (h1-vec (blob->u8vector h1-blob))
           (h2-vec (blob->u8vector h2-blob))
           (h1 (bytes->integer h1-vec 0 4))
           (h2 (bytes->integer h2-vec 0 4))
           (m (counting-bloom-size bloom))
           (k (counting-bloom-hash-count bloom)))
      (let loop ((i 0) (indices '()))
        (if (= i k)
            (reverse indices)
            (loop (+ i 1)
                  (cons (modulo (+ h1 (* i h2)) m) indices))))))

  (define (counting-bloom-add! bloom data)
    "Add element to counting Bloom filter"
    (let ((indices (counting-bloom-hash-indices bloom data))
          (counters (counting-bloom-counters bloom)))
      (for-each
       (lambda (idx)
         (let ((current (counting-bloom-get counters idx)))
           (when (< current 15)  ; don't overflow
             (counting-bloom-set! counters idx (+ current 1)))))
       indices)
      (counting-bloom-element-count-set! bloom
                                         (+ 1 (counting-bloom-element-count bloom)))))

  (define (counting-bloom-remove! bloom data)
    "Remove element from counting Bloom filter"
    (let ((indices (counting-bloom-hash-indices bloom data))
          (counters (counting-bloom-counters bloom)))
      ;; Only remove if all counters > 0
      (when (every (lambda (idx) (> (counting-bloom-get counters idx) 0)) indices)
        (for-each
         (lambda (idx)
           (let ((current (counting-bloom-get counters idx)))
             (when (> current 0)
               (counting-bloom-set! counters idx (- current 1)))))
         indices)
        (counting-bloom-element-count-set! bloom
                                           (max 0 (- (counting-bloom-element-count bloom) 1))))))

  (define (counting-bloom-contains? bloom data)
    "Check if element might be in counting Bloom filter"
    (let ((indices (counting-bloom-hash-indices bloom data))
          (counters (counting-bloom-counters bloom)))
      (every (lambda (idx) (> (counting-bloom-get counters idx) 0)) indices)))

  (define (counting-bloom-count bloom)
    "Return approximate element count"
    (counting-bloom-element-count bloom))

  ;; ============================================================
  ;; Inventory Operations for Federation
  ;; ============================================================

  (define (make-inventory-bloom hashes #!key (error-rate 0.01))
    "Create Bloom filter from list of object hashes"
    (let* ((n (length hashes))
           (bloom (make-blocked-bloom capacity: (max 1000 (* n 2))
                                      error-rate: error-rate)))
      (for-each (lambda (hash)
                  (blocked-bloom-add! bloom
                                      (if (string? hash)
                                          (string->blob hash)
                                          hash)))
                hashes)
      bloom))

  (define (inventory-diff local-bloom remote-bloom local-hashes)
    "Find objects we might be missing.
     Returns list of local hashes that remote probably has but we might not."
    ;; This is used for the first phase of federation convergence:
    ;; exchange Bloom filters, identify candidates for detailed comparison
    (filter (lambda (hash)
              (let ((hash-blob (if (string? hash)
                                   (string->blob hash)
                                   hash)))
                ;; Remote has it (probably) and we might not
                (and (blocked-bloom-contains? remote-bloom hash-blob)
                     (not (blocked-bloom-contains? local-bloom hash-blob)))))
            local-hashes))

) ;; end module

;;;
;;; Example: Federation inventory exchange
;;;
;;;   (import bloom)
;;;
;;;   ;; Node A creates inventory Bloom
;;;   (define a-hashes '("sha512:abc..." "sha512:def..." ...))
;;;   (define a-bloom (make-inventory-bloom a-hashes))
;;;
;;;   ;; Node B creates inventory Bloom
;;;   (define b-hashes '("sha512:def..." "sha512:ghi..." ...))
;;;   (define b-bloom (make-inventory-bloom b-hashes))
;;;
;;;   ;; Exchange and find candidates for sync
;;;   ;; A receives B's bloom, finds what B has that A might not
;;;   (inventory-diff a-bloom b-bloom a-hashes)
;;;   => ("sha512:ghi..." ...)  ; candidates to request from B
;;;
;;; Example: Standard Bloom filter
;;;
;;;   (define bf (make-bloom capacity: 1000 error-rate: 0.01))
;;;   (bloom-add! bf "hello")
;;;   (bloom-contains? bf "hello")  => #t
;;;   (bloom-contains? bf "world")  => #f (probably)
;;;
