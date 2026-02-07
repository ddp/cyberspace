;;; SPKI Scheme - Blocked Bloom Filters for Federation Convergence (Chez Port)
;;; Library of Cyberspace
;;;
;;; Space-efficient probabilistic set membership for:
;;; - Fast detection of missing objects during sync
;;; - Inventory exchange between federation peers
;;; - Content-addressed storage existence checking
;;;
;;; Implements standard, blocked (cache-line aligned), and counting
;;; Bloom filters.
;;;
;;; Ported from bloom.scm.
;;; Copyright (c) 2026 Yoyodyne. See LICENSE.

(library (cyberspace bloom)
  (export
    ;; Standard Bloom filter
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

  (import (rnrs)
          (only (chezscheme) printf format void iota)
          (cyberspace crypto-ffi))

  ;; ============================================================
  ;; Bloom Filter Theory
  ;;
  ;; False positive rate: p = (1 - e^(-kn/m))^k
  ;; Optimal k = (m/n) * ln(2)
  ;; Optimal m = -n * ln(p) / (ln(2))^2
  ;; ============================================================

  (define (optimal-bloom-size n p)
    "Calculate optimal bit array size for n elements with false positive rate p."
    (exact
     (ceiling (- (/ (* n (log p))
                    (* (log 2) (log 2)))))))

  (define (optimal-hash-count m n)
    "Calculate optimal number of hash functions."
    (max 1 (exact
            (round (* (/ m n) (log 2))))))

  (define (bloom-false-positive-rate m n k)
    "Calculate actual false positive rate."
    (expt (- 1 (exp (- (/ (* k n) m)))) k))

  ;; ============================================================
  ;; Helpers
  ;; ============================================================

  (define (bytes->integer bv start len)
    "Convert bytes to integer (little-endian)."
    (let loop ((i 0) (acc 0))
      (if (= i len)
          acc
          (loop (+ i 1)
                (+ acc (bitwise-arithmetic-shift-left
                        (bytevector-u8-ref bv (+ start i))
                        (* i 8)))))))

  (define (bloom-set-bit! bits index)
    (let* ((byte-idx (div index 8))
           (bit-idx (mod index 8))
           (mask (bitwise-arithmetic-shift-left 1 bit-idx)))
      (bytevector-u8-set! bits byte-idx
                           (bitwise-ior (bytevector-u8-ref bits byte-idx) mask))))

  (define (bloom-get-bit bits index)
    (let* ((byte-idx (div index 8))
           (bit-idx (mod index 8))
           (mask (bitwise-arithmetic-shift-left 1 bit-idx)))
      (not (zero? (bitwise-and (bytevector-u8-ref bits byte-idx) mask)))))

  (define (ensure-bytevector data)
    (if (string? data) (string->utf8 data) data))

  ;; ============================================================
  ;; Standard Bloom Filter
  ;; ============================================================

  (define *bloom-tag* (list 'bloom))

  ;; #(tag bits size hash-count element-count)
  (define (%make-bloom bits size hash-count element-count)
    (vector *bloom-tag* bits size hash-count element-count))

  (define (bloom? x)
    (and (vector? x) (= (vector-length x) 5)
         (eq? (vector-ref x 0) *bloom-tag*)))

  (define (bloom-bits b) (vector-ref b 1))
  (define (bloom-size b) (vector-ref b 2))
  (define (bloom-hash-count b) (vector-ref b 3))
  (define (bloom-element-count b) (vector-ref b 4))
  (define (bloom-element-count-set! b v) (vector-set! b 4 v))

  (define (make-bloom . opts)
    "Create a Bloom filter.
     (make-bloom capacity: 10000 error-rate: 0.01)"
    (let ((capacity (let loop ((r opts))
                      (cond ((null? r) 10000)
                            ((null? (cdr r)) 10000)
                            ((eq? (car r) 'capacity:) (cadr r))
                            (else (loop (cddr r))))))
          (error-rate (let loop ((r opts))
                        (cond ((null? r) 0.01)
                              ((null? (cdr r)) 0.01)
                              ((eq? (car r) 'error-rate:) (cadr r))
                              (else (loop (cddr r)))))))
      (let* ((m (optimal-bloom-size capacity error-rate))
             (k (optimal-hash-count m capacity))
             (byte-size (div (+ m 7) 8))
             (bits (make-bytevector byte-size 0)))
        (%make-bloom bits m k 0))))

  (define (bloom-hash-indices bloom data)
    "Generate k hash indices using double hashing."
    (let* ((d (ensure-bytevector data))
           (h1 (sha256-hash d))
           (h2 (blake2b-hash d))
           (h1-int (bytes->integer h1 0 4))
           (h2-int (bytes->integer h2 0 4))
           (m (bloom-size bloom))
           (k (bloom-hash-count bloom)))
      (let loop ((i 0) (indices '()))
        (if (= i k)
            (reverse indices)
            (loop (+ i 1)
                  (cons (mod (+ h1-int (* i h2-int)) m) indices))))))

  (define (bloom-add! bloom data)
    "Add element to Bloom filter."
    (let ((indices (bloom-hash-indices bloom data))
          (bits (bloom-bits bloom)))
      (for-each (lambda (idx) (bloom-set-bit! bits idx)) indices)
      (bloom-element-count-set! bloom (+ 1 (bloom-element-count bloom)))))

  (define (bloom-contains? bloom data)
    "Check if element might be in Bloom filter."
    (let ((indices (bloom-hash-indices bloom data))
          (bits (bloom-bits bloom)))
      (for-all (lambda (idx) (bloom-get-bit bits idx)) indices)))

  (define (bloom-count bloom)
    (bloom-element-count bloom))

  (define (bloom-merge! bloom1 bloom2)
    "Merge bloom2 into bloom1 (union)."
    (unless (= (bloom-size bloom1) (bloom-size bloom2))
      (error 'bloom-merge! "Cannot merge Bloom filters of different sizes"))
    (let ((bits1 (bloom-bits bloom1))
          (bits2 (bloom-bits bloom2)))
      (do ((i 0 (+ i 1)))
          ((= i (bytevector-length bits1)))
        (bytevector-u8-set! bits1 i
                             (bitwise-ior (bytevector-u8-ref bits1 i)
                                          (bytevector-u8-ref bits2 i))))))

  (define (bloom-serialize bloom)
    `(bloom-filter
      (version 1)
      (size ,(bloom-size bloom))
      (hash-count ,(bloom-hash-count bloom))
      (element-count ,(bloom-element-count bloom))
      (bits ,(bloom-bits bloom))))

  (define (bloom-deserialize sexp)
    (let* ((size (cadr (assq 'size (cdr sexp))))
           (hash-count (cadr (assq 'hash-count (cdr sexp))))
           (element-count (cadr (assq 'element-count (cdr sexp))))
           (bits (cadr (assq 'bits (cdr sexp)))))
      (%make-bloom bits size hash-count element-count)))

  ;; ============================================================
  ;; Blocked Bloom Filter (Cache-Line Optimized)
  ;;
  ;; All k hash probes constrained to single cache-line block.
  ;; Block size = 64 bytes (512 bits)
  ;; ============================================================

  (define *block-size* 64)
  (define *block-bits* 512)
  (define *blocked-bloom-tag* (list 'blocked-bloom))

  ;; #(tag blocks block-count hash-count element-count)
  (define (%make-blocked-bloom blocks block-count hash-count element-count)
    (vector *blocked-bloom-tag* blocks block-count hash-count element-count))

  (define (blocked-bloom? x)
    (and (vector? x) (= (vector-length x) 5)
         (eq? (vector-ref x 0) *blocked-bloom-tag*)))

  (define (blocked-bloom-blocks b) (vector-ref b 1))
  (define (blocked-bloom-block-count b) (vector-ref b 2))
  (define (blocked-bloom-hash-count b) (vector-ref b 3))
  (define (blocked-bloom-element-count b) (vector-ref b 4))
  (define (blocked-bloom-element-count-set! b v) (vector-set! b 4 v))

  (define (make-blocked-bloom . opts)
    "Create a blocked Bloom filter (cache-optimized).
     (make-blocked-bloom capacity: 10000 error-rate: 0.01)"
    (let ((capacity (let loop ((r opts))
                      (cond ((null? r) 10000)
                            ((null? (cdr r)) 10000)
                            ((eq? (car r) 'capacity:) (cadr r))
                            (else (loop (cddr r))))))
          (error-rate (let loop ((r opts))
                        (cond ((null? r) 0.01)
                              ((null? (cdr r)) 0.01)
                              ((eq? (car r) 'error-rate:) (cadr r))
                              (else (loop (cddr r)))))))
      (let* ((m (optimal-bloom-size capacity error-rate))
             (k (min 8 (optimal-hash-count m capacity)))
             (num-blocks (div (+ m *block-bits* -1) *block-bits*))
             (blocks (make-bytevector (* num-blocks *block-size*) 0)))
        (%make-blocked-bloom blocks num-blocks k 0))))

  (define (blocked-bloom-add! bloom data)
    "Add element to blocked Bloom filter."
    (let* ((d (ensure-bytevector data))
           (hash-bv (sha256-hash d))
           (block-idx (mod (bytes->integer hash-bv 0 4)
                           (blocked-bloom-block-count bloom)))
           (block-offset (* block-idx *block-size*))
           (blocks (blocked-bloom-blocks bloom))
           (k (blocked-bloom-hash-count bloom)))
      (do ((i 0 (+ i 1)))
          ((= i k))
        (let* ((bit-idx (mod (bytes->integer hash-bv (+ 4 (* i 2)) 2)
                              *block-bits*))
               (byte-idx (+ block-offset (div bit-idx 8)))
               (bit-pos (mod bit-idx 8))
               (mask (bitwise-arithmetic-shift-left 1 bit-pos)))
          (bytevector-u8-set! blocks byte-idx
                               (bitwise-ior (bytevector-u8-ref blocks byte-idx) mask))))
      (blocked-bloom-element-count-set! bloom
                                         (+ 1 (blocked-bloom-element-count bloom)))))

  (define (blocked-bloom-contains? bloom data)
    "Check if element might be in blocked Bloom filter."
    (let* ((d (ensure-bytevector data))
           (hash-bv (sha256-hash d))
           (block-idx (mod (bytes->integer hash-bv 0 4)
                           (blocked-bloom-block-count bloom)))
           (block-offset (* block-idx *block-size*))
           (blocks (blocked-bloom-blocks bloom))
           (k (blocked-bloom-hash-count bloom)))
      (let loop ((i 0))
        (if (= i k)
            #t
            (let* ((bit-idx (mod (bytes->integer hash-bv (+ 4 (* i 2)) 2)
                                  *block-bits*))
                   (byte-idx (+ block-offset (div bit-idx 8)))
                   (bit-pos (mod bit-idx 8))
                   (mask (bitwise-arithmetic-shift-left 1 bit-pos)))
              (if (zero? (bitwise-and (bytevector-u8-ref blocks byte-idx) mask))
                  #f
                  (loop (+ i 1))))))))

  (define (blocked-bloom-serialize bloom)
    `(blocked-bloom
      (version 1)
      (block-count ,(blocked-bloom-block-count bloom))
      (hash-count ,(blocked-bloom-hash-count bloom))
      (element-count ,(blocked-bloom-element-count bloom))
      (blocks ,(blocked-bloom-blocks bloom))))

  (define (blocked-bloom-deserialize sexp)
    (let* ((block-count (cadr (assq 'block-count (cdr sexp))))
           (hash-count (cadr (assq 'hash-count (cdr sexp))))
           (element-count (cadr (assq 'element-count (cdr sexp))))
           (blocks (cadr (assq 'blocks (cdr sexp)))))
      (%make-blocked-bloom blocks block-count hash-count element-count)))

  ;; ============================================================
  ;; Counting Bloom Filter (Supports Deletion)
  ;;
  ;; 4-bit counters, saturating at 15.
  ;; ============================================================

  (define *counting-bloom-tag* (list 'counting-bloom))

  ;; #(tag counters size hash-count element-count)
  (define (%make-counting-bloom counters size hash-count element-count)
    (vector *counting-bloom-tag* counters size hash-count element-count))

  (define (counting-bloom? x)
    (and (vector? x) (= (vector-length x) 5)
         (eq? (vector-ref x 0) *counting-bloom-tag*)))

  (define (counting-bloom-counters b) (vector-ref b 1))
  (define (counting-bloom-size b) (vector-ref b 2))
  (define (counting-bloom-hash-count b) (vector-ref b 3))
  (define (counting-bloom-element-count b) (vector-ref b 4))
  (define (counting-bloom-element-count-set! b v) (vector-set! b 4 v))

  (define (make-counting-bloom . opts)
    "Create a counting Bloom filter (supports deletion).
     (make-counting-bloom capacity: 10000 error-rate: 0.01)"
    (let ((capacity (let loop ((r opts))
                      (cond ((null? r) 10000)
                            ((null? (cdr r)) 10000)
                            ((eq? (car r) 'capacity:) (cadr r))
                            (else (loop (cddr r))))))
          (error-rate (let loop ((r opts))
                        (cond ((null? r) 0.01)
                              ((null? (cdr r)) 0.01)
                              ((eq? (car r) 'error-rate:) (cadr r))
                              (else (loop (cddr r)))))))
      (let* ((m (optimal-bloom-size capacity error-rate))
             (k (optimal-hash-count m capacity))
             (byte-size (div (+ m 1) 2))
             (counters (make-bytevector byte-size 0)))
        (%make-counting-bloom counters m k 0))))

  (define (counting-bloom-get counters index)
    (let* ((byte-idx (div index 2))
           (nibble (mod index 2))
           (byte-val (bytevector-u8-ref counters byte-idx)))
      (if (= nibble 0)
          (bitwise-and byte-val #x0F)
          (bitwise-arithmetic-shift-right byte-val 4))))

  (define (counting-bloom-set! counters index value)
    (let* ((byte-idx (div index 2))
           (nibble (mod index 2))
           (byte-val (bytevector-u8-ref counters byte-idx))
           (clamped (min 15 (max 0 value))))
      (bytevector-u8-set! counters byte-idx
                           (if (= nibble 0)
                               (bitwise-ior (bitwise-and byte-val #xF0) clamped)
                               (bitwise-ior (bitwise-and byte-val #x0F)
                                            (bitwise-arithmetic-shift-left clamped 4))))))

  (define (counting-bloom-hash-indices bloom data)
    (let* ((d (ensure-bytevector data))
           (h1 (sha256-hash d))
           (h2 (blake2b-hash d))
           (h1-int (bytes->integer h1 0 4))
           (h2-int (bytes->integer h2 0 4))
           (m (counting-bloom-size bloom))
           (k (counting-bloom-hash-count bloom)))
      (let loop ((i 0) (indices '()))
        (if (= i k)
            (reverse indices)
            (loop (+ i 1)
                  (cons (mod (+ h1-int (* i h2-int)) m) indices))))))

  (define (counting-bloom-add! bloom data)
    (let ((indices (counting-bloom-hash-indices bloom data))
          (counters (counting-bloom-counters bloom)))
      (for-each
       (lambda (idx)
         (let ((current (counting-bloom-get counters idx)))
           (when (< current 15)
             (counting-bloom-set! counters idx (+ current 1)))))
       indices)
      (counting-bloom-element-count-set! bloom
                                          (+ 1 (counting-bloom-element-count bloom)))))

  (define (counting-bloom-remove! bloom data)
    (let ((indices (counting-bloom-hash-indices bloom data))
          (counters (counting-bloom-counters bloom)))
      (when (for-all (lambda (idx) (> (counting-bloom-get counters idx) 0)) indices)
        (for-each
         (lambda (idx)
           (let ((current (counting-bloom-get counters idx)))
             (when (> current 0)
               (counting-bloom-set! counters idx (- current 1)))))
         indices)
        (counting-bloom-element-count-set! bloom
                                            (max 0 (- (counting-bloom-element-count bloom) 1))))))

  (define (counting-bloom-contains? bloom data)
    (let ((indices (counting-bloom-hash-indices bloom data))
          (counters (counting-bloom-counters bloom)))
      (for-all (lambda (idx) (> (counting-bloom-get counters idx) 0)) indices)))

  (define (counting-bloom-count bloom)
    (counting-bloom-element-count bloom))

  ;; ============================================================
  ;; Inventory Operations for Federation
  ;; ============================================================

  (define (make-inventory-bloom hashes . opts)
    "Create Bloom filter from list of object hashes."
    (let ((error-rate (let loop ((r opts))
                        (cond ((null? r) 0.01)
                              ((null? (cdr r)) 0.01)
                              ((eq? (car r) 'error-rate:) (cadr r))
                              (else (loop (cddr r)))))))
      (let* ((n (length hashes))
             (bloom (make-blocked-bloom 'capacity: (max 1000 (* n 2))
                                        'error-rate: error-rate)))
        (for-each (lambda (hash)
                    (blocked-bloom-add! bloom (ensure-bytevector hash)))
                  hashes)
        bloom)))

  (define (inventory-diff local-bloom remote-bloom local-hashes)
    "Find objects we might be missing."
    (filter (lambda (hash)
              (let ((hash-bv (ensure-bytevector hash)))
                (and (blocked-bloom-contains? remote-bloom hash-bv)
                     (not (blocked-bloom-contains? local-bloom hash-bv)))))
            local-hashes))

) ;; end library
