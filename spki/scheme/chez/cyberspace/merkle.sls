;;; merkle.scm - Quantum-Resistant Merkle Trees (Memo-047)
;;; Chez Scheme Port
;;;
;;; Tree-structured hashing for:
;;; - Incremental updates (change one chunk, rehash one branch)
;;; - Selective disclosure (prove chunk exists without revealing siblings)
;;; - Streaming verification (verify chunks as they arrive)
;;; - Quantum resistance (BLAKE2b provides 128-bit post-quantum security)
;;;
;;; See: Merkle, R. "A Digital Signature Based on a Conventional
;;;      Encryption Function" (1987)
;;;
;;; Ported from Chicken's merkle.scm.
;;; Changes: module -> library, blob/u8vector -> bytevector compat,
;;;          #u8() -> #vu8(), SRFI-9 records -> R6RS, SRFI-1 -> local.

(library (cyberspace merkle)
  (export
    ;; Tree construction
    merkle-hash
    merkle-tree
    merkle-root

    ;; Proofs
    merkle-proof
    merkle-verify

    ;; Chunk operations
    chunk-content
    chunk-size-default
    fanout-default

    ;; Hash algorithms
    merkle-hash-leaf
    merkle-hash-node

    ;; Tree inspection
    merkle-tree?
    merkle-tree-root
    merkle-tree-depth
    merkle-tree-chunk-count
    merkle-tree-params

    ;; Dual-hash support (transition period)
    dual-hash
    dual-hash?
    dual-hash-legacy
    dual-hash-merkle)

  (import (rnrs)
          (only (chezscheme) quotient remainder)
          (cyberspace chicken-compatibility blob)
          (cyberspace chicken-compatibility chicken)
          (cyberspace crypto-ffi))

  ;; ============================================================
  ;; SRFI-1 helpers
  ;; ============================================================

  (define (split-at lst n)
    (let loop ((i 0) (rest lst) (head '()))
      (if (or (= i n) (null? rest))
          (values (reverse head) rest)
          (loop (+ i 1) (cdr rest) (cons (car rest) head)))))

  ;; ============================================================
  ;; Constants
  ;; ============================================================

  (define chunk-size-default 4096)
  (define fanout-default 16)

  ;; Domain separation prefixes (prevent leaf/node confusion)
  (define leaf-prefix #vu8(0))
  (define node-prefix #vu8(1))

  ;; ============================================================
  ;; Chunking
  ;; ============================================================

  (define (chunk-content data . rest)
    "Split data into fixed-size chunks. Last chunk may be smaller."
    (let* ((chunk-size (get-opt rest 0 chunk-size-default))
           (data-bv (if (bytevector? data) data (string->utf8 data)))
           (len (bytevector-length data-bv)))
      (let loop ((offset 0) (chunks '()))
        (if (>= offset len)
            (reverse chunks)
            (let* ((end (min (+ offset chunk-size) len))
                   (chunk-len (- end offset))
                   (chunk (make-bytevector chunk-len)))
              (bytevector-copy! data-bv offset chunk 0 chunk-len)
              (loop end (cons chunk chunks)))))))

  ;; ============================================================
  ;; Hash Functions with Domain Separation
  ;; ============================================================

  (define (merkle-hash-leaf chunk)
    "Hash a leaf chunk with domain separation prefix 0x00."
    (let* ((chunk-bv (if (bytevector? chunk) chunk (string->utf8 chunk)))
           (prefixed (make-bytevector (+ 1 (bytevector-length chunk-bv)))))
      (bytevector-u8-set! prefixed 0 0)
      (bytevector-copy! chunk-bv 0 prefixed 1 (bytevector-length chunk-bv))
      (blake2b-hash prefixed)))

  (define (merkle-hash-node children)
    "Hash internal node with domain separation prefix 0x01.
     Children is a list of hash bytevectors."
    (let* ((child-bvs (map (lambda (h)
                             (if (bytevector? h) h (string->utf8 h)))
                           children))
           (total-len (+ 1 (fold-left + 0 (map bytevector-length child-bvs))))
           (prefixed (make-bytevector total-len)))
      (bytevector-u8-set! prefixed 0 1)
      (let loop ((children child-bvs) (offset 1))
        (if (null? children)
            (blake2b-hash prefixed)
            (let ((child (car children))
                  (clen (bytevector-length (car children))))
              (bytevector-copy! child 0 prefixed offset clen)
              (loop (cdr children) (+ offset clen)))))))

  ;; ============================================================
  ;; Tree Construction
  ;; ============================================================

  (define (partition-into-groups lst n)
    "Partition list into groups of at most n elements."
    (if (null? lst)
        '()
        (let loop ((remaining lst) (groups '()))
          (if (null? remaining)
              (reverse groups)
              (let-values (((group rest) (split-at remaining (min n (length remaining)))))
                (loop rest (cons group groups)))))))

  (define (build-tree-level nodes fanout)
    "Build one level of the tree by grouping nodes and hashing."
    (map merkle-hash-node (partition-into-groups nodes fanout)))

  (define (build-tree leaves fanout)
    "Build complete tree from leaves, return root hash."
    (if (<= (length leaves) 1)
        (if (null? leaves)
            (merkle-hash-leaf (make-bytevector 0))
            (car leaves))
        (build-tree (build-tree-level leaves fanout) fanout)))

  (define (merkle-hash content . opts)
    "Compute Merkle root hash of content. Returns root hash bytevector."
    (let* ((chunk-size (get-key opts 'chunk-size: chunk-size-default))
           (fanout (get-key opts 'fanout: fanout-default))
           (data (if (string? content)
                     (string->utf8 content)
                     content))
           (chunks (chunk-content data chunk-size))
           (leaves (map merkle-hash-leaf chunks)))
      (build-tree leaves fanout)))

  ;; ============================================================
  ;; Tree Structure (for proofs)
  ;; ============================================================

  (define-record-type (merkle-tree-record make-merkle-tree-internal merkle-tree?)
    (fields (immutable root merkle-tree-root)
            (immutable levels merkle-tree-levels)
            (immutable params merkle-tree-params)))

  (define (merkle-tree-depth tree)
    (vector-length (merkle-tree-levels tree)))

  (define (merkle-tree-chunk-count tree)
    (length (vector-ref (merkle-tree-levels tree) 0)))

  (define (merkle-tree content . opts)
    "Build complete Merkle tree, preserving structure for proofs."
    (let* ((chunk-size (get-key opts 'chunk-size: chunk-size-default))
           (fanout (get-key opts 'fanout: fanout-default))
           (data (if (string? content)
                     (string->utf8 content)
                     content))
           (chunks (chunk-content data chunk-size))
           (leaves (map merkle-hash-leaf chunks)))
      (let loop ((current-level leaves) (levels (list leaves)))
        (if (<= (length current-level) 1)
            (let ((all-levels (reverse levels)))
              (make-merkle-tree-internal
               (if (null? current-level)
                   (merkle-hash-leaf (make-bytevector 0))
                   (car current-level))
               (list->vector all-levels)
               (list chunk-size fanout)))
            (let ((next-level (build-tree-level current-level fanout)))
              (loop next-level (cons next-level levels)))))))

  (define (merkle-root tree)
    "Get root hash from a merkle-tree."
    (merkle-tree-root tree))

  ;; ============================================================
  ;; Inclusion Proofs
  ;; ============================================================

  (define-record-type (merkle-proof-record make-merkle-proof merkle-proof?)
    (fields (immutable root proof-root)
            (immutable index proof-index)
            (immutable chunk-hash proof-chunk-hash)
            (immutable path proof-path)))

  (define (merkle-proof tree chunk-index)
    "Generate inclusion proof for chunk at index."
    (let* ((levels (merkle-tree-levels tree))
           (fanout (cadr (merkle-tree-params tree)))
           (leaves (vector-ref levels 0)))
      (when (or (< chunk-index 0) (>= chunk-index (length leaves)))
        (error 'merkle-proof "Chunk index out of range" chunk-index))
      (let ((chunk-hash (list-ref leaves chunk-index)))
        (let loop ((level 0)
                   (idx chunk-index)
                   (path '()))
          (if (>= level (- (vector-length levels) 1))
              (make-merkle-proof
               (merkle-tree-root tree)
               chunk-index
               chunk-hash
               (reverse path))
              (let* ((current (vector-ref levels level))
                     (group-idx (quotient idx fanout))
                     (pos-in-group (remainder idx fanout))
                     (group-start (* group-idx fanout))
                     (group-end (min (+ group-start fanout) (length current)))
                     (siblings
                      (let sib-loop ((i group-start) (sibs '()))
                        (if (>= i group-end)
                            (reverse sibs)
                            (if (= i idx)
                                (sib-loop (+ i 1) sibs)
                                (sib-loop (+ i 1)
                                          (cons (cons (list-ref current i)
                                                      (if (< i idx) 'left 'right))
                                                sibs)))))))
                (loop (+ level 1)
                      group-idx
                      (cons (cons pos-in-group siblings) path))))))))

  (define (merkle-verify proof chunk-data)
    "Verify that chunk-data is at proof-index in the tree with proof-root."
    (let ((computed-leaf (merkle-hash-leaf chunk-data)))
      (if (not (bytevector=? computed-leaf (proof-chunk-hash proof)))
          #f
          (let loop ((path (proof-path proof))
                     (current-hash computed-leaf))
            (if (null? path)
                (bytevector=? current-hash (proof-root proof))
                (let* ((level-info (car path))
                       (pos-in-group (car level-info))
                       (siblings (cdr level-info))
                       (children
                        (let build ((left-sibs (filter (lambda (s) (eq? (cdr s) 'left)) siblings))
                                    (right-sibs (filter (lambda (s) (eq? (cdr s) 'right)) siblings))
                                    (pos 0)
                                    (result '()))
                          (cond
                           ((and (null? left-sibs) (null? right-sibs) (> pos pos-in-group))
                            (reverse result))
                           ((= pos pos-in-group)
                            (build left-sibs right-sibs (+ pos 1) (cons current-hash result)))
                           ((and (not (null? left-sibs)) (< pos pos-in-group))
                            (build (cdr left-sibs) right-sibs (+ pos 1)
                                   (cons (caar left-sibs) result)))
                           ((not (null? right-sibs))
                            (build left-sibs (cdr right-sibs) (+ pos 1)
                                   (cons (caar right-sibs) result)))
                           (else (reverse result))))))
                  (loop (cdr path) (merkle-hash-node children))))))))

  ;; ============================================================
  ;; Dual-Hash Support (Transition Period)
  ;; ============================================================

  (define-record-type (dual-hash-record make-dual-hash dual-hash?)
    (fields (immutable legacy dual-hash-legacy)
            (immutable merkle dual-hash-merkle)
            (immutable params dual-hash-params)))

  (define (dual-hash content . opts)
    "Compute both legacy SHA-512 and quantum-resistant Merkle hashes."
    (let* ((chunk-size (get-key opts 'chunk-size: chunk-size-default))
           (fanout (get-key opts 'fanout: fanout-default))
           (data (if (string? content)
                     (string->utf8 content)
                     content))
           (legacy (sha512-hash data))
           (merk (merkle-hash data 'chunk-size: chunk-size 'fanout: fanout)))
      (make-dual-hash legacy merk (list chunk-size fanout 'blake2b))))

) ;; end library
