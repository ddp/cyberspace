;;; merkle.scm - Quantum-Resistant Merkle Trees (Memo-047)
;;; Library of Cyberspace - Chez Port
;;;
;;; Implements tree-structured hashing for:
;;; - Incremental updates (change one chunk, rehash one branch)
;;; - Selective disclosure (prove chunk exists without revealing siblings)
;;; - Streaming verification (verify chunks as they arrive)
;;; - Quantum resistance (BLAKE2b provides 128-bit post-quantum security)
;;;
;;; See: Merkle, R. "A Digital Signature Based on a Conventional
;;;      Encryption Function" (1987)

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

  (import (except (rnrs) find)
          (only (chezscheme) void)
          (cyberspace chicken-compatibility blob)
          (cyberspace chicken-compatibility chicken)
          (only (cyberspace crypto-ffi)
                blake2b-hash sha512-hash))

  ;;; ============================================================
  ;;; Constants
  ;;; ============================================================

  ;; Default chunk size: 4 KB (filesystem-friendly)
  (define chunk-size-default 4096)

  ;; Default fanout: 16 children per node (balance between depth and width)
  (define fanout-default 16)

  ;; Domain separation prefixes (prevent leaf/node confusion)
  (define leaf-prefix (make-bytevector 1 0))
  (define node-prefix (make-bytevector 1 1))

  ;;; ============================================================
  ;;; Chunking
  ;;; ============================================================

  (define (chunk-content data . rest)
    "Split data into fixed-size chunks. Last chunk may be smaller."
    (let* ((chunk-size (if (null? rest) chunk-size-default (car rest)))
           (data-bv (if (string? data) (string->utf8 data) data))
           (len (bytevector-length data-bv)))
      (let loop ((offset 0) (chunks '()))
        (if (>= offset len)
            (reverse chunks)
            (let* ((end (min (+ offset chunk-size) len))
                   (chunk-len (- end offset))
                   (chunk (make-bytevector chunk-len)))
              ;; Copy chunk data
              (do ((i 0 (+ i 1)))
                  ((>= i chunk-len))
                (bytevector-u8-set! chunk i (bytevector-u8-ref data-bv (+ offset i))))
              (loop end (cons chunk chunks)))))))

  ;;; ============================================================
  ;;; Hash Functions with Domain Separation
  ;;; ============================================================

  (define (merkle-hash-leaf chunk)
    "Hash a leaf chunk with domain separation prefix 0x00.
     Prevents leaf from being interpreted as internal node."
    (let* ((chunk-bv (if (string? chunk) (string->utf8 chunk) chunk))
           (prefixed (make-bytevector (+ 1 (bytevector-length chunk-bv)))))
      ;; Prefix with 0x00 for leaf
      (bytevector-u8-set! prefixed 0 0)
      ;; Copy chunk data
      (do ((i 0 (+ i 1)))
          ((>= i (bytevector-length chunk-bv)))
        (bytevector-u8-set! prefixed (+ i 1) (bytevector-u8-ref chunk-bv i)))
      (blake2b-hash prefixed)))

  (define (merkle-hash-node children)
    "Hash internal node with domain separation prefix 0x01.
     Children is a list of hash bytevectors."
    (let* ((total-len (+ 1 (fold-left + 0 (map bytevector-length children))))
           (prefixed (make-bytevector total-len)))
      ;; Prefix with 0x01 for internal node
      (bytevector-u8-set! prefixed 0 1)
      ;; Concatenate all children
      (let loop ((children children) (offset 1))
        (if (null? children)
            (blake2b-hash prefixed)
            (let ((child (car children)))
              (do ((i 0 (+ i 1)))
                  ((>= i (bytevector-length child)))
                (bytevector-u8-set! prefixed (+ offset i) (bytevector-u8-ref child i)))
              (loop (cdr children) (+ offset (bytevector-length child))))))))

  ;;; ============================================================
  ;;; Tree Construction
  ;;; ============================================================

  (define (partition-into-groups lst n)
    "Partition list into groups of at most n elements."
    (if (null? lst)
        '()
        (let loop ((remaining lst) (groups '()))
          (if (null? remaining)
              (reverse groups)
              (let-values (((group rest) (split-at-n remaining (min n (length remaining)))))
                (loop rest (cons group groups)))))))

  (define (split-at-n lst n)
    "Split list at position n, return (values front back)"
    (let loop ((lst lst) (n n) (acc '()))
      (if (or (= n 0) (null? lst))
          (values (reverse acc) lst)
          (loop (cdr lst) (- n 1) (cons (car lst) acc)))))

  (define (build-tree-level nodes fanout)
    "Build one level of the tree by grouping nodes and hashing."
    (map merkle-hash-node (partition-into-groups nodes fanout)))

  (define (build-tree leaves fanout)
    "Build complete tree from leaves, return root hash."
    (if (<= (length leaves) 1)
        (if (null? leaves)
            (merkle-hash-leaf (make-bytevector 0))  ; Empty content
            (car leaves))
        (build-tree (build-tree-level leaves fanout) fanout)))

  (define (merkle-hash content . rest)
    "Compute Merkle root hash of content.
     Optional args: chunk-size fanout
     Returns the root hash bytevector."
    (let* ((chunk-size (if (null? rest) chunk-size-default (car rest)))
           (fanout (if (or (null? rest) (null? (cdr rest))) fanout-default (cadr rest)))
           (data (if (string? content) (string->utf8 content) content))
           (chunks (chunk-content data chunk-size))
           (leaves (map merkle-hash-leaf chunks)))
      (build-tree leaves fanout)))

  ;;; ============================================================
  ;;; Tree Structure (for proofs)
  ;;; ============================================================

  ;; Tagged vector: #(*merkle-tree-tag* root levels params)
  (define *merkle-tree-tag* (list 'merkle-tree))

  (define (make-merkle-tree-internal root levels params)
    (vector *merkle-tree-tag* root levels params))

  (define (merkle-tree? x)
    (and (vector? x) (>= (vector-length x) 4)
         (eq? (vector-ref x 0) *merkle-tree-tag*)))

  (define (merkle-tree-root tree) (vector-ref tree 1))
  (define (merkle-tree-levels tree) (vector-ref tree 2))
  (define (merkle-tree-params tree) (vector-ref tree 3))

  (define (merkle-tree-depth tree)
    (vector-length (merkle-tree-levels tree)))

  (define (merkle-tree-chunk-count tree)
    (length (vector-ref (merkle-tree-levels tree) 0)))

  (define (merkle-tree content . rest)
    "Build complete Merkle tree, preserving structure for proofs.
     Returns a merkle-tree record."
    (let* ((chunk-size (if (null? rest) chunk-size-default (car rest)))
           (fanout (if (or (null? rest) (null? (cdr rest))) fanout-default (cadr rest)))
           (data (if (string? content) (string->utf8 content) content))
           (chunks (chunk-content data chunk-size))
           (leaves (map merkle-hash-leaf chunks)))
      ;; Build all levels
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

  ;;; ============================================================
  ;;; Inclusion Proofs
  ;;; ============================================================

  ;; Tagged vector: #(*merkle-proof-tag* root index chunk-hash path)
  (define *merkle-proof-tag* (list 'merkle-proof))

  (define (make-merkle-proof root index chunk-hash path)
    (vector *merkle-proof-tag* root index chunk-hash path))

  (define (merkle-proof? x)
    (and (vector? x) (>= (vector-length x) 5)
         (eq? (vector-ref x 0) *merkle-proof-tag*)))

  (define (proof-root p) (vector-ref p 1))
  (define (proof-index p) (vector-ref p 2))
  (define (proof-chunk-hash p) (vector-ref p 3))
  (define (proof-path p) (vector-ref p 4))

  (define (merkle-proof tree chunk-index)
    "Generate inclusion proof for chunk at index.
     Returns a merkle-proof record."
    (let* ((levels (merkle-tree-levels tree))
           (fanout (cadr (merkle-tree-params tree)))
           (leaves (vector-ref levels 0)))
      (when (or (< chunk-index 0) (>= chunk-index (length leaves)))
        (error 'merkle-proof "Chunk index out of range" chunk-index))
      (let ((chunk-hash (list-ref leaves chunk-index)))
        ;; Build proof path
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
                     ;; Get siblings in this group
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
    "Verify that chunk-data is at proof-index in the tree with proof-root.
     Returns #t if valid, #f otherwise."
    (let ((computed-leaf (merkle-hash-leaf chunk-data)))
      ;; Check leaf hash matches
      (if (not (bytevector=? computed-leaf (proof-chunk-hash proof)))
          #f
          ;; Reconstruct path to root
          (let loop ((path (proof-path proof))
                     (current-hash computed-leaf))
            (if (null? path)
                (bytevector=? current-hash (proof-root proof))
                (let* ((level-info (car path))
                       (pos-in-group (car level-info))
                       (siblings (cdr level-info))
                       ;; Reconstruct the group's children in order
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

  ;; bytevector=? is provided by (rnrs bytevectors)

  ;;; ============================================================
  ;;; Dual-Hash Support (Transition Period)
  ;;; ============================================================

  ;; Tagged vector: #(*dual-hash-tag* legacy merkle-root params)
  (define *dual-hash-tag* (list 'dual-hash))

  (define (make-dual-hash legacy merkle-root params)
    (vector *dual-hash-tag* legacy merkle-root params))

  (define (dual-hash? x)
    (and (vector? x) (>= (vector-length x) 4)
         (eq? (vector-ref x 0) *dual-hash-tag*)))

  (define (dual-hash-legacy dh) (vector-ref dh 1))
  (define (dual-hash-merkle dh) (vector-ref dh 2))
  (define (dual-hash-params dh) (vector-ref dh 3))

  (define (dual-hash content . rest)
    "Compute both legacy SHA-512 and quantum-resistant Merkle hashes.
     For transition period compatibility."
    (let* ((chunk-size (if (null? rest) chunk-size-default (car rest)))
           (fanout (if (or (null? rest) (null? (cdr rest))) fanout-default (cadr rest)))
           (data (if (string? content) (string->utf8 content) content))
           (legacy (sha512-hash data))
           (merkle (merkle-hash data chunk-size fanout)))
      (make-dual-hash legacy merkle (list chunk-size fanout 'blake2b))))

) ;; end library
