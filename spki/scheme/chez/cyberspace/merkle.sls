;;; merkle.sls - Quantum-Resistant Merkle Trees (Memo-047)
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
;;;
;;; Ported from Chicken's merkle.scm.
;;; Changes: module -> library, (srfi 1) split-at/fold -> manual,
;;;          #!key/#!optional -> get-key/get-opt, blob -> bytevector compat,
;;;          (chicken bitwise) -> (rnrs arithmetic bitwise).

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
          (only (chezscheme) format)
          (cyberspace crypto-ffi)
          (cyberspace chicken-compatibility blob)
          (cyberspace chicken-compatibility chicken))

  ;;; ============================================================
  ;;; Constants
  ;;; ============================================================

  ;; Default chunk size: 4 KB (filesystem-friendly)
  (define chunk-size-default 4096)

  ;; Default fanout: 16 children per node (balance between depth and width)
  (define fanout-default 16)

  ;;; ============================================================
  ;;; SRFI-1 helpers
  ;;; ============================================================

  (define (fold proc init lst)
    (if (null? lst)
        init
        (fold proc (proc (car lst) init) (cdr lst))))

  (define (split-at lst n)
    (let loop ((i 0) (head '()) (tail lst))
      (if (or (= i n) (null? tail))
          (values (reverse head) tail)
          (loop (+ i 1) (cons (car tail) head) (cdr tail)))))

  ;;; ============================================================
  ;;; Chunking
  ;;; ============================================================

  (define (chunk-content data . rest)
    "Split data into fixed-size chunks. Last chunk may be smaller."
    (let* ((chunk-size (get-opt rest 0 chunk-size-default))
           (data-vec (if (bytevector? data)
                         (blob->u8vector data)
                         data))
           (len (u8vector-length data-vec)))
      (let loop ((offset 0) (chunks '()))
        (if (>= offset len)
            (reverse chunks)
            (let* ((end (min (+ offset chunk-size) len))
                   (chunk (make-u8vector (- end offset))))
              (do ((i 0 (+ i 1)))
                  ((>= i (- end offset)))
                (u8vector-set! chunk i (u8vector-ref data-vec (+ offset i))))
              (loop end (cons (u8vector->blob chunk) chunks)))))))

  ;;; ============================================================
  ;;; Hash Functions with Domain Separation
  ;;; ============================================================

  (define (merkle-hash-leaf chunk)
    "Hash a leaf chunk with domain separation prefix 0x00.
     Prevents leaf from being interpreted as internal node."
    (let* ((chunk-vec (if (bytevector? chunk)
                          (blob->u8vector chunk)
                          chunk))
           (prefixed (make-u8vector (+ 1 (u8vector-length chunk-vec)))))
      ;; Prefix with 0x00 for leaf
      (u8vector-set! prefixed 0 0)
      ;; Copy chunk data
      (do ((i 0 (+ i 1)))
          ((>= i (u8vector-length chunk-vec)))
        (u8vector-set! prefixed (+ i 1) (u8vector-ref chunk-vec i)))
      (blake2b-hash (u8vector->blob prefixed))))

  (define (merkle-hash-node children)
    "Hash internal node with domain separation prefix 0x01.
     Children is a list of hash blobs."
    (let* ((child-vecs (map (lambda (h)
                              (if (bytevector? h)
                                  (blob->u8vector h)
                                  h))
                            children))
           (total-len (+ 1 (fold (lambda (v acc) (+ (u8vector-length v) acc))
                                 0 child-vecs)))
           (prefixed (make-u8vector total-len)))
      ;; Prefix with 0x01 for internal node
      (u8vector-set! prefixed 0 1)
      ;; Concatenate all children
      (let loop ((children child-vecs) (offset 1))
        (if (null? children)
            (blake2b-hash (u8vector->blob prefixed))
            (let ((child (car children)))
              (do ((i 0 (+ i 1)))
                  ((>= i (u8vector-length child)))
                (u8vector-set! prefixed (+ offset i) (u8vector-ref child i)))
              (loop (cdr children) (+ offset (u8vector-length child))))))))

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
              (let-values (((group rest) (split-at remaining (min n (length remaining)))))
                (loop rest (cons group groups)))))))

  (define (build-tree-level nodes fanout)
    "Build one level of the tree by grouping nodes and hashing."
    (map merkle-hash-node (partition-into-groups nodes fanout)))

  (define (build-tree leaves fanout)
    "Build complete tree from leaves, return root hash."
    (if (<= (length leaves) 1)
        (if (null? leaves)
            (merkle-hash-leaf (make-blob 0))
            (car leaves))
        (build-tree (build-tree-level leaves fanout) fanout)))

  (define (merkle-hash content . opts)
    "Compute Merkle root hash of content. Returns the root hash blob."
    (let* ((cs (get-key opts 'chunk-size: chunk-size-default))
           (fo (get-key opts 'fanout: fanout-default))
           (data (if (string? content)
                     (string->blob content)
                     content))
           (chunks (chunk-content data cs))
           (leaves (map merkle-hash-leaf chunks)))
      (build-tree leaves fo)))

  ;;; ============================================================
  ;;; Tree Structure (for proofs)
  ;;; ============================================================

  (define-record-type <merkle-tree>
    (fields (immutable root merkle-tree-root)
            (immutable levels merkle-tree-levels)   ; Vector of levels, 0 = leaves
            (immutable params merkle-tree-params)))  ; (chunk-size fanout)

  (define (make-merkle-tree-internal root levels params)
    (make-<merkle-tree> root levels params))

  (define (merkle-tree? x)
    (<merkle-tree>? x))

  (define (merkle-tree-depth tree)
    (vector-length (merkle-tree-levels tree)))

  (define (merkle-tree-chunk-count tree)
    (length (vector-ref (merkle-tree-levels tree) 0)))

  (define (merkle-tree content . opts)
    "Build complete Merkle tree, preserving structure for proofs.
     Returns a merkle-tree record."
    (let* ((cs (get-key opts 'chunk-size: chunk-size-default))
           (fo (get-key opts 'fanout: fanout-default))
           (data (if (string? content)
                     (string->blob content)
                     content))
           (chunks (chunk-content data cs))
           (leaves (map merkle-hash-leaf chunks)))
      ;; Build all levels
      (let loop ((current-level leaves) (levels (list leaves)))
        (if (<= (length current-level) 1)
            (let ((all-levels (reverse levels)))
              (make-merkle-tree-internal
               (if (null? current-level)
                   (merkle-hash-leaf (make-blob 0))
                   (car current-level))
               (list->vector all-levels)
               (list cs fo)))
            (let ((next-level (build-tree-level current-level fo)))
              (loop next-level (cons next-level levels)))))))

  (define (merkle-root tree)
    "Get root hash from a merkle-tree."
    (merkle-tree-root tree))

  ;;; ============================================================
  ;;; Inclusion Proofs
  ;;; ============================================================

  (define-record-type <merkle-proof>
    (fields (immutable root proof-root)
            (immutable index proof-index)
            (immutable chunk-hash proof-chunk-hash)
            (immutable path proof-path)))

  (define (make-merkle-proof-record root index chunk-hash path)
    (make-<merkle-proof> root index chunk-hash path))

  (define (merkle-proof? x)
    (<merkle-proof>? x))

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
              (make-merkle-proof-record
               (merkle-tree-root tree)
               chunk-index
               chunk-hash
               (reverse path))
              (let* ((current (vector-ref levels level))
                     (group-idx (div idx fanout))
                     (pos-in-group (mod idx fanout))
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
      (if (not (merkle-blob=? computed-leaf (proof-chunk-hash proof)))
          #f
          ;; Reconstruct path to root
          (let loop ((path (proof-path proof))
                     (current-hash computed-leaf))
            (if (null? path)
                (merkle-blob=? current-hash (proof-root proof))
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

  ;;; ============================================================
  ;;; Blob equality helper
  ;;; ============================================================

  (define (merkle-blob=? a b)
    "Compare two blobs for equality."
    (let ((va (blob->u8vector a))
          (vb (blob->u8vector b)))
      (and (= (u8vector-length va) (u8vector-length vb))
           (let loop ((i 0))
             (or (>= i (u8vector-length va))
                 (and (= (u8vector-ref va i) (u8vector-ref vb i))
                      (loop (+ i 1))))))))

  ;;; ============================================================
  ;;; Dual-Hash Support (Transition Period)
  ;;; ============================================================

  (define-record-type <dual-hash>
    (fields (immutable legacy dual-hash-legacy)        ; SHA-512 hash
            (immutable merkle-root dual-hash-merkle)   ; Merkle root
            (immutable params dual-hash-params)))      ; (chunk-size fanout algorithm)

  (define (dual-hash? x)
    (<dual-hash>? x))

  (define (dual-hash content . opts)
    "Compute both legacy SHA-512 and quantum-resistant Merkle hashes.
     For transition period compatibility."
    (let* ((cs (get-key opts 'chunk-size: chunk-size-default))
           (fo (get-key opts 'fanout: fanout-default))
           (data (if (string? content)
                     (string->blob content)
                     content))
           (legacy (sha512-hash data))
           (merkle (merkle-hash data 'chunk-size: cs 'fanout: fo)))
      (make-<dual-hash> legacy merkle (list cs fo 'blake2b))))

) ;; end library
