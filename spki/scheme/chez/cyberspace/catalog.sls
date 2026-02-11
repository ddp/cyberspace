;;; SPKI Scheme - Merkle Catalog for Federation Convergence
;;; Library of Cyberspace - Chez Port
;;;
;;; Provides deterministic Merkle tree of object inventory for
;;; efficient diff calculation between federation peers.
;;;
;;; Ported from Chicken's catalog.scm.
;;; Changes: module -> library, srfi-69 -> Chez hashtables,
;;;          mutable records -> R6RS, (chicken sort) -> Chez sort.

(library (cyberspace catalog)
  (export
    make-catalog
    catalog-root
    catalog-add!
    catalog-remove!
    catalog-contains?
    catalog-size
    catalog->list
    catalog-diff
    catalog-proof
    catalog-verify-proof
    catalog-merge-diff
    catalog-serialize
    catalog-deserialize
    hash-combine
    sorted-hash-tree)

  (import (except (rnrs) make-hashtable equal-hash)
          (only (chezscheme) sort make-hashtable equal-hash)
          (cyberspace crypto-ffi)
          (except (cyberspace chicken-compatibility blob) blob=?)
          (cyberspace chicken-compatibility chicken))

  ;; ============================================================
  ;; Post-Quantum Hash Selection
  ;; ============================================================

  (define *catalog-hash* 'sha256)

  (define (catalog-hash data)
    (case *catalog-hash*
      ((sha256) (sha256-hash data))
      (else (sha256-hash data))))

  (define (hash-combine h1 h2)
    "Combine two hashes for Merkle tree interior node."
    (let* ((h1-vec (blob->u8vector h1))
           (h2-vec (blob->u8vector h2))
           (combined (make-u8vector (+ 1 (u8vector-length h1-vec)
                                       (u8vector-length h2-vec)))))
      (u8vector-set! combined 0 1)  ; interior node marker
      (do ((i 0 (+ i 1))) ((= i (u8vector-length h1-vec)))
        (u8vector-set! combined (+ 1 i) (u8vector-ref h1-vec i)))
      (do ((i 0 (+ i 1))) ((= i (u8vector-length h2-vec)))
        (u8vector-set! combined (+ 1 (u8vector-length h1-vec) i)
                       (u8vector-ref h2-vec i)))
      (catalog-hash (u8vector->blob combined))))

  (define (leaf-hash data)
    (let* ((data-bytes (if (bytevector? data) (blob->u8vector data)
                           (blob->u8vector (string->blob data))))
           (prefixed (make-u8vector (+ 1 (u8vector-length data-bytes)))))
      (u8vector-set! prefixed 0 0)  ; leaf node marker
      (do ((i 0 (+ i 1))) ((= i (u8vector-length data-bytes)))
        (u8vector-set! prefixed (+ 1 i) (u8vector-ref data-bytes i)))
      (catalog-hash (u8vector->blob prefixed))))

  ;; ============================================================
  ;; Merkle Tree Structure
  ;; ============================================================

  (define-record-type <merkle-node>
    (fields (immutable hash node-hash)
            (immutable left node-left)
            (immutable right node-right)
            (immutable leaf-data node-leaf-data)))

  (define (make-merkle-node hash left right leaf-data)
    (make-<merkle-node> hash left right leaf-data))

  (define (make-leaf data)
    (make-merkle-node (leaf-hash data) #f #f data))

  (define (make-interior left right)
    (make-merkle-node (hash-combine (node-hash left) (node-hash right))
                      left right #f))

  (define (node-leaf? node)
    (and (not (node-left node)) (not (node-right node))))

  ;; ============================================================
  ;; Catalog
  ;; ============================================================

  (define-record-type <catalog>
    (fields (mutable root-node catalog-root-node catalog-root-node-set!)
            (mutable items catalog-items catalog-items-set!)
            (immutable item-set catalog-item-set)))

  (define (make-catalog)
    (make-<catalog> #f '() (make-hashtable equal-hash equal?)))

  (define (catalog-root catalog)
    (let ((root (catalog-root-node catalog)))
      (and root (node-hash root))))

  (define (catalog-size catalog)
    (length (catalog-items catalog)))

  (define (catalog-contains? catalog item)
    (hashtable-contains? (catalog-item-set catalog) item))

  (define (catalog->list catalog)
    (catalog-items catalog))

  ;; ============================================================
  ;; Tree Construction
  ;; ============================================================

  (define (sorted-hash-tree items)
    (if (null? items) #f
        (build-tree (map make-leaf items))))

  (define (build-tree nodes)
    (cond
     ((null? nodes) #f)
     ((null? (cdr nodes)) (car nodes))
     (else (build-tree (pair-nodes nodes)))))

  (define (pair-nodes nodes)
    (cond
     ((null? nodes) '())
     ((null? (cdr nodes)) (list (car nodes)))
     (else (cons (make-interior (car nodes) (cadr nodes))
                 (pair-nodes (cddr nodes))))))

  (define (rebuild-catalog! catalog)
    (let* ((items (sort string<? (catalog-items catalog)))
           (tree (sorted-hash-tree items)))
      (catalog-items-set! catalog items)
      (catalog-root-node-set! catalog tree)))

  (define (catalog-add! catalog item)
    (unless (catalog-contains? catalog item)
      (hashtable-set! (catalog-item-set catalog) item #t)
      (catalog-items-set! catalog (cons item (catalog-items catalog)))
      (rebuild-catalog! catalog)))

  (define (catalog-remove! catalog item)
    (when (catalog-contains? catalog item)
      (hashtable-delete! (catalog-item-set catalog) item)
      (catalog-items-set! catalog
                         (filter (lambda (x) (not (string=? x item)))
                                (catalog-items catalog)))
      (rebuild-catalog! catalog)))

  ;; ============================================================
  ;; Merkle Diff
  ;; ============================================================

  (define (blob=? a b)
    (let ((va (blob->u8vector a))
          (vb (blob->u8vector b)))
      (and (= (u8vector-length va) (u8vector-length vb))
           (let loop ((i 0))
             (or (>= i (u8vector-length va))
                 (and (= (u8vector-ref va i) (u8vector-ref vb i))
                      (loop (+ i 1))))))))

  (define (catalog-diff local-catalog remote-root)
    (let ((local-root (catalog-root local-catalog)))
      (cond
       ((and (not local-root) (not remote-root)) (values '() '()))
       ((not remote-root) (values '() (catalog-items local-catalog)))
       ((not local-root) (values 'need-full-sync '()))
       ((blob=? local-root remote-root) (values '() '()))
       (else (values 'subtree-diff-needed '())))))

  ;; ============================================================
  ;; Merkle Proofs
  ;; ============================================================

  (define (tree-contains? node target)
    (cond
     ((not node) #f)
     ((node-leaf? node) (string=? (node-leaf-data node) target))
     (else (or (tree-contains? (node-left node) target)
               (tree-contains? (node-right node) target)))))

  (define (generate-proof node target items path)
    (cond
     ((not node) #f)
     ((node-leaf? node)
      (if (string=? (node-leaf-data node) target) path #f))
     (else
      (cond
       ((tree-contains? (node-left node) target)
        (let ((sub-proof (generate-proof (node-left node) target items path)))
          (and sub-proof
               (append sub-proof (list `(right ,(node-hash (node-right node))))))))
       ((tree-contains? (node-right node) target)
        (let ((sub-proof (generate-proof (node-right node) target items path)))
          (and sub-proof
               (append sub-proof (list `(left ,(node-hash (node-left node))))))))
       (else #f)))))

  (define (catalog-proof catalog item)
    (if (not (catalog-contains? catalog item))
        #f
        (generate-proof (catalog-root-node catalog) item (catalog-items catalog) '())))

  (define (catalog-verify-proof root-hash item proof)
    (let loop ((current (leaf-hash item)) (path proof))
      (if (null? path)
          (blob=? current root-hash)
          (let* ((sibling (car path))
                 (side (car sibling))
                 (sibling-hash (cadr sibling)))
            (loop (if (eq? side 'left)
                      (hash-combine sibling-hash current)
                      (hash-combine current sibling-hash))
                  (cdr path))))))

  ;; ============================================================
  ;; Serialization
  ;; ============================================================

  (define (catalog-serialize catalog)
    `(catalog
      (version 1)
      (algorithm ,*catalog-hash*)
      (root ,(catalog-root catalog))
      (size ,(catalog-size catalog))
      (items ,(catalog-items catalog))))

  (define (catalog-deserialize sexp)
    (let* ((items (cadr (assq 'items (cdr sexp))))
           (catalog (make-catalog)))
      (for-each (lambda (item) (catalog-add! catalog item)) items)
      catalog))

  (define (catalog-merge-diff catalog missing-items)
    (for-each (lambda (item) (catalog-add! catalog item)) missing-items))

) ;; end library
