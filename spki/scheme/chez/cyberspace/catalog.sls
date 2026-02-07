;;; SPKI Scheme - Merkle Catalog for Federation Convergence (Chez Port)
;;; Library of Cyberspace
;;;
;;; Deterministic Merkle tree of object inventory for efficient
;;; diff calculation between federation peers.
;;;
;;; Three-layer convergence (Memo-010):
;;;   Layer 1: Bloom filter exchange (bloom.sls)
;;;   Layer 2: Merkle tree diff (this module)
;;;   Layer 3: Object transfer (gossip.sls)
;;;
;;; Ported from catalog.scm.
;;; Copyright (c) 2026 Yoyodyne. See LICENSE.

(library (cyberspace catalog)
  (export
    ;; Catalog operations
    make-catalog
    catalog-root
    catalog-add!
    catalog-remove!
    catalog-contains?
    catalog-size
    catalog->list
    ;; Merkle tree operations
    catalog-diff
    catalog-proof
    catalog-verify-proof
    catalog-merge-diff
    ;; Serialization
    catalog-serialize
    catalog-deserialize
    ;; Utilities
    hash-combine
    sorted-hash-tree)

  (import (rnrs)
          (only (chezscheme) printf format void list-sort)
          (cyberspace crypto-ffi)
          (cyberspace chicken-compatibility blob)
          (cyberspace chicken-compatibility hashtable))

  ;; ============================================================
  ;; Hash Selection
  ;; ============================================================

  (define *catalog-hash* 'sha256)

  (define (catalog-hash data)
    (case *catalog-hash*
      ((sha256) (sha256-hash data))
      (else (sha256-hash data))))

  (define (hash-combine h1 h2)
    "Combine two hashes for interior node (domain separation: 0x01 prefix)."
    (let* ((h1-len (bytevector-length h1))
           (h2-len (bytevector-length h2))
           (combined (make-bytevector (+ 1 h1-len h2-len))))
      ;; Interior node marker
      (bytevector-u8-set! combined 0 1)
      ;; Copy h1
      (bytevector-copy! h1 0 combined 1 h1-len)
      ;; Copy h2
      (bytevector-copy! h2 0 combined (+ 1 h1-len) h2-len)
      (catalog-hash combined)))

  (define (leaf-hash data)
    "Hash leaf data (domain separation: 0x00 prefix)."
    (let* ((data-bytes (if (bytevector? data) data (string->utf8 data)))
           (prefixed (make-bytevector (+ 1 (bytevector-length data-bytes)))))
      (bytevector-u8-set! prefixed 0 0)
      (bytevector-copy! data-bytes 0 prefixed 1 (bytevector-length data-bytes))
      (catalog-hash prefixed)))

  ;; ============================================================
  ;; Merkle Tree Structure
  ;; ============================================================

  (define *node-tag* (list 'merkle-node))

  ;; #(tag hash left right leaf-data)
  (define (make-merkle-node hash left right leaf-data)
    (vector *node-tag* hash left right leaf-data))

  (define (merkle-node? x)
    (and (vector? x) (= (vector-length x) 5)
         (eq? (vector-ref x 0) *node-tag*)))

  (define (node-hash n) (vector-ref n 1))
  (define (node-left n) (vector-ref n 2))
  (define (node-right n) (vector-ref n 3))
  (define (node-leaf-data n) (vector-ref n 4))

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

  (define *catalog-tag* (list 'catalog))

  ;; #(tag root items item-set)
  (define (make-catalog-internal root items item-set)
    (vector *catalog-tag* root items item-set))

  (define (catalog? x)
    (and (vector? x) (= (vector-length x) 4)
         (eq? (vector-ref x 0) *catalog-tag*)))

  (define (catalog-root-node c) (vector-ref c 1))
  (define (catalog-root-node-set! c v) (vector-set! c 1 v))
  (define (catalog-items c) (vector-ref c 2))
  (define (catalog-items-set! c v) (vector-set! c 2 v))
  (define (catalog-item-set c) (vector-ref c 3))

  (define (make-catalog)
    (make-catalog-internal #f '() (make-hash-table string=?)))

  (define (catalog-root catalog)
    (let ((root (catalog-root-node catalog)))
      (and root (node-hash root))))

  (define (catalog-size catalog)
    (length (catalog-items catalog)))

  (define (catalog-contains? catalog item)
    (hash-table-exists? (catalog-item-set catalog) item))

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
     (else
      (cons (make-interior (car nodes) (cadr nodes))
            (pair-nodes (cddr nodes))))))

  (define (rebuild-catalog! catalog)
    (let* ((items (list-sort string<? (catalog-items catalog)))
           (tree (sorted-hash-tree items)))
      (catalog-items-set! catalog items)
      (catalog-root-node-set! catalog tree)))

  (define (catalog-add! catalog item)
    (unless (catalog-contains? catalog item)
      (hash-table-set! (catalog-item-set catalog) item #t)
      (catalog-items-set! catalog (cons item (catalog-items catalog)))
      (rebuild-catalog! catalog)))

  (define (catalog-remove! catalog item)
    (when (catalog-contains? catalog item)
      (hash-table-delete! (catalog-item-set catalog) item)
      (catalog-items-set! catalog
                         (filter (lambda (x) (not (string=? x item)))
                                (catalog-items catalog)))
      (rebuild-catalog! catalog)))

  ;; ============================================================
  ;; Merkle Diff
  ;; ============================================================

  (define (catalog-diff local-catalog remote-root)
    "Compare local catalog with remote root hash.
     Returns two values: missing-locally, extra-locally."
    (let ((local-root (catalog-root local-catalog)))
      (cond
       ((and (not local-root) (not remote-root))
        (values '() '()))
       ((not remote-root)
        (values '() (catalog-items local-catalog)))
       ((not local-root)
        (values 'need-full-sync '()))
       ((bytevector=? local-root remote-root)
        (values '() '()))
       (else
        (values 'subtree-diff-needed '())))))

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
        (let ((sub (generate-proof (node-left node) target items path)))
          (and sub
               (append sub (list `(right ,(node-hash (node-right node))))))))
       ((tree-contains? (node-right node) target)
        (let ((sub (generate-proof (node-right node) target items path)))
          (and sub
               (append sub (list `(left ,(node-hash (node-left node))))))))
       (else #f)))))

  (define (catalog-proof catalog item)
    (if (not (catalog-contains? catalog item))
        #f
        (generate-proof (catalog-root-node catalog) item
                        (catalog-items catalog) '())))

  (define (catalog-verify-proof root-hash item proof)
    (let loop ((current (leaf-hash item))
               (path proof))
      (if (null? path)
          (bytevector=? current root-hash)
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
