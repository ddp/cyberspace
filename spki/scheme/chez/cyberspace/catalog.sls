;;; SPKI Scheme - Merkle Catalog for Federation Convergence
;;; Chez Scheme Port
;;;
;;; Provides deterministic Merkle tree of object inventory for
;;; efficient diff calculation between federation peers.
;;;
;;; Post-Quantum Design:
;;; - Uses SHA-256 (128-bit quantum security via Grover)
;;; - Ready for SHAKE256 upgrade when libsodium adds support
;;; - Tree structure allows O(log n) diff detection
;;;
;;; Memo-042 specifies SHAKE256 for quantum resistance.
;;; This implementation uses SHA-256 as transitional hash
;;; (same 128-bit quantum security level).
;;;
;;; Ported from Chicken's catalog.scm.
;;; Changes: module -> library, blob/u8vector -> bytevector compat,
;;;          srfi-69 -> hash-table compat, SRFI-9 -> R6RS records,
;;;          (chicken sort) -> (chezscheme) sort, sprintf -> format.

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
          (only (chezscheme) sort format printf)
          (cyberspace chicken-compatibility blob)
          (cyberspace chicken-compatibility chicken)
          (cyberspace chicken-compatibility hash-table)
          (cyberspace crypto-ffi))

  ;; ============================================================
  ;; SRFI-1 helpers
  ;; ============================================================

  (define (filter-map f lst)
    (let loop ((rest lst) (acc '()))
      (if (null? rest)
          (reverse acc)
          (let ((v (f (car rest))))
            (loop (cdr rest) (if v (cons v acc) acc))))))

  ;; ============================================================
  ;; Post-Quantum Hash Selection
  ;; ============================================================
  ;;
  ;; Current: SHA-256 (256-bit classical, 128-bit quantum)
  ;; Future:  SHAKE256 (256-bit classical, 128-bit quantum)
  ;;
  ;; Both provide same quantum security. SHAKE256 preferred for
  ;; alignment with SPHINCS+ signatures (Memo-043).

  (define *catalog-hash* 'sha256)  ; 'sha256 | 'shake256 (future)

  (define (catalog-hash data)
    "Hash data using catalog algorithm (post-quantum ready)"
    (case *catalog-hash*
      ((sha256) (sha256-hash data))
      ;; When SHAKE256 available:
      ;; ((shake256) (shake256-hash data 32))
      (else (sha256-hash data))))

  (define (hash-combine h1 h2)
    "Combine two hashes for Merkle tree interior node.
     Domain separation: prefix with 0x01 for interior nodes."
    (let* ((h1-bv (if (bytevector? h1) h1 (string->utf8 h1)))
           (h2-bv (if (bytevector? h2) h2 (string->utf8 h2)))
           (combined (make-bytevector (+ 1 (bytevector-length h1-bv)
                                          (bytevector-length h2-bv)))))
      ;; Interior node marker (Memo-042 domain separation)
      (bytevector-u8-set! combined 0 1)
      ;; Copy h1
      (bytevector-copy! h1-bv 0 combined 1 (bytevector-length h1-bv))
      ;; Copy h2
      (bytevector-copy! h2-bv 0 combined (+ 1 (bytevector-length h1-bv))
                        (bytevector-length h2-bv))
      (catalog-hash combined)))

  (define (leaf-hash data)
    "Hash leaf data with domain separation.
     Prefix with 0x00 for leaf nodes."
    (let* ((data-bytes (cond
                        ((bytevector? data) data)
                        ((string? data) (string->utf8 data))
                        (else (string->utf8 (blob->string data)))))
           (prefixed (make-bytevector (+ 1 (bytevector-length data-bytes)))))
      ;; Leaf node marker (Memo-042 domain separation)
      (bytevector-u8-set! prefixed 0 0)
      (bytevector-copy! data-bytes 0 prefixed 1 (bytevector-length data-bytes))
      (catalog-hash prefixed)))

  ;; ============================================================
  ;; Merkle Tree Structure
  ;; ============================================================
  ;;
  ;; Catalog is a sorted Merkle tree of object hashes.
  ;; Sorting ensures deterministic tree structure for diffing.

  (define-record-type (merkle-node make-merkle-node merkle-node?)
    (fields (immutable hash node-hash)
            (immutable left node-left)
            (immutable right node-right)
            (immutable leaf-data node-leaf-data)))

  (define (make-leaf data)
    "Create a leaf node"
    (make-merkle-node (leaf-hash data) #f #f data))

  (define (make-interior left right)
    "Create an interior node from two children"
    (make-merkle-node (hash-combine (node-hash left) (node-hash right))
                      left right #f))

  (define (node-leaf? node)
    "Is this a leaf node?"
    (and (not (node-left node)) (not (node-right node))))

  ;; ============================================================
  ;; Catalog (Merkle Tree of Object Hashes)
  ;; ============================================================

  (define-record-type (catalog-record make-catalog-internal catalog?)
    (fields (mutable root-node catalog-root-node catalog-root-node-set!)
            (mutable items catalog-items catalog-items-set!)
            (immutable item-set catalog-item-set)))

  (define (make-catalog)
    "Create empty catalog"
    (make-catalog-internal #f '() (make-hash-table)))

  (define (catalog-root catalog)
    "Get root hash of catalog (or #f if empty)"
    (let ((root (catalog-root-node catalog)))
      (and root (node-hash root))))

  (define (catalog-size catalog)
    "Number of items in catalog"
    (length (catalog-items catalog)))

  (define (catalog-contains? catalog item)
    "Check if item is in catalog"
    (hash-table-exists? (catalog-item-set catalog) item))

  (define (catalog->list catalog)
    "Get sorted list of catalog items"
    (catalog-items catalog))

  ;; ============================================================
  ;; Sorted Hash Tree Construction
  ;; ============================================================

  (define (sorted-hash-tree items)
    "Build balanced Merkle tree from sorted list of items"
    (if (null? items)
        #f
        (build-tree (map make-leaf items))))

  (define (build-tree nodes)
    "Build tree bottom-up from leaf nodes"
    (cond
     ((null? nodes) #f)
     ((null? (cdr nodes)) (car nodes))  ; single node
     (else
      (build-tree (pair-nodes nodes)))))

  (define (pair-nodes nodes)
    "Pair adjacent nodes into parent nodes"
    (cond
     ((null? nodes) '())
     ((null? (cdr nodes))
      ;; Odd node: promote as-is (or duplicate for balanced tree)
      (list (car nodes)))
     (else
      (cons (make-interior (car nodes) (cadr nodes))
            (pair-nodes (cddr nodes))))))

  (define (rebuild-catalog! catalog)
    "Rebuild Merkle tree from items"
    (let* ((items (sort string<? (catalog-items catalog)))
           (tree (sorted-hash-tree items)))
      (catalog-items-set! catalog items)
      (catalog-root-node-set! catalog tree)))

  (define (catalog-add! catalog item)
    "Add item to catalog"
    (unless (catalog-contains? catalog item)
      (hash-table-set! (catalog-item-set catalog) item #t)
      (catalog-items-set! catalog (cons item (catalog-items catalog)))
      (rebuild-catalog! catalog)))

  (define (catalog-remove! catalog item)
    "Remove item from catalog"
    (when (catalog-contains? catalog item)
      (hash-table-delete! (catalog-item-set catalog) item)
      (catalog-items-set! catalog
                         (filter (lambda (x) (not (string=? x item)))
                                (catalog-items catalog)))
      (rebuild-catalog! catalog)))

  ;; ============================================================
  ;; Merkle Diff (O(log n) Difference Detection)
  ;; ============================================================

  (define (catalog-diff local-catalog remote-root)
    "Find items that differ between local catalog and remote root.
     Returns: (values missing-locally extra-locally)

     This is the second phase of federation convergence:
     After Bloom filter exchange identifies candidates,
     Merkle diff precisely locates differences."

    ;; Compare root hashes
    (let ((local-root (catalog-root local-catalog)))
      (cond
       ;; Both empty - no diff
       ((and (not local-root) (not remote-root))
        (values '() '()))
       ;; Remote empty - everything is extra locally
       ((not remote-root)
        (values '() (catalog-items local-catalog)))
       ;; Local empty - everything is missing
       ((not local-root)
        (values 'need-full-sync '()))
       ;; Roots match - synchronized
       ((bytevector=? local-root remote-root)
        (values '() '()))
       ;; Roots differ - need detailed comparison
       (else
        ;; For detailed diff, we'd need to exchange subtree hashes
        ;; This returns indication that diff is needed
        (values 'subtree-diff-needed '())))))

  ;; ============================================================
  ;; Merkle Proofs
  ;; ============================================================

  (define (catalog-proof catalog item)
    "Generate inclusion proof for item.
     Returns: list of sibling hashes from leaf to root"
    (if (not (catalog-contains? catalog item))
        #f
        (let ((items (catalog-items catalog)))
          (generate-proof (catalog-root-node catalog)
                         item
                         items
                         '()))))

  (define (tree-contains? node target)
    "Check if target is in this subtree"
    (cond
     ((not node) #f)
     ((node-leaf? node) (string=? (node-leaf-data node) target))
     (else (or (tree-contains? (node-left node) target)
               (tree-contains? (node-right node) target)))))

  (define (generate-proof node target items path)
    "Recursively generate proof path by traversing actual tree structure.
     Returns proof in leaf-to-root order (first element is leaf's sibling)."
    (cond
     ((not node) #f)
     ((node-leaf? node)
      (if (string=? (node-leaf-data node) target)
          path  ;; Return path as-is (leaf-to-root order)
          #f))
     (else
      ;; Check which subtree actually contains the target
      ;; Append sibling info AFTER recursing (so leaf level comes first)
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

  (define (catalog-verify-proof root-hash item proof)
    "Verify an inclusion proof"
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
    "Serialize catalog for network transfer"
    `(catalog
      (version 1)
      (algorithm ,*catalog-hash*)
      (root ,(catalog-root catalog))
      (size ,(catalog-size catalog))
      (items ,(catalog-items catalog))))

  (define (catalog-deserialize sexp)
    "Deserialize catalog"
    (let* ((items (cadr (assq 'items (cdr sexp))))
           (catalog (make-catalog)))
      (for-each (lambda (item) (catalog-add! catalog item)) items)
      catalog))

  (define (catalog-merge-diff catalog missing-items)
    "Merge items from remote into local catalog"
    (for-each (lambda (item) (catalog-add! catalog item)) missing-items))

) ;; end library
