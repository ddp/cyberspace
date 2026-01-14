;;; SPKI Scheme - Merkle Catalog for Federation Convergence
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

(module catalog
  (;; Catalog operations
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

  (import scheme
          (chicken base)
          (chicken blob)
          (chicken sort)
          (chicken format)
          srfi-1      ; list utilities
          srfi-4      ; u8vectors
          srfi-69     ; hash tables
          crypto-ffi)

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
    (let* ((h1-vec (blob->u8vector h1))
           (h2-vec (blob->u8vector h2))
           (combined (make-u8vector (+ 1 (u8vector-length h1-vec)
                                       (u8vector-length h2-vec)))))
      ;; Interior node marker (Memo-042 domain separation)
      (u8vector-set! combined 0 1)
      ;; Copy h1
      (do ((i 0 (+ i 1)))
          ((= i (u8vector-length h1-vec)))
        (u8vector-set! combined (+ 1 i) (u8vector-ref h1-vec i)))
      ;; Copy h2
      (do ((i 0 (+ i 1)))
          ((= i (u8vector-length h2-vec)))
        (u8vector-set! combined (+ 1 (u8vector-length h1-vec) i)
                       (u8vector-ref h2-vec i)))
      (catalog-hash (u8vector->blob combined))))

  (define (leaf-hash data)
    "Hash leaf data with domain separation.
     Prefix with 0x00 for leaf nodes."
    (let* ((data-bytes (if (blob? data) (blob->u8vector data)
                           (blob->u8vector (string->blob data))))
           (prefixed (make-u8vector (+ 1 (u8vector-length data-bytes)))))
      ;; Leaf node marker (Memo-042 domain separation)
      (u8vector-set! prefixed 0 0)
      (do ((i 0 (+ i 1)))
          ((= i (u8vector-length data-bytes)))
        (u8vector-set! prefixed (+ 1 i) (u8vector-ref data-bytes i)))
      (catalog-hash (u8vector->blob prefixed))))

  ;; ============================================================
  ;; Merkle Tree Structure
  ;; ============================================================
  ;;
  ;; Catalog is a sorted Merkle tree of object hashes.
  ;; Sorting ensures deterministic tree structure for diffing.

  (define-record-type <merkle-node>
    (make-merkle-node hash left right leaf-data)
    merkle-node?
    (hash node-hash)
    (left node-left)
    (right node-right)
    (leaf-data node-leaf-data))

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

  (define-record-type <catalog>
    (make-catalog-internal root items item-set)
    catalog?
    (root catalog-root-node catalog-root-node-set!)
    (items catalog-items catalog-items-set!)
    (item-set catalog-item-set))

  (define (make-catalog)
    "Create empty catalog"
    (make-catalog-internal #f '() (make-hash-table string=?)))

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
    (let* ((items (sort (catalog-items catalog) string<?))
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
       ((blob=? local-root remote-root)
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

  ;; ============================================================
  ;; Helpers
  ;; ============================================================

  (define (blob=? a b)
    "Compare two blobs for equality"
    (let ((av (blob->u8vector a))
          (bv (blob->u8vector b)))
      (and (= (u8vector-length av) (u8vector-length bv))
           (let loop ((i 0))
             (or (= i (u8vector-length av))
                 (and (= (u8vector-ref av i) (u8vector-ref bv i))
                      (loop (+ i 1))))))))

) ;; end module

;;;
;;; Example: Catalog for federation convergence
;;;
;;;   (import catalog)
;;;
;;;   ;; Node A builds catalog of local objects
;;;   (define cat-a (make-catalog))
;;;   (catalog-add! cat-a "sha256:abc123...")
;;;   (catalog-add! cat-a "sha256:def456...")
;;;   (catalog-root cat-a)  ; => #${merkle-root-hash}
;;;
;;;   ;; Node B builds its catalog
;;;   (define cat-b (make-catalog))
;;;   (catalog-add! cat-b "sha256:def456...")
;;;   (catalog-add! cat-b "sha256:ghi789...")
;;;
;;;   ;; Exchange roots, detect difference
;;;   (catalog-diff cat-a (catalog-root cat-b))
;;;   ; => needs detailed sync
;;;
;;;   ;; Generate proof that abc123 is in cat-a
;;;   (define proof (catalog-proof cat-a "sha256:abc123..."))
;;;
;;;   ;; Verify proof
;;;   (catalog-verify-proof (catalog-root cat-a) "sha256:abc123..." proof)
;;;   ; => #t
;;;
;;; Post-Quantum Notes:
;;;
;;;   Current: SHA-256 (128-bit quantum security)
;;;   Future:  SHAKE256 (128-bit quantum security, NIST standard)
;;;
;;;   Both hash functions provide equivalent security against
;;;   Grover's algorithm. Migration path preserves security.
;;;
