#!/usr/bin/env csi -s
;; Merkle Tree Implementation
;; Based on Ralph Merkle's 1979 paper "A Certified Digital Signature"
;;
;; Paper: ~/cyberspace/library/cryptographers/merkle/
;;
;; Concept: Build a binary tree where:
;;   - Leaf nodes = hash of data blocks
;;   - Internal nodes = hash of concatenated child hashes
;;   - Root hash authenticates entire dataset
;;
;; Applications: Git, Bitcoin, IPFS, Certificate Transparency

(import scheme)
(import (chicken base))
(import (chicken io))
(import (chicken file))
(import (chicken process))
(import (chicken process-context))
(import (chicken string))
(import (chicken format))
(import srfi-1)
(import srfi-13)

;; ============================================================================
;; SHA-256 Hashing
;; ============================================================================

(define (sha256 text)
  "Compute SHA-256 hash using openssl"
  (let ((result (with-input-from-pipe
                 (string-append "echo -n '" (escape-shell text) "' | openssl dgst -sha256 -hex")
                 read-line)))
    (if result
        (string-trim-both (car (reverse (string-split result " "))))
        #f)))

(define (escape-shell text)
  "Escape single quotes for shell"
  (string-translate* text '(("'" . "'\"'\"'"))))

(define (sha256-concat hash1 hash2)
  "Hash the concatenation of two hashes"
  (sha256 (string-append hash1 hash2)))

;; ============================================================================
;; Merkle Tree Structure
;; ============================================================================

;; Tree node: (type value left right)
;;   type: 'leaf or 'internal
;;   value: hash
;;   left/right: child nodes (or #f for leaf)

(define (make-leaf data)
  "Create a leaf node from data"
  (list 'leaf (sha256 data) data #f))

(define (make-internal left right)
  "Create an internal node from two children"
  (let ((left-hash (node-hash left))
        (right-hash (node-hash right)))
    (list 'internal (sha256-concat left-hash right-hash) left right)))

(define (node-type node) (car node))
(define (node-hash node) (cadr node))
(define (node-data node) (caddr node))
(define (node-left node) (caddr node))
(define (node-right node) (cadddr node))

(define (leaf? node) (eq? (node-type node) 'leaf))
(define (internal? node) (eq? (node-type node) 'internal))

;; ============================================================================
;; Tree Construction
;; ============================================================================

(define (build-merkle-tree data-list)
  "Build a Merkle tree from a list of data items"
  (if (null? data-list)
      #f
      (let ((leaves (map make-leaf data-list)))
        (build-tree-level leaves))))

(define (build-tree-level nodes)
  "Build one level of the tree by pairing nodes"
  (cond
   ((null? nodes) #f)
   ((null? (cdr nodes)) (car nodes))  ; Single node = root
   (else
    ;; Pair up nodes and build next level
    (let ((paired (pair-nodes nodes)))
      (build-tree-level paired)))))

(define (pair-nodes nodes)
  "Pair up nodes to create parent level"
  (cond
   ((null? nodes) '())
   ((null? (cdr nodes))
    ;; Odd number: duplicate last node
    (list (make-internal (car nodes) (car nodes))))
   (else
    ;; Pair first two nodes
    (cons (make-internal (car nodes) (cadr nodes))
          (pair-nodes (cddr nodes))))))

;; ============================================================================
;; Tree Traversal and Display
;; ============================================================================

(define (tree-height node)
  "Calculate height of tree"
  (if (leaf? node)
      0
      (+ 1 (max (tree-height (node-left node))
                (tree-height (node-right node))))))

(define (count-leaves node)
  "Count leaf nodes"
  (if (leaf? node)
      1
      (+ (count-leaves (node-left node))
         (count-leaves (node-right node)))))

(define (display-tree node #!optional (indent 0))
  "Pretty print tree structure"
  (let ((prefix (make-string (* indent 2) #\space))
        (hash-abbrev (substring (node-hash node) 0 8)))
    (if (leaf? node)
        (begin
          (display prefix)
          (display "LEAF: ")
          (display hash-abbrev)
          (display "... [")
          (display (node-data node))
          (display "]\n"))
        (begin
          (display prefix)
          (display "NODE: ")
          (display hash-abbrev)
          (display "...\n")
          (display-tree (node-left node) (+ indent 1))
          (display-tree (node-right node) (+ indent 1))))))

;; ============================================================================
;; Merkle Proof (Inclusion Proof)
;; ============================================================================

(define (generate-proof tree data)
  "Generate a Merkle proof that data is in tree"
  (let ((target-hash (sha256 data)))
    (find-path tree target-hash '())))

(define (find-path node target path)
  "Find path from root to target leaf, building path from leaf to root"
  (cond
   ((not node) #f)
   ((and (leaf? node) (string=? (node-hash node) target))
    path)  ; Don't reverse - path is already leaf-to-root
   ((leaf? node) #f)
   (else
    ;; Try left subtree (we are on left, sibling on right)
    (let ((left-result (find-path (node-left node) target
                                  (cons (list 'left (node-hash (node-right node))) path))))
      (if left-result
          left-result
          ;; Try right subtree (we are on right, sibling on left)
          (find-path (node-right node) target
                     (cons (list 'right (node-hash (node-left node))) path)))))))

(define (verify-proof data root-hash proof)
  "Verify a Merkle proof"
  (let ((leaf-hash (sha256 data)))
    (verify-proof-hash leaf-hash root-hash proof)))

(define *debug-verify* #f)

(define (verify-proof-hash current-hash root-hash proof)
  "Verify proof by recomputing root hash"
  (if (null? proof)
      (begin
        (when *debug-verify*
          (print "Final hash: " current-hash)
          (print "Root hash:  " root-hash))
        (string=? current-hash root-hash))
      (let* ((step (car proof))
             (direction (car step))
             (sibling-hash (cadr step))
             ;; If we are on left, concat us then sibling
             ;; If we are on right, concat sibling then us
             (next-hash (if (eq? direction 'left)
                           (sha256-concat current-hash sibling-hash)
                           (sha256-concat sibling-hash current-hash))))
        (when *debug-verify*
          (print "Current: " (substring current-hash 0 16) "...")
          (print "Direction: " direction)
          (print "Sibling: " (substring sibling-hash 0 16) "...")
          (print "Next: " (substring next-hash 0 16) "...")
          (print ""))
        (verify-proof-hash next-hash root-hash (cdr proof)))))

;; ============================================================================
;; Content-Addressable Storage (Git-like)
;; ============================================================================

(define *object-store* "objects/")

(define (init-object-store!)
  "Initialize object store directory"
  (unless (directory-exists? *object-store*)
    (create-directory *object-store*)
    (print "Initialized object store: " *object-store*)))

(define (store-object data)
  "Store data in content-addressable store, return hash"
  (let ((hash (sha256 data)))
    (init-object-store!)
    (let ((path (string-append *object-store* hash)))
      (unless (file-exists? path)
        (with-output-to-file path
          (lambda () (display data))))
      hash)))

(define (retrieve-object hash)
  "Retrieve data by hash from store"
  (let ((path (string-append *object-store* hash)))
    (if (file-exists? path)
        (with-input-from-file path
          (lambda () (read-string #f)))
        #f)))

(define (store-tree tree)
  "Store entire Merkle tree in object store"
  (if (leaf? tree)
      (store-object (node-data tree))
      (begin
        (store-tree (node-left tree))
        (store-tree (node-right tree))
        (node-hash tree))))

;; ============================================================================
;; Git-like Operations
;; ============================================================================

(define (commit message files)
  "Create a Git-like commit with files"
  (init-object-store!)

  ;; Store each file
  (let ((file-hashes
         (map (lambda (filename)
                (if (file-exists? filename)
                    (let ((content (with-input-from-file filename
                                    (lambda () (read-string #f)))))
                      (list filename (store-object content)))
                    (begin
                      (print "Warning: File not found: " filename)
                      (list filename #f))))
              files)))

    ;; Build tree from file hashes
    (let* ((valid-files (filter (lambda (f) (cadr f)) file-hashes))
           (file-data (map (lambda (f) (string-append (car f) ":" (cadr f)))
                          valid-files))
           (tree (build-merkle-tree file-data))
           (tree-hash (if tree (node-hash tree) "empty")))

      ;; Create commit object
      (let ((commit-data (string-append
                         "tree " tree-hash "\n"
                         "message " message "\n"
                         "files " (number->string (length valid-files)) "\n"
                         (apply string-append
                                (map (lambda (f)
                                       (string-append (car f) " " (cadr f) "\n"))
                                     valid-files)))))
        (let ((commit-hash (store-object commit-data)))
          (print "Commit " commit-hash)
          (print "Tree " tree-hash)
          (print "Files: " (length valid-files))
          commit-hash)))))

;; ============================================================================
;; CLI Interface
;; ============================================================================

(define (show-help)
  (display "╔═══════════════════════════════════════════════════════════════════╗\n")
  (display "║              MERKLE TREE IMPLEMENTATION                           ║\n")
  (display "║              Based on Merkle (1979)                               ║\n")
  (display "╚═══════════════════════════════════════════════════════════════════╝\n\n")
  (display "USAGE:\n")
  (display "  ./merkle.scm build <item1> <item2> ...\n")
  (display "  ./merkle.scm prove <item> <item1> <item2> ...\n")
  (display "  ./merkle.scm commit <message> <file1> <file2> ...\n")
  (display "  ./merkle.scm store <file>\n")
  (display "  ./merkle.scm retrieve <hash>\n")
  (display "\n")
  (display "COMMANDS:\n")
  (display "  build    - Build Merkle tree from items and show structure\n")
  (display "  prove    - Generate and verify inclusion proof\n")
  (display "  commit   - Git-like commit with content-addressable storage\n")
  (display "  store    - Store file by content hash\n")
  (display "  retrieve - Retrieve file by hash\n")
  (display "\n")
  (display "EXAMPLES:\n")
  (display "  # Build tree from data items\n")
  (display "  ./merkle.scm build \"alice\" \"bob\" \"carol\" \"dave\"\n")
  (display "\n")
  (display "  # Prove 'bob' is in the tree\n")
  (display "  ./merkle.scm prove \"bob\" \"alice\" \"bob\" \"carol\" \"dave\"\n")
  (display "\n")
  (display "  # Create a commit\n")
  (display "  ./merkle.scm commit \"Initial commit\" file1.txt file2.txt\n")
  (display "\n")
  (display "  # Store file by hash\n")
  (display "  ./merkle.scm store README.md\n")
  (display "\n")
  (display "CONCEPTS:\n")
  (display "  Merkle Tree: Binary tree where each node = hash of children\n")
  (display "  Root Hash: Single hash that authenticates entire dataset\n")
  (display "  Inclusion Proof: Prove data is in tree with O(log n) hashes\n")
  (display "  Content-Addressable: Store data by its hash (Git model)\n")
  (display "\n")
  (display "APPLICATIONS:\n")
  (display "  Git: Commits, trees, and blobs are Merkle trees\n")
  (display "  Bitcoin: Transactions in blocks use Merkle trees\n")
  (display "  IPFS: Content-addressable distributed storage\n")
  (display "  Certificate Transparency: Append-only log with Merkle trees\n")
  (display "\n")
  (display "PAPER:\n")
  (display "  Ralph Merkle (1979)\n")
  (display "  \"A Certified Digital Signature\"\n")
  (display "  ~/cyberspace/library/cryptographers/merkle/\n")
  (display "\n"))

(define (cmd-build args)
  "Build and display Merkle tree"
  (if (null? args)
      (print "Error: Need at least one data item")
      (let ((tree (build-merkle-tree args)))
        (print "╔═══════════════════════════════════════")
        (print "║ Merkle Tree Built")
        (print "╠═══════════════════════════════════════")
        (print "║ Items: " (length args))
        (print "║ Leaves: " (count-leaves tree))
        (print "║ Height: " (tree-height tree))
        (print "║ Root: " (node-hash tree))
        (print "╚═══════════════════════════════════════\n")
        (print "Tree Structure:")
        (display-tree tree)
        (print ""))))

(define (cmd-prove args)
  "Generate and verify inclusion proof"
  (if (< (length args) 2)
      (print "Error: Need <item> followed by tree items")
      (let* ((target (car args))
             (tree-items (cdr args))
             (tree (build-merkle-tree tree-items))
             (proof (generate-proof tree target)))
        (print "═══════════════════════════════════════")
        (print "Target: " target)
        (print "Target Hash: " (sha256 target))
        (print "Root Hash: " (node-hash tree))
        (print "═══════════════════════════════════════\n")

        (if proof
            (begin
              (print "✓ Inclusion Proof Found!")
              (print "Proof path (" (length proof) " steps):\n")
              (let loop ((p proof) (n 1))
                (unless (null? p)
                  (let* ((step (car p))
                         (dir (car step))
                         (hash (cadr step)))
                    (print "  " n ". " dir " sibling: " (substring hash 0 16) "...")
                    (loop (cdr p) (+ n 1)))))
              (print "")

              ;; Verify the proof
              (if (verify-proof target (node-hash tree) proof)
                  (print "✓ Proof verification PASSED")
                  (print "✗ Proof verification FAILED")))
            (print "✗ Item not found in tree")))))

(define (cmd-commit args)
  "Create Git-like commit"
  (if (< (length args) 2)
      (print "Error: Need <message> followed by files")
      (let ((message (car args))
            (files (cdr args)))
        (commit message files))))

(define (cmd-store args)
  "Store file by content hash"
  (if (null? args)
      (print "Error: Need filename")
      (let ((filename (car args)))
        (if (file-exists? filename)
            (let* ((content (with-input-from-file filename
                             (lambda () (read-string #f))))
                   (hash (store-object content)))
              (print "Stored: " filename)
              (print "Hash: " hash)
              (print "Size: " (string-length content) " bytes"))
            (print "Error: File not found: " filename)))))

(define (cmd-retrieve args)
  "Retrieve file by hash"
  (if (null? args)
      (print "Error: Need hash")
      (let* ((hash (car args))
             (content (retrieve-object hash)))
        (if content
            (begin
              (print "Retrieved object " hash ":")
              (print "─────────────────────────────────────")
              (display content)
              (print "\n─────────────────────────────────────")
              (print "Size: " (string-length content) " bytes"))
            (print "Error: Object not found: " hash)))))

;; Main entry point
(when (not (null? (command-line-arguments)))
  (let ((cmd (car (command-line-arguments)))
        (args (cdr (command-line-arguments))))
    (cond
     ((string=? cmd "build") (cmd-build args))
     ((string=? cmd "prove") (cmd-prove args))
     ((string=? cmd "commit") (cmd-commit args))
     ((string=? cmd "store") (cmd-store args))
     ((string=? cmd "retrieve") (cmd-retrieve args))
     (else (show-help)))))

;; REPL usage
(when (and (equal? (program-name) "csi")
           (null? (command-line-arguments)))
  (show-help)
  (print "REPL Functions:")
  (print "  (build-merkle-tree '(\"item1\" \"item2\" ...))")
  (print "  (display-tree tree)")
  (print "  (generate-proof tree \"item\")")
  (print "  (verify-proof \"item\" root-hash proof)")
  (print ""))
