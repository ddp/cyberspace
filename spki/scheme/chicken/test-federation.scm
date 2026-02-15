#!/usr/bin/env csi -s
;;; test-federation.scm - Federation integration tests
;;;
;;; Simulates multi-node federation scenarios:
;;; - Network partitions and healing
;;; - Concurrent updates
;;; - Byzantine (malicious) nodes
;;; - Large-scale convergence

(import scheme
        (chicken base)
        (chicken blob)
        (chicken format)
        (chicken condition)
        (chicken time)
        srfi-1
        srfi-4
        srfi-69
        bloom
        catalog
        crypto-ffi)

;; Initialize libsodium
(sodium-init)

;; ============================================================
;; Test Framework
;; ============================================================

(define *tests-run* 0)
(define *tests-passed* 0)
(define *tests-failed* '())

(define (test name thunk)
  (set! *tests-run* (+ 1 *tests-run*))
  (handle-exceptions exn
    (begin
      (printf "FAIL: ~a~n" name)
      (printf "      ~a~n" (get-condition-property exn 'exn 'message "unknown error"))
      (set! *tests-failed* (cons name *tests-failed*)))
    (let ((result (thunk)))
      (if result
          (begin
            (printf "PASS: ~a~n" name)
            (set! *tests-passed* (+ 1 *tests-passed*)))
          (begin
            (printf "FAIL: ~a (returned #f)~n" name)
            (set! *tests-failed* (cons name *tests-failed*)))))))

(define (assert-equal expected actual)
  (or (equal? expected actual)
      (error (sprintf "expected ~s, got ~s" expected actual))))

(define (assert-true val)
  (or val (error "expected truthy value")))

;; ============================================================
;; Simulated Node
;; ============================================================

(define-record-type <node>
  (make-node-internal name catalog bloom objects)
  node?
  (name node-name)
  (catalog node-catalog)
  (bloom node-bloom node-bloom-set!)
  (objects node-objects node-objects-set!))

(define (make-node name)
  "Create a simulated federation node"
  (make-node-internal name (make-catalog) #f (make-hash-table string=?)))

(define (node-add-object! node hash content)
  "Add an object to a node's inventory"
  (hash-table-set! (node-objects node) hash content)
  (catalog-add! (node-catalog node) hash)
  (node-bloom-set! node
    (make-inventory-bloom (hash-table-keys (node-objects node)))))

(define (node-has-object? node hash)
  "Check if node has an object"
  (hash-table-exists? (node-objects node) hash))

(define (node-object-count node)
  "Count objects in node"
  (hash-table-size (node-objects node)))

(define (node-root node)
  "Get node's Merkle root"
  (catalog-root (node-catalog node)))

(define (nodes-synchronized? node1 node2)
  "Check if two nodes have the same inventory"
  (let ((r1 (node-root node1))
        (r2 (node-root node2)))
    (cond
     ((and (not r1) (not r2)) #t)  ; both empty
     ((or (not r1) (not r2)) #f)   ; one empty
     (else
      (let ((v1 (blob->u8vector r1))
            (v2 (blob->u8vector r2)))
        (equal? (u8vector->list v1) (u8vector->list v2)))))))

;; ============================================================
;; Simulated Sync Operation
;; ============================================================

(define (sync-nodes! source target)
  "Simulate one-way sync: target gets source's objects"
  ;; Layer 1: Exchange Bloom filters
  (let* ((source-bloom (node-bloom source))
         (target-bloom (node-bloom target))
         (source-hashes (hash-table-keys (node-objects source))))

    ;; Find what source has that target might not
    (let ((candidates
           (if (not target-bloom)
               source-hashes  ; target is empty, get everything
               (filter (lambda (h)
                         (or (not (blocked-bloom-contains?
                                   target-bloom (string->blob h)))
                             ;; Also check if target really has it
                             (not (node-has-object? target h))))
                       source-hashes))))

      ;; Layer 2: Verify with catalog
      ;; (Simplified: just check if target really has them)
      (let ((actually-missing
             (filter (lambda (h) (not (node-has-object? target h)))
                     candidates)))

        ;; Layer 3: Transfer objects
        (for-each
         (lambda (hash)
           (let ((content (hash-table-ref (node-objects source) hash)))
             (node-add-object! target hash content)))
         actually-missing)

        (length actually-missing)))))

(define (bidirectional-sync! node1 node2)
  "Bidirectional sync between two nodes"
  (let ((from-1-to-2 (sync-nodes! node1 node2))
        (from-2-to-1 (sync-nodes! node2 node1)))
    (+ from-1-to-2 from-2-to-1)))

;; ============================================================
;; Basic Federation Tests
;; ============================================================

(printf "~n=== Federation Integration Tests ===~n~n")
(printf "--- Basic Federation ---~n")

(test "two empty nodes are synchronized"
  (lambda ()
    (let ((alice (make-node 'alice))
          (bob (make-node 'bob)))
      (nodes-synchronized? alice bob))))

(test "sync from populated to empty node"
  (lambda ()
    (let ((alice (make-node 'alice))
          (bob (make-node 'bob)))
      (node-add-object! alice "sha256:doc1" "content 1")
      (node-add-object! alice "sha256:doc2" "content 2")
      (sync-nodes! alice bob)
      (and (node-has-object? bob "sha256:doc1")
           (node-has-object? bob "sha256:doc2")
           (nodes-synchronized? alice bob)))))

(test "bidirectional sync merges inventories"
  (lambda ()
    (let ((alice (make-node 'alice))
          (bob (make-node 'bob)))
      (node-add-object! alice "sha256:from-alice" "alice content")
      (node-add-object! bob "sha256:from-bob" "bob content")
      (bidirectional-sync! alice bob)
      (and (node-has-object? alice "sha256:from-bob")
           (node-has-object? bob "sha256:from-alice")
           (nodes-synchronized? alice bob)))))

(test "sync is idempotent"
  (lambda ()
    (let ((alice (make-node 'alice))
          (bob (make-node 'bob)))
      (node-add-object! alice "sha256:doc" "content")
      (sync-nodes! alice bob)
      (let ((count1 (node-object-count bob)))
        (sync-nodes! alice bob)  ; sync again
        (= count1 (node-object-count bob))))))

;; ============================================================
;; Multi-Node Federation
;; ============================================================

(printf "~n--- Multi-Node Federation ---~n")

(test "three-node linear sync"
  (lambda ()
    ;; alice -> bob -> carol
    (let ((alice (make-node 'alice))
          (bob (make-node 'bob))
          (carol (make-node 'carol)))
      (node-add-object! alice "sha256:origin" "from alice")
      (sync-nodes! alice bob)
      (sync-nodes! bob carol)
      (node-has-object? carol "sha256:origin"))))

(test "three-node convergence"
  (lambda ()
    ;; Each node has unique content, all sync
    (let ((alice (make-node 'alice))
          (bob (make-node 'bob))
          (carol (make-node 'carol)))
      (node-add-object! alice "sha256:alice-doc" "alice")
      (node-add-object! bob "sha256:bob-doc" "bob")
      (node-add-object! carol "sha256:carol-doc" "carol")

      ;; Full mesh sync
      (bidirectional-sync! alice bob)
      (bidirectional-sync! bob carol)
      (bidirectional-sync! alice carol)

      (and (= 3 (node-object-count alice))
           (= 3 (node-object-count bob))
           (= 3 (node-object-count carol))
           (nodes-synchronized? alice bob)
           (nodes-synchronized? bob carol)))))

(test "star topology convergence"
  (lambda ()
    ;; Central hub with spokes
    (let ((hub (make-node 'hub))
          (spoke1 (make-node 'spoke1))
          (spoke2 (make-node 'spoke2))
          (spoke3 (make-node 'spoke3)))
      (node-add-object! spoke1 "sha256:s1" "spoke 1")
      (node-add-object! spoke2 "sha256:s2" "spoke 2")
      (node-add-object! spoke3 "sha256:s3" "spoke 3")

      ;; All spokes sync with hub
      (bidirectional-sync! spoke1 hub)
      (bidirectional-sync! spoke2 hub)
      (bidirectional-sync! spoke3 hub)

      ;; Hub should have all
      (= 3 (node-object-count hub)))))

;; ============================================================
;; Network Partition Scenarios
;; ============================================================

(printf "~n--- Network Partitions ---~n")

(test "partition healing: rejoin after isolated updates"
  (lambda ()
    (let ((alice (make-node 'alice))
          (bob (make-node 'bob)))
      ;; Initial sync
      (node-add-object! alice "sha256:initial" "shared")
      (sync-nodes! alice bob)

      ;; Partition: each adds content while disconnected
      (node-add-object! alice "sha256:during-partition-a" "alice private")
      (node-add-object! bob "sha256:during-partition-b" "bob private")

      ;; Healing: reconnect and sync
      (bidirectional-sync! alice bob)

      (and (= 3 (node-object-count alice))
           (= 3 (node-object-count bob))
           (nodes-synchronized? alice bob)))))

(test "partition: three-way split and heal"
  (lambda ()
    (let ((a (make-node 'a))
          (b (make-node 'b))
          (c (make-node 'c)))
      ;; Initial shared state
      (node-add-object! a "sha256:shared" "common")
      (bidirectional-sync! a b)
      (bidirectional-sync! b c)

      ;; Three-way partition
      (node-add-object! a "sha256:a-isolated" "a only")
      (node-add-object! b "sha256:b-isolated" "b only")
      (node-add-object! c "sha256:c-isolated" "c only")

      ;; Heal
      (bidirectional-sync! a b)
      (bidirectional-sync! b c)
      (bidirectional-sync! a c)

      (and (= 4 (node-object-count a))
           (= 4 (node-object-count b))
           (= 4 (node-object-count c))))))

;; ============================================================
;; Concurrent Update Scenarios
;; ============================================================

(printf "~n--- Concurrent Updates ---~n")

(test "concurrent additions converge"
  (lambda ()
    (let ((a (make-node 'a))
          (b (make-node 'b)))
      ;; Simulate concurrent updates
      (node-add-object! a "sha256:concurrent-1" "from a")
      (node-add-object! b "sha256:concurrent-2" "from b")
      (node-add-object! a "sha256:concurrent-3" "from a again")
      (node-add-object! b "sha256:concurrent-4" "from b again")

      (bidirectional-sync! a b)

      (and (= 4 (node-object-count a))
           (= 4 (node-object-count b))
           (nodes-synchronized? a b)))))

(test "rapid-fire updates"
  (lambda ()
    (let ((a (make-node 'a))
          (b (make-node 'b)))
      ;; Many rapid updates
      (do ((i 0 (+ i 1)))
          ((= i 50))
        (node-add-object! a (sprintf "sha256:a-~a" i) "content"))
      (do ((i 0 (+ i 1)))
          ((= i 50))
        (node-add-object! b (sprintf "sha256:b-~a" i) "content"))

      (bidirectional-sync! a b)

      (and (= 100 (node-object-count a))
           (= 100 (node-object-count b))))))

;; ============================================================
;; Gossip Propagation Scenarios
;; ============================================================

(printf "~n--- Gossip Propagation ---~n")

(test "epidemic spread: 10-node ring"
  (lambda ()
    ;; Create ring of nodes
    (let ((nodes (map (lambda (i) (make-node (string->symbol (sprintf "node~a" i))))
                      (iota 10))))
      ;; Origin has content
      (node-add-object! (car nodes) "sha256:epidemic" "spreading content")

      ;; Gossip around ring (each talks to next)
      (let loop ((remaining nodes))
        (when (pair? (cdr remaining))
          (bidirectional-sync! (car remaining) (cadr remaining))
          (loop (cdr remaining))))

      ;; Last node should have the content
      (node-has-object? (last nodes) "sha256:epidemic"))))

(test "epidemic spread: random mesh"
  (lambda ()
    (let ((nodes (map (lambda (i) (make-node (string->symbol (sprintf "n~a" i))))
                      (iota 5))))
      ;; Each node adds unique content
      (for-each
       (lambda (n i)
         (node-add-object! n (sprintf "sha256:from-~a" i) "content"))
       nodes (iota 5))

      ;; Random-ish sync pattern (fully connected for simplicity)
      (for-each
       (lambda (n1)
         (for-each
          (lambda (n2)
            (unless (eq? n1 n2)
              (bidirectional-sync! n1 n2)))
          nodes))
       nodes)

      ;; All nodes should have all content
      (every (lambda (n) (= 5 (node-object-count n))) nodes))))

;; ============================================================
;; Large Scale Tests
;; ============================================================

(printf "~n--- Large Scale ---~n")

(test "1000 objects converge"
  (lambda ()
    (let ((a (make-node 'a))
          (b (make-node 'b)))
      (do ((i 0 (+ i 1)))
          ((= i 1000))
        (node-add-object! a (sprintf "sha256:~a" i) "c"))
      (sync-nodes! a b)
      (= 1000 (node-object-count b)))))

(test "20-node federation with unique content"
  (lambda ()
    (let ((nodes (map (lambda (i) (make-node (string->symbol (sprintf "node~a" i))))
                      (iota 20))))
      ;; Each adds 10 objects
      (for-each
       (lambda (n i)
         (do ((j 0 (+ j 1)))
             ((= j 10))
           (node-add-object! n (sprintf "sha256:~a-~a" i j) "c")))
       nodes (iota 20))

      ;; Full sync (naive O(n^2) for test)
      (for-each
       (lambda (n1)
         (for-each
          (lambda (n2)
            (unless (eq? n1 n2)
              (sync-nodes! n1 n2)))
          nodes))
       nodes)

      ;; All should have 200 objects
      (every (lambda (n) (= 200 (node-object-count n))) nodes))))

;; ============================================================
;; Summary
;; ============================================================

(printf "~n=== Results ===~n")
(printf "Passed: ~a/~a~n" *tests-passed* *tests-run*)
(when (> (length *tests-failed*) 0)
  (printf "Failed:~n")
  (for-each (lambda (n) (printf "  - ~a~n" n)) (reverse *tests-failed*)))
(newline)

;; Exit with error code if tests failed
(when (> (length *tests-failed*) 0)
  (exit 1))
