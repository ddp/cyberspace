;;; test-query.sps - Query cursor tests for Chez Scheme port
;;; Exercises cursor creation, traversal, sorting, pagination, aggregation.

(import (rnrs)
        (only (chezscheme) printf format)
        (cyberspace query)
        (cyberspace test))

(display "=== Query Cursor Tests ===\n\n")

;; Synthetic four-tuples: (type name size info)
(define test-data
  '((keys    "alice.pub"    32  ("ed25519"))
    (keys    "bob.pub"      32  ("ed25519"))
    (certs   "realm-cert"   512 ("signed"))
    (releases "v1.0.tar"   4096 ("signed" "compressed"))
    (releases "v2.0.tar"   8192 ("signed" "compressed"))
    (archives "backup.zst" 16384 ("compressed"))
    (keys    "carol.pub"    32  ("ed25519" "hybrid"))))

;;; Test 1: Cursor creation
(test-case "cursor-from-list creates cursor"
  (lambda ()
    (let ((c (cursor-from-list test-data)))
      (assert-true (cursor? c) "should be a cursor")
      (assert-equal 7 (cursor-count c) "should have 7 items"))))

;;; Test 2: Cursor traversal
(test-case "cursor-next traversal"
  (lambda ()
    (let ((c (cursor-from-list test-data)))
      (let ((first (cursor-next c)))
        (assert-equal "alice.pub" (cadr first) "first should be alice"))
      (let ((second (cursor-next c)))
        (assert-equal "bob.pub" (cadr second) "second should be bob"))
      ;; Exhaust remaining
      (cursor-next c) (cursor-next c) (cursor-next c)
      (cursor-next c) (cursor-next c)
      (assert-equal #f (cursor-next c) "should return #f at end"))))

;;; Test 3: Cursor peek
(test-case "cursor-peek does not advance"
  (lambda ()
    (let ((c (cursor-from-list test-data)))
      (let ((p1 (cursor-peek c))
            (p2 (cursor-peek c)))
        (assert-equal (cadr p1) (cadr p2) "peek should return same item")
        (assert-equal "alice.pub" (cadr p1) "should be first item")))))

;;; Test 4: Cursor reset
(test-case "cursor-reset returns to beginning"
  (lambda ()
    (let ((c (cursor-from-list test-data)))
      (cursor-next c)
      (cursor-next c)
      (cursor-next c)
      (cursor-reset c)
      (let ((first (cursor-next c)))
        (assert-equal "alice.pub" (cadr first) "should be back at start")))))

;;; Test 5: cursor->list
(test-case "cursor->list materializes remaining"
  (lambda ()
    (let ((c (cursor-from-list test-data)))
      (cursor-next c)  ; skip first
      (let ((rest (cursor->list c)))
        (assert-equal 6 (length rest) "should have 6 remaining")
        (assert-equal "bob.pub" (cadr (car rest)) "should start at bob")))))

;;; Test 6: Sort by name ascending
(test-case "order-by name asc"
  (lambda ()
    (let* ((c (cursor-from-list test-data))
           (sorted (order-by c 'name 'asc))
           (items (cursor->list sorted)))
      (assert-equal "alice.pub" (cadr (car items)) "first alphabetically")
      (assert-equal "v2.0.tar" (cadr (list-ref items 6)) "last alphabetically"))))

;;; Test 7: Sort by size descending
(test-case "order-by size desc"
  (lambda ()
    (let* ((c (cursor-from-list test-data))
           (sorted (order-by c 'size 'desc))
           (items (cursor->list sorted)))
      (assert-equal 16384 (caddr (car items)) "largest first")
      (assert-equal 32 (caddr (list-ref items 6)) "smallest last"))))

;;; Test 8: Cursor limit
(test-case "cursor-limit restricts results"
  (lambda ()
    (let* ((c (cursor-from-list test-data))
           (limited (cursor-limit c 3)))
      (assert-equal 3 (cursor-count limited) "should have 3 items")
      (let ((items (cursor->list limited)))
        (assert-equal 3 (length items) "list should have 3 items")))))

;;; Test 9: Cursor offset
(test-case "cursor-offset skips results"
  (lambda ()
    (let* ((c (cursor-from-list test-data))
           (skipped (cursor-offset c 3)))
      (assert-equal 4 (cursor-count skipped) "should have 4 remaining")
      (let ((first (cursor-next skipped)))
        (assert-equal "v1.0.tar" (cadr first) "should start at 4th item")))))

;;; Test 10: Cursor page
(test-case "cursor-page returns correct page"
  (lambda ()
    (let* ((c (cursor-from-list test-data))
           (page1 (cursor-page c 1 3))
           (page2 (cursor-page c 2 3))
           (page3 (cursor-page c 3 3)))
      (assert-equal 3 (cursor-count page1) "page 1 has 3 items")
      (assert-equal 3 (cursor-count page2) "page 2 has 3 items")
      (assert-equal 1 (cursor-count page3) "page 3 has 1 item"))))

;;; Test 11: Aggregate count
(test-case "cursor-aggregate count"
  (lambda ()
    (let ((c (cursor-from-list test-data)))
      (assert-equal 7 (cursor-aggregate c 'count) "count should be 7"))))

;;; Test 12: Aggregate total-size
(test-case "cursor-aggregate total-size"
  (lambda ()
    (let ((c (cursor-from-list test-data)))
      (assert-equal (+ 32 32 512 4096 8192 16384 32)
                    (cursor-aggregate c 'total-size)
                    "total size"))))

;;; Test 13: Aggregate distinct-types
(test-case "cursor-aggregate distinct-types"
  (lambda ()
    (let* ((c (cursor-from-list test-data))
           (types (cursor-aggregate c 'distinct-types)))
      (assert-equal 4 (length types) "should have 4 distinct types"))))

;;; Test 14: Aggregate distinct-names
(test-case "cursor-aggregate distinct-names"
  (lambda ()
    (let* ((c (cursor-from-list test-data))
           (names (cursor-aggregate c 'distinct-names)))
      (assert-equal 7 (length names) "all names unique, should be 7"))))

;;; Test 15: Combined sort + limit
(test-case "sort then limit"
  (lambda ()
    (let* ((c (cursor-from-list test-data))
           (sorted (order-by c 'size 'desc))
           (top3 (cursor-limit sorted 3))
           (items (cursor->list top3)))
      (assert-equal 3 (length items) "top 3")
      (assert-equal 16384 (caddr (car items)) "largest")
      (assert-equal 4096 (caddr (caddr items)) "third largest"))))

;;; Test 16: Empty cursor
(test-case "empty cursor"
  (lambda ()
    (let ((c (cursor-from-list '())))
      (assert-equal 0 (cursor-count c) "empty count")
      (assert-equal #f (cursor-next c) "next returns #f")
      (assert-equal #f (cursor-peek c) "peek returns #f")
      (assert-equal '() (cursor->list c) "list is empty"))))

(display "\n=== All Query tests PASSED ===\n")
