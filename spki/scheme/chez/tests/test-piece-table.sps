#!/usr/bin/env chez --script
;;; test-piece-table.sps - Tests for piece table data structure

(import (rnrs)
        (only (chezscheme) printf)
        (cyberspace piece-table))

(define *pass* 0)
(define *fail* 0)

(define (assert-true msg expr)
  (if expr
      (begin (set! *pass* (+ *pass* 1))
             (printf "  PASS: ~a~%" msg))
      (begin (set! *fail* (+ *fail* 1))
             (printf "  FAIL: ~a~%" msg))))

(define (assert-equal msg expected actual)
  (if (equal? expected actual)
      (begin (set! *pass* (+ *pass* 1))
             (printf "  PASS: ~a~%" msg))
      (begin (set! *fail* (+ *fail* 1))
             (printf "  FAIL: ~a (expected ~s, got ~s)~%" msg expected actual))))

(printf "~%=== Piece Table Tests ===~%~%")

;; Test 1: Empty table
(printf "--- Construction ---~%")
(let ((pt (pt-new)))
  (assert-equal "new pt length" 0 (pt-length pt))
  (assert-equal "new pt->string" "" (pt->string pt))
  (assert-equal "new pt piece-count" 0 (pt-piece-count pt)))

;; Test 2: From string
(let ((pt (pt-from-string "Hello World")))
  (assert-equal "from-string length" 11 (pt-length pt))
  (assert-equal "from-string round-trip" "Hello World" (pt->string pt))
  (assert-equal "from-string piece-count" 1 (pt-piece-count pt)))

;; Test 3: Char at
(printf "--- Char At ---~%")
(let ((pt (pt-from-string "abcdef")))
  (assert-equal "char 0" #\a (pt-char-at pt 0))
  (assert-equal "char 3" #\d (pt-char-at pt 3))
  (assert-equal "char 5" #\f (pt-char-at pt 5))
  (assert-equal "char -1" #f (pt-char-at pt -1))
  (assert-equal "char 6" #f (pt-char-at pt 6)))

;; Test 4: Insert in middle
(printf "--- Insert ---~%")
(let ((pt (pt-from-string "Hello World")))
  (pt-insert! pt 5 " Beautiful")
  (assert-equal "insert middle" "Hello Beautiful World" (pt->string pt))
  (assert-equal "insert length" 21 (pt-length pt))
  (assert-equal "insert pieces" 3 (pt-piece-count pt)))

;; Test 5: Insert at beginning
(let ((pt (pt-from-string "World")))
  (pt-insert! pt 0 "Hello ")
  (assert-equal "insert at start" "Hello World" (pt->string pt)))

;; Test 6: Insert at end
(let ((pt (pt-from-string "Hello")))
  (pt-insert! pt 5 " World")
  (assert-equal "insert at end" "Hello World" (pt->string pt)))

;; Test 7: Insert into empty
(let ((pt (pt-new)))
  (pt-insert! pt 0 "Hello")
  (assert-equal "insert into empty" "Hello" (pt->string pt)))

;; Test 8: Multiple inserts
(let ((pt (pt-from-string "ac")))
  (pt-insert! pt 1 "b")
  (assert-equal "after first insert" "abc" (pt->string pt))
  (pt-insert! pt 3 "d")
  (assert-equal "after second insert" "abcd" (pt->string pt)))

;; Test 9: Delete
(printf "--- Delete ---~%")
(let ((pt (pt-from-string "Hello Beautiful World")))
  (pt-delete! pt 5 10)
  (assert-equal "delete middle" "Hello World" (pt->string pt))
  (assert-equal "delete length" 11 (pt-length pt)))

;; Test 10: Delete from beginning
(let ((pt (pt-from-string "Hello World")))
  (pt-delete! pt 0 6)
  (assert-equal "delete from start" "World" (pt->string pt)))

;; Test 11: Delete to end
(let ((pt (pt-from-string "Hello World")))
  (pt-delete! pt 5 6)
  (assert-equal "delete to end" "Hello" (pt->string pt)))

;; Test 12: Substring
(printf "--- Substring ---~%")
(let ((pt (pt-from-string "Hello World")))
  (assert-equal "substring" "World" (pt-substring pt 6 5))
  (assert-equal "substring from start" "Hello" (pt-substring pt 0 5))
  (assert-equal "substring whole" "Hello World" (pt-substring pt 0 11)))

;; Test 13: Undo/Redo
(printf "--- Undo/Redo ---~%")
(let ((pt (pt-from-string "Hello")))
  (assert-true "no undo initially" (not (pt-can-undo? pt)))
  (pt-insert! pt 5 " World")
  (assert-equal "after insert" "Hello World" (pt->string pt))
  (assert-true "can undo" (pt-can-undo? pt))
  (pt-undo! pt)
  (assert-equal "after undo" "Hello" (pt->string pt))
  (assert-true "can redo" (pt-can-redo? pt))
  (pt-redo! pt)
  (assert-equal "after redo" "Hello World" (pt->string pt)))

;; Test 14: Multiple undo
(let ((pt (pt-from-string "a")))
  (pt-insert! pt 1 "b")
  (pt-insert! pt 2 "c")
  (assert-equal "after 2 inserts" "abc" (pt->string pt))
  (pt-undo! pt)
  (assert-equal "undo once" "ab" (pt->string pt))
  (pt-undo! pt)
  (assert-equal "undo twice" "a" (pt->string pt)))

;; Test 15: Undo clears redo on new edit
(let ((pt (pt-from-string "ab")))
  (pt-insert! pt 2 "c")
  (pt-undo! pt)
  (assert-true "can redo before new edit" (pt-can-redo? pt))
  (pt-insert! pt 2 "d")
  (assert-true "redo cleared after new edit" (not (pt-can-redo? pt)))
  (assert-equal "new edit applied" "abd" (pt->string pt)))

;; Test 16: Checkpoint
(printf "--- Checkpoint ---~%")
(let ((pt (pt-from-string "Hello")))
  (pt-checkpoint! pt)
  (pt-insert! pt 5 " World")
  (pt-undo! pt)
  ;; Undoes the insert, going back to checkpoint state
  (assert-equal "undo to checkpoint" "Hello" (pt->string pt)))

;; Test 17: Collaboration operations
(printf "--- Collaboration ---~%")
(let ((ops (pt-get-operations)))
  (assert-true "initially empty ops" (null? ops)))

;; Summary
(printf "~%=== Piece Table: ~a passed, ~a failed ===~%~%" *pass* *fail*)
(when (> *fail* 0) (exit 1))
