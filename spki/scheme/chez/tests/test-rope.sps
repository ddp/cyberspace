#!/usr/bin/env chez --script
;;; test-rope.sps - Tests for rope data structure

(import (rnrs)
        (only (chezscheme) printf)
        (cyberspace rope))

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

(printf "~%=== Rope Tests ===~%~%")

;; Test 1: Construction
(printf "--- Construction ---~%")
(let ((r (rope-new)))
  (assert-true "new rope is rope" (rope? r))
  (assert-true "new rope is leaf" (rope-leaf? r))
  (assert-equal "new rope length 0" 0 (rope-length r))
  (assert-equal "new rope->string" "" (rope->string r)))

;; Test 2: From string
(printf "--- From String ---~%")
(let ((r (rope-from-string "Hello, World!")))
  (assert-true "from-string is rope" (rope? r))
  (assert-equal "from-string length" 13 (rope-length r))
  (assert-equal "from-string round-trip" "Hello, World!" (rope->string r)))

;; Test 3: Char at
(printf "--- Char At ---~%")
(let ((r (rope-from-string "abcdefghij")))
  (assert-equal "char 0" #\a (rope-char-at r 0))
  (assert-equal "char 4" #\e (rope-char-at r 4))
  (assert-equal "char 9" #\j (rope-char-at r 9))
  (assert-equal "char -1" #f (rope-char-at r -1))
  (assert-equal "char 10" #f (rope-char-at r 10)))

;; Test 4: Concatenation
(printf "--- Concat ---~%")
(let* ((r1 (rope-from-string "Hello"))
       (r2 (rope-from-string " World"))
       (r3 (rope-concat r1 r2)))
  (assert-equal "concat length" 11 (rope-length r3))
  (assert-equal "concat string" "Hello World" (rope->string r3)))

;; Test 5: Concat with empty
(let* ((r1 (rope-from-string "abc"))
       (r2 (rope-new)))
  (assert-equal "concat with empty right" "abc" (rope->string (rope-concat r1 r2)))
  (assert-equal "concat with empty left" "abc" (rope->string (rope-concat r2 r1))))

;; Test 6: Split
(printf "--- Split ---~%")
(let* ((r (rope-from-string "Hello World"))
       (split (rope-split r 5)))
  (assert-equal "split left" "Hello" (rope->string (car split)))
  (assert-equal "split right" " World" (rope->string (cdr split))))

;; Test 7: Split at boundaries
(let ((r (rope-from-string "abc")))
  (let ((s0 (rope-split r 0)))
    (assert-equal "split at 0 left" "" (rope->string (car s0)))
    (assert-equal "split at 0 right" "abc" (rope->string (cdr s0))))
  (let ((s3 (rope-split r 3)))
    (assert-equal "split at end left" "abc" (rope->string (car s3)))
    (assert-equal "split at end right" "" (rope->string (cdr s3)))))

;; Test 8: Insert
(printf "--- Insert ---~%")
(let* ((r (rope-from-string "Hello World"))
       (r2 (rope-insert r 5 " Beautiful")))
  (assert-equal "insert" "Hello Beautiful World" (rope->string r2))
  (assert-equal "insert length" 21 (rope-length r2)))

;; Test 9: Insert at beginning and end
(let* ((r (rope-from-string "middle"))
       (r2 (rope-insert r 0 "start "))
       (r3 (rope-insert r2 12 " end")))
  (assert-equal "insert at start" "start middle end" (rope->string r3)))

;; Test 10: Delete
(printf "--- Delete ---~%")
(let* ((r (rope-from-string "Hello Beautiful World"))
       (r2 (rope-delete r 5 10)))
  (assert-equal "delete" "Hello World" (rope->string r2))
  (assert-equal "delete length" 11 (rope-length r2)))

;; Test 11: Substring
(printf "--- Substring ---~%")
(let ((r (rope-from-string "Hello World")))
  (assert-equal "substring" "World" (rope-substring r 6 11))
  (assert-equal "substring from start" "Hello" (rope-substring r 0 5)))

;; Test 12: Depth
(printf "--- Depth ---~%")
(let ((leaf (rope-from-string "short")))
  (assert-equal "leaf depth" 0 (rope-depth leaf)))
;; Small leaves merge into single leaf (< max-leaf-size)
(let* ((r1 (rope-from-string "a"))
       (r2 (rope-from-string "b"))
       (r3 (rope-concat r1 r2)))
  (assert-equal "small concat merges to leaf" 0 (rope-depth r3))
  (assert-equal "merged content" "ab" (rope->string r3)))
;; Large enough to force a node
(let* ((big1 (rope-from-string (make-string 600 #\a)))
       (big2 (rope-from-string (make-string 600 #\b)))
       (r3 (rope-concat big1 big2)))
  (assert-true "large concat has depth > 0" (> (rope-depth r3) 0)))

;; Test 13: Large string splits into tree
(printf "--- Large Rope ---~%")
(let* ((big (make-string 5000 #\x))
       (r (rope-from-string big)))
  (assert-equal "large rope length" 5000 (rope-length r))
  (assert-true "large rope has depth" (> (rope-depth r) 0))
  (assert-equal "large rope round-trip" big (rope->string r)))

;; Test 14: Immutability (original not modified)
(printf "--- Immutability ---~%")
(let* ((r1 (rope-from-string "original"))
       (r2 (rope-insert r1 4 "XY"))
       (r3 (rope-delete r1 2 3)))
  (assert-equal "original unchanged after insert" "original" (rope->string r1))
  (assert-equal "insert result" "origXYinal" (rope->string r2))
  (assert-equal "delete result" "ornal" (rope->string r3)))

;; Summary
(printf "~%=== Rope: ~a passed, ~a failed ===~%~%" *pass* *fail*)
(when (> *fail* 0) (exit 1))
