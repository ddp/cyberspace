;;; Cyberspace Test Framework - Chez Scheme
;;;
;;; Minimal test harness for porting Chicken test suite.
;;; Provides test/assert pattern matching the Chicken tests.

(library (cyberspace test)
  (export
    test
    test-case
    assert-equal
    assert-true
    assert-false
    assert-near
    test-summary
    tests-run
    tests-passed
    tests-failed)

  (import (rnrs)
         (only (chezscheme) printf format))

  ;; Counters
  (define *tests-run* 0)
  (define *tests-passed* 0)
  (define *tests-failed* '())

  (define (tests-run) *tests-run*)
  (define (tests-passed) *tests-passed*)
  (define (tests-failed) *tests-failed*)

  ;; Framework-style test: runs thunk, catches exceptions, tracks pass/fail
  (define (test name thunk)
    (set! *tests-run* (+ 1 *tests-run*))
    (guard (exn
            [#t
             (printf "FAIL: ~a~n" name)
             (printf "      ~a~n"
                     (if (message-condition? exn)
                         (condition-message exn)
                         "unknown error"))
             (set! *tests-failed* (cons name *tests-failed*))])
      (let ((result (thunk)))
        (if result
            (begin
              (printf "PASS: ~a~n" name)
              (set! *tests-passed* (+ 1 *tests-passed*)))
            (begin
              (printf "FAIL: ~a (returned #f)~n" name)
              (set! *tests-failed* (cons name *tests-failed*)))))))

  ;; Simple test-case: display name, run, print checkmark
  (define (test-case name thunk)
    (display (format #f "Testing ~a... " name))
    (thunk)
    (display "✓\n"))

  ;; Assertions
  (define (assert-equal expected actual . rest)
    (or (equal? expected actual)
        (error 'assert-equal
               (format #f "expected ~s, got ~s" expected actual))))

  (define (assert-true val . rest)
    (or val (error 'assert-true "expected truthy value")))

  (define (assert-false val . rest)
    (or (not val) (error 'assert-false "expected falsy value")))

  (define (assert-near expected actual tolerance)
    (or (< (abs (- expected actual)) tolerance)
        (error 'assert-near
               (format #f "expected ~a within ~a of ~a" actual tolerance expected))))

  ;; Summary
  (define (test-summary)
    (printf "~n=== Results ===~n")
    (printf "Passed: ~a/~a~n" *tests-passed* *tests-run*)
    (when (> (length *tests-failed*) 0)
      (printf "Failed:~n")
      (for-each (lambda (n) (printf "  - ~a~n" n)) (reverse *tests-failed*)))
    (newline)
    (when (> (length *tests-failed*) 0)
      (exit 1)))

) ;; end library
