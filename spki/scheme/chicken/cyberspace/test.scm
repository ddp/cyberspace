;;; Cyberspace Test Framework - Chicken Scheme
;;;
;;; Minimal test harness matching the Chez test.sls module.
;;; Provides test/assert pattern for portable test suites.

(module test
  (test
   test-case
   assert-equal
   assert-true
   assert-false
   assert-near
   test-summary
   tests-run
   tests-passed
   tests-failed)

  (import scheme
          (chicken base)
          (chicken format))

  ;; Counters
  (define *tests-run* 0)
  (define *tests-passed* 0)
  (define *tests-failed* '())

  (define (tests-run) *tests-run*)
  (define (tests-passed) *tests-passed*)
  (define (tests-failed) *tests-failed*)

  (define (test name thunk)
    (set! *tests-run* (+ 1 *tests-run*))
    (handle-exceptions exn
      (begin
        (printf "FAIL: ~a~%" name)
        (printf "      ~a~%"
                (if (condition? exn)
                    ((condition-property-accessor 'exn 'message "unknown error") exn)
                    "unknown error"))
        (set! *tests-failed* (cons name *tests-failed*)))
      (let ((result (thunk)))
        (if result
            (begin
              (printf "PASS: ~a~%" name)
              (set! *tests-passed* (+ 1 *tests-passed*)))
            (begin
              (printf "FAIL: ~a (returned #f)~%" name)
              (set! *tests-failed* (cons name *tests-failed*)))))))

  (define (test-case name thunk)
    (display (format #f "Testing ~a... " name))
    (thunk)
    (display "✓\n"))

  (define (assert-equal expected actual . rest)
    (or (equal? expected actual)
        (error 'assert-equal (format #f "expected ~s, got ~s" expected actual))))

  (define (assert-true val . rest)
    (or val (error 'assert-true "expected truthy value")))

  (define (assert-false val . rest)
    (or (not val) (error 'assert-false "expected falsy value")))

  (define (assert-near expected actual tolerance)
    (or (< (abs (- expected actual)) tolerance)
        (error 'assert-near
               (format #f "expected ~a within ~a of ~a" actual tolerance expected))))

  (define (test-summary)
    (printf "~%=== Results ===~%")
    (printf "Passed: ~a/~a~%" *tests-passed* *tests-run*)
    (when (> (length *tests-failed*) 0)
      (printf "Failed:~%")
      (for-each (lambda (n) (printf "  - ~a~%" n)) (reverse *tests-failed*)))
    (newline)
    (when (> (length *tests-failed*) 0)
      (exit 1)))

) ;; end module
