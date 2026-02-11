#!/usr/bin/env csi -s
;;; test-auto-enroll.scm - Tests for auto-enrollment module
;;;
;;; Tests enrollment state management, realm status,
;;; persistence round-trip, and scaling factor computation.

(import scheme
        (chicken base)
        (chicken format)
        (chicken condition)
        srfi-1
        crypto-ffi
        capability
        auto-enroll)

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
;; Tests
;; ============================================================

(printf "~n=== Auto-Enrollment Tests ===~n~n")

(test "reset-enrollment-state! clears all state"
  (lambda ()
    (reset-enrollment-state!)
    (let ((status (realm-status)))
      (and (not (alist-ref 'master status))
           (not (alist-ref 'role status))
           (= 0 (alist-ref 'member-count status))))))

(test "enrollment-status reports not enrolled after reset"
  (lambda ()
    (reset-enrollment-state!)
    (let ((status (enrollment-status)))
      (assert-equal #f (alist-ref 'enrolled status)))))

(test "realm-status structure is well-formed"
  (lambda ()
    (reset-enrollment-state!)
    (let ((status (realm-status)))
      (and (assq 'master status)
           (assq 'role status)
           (assq 'member-count status)
           (assq 'scaling status)))))

(test "compute-scaling-factor with single member"
  (lambda ()
    (let* ((hw '(hardware
                 (model "Mac Studio")
                 (mobile #f)
                 (weave 2000000)
                 (memory-gb 128)
                 (root-avail-gb 1000)))
           (members (list (cons 'studio hw)))
           (scaling (compute-scaling-factor members)))
      ;; Single member should be reference with scale 1.0
      (and (equal? 'studio (alist-ref 'reference scaling))
           (= 1 (alist-ref 'member-count scaling))
           (= 1.0 (alist-ref 'effective-capacity scaling))))))

(test "compute-scaling-factor normalization"
  (lambda ()
    (let* ((hw-strong '(hardware
                        (model "Mac Studio")
                        (mobile #f)
                        (weave 2000000)
                        (memory-gb 128)
                        (root-avail-gb 1000)))
           (hw-weak '(hardware
                      (model "MacBook Air")
                      (mobile #t)
                      (weave 500000)
                      (memory-gb 16)
                      (root-avail-gb 256)))
           (members (list (cons 'studio hw-strong)
                          (cons 'air hw-weak)))
           (scaling (compute-scaling-factor members))
           (member-scales (alist-ref 'members scaling)))
      ;; Studio should be reference (1.0), Air should be < 1.0
      (and (equal? 'studio (alist-ref 'reference scaling))
           (= 2 (alist-ref 'member-count scaling))
           ;; Air gets 10x mobile penalty, should be much less than 1.0
           (let ((air-scale (alist-ref 'air member-scales)))
             (and air-scale (< air-scale 0.5)))))))

(test "elect-master picks most capable, prefers non-mobile"
  (lambda ()
    (let* ((hw-server '(hardware
                        (model "Mac Studio")
                        (mobile #f)
                        (weave 2000000)
                        (memory-gb 128)
                        (root-avail-gb 1000)))
           (hw-laptop '(hardware
                        (model "MacBook Air")
                        (mobile #t)
                        (weave 500000)
                        (memory-gb 16)
                        (root-avail-gb 256)))
           (candidates (list (cons 'laptop hw-laptop)
                             (cons 'server hw-server))))
      (let-values (((winner score all-scores) (elect-master candidates)))
        ;; Server should win due to mobile penalty on laptop
        (eq? winner 'server)))))

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
