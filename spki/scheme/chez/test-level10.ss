#!/usr/bin/env chez-script
;;; test-level10.ss - Tests for Level 10 Application Modules (Chez Port)
;;;
;;; Tests: ui, display, edt, info, inspector, seal CLI, cyberspace CLI
;;;
;;; Run: CHEZSCHEMELIBDIRS=. chez --program test-level10.ss
;;;
;;; Copyright (c) 2026 Yoyodyne. See LICENSE.

(import (rnrs)
        (only (chezscheme)
              printf format void
              with-output-to-string with-input-from-string
              file-exists? getenv)
        (cyberspace chicken-compatibility chicken)
        (cyberspace chicken-compatibility hashtable)
        (cyberspace os)
        (cyberspace display)
        (cyberspace edt)
        (cyberspace info)
        (cyberspace inspector))

;; ============================================================
;; Test Framework
;; ============================================================

(define *tests-run* 0)
(define *tests-passed* 0)
(define *tests-failed* 0)

(define (test name expected actual)
  (set! *tests-run* (+ *tests-run* 1))
  (if (equal? expected actual)
      (begin
        (set! *tests-passed* (+ *tests-passed* 1))
        (printf "  PASS: ~a~%" name))
      (begin
        (set! *tests-failed* (+ *tests-failed* 1))
        (printf "  FAIL: ~a~%    expected: ~s~%    actual:   ~s~%" name expected actual))))

(define (test-true name actual)
  (test name #t (and actual #t)))

(define (test-false name actual)
  (test name #f actual))

(define (test-pred name pred actual)
  (set! *tests-run* (+ *tests-run* 1))
  (if (pred actual)
      (begin
        (set! *tests-passed* (+ *tests-passed* 1))
        (printf "  PASS: ~a~%" name))
      (begin
        (set! *tests-failed* (+ *tests-failed* 1))
        (printf "  FAIL: ~a~%    value: ~s did not satisfy predicate~%" name actual))))

(define (test-error name thunk)
  (set! *tests-run* (+ *tests-run* 1))
  (guard (exn
    [#t (begin
          (set! *tests-passed* (+ *tests-passed* 1))
          (printf "  PASS: ~a (error caught)~%" name))])
    (thunk)
    (set! *tests-failed* (+ *tests-failed* 1))
    (printf "  FAIL: ~a (expected error, got none)~%" name)))

;; ============================================================
;; Display Module
;; ============================================================

(printf "~%=== Display Module ===~%")

;; Display mode
(test "default display mode is vt100" 'vt100 *display-mode*)
(display-mode! 'html)
(test "display-mode! changes mode" 'html *display-mode*)
(display-mode! 'vt100)
(test "restore display mode to vt100" 'vt100 *display-mode*)
(test-error "invalid display mode rejected"
            (lambda () (display-mode! 'invalid)))

;; Themes
(test "default theme is phosphor" 'phosphor *theme*)
(test-pred "theme-color fg is hex string"
           string? (theme-color 'fg))
(test "phosphor fg is green" "#33ff33" (theme-color 'fg))
(test "phosphor bg is near-black" "#0a0a0a" (theme-color 'bg))

(theme! 'reading-lamp)
(test "theme changed to reading-lamp" 'reading-lamp *theme*)
(test "reading-lamp fg is sepia" "#3d3929" (theme-color 'fg))

(theme! 'midnight)
(test "theme changed to midnight" 'midnight *theme*)
(test "midnight accent is cyan" "#00d4ff" (theme-color 'accent))

(theme! 'phosphor)  ; restore

;; VT100 codes
(test-pred "vt100-bold is string" string? vt100-bold)
(test-pred "vt100-normal is string" string? vt100-normal)
(test-pred "vt100-red is string" string? vt100-red)
(test-pred "vt100-green is string" string? vt100-green)
(test-pred "vt100-clear is string" string? vt100-clear)
(test-pred "vt100-home is string" string? vt100-home)

;; Terminal dimensions (fallback values in non-tty)
(test-pred "terminal-width returns integer"
           integer? (terminal-width))
(test-pred "terminal-height returns integer"
           integer? (terminal-height))

;; Sparklines
(test "sparkline empty" "" (sparkline '()))
(test-pred "sparkline single value"
           string? (sparkline '(0.5)))
(test-pred "sparkline multiple values"
           (lambda (s) (= (string-length s) 5))
           (sparkline '(0.0 0.25 0.5 0.75 1.0)))
(test "sparkline all zeros"
      (make-string 3 #\space)
      (sparkline '(0.0 0.0 0.0)))

;; HTML rendering
(let ((html (render-html "Test" "<p>Hello</p>")))
  (test-pred "render-html produces string" string? html)
  (test-true "render-html contains DOCTYPE"
             (string-contains html "<!DOCTYPE html>"))
  (test-true "render-html contains title"
             (string-contains html "Test"))
  (test-true "render-html contains body"
             (string-contains html "<p>Hello</p>"))
  (test-true "render-html contains theme colors"
             (string-contains html "#33ff33")))

;; ============================================================
;; EDT Module
;; ============================================================

(printf "~%=== EDT Module ===~%")

;; QMK prefix
(test "qmk-prefix value" "#;QMK " qmk-prefix)

;; GOLD state
(test "gold initially inactive" #f *edt-gold-active*)
(edt-gold)
(test "edt-gold activates gold" #t *edt-gold-active*)
(edt-reset)
(test "edt-reset deactivates gold" #f *edt-gold-active*)

;; Editor hook
(test "edt-editor initially #f" #f *edt-editor*)

;; QMK dispatch for non-QMK input
(test-false "qmk-dispatch rejects normal text"
            (qmk-dispatch "hello world"))
(test-false "qmk-dispatch rejects empty string"
            (qmk-dispatch ""))

;; QMK dispatch with QMK prefix (gold command)
(set! *edt-gold-active* #f)
(test-true "qmk-dispatch handles QMK command"
           (qmk-dispatch "#;QMK (gold)"))
(test "gold activated by QMK dispatch" #t *edt-gold-active*)
(edt-reset)

;; EDT key dispatch without editor (should print message, not crash)
(let ((output (with-output-to-string (lambda () (edt 'page-down)))))
  (test-true "edt outputs no-editor message"
             (string-contains output "no editor active")))

;; EDT with mock editor
(let ((commands-received '()))
  (set! *edt-editor*
    `((help . ,(lambda () (set! commands-received (cons 'help commands-received))))
      (page-down . ,(lambda () (set! commands-received (cons 'page-down commands-received))))
      (find-next . ,(lambda () (set! commands-received (cons 'find-next commands-received))))))
  (edt 'help)
  (test "edt dispatches help" '(help) commands-received)
  (edt 'page-down)
  (test "edt dispatches page-down" '(page-down help) commands-received)
  ;; Gold prefix command
  (edt-gold)
  (edt 'fndnxt)
  ;; Gold+fndnxt = find (not find-next)
  ;; The mock editor doesn't have 'find, so it should print message
  (set! *edt-editor* #f))

;; ============================================================
;; Info Module
;; ============================================================

(printf "~%=== Info Module ===~%")

;; Initial state
(test "info-node starts at top" '(top) *info-node*)
(test-pred "info-history is list" list? *info-history*)

;; Info? function
(let ((output (with-output-to-string (lambda () (info?)))))
  (test-true "info? shows current location"
             (string-contains output "Current:")))

;; Info index output
(let ((output (with-output-to-string (lambda () (info-index)))))
  (test-true "info-index shows header"
             (string-contains output "Documentation Index"))
  (test-true "info-index shows architecture"
             (string-contains output "architecture"))
  (test-true "info-index shows vault"
             (string-contains output "vault"))
  (test-true "info-index shows crypto"
             (string-contains output "crypto")))

;; Navigate to topic
(let ((output (with-output-to-string (lambda () (info 'architecture)))))
  (test-true "info architecture shows title"
             (string-contains output "System Architecture"))
  (test-true "info architecture shows subtopics"
             (or (string-contains output "overview")
                 (string-contains output "replication"))))

;; Info-up
(info-up)
;; Should go back up

;; Info-next placeholder
(let ((output (with-output-to-string (lambda () (info-next)))))
  (test-true "info-next shows not-implemented"
             (string-contains output "Not yet")))

;; ============================================================
;; Inspector Module
;; ============================================================

(printf "~%=== Inspector Module ===~%")

;; State
(test "inspector initially disabled" #f *inspector-enabled*)
(test "inspector-current initially #f" #f *inspector-current*)
(test-pred "inspector-stack is list" list? *inspector-stack*)
(test-pred "inspector-bookmarks is list" list? *inspector-bookmarks*)
(test-pred "call-stack is list" list? *call-stack*)

;; Install inspector
(install-inspector!)
(test "inspector enabled after install" #t *inspector-enabled*)
(set! *inspector-enabled* #f)  ; don't leave it on

;; Call stack tracking
(clear-stack!)
(test "clear-stack! empties stack" '() *call-stack*)
(push-frame! 'test-func '(1 2 3) #f)
(test "push-frame! adds to stack" 1 (length *call-stack*))
(push-frame! 'test-func2 '(a b) #f)
(test "second push increases stack" 2 (length *call-stack*))
(pop-frame!)
(test "pop-frame! removes from stack" 1 (length *call-stack*))
(clear-stack!)

;; Describe various types
(let ((output (with-output-to-string (lambda () (describe 42)))))
  (test-true "describe number shows type"
             (string-contains output "integer"))
  (test-true "describe number shows value"
             (string-contains output "42")))

(let ((output (with-output-to-string (lambda () (describe "hello")))))
  (test-true "describe string shows type"
             (string-contains output "string"))
  (test-true "describe string shows value"
             (string-contains output "hello")))

(let ((output (with-output-to-string (lambda () (describe '(a b c))))))
  (test-true "describe list shows pair type"
             (string-contains output "pair"))
  (test-true "describe list shows car"
             (string-contains output "car")))

(let ((output (with-output-to-string (lambda () (describe '#(1 2 3))))))
  (test-true "describe vector shows type"
             (string-contains output "vector"))
  (test-true "describe vector shows length"
             (string-contains output "3")))

(let ((output (with-output-to-string (lambda () (describe #t)))))
  (test-true "describe boolean shows type"
             (string-contains output "boolean")))

(let ((output (with-output-to-string (lambda () (describe 'foo)))))
  (test-true "describe symbol shows type"
             (string-contains output "symbol"))
  (test-true "describe symbol shows value"
             (string-contains output "foo")))

;; Slots
(test "slots of pair" 2 (length (slots '(a . b))))
(test "slots of vector" 3 (length (slots '#(1 2 3))))
(test "slots of empty list" '() (slots '()))

;; Slot-ref
(test "slot-ref pair car" 'a (slot-ref '(a . b) 0))
(test "slot-ref pair cdr" 'b (slot-ref '(a . b) 1))
(test "slot-ref vector" 2 (slot-ref '#(1 2 3) 1))
(test "slot-ref string" #\e (slot-ref "hello" 1))

;; Inspector navigation
(let ((result (inspect '(foo bar baz))))
  (test-true "inspect returns object" (pair? result))
  (test-true "inspector-current set" (pair? *inspector-current*)))

(inspector-descend 0)
(test "after descend, current is car" 'foo *inspector-current*)
(test "stack has one entry" 1 (length *inspector-stack*))

(inspector-up)
(test-true "after up, back to list" (pair? *inspector-current*))
(test "stack empty after up" 0 (length *inspector-stack*))

;; Bookmark
(inspector-bookmark)
(test "bookmark added" 1 (length *inspector-bookmarks*))

;; Inspector history output
(let ((output (with-output-to-string (lambda () (inspector-history)))))
  (test-true "inspector-history shows output"
             (string-contains output "History")))

;; Inspector type output
(let ((output (with-output-to-string (lambda () (inspector-type)))))
  (test-true "inspector-type shows type"
             (string-contains output "Type")))

;; Restarts
(define-restart 'test-restart "Test restart" (lambda () 'restarted))
(test-pred "available-restarts has entries"
           pair? (available-restarts))
(test "invoke-restart works" 'restarted (invoke-restart 'test-restart))

;; Pretty print
(let ((output (with-output-to-string (lambda () (pprint '(a b c))))))
  (test-true "pprint produces output"
             (> (string-length output) 0)))

;; ============================================================
;; Results
;; ============================================================

(printf "~%=== Results ===~%")
(printf "Tests run:    ~a~%" *tests-run*)
(printf "Tests passed: ~a~%" *tests-passed*)
(printf "Tests failed: ~a~%" *tests-failed*)
(when (> *tests-failed* 0)
  (printf "~%*** FAILURES DETECTED ***~%"))
(printf "~%")
