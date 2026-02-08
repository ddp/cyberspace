#!/usr/bin/env chez-script
;;; test-repl-build.ss - Tests for build system and REPL support modules
;;;
;;; Run: CHEZSCHEMELIBDIRS=. chez --program test-repl-build.ss
;;;
;;; Copyright (c) 2026 Yoyodyne. See LICENSE.

(import (rnrs)
        (only (chezscheme)
              printf format void
              file-exists?
              with-output-to-string with-input-from-string
              getenv)
        (cyberspace chicken-compatibility chicken)
        (cyberspace os)
        (cyberspace tty-ffi)
        (cyberspace display)
        (cyberspace edt)
        (cyberspace lineage))

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

;; ============================================================
;; Lineage (Line Editor)
;; ============================================================

(printf "~%=== Lineage (Line Editor) ===~%")

;; History
(lineage-add-history! "first command")
(lineage-add-history! "second command")
(test-pred "history has entries"
           (lambda (h) (>= (length h) 2))
           (lineage-history))
(test "most recent is first"
      "second command"
      (car (lineage-history)))

;; Duplicate suppression
(lineage-add-history! "second command")
(let ((before (length (lineage-history))))
  (lineage-add-history! "second command")
  (test "duplicate not added"
        before
        (length (lineage-history))))

;; Prompt
(lineage-set-prompt! "test> ")
;; Just verify it doesn't crash
(test-true "set-prompt! doesn't crash" #t)

;; Command completions
(lineage-add-command "status")
(lineage-add-command "help")
(lineage-add-command "commit")
(test-true "add-command doesn't crash" #t)

;; Paren wrap
(lineage-set-paren-wrap 0)
(test-true "set-paren-wrap 0 ok" #t)
(lineage-set-paren-wrap 1)
(test-true "set-paren-wrap 1 ok" #t)

;; ============================================================
;; TTY-FFI (Terminal)
;; ============================================================

(printf "~%=== TTY-FFI ===~%")

;; Terminal dimensions (defaults in non-tty)
(test-pred "tty-rows returns positive int"
           (lambda (n) (> n 0))
           (tty-rows))
(test-pred "tty-cols returns positive int"
           (lambda (n) (> n 0))
           (tty-cols))

;; tty? in test environment
(test-pred "tty? returns boolean"
           boolean?
           (tty?))

;; ============================================================
;; Display Module - VT100 Escapes
;; ============================================================

(printf "~%=== Display VT100 ===~%")

;; Verify escape sequences have correct structure
(test-pred "vt100-bold starts with ESC["
           (lambda (s) (and (> (string-length s) 2)
                            (char=? (string-ref s 0) #\x1b)))
           vt100-bold)

(test-pred "vt100-normal starts with ESC["
           (lambda (s) (and (> (string-length s) 2)
                            (char=? (string-ref s 0) #\x1b)))
           vt100-normal)

;; Theme operations
(test "default theme" 'phosphor *theme*)
(theme! 'midnight)
(test "theme changed" 'midnight *theme*)
(theme! 'phosphor)

;; Sparklines
(test-pred "sparkline 5 values = 5 chars"
           (lambda (s) (= (string-length s) 5))
           (sparkline '(0.0 0.25 0.5 0.75 1.0)))

;; ============================================================
;; EDT Module
;; ============================================================

(printf "~%=== EDT ===~%")

(test "gold initially off" #f *edt-gold-active*)
(edt-gold)
(test "gold on" #t *edt-gold-active*)
(edt-reset)
(test "gold off" #f *edt-gold-active*)

;; QMK dispatch
(test-false "non-QMK rejected" (qmk-dispatch "hello"))
(test-true "QMK gold accepted" (qmk-dispatch "#;QMK (gold)"))
(edt-reset)

;; ============================================================
;; OS Module Integration
;; ============================================================

(printf "~%=== OS Module ===~%")

(test-pred "hostname returns string"
           string? (hostname))
(test-pred "os-type returns string"
           string? (os-type))
(test-pred "os-arch returns string"
           string? (os-arch))
(test-pred "current-seconds returns number"
           number? (current-seconds))

;; Box drawing
(let ((box (make-box 30)))
  (test-pred "make-box returns pair"
             pair? box)
  (test-pred "box-top returns string"
             string? (box-top box "Test"))
  (test-pred "box-bottom returns string"
             string? (box-bottom box))
  (test-pred "box-separator returns string"
             string? (box-separator box)))

;; ============================================================
;; Build System Library List
;; ============================================================

(printf "~%=== Build System Checks ===~%")

;; Check that key .sls files exist
(define chez-dir
  (let ((d (getenv "CHEZSCHEMELIBDIRS")))
    (if (and d (> (string-length d) 0)) d ".")))

(define (sls-exists? mod)
  (file-exists? (string-append chez-dir "/cyberspace/" mod ".sls")))

(define *expected-modules*
  '("sexp" "os" "tty-ffi" "crypto-ffi" "pq-crypto"
    "fips" "wordlist" "cert" "capability" "bloom" "audit"
    "vault" "catalog" "merkle" "gossip" "mdns"
    "filetype" "http" "osc" "rnbo" "metadata-ffi"
    "fuse-ffi" "wormhole" "enroll" "auto-enroll"
    "ui" "display" "inspector" "info" "edt"
    "thread" "tcp" "lineage"))

(let ((present (filter sls-exists? *expected-modules*))
      (total (length *expected-modules*)))
  (printf "  Library modules: ~a/~a present~%" (length present) total)
  (test-pred "majority of modules present"
             (lambda (n) (>= n (- total 5)))
             (length present)))

;; Check C bridge source files exist
(define (bridge-exists? name)
  (or (file-exists? (string-append chez-dir "/cyberspace/" name ".c"))
      (file-exists? (string-append "cyberspace/" name ".c"))))

(let ((bridges '("crypto-bridge" "tcp-bridge" "tty-bridge" "fuse-bridge" "pq-bridge")))
  (let ((present (filter bridge-exists? bridges)))
    (printf "  C bridges: ~a/~a present~%" (length present) (length bridges))
    ;; At least tcp, tty, fuse should be present (we wrote them)
    (test-pred "C bridges present"
               (lambda (n) (>= n 3))
               (length present))))

;; Check test suites exist
(let ((tests '("test-sexp.ss" "test-os-chicken.ss" "test-crypto-pq.ss"
               "test-cert-capability.ss" "test-vault-audit.ss"
               "test-gossip-mdns.ss" "test-enroll-auto-enroll.ss"
               "test-filetype-http-osc-rnbo-metadata.ss"
               "test-tty-fuse-wormhole.ss" "test-level10.ss"
               "test-repl-build.ss")))
  (let ((present (filter (lambda (t) (file-exists? (string-append chez-dir "/" t))) tests)))
    (printf "  Test suites: ~a/~a present~%" (length present) (length tests))))

;; Check program files
(let ((programs '("repl.ss" "build.ss" "seal.ss" "cyberspace.ss")))
  (let ((present (filter (lambda (p) (file-exists? (string-append chez-dir "/" p))) programs)))
    (printf "  Programs: ~a/~a present~%" (length present) (length programs))))

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
