#!/usr/bin/env chez --script
;;; test-portal.sps - Tests for portal (session lifecycle)

(import (rnrs)
        (only (chezscheme) printf format void)
        (cyberspace portal)
        (cyberspace os))

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
             (printf "  FAIL: ~a (expected ~a, got ~a)~%" msg expected actual))))

(printf "~%=== Portal Tests ===~%~%")

;; Test 1: format-duration seconds
(printf "--- Format Duration ---~%")
(assert-equal "seconds only" "30s" (format-duration 30))
(assert-equal "minutes + seconds" "5m 30s" (format-duration 330))
(assert-equal "hours + minutes" "2h 30m" (format-duration 9000))
(assert-equal "days + hours" "1d 12h" (format-duration 129600))
(assert-equal "zero seconds" "0s" (format-duration 0))

;; Test 2: format-bytes
(printf "--- Format Bytes ---~%")
(assert-equal "bytes" "512B" (format-bytes 512))
(assert-equal "kilobytes" "10K" (format-bytes 10240))
(assert-equal "megabytes" "1.5M" (format-bytes 1572864))
(assert-equal "gigabytes" "2.0G" (format-bytes 2147483648))

;; Test 3: session-stat-init! initializes all stats
(printf "--- Session Statistics ---~%")
(session-stats-reset!)
(session-stat-init!)
(assert-true "boot-time is set" (> (session-stat 'boot-time) 0))
(assert-equal "commands starts at 0" 0 (session-stat 'commands))
(assert-equal "reads starts at 0" 0 (session-stat 'reads))
(assert-equal "writes starts at 0" 0 (session-stat 'writes))
(assert-equal "hashes starts at 0" 0 (session-stat 'hashes))
(assert-equal "signs starts at 0" 0 (session-stat 'signs))
(assert-equal "gossip-exchanges starts at 0" 0 (session-stat 'gossip-exchanges))
(assert-equal "verify-fails starts at 0" 0 (session-stat 'verify-fails))

;; Test 4: session-uptime
(printf "--- Session Uptime ---~%")
(let ((up (session-uptime)))
  (assert-true "uptime is non-negative" (>= up 0))
  (assert-true "uptime is small (just started)" (< up 5)))

;; Test 5: session-summary generates list of strings
(printf "--- Session Summary ---~%")
(let ((summary (session-summary)))
  (assert-true "summary is a list" (list? summary))
  (assert-true "summary has at least uptime" (> (length summary) 0))
  (assert-true "first element is string (uptime)" (string? (car summary))))

;; Test 6: session-summary with some stats
(session-stat! 'reads 5)
(session-stat! 'writes 1)
(session-stat! 'hashes 10)
(let ((summary (session-summary)))
  (assert-true "summary includes reads" (exists (lambda (s) (string=? s "5 reads")) summary))
  (assert-true "summary includes write (singular)" (exists (lambda (s) (string=? s "1 write")) summary))
  (assert-true "summary includes hashes" (exists (lambda (s) (string=? s "10 hashes")) summary)))

;; Test 7: count-vault-items (may or may not have vault dir)
(printf "--- Vault Helpers ---~%")
(let ((count (count-vault-items "nonexistent")))
  (assert-equal "nonexistent dir returns 0" 0 count))

;; Test 8: audit-load-entries-raw (may or may not have audit dir)
(let ((entries (audit-load-entries-raw)))
  (assert-true "returns a list" (list? entries)))

;; Test 9: install-signal-handlers! (no-op in Chez)
(printf "--- Signal Handlers ---~%")
(assert-true "install-signal-handlers! doesn't error"
  (begin (install-signal-handlers!) #t))

;; Test 10: format-stat helpers
(printf "--- Format Stat ---~%")
(session-stats-reset!)
(session-stat-init!)
(session-stat! 'queries 3)
(let ((summary (session-summary)))
  (assert-true "queries uses irregular plural"
    (exists (lambda (s) (string=? s "3 queries")) summary)))

(session-stats-reset!)
(session-stat-init!)
(session-stat! 'queries 1)
(let ((summary (session-summary)))
  (assert-true "1 query uses singular"
    (exists (lambda (s) (string=? s "1 query")) summary)))

;; Summary
(printf "~%=== Portal: ~a passed, ~a failed ===~%~%" *pass* *fail*)
(when (> *fail* 0) (exit 1))
