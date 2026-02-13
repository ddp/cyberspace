#!/usr/bin/env chez --script
;;; test-join.sps - Test the join-realm functionality
;;;
;;; Tests the gossip-based federation join with local loopback.
;;; Uses reset-enrollment-state! between tests to handle shared state.
;;;
;;; Ported from Chicken's test-join.scm.
;;; Changes: SRFI-18 threads -> fork-thread/sleep, handle-exceptions -> guard,
;;;          Chicken imports -> R6RS libraries, #!key -> get-key convention.
;;; Note: Uses high port numbers (18700+) to avoid conflicts.

(import (rnrs)
        (only (chezscheme) printf format fork-thread sleep make-time
              system file-directory? display-condition)
        (cyberspace auto-enroll)
        (cyberspace crypto-ffi))

;; Initialize libsodium
(sodium-init)

;; Create a temporary .vault in CWD for tests (cleaned up at end)
(define *vault-existed* (file-directory? ".vault"))
(unless *vault-existed*
  (system "mkdir -p .vault/certs .vault/keystore"))

;; ============================================================
;; Test Framework
;; ============================================================

(define *tests-run* 0)
(define *tests-passed* 0)
(define *tests-failed* '())

(define (test name thunk)
  (set! *tests-run* (+ *tests-run* 1))
  (guard (exn
    [#t
     (printf "FAIL: ~a~n" name)
     (printf "      ")
     (display-condition exn)
     (newline)
     (set! *tests-failed* (cons name *tests-failed*))])
    (let ((result (thunk)))
      (if result
          (begin
            (printf "PASS: ~a~n" name)
            (set! *tests-passed* (+ *tests-passed* 1)))
          (begin
            (printf "FAIL: ~a (returned #f)~n" name)
            (set! *tests-failed* (cons name *tests-failed*)))))))

;; Short delay for listener threads to start
(define (brief-pause)
  (sleep (make-time 'time-duration 500000000 0)))  ; 500ms

;; Ensure listener is stopped even on error
(define (with-listener thunk)
  (dynamic-wind
    (lambda () #f)
    thunk
    (lambda ()
      (guard (exn [#t #f])
        (stop-join-listener)))))

;; ============================================================
;; Join Tests
;; ============================================================

(printf "~n=== Join Realm Tests ===~n~n")

(define fluffy-keypair (ed25519-keypair))

;; Test 1: Founding a realm
(printf "--- Founding a Realm ---~n")
(reset-enrollment-state!)

(with-listener
  (lambda ()
    (test "start-join-listener founds realm"
      (lambda ()
        (let ((result (start-join-listener 'fluffy 'port: 18701 'keypair: fluffy-keypair)))
          (and (pair? result)
               (eq? (car result) 'join-listener-started)))))

    (test "founding node has master role"
      (lambda ()
        (let ((status (realm-status)))
          (and (eq? 'fluffy (cdr (assq 'master status)))
               (eq? 'master (cdr (assq 'role status)))))))

    (test "founding node has 1 member"
      (lambda ()
        (= 1 (cdr (assq 'member-count (realm-status))))))))

;; Test 2: Join process
(printf "~n--- Join Process ---~n")
(reset-enrollment-state!)

(with-listener
  (lambda ()
    (start-join-listener 'fluffy 'port: 18702 'keypair: fluffy-keypair)
    (brief-pause)

    (test "join-realm successfully joins"
      (lambda ()
        (let ((result (join-realm 'starlight "127.0.0.1" 'port: 18702)))
          (eq? 'joined (cdr (assq 'status result))))))))

;; Test 3: Join result contents
(printf "~n--- Join Result Contents ---~n")
(reset-enrollment-state!)

(with-listener
  (lambda ()
    (start-join-listener 'fluffy 'port: 18703 'keypair: fluffy-keypair)
    (brief-pause)

    (let ((join-result (join-realm 'starlight "127.0.0.1" 'port: 18703)))

      (test "join result includes certificate"
        (lambda ()
          (and (pair? join-result)
               (assq 'certificate join-result)
               (pair? (cdr (assq 'certificate join-result))))))

      (test "join result includes keypair"
        (lambda ()
          (and (pair? join-result)
               (assq 'pubkey join-result)
               (assq 'privkey join-result))))

      (test "join result includes sponsor"
        (lambda ()
          (and (pair? join-result)
               (eq? 'fluffy (cdr (assq 'sponsor join-result))))))

      (test "joined node has member role"
        (lambda ()
          (eq? 'member (cdr (assq 'role (realm-status)))))))))

;; Test 4: Failed connection
(printf "~n--- Error Handling ---~n")
(reset-enrollment-state!)

(test "join-realm fails when no listener"
  (lambda ()
    (let ((result (join-realm 'orphan "127.0.0.1" 'port: 19999)))
      (eq? 'error (cdr (assq 'status result))))))

;; ============================================================
;; Summary
;; ============================================================

(printf "~n=== Results ===~n")
(printf "Passed: ~a/~a~n" *tests-passed* *tests-run*)
(when (> (length *tests-failed*) 0)
  (printf "Failed:~n")
  (for-each (lambda (n) (printf "  - ~a~n" n)) (reverse *tests-failed*)))
(newline)

;; Clean up temp .vault if we created it
(unless *vault-existed*
  (system "rm -rf .vault"))

;; Kill any orphan dns-sd processes from bonjour-register
(system "pkill -f 'dns-sd.*_cyberspace' 2>/dev/null")

;; Exit with error code if tests failed
(when (> (length *tests-failed*) 0)
  (exit 1))
