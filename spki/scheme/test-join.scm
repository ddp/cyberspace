#!/usr/bin/env csi -s
;;; test-join.scm - Test the join-realm functionality
;;;
;;; Tests the gossip-based federation join with local loopback.
;;; Uses reset-enrollment-state! between tests to handle shared state.

(import scheme
        (chicken base)
        (chicken format)
        (chicken condition)
        (chicken time)
        srfi-18     ; threads
        auto-enroll
        crypto-ffi)

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

;; ============================================================
;; Join Tests
;; ============================================================

(printf "~n=== Join Realm Tests ===~n~n")

;; Test 1: Founding a realm
(printf "--- Founding a Realm ---~n")
(reset-enrollment-state!)
(define fluffy-keypair (ed25519-keypair))

(test "start-join-listener founds realm"
  (lambda ()
    (let ((result (start-join-listener 'fluffy port: 17656 keypair: fluffy-keypair)))
      (and (pair? result)
           (eq? (car result) 'join-listener-started)))))

(test "founding node has master role"
  (lambda ()
    (let ((status (realm-status)))
      (and (eq? 'fluffy (cdr (assq 'master status)))
           (eq? 'master (cdr (assq 'role status)))))))

(test "founding node has 1 member"
  (lambda ()
    (= 1 (cdr (assq 'member-count (realm-status))))))

(stop-join-listener)

;; Test 2: Join process
(printf "~n--- Join Process ---~n")
(reset-enrollment-state!)
(start-join-listener 'fluffy port: 17657 keypair: fluffy-keypair)
(thread-sleep! 0.3)

(test "join-realm successfully joins"
  (lambda ()
    (let ((result (join-realm 'starlight "127.0.0.1" port: 17657)))
      (eq? 'joined (cdr (assq 'status result))))))

(stop-join-listener)

;; Test 3: Join result contents
(printf "~n--- Join Result Contents ---~n")
(reset-enrollment-state!)
(start-join-listener 'fluffy port: 17658 keypair: fluffy-keypair)
(thread-sleep! 0.3)

(define join-result (join-realm 'starlight "127.0.0.1" port: 17658))

(test "join result includes certificate"
  (lambda ()
    (and (assq 'certificate join-result)
         (pair? (cdr (assq 'certificate join-result))))))

(test "join result includes keypair"
  (lambda ()
    (and (assq 'pubkey join-result)
         (assq 'privkey join-result))))

(test "join result includes sponsor"
  (lambda ()
    (eq? 'fluffy (cdr (assq 'sponsor join-result)))))

(test "joined node auto-starts listener"
  (lambda ()
    ;; After join, node should be listening (check role)
    (eq? 'member (cdr (assq 'role (realm-status))))))

(stop-join-listener)

;; Test 4: Multi-node chain (A sponsors B, B sponsors C)
(printf "~n--- Multi-Node Chain ---~n")
(reset-enrollment-state!)

;; Fluffy starts realm
(start-join-listener 'fluffy port: 17659 keypair: fluffy-keypair)
(thread-sleep! 0.3)

;; Starlight joins Fluffy
(define starlight-result (join-realm 'starlight "127.0.0.1" port: 17659))
;; Now starlight is listening on port 7656 (default)

(test "starlight joined fluffy"
  (lambda ()
    (eq? 'joined (cdr (assq 'status starlight-result)))))

;; Moonbeam joins Starlight (any member can sponsor!)
(thread-sleep! 0.3)
(define moonbeam-result (join-realm 'moonbeam "127.0.0.1" port: 7656))

(test "moonbeam joined via starlight (any member sponsors)"
  (lambda ()
    (eq? 'joined (cdr (assq 'status moonbeam-result)))))

(test "moonbeam's sponsor is starlight"
  (lambda ()
    (eq? 'starlight (cdr (assq 'sponsor moonbeam-result)))))

(stop-join-listener)

;; Test 5: Failed connection
(printf "~n--- Error Handling ---~n")
(reset-enrollment-state!)

(test "join-realm fails when no listener"
  (lambda ()
    (let ((result (join-realm 'orphan "127.0.0.1" port: 19999)))
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

;; Exit with error code if tests failed
(when (> (length *tests-failed*) 0)
  (exit 1))
