#!/usr/bin/env csi -s
;;; test-security.scm - Tests for security module
;;;
;;; Tests validity checking, ISO 8601 parsing, certificate status,
;;; revocation detection, and principal fingerprinting.

(import scheme
        (chicken base)
        (chicken format)
        (chicken condition)
        (chicken time)
        srfi-1
        crypto-ffi
        sexp
        cert
        security)

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
;; Test Fixtures
;; ============================================================

;; Generate keypair for tests
(define keypair (ed25519-keypair))
(define public-key (car keypair))
(define private-key (cadr keypair))

;; Create principals
(define issuer (make-key-principal public-key))
(define subject (make-key-principal public-key))

;; ============================================================
;; Tests
;; ============================================================

(printf "~n=== Security Module Tests ===~n~n")

;; --- ISO 8601 Parsing ---

(test "iso8601->seconds parses valid date"
  (lambda ()
    (let ((secs (iso8601->seconds "2025-01-01T00:00:00Z")))
      (and (number? secs) (> secs 0)))))

(test "iso8601->seconds parses date with time"
  (lambda ()
    (let ((s1 (iso8601->seconds "2025-06-15T12:30:00Z"))
          (s2 (iso8601->seconds "2025-06-15T00:00:00Z")))
      ;; 12:30 should be later than midnight
      (> s1 s2))))

(test "iso8601->seconds monotonic ordering"
  (lambda ()
    (let ((s1 (iso8601->seconds "2024-01-01T00:00:00Z"))
          (s2 (iso8601->seconds "2025-01-01T00:00:00Z"))
          (s3 (iso8601->seconds "2026-01-01T00:00:00Z")))
      (and (< s1 s2) (< s2 s3)))))

;; --- validity-expired? ---

(test "validity-expired? returns #f for future date"
  (lambda ()
    ;; A date far in the future should not be expired
    (let ((v (make-validity "2020-01-01T00:00:00Z" "2099-12-31T23:59:59Z")))
      (not (validity-expired? v)))))

(test "validity-expired? returns #t for past date"
  (lambda ()
    ;; A date in the past should be expired
    (let ((v (make-validity "2020-01-01T00:00:00Z" "2020-06-01T00:00:00Z")))
      (validity-expired? v))))

(test "validity-expired? handles no expiration"
  (lambda ()
    ;; No validity period means not expired
    (not (validity-expired? #f))))

;; --- cert-status ---

(test "cert-status returns valid for good cert"
  (lambda ()
    ;; Create a self-signed cert with future validity (epoch seconds)
    (let* ((tag (make-tag (sexp-atom "test")))
           (far-future (+ (current-seconds) (* 365 24 3600)))
           (validity (make-validity 1577836800 far-future))
           (c (create-cert issuer subject tag
                           validity: validity))
           (sc (sign-cert c private-key)))
      (eq? 'valid (cert-status sc public-key)))))

(test "cert-status returns invalid-signature for bad sig"
  (lambda ()
    ;; Create cert, sign with one key, verify with another
    (let* ((other-keypair (ed25519-keypair))
           (other-pubkey (car other-keypair))
           (tag (make-tag (sexp-atom "test")))
           (c (create-cert issuer subject tag))
           (sc (sign-cert c private-key)))
      ;; Verify with wrong key
      (eq? 'invalid-signature (cert-status sc other-pubkey)))))

(test "cert-status returns expired for past validity"
  (lambda ()
    (let* ((tag (make-tag (sexp-atom "test")))
           ;; Both dates in the past (epoch seconds)
           (validity (make-validity 1577836800 1590969600))
           (c (create-cert issuer subject tag
                           validity: validity))
           (sc (sign-cert c private-key)))
      (eq? 'expired (cert-status sc public-key)))))

(test "cert-status detects revocation"
  (lambda ()
    (let* ((tag (make-tag (sexp-atom "test")))
           (c (create-cert issuer subject tag))
           (sc (sign-cert c private-key))
           (fp (principal-fingerprint subject))
           (revocations (list `((fingerprint . ,fp)))))
      (eq? 'revoked (cert-status sc public-key revocations)))))

;; --- cert-revoked? ---

(test "cert-revoked? detects revoked cert"
  (lambda ()
    (let* ((fp "abcd:1234:5678:9abc")
           (revocations (list `((fingerprint . ,fp)))))
      (cert-revoked? fp revocations))))

(test "cert-revoked? returns #f for non-revoked"
  (lambda ()
    (let* ((fp "abcd:1234:5678:9abc")
           (revocations (list `((fingerprint . "other:fingerprint")))))
      (not (cert-revoked? fp revocations)))))

;; --- principal-fingerprint ---

(test "principal-fingerprint is consistent"
  (lambda ()
    (let ((fp1 (principal-fingerprint issuer))
          (fp2 (principal-fingerprint issuer)))
      (string=? fp1 fp2))))

(test "principal-fingerprint differs for different keys"
  (lambda ()
    (let* ((other-keypair (ed25519-keypair))
           (other-principal (make-key-principal (car other-keypair)))
           (fp1 (principal-fingerprint issuer))
           (fp2 (principal-fingerprint other-principal)))
      (not (string=? fp1 fp2)))))

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
