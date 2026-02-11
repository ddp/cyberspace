;;; Security Module Tests - Chez Scheme Port
;;; Tests validity checking, ISO 8601, cert status, revocation, fingerprints.

(import (rnrs)
        (only (chezscheme) printf format time-second current-time)
        (cyberspace chicken-compatibility blob)
        (cyberspace test)
        (cyberspace sexp)
        (cyberspace cert)
        (cyberspace security)
        (cyberspace crypto-ffi))

;; Initialize libsodium
(sodium-init)

;; Current time in epoch seconds
(define (current-seconds) (time-second (current-time)))

;; Test Fixtures
(define keypair (ed25519-keypair))
(define public-key (car keypair))
(define private-key (cadr keypair))
(define issuer (make-key-principal public-key))
(define subject (make-key-principal public-key))

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
    (let ((v (make-validity "2020-01-01T00:00:00Z" "2099-12-31T23:59:59Z")))
      (not (validity-expired? v)))))

(test "validity-expired? returns #t for past date"
  (lambda ()
    (let ((v (make-validity "2020-01-01T00:00:00Z" "2020-06-01T00:00:00Z")))
      (validity-expired? v))))

(test "validity-expired? handles no expiration"
  (lambda ()
    (not (validity-expired? #f))))

;; --- cert-status ---

(test "cert-status returns valid for good cert"
  (lambda ()
    (let* ((tag (make-tag (sexp-atom "test")))
           (far-future (+ (current-seconds) (* 365 24 3600)))
           (validity (make-validity 1577836800 far-future))
           (c (create-cert issuer subject tag
                           'validity: validity))
           (sc (sign-cert c private-key)))
      (eq? 'valid (cert-status sc public-key)))))

(test "cert-status returns invalid-signature for bad sig"
  (lambda ()
    (let* ((other-keypair (ed25519-keypair))
           (other-pubkey (car other-keypair))
           (tag (make-tag (sexp-atom "test")))
           (c (create-cert issuer subject tag))
           (sc (sign-cert c private-key)))
      (eq? 'invalid-signature (cert-status sc other-pubkey)))))

(test "cert-status returns expired for past validity"
  (lambda ()
    (let* ((tag (make-tag (sexp-atom "test")))
           (validity (make-validity 1577836800 1590969600))
           (c (create-cert issuer subject tag
                           'validity: validity))
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

(test-summary)
