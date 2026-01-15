;;; SPKI Scheme - FIPS 140-2 Style Self-Tests
;;;
;;; Known-Answer Tests (KATs) to verify crypto primitives on startup.
;;; If any test fails, Cyberspace refuses to start.
;;;
;;; This is not actual FIPS certification (which requires hardware modules
;;; and extensive documentation), but follows the spirit: verify the
;;; cryptographic primitives work correctly before trusting them.
;;;
;;; Test vectors from official sources:
;;;   - SHA-256/512: NIST FIPS 180-4 examples
;;;   - Ed25519: RFC 8032 test vectors
;;;

(module fips
  (;; Self-test entry point
   fips-self-test
   ;; Individual tests (for diagnostics)
   test-sha256
   test-sha512
   test-ed25519
   test-randomness
   ;; Results
   fips-status)

  (import scheme
          (chicken base)
          (chicken format)
          (chicken blob)
          srfi-4
          crypto-ffi)

  ;;; ============================================================
  ;;; Helper: hex string to blob
  ;;; ============================================================

  (define (hex-char->int c)
    (cond ((and (char>=? c #\0) (char<=? c #\9))
           (- (char->integer c) (char->integer #\0)))
          ((and (char>=? c #\a) (char<=? c #\f))
           (+ 10 (- (char->integer c) (char->integer #\a))))
          ((and (char>=? c #\A) (char<=? c #\F))
           (+ 10 (- (char->integer c) (char->integer #\A))))
          (else (error "Invalid hex character" c))))

  (define (hex->blob hex-str)
    "Convert hex string to blob"
    (let* ((len (quotient (string-length hex-str) 2))
           (vec (make-u8vector len)))
      (do ((i 0 (+ i 1)))
          ((= i len) (u8vector->blob vec))
        (let ((hi (hex-char->int (string-ref hex-str (* i 2))))
              (lo (hex-char->int (string-ref hex-str (+ (* i 2) 1)))))
          (u8vector-set! vec i (+ (* hi 16) lo))))))

  (define (blob->hex blob)
    "Convert blob to hex string"
    (let* ((vec (blob->u8vector blob))
           (len (u8vector-length vec)))
      (let loop ((i 0) (acc '()))
        (if (= i len)
            (apply string-append (reverse acc))
            (loop (+ i 1)
                  (cons (sprintf "~2,'0x" (u8vector-ref vec i)) acc))))))

  (define (blob=? a b)
    "Compare two blobs for equality"
    (let ((av (blob->u8vector a))
          (bv (blob->u8vector b)))
      (and (= (u8vector-length av) (u8vector-length bv))
           (let loop ((i 0))
             (or (= i (u8vector-length av))
                 (and (= (u8vector-ref av i) (u8vector-ref bv i))
                      (loop (+ i 1))))))))

  ;;; ============================================================
  ;;; SHA-256 KAT (NIST FIPS 180-4)
  ;;; ============================================================

  ;; Test vector: "abc"
  ;; Expected: ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad

  (define *sha256-test-input* "abc")
  (define *sha256-test-expected*
    "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")

  (define (test-sha256)
    "KAT for SHA-256. Returns #t on pass, #f on fail."
    (let* ((hash (sha256-hash *sha256-test-input*))
           (expected (hex->blob *sha256-test-expected*)))
      (blob=? hash expected)))

  ;;; ============================================================
  ;;; SHA-512 KAT (NIST FIPS 180-4)
  ;;; ============================================================

  ;; Test vector: "abc"
  ;; Expected: ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a
  ;;           2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f

  (define *sha512-test-input* "abc")
  (define *sha512-test-expected*
    "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f")

  (define (test-sha512)
    "KAT for SHA-512. Returns #t on pass, #f on fail."
    (let* ((hash (sha512-hash *sha512-test-input*))
           (expected (hex->blob *sha512-test-expected*)))
      (blob=? hash expected)))

  ;;; ============================================================
  ;;; Ed25519 KAT (RFC 8032 Test Vector 1)
  ;;; ============================================================

  ;; RFC 8032 Section 7.1 - TEST 1
  ;; Secret key (seed): 9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60
  ;; Public key: d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a
  ;; Message: (empty)
  ;; Signature: e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b

  (define *ed25519-secret-seed*
    "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60")
  (define *ed25519-public-key*
    "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a")
  (define *ed25519-message* "")  ; empty message
  (define *ed25519-signature*
    "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b")

  (define (test-ed25519)
    "KAT for Ed25519. Returns #t on pass, #f on fail."
    ;; Note: Ed25519 secret key in libsodium is seed || public_key (64 bytes)
    ;; RFC 8032 gives 32-byte seed, we need to expand it
    (let* ((seed (hex->blob *ed25519-secret-seed*))
           (expected-pk (hex->blob *ed25519-public-key*))
           (expected-sig (hex->blob *ed25519-signature*))
           (message (string->blob *ed25519-message*))
           ;; Build the 64-byte secret key: seed || public_key
           (sk (make-blob 64))
           (sk-vec (blob->u8vector/shared sk))
           (seed-vec (blob->u8vector seed))
           (pk-vec (blob->u8vector expected-pk)))
      ;; Copy seed to first 32 bytes
      (do ((i 0 (+ i 1)))
          ((= i 32))
        (u8vector-set! sk-vec i (u8vector-ref seed-vec i)))
      ;; Copy public key to last 32 bytes
      (do ((i 0 (+ i 1)))
          ((= i 32))
        (u8vector-set! sk-vec (+ i 32) (u8vector-ref pk-vec i)))
      ;; Sign the message
      (let ((sig (ed25519-sign sk message)))
        ;; Verify signature matches expected
        (and (blob=? sig expected-sig)
             ;; Also verify the signature is valid
             (ed25519-verify expected-pk message sig)))))

  ;;; ============================================================
  ;;; Randomness Sanity Check
  ;;; ============================================================

  (define (test-randomness)
    "Basic randomness sanity check. Returns #t on pass, #f on fail.
     Verifies:
     1. random-bytes returns correct length
     2. Two 32-byte samples are different (overwhelmingly likely)
     3. Bytes are not all zeros"
    (let ((r1 (random-bytes 32))
          (r2 (random-bytes 32)))
      (and (= (blob-size r1) 32)
           (= (blob-size r2) 32)
           (not (blob=? r1 r2))
           ;; Check not all zeros
           (let ((v1 (blob->u8vector r1)))
             (let loop ((i 0) (sum 0))
               (if (= i 32)
                   (> sum 0)
                   (loop (+ i 1) (+ sum (u8vector-ref v1 i)))))))))

  ;;; ============================================================
  ;;; FIPS Self-Test Entry Point
  ;;; ============================================================

  (define *fips-status* 'untested)

  (define (fips-status)
    "Get FIPS self-test status: 'passed, 'failed, or 'untested"
    *fips-status*)

  (define (fips-self-test #!optional (verbose #f))
    "Run all FIPS self-tests. Returns #t if all pass, signals error if any fail.
     If verbose, prints test progress."
    (let ((tests `((sha256 . ,test-sha256)
                   (sha512 . ,test-sha512)
                   (ed25519 . ,test-ed25519)
                   (randomness . ,test-randomness)))
          (failed '()))
      (for-each
        (lambda (test)
          (let ((name (car test))
                (proc (cdr test)))
            (when verbose
              (printf "  FIPS ~a... " name)
              (flush-output))
            (let ((result (proc)))
              (when verbose
                (printf "~a~n" (if result "ok" "FAILED")))
              (unless result
                (set! failed (cons name failed))))))
        tests)
      (if (null? failed)
          (begin
            (set! *fips-status* 'passed)
            #t)
          (begin
            (set! *fips-status* 'failed)
            (error (sprintf "FIPS self-test FAILED: ~a" (reverse failed)))))))

) ;; end module
