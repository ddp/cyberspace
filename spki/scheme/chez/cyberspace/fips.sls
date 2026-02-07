;;; SPKI Scheme - FIPS 140-2 Style Self-Tests
;;; Library of Cyberspace - Chez Port
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

(library (cyberspace fips)
  (export
    ;; Self-test entry point
    fips-self-test
    ;; Individual tests (for diagnostics)
    test-sha256
    test-sha512
    test-ed25519
    test-randomness
    ;; FIPS 140-2 randomness tests (20,000 bits)
    fips-monobit-test
    fips-poker-test
    fips-runs-test
    fips-long-run-test
    ;; Results
    fips-status)

  (import (rnrs)
          (only (chezscheme) printf format void flush-output-port)
          (cyberspace chicken-compatibility blob)
          (cyberspace crypto-ffi))

  ;;; ============================================================
  ;;; Helper: hex string to bytevector
  ;;; ============================================================

  (define (hex-char->int c)
    (cond ((and (char>=? c #\0) (char<=? c #\9))
           (- (char->integer c) (char->integer #\0)))
          ((and (char>=? c #\a) (char<=? c #\f))
           (+ 10 (- (char->integer c) (char->integer #\a))))
          ((and (char>=? c #\A) (char<=? c #\F))
           (+ 10 (- (char->integer c) (char->integer #\A))))
          (else (error 'hex-char->int "Invalid hex character" c))))

  (define (hex->bytevector hex-str)
    "Convert hex string to bytevector"
    (let* ((len (quotient (string-length hex-str) 2))
           (bv (make-bytevector len)))
      (do ((i 0 (+ i 1)))
          ((= i len) bv)
        (let ((hi (hex-char->int (string-ref hex-str (* i 2))))
              (lo (hex-char->int (string-ref hex-str (+ (* i 2) 1)))))
          (bytevector-u8-set! bv i (+ (* hi 16) lo))))))

  (define (byte->hex b)
    "Convert byte to 2-char hex string"
    (let ((hi (quotient b 16))
          (lo (modulo b 16)))
      (string (integer->char (+ (if (< hi 10) 48 87) hi))
              (integer->char (+ (if (< lo 10) 48 87) lo)))))

  (define (bytevector->hex bv)
    "Convert bytevector to hex string"
    (let ((len (bytevector-length bv)))
      (let loop ((i 0) (acc '()))
        (if (= i len)
            (apply string-append (reverse acc))
            (loop (+ i 1)
                  (cons (byte->hex (bytevector-u8-ref bv i)) acc))))))

  (define (bytevectors-equal? a b)
    "Compare two bytevectors for equality"
    (and (= (bytevector-length a) (bytevector-length b))
         (let loop ((i 0))
           (or (= i (bytevector-length a))
               (and (= (bytevector-u8-ref a i) (bytevector-u8-ref b i))
                    (loop (+ i 1)))))))

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
    (let* ((hash (sha256-hash (string->utf8 *sha256-test-input*)))
           (expected (hex->bytevector *sha256-test-expected*)))
      (bytevectors-equal? hash expected)))

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
    (let* ((hash (sha512-hash (string->utf8 *sha512-test-input*)))
           (expected (hex->bytevector *sha512-test-expected*)))
      (bytevectors-equal? hash expected)))

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
    (let* ((seed (hex->bytevector *ed25519-secret-seed*))
           (expected-pk (hex->bytevector *ed25519-public-key*))
           (expected-sig (hex->bytevector *ed25519-signature*))
           (message (string->utf8 *ed25519-message*))
           ;; Build the 64-byte secret key: seed || public_key
           (sk (make-bytevector 64 0)))
      ;; Copy seed to first 32 bytes
      (do ((i 0 (+ i 1)))
          ((= i 32))
        (bytevector-u8-set! sk i (bytevector-u8-ref seed i)))
      ;; Copy public key to last 32 bytes
      (do ((i 0 (+ i 1)))
          ((= i 32))
        (bytevector-u8-set! sk (+ i 32) (bytevector-u8-ref expected-pk i)))
      ;; Sign the message
      (let ((sig (ed25519-sign sk message)))
        ;; Verify signature matches expected
        (and (bytevectors-equal? sig expected-sig)
             ;; Also verify the signature is valid
             (ed25519-verify expected-pk message sig)))))

  ;;; ============================================================
  ;;; FIPS 140-2 Randomness Tests
  ;;; ============================================================
  ;;
  ;; Per FIPS 140-2 Section 4.9.1, continuous RNG tests on 20,000 bits.
  ;; These are the statistical tests required for RNG validation.

  (define *fips-sample-bits* 20000)
  (define *fips-sample-bytes* 2500)  ; 20000 / 8

  (define (count-bits bytes)
    "Count number of 1 bits in bytevector"
    (let ((len (bytevector-length bytes)))
      (let loop ((i 0) (count 0))
        (if (>= i len)
            count
            (let ((byte (bytevector-u8-ref bytes i)))
              (loop (+ i 1)
                    (+ count
                       ;; Population count
                       (let bloop ((b byte) (c 0))
                         (if (= b 0) c
                             (bloop (bitwise-arithmetic-shift-right b 1)
                                    (+ c (bitwise-and b 1))))))))))))

  (define (fips-monobit-test bytes)
    "FIPS 140-2 Monobit Test: count of 1s must be 9654 < n < 10346"
    (let ((ones (count-bits bytes)))
      (and (> ones 9654) (< ones 10346))))

  (define (fips-poker-test bytes)
    "FIPS 140-2 Poker Test: 4-bit nibble distribution.
     X = (16/5000) * sum(f_i^2) - 5000, must be 1.03 < X < 57.4"
    (let ((nibble-counts (make-vector 16 0))
          (len (bytevector-length bytes)))
      ;; Count 4-bit nibbles (2 per byte = 5000 nibbles)
      (let loop ((i 0))
        (when (< i len)
          (let* ((byte (bytevector-u8-ref bytes i))
                 (hi (bitwise-arithmetic-shift-right byte 4))
                 (lo (bitwise-and byte #xf)))
            (vector-set! nibble-counts hi (+ 1 (vector-ref nibble-counts hi)))
            (vector-set! nibble-counts lo (+ 1 (vector-ref nibble-counts lo)))
            (loop (+ i 1)))))
      ;; Calculate X statistic
      (let ((sum-sq (let loop ((i 0) (sum 0))
                      (if (>= i 16)
                          sum
                          (let ((f (vector-ref nibble-counts i)))
                            (loop (+ i 1) (+ sum (* f f))))))))
        (let ((x (- (* (/ 16.0 5000.0) sum-sq) 5000.0)))
          (and (> x 1.03) (< x 57.4))))))

  (define (fips-runs-test bytes)
    "FIPS 140-2 Runs Test: count runs of 0s and 1s, verify within bounds."
    (let ((run-counts-0 (make-vector 7 0))  ; runs of 0s, length 1-6+
          (run-counts-1 (make-vector 7 0))  ; runs of 1s, length 1-6+
          (len (bytevector-length bytes)))
      ;; Count runs
      (let loop ((byte-idx 0) (bit-idx 0) (current-bit #f) (run-len 0))
        (if (>= byte-idx len)
            ;; End final run
            (when (and current-bit (> run-len 0))
              (let ((idx (min run-len 6))
                    (counts (if (= current-bit 1) run-counts-1 run-counts-0)))
                (vector-set! counts idx (+ 1 (vector-ref counts idx)))))
            (let* ((byte (bytevector-u8-ref bytes byte-idx))
                   (bit (bitwise-and 1 (bitwise-arithmetic-shift-right byte bit-idx))))
              (if (or (not current-bit) (= bit current-bit))
                  ;; Continue run
                  (let ((new-byte-idx (if (= bit-idx 7) (+ byte-idx 1) byte-idx))
                        (new-bit-idx (if (= bit-idx 7) 0 (+ bit-idx 1))))
                    (loop new-byte-idx new-bit-idx bit (+ run-len 1)))
                  ;; End run, start new
                  (begin
                    (let ((idx (min run-len 6))
                          (counts (if (= current-bit 1) run-counts-1 run-counts-0)))
                      (vector-set! counts idx (+ 1 (vector-ref counts idx))))
                    (let ((new-byte-idx (if (= bit-idx 7) (+ byte-idx 1) byte-idx))
                          (new-bit-idx (if (= bit-idx 7) 0 (+ bit-idx 1))))
                      (loop new-byte-idx new-bit-idx bit 1)))))))
      ;; Check bounds (indices 1-6 for run lengths 1-6+)
      (let ((bounds '((1 2267 2733)
                      (2 1079 1421)
                      (3 502 748)
                      (4 223 402)
                      (5 90 223)
                      (6 90 223))))
        (let check ((b bounds))
          (if (null? b)
              #t
              (let* ((spec (car b))
                     (idx (car spec))
                     (lo (cadr spec))
                     (hi (caddr spec))
                     (c0 (vector-ref run-counts-0 idx))
                     (c1 (vector-ref run-counts-1 idx)))
                (if (and (>= c0 lo) (<= c0 hi) (>= c1 lo) (<= c1 hi))
                    (check (cdr b))
                    #f)))))))

  (define (fips-long-run-test bytes)
    "FIPS 140-2 Long Run Test: no run of 26+ consecutive identical bits."
    (let ((len (bytevector-length bytes)))
      (let loop ((byte-idx 0) (bit-idx 0) (current-bit #f) (run-len 0))
        (cond
          ((>= run-len 26) #f)  ; Failed
          ((>= byte-idx len) #t)  ; Passed
          (else
            (let* ((byte (bytevector-u8-ref bytes byte-idx))
                   (bit (bitwise-and 1 (bitwise-arithmetic-shift-right byte bit-idx)))
                   (new-run (if (eqv? bit current-bit) (+ run-len 1) 1))
                   (new-byte-idx (if (= bit-idx 7) (+ byte-idx 1) byte-idx))
                   (new-bit-idx (if (= bit-idx 7) 0 (+ bit-idx 1))))
              (loop new-byte-idx new-bit-idx bit new-run)))))))

  (define (test-randomness)
    "FIPS 140-2 randomness tests on 20,000 bits from entropy source.
     Tests: Monobit, Poker, Runs, Long Run.
     Returns #t if all pass, #f if any fail."
    (let ((sample (random-bytes *fips-sample-bytes*)))
      (and (= (bytevector-length sample) *fips-sample-bytes*)
           (fips-monobit-test sample)
           (fips-poker-test sample)
           (fips-runs-test sample)
           (fips-long-run-test sample))))

  ;;; ============================================================
  ;;; FIPS Self-Test Entry Point
  ;;; ============================================================

  (define *fips-status* 'untested)

  (define (fips-status)
    "Get FIPS self-test status: 'passed, 'failed, or 'untested"
    *fips-status*)

  (define (fips-self-test . rest)
    "Run all FIPS self-tests. Returns #t if all pass, signals error if any fail.
     Optional: (fips-self-test #t) for verbose output."
    (let ((verbose (and (pair? rest) (car rest)))
          (tests `((sha256 . ,test-sha256)
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
              (flush-output-port (current-output-port)))
            (let ((result (proc)))
              (when verbose
                (printf "~a~%" (if result "ok" "FAILED")))
              (unless result
                (set! failed (cons name failed))))))
        tests)
      (if (null? failed)
          (begin
            (set! *fips-status* 'passed)
            #t)
          (begin
            (set! *fips-status* 'failed)
            (error 'fips-self-test
                   (string-append "FIPS self-test FAILED: "
                                  (let loop ((lst (reverse failed)) (acc ""))
                                    (if (null? lst)
                                        acc
                                        (loop (cdr lst)
                                              (string-append acc
                                                (if (string=? acc "") "" ", ")
                                                (symbol->string (car lst))))))))))))

) ;; end library
