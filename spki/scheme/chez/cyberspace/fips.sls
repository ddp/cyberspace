;;; SPKI Scheme - FIPS 140-2 Style Self-Tests
;;; Library of Cyberspace - Chez Port
;;;
;;; Known-Answer Tests (KATs) to verify crypto primitives on startup.
;;; If any test fails, Cyberspace refuses to start.
;;;
;;; Test vectors from official sources:
;;;   - SHA-256/512: NIST FIPS 180-4 examples
;;;   - Ed25519: RFC 8032 test vectors

(library (cyberspace fips)
  (export
    fips-self-test
    test-sha256
    test-sha512
    test-ed25519
    test-randomness
    fips-monobit-test
    fips-poker-test
    fips-runs-test
    fips-long-run-test
    fips-status)

  (import (rnrs)
          (only (chezscheme) printf format)
          (cyberspace crypto-ffi)
          (cyberspace chicken-compatibility blob)
          (cyberspace chicken-compatibility chicken))

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
          (else (error 'hex-char->int "Invalid hex character" c))))

  (define (hex->blob hex-str)
    (let* ((len (div (string-length hex-str) 2))
           (vec (make-u8vector len)))
      (do ((i 0 (+ i 1)))
          ((= i len) (u8vector->blob vec))
        (let ((hi (hex-char->int (string-ref hex-str (* i 2))))
              (lo (hex-char->int (string-ref hex-str (+ (* i 2) 1)))))
          (u8vector-set! vec i (+ (* hi 16) lo))))))

  (define (blobs-equal? a b)
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

  (define *sha256-test-input* "abc")
  (define *sha256-test-expected*
    "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")

  (define (test-sha256)
    (let* ((hash (sha256-hash *sha256-test-input*))
           (expected (hex->blob *sha256-test-expected*)))
      (blobs-equal? hash expected)))

  ;;; ============================================================
  ;;; SHA-512 KAT (NIST FIPS 180-4)
  ;;; ============================================================

  (define *sha512-test-input* "abc")
  (define *sha512-test-expected*
    "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f")

  (define (test-sha512)
    (let* ((hash (sha512-hash *sha512-test-input*))
           (expected (hex->blob *sha512-test-expected*)))
      (blobs-equal? hash expected)))

  ;;; ============================================================
  ;;; Ed25519 KAT (RFC 8032 Test Vector 1)
  ;;; ============================================================

  (define *ed25519-secret-seed*
    "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60")
  (define *ed25519-public-key*
    "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a")
  (define *ed25519-message* "")
  (define *ed25519-signature*
    "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b")

  (define (test-ed25519)
    (let* ((seed (hex->blob *ed25519-secret-seed*))
           (expected-pk (hex->blob *ed25519-public-key*))
           (expected-sig (hex->blob *ed25519-signature*))
           (message (string->blob *ed25519-message*))
           (sk (make-blob 64))
           (sk-vec (blob->u8vector/shared sk))
           (seed-vec (blob->u8vector seed))
           (pk-vec (blob->u8vector expected-pk)))
      (do ((i 0 (+ i 1))) ((= i 32))
        (u8vector-set! sk-vec i (u8vector-ref seed-vec i)))
      (do ((i 0 (+ i 1))) ((= i 32))
        (u8vector-set! sk-vec (+ i 32) (u8vector-ref pk-vec i)))
      (let ((sig (ed25519-sign sk message)))
        (and (blobs-equal? sig expected-sig)
             (ed25519-verify expected-pk message sig)))))

  ;;; ============================================================
  ;;; FIPS 140-2 Randomness Tests (20,000 bits)
  ;;; ============================================================

  (define *fips-sample-bytes* 2500)

  (define (count-bits bytes)
    (let ((len (u8vector-length bytes)))
      (let loop ((i 0) (count 0))
        (if (>= i len)
            count
            (let ((byte (u8vector-ref bytes i)))
              (loop (+ i 1)
                    (+ count
                       (let bloop ((b byte) (c 0))
                         (if (= b 0) c
                             (bloop (bitwise-arithmetic-shift-right b 1)
                                    (+ c (bitwise-and b 1))))))))))))

  (define (fips-monobit-test bytes)
    (let ((ones (count-bits bytes)))
      (and (> ones 9654) (< ones 10346))))

  (define (fips-poker-test bytes)
    (let ((nibble-counts (make-vector 16 0))
          (len (u8vector-length bytes)))
      (let loop ((i 0))
        (when (< i len)
          (let* ((byte (u8vector-ref bytes i))
                 (hi (bitwise-arithmetic-shift-right byte 4))
                 (lo (bitwise-and byte #xf)))
            (vector-set! nibble-counts hi (+ 1 (vector-ref nibble-counts hi)))
            (vector-set! nibble-counts lo (+ 1 (vector-ref nibble-counts lo)))
            (loop (+ i 1)))))
      (let ((sum-sq (let loop ((i 0) (sum 0))
                      (if (>= i 16)
                          sum
                          (let ((f (vector-ref nibble-counts i)))
                            (loop (+ i 1) (+ sum (* f f))))))))
        (let ((x (- (* (/ 16.0 5000.0) sum-sq) 5000.0)))
          (and (> x 1.03) (< x 57.4))))))

  (define (fips-runs-test bytes)
    (let ((run-counts-0 (make-vector 7 0))
          (run-counts-1 (make-vector 7 0))
          (len (u8vector-length bytes)))
      (let loop ((byte-idx 0) (bit-idx 0) (current-bit #f) (run-len 0))
        (if (>= byte-idx len)
            (when (and current-bit (> run-len 0))
              (let ((idx (min run-len 6))
                    (counts (if (= current-bit 1) run-counts-1 run-counts-0)))
                (vector-set! counts idx (+ 1 (vector-ref counts idx)))))
            (let* ((byte (u8vector-ref bytes byte-idx))
                   (bit (bitwise-and 1 (bitwise-arithmetic-shift-right byte bit-idx))))
              (if (or (not current-bit) (= bit current-bit))
                  (let ((new-byte-idx (if (= bit-idx 7) (+ byte-idx 1) byte-idx))
                        (new-bit-idx (if (= bit-idx 7) 0 (+ bit-idx 1))))
                    (loop new-byte-idx new-bit-idx bit (+ run-len 1)))
                  (begin
                    (let ((idx (min run-len 6))
                          (counts (if (= current-bit 1) run-counts-1 run-counts-0)))
                      (vector-set! counts idx (+ 1 (vector-ref counts idx))))
                    (let ((new-byte-idx (if (= bit-idx 7) (+ byte-idx 1) byte-idx))
                          (new-bit-idx (if (= bit-idx 7) 0 (+ bit-idx 1))))
                      (loop new-byte-idx new-bit-idx bit 1)))))))
      (let ((bounds '((1 2267 2733) (2 1079 1421) (3 502 748)
                      (4 223 402) (5 90 223) (6 90 223))))
        (let check ((b bounds))
          (if (null? b) #t
              (let* ((spec (car b))
                     (idx (car spec)) (lo (cadr spec)) (hi (caddr spec))
                     (c0 (vector-ref run-counts-0 idx))
                     (c1 (vector-ref run-counts-1 idx)))
                (if (and (>= c0 lo) (<= c0 hi) (>= c1 lo) (<= c1 hi))
                    (check (cdr b))
                    #f)))))))

  (define (fips-long-run-test bytes)
    (let ((len (u8vector-length bytes)))
      (let loop ((byte-idx 0) (bit-idx 0) (current-bit #f) (run-len 0))
        (cond
          ((>= run-len 26) #f)
          ((>= byte-idx len) #t)
          (else
            (let* ((byte (u8vector-ref bytes byte-idx))
                   (bit (bitwise-and 1 (bitwise-arithmetic-shift-right byte bit-idx)))
                   (new-run (if (eqv? bit current-bit) (+ run-len 1) 1))
                   (new-byte-idx (if (= bit-idx 7) (+ byte-idx 1) byte-idx))
                   (new-bit-idx (if (= bit-idx 7) 0 (+ bit-idx 1))))
              (loop new-byte-idx new-bit-idx bit new-run)))))))

  (define (test-randomness)
    (let* ((sample (random-bytes *fips-sample-bytes*))
           (bytes (blob->u8vector sample)))
      (and (= (u8vector-length bytes) *fips-sample-bytes*)
           (fips-monobit-test bytes)
           (fips-poker-test bytes)
           (fips-runs-test bytes)
           (fips-long-run-test bytes))))

  ;;; ============================================================
  ;;; FIPS Self-Test Entry Point
  ;;; ============================================================

  (define *fips-status* 'untested)

  (define (fips-status) *fips-status*)

  (define (fips-self-test . rest)
    (let ((verbose (get-opt rest 0 #f))
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
                   (format #f "FIPS self-test FAILED: ~a" (reverse failed)))))))

) ;; end library
