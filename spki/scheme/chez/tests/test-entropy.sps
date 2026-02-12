#!/usr/bin/env chez --script
;;; test-entropy.sps - Cryptographic entropy quality tests
;;;
;;; Verifies that libsodium's CSPRNG produces output with
;;; expected statistical properties. Not a replacement for
;;; NIST SP 800-22, but catches obvious failures: stuck RNG,
;;; zero-fill, bias, and implementation misconfiguration.

(import (rnrs)
        (only (chezscheme) printf format time real-time for-all)
        (cyberspace crypto-ffi))

;; member with custom comparator (R6RS member only takes 2 args)
(define (bv-member bv lst)
  (cond
   ((null? lst) #f)
   ((bytevector=? bv (car lst)) #t)
   (else (bv-member bv (cdr lst)))))

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
             (printf "  FAIL: ~a (expected ~s, got ~s)~%" msg expected actual))))

(printf "~%=== Entropy Quality Tests ===~%~%")
(sodium-init)

;; Test 1: Implementation identity
(printf "--- RNG Implementation ---~%")
(let ((status (entropy-status)))
  (assert-true "entropy-status returns alist" (list? status))
  (let ((impl (cond ((assq 'implementation status) => cdr)
                     (else #f))))
    (assert-true "implementation is reported" (string? impl))
    (assert-true "implementation is known-good"
                 (member impl '("sysrandom" "urandom" "getrandom")))
    (printf "  INFO: RNG implementation: ~a~%" impl)))

;; Test 2: Uniqueness - no collisions in 1000 32-byte samples
(printf "--- Uniqueness ---~%")
(let ((samples (let loop ((i 0) (acc '()))
                 (if (>= i 1000)
                     acc
                     (loop (+ i 1) (cons (random-bytes 32) acc))))))
  ;; Check no two samples are equal
  (let ((unique (let loop ((lst samples) (seen '()) (dups 0))
                  (cond
                   ((null? lst) dups)
                   ((bv-member (car lst) seen)
                    (loop (cdr lst) seen (+ dups 1)))
                   (else
                    (loop (cdr lst) (cons (car lst) seen) dups))))))
    (assert-equal "no collisions in 1000 x 32-byte samples" 0 unique)))

;; Test 3: Uniqueness of keypairs
(printf "--- Keypair Uniqueness ---~%")
(let ((keys (let loop ((i 0) (acc '()))
              (if (>= i 100)
                  acc
                  (let ((kp (ed25519-keypair)))
                    (loop (+ i 1) (cons (car kp) acc)))))))
  (let ((unique (let loop ((lst keys) (seen '()) (dups 0))
                  (cond
                   ((null? lst) dups)
                   ((bv-member (car lst) seen)
                    (loop (cdr lst) seen (+ dups 1)))
                   (else
                    (loop (cdr lst) (cons (car lst) seen) dups))))))
    (assert-equal "no duplicate public keys in 100 keypairs" 0 unique)))

;; Test 4: Non-zero - random bytes are not all zeros
(printf "--- Non-Zero ---~%")
(let ((zero-count
       (let loop ((i 0) (zeros 0))
         (if (>= i 100)
             zeros
             (let* ((buf (random-bytes 32))
                    (all-zero? (let inner ((j 0))
                                 (cond
                                  ((>= j 32) #t)
                                  ((not (= 0 (bytevector-u8-ref buf j))) #f)
                                  (else (inner (+ j 1)))))))
               (loop (+ i 1) (if all-zero? (+ zeros 1) zeros)))))))
  (assert-equal "no all-zero buffers in 100 samples" 0 zero-count))

;; Also check that private keys are non-zero
(let* ((kp (ed25519-keypair))
       (sk (cadr kp))
       (all-zero? (let loop ((i 0))
                    (cond
                     ((>= i (bytevector-length sk)) #t)
                     ((not (= 0 (bytevector-u8-ref sk i))) #f)
                     (else (loop (+ i 1)))))))
  (assert-true "private key is not all zeros" (not all-zero?)))

;; Test 5: Byte distribution (chi-squared)
;; Generate 25600 bytes (100 expected per bucket for 256 buckets).
;; Chi-squared critical value at p=0.001, df=255 is ~310.
;; A stuck or biased RNG will vastly exceed this.
(printf "--- Byte Distribution (Chi-Squared) ---~%")
(let ((counts (make-vector 256 0))
      (buf (random-bytes 25600))
      (n 25600))
  ;; Count byte frequencies
  (let loop ((i 0))
    (when (< i n)
      (let ((b (bytevector-u8-ref buf i)))
        (vector-set! counts b (+ 1 (vector-ref counts b)))
        (loop (+ i 1)))))
  ;; Compute chi-squared statistic
  (let* ((expected (/ n 256))  ; 100.0
         (chi-sq (let loop ((i 0) (sum 0.0))
                   (if (>= i 256)
                       sum
                       (let ((obs (vector-ref counts i)))
                         (loop (+ i 1)
                               (+ sum (/ (* (- obs expected) (- obs expected))
                                         expected))))))))
    (printf "  INFO: chi-squared = ~a (critical ~a at p=0.001)~%"
            (let ((r (* (round (* chi-sq 100)) 0.01))) r) 310)
    (assert-true "chi-squared within expected range (< 310)" (< chi-sq 310.0))
    ;; Also check it's not suspiciously low (perfectly uniform = not random)
    ;; Lower critical value at p=0.001, df=255 is ~198
    (assert-true "chi-squared not suspiciously low (> 198)" (> chi-sq 198.0))))

;; Test 6: Monobit test (NIST SP 800-22 section 2.1)
;; Count 1-bits in 2500 bytes (20000 bits).
;; Expected: 10000. Acceptable range: 9725..10275 (at p=0.01).
(printf "--- Monobit (Bit Balance) ---~%")
(let ((buf (random-bytes 2500)))
  (let ((ones (let loop ((i 0) (count 0))
                (if (>= i 2500)
                    count
                    (let ((byte (bytevector-u8-ref buf i)))
                      (loop (+ i 1)
                            (+ count
                               ;; popcount
                               (let inner ((b byte) (c 0))
                                 (if (= b 0) c
                                     (inner (bitwise-arithmetic-shift-right b 1)
                                            (+ c (bitwise-and b 1))))))))))))
    (printf "  INFO: ones = ~a / 20000 (expected 10000)~%" ones)
    (assert-true "monobit: ones in range 9725..10275"
                 (and (>= ones 9725) (<= ones 10275)))))

;; Test 7: Runs test (adjacent bit transitions)
;; In truly random bits, we expect roughly n/2 transitions in n bits.
;; For 20000 bits: expected ~10000 transitions.
(printf "--- Runs (Bit Transitions) ---~%")
(let ((buf (random-bytes 2500)))
  (let ((transitions
         (let loop ((i 0) (prev-bit -1) (count 0))
           (if (>= i 2500)
               count
               (let ((byte (bytevector-u8-ref buf i)))
                 (let inner ((bit 7) (pb prev-bit) (c count))
                   (if (< bit 0)
                       (loop (+ i 1) pb c)
                       (let ((this-bit (bitwise-and 1 (bitwise-arithmetic-shift-right byte bit))))
                         (if (= pb -1)
                             (inner (- bit 1) this-bit c)
                             (inner (- bit 1) this-bit
                                    (if (not (= this-bit pb)) (+ c 1) c)))))))))))
    (printf "  INFO: transitions = ~a / 19999 (expected 10000)~%" transitions)
    (assert-true "runs: transitions in range 9600..10400"
                 (and (>= transitions 9600) (<= transitions 10400)))))

;; Test 8: random-u32 range and distribution
(printf "--- random-u32 ---~%")
(let ((samples (let loop ((i 0) (acc '()))
                 (if (>= i 1000)
                     acc
                     (loop (+ i 1) (cons (random-u32) acc))))))
  ;; Check we get values across the full 32-bit range
  (let ((min-val (apply min samples))
        (max-val (apply max samples)))
    (assert-true "random-u32 min < 2^30" (< min-val (expt 2 30)))
    (assert-true "random-u32 max > 2^30" (> max-val (expt 2 30)))))

;; Test 9: random-uniform bounds
(printf "--- random-uniform ---~%")
(let ((samples (let loop ((i 0) (acc '()))
                 (if (>= i 1000)
                     acc
                     (loop (+ i 1) (cons (random-uniform 100) acc))))))
  (assert-true "all values < 100" (for-all (lambda (x) (< x 100)) samples))
  (assert-true "all values >= 0" (for-all (lambda (x) (>= x 0)) samples))
  ;; Should see values near both ends
  (assert-true "min value < 10" (< (apply min samples) 10))
  (assert-true "max value > 90" (> (apply max samples) 90)))

;; Test 10: Successive keypairs produce independent signatures
(printf "--- Signature Independence ---~%")
(let* ((msg "test message for independence check")
       (kp1 (ed25519-keypair))
       (kp2 (ed25519-keypair))
       (sig1 (ed25519-sign (cadr kp1) msg))
       (sig2 (ed25519-sign (cadr kp2) msg)))
  (assert-true "different keys produce different signatures"
               (not (bytevector=? sig1 sig2)))
  ;; Same key, same message should produce same signature (Ed25519 is deterministic)
  (let ((sig1b (ed25519-sign (cadr kp1) msg)))
    (assert-true "same key + message produces same signature (deterministic)"
                 (bytevector=? sig1 sig1b))))

;; Summary
(printf "~%=== Entropy: ~a passed, ~a failed ===~%~%" *pass* *fail*)
(when (> *fail* 0) (exit 1))
