#!/usr/bin/env csi -q
;;; FIPS-181 Compliance Tests
;;;
;;; Validates pronounceable syllable generation per FIPS PUB 181
;;; (Automated Password Generator).
;;;
;;; Run: csi -q test-fips181.scm

(import wordlist crypto-ffi (chicken format) (chicken blob) srfi-1 srfi-4 srfi-69)

(sodium-init)

(define *tests-passed* 0)
(define *tests-failed* 0)

(define (test name expected actual)
  (if (equal? expected actual)
      (begin
        (set! *tests-passed* (+ *tests-passed* 1))
        (printf "[PASS] ~a~n" name))
      (begin
        (set! *tests-failed* (+ *tests-failed* 1))
        (printf "[FAIL] ~a~n  Expected: ~a~n  Actual: ~a~n" name expected actual))))

(define (test-pred name pred actual)
  (if (pred actual)
      (begin
        (set! *tests-passed* (+ *tests-passed* 1))
        (printf "[PASS] ~a~n" name))
      (begin
        (set! *tests-failed* (+ *tests-failed* 1))
        (printf "[FAIL] ~a - predicate failed~n  Value: ~a~n" name actual))))

;; ============================================================
;; FIPS-181 Pronounceability Tests
;; ============================================================

(printf "~n=== FIPS-181 Pronounceability Tests ===~n~n")

;; Test 1: Syllable structure (CVC pattern)
(define (valid-cvc? syllable)
  "Check if syllable follows consonant-vowel-consonant pattern"
  (and (= (string-length syllable) 3)
       (let ((c1 (string-ref syllable 0))
             (v  (string-ref syllable 1))
             (c2 (string-ref syllable 2)))
         (and (not (memq c1 '(#\a #\e #\i #\o #\u)))
              (memq v '(#\a #\e #\i #\o #\u))
              (not (memq c2 '(#\a #\e #\i #\o #\u)))))))

;; Test various byte values
(printf "Testing CVC structure for byte values...~n")
(let loop ((byte 0) (cvc-pass 0) (cvc-fail 0))
  (if (= byte 256)
      (begin
        (printf "  CVC compliance: ~a/256 bytes produce valid CVC~n" cvc-pass)
        (test "All bytes produce valid CVC syllables" 256 cvc-pass))
      (let ((syllable (byte->syllable byte)))
        (if (valid-cvc? syllable)
            (loop (+ byte 1) (+ cvc-pass 1) cvc-fail)
            (begin
              (printf "  FAIL: byte ~a -> ~a (not CVC)~n" byte syllable)
              (loop (+ byte 1) cvc-pass (+ cvc-fail 1)))))))

;; Test 2: Determinism
(printf "~nTesting determinism...~n")
(let ((s1 (byte->syllable 42))
      (s2 (byte->syllable 42)))
  (test "Same byte produces same syllable" s1 s2))

;; Test 3: Uniqueness (ideally all 256 bytes produce different syllables)
(printf "~nTesting syllable distribution...~n")
(let ((syllables (make-hash-table string=?)))
  (do ((byte 0 (+ byte 1)))
      ((= byte 256))
    (let ((s (byte->syllable byte)))
      (hash-table-set! syllables s #t)))
  (let ((unique-count (hash-table-size syllables)))
    (printf "  Unique syllables: ~a/256~n" unique-count)
    ;; At least 200 unique (some collision expected due to modulo)
    (test-pred "Sufficient syllable diversity (>200 unique)"
               (lambda (n) (> n 200))
               unique-count)))

;; ============================================================
;; FIPS-181 Encoding Tests
;; ============================================================

(printf "~n=== FIPS-181 Encoding Tests ===~n~n")

;; Test pubkey encoding
(printf "Testing public key encoding...~n")
(let* ((keypair (ed25519-keypair))
       (pubkey (car keypair))
       (syllables (pubkey->syllables pubkey)))
  (test "Public key produces 4 syllables" 4 (length syllables))
  (test-pred "All syllables are strings"
             (lambda (syls) (every string? syls))
             syllables)
  (test-pred "All syllables are CVC"
             (lambda (syls) (every valid-cvc? syls))
             syllables))

;; Test display format
(printf "~nTesting display format...~n")
(let* ((syllables '("bek" "fom" "riz" "tup"))
       (display-str (syllables->display syllables)))
  (test "Syllables joined with hyphens" "bek-fom-riz-tup" display-str))

;; Test determinism across calls
(printf "~nTesting encoding determinism...~n")
(let* ((keypair (ed25519-keypair))
       (pubkey (car keypair))
       (enc1 (pubkey->syllables pubkey))
       (enc2 (pubkey->syllables pubkey)))
  (test "Same key produces same encoding" enc1 enc2))

;; ============================================================
;; PGP Word List Tests (Alternative Mode)
;; ============================================================

(printf "~n=== PGP Word List Tests ===~n~n")

;; Test even words (two syllables)
(printf "Testing even-position word list...~n")
(test "Even word list has 256 entries" 256 (vector-length even-words))

;; Test odd words (three syllables)
(printf "Testing odd-position word list...~n")
(test "Odd word list has 256 entries" 256 (vector-length odd-words))

;; Test byte->word mapping
(printf "~nTesting byte to word mapping...~n")
(test "Byte 0 even = aardvark" "aardvark" (byte->word 0 0))
(test "Byte 0 odd = adroitness" "adroitness" (byte->word 0 1))
(test "Byte 255 even = Zulu" "Zulu" (byte->word 255 0))

;; Test pubkey->words
(printf "~nTesting public key to words...~n")
(let* ((keypair (ed25519-keypair))
       (pubkey (car keypair))
       (words (pubkey->words pubkey)))
  (test "Public key produces 4 words" 4 (length words))
  (test-pred "All words are strings"
             (lambda (ws) (every string? ws))
             words))

;; ============================================================
;; Summary
;; ============================================================

(printf "~n=== Test Summary ===~n")
(printf "Passed: ~a~n" *tests-passed*)
(printf "Failed: ~a~n" *tests-failed*)

(if (= *tests-failed* 0)
    (printf "~nAll FIPS-181 compliance tests PASSED~n")
    (printf "~nSome tests FAILED - review output above~n"))

(exit *tests-failed*)
