#!/usr/bin/env csi -s
;; ChaCha20 Stream Cipher
;; RFC 7539: ChaCha20 and Poly1305 for IETF Protocols
;;
;; Paper: D. J. Bernstein (2008), "ChaCha, a variant of Salsa20"
;; RFC: RFC 7539 (2015)
;; Source: ~/cyberspace/library/cryptographers/djb/chacha20-2008.pdf
;;
;; Concept: Fast, secure stream cipher using ARX operations
;;   - ARX = Add, Rotate, XOR (no table lookups, no timing attacks)
;;   - 256-bit key, 96-bit nonce, 32-bit counter
;;   - 20 rounds of mixing (quarter-round function)
;;   - Constant-time (no secret-dependent branches)
;;
;; "The wonderful thing about ARX is that it's very simple to implement,
;;  very fast, and very resistant to timing attacks."
;; —Daniel J. Bernstein

(import scheme)
(import (chicken base))
(import (chicken bitwise))
(import (chicken string))
(import (chicken process-context))
(import srfi-4)   ;; Homogeneous numeric vectors
(import srfi-13)  ;; String libraries

;; ============================================================================
;; 32-bit Unsigned Integer Operations
;; ============================================================================

(define (u32+ a b)
  "32-bit addition (wrapping)"
  (bitwise-and (+ a b) #xFFFFFFFF))

(define (u32-xor a b)
  "32-bit XOR"
  (bitwise-xor a b))

(define (rotl32 value shift)
  "Rotate left 32-bit value by shift bits"
  (let ((shifted (arithmetic-shift value shift))
        (wrapped (arithmetic-shift value (- shift 32))))
    (bitwise-and (bitwise-ior shifted wrapped) #xFFFFFFFF)))

;; ============================================================================
;; ChaCha20 Quarter Round
;; ============================================================================

(define (quarter-round a b c d state)
  "ChaCha20 quarter round: modifies state indices a,b,c,d"
  ;; a += b; d ^= a; d <<<= 16
  (let* ((new-a (u32+ (u32vector-ref state a) (u32vector-ref state b))))
    (u32vector-set! state a new-a)
    (let ((new-d (rotl32 (u32-xor (u32vector-ref state d) new-a) 16)))
      (u32vector-set! state d new-d)
      ;; c += d; b ^= c; b <<<= 12
      (let* ((new-c (u32+ (u32vector-ref state c) new-d)))
        (u32vector-set! state c new-c)
        (let ((new-b (rotl32 (u32-xor (u32vector-ref state b) new-c) 12)))
          (u32vector-set! state b new-b)
          ;; a += b; d ^= a; d <<<= 8
          (let* ((new-a2 (u32+ (u32vector-ref state a) new-b)))
            (u32vector-set! state a new-a2)
            (let ((new-d2 (rotl32 (u32-xor (u32vector-ref state d) new-a2) 8)))
              (u32vector-set! state d new-d2)
              ;; c += d; b ^= c; b <<<= 7
              (let* ((new-c2 (u32+ (u32vector-ref state c) new-d2)))
                (u32vector-set! state c new-c2)
                (let ((new-b2 (rotl32 (u32-xor (u32vector-ref state b) new-c2) 7)))
                  (u32vector-set! state b new-b2))))))))))

;; ============================================================================
;; ChaCha20 Block Function
;; ============================================================================

(define (chacha20-block key counter nonce)
  "Generate one ChaCha20 block (64 bytes) from key, counter, and nonce"
  ;; key: 32 bytes, counter: 4 bytes (u32), nonce: 12 bytes

  ;; Initialize state with constants, key, counter, nonce
  (let ((state (make-u32vector 16)))

    ;; Constants "expand 32-byte k"
    (u32vector-set! state 0 #x61707865)  ;; "expa"
    (u32vector-set! state 1 #x3320646e)  ;; "nd 3"
    (u32vector-set! state 2 #x79622d32)  ;; "2-by"
    (u32vector-set! state 3 #x6b206574)  ;; "te k"

    ;; Key (256 bits = 8 x 32-bit words)
    (do ((i 0 (+ i 1)))
        ((= i 8))
      (u32vector-set! state (+ 4 i) (u32vector-ref key i)))

    ;; Counter (32 bits)
    (u32vector-set! state 12 counter)

    ;; Nonce (96 bits = 3 x 32-bit words)
    (do ((i 0 (+ i 1)))
        ((= i 3))
      (u32vector-set! state (+ 13 i) (u32vector-ref nonce i)))

    ;; Save initial state
    (let ((initial-state (make-u32vector 16)))
      (do ((i 0 (+ i 1)))
          ((= i 16))
        (u32vector-set! initial-state i (u32vector-ref state i)))

      ;; 20 rounds (10 iterations of double-round)
      (do ((i 0 (+ i 1)))
          ((= i 10))
        ;; Column rounds
        (quarter-round 0 4  8 12 state)
        (quarter-round 1 5  9 13 state)
        (quarter-round 2 6 10 14 state)
        (quarter-round 3 7 11 15 state)
        ;; Diagonal rounds
        (quarter-round 0 5 10 15 state)
        (quarter-round 1 6 11 12 state)
        (quarter-round 2 7  8 13 state)
        (quarter-round 3 4  9 14 state))

      ;; Add initial state
      (do ((i 0 (+ i 1)))
          ((= i 16))
        (u32vector-set! state i (u32+ (u32vector-ref state i)
                                      (u32vector-ref initial-state i))))

      state)))

;; ============================================================================
;; Helper Functions
;; ============================================================================

(define (hex-string->bytes hex)
  "Convert hex string to byte vector"
  (let* ((hex-clean (string-delete (lambda (c) (char-whitespace? c)) hex))
         (len (quotient (string-length hex-clean) 2))
         (bytes (make-u8vector len)))
    (do ((i 0 (+ i 1)))
        ((= i len) bytes)
      (let ((start (* i 2))
            (end (+ (* i 2) 2)))
        (u8vector-set! bytes i
                       (string->number (substring hex-clean start end) 16))))))

(define (bytes->u32vector bytes)
  "Convert byte vector to u32vector (little-endian)"
  (let* ((len (quotient (u8vector-length bytes) 4))
         (words (make-u32vector len)))
    (do ((i 0 (+ i 1)))
        ((= i len) words)
      (let ((offset (* i 4)))
        (u32vector-set! words i
                        (+ (u8vector-ref bytes offset)
                           (arithmetic-shift (u8vector-ref bytes (+ offset 1)) 8)
                           (arithmetic-shift (u8vector-ref bytes (+ offset 2)) 16)
                           (arithmetic-shift (u8vector-ref bytes (+ offset 3)) 24)))))))

(define (u32vector->bytes words)
  "Convert u32vector to byte vector (little-endian)"
  (let* ((len (* (u32vector-length words) 4))
         (bytes (make-u8vector len)))
    (do ((i 0 (+ i 1)))
        ((= i (u32vector-length words)) bytes)
      (let ((word (u32vector-ref words i))
            (offset (* i 4)))
        (u8vector-set! bytes offset (bitwise-and word #xFF))
        (u8vector-set! bytes (+ offset 1) (bitwise-and (arithmetic-shift word -8) #xFF))
        (u8vector-set! bytes (+ offset 2) (bitwise-and (arithmetic-shift word -16) #xFF))
        (u8vector-set! bytes (+ offset 3) (bitwise-and (arithmetic-shift word -24) #xFF))))))

(define (bytes->hex bytes)
  "Convert byte vector to hex string"
  (let ((result (make-string (* (u8vector-length bytes) 2))))
    (do ((i 0 (+ i 1)))
        ((= i (u8vector-length bytes)) result)
      (let* ((byte (u8vector-ref bytes i))
             (hex (number->string byte 16))
             (hex-padded (if (< byte 16)
                             (string-append "0" hex)
                             hex)))
        (string-set! result (* i 2) (string-ref hex-padded 0))
        (string-set! result (+ (* i 2) 1) (string-ref hex-padded 1))))))

(define (u8vector->string bytes)
  "Convert byte vector to string"
  (let* ((len (u8vector-length bytes))
         (str (make-string len)))
    (do ((i 0 (+ i 1)))
        ((= i len) str)
      (string-set! str i (integer->char (u8vector-ref bytes i))))))

;; ============================================================================
;; ChaCha20 Encryption/Decryption
;; ============================================================================

(define (chacha20-encrypt key-hex nonce-hex counter plaintext)
  "Encrypt plaintext using ChaCha20"
  (let* ((key (bytes->u32vector (hex-string->bytes key-hex)))
         (nonce (bytes->u32vector (hex-string->bytes nonce-hex)))
         (plaintext-bytes (if (string? plaintext)
                              (let* ((slen (string-length plaintext))
                                     (bytes (make-u8vector slen)))
                                (do ((i 0 (+ i 1)))
                                    ((= i slen) bytes)
                                  (u8vector-set! bytes i (char->integer (string-ref plaintext i)))))
                              plaintext))
         (len (u8vector-length plaintext-bytes))
         (ciphertext (make-u8vector len))
         (block-count (quotient (+ len 63) 64)))

    (do ((block-num 0 (+ block-num 1)))
        ((= block-num block-count) ciphertext)
      (let* ((keystream-words (chacha20-block key (+ counter block-num) nonce))
             (keystream (u32vector->bytes keystream-words))
             (offset (* block-num 64))
             (remaining (- len offset))
             (chunk-size (min remaining 64)))

        ;; XOR plaintext with keystream
        (do ((i 0 (+ i 1)))
            ((= i chunk-size))
          (u8vector-set! ciphertext (+ offset i)
                         (bitwise-xor (u8vector-ref plaintext-bytes (+ offset i))
                                      (u8vector-ref keystream i))))))))

(define (chacha20-decrypt key-hex nonce-hex counter ciphertext)
  "Decrypt ciphertext using ChaCha20 (same as encrypt for stream cipher)"
  (chacha20-encrypt key-hex nonce-hex counter ciphertext))

;; ============================================================================
;; RFC 7539 Test Vectors
;; ============================================================================

(define (test-quarter-round)
  "Test ChaCha20 quarter round (RFC 7539 Section 2.1.1)"
  (print "Testing quarter round...")
  (let ((state (u32vector #x879531e0 #xc5ecf37d #x516461b1 #xc9a62f8a
                          #x44c20ef3 #x3390af7f #xd9fc690b #x2a5f714c
                          #x53372767 #xb00a5631 #x974c541a #x359e9963
                          #x5c971061 #x3d631689 #x2098d9d6 #x91dbd320)))
    (quarter-round 2 7 8 13 state)
    (let ((expected #xe876d72b)
          (actual (u32vector-ref state 2)))
      (if (= expected actual)
          (print "✓ Quarter round test PASSED")
          (print "✗ Quarter round test FAILED: expected " (number->string expected 16)
                 " got " (number->string actual 16))))))

(define (test-chacha20-block)
  "Test ChaCha20 block function (RFC 7539 Section 2.3.2)"
  (print "\nTesting ChaCha20 block function...")
  (let* ((key (bytes->u32vector
               (hex-string->bytes
                "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f")))
         (nonce (bytes->u32vector
                 (hex-string->bytes "000000090000004a00000000")))
         (counter 1)
         (result (chacha20-block key counter nonce))
         (result-bytes (u32vector->bytes result))
         (result-hex (bytes->hex result-bytes))
         (expected "10f1e7e4d13b5915500fdd1fa32071c4c7d1f4c733c068030422aa9ac3d46c4ed2826446079faa0914c2d705d98b02a2b5129cd1de164eb9cbd083e8a2503c4e"))
    (if (string=? result-hex expected)
        (print "✓ ChaCha20 block test PASSED")
        (begin
          (print "✗ ChaCha20 block test FAILED")
          (print "Expected: " expected)
          (print "Got:      " result-hex)))))

(define (test-chacha20-encryption)
  "Test ChaCha20 encryption (RFC 7539 Section 2.4.2)"
  (print "\nTesting ChaCha20 encryption...")
  (let* ((key "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f")
         (nonce "000000000000004a00000000")
         (counter 1)
         (plaintext "Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it.")
         (ciphertext (chacha20-encrypt key nonce counter plaintext))
         (ciphertext-hex (bytes->hex ciphertext))
         (expected "6e2e359a2568f98041ba0728dd0d6981e97e7aec1d4360c20a27afccfd9fae0bf91b65c5524733ab8f593dabcd62b3571639d624e65152ab8f530c359f0861d807ca0dbf500d6a6156a38e088a22b65e52bc514d16ccf806818ce91ab77937365af90bbf74a35be6b40b8eedf2785e42874d"))
    (if (string=? ciphertext-hex expected)
        (print "✓ ChaCha20 encryption test PASSED")
        (begin
          (print "✗ ChaCha20 encryption test FAILED")
          (print "Expected: " expected)
          (print "Got:      " ciphertext-hex)))))

;; ============================================================================
;; Demonstrations
;; ============================================================================

(define (demo-basic)
  "Basic ChaCha20 demonstration"
  (print "═══════════════════════════════════════════════════")
  (print "ChaCha20 Demo: Basic Encryption")
  (print "═══════════════════════════════════════════════════\n")

  (let* ((key "0000000000000000000000000000000000000000000000000000000000000000")
         (nonce "000000000000000000000000")
         (counter 0)
         (plaintext "Hello, Cyberspace! This is a secret message.")
         (ciphertext (chacha20-encrypt key nonce counter plaintext))
         (decrypted (chacha20-decrypt key nonce counter ciphertext)))

    (print "Key:        " key)
    (print "Nonce:      " nonce)
    (print "Counter:    " counter)
    (print "")
    (print "Plaintext:  " plaintext)
    (print "Ciphertext: " (bytes->hex ciphertext))
    (print "Decrypted:  " (u8vector->string decrypted))
    (print "")))

(define (demo-stream-cipher)
  "Demonstrate stream cipher properties"
  (print "═══════════════════════════════════════════════════")
  (print "ChaCha20 Demo: Stream Cipher Properties")
  (print "═══════════════════════════════════════════════════\n")

  (print "Property: Encryption and decryption are the same operation (XOR)")
  (print "")

  (let* ((key "0101010101010101010101010101010101010101010101010101010101010101")
         (nonce "000000000000000000000001")
         (counter 0)
         (message1 "First message")
         (message2 "Second one!!!")
         (cipher1 (chacha20-encrypt key nonce counter message1))
         (cipher2 (chacha20-encrypt key nonce counter message2)))

    (print "Same key/nonce, different messages:")
    (print "  Message 1:    " message1)
    (print "  Ciphertext 1: " (bytes->hex cipher1))
    (print "  Message 2:    " message2)
    (print "  Ciphertext 2: " (bytes->hex cipher2))
    (print "")
    (print "Warning: Never reuse nonce with same key!")
    (print "  (Two-time pad attack would reveal XOR of plaintexts)")
    (print "")))

(define (demo-nonce-importance)
  "Demonstrate importance of unique nonces"
  (print "═══════════════════════════════════════════════════")
  (print "ChaCha20 Demo: Nonce Must Be Unique")
  (print "═══════════════════════════════════════════════════\n")

  (let* ((key "0202020202020202020202020202020202020202020202020202020202020202")
         (nonce1 "000000000000000000000001")
         (nonce2 "000000000000000000000002")
         (counter 0)
         (message "Secret data"))

    (print "Same key, different nonces (correct usage):")
    (print "  Nonce 1: " nonce1)
    (print "  Cipher:  " (bytes->hex (chacha20-encrypt key nonce1 counter message)))
    (print "  Nonce 2: " nonce2)
    (print "  Cipher:  " (bytes->hex (chacha20-encrypt key nonce2 counter message)))
    (print "")
    (print "✓ Different ciphertexts → secure")
    (print "")
    (print "Security requirement: (key, nonce) pair must NEVER repeat")
    (print "  Typical approach: Random 96-bit nonce (2^96 ≈ 10^28 possible values)")
    (print "  Or: Counter-based nonce (increment for each message)")
    (print "")))

;; ============================================================================
;; CLI Interface
;; ============================================================================

(define (show-help)
  (display "╔═══════════════════════════════════════════════════════════════════╗\n")
  (display "║                  ChaCha20 STREAM CIPHER                           ║\n")
  (display "║                  RFC 7539 Implementation                          ║\n")
  (display "╚═══════════════════════════════════════════════════════════════════╝\n\n")
  (display "CONCEPT:\n")
  (display "  ChaCha20 = Fast, secure stream cipher using ARX operations\n")
  (display "  ARX = Add, Rotate, XOR (constant-time, no table lookups)\n")
  (display "  256-bit key + 96-bit nonce + 32-bit counter\n")
  (display "  20 rounds of quarter-round mixing\n")
  (display "\n")
  (display "USAGE:\n")
  (display "  ./chacha20.scm test              # Run RFC 7539 test vectors\n")
  (display "  ./chacha20.scm demo-basic        # Basic encryption demo\n")
  (display "  ./chacha20.scm demo-stream       # Stream cipher properties\n")
  (display "  ./chacha20.scm demo-nonce        # Nonce importance\n")
  (display "  ./chacha20.scm demo-all          # Run all demos\n")
  (display "\n")
  (display "SECURITY PROPERTIES:\n")
  (display "  ✓ Constant-time (no timing attacks)\n")
  (display "  ✓ Fast in software (ARX operations)\n")
  (display "  ✓ 256-bit security (quantum-resistant against Grover)\n")
  (display "  ✓ No weak keys\n")
  (display "  ✓ Provable security bounds\n")
  (display "\n")
  (display "REQUIREMENTS:\n")
  (display "  CRITICAL: Never reuse (key, nonce) pair\n")
  (display "  CRITICAL: Use random or counter-based nonces\n")
  (display "  CRITICAL: Use authenticated encryption (ChaCha20-Poly1305)\n")
  (display "\n")
  (display "PAPER:\n")
  (display "  D. J. Bernstein (2008) \"ChaCha, a variant of Salsa20\"\n")
  (display "  RFC 7539 (2015) \"ChaCha20 and Poly1305 for IETF Protocols\"\n")
  (display "  ~/cyberspace/library/cryptographers/djb/chacha20-2008.pdf\n")
  (display "\n"))

;; Main entry point
(when (not (null? (command-line-arguments)))
  (let ((cmd (car (command-line-arguments))))
    (cond
     ((string=? cmd "test")
      (test-quarter-round)
      (test-chacha20-block)
      (test-chacha20-encryption))
     ((string=? cmd "demo-basic") (demo-basic))
     ((string=? cmd "demo-stream") (demo-stream-cipher))
     ((string=? cmd "demo-nonce") (demo-nonce-importance))
     ((string=? cmd "demo-all")
      (demo-basic)
      (demo-stream-cipher)
      (demo-nonce-importance))
     (else (show-help)))))

;; REPL usage
(when (and (equal? (program-name) "csi")
           (null? (command-line-arguments)))
  (show-help)
  (print "REPL Functions:")
  (print "  (test-quarter-round)")
  (print "  (test-chacha20-block)")
  (print "  (test-chacha20-encryption)")
  (print "  (chacha20-encrypt key-hex nonce-hex counter plaintext)")
  (print "  (chacha20-decrypt key-hex nonce-hex counter ciphertext)")
  (print ""))
