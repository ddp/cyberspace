#!/usr/bin/env csi -s
;; Lamport Signatures
;; Hash-based one-time digital signature scheme
;;
;; Paper: Leslie Lamport (1979), "Constructing Digital Signatures from a One-Way Function"
;; Source: ~/cyberspace/library/cryptographers/lamport/
;;
;; Concept: Digital signatures using only hash functions
;;   - Quantum-resistant (no number theory, only hashing)
;;   - One-time use (must generate new keypair for each signature)
;;   - Large signatures (256 hashes × 2 × 32 bytes = 16 KB)
;;   - Foundation for modern hash-based signatures (SPHINCS+, XMSS)
;;
;; "We show how to construct a digital signature from any one-way function."
;; —Leslie Lamport, 1979

(import scheme)
(import (chicken base))
(import (chicken io))
(import (chicken file))
(import (chicken process))
(import (chicken string))
(import (chicken process-context))
(import srfi-1)
(import srfi-13)

;; ============================================================================
;; Cryptographic Primitives
;; ============================================================================

(define (random-bytes n)
  "Generate n random bytes as hex string"
  (let ((result (with-input-from-pipe
                 (string-append "openssl rand -hex " (number->string n))
                 read-line)))
    result))

(define (sha256 text)
  "Compute SHA-256 hash"
  (let ((result (with-input-from-pipe
                 (string-append "echo -n '" (escape-shell text) "' | openssl dgst -sha256 -hex")
                 read-line)))
    (if result
        (string-trim-both (car (reverse (string-split result " "))))
        #f)))

(define (escape-shell text)
  "Escape single quotes for shell"
  (string-translate* text '(("'" . "'\"'\"'"))))

;; ============================================================================
;; Lamport Signature Key Generation
;; ============================================================================

(define (generate-lamport-keypair bits)
  "Generate Lamport signature keypair for 'bits'-bit messages

   For each bit of the message, we need TWO random values:
   - One for bit=0
   - One for bit=1

   Private key: 2×bits random values
   Public key: SHA-256 hash of each private key value"

  (let ((private-key '())
        (public-key '()))

    ;; For each bit position
    (do ((i 0 (+ i 1)))
        ((= i bits))

      ;; Generate two random 256-bit (32-byte) values
      (let ((private-0 (random-bytes 32))
            (private-1 (random-bytes 32)))

        ;; Hash them for public key
        (let ((public-0 (sha256 private-0))
              (public-1 (sha256 private-1)))

          ;; Store in key structures
          (set! private-key (append private-key
                                   (list (list private-0 private-1))))
          (set! public-key (append public-key
                                  (list (list public-0 public-1)))))))

    (list private-key public-key)))

;; ============================================================================
;; Message Hashing
;; ============================================================================

(define (message-to-bits message)
  "Convert message to 256 bits via SHA-256 hashing"
  (let* ((hash (sha256 message))
         ;; Convert hex string to binary string
         (bits (apply string-append
                     (map (lambda (hex-char)
                            (let ((val (string->number (string hex-char) 16)))
                              (let loop ((n val) (acc '()) (count 0))
                                (if (= count 4)
                                    (apply string acc)
                                    (loop (quotient n 2)
                                          (cons (if (even? n) #\0 #\1) acc)
                                          (+ count 1))))))
                          (string->list hash)))))
    bits))

;; ============================================================================
;; Signing
;; ============================================================================

(define (sign-message private-key message)
  "Sign message with Lamport private key

   For each bit of the message hash:
   - If bit is 0: reveal private-key[i][0]
   - If bit is 1: reveal private-key[i][1]

   Signature = list of revealed private key values"

  (let ((bits (message-to-bits message))
        (signature '()))

    ;; For each bit
    (do ((i 0 (+ i 1)))
        ((= i (string-length bits)) signature)

      (let ((bit (string-ref bits i))
            (key-pair (list-ref private-key i)))

        ;; Select private key based on bit value
        (set! signature
          (append signature
                 (list (if (char=? bit #\0)
                          (car key-pair)   ; bit 0
                          (cadr key-pair)  ; bit 1
                          ))))))))

;; ============================================================================
;; Verification
;; ============================================================================

(define (verify-signature public-key message signature)
  "Verify Lamport signature

   For each bit of the message hash:
   - If bit is 0: check that SHA-256(signature[i]) == public-key[i][0]
   - If bit is 1: check that SHA-256(signature[i]) == public-key[i][1]

   All checks must pass for valid signature"

  (let ((bits (message-to-bits message)))

    ;; Check each bit
    (let loop ((i 0))
      (cond
       ;; All bits checked - valid!
       ((= i (string-length bits)) #t)

       ;; Check this bit
       (else
        (let ((bit (string-ref bits i))
              (sig-value (list-ref signature i))
              (pub-pair (list-ref public-key i)))

          ;; Hash signature value
          (let ((sig-hash (sha256 sig-value)))

            ;; Compare with appropriate public key
            (let ((expected (if (char=? bit #\0)
                               (car pub-pair)
                               (cadr pub-pair))))

              (if (string=? sig-hash expected)
                  (loop (+ i 1))  ; Continue checking
                  #f)))))))))      ; Mismatch - invalid!

;; ============================================================================
;; Key Storage
;; ============================================================================

(define (save-private-key filename private-key)
  "Save private key to file"
  (with-output-to-file filename
    (lambda ()
      (for-each (lambda (pair)
                  (display (car pair))
                  (display " ")
                  (display (cadr pair))
                  (newline))
               private-key))))

(define (save-public-key filename public-key)
  "Save public key to file"
  (with-output-to-file filename
    (lambda ()
      (for-each (lambda (pair)
                  (display (car pair))
                  (display " ")
                  (display (cadr pair))
                  (newline))
               public-key))))

(define (load-private-key filename)
  "Load private key from file"
  (with-input-from-file filename
    (lambda ()
      (let loop ((pairs '()))
        (let ((line (read-line)))
          (if (eof-object? line)
              (reverse pairs)
              (let ((parts (string-split line " ")))
                (loop (cons (list (car parts) (cadr parts)) pairs)))))))))

(define (load-public-key filename)
  "Load public key from file"
  (load-private-key filename))  ; Same format

(define (save-signature filename signature)
  "Save signature to file"
  (with-output-to-file filename
    (lambda ()
      (for-each (lambda (value)
                  (display value)
                  (newline))
               signature))))

(define (load-signature filename)
  "Load signature from file"
  (with-input-from-file filename
    (lambda ()
      (let loop ((values '()))
        (let ((line (read-line)))
          (if (eof-object? line)
              (reverse values)
              (loop (cons line values))))))))

;; ============================================================================
;; Demonstrations
;; ============================================================================

(define (demo-basic)
  "Basic Lamport signature demonstration"
  (print "═══════════════════════════════════════════════════")
  (print "Lamport Signatures: Hash-Based Digital Signatures")
  (print "═══════════════════════════════════════════════════\n")

  (print "1. Generate keypair (256-bit message → 256 × 2 private values)")
  (let* ((keys (generate-lamport-keypair 256))
         (private-key (car keys))
         (public-key (cadr keys)))

    (print "   Private key: 256 pairs of 32-byte random values (16 KB)")
    (print "   Public key:  256 pairs of 32-byte hashes (16 KB)")
    (print "")

    (print "2. Sign message")
    (let* ((message "Hello, Lamport Signatures!")
           (signature (sign-message private-key message)))

      (print "   Message:   " message)
      (print "   Signature: 256 revealed private key values (8 KB)")
      (print "")

      (print "3. Verify signature")
      (let ((valid (verify-signature public-key message signature)))
        (print "   Valid: " valid)
        (print "   ✓ Signature verification " (if valid "PASSED" "FAILED"))
        (print ""))

      (print "4. Try to verify wrong message")
      (let ((valid2 (verify-signature public-key "Wrong message" signature)))
        (print "   Message: Wrong message")
        (print "   Valid:   " valid2)
        (print "   ✓ Wrong message correctly " (if valid2 "accepted (BAD!)" "rejected"))
        (print "")))))

(define (demo-one-time)
  "Demonstrate one-time use requirement"
  (print "═══════════════════════════════════════════════════")
  (print "Lamport Signatures: One-Time Use Requirement")
  (print "═══════════════════════════════════════════════════\n")

  (print "Why Lamport signatures are ONE-TIME only:")
  (print "")

  (let* ((keys (generate-lamport-keypair 256))
         (private-key (car keys))
         (public-key (cadr keys)))

    (print "1. Sign first message")
    (let* ((msg1 "First message")
           (sig1 (sign-message private-key msg1)))
      (print "   Message:  " msg1)
      (print "   Reveals:  256 private key values (one per bit)")
      (print "")

      (print "2. Sign second message with SAME keypair")
      (let* ((msg2 "Second message")
             (sig2 (sign-message private-key msg2)))
        (print "   Message:  " msg2)
        (print "   Reveals:  256 more private key values")
        (print "")

        (print "3. Information leakage analysis")
        (print "   - Both signatures reveal parts of private key")
        (print "   - Attacker learns BOTH values for some bit positions")
        (print "   - Can forge signatures for messages with those bit patterns!")
        (print "")

        (print "SECURITY REQUIREMENT:")
        (print "  ✗ NEVER sign two messages with the same keypair")
        (print "  ✓ Generate NEW keypair for each signature")
        (print "  ✓ Or use Merkle tree signatures (XMSS, SPHINCS+)")
        (print "")))))

(define (demo-quantum-resistance)
  "Explain quantum resistance"
  (print "═══════════════════════════════════════════════════")
  (print "Lamport Signatures: Post-Quantum Security")
  (print "═══════════════════════════════════════════════════\n")

  (print "Why Lamport signatures resist quantum computers:")
  (print "")

  (print "Classical signatures (RSA, ECDSA):")
  (print "  - Based on number theory (factoring, discrete log)")
  (print "  - Shor's algorithm (quantum) breaks them efficiently")
  (print "  - Security: BROKEN by quantum computers")
  (print "")

  (print "Lamport signatures:")
  (print "  - Based on hash functions (SHA-256)")
  (print "  - No number theory involved")
  (print "  - Best quantum attack: Grover's algorithm (√n speedup)")
  (print "  - Security: 256-bit hash → 128-bit quantum security")
  (print "  - Still secure! (2^128 operations infeasible)")
  (print "")

  (print "Modern evolution:")
  (print "  Lamport (1979) → Merkle Trees (1987) → XMSS (2011) → SPHINCS+ (2015)")
  (print "  └─ One-time    └─ Many signatures   └─ Stateless   └─ NIST finalist")
  (print "")

  (print "NIST Post-Quantum Competition:")
  (print "  - SPHINCS+ selected as hash-based signature standard (2022)")
  (print "  - Based on Lamport's 1979 insight: hash functions suffice")
  (print "  - 40+ years from paper to quantum-resistant standard")
  (print ""))

;; ============================================================================
;; CLI Interface
;; ============================================================================

(define (show-help)
  (display "╔═══════════════════════════════════════════════════════════════════╗\n")
  (display "║            LAMPORT DIGITAL SIGNATURES                             ║\n")
  (display "║            Hash-Based One-Time Signatures                         ║\n")
  (display "╚═══════════════════════════════════════════════════════════════════╝\n\n")
  (display "CONCEPT:\n")
  (display "  Lamport signatures = Digital signatures using only hash functions\n")
  (display "  Quantum-resistant (no number theory, only hashing)\n")
  (display "  One-time use (must generate new keypair for each message)\n")
  (display "  Foundation for modern post-quantum signatures\n")
  (display "\n")
  (display "USAGE:\n")
  (display "  ./lamport-sigs.scm demo-basic     # Basic signing/verification\n")
  (display "  ./lamport-sigs.scm demo-onetime   # One-time use requirement\n")
  (display "  ./lamport-sigs.scm demo-quantum   # Post-quantum security\n")
  (display "  ./lamport-sigs.scm demo-all       # Run all demos\n")
  (display "\n")
  (display "  ./lamport-sigs.scm keygen <name>             # Generate keypair\n")
  (display "  ./lamport-sigs.scm sign <private-key> <msg>  # Sign message\n")
  (display "  ./lamport-sigs.scm verify <public-key> <sig> <msg>  # Verify\n")
  (display "\n")
  (display "SECURITY PROPERTIES:\n")
  (display "  ✓ Quantum-resistant (hash-based, not number theory)\n")
  (display "  ✓ Simple (only needs hash function)\n")
  (display "  ✓ Provably secure (one-way function assumption)\n")
  (display "  ✗ One-time only (reuse reveals private key)\n")
  (display "  ✗ Large (16 KB keys, 8 KB signatures)\n")
  (display "\n")
  (display "PAPER:\n")
  (display "  Leslie Lamport (1979) \"Constructing Digital Signatures from a\n")
  (display "    One-Way Function\"\n")
  (display "  ~/cyberspace/library/cryptographers/lamport/\n")
  (display "\n"))

;; Main entry point
(when (not (null? (command-line-arguments)))
  (let ((cmd (car (command-line-arguments))))
    (cond
     ((string=? cmd "demo-basic") (demo-basic))
     ((string=? cmd "demo-onetime") (demo-one-time))
     ((string=? cmd "demo-quantum") (demo-quantum-resistance))
     ((string=? cmd "demo-all")
      (demo-basic)
      (demo-one-time)
      (demo-quantum-resistance))

     ;; Keygen
     ((string=? cmd "keygen")
      (if (< (length (command-line-arguments)) 2)
          (print "Usage: ./lamport-sigs.scm keygen <name>")
          (let* ((name (cadr (command-line-arguments)))
                 (keys (generate-lamport-keypair 256))
                 (private-key (car keys))
                 (public-key (cadr keys))
                 (priv-file (string-append name ".private"))
                 (pub-file (string-append name ".public")))
            (save-private-key priv-file private-key)
            (save-public-key pub-file public-key)
            (print "Generated keypair:")
            (print "  Private key: " priv-file " (KEEP SECRET!)")
            (print "  Public key:  " pub-file)
            (print "")
            (print "WARNING: This keypair can sign ONE message only!"))))

     ;; Sign
     ((string=? cmd "sign")
      (if (< (length (command-line-arguments)) 3)
          (print "Usage: ./lamport-sigs.scm sign <private-key-file> <message>")
          (let* ((priv-file (cadr (command-line-arguments)))
                 (message (caddr (command-line-arguments)))
                 (private-key (load-private-key priv-file))
                 (signature (sign-message private-key message))
                 (sig-file (string-append priv-file ".sig")))
            (save-signature sig-file signature)
            (print "Signed message: " message)
            (print "Signature: " sig-file)
            (print "")
            (print "WARNING: You have now USED this private key!")
            (print "         NEVER sign another message with it!"))))

     ;; Verify
     ((string=? cmd "verify")
      (if (< (length (command-line-arguments)) 4)
          (print "Usage: ./lamport-sigs.scm verify <public-key-file> <signature-file> <message>")
          (let* ((pub-file (cadr (command-line-arguments)))
                 (sig-file (caddr (command-line-arguments)))
                 (message (cadddr (command-line-arguments)))
                 (public-key (load-public-key pub-file))
                 (signature (load-signature sig-file))
                 (valid (verify-signature public-key message signature)))
            (print "Message:   " message)
            (print "Signature: " (if valid "VALID ✓" "INVALID ✗"))
            (if (not valid)
                (print "\nWARNING: Signature verification FAILED!")))))

     (else (show-help)))))

;; REPL usage
(when (and (equal? (program-name) "csi")
           (null? (command-line-arguments)))
  (show-help)
  (print "REPL Functions:")
  (print "  (generate-lamport-keypair 256)")
  (print "  (sign-message private-key message)")
  (print "  (verify-signature public-key message signature)")
  (print ""))
