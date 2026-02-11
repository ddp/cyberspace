;;; Test Crypto FFI - Chez Scheme Port
;;; Tests Ed25519, SHA-256, and basic crypto operations.

(import (rnrs)
        (only (chezscheme) printf format)
        (cyberspace chicken-compatibility blob)
        (cyberspace crypto-ffi))

(define (print . args) (for-each display args) (newline))

(print "=== SPKI Scheme Crypto FFI Test ===")
(print "")

;; Initialize libsodium
(print "Initializing libsodium...")
(let ((result (sodium-init)))
  (cond
   ((= result 0) (print "✓ libsodium initialized"))
   ((= result 1) (print "✓ libsodium already initialized"))
   (else (error 'test-crypto "Failed to initialize libsodium"))))

;; Generate keypair
(print "")
(print "Generating Ed25519 keypair...")
(define keypair (ed25519-keypair))
(define public-key (car keypair))
(define secret-key (cadr keypair))
(printf "✓ Generated keypair (pk: ~a bytes, sk: ~a bytes)~n"
        (bytevector-length public-key)
        (bytevector-length secret-key))

;; Sign a message
(define message "The Library of Cyberspace")
(print "")
(print "Signing message: \"" message "\"")
(define signature (ed25519-sign secret-key message))
(printf "✓ Generated signature (~a bytes)~n" (bytevector-length signature))

;; Verify the signature
(print "")
(print "Verifying signature...")
(define valid? (ed25519-verify public-key message signature))
(if valid?
    (print "✓ Signature verified successfully")
    (error 'test-crypto "CRITICAL: Valid signature failed verification!"))

;; Test tampering detection
(print "")
(print "Testing tampering detection...")
(define tampered-message "The Library of Cyberspace!")
(define tampered-valid? (ed25519-verify public-key tampered-message signature))
(if (not tampered-valid?)
    (print "✓ Tampered message correctly rejected")
    (error 'test-crypto "CRITICAL: Tampered message accepted!"))

;; Test wrong public key
(print "")
(print "Testing wrong public key detection...")
(define wrong-keypair (ed25519-keypair))
(define wrong-public-key (car wrong-keypair))
(define wrong-key-valid? (ed25519-verify wrong-public-key message signature))
(if (not wrong-key-valid?)
    (print "✓ Wrong public key correctly rejected")
    (error 'test-crypto "CRITICAL: Signature verified with wrong key!"))

;; Test SHA-256 hash
(print "")
(print "Testing SHA-256 hash...")
(define hash (sha256-hash message))
(printf "✓ SHA-256 hash (~a bytes)~n" (bytevector-length hash))

;; Display results summary
(print "")
(print "=== All Scheme Crypto FFI tests passed ===")
(print "TCB guarantees verified:")
(print "  1. Signature correctness: sign/verify round-trip works")
(print "  2. Unforgeability: tampered message rejected")
(print "  3. Key binding: wrong key rejected")
