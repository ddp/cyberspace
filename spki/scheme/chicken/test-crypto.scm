#!/usr/bin/env csi -s
;;; SPKI Scheme - Test Crypto FFI
;;;
;;; Tests that Chicken Scheme can call libsodium for Ed25519 operations.
;;; This verifies the Scheme side of the SPKI implementation.

(import (chicken base)
        (chicken format)
        crypto-ffi)

(print "=== SPKI Scheme Crypto FFI Test ===\n")

;; Initialize libsodium
(print "Initializing libsodium...")
(let ((result (sodium-init)))
  (cond
   ((= result 0) (print "✓ libsodium initialized"))
   ((= result 1) (print "✓ libsodium already initialized"))
   (else (error "Failed to initialize libsodium"))))

;; Generate keypair
(print "\nGenerating Ed25519 keypair...")
(define keypair (ed25519-keypair))
(define public-key (car keypair))
(define secret-key (cdr keypair))
(printf "✓ Generated keypair (pk: ~a bytes, sk: ~a bytes)\n"
        (u8vector-length public-key)
        (u8vector-length secret-key))

;; Sign a message
(define message "The Library of Cyberspace")
(print "\nSigning message: \"" message "\"")
(define signature (ed25519-sign secret-key message))
(printf "✓ Generated signature (~a bytes)\n" (u8vector-length signature))

;; Verify the signature
(print "\nVerifying signature...")
(define valid? (ed25519-verify public-key message signature))
(if valid?
    (print "✓ Signature verified successfully")
    (error "CRITICAL: Valid signature failed verification!"))

;; Test tampering detection
(print "\nTesting tampering detection...")
(define tampered-message "The Library of Cyberspace!")  ; added '!'
(define tampered-valid? (ed25519-verify public-key tampered-message signature))
(if (not tampered-valid?)
    (print "✓ Tampered message correctly rejected")
    (error "CRITICAL: Tampered message accepted!"))

;; Test wrong public key
(print "\nTesting wrong public key detection...")
(define wrong-keypair (ed25519-keypair))
(define wrong-public-key (car wrong-keypair))
(define wrong-key-valid? (ed25519-verify wrong-public-key message signature))
(if (not wrong-key-valid?)
    (print "✓ Wrong public key correctly rejected")
    (error "CRITICAL: Signature verified with wrong key!"))

;; Test SHA-256 hash
(print "\nTesting SHA-256 hash...")
(define hash (sha256-hash message))
(printf "✓ SHA-256 hash (~a bytes)\n" (u8vector-length hash))

;; Display results summary
(print "\n=== All Scheme Crypto FFI tests passed ===")
(print "TCB guarantees verified:")
(print "  1. Signature correctness: sign/verify round-trip works")
(print "  2. Unforgeability: tampered message rejected")
(print "  3. Key binding: wrong key rejected")
(print "\nScheme layer can now implement SPKI policy on top of verified crypto.")
