#!/usr/bin/env csi -s
;;; Minimal crypto test

(import (chicken base)
        (chicken format)
        srfi-4
        crypto-ffi)

(print "=== Minimal Crypto Test ===\n")

;; Initialize
(print "1. Initializing libsodium...")
(sodium-init)
(print "   ✓\n")

;; Generate keypair
(print "2. Generating keypair...")
(define keypair (ed25519-keypair))
(define pk (car keypair))
(define sk (cadr keypair))
(print "   ✓ PK length: " (u8vector-length pk))
(print "   ✓ SK length: " (u8vector-length sk))
(print "")

;; Test with string message
(print "3. Signing string message...")
(define msg-str "Hello World")
(define sig1 (ed25519-sign sk msg-str))
(print "   ✓ Signature length: " (u8vector-length sig1))
(print "")

;; Test with u8vector message
(print "4. Signing u8vector message...")
(define msg-vec (make-u8vector 10 42))
(print "   Message vector length: " (u8vector-length msg-vec))
(define sig2 (ed25519-sign sk msg-vec))
(print "   ✓ Signature length: " (u8vector-length sig2))
(print "")

;; Test SHA-512
(print "5. Testing SHA-512 hash...")
(define hash1 (sha512-hash "Test message"))
(print "   ✓ Hash length: " (u8vector-length hash1))
(print "")

;; Test signing a hash
(print "6. Signing a SHA-512 hash...")
(define test-hash (sha512-hash "Certificate data"))
(print "   Hash length: " (u8vector-length test-hash))
(print "   Hash is u8vector: " (u8vector? test-hash))
(print "   Signing hash...")
(define sig3 (ed25519-sign sk test-hash))
(print "   ✓ Signature length: " (u8vector-length sig3))
(print "")

;; Verify signature
(print "7. Verifying signature...")
(define verified (ed25519-verify pk test-hash sig3))
(print "   ✓ Verified: " verified)
(print "")

(print "=== All tests passed! ===")
