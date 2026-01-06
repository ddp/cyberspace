#!/usr/bin/env csi -s
;;; SPKI Scheme - Simple Crypto FFI Test (no modules)
;;;
;;; Tests that Chicken Scheme can call libsodium for Ed25519 operations.

(import (chicken base)
        (chicken format)
        (chicken foreign)
        srfi-4)

;; Include libsodium header
(foreign-declare "#include <sodium.h>")

;; Constants from libsodium
(define crypto-sign-publickeybytes 32)
(define crypto-sign-secretkeybytes 64)
(define crypto-sign-bytes 64)
(define crypto-hash-sha256-bytes 32)

;; Initialize libsodium
(define sodium-init
  (foreign-lambda int "sodium_init"))

;; Generate Ed25519 keypair
(define (ed25519-keypair)
  (let ((pk (make-u8vector crypto-sign-publickeybytes))
        (sk (make-u8vector crypto-sign-secretkeybytes)))
    ((foreign-lambda int "crypto_sign_keypair"
                    scheme-pointer scheme-pointer)
     pk sk)
    (cons pk sk)))

;; Sign message with Ed25519
(define (ed25519-sign secret-key message)
  (let* ((msg-bytes (if (string? message)
                        (string->u8vector message)
                        message))
         (signature (make-u8vector crypto-sign-bytes))
         (sig-len-ptr (make-u8vector 8)))
    ((foreign-lambda int "crypto_sign_detached"
                    scheme-pointer scheme-pointer scheme-pointer
                    unsigned-integer scheme-pointer)
     signature sig-len-ptr msg-bytes (u8vector-length msg-bytes) secret-key)
    signature))

;; Verify Ed25519 signature
(define (ed25519-verify public-key message signature)
  (let* ((msg-bytes (if (string? message)
                        (string->u8vector message)
                        message))
         (result ((foreign-lambda int "crypto_sign_verify_detached"
                                 scheme-pointer scheme-pointer
                                 unsigned-integer scheme-pointer)
                  signature msg-bytes (u8vector-length msg-bytes) public-key)))
    (= result 0)))

;; Compute SHA-256 hash
(define (sha256-hash data)
  (let* ((data-bytes (if (string? data)
                         (string->u8vector data)
                         data))
         (hash (make-u8vector crypto-hash-sha256-bytes)))
    ((foreign-lambda int "crypto_hash_sha256"
                    scheme-pointer scheme-pointer unsigned-integer)
     hash data-bytes (u8vector-length data-bytes))
    hash))

;; Helper: convert string to u8vector
(define (string->u8vector str)
  (let* ((len (string-length str))
         (vec (make-u8vector len)))
    (do ((i 0 (+ i 1)))
        ((= i len) vec)
      (u8vector-set! vec i (char->integer (string-ref str i))))))

;;; Run tests

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
(display "✓ Generated keypair (pk: ")
(display (u8vector-length public-key))
(display " bytes, sk: ")
(display (u8vector-length secret-key))
(display " bytes)")
(newline)

;; Sign a message
(define message "The Library of Cyberspace")
(newline)
(display "Signing message: \"")
(display message)
(display "\"")
(newline)
(define signature (ed25519-sign secret-key message))
(display "✓ Generated signature (")
(display (u8vector-length signature))
(display " bytes)")
(newline)

;; Verify the signature
(print "\nVerifying signature...")
(define valid? (ed25519-verify public-key message signature))
(if valid?
    (print "✓ Signature verified successfully")
    (error "CRITICAL: Valid signature failed verification!"))

;; Test tampering detection
(print "\nTesting tampering detection...")
(define tampered-message "The Library of Cyberspace!")
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
(display "✓ SHA-256 hash (")
(display (u8vector-length hash))
(display " bytes)")
(newline)

;; Display results summary
(print "\n=== All Scheme Crypto FFI tests passed ===")
(print "TCB guarantees verified:")
(print "  1. Signature correctness: sign/verify round-trip works")
(print "  2. Unforgeability: tampered message rejected")
(print "  3. Key binding: wrong key rejected")
(print "\nScheme layer can now implement SPKI policy on top of verified crypto.")
