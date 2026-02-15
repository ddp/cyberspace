#!/usr/bin/env csi -s
;;; SPKI Scheme - Direct libsodium test
;;;
;;; Minimal test to verify Chicken Scheme can call libsodium.

(import (chicken base)
        (chicken foreign)
        srfi-4)

;; Include libsodium header
(foreign-declare "#include <sodium.h>")

(print "=== Testing libsodium from Chicken Scheme ===\n")

;; Test 1: Initialize libsodium
(print "1. Initializing libsodium...")
(define init-result
  ((foreign-lambda int "sodium_init")))
(if (>= init-result 0)
    (print "   ✓ libsodium initialized (result: " init-result ")")
    (print "   ✗ FAILED to initialize"))

;; Test 2: Generate keypair
(print "\n2. Generating Ed25519 keypair...")
(define pk (make-u8vector 32))
(define sk (make-u8vector 64))
(define keypair-result
  ((foreign-lambda int "crypto_sign_keypair" scheme-pointer scheme-pointer)
   pk sk))
(if (= keypair-result 0)
    (begin
      (print "   ✓ Keypair generated")
      (display "   Public key length: ")
      (display (u8vector-length pk))
      (display " bytes")
      (newline))
    (print "   ✗ FAILED to generate keypair"))

;; Test 3: Sign a message
(print "\n3. Signing message...")
(define message (string->utf8 "The Library of Cyberspace"))
(define message-len (u8vector-length message))
(define signature (make-u8vector 64))
(define sig-len (make-u8vector 8))  ; unsigned long long*

(define sign-result
  ((foreign-lambda int "crypto_sign_detached"
                   scheme-pointer    ; signature
                   scheme-pointer    ; sig_len (out)
                   scheme-pointer    ; message
                   unsigned-integer  ; message_len
                   scheme-pointer)   ; secret_key
   signature sig-len message message-len sk))

(if (= sign-result 0)
    (begin
      (print "   ✓ Message signed")
      (display "   Signature length: ")
      (display (u8vector-length signature))
      (display " bytes")
      (newline))
    (print "   ✗ FAILED to sign message"))

;; Test 4: Verify signature
(print "\n4. Verifying signature...")
(define verify-result
  ((foreign-lambda int "crypto_sign_verify_detached"
                   scheme-pointer    ; signature
                   scheme-pointer    ; message
                   unsigned-integer  ; message_len
                   scheme-pointer)   ; public_key
   signature message message-len pk))

(if (= verify-result 0)
    (print "   ✓ Signature verified successfully")
    (print "   ✗ FAILED to verify signature"))

;; Test 5: Detect tampering
(print "\n5. Testing tamper detection...")
(define tampered-message (string->utf8 "The Library of Cyberspace!"))
(define tampered-len (u8vector-length tampered-message))
(define tampered-result
  ((foreign-lambda int "crypto_sign_verify_detached"
                   scheme-pointer scheme-pointer unsigned-integer scheme-pointer)
   signature tampered-message tampered-len pk))

(if (not (= tampered-result 0))
    (print "   ✓ Tampered message correctly rejected")
    (print "   ✗ FAILED - tampered message accepted!"))

;; Test 6: SHA-512 hash
(print "\n6. Testing SHA-512 hash...")
(define hash (make-u8vector 64))
(define hash-result
  ((foreign-lambda int "crypto_hash_sha512"
                   scheme-pointer    ; hash (out)
                   scheme-pointer    ; data
                   unsigned-integer) ; data_len
   hash message message-len))

(if (= hash-result 0)
    (begin
      (print "   ✓ SHA-512 hash computed")
      (display "   Hash length: ")
      (display (u8vector-length hash))
      (display " bytes")
      (newline))
    (print "   ✗ FAILED to compute hash"))

(print "\n=== All tests completed ===")
