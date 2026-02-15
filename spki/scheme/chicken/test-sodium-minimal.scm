#!/usr/bin/env csi -s
;;; SPKI Scheme - Minimal libsodium test
;;;
;;; Test that libsodium FFI works without any display complications.

(import (chicken base)
        (chicken foreign)
        (chicken string)
        srfi-4)

;; Include libsodium header
(foreign-declare "#include <sodium.h>")

;; Test 1: Initialize
(define init-result ((foreign-lambda int "sodium_init")))
(if (< init-result 0)
    (begin
      (print "FAILED: Could not initialize libsodium")
      (exit 1)))

;; Test 2: Generate keypair
(define pk (make-u8vector 32))
(define sk (make-u8vector 64))
(define keypair-result
  ((foreign-lambda int "crypto_sign_keypair" scheme-pointer scheme-pointer) pk sk))
(if (not (= keypair-result 0))
    (begin
      (print "FAILED: Could not generate keypair")
      (exit 1)))

;; Helper: convert string to u8vector
(define (string->bytes str)
  (let* ((len (string-length str))
         (vec (make-u8vector len)))
    (do ((i 0 (+ i 1)))
        ((= i len) vec)
      (u8vector-set! vec i (char->integer (string-ref str i))))))

;; Test 3: Sign message
(define message (string->bytes "The Library of Cyberspace"))
(define message-len (u8vector-length message))
(define signature (make-u8vector 64))
(define sig-len (make-u8vector 8))

(define sign-result
  ((foreign-lambda int "crypto_sign_detached"
                   scheme-pointer scheme-pointer scheme-pointer
                   unsigned-integer scheme-pointer)
   signature sig-len message message-len sk))
(if (not (= sign-result 0))
    (begin
      (print "FAILED: Could not sign message")
      (exit 1)))

;; Test 4: Verify signature
(define verify-result
  ((foreign-lambda int "crypto_sign_verify_detached"
                   scheme-pointer scheme-pointer unsigned-integer scheme-pointer)
   signature message message-len pk))
(if (not (= verify-result 0))
    (begin
      (print "FAILED: Signature verification failed")
      (exit 1)))

;; Test 5: Detect tampering
(define tampered (string->bytes "The Library of Cyberspace!"))
(define tampered-len (u8vector-length tampered))
(define tampered-result
  ((foreign-lambda int "crypto_sign_verify_detached"
                   scheme-pointer scheme-pointer unsigned-integer scheme-pointer)
   signature tampered tampered-len pk))
(if (= tampered-result 0)
    (begin
      (print "FAILED: Tampered message was accepted!")
      (exit 1)))

;; Test 6: SHA-512
(define hash (make-u8vector 64))
(define hash-result
  ((foreign-lambda int "crypto_hash_sha512"
                   scheme-pointer scheme-pointer unsigned-integer)
   hash message message-len))
(if (not (= hash-result 0))
    (begin
      (print "FAILED: Could not compute SHA-512 hash")
      (exit 1)))

;; All tests passed
(print "✓ All Scheme crypto tests PASSED")
(print "  - libsodium initialized")
(print "  - Ed25519 keypair generated")
(print "  - Message signed")
(print "  - Signature verified")
(print "  - Tampered message rejected")
(print "  - SHA-512 hash computed")
(print "")
(print "Chicken Scheme can call libsodium directly.")
(print "Ready to implement SPKI policy layer in Scheme.")
