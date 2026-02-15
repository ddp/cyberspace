#!/usr/bin/env csi -s
(import (chicken base)
        (chicken foreign)
        (chicken string)
        srfi-4)

(foreign-declare "#include <sodium.h>")

;; Initialize
((foreign-lambda int "sodium_init"))

;; Generate keypair
(define pk (make-u8vector 32))
(define sk (make-u8vector 64))
((foreign-lambda int "crypto_sign_keypair" scheme-pointer scheme-pointer) pk sk)

;; DON'T check if u8vector, just USE them

;; Create message
(define (string->bytes str)
  (let* ((len (string-length str))
         (vec (make-u8vector len)))
    (do ((i 0 (+ i 1)))
        ((= i len) vec)
      (u8vector-set! vec i (char->integer (string-ref str i))))))

(define message (string->bytes "Test"))
(define message-len (u8vector-length message))
(define signature (make-u8vector 64))
(define sig-len (make-u8vector 8))

;; Sign using pk and sk WITHOUT checking their type first
(define sign-result
  ((foreign-lambda int "crypto_sign_detached"
                   scheme-pointer scheme-pointer scheme-pointer
                   unsigned-integer scheme-pointer)
   signature sig-len message message-len sk))

(if (= sign-result 0)
    (print "SUCCESS: Signed message using sk!")
    (print "FAILED: Could not sign"))

;; Try to verify
(define verify-result
  ((foreign-lambda int "crypto_sign_verify_detached"
                   scheme-pointer scheme-pointer
                   unsigned-integer scheme-pointer)
   signature message message-len pk))

(if (= verify-result 0)
    (print "SUCCESS: Verified signature using pk!")
    (print "FAILED: Could not verify"))
