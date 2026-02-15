#!/usr/bin/env csi -s
(import (chicken base)
        (chicken foreign)
        (chicken string)
        srfi-4)

(foreign-declare "#include <sodium.h>")

;; Initialize
(define init-result ((foreign-lambda int "sodium_init")))
(if (< init-result 0)
    (begin
      (print "FAILED: Could not initialize libsodium")
      (exit 1)))

;; Generate keypair
(define pk (make-u8vector 32))
(define sk (make-u8vector 64))
(define keypair-result
  ((foreign-lambda int "crypto_sign_keypair" scheme-pointer scheme-pointer) pk sk))
(if (not (= keypair-result 0))
    (begin
      (print "FAILED: Could not generate keypair")
      (exit 1)))

(print "✓ Keypair generated")
(print "  PK is u8vector?: " (u8vector? pk))
(print "  SK is u8vector?: " (u8vector? sk))
(print "  PK length: " (u8vector-length pk))
(print "  SK length: " (u8vector-length sk))
