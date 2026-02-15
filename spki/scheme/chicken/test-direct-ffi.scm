#!/usr/bin/env csi -s
(import (chicken base)
        (chicken foreign)
        srfi-4)

(foreign-declare "#include <sodium.h>")

;; Initialize
((foreign-lambda int "sodium_init"))

;; Create vectors
(define pk (make-u8vector 32))
(define sk (make-u8vector 64))

(display "Before call:\n")
(display "  pk is u8vector?: ")
(display (u8vector? pk))
(display "\n")

;; Call directly
(define result
  ((foreign-lambda int "crypto_sign_keypair" scheme-pointer scheme-pointer)
   pk sk))

(display "After call:\n")
(display "  result: ")
(display result)
(display "\n")
(display "  pk is u8vector?: ")
(display (u8vector? pk))
(display "\n")

(if (u8vector? pk)
    (begin
      (display "SUCCESS! pk is still a u8vector\n")
      (display "PK length: ")
      (display (u8vector-length pk))
      (display "\n"))
    (display "FAILED: pk is not a u8vector\n"))

(exit 0)
