#!/usr/bin/env csi -s
(import (chicken base)
        srfi-4
        crypto-ffi)

;; Initialize
(sodium-init)

;; Generate keypair using values
(define-values (pk sk) (ed25519-keypair))

;; Check they're u8vectors
(if (not (u8vector? pk))
    (begin
      (display "ERROR: pk is not a u8vector\n")
      (exit 1)))

(if (not (u8vector? sk))
    (begin
      (display "ERROR: sk is not a u8vector\n")
      (exit 1)))

;; Check lengths
(define pk-len (u8vector-length pk))
(define sk-len (u8vector-length sk))

(if (not (= pk-len 32))
    (begin
      (display "ERROR: pk length wrong: ")
      (display pk-len)
      (display "\n")
      (exit 1)))

(if (not (= sk-len 64))
    (begin
      (display "ERROR: sk length wrong: ")
      (display sk-len)
      (display "\n")
      (exit 1)))

(display "SUCCESS: Keypair generated correctly\n")
(display "  PK length: 32\n")
(display "  SK length: 64\n")
(exit 0)
