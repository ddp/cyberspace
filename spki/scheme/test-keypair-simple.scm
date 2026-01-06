#!/usr/bin/env csi -s
(import (chicken base)
        srfi-4
        crypto-ffi)

;; Initialize
(sodium-init)

;; Create vectors for keys
(define pk (make-u8vector crypto-sign-publickeybytes))
(define sk (make-u8vector crypto-sign-secretkeybytes))

;; Check they're u8vectors BEFORE foreign call
(display "Before foreign call:\n")
(display "  pk is u8vector?: ")
(display (u8vector? pk))
(display "\n")
(display "  sk is u8vector?: ")
(display (u8vector? sk))
(display "\n")

;; Generate keypair
(define result (ed25519-keypair! pk sk))

(display "After foreign call:\n")
(display "  result: ")
(display result)
(display "\n")

(if (not (= result 0))
    (begin
      (display "ERROR: keypair generation failed\n")
      (exit 1)))

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
      (display "ERROR: pk length wrong\n")
      (exit 1)))

(if (not (= sk-len 64))
    (begin
      (display "ERROR: sk length wrong\n")
      (exit 1)))

(display "SUCCESS: Keypair generated!\n")
(display "  PK length: 32\n")
(display "  SK length: 64\n")
(exit 0)
