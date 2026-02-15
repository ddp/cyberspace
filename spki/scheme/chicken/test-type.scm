#!/usr/bin/env csi -s
(import (chicken base)
        (chicken type)
        srfi-4
        crypto-ffi)

;; Initialize
(sodium-init)

;; Generate keypair using values
(define-values (pk sk) (ed25519-keypair))

;; Check what pk actually is
(display "pk type: ")
(display (if (vector? pk) "vector" "not-vector"))
(display "\n")

(display "pk is u8vector?: ")
(display (u8vector? pk))
(display "\n")

(display "pk is bytevector?: ")
(display (if (procedure? bytevector?) (bytevector? pk) "bytevector? not available"))
(display "\n")

(display "pk value: ")
(display pk)
(display "\n")

(exit 0)
