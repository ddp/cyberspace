#!/usr/bin/env csi -s
(import (chicken base)
        (chicken format)
        srfi-4
        crypto-ffi)

(sodium-init)

(display "Testing sha512-hash with string...\n")
(define test-string "Hello, World!")
(define hash-result (sha512-hash test-string))

(display "Hash result: ")
(display hash-result)
(display "\n")
(display "Hash is u8vector?: ")
(display (u8vector? hash-result))
(display "\n")

(display "SUCCESS!\n")
