#!/usr/bin/env csi -s
(import (chicken base)
        (chicken format)
        crypto-ffi)

(sodium-init)

(display "Testing sha512-hash with simple string...\n")
(define test-str "hello")
(display "Input string: ")
(display test-str)
(display "\n")
(display "Input is string?: ")
(display (string? test-str))
(display "\n")

(display "Calling sha512-hash...\n")
(define hash (sha512-hash test-str))

(display "Success! Hash computed.\n")
