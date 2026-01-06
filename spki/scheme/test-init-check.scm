#!/usr/bin/env csi -s
(import (chicken base)
        (chicken format)
        crypto-ffi)

(display "Calling sodium-init...\n")
(define init-result (sodium-init))
(display "Init result: ")
(display init-result)
(display "\n")

(if (< init-result 0)
    (begin
      (display "ERROR: sodium-init failed!\n")
      (exit 1))
    (display "sodium-init succeeded\n"))
