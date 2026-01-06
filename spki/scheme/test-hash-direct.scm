#!/usr/bin/env csi -s
(import (chicken base)
        (chicken foreign)
        (chicken string)
        srfi-4)

(foreign-declare "#include <sodium.h>")

;; Initialize
((foreign-lambda int "sodium_init"))

;; Convert string to u8vector
(define (string->u8vector str)
  (let* ((len (string-length str))
         (vec (make-u8vector len)))
    (do ((i 0 (+ i 1)))
        ((= i len) vec)
      (u8vector-set! vec i (char->integer (string-ref str i))))))

(display "Testing SHA-512 hash directly...\n")
(define test-data (string->u8vector "Hello"))
(define hash (make-u8vector 64))

(display "Calling crypto_hash_sha512...\n")
((foreign-lambda int "crypto_hash_sha512"
                scheme-pointer scheme-pointer unsigned-integer)
 hash test-data (u8vector-length test-data))

(display "Hash computed successfully!\n")
(display "Hash length: ")
(display (u8vector-length hash))
(display "\n")
