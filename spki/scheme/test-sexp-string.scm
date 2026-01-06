#!/usr/bin/env csi -s
(import (chicken base)
        (chicken format)
        sexp)

(define test-atom (sexp-atom "hello"))
(define result (sexp->string test-atom))

(display "Result: ")
(display result)
(display "\n")
(display "Result is string?: ")
(display (string? result))
(display "\n")
(display "Result type: ")
(display (type-of result))
(display "\n")

(define test-list (sexp-list (list (sexp-atom "foo") (sexp-atom "bar"))))
(define result2 (sexp->string test-list))

(display "\nList result: ")
(display result2)
(display "\n")
(display "List result is string?: ")
(display (string? result2))
(display "\n")
