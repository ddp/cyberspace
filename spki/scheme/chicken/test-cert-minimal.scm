#!/usr/bin/env csi -s
(import (chicken base)
        (chicken format)
        srfi-4
        sexp
        cert
        crypto-ffi)

(sodium-init)

(display "=== Minimal Certificate Test ===\n\n")

(display "Step 1: Generate keypair...\n")
(define keypair (ed25519-keypair))
(define public-key (car keypair))
(define private-key (cadr keypair))
(display "  Keypair generated\n\n")

(display "Step 2: Create principal from public key...\n")
(define principal (make-key-principal public-key))
(display "  Principal created\n\n")

(display "Step 3: Convert principal to sexp...\n")
(define prin-sexp (principal->sexp principal))
(display "  Principal sexp created\n\n")

(display "Step 4: Convert sexp to string...\n")
(define prin-str (sexp->string prin-sexp))
(display "  Principal string: ")
(display prin-str)
(display "\n\n")

(display "Step 5: Create simple certificate...\n")
(define cert (create-cert principal principal (make-tag (sexp-atom "test"))))
(display "  Certificate created\n\n")

(display "Step 6: Convert cert to sexp...\n")
(define cert-sexp (cert->sexp cert))
(display "  Cert sexp created\n\n")

(display "Step 7: Convert cert sexp to string...\n")
(define cert-str (sexp->string cert-sexp))
(display "  Cert string created (length: ")
(display (string-length cert-str))
(display ")\n\n")

(display "Step 8: Hash the cert string...\n")
(define cert-hash (sha512-hash cert-str))
(display "  Cert hash computed!\n\n")

(display "SUCCESS!\n")
