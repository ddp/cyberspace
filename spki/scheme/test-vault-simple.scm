#!/usr/bin/env csi -s
;;; Simple vault test - create sealed commit

(import vault
        crypto-ffi
        (chicken file)
        (chicken format)
        (chicken blob)
        srfi-4)

(sodium-init)

;; Helper
(define (blob->hex b)
  (define (byte->hex n)
    (let ((s (number->string n 16)))
      (if (= (string-length s) 1)
          (string-append "0" s)
          s)))
  (let ((vec (blob->u8vector b)))
    (let loop ((i 0) (acc '()))
      (if (= i (u8vector-length vec))
          (apply string-append (reverse acc))
          (loop (+ i 1)
                (cons (byte->hex (u8vector-ref vec i)) acc))))))

(print "=== Simple Vault Test ===\n")

;; Check if .vault directory exists
(unless (directory-exists? ".vault")
  (print "Creating .vault directory...")
  (create-directory ".vault" #t))

(unless (directory-exists? ".vault/metadata")
  (print "Creating .vault/metadata directory...")
  (create-directory ".vault/metadata" #t))

;; Generate a keypair for sealing
(print "Generating signing keypair...")
(define keys (ed25519-keypair))
(define public-key (car keys))
(define private-key (cadr keys))

(print "Public key: " (substring (blob->hex public-key) 0 32) "...\n")

;; Try to initialize vault
(print "Attempting vault-init...")
(vault-init signing-key: private-key)
(print "✓ Vault initialized\n")

;; Create a simple file to commit
(with-output-to-file "test-file.txt"
  (lambda ()
    (display "Hello from cyberspace!")))

(print "Created test-file.txt")
(print "Content: Hello from cyberspace!\n")

;; Try a minimal sealed commit
(print "Attempting minimal sealed commit...")
(seal-commit "Test commit: Hello cyberspace")
(print "✓ Sealed commit created\n")

(print "=== Test Complete ===")
