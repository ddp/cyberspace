#!/usr/bin/env csi -s
;;; Demo: Create signed script and verify with cyberspace interpreter

(import script
        crypto-ffi
        (chicken blob)
        (chicken format)
        (chicken file)
        (chicken io)
        srfi-4)

(sodium-init)

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

(print "=== Cyberspace Demo: Creating Signed Script ===\n")

;; Generate 3 keypairs for Alice, Bob, Carol
(print "Generating keypairs for Alice, Bob, Carol...")

(define alice-keys (ed25519-keypair))
(define bob-keys (ed25519-keypair))
(define carol-keys (ed25519-keypair))

;; Save public keys
(with-output-to-file "alice.pub"
  (lambda () (write-string (blob->string (car alice-keys)))))

(with-output-to-file "bob.pub"
  (lambda () (write-string (blob->string (car bob-keys)))))

(with-output-to-file "carol.pub"
  (lambda () (write-string (blob->string (car carol-keys)))))

(print "  Saved: alice.pub, bob.pub, carol.pub\n")

;; Create a simple deployment script
(define script-content
  ";; Cyberspace Deployment Script
(seal-release \"1.0.0\"
  message: \"First stable release\"
  catalog: #t
  subjects: '(\"library\" \"preservation\")
  keywords: '(\"cyberspace\" \"archival\"))")

(with-output-to-file "deploy.scm"
  (lambda () (write-string script-content)))

(print "Created deploy.scm:")
(print script-content)
(print "")

;; Sign script with all 3 keys
(print "\nSigning script with Alice, Bob, Carol...")

(define alice-sig (sign-script script-content (cadr alice-keys) (car alice-keys)))
(define bob-sig (sign-script script-content (cadr bob-keys) (car bob-keys)))
(define carol-sig (sign-script script-content (cadr carol-keys) (car carol-keys)))

;; Create signature file in S-expression format
(define sig-sexp
  `((signature ,(blob->hex (signature-value alice-sig))
               ,(blob->hex (signature-signer alice-sig))
               ,(signature-timestamp alice-sig))
    (signature ,(blob->hex (signature-value bob-sig))
               ,(blob->hex (signature-signer bob-sig))
               ,(signature-timestamp bob-sig))
    (signature ,(blob->hex (signature-value carol-sig))
               ,(blob->hex (signature-signer carol-sig))
               ,(signature-timestamp carol-sig))))

(with-output-to-file "deploy.sig"
  (lambda ()
    (write sig-sexp)))

(print "  Saved: deploy.sig (3 signatures)\n")

(print "=== Demo Setup Complete ===\n")
(print "Now run:")
(print "  ./cyberspace.scm verify deploy.scm deploy.sig --threshold 2 --keys alice.pub bob.pub carol.pub")
(print "  ./cyberspace.scm run deploy.scm deploy.sig --threshold 2 --keys alice.pub bob.pub carol.pub")
