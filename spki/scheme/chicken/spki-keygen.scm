#!/usr/bin/env csi -s
;;; spki-keygen: Generate SPKI keypair

(import (chicken base)
        (chicken format)
        (chicken file)
        (chicken process-context)
        (chicken string)
        (chicken pathname)
        (chicken blob)
        srfi-4  ; u8vectors
        sexp
        crypto-ffi)

(define (usage)
  (print "Usage: spki-keygen [OPTIONS]")
  (print "Generates an SPKI keypair and saves to files.")
  (print "")
  (print "Options:")
  (print "  --output-dir DIR    Directory to save keys (default: current directory)")
  (print "  --name NAME         Base name for key files (default: spki-key)")
  (print "  --help              Show this help")
  (exit 0))

(define (main args)
  ;; Initialize libsodium
  (sodium-init)

  ;; Parse arguments
  (define output-dir ".")
  (define key-name "spki-key")

  (let loop ((args args))
    (cond
     ((null? args) #t)

     ((string=? (car args) "--help")
      (usage))

     ((string=? (car args) "--output-dir")
      (if (null? (cdr args))
          (begin
            (print "Error: --output-dir requires an argument")
            (exit 1))
          (begin
            (set! output-dir (cadr args))
            (loop (cddr args)))))

     ((string=? (car args) "--name")
      (if (null? (cdr args))
          (begin
            (print "Error: --name requires an argument")
            (exit 1))
          (begin
            (set! key-name (cadr args))
            (loop (cddr args)))))

     (else
      (print "Error: Unknown argument: " (car args))
      (usage))))

  ;; Generate keypair
  (print "Generating SPKI keypair...")
  (define keypair (ed25519-keypair))
  (define public-key (car keypair))
  (define private-key (cadr keypair))

  ;; Compute key hash for display (first 16 bytes in hex)
  (define key-hash (sha512-hash public-key))
  (define hash-vec (blob->u8vector/shared key-hash))
  (define hash-preview
    (let loop ((i 0) (acc ""))
      (if (>= i 16)
          acc
          (loop (+ i 1)
                (string-append acc
                               (sprintf "~x" (u8vector-ref hash-vec i)))))))
  (print "Public key hash (first 16 bytes): " hash-preview)

  ;; Create output directory if it doesn't exist
  (unless (directory-exists? output-dir)
    (create-directory output-dir #t))

  ;; Save private key
  (define priv-file (make-pathname output-dir (string-append key-name ".private")))
  (define priv-sexp (sexp-list (list
                                 (sexp-atom "spki-private-key")
                                 (sexp-bytes private-key))))
  (define priv-content (sexp->string-indent priv-sexp ""))
  (with-output-to-file priv-file
    (lambda ()
      (print priv-content)))
  (print "Private key saved to: " priv-file)

  ;; Save public key
  (define pub-file (make-pathname output-dir (string-append key-name ".public")))
  (define pub-sexp (sexp-list (list
                                (sexp-atom "spki-public-key")
                                (sexp-bytes public-key))))
  (define pub-content (sexp->string-indent pub-sexp ""))
  (with-output-to-file pub-file
    (lambda ()
      (print pub-content)))
  (print "Public key saved to: " pub-file)

  (print "")
  (print "Keypair generation complete!")
  (print "Share your public key hash with friends: " hash-preview))

(main (command-line-arguments))
