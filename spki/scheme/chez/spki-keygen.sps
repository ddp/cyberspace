#!/usr/bin/env chez --script
;;; spki-keygen: Generate SPKI keypair
;;; Chez Scheme port

(import (rnrs)
        (only (chezscheme) printf format command-line void mkdir)
        (cyberspace sexp)
        (cyberspace crypto-ffi))

(define (usage)
  (printf "Usage: spki-keygen [OPTIONS]~%")
  (printf "Generates an SPKI keypair and saves to files.~%")
  (printf "~%")
  (printf "Options:~%")
  (printf "  --output-dir DIR    Directory to save keys (default: current directory)~%")
  (printf "  --name NAME         Base name for key files (default: spki-key)~%")
  (printf "  --help              Show this help~%")
  (exit 0))

(define (bytevector->hex bv n)
  ;; First n bytes of bytevector as hex string
  (let loop ((i 0) (acc ""))
    (if (>= i (min n (bytevector-length bv)))
        acc
        (loop (+ i 1)
              (string-append acc
                             (let ((b (bytevector-u8-ref bv i)))
                               (format #f "~2,'0x" b)))))))

(define (make-pathname dir name)
  (string-append dir "/" name))

(define (main args)
  (sodium-init)

  (let ((output-dir ".")
        (key-name "spki-key"))

    (let loop ((args args))
      (cond
       ((null? args) (void))

       ((string=? (car args) "--help")
        (usage))

       ((string=? (car args) "--output-dir")
        (if (null? (cdr args))
            (begin (printf "Error: --output-dir requires an argument~%") (exit 1))
            (begin
              (set! output-dir (cadr args))
              (loop (cddr args)))))

       ((string=? (car args) "--name")
        (if (null? (cdr args))
            (begin (printf "Error: --name requires an argument~%") (exit 1))
            (begin
              (set! key-name (cadr args))
              (loop (cddr args)))))

       (else
        (printf "Error: Unknown argument: ~a~%" (car args))
        (usage))))

    ;; Generate keypair
    (printf "Generating SPKI keypair...~%")
    (let* ((keypair (ed25519-keypair))
           (public-key (car keypair))
           (private-key (cadr keypair))
           (key-hash (sha512-hash public-key))
           (hash-preview (bytevector->hex key-hash 16)))

      (printf "Public key hash (first 16 bytes): ~a~%" hash-preview)

      ;; Create output directory if needed
      (unless (file-exists? output-dir)
        (mkdir output-dir))

      ;; Save private key
      (let* ((priv-file (make-pathname output-dir (string-append key-name ".private")))
             (priv-sexp (sexp-list (list (sexp-atom "spki-private-key")
                                         (sexp-bytes private-key))))
             (priv-content (sexp->string-indent priv-sexp "")))
        (with-output-to-file priv-file
          (lambda () (printf "~a~%" priv-content)))
        (printf "Private key saved to: ~a~%" priv-file))

      ;; Save public key
      (let* ((pub-file (make-pathname output-dir (string-append key-name ".public")))
             (pub-sexp (sexp-list (list (sexp-atom "spki-public-key")
                                        (sexp-bytes public-key))))
             (pub-content (sexp->string-indent pub-sexp "")))
        (with-output-to-file pub-file
          (lambda () (printf "~a~%" pub-content)))
        (printf "Public key saved to: ~a~%" pub-file))

      (printf "~%Keypair generation complete!~%")
      (printf "Share your public key hash with friends: ~a~%" hash-preview))))

;; Skip argv[0] (the script name)
(main (cdr (command-line)))
