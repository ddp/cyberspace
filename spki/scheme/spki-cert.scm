#!/usr/bin/env csi -s
;;; spki-cert: Create and sign SPKI certificate

(import (chicken base)
        (chicken format)
        (chicken file)
        (chicken io)
        (chicken process-context)
        (chicken string)
        sexp
        cert
        crypto-ffi)

(define (usage)
  (print "Usage: spki-cert --issuer KEYFILE --subject KEYFILE --tag TAG [OPTIONS]")
  (print "Create and sign an SPKI authorization certificate.")
  (print "")
  (print "Required:")
  (print "  --issuer FILE       Issuer's private key file")
  (print "  --subject FILE      Subject's public key file")
  (print "  --tag TAG           Authorization tag (s-expression)")
  (print "")
  (print "Optional:")
  (print "  --propagate         Allow subject to re-delegate (default: false)")
  (print "  --not-before TIME   Validity start time (ISO 8601)")
  (print "  --not-after TIME    Validity end time (ISO 8601)")
  (print "  --output FILE       Output file (default: stdout)")
  (print "  --help              Show this help")
  (print "")
  (print "Example tags:")
  (print "  '(read (path /library/lamport-papers))'")
  (print "  '(spawn-agent (max-count 5))'")
  (print "  '(write (path /shared/notes))'")
  (exit 0))

(define (read-key-file filename)
  "Read a key file and return (key . is-private?)"
  (let ((content (with-input-from-file filename read-string)))
    (let ((sexp (parse-sexp content)))
      (if (and (sexp-list? sexp)
               (= 2 (length (list-items sexp))))
          (let ((items (list-items sexp)))
            (let ((type-atom (car items))
                  (key-bytes (cadr items)))
              (cond
               ((and (sexp-atom? type-atom)
                     (string=? (atom-value type-atom) "spki-private-key")
                     (sexp-bytes? key-bytes))
                (cons (bytes-value key-bytes) #t))

               ((and (sexp-atom? type-atom)
                     (string=? (atom-value type-atom) "spki-public-key")
                     (sexp-bytes? key-bytes))
                (cons (bytes-value key-bytes) #f))

               (else
                (print "Error: Invalid key file format: " filename)
                (exit 1)))))
          (begin
            (print "Error: Invalid key file format: " filename)
            (exit 1))))))

(define (main args)
  ;; Initialize libsodium
  (sodium-init)

  ;; Parse arguments
  (define issuer-file #f)
  (define subject-file #f)
  (define tag-str #f)
  (define propagate #f)
  (define not-before #f)
  (define not-after #f)
  (define output-file #f)

  (let loop ((args args))
    (cond
     ((null? args) #t)

     ((string=? (car args) "--help")
      (usage))

     ((string=? (car args) "--issuer")
      (if (null? (cdr args))
          (begin
            (print "Error: --issuer requires an argument")
            (exit 1))
          (begin
            (set! issuer-file (cadr args))
            (loop (cddr args)))))

     ((string=? (car args) "--subject")
      (if (null? (cdr args))
          (begin
            (print "Error: --subject requires an argument")
            (exit 1))
          (begin
            (set! subject-file (cadr args))
            (loop (cddr args)))))

     ((string=? (car args) "--tag")
      (if (null? (cdr args))
          (begin
            (print "Error: --tag requires an argument")
            (exit 1))
          (begin
            (set! tag-str (cadr args))
            (loop (cddr args)))))

     ((string=? (car args) "--propagate")
      (set! propagate #t)
      (loop (cdr args)))

     ((string=? (car args) "--not-before")
      (if (null? (cdr args))
          (begin
            (print "Error: --not-before requires an argument")
            (exit 1))
          (begin
            (set! not-before (cadr args))
            (loop (cddr args)))))

     ((string=? (car args) "--not-after")
      (if (null? (cdr args))
          (begin
            (print "Error: --not-after requires an argument")
            (exit 1))
          (begin
            (set! not-after (cadr args))
            (loop (cddr args)))))

     ((string=? (car args) "--output")
      (if (null? (cdr args))
          (begin
            (print "Error: --output requires an argument")
            (exit 1))
          (begin
            (set! output-file (cadr args))
            (loop (cddr args)))))

     (else
      (print "Error: Unknown argument: " (car args))
      (usage))))

  ;; Validate required arguments
  (unless (and issuer-file subject-file tag-str)
    (print "Error: --issuer, --subject, and --tag are required")
    (usage))

  ;; Read keys
  (let ((issuer-key-pair (read-key-file issuer-file))
        (subject-key-pair (read-key-file subject-file)))

    (let ((issuer-key (car issuer-key-pair))
          (issuer-is-private? (cdr issuer-key-pair))
          (subject-key (car subject-key-pair)))

      (unless issuer-is-private?
        (print "Error: issuer key must be a private key")
        (exit 1))

      ;; Parse tag
      (let ((tag-sexp (parse-sexp tag-str)))
        (let ((tag (make-tag tag-sexp)))

          ;; Create principals
          ;; Note: For private key, we need to derive public key
          ;; For now, assume private key file also contains or implies the public key
          ;; In ed25519, the public key is derivable from private key
          ;; But libsodium stores both together in the 64-byte "secret key"
          ;; The first 32 bytes are the seed, last 32 are the public key

          ;; Extract public key from 64-byte secret key
          (let ((issuer-public-key (ed25519-secret-to-public issuer-key)))
            (let ((issuer-principal (make-key-principal issuer-public-key))
                  (subject-principal (make-key-principal subject-key)))

              ;; Create certificate
              (let ((the-cert
                     (if (and not-before not-after)
                         (let ((validity (make-validity not-before not-after)))
                           (create-cert issuer-principal subject-principal tag
                                       validity: validity
                                       propagate: propagate))
                         (create-cert issuer-principal subject-principal tag
                                     propagate: propagate))))

                ;; Sign certificate with issuer's private key
                (let ((signed-cert (sign-cert the-cert issuer-key)))

                  ;; Output certificate
                  (let ((cert-str (signed-cert->string signed-cert)))
                    (if output-file
                        (begin
                          (with-output-to-file output-file
                            (lambda ()
                              (print cert-str)))
                          (print "Certificate saved to: " output-file))
                        (print cert-str))))))))))))

(main (command-line-arguments))
