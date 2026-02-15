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

;;; ============================================================
;;; Argument Parsing
;;; ============================================================

(define (parse-option args name has-value?)
  "Parse --name [value] from args. Returns (value . remaining-args) or #f."
  (let loop ((args args) (acc '()))
    (cond
     ((null? args) #f)
     ((string=? (car args) name)
      (if has-value?
          (if (null? (cdr args))
              (begin (print "Error: " name " requires an argument") (exit 1))
              (cons (cadr args) (append (reverse acc) (cddr args))))
          (cons #t (append (reverse acc) (cdr args)))))
     (else (loop (cdr args) (cons (car args) acc))))))

(define (parse-args args)
  "Parse all arguments into an alist."
  (let ((opts '())
        (remaining args))
    ;; Extract each option
    (let ((r (parse-option remaining "--help" #f)))
      (when r (usage)))
    (let ((r (parse-option remaining "--issuer" #t)))
      (when r (set! opts (cons (cons 'issuer (car r)) opts))
                   (set! remaining (cdr r))))
    (let ((r (parse-option remaining "--subject" #t)))
      (when r (set! opts (cons (cons 'subject (car r)) opts))
                   (set! remaining (cdr r))))
    (let ((r (parse-option remaining "--tag" #t)))
      (when r (set! opts (cons (cons 'tag (car r)) opts))
                   (set! remaining (cdr r))))
    (let ((r (parse-option remaining "--propagate" #f)))
      (when r (set! opts (cons (cons 'propagate #t) opts))
                   (set! remaining (cdr r))))
    (let ((r (parse-option remaining "--not-before" #t)))
      (when r (set! opts (cons (cons 'not-before (car r)) opts))
                   (set! remaining (cdr r))))
    (let ((r (parse-option remaining "--not-after" #t)))
      (when r (set! opts (cons (cons 'not-after (car r)) opts))
                   (set! remaining (cdr r))))
    (let ((r (parse-option remaining "--output" #t)))
      (when r (set! opts (cons (cons 'output (car r)) opts))
                   (set! remaining (cdr r))))
    ;; Check for unknown args
    (unless (null? remaining)
      (print "Error: Unknown argument: " (car remaining))
      (usage))
    opts))

(define (opt key opts)
  "Get option value from alist."
  (let ((pair (assq key opts)))
    (and pair (cdr pair))))

;;; ============================================================
;;; Certificate Creation
;;; ============================================================

(define (create-signed-cert issuer-file subject-file tag-str propagate not-before not-after)
  "Create and sign a certificate. Returns signed cert."
  (let ((issuer-key-pair (read-key-file issuer-file))
        (subject-key-pair (read-key-file subject-file)))
    (let ((issuer-key (car issuer-key-pair))
          (issuer-is-private? (cdr issuer-key-pair))
          (subject-key (car subject-key-pair)))
      (unless issuer-is-private?
        (print "Error: issuer key must be a private key")
        (exit 1))
      (let* ((tag-sexp (parse-sexp tag-str))
             (tag (make-tag tag-sexp))
             (issuer-public-key (ed25519-secret-to-public issuer-key))
             (issuer-principal (make-key-principal issuer-public-key))
             (subject-principal (make-key-principal subject-key))
             (the-cert (if (and not-before not-after)
                           (create-cert issuer-principal subject-principal tag
                                       validity: (make-validity not-before not-after)
                                       propagate: propagate)
                           (create-cert issuer-principal subject-principal tag
                                       propagate: propagate))))
        (sign-cert the-cert issuer-key)))))

;;; ============================================================
;;; Main
;;; ============================================================

(define (main args)
  (sodium-init)
  (let ((opts (parse-args args)))
    ;; Validate required
    (unless (and (opt 'issuer opts) (opt 'subject opts) (opt 'tag opts))
      (print "Error: --issuer, --subject, and --tag are required")
      (usage))
    ;; Create certificate
    (let* ((signed-cert (create-signed-cert
                         (opt 'issuer opts)
                         (opt 'subject opts)
                         (opt 'tag opts)
                         (opt 'propagate opts)
                         (opt 'not-before opts)
                         (opt 'not-after opts)))
           (cert-str (signed-cert->string signed-cert))
           (output-file (opt 'output opts)))
      (if output-file
          (begin
            (with-output-to-file output-file (lambda () (print cert-str)))
            (print "Certificate saved to: " output-file))
          (print cert-str)))))

(main (command-line-arguments))
