#!/usr/bin/env chez --script
;;; spki-cert: Create and sign SPKI certificate
;;; Chez Scheme port

(import (rnrs)
        (only (chezscheme) printf format command-line void)
        (cyberspace sexp)
        (cyberspace cert)
        (cyberspace crypto-ffi))

(define (usage)
  (printf "Usage: spki-cert --issuer KEYFILE --subject KEYFILE --tag TAG [OPTIONS]~%")
  (printf "Create and sign an SPKI authorization certificate.~%")
  (printf "~%")
  (printf "Required:~%")
  (printf "  --issuer FILE       Issuer's private key file~%")
  (printf "  --subject FILE      Subject's public key file~%")
  (printf "  --tag TAG           Authorization tag (s-expression)~%")
  (printf "~%")
  (printf "Optional:~%")
  (printf "  --propagate         Allow subject to re-delegate (default: false)~%")
  (printf "  --not-before TIME   Validity start time (ISO 8601)~%")
  (printf "  --not-after TIME    Validity end time (ISO 8601)~%")
  (printf "  --output FILE       Output file (default: stdout)~%")
  (printf "  --help              Show this help~%")
  (printf "~%")
  (printf "Example tags:~%")
  (printf "  '(read (path /library/lamport-papers))'~%")
  (printf "  '(spawn-agent (max-count 5))'~%")
  (printf "  '(write (path /shared/notes))'~%")
  (exit 0))

(define (read-key-file filename)
  ;; Read a key file and return (key . is-private?)
  (let ((content (with-input-from-file filename
                   (lambda () (get-string-all (current-input-port))))))
    (let ((s (parse-sexp content)))
      (if (and (sexp-list? s)
               (= 2 (length (list-items s))))
          (let ((items (list-items s)))
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
                (printf "Error: Invalid key file format: ~a~%" filename)
                (exit 1)))))
          (begin
            (printf "Error: Invalid key file format: ~a~%" filename)
            (exit 1))))))

;;; Argument Parsing

(define (parse-option args name has-value?)
  ;; Parse --name [value] from args. Returns (value . remaining-args) or #f.
  (let loop ((args args) (acc '()))
    (cond
     ((null? args) #f)
     ((string=? (car args) name)
      (if has-value?
          (if (null? (cdr args))
              (begin (printf "Error: ~a requires an argument~%" name) (exit 1))
              (cons (cadr args) (append (reverse acc) (cddr args))))
          (cons #t (append (reverse acc) (cdr args)))))
     (else (loop (cdr args) (cons (car args) acc))))))

(define (parse-args args)
  ;; Parse all arguments into an alist.
  (let ((opts '())
        (remaining args))
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
    (unless (null? remaining)
      (printf "Error: Unknown argument: ~a~%" (car remaining))
      (usage))
    opts))

(define (opt key opts)
  (let ((pair (assq key opts)))
    (and pair (cdr pair))))

;;; Certificate Creation

(define (create-signed-cert issuer-file subject-file tag-str propagate not-before not-after)
  (let ((issuer-key-pair (read-key-file issuer-file))
        (subject-key-pair (read-key-file subject-file)))
    (let ((issuer-key (car issuer-key-pair))
          (issuer-is-private? (cdr issuer-key-pair))
          (subject-key (car subject-key-pair)))
      (unless issuer-is-private?
        (printf "Error: issuer key must be a private key~%")
        (exit 1))
      (let* ((tag-sexp (parse-sexp tag-str))
             (tag (make-tag tag-sexp))
             (issuer-public-key (ed25519-secret-to-public issuer-key))
             (issuer-principal (make-key-principal issuer-public-key))
             (subject-principal (make-key-principal subject-key))
             (the-cert (if (and not-before not-after)
                           (create-cert issuer-principal subject-principal tag
                                       'validity: (make-validity not-before not-after)
                                       'propagate: propagate)
                           (create-cert issuer-principal subject-principal tag
                                       'propagate: propagate))))
        (sign-cert the-cert issuer-key)))))

;;; Main

(define (main args)
  (sodium-init)
  (let ((opts (parse-args args)))
    (unless (and (opt 'issuer opts) (opt 'subject opts) (opt 'tag opts))
      (printf "Error: --issuer, --subject, and --tag are required~%")
      (usage))
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
            (with-output-to-file output-file (lambda () (printf "~a~%" cert-str)))
            (printf "Certificate saved to: ~a~%" output-file))
          (printf "~a~%" cert-str)))))

(main (cdr (command-line)))
