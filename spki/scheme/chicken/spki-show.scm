#!/usr/bin/env csi -s
;;; spki-show: Display SPKI certificate in human-readable format

(import (chicken base)
        (chicken format)
        (chicken file)
        (chicken io)
        (chicken process-context)
        (chicken string)
        (chicken condition)
        (chicken blob)
        srfi-4
        sexp
        cert
        crypto-ffi)

(define (usage)
  (print "Usage: spki-show [FILE]")
  (print "Display an SPKI certificate or key in human-readable format.")
  (print "")
  (print "If FILE is omitted, reads from stdin.")
  (print "")
  (print "  --help              Show this help")
  (exit 0))

(define (show-key-hash hash)
  "Display first 16 bytes of hash in hex"
  (let* ((vec (blob->u8vector/shared hash))
         (len (min 16 (u8vector-length vec))))
    (let loop ((i 0) (acc ""))
      (if (>= i len)
          acc
          (loop (+ i 1)
                (string-append acc
                               (sprintf "~x" (u8vector-ref vec i))))))))

(define (show-principal principal)
  "Display principal in human-readable format"
  (cond
   ((key-principal? principal)
    (let ((key (principal-public-key principal)))
      (let ((hash (sha512-hash key)))
        (sprintf "Key (hash: ~a)" (show-key-hash hash)))))

   ((keyhash-principal? principal)
    (let ((alg (principal-hash-alg principal))
          (hash (principal-hash principal)))
      (sprintf "KeyHash (~a: ~a)"
               (hash-alg->string alg)
               (show-key-hash hash))))

   (else
    "Unknown principal type")))

(define (show-tag tag-or-all)
  "Display tag in human-readable format"
  (cond
   ((tag? tag-or-all)
    (sexp->string (tag-sexp tag-or-all)))

   ((all-perms? tag-or-all)
    "(*)")

   (else
    "Unknown tag type")))

(define (show-validity cert)
  "Display validity period"
  (let ((val (cert-validity cert)))
    (if val
        (sprintf "~a to ~a"
                 (validity-not-before val)
                 (validity-not-after val))
        "No expiration")))

(define (show-cert cert)
  "Display certificate in human-readable format"
  (print "SPKI Certificate")
  (print "================")
  (print "")
  (print "Issuer:     " (show-principal (cert-issuer cert)))
  (print "Subject:    " (show-principal (cert-subject cert)))
  (print "Tag:        " (show-tag (cert-tag cert)))
  (print "Validity:   " (show-validity cert))
  (print "Propagate:  " (if (cert-propagate cert) "yes" "no"))
  (print ""))

(define (show-signed-cert signed-cert)
  "Display signed certificate with signature info"
  (show-cert (signed-cert-cert signed-cert))
  (print "Signature")
  (print "---------")
  (let ((sig (signed-cert-signature signed-cert)))
    (print "Algorithm:  " (hash-alg->string (signature-hash-alg sig)))
    (print "Cert hash:  " (show-key-hash (signature-cert-hash sig)))
    (print "Signature:  " (show-key-hash (signature-sig-bytes sig)) "..."))
  (print "")
  (print "S-Expression")
  (print "------------")
  (print (signed-cert->string signed-cert)))

(define (show-key key is-private?)
  "Display key information"
  (let ((key-type (if is-private? "Private" "Public")))
    (print "SPKI " key-type " Key")
    (print "================")
    (print "")
    ;; For private keys, extract public key first
    (let ((pub-key (if is-private?
                       (ed25519-secret-to-public key)
                       key)))
      (let ((hash (sha512-hash pub-key)))
        (print "Key hash: " (show-key-hash hash))))
    (when is-private?
      (print "")
      (print "⚠  This is a PRIVATE key - keep it secret!"))))

(define (main args)
  ;; Initialize libsodium
  (sodium-init)

  ;; Parse arguments
  (define filename "-")

  (let loop ((args args))
    (cond
     ((null? args) #t)

     ((string=? (car args) "--help")
      (usage))

     (else
      (set! filename (car args))
      (loop (cdr args)))))

  ;; Read content
  (let ((content (if (string=? filename "-")
                     (read-string)
                     (with-input-from-file filename read-string))))

    ;; Try to parse as different types
    (handle-exceptions exn
      (begin
        (print "Error parsing input: "
               (if (condition? exn)
                   (get-condition-property exn 'exn 'message)
                   (sprintf "~a" exn)))
        (exit 1))

      (let ((sexp (parse-sexp content)))
        (cond
         ;; Check if it's a private key
         ((and (sexp-list? sexp)
               (= 2 (length (list-items sexp)))
               (sexp-atom? (car (list-items sexp)))
               (string=? (atom-value (car (list-items sexp))) "spki-private-key")
               (sexp-bytes? (cadr (list-items sexp))))
          (show-key (bytes-value (cadr (list-items sexp))) #t))

         ;; Check if it's a public key
         ((and (sexp-list? sexp)
               (= 2 (length (list-items sexp)))
               (sexp-atom? (car (list-items sexp)))
               (string=? (atom-value (car (list-items sexp))) "spki-public-key")
               (sexp-bytes? (cadr (list-items sexp))))
          (show-key (bytes-value (cadr (list-items sexp))) #f))

         ;; Otherwise try to parse as signed cert
         (else
          (let ((signed-cert (signed-cert-of-string content)))
            (show-signed-cert signed-cert))))))))

(main (command-line-arguments))
