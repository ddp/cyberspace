;;; SPKI Scheme - Certificate Types and Operations
;;;
;;; This module defines SPKI certificates and operations for:
;;; - Creating certificates
;;; - Signing certificates
;;; - Verifying certificates
;;; - Checking delegation chains
;;;
;;; Follows SPKI/SDSI specification with Ed25519 signatures.

(module cert
  (;; Exports
   ;; Principal constructors
   make-key-principal make-keyhash-principal
   key-principal? keyhash-principal?
   principal-public-key principal-hash-alg principal-hash

   ;; Tag constructors
   make-tag make-all-perms
   tag? all-perms?
   tag-sexp

   ;; Validity
   make-validity
   validity? validity-not-before validity-not-after

   ;; Certificate
   make-cert
   cert? cert-issuer cert-subject cert-tag cert-validity cert-propagate

   ;; Signed certificate
   make-signed-cert
   signed-cert? signed-cert-cert signed-cert-signature

   ;; Signature
   make-signature
   signature? signature-hash-alg signature-cert-hash signature-sig-bytes
   hash-alg->string

   ;; Operations
   create-cert
   sign-cert
   verify-signed-cert
   verify-chain
   tag-implies

   ;; Conversion
   principal->sexp sexp->principal
   tag->sexp sexp->tag
   validity->sexp sexp->validity
   cert->sexp sexp->cert
   signature->sexp
   signed-cert->sexp sexp->signed-cert
   signed-cert->string signed-cert-of-string)

  (import scheme
          (chicken base)
          (chicken string)
          (chicken format)
          srfi-1   ; list utilities
          srfi-4   ; u8vectors
          srfi-13  ; string utilities
          srfi-14  ; character sets
          sexp
          crypto-ffi)

  ;;; Hash algorithms
  (define hash-alg-sha512 'sha512)

  (define (hash-alg->string alg)
    (case alg
      ((sha512) "sha512")
      (else (error "Unknown hash algorithm" alg))))

  (define (string->hash-alg str)
    (cond
     ((string=? str "sha512") hash-alg-sha512)
     (else (error "Unknown hash algorithm" str))))

  ;;; Principal: either a key or a hash of a key

  (define-record-type <key-principal>
    (make-key-principal-internal public-key)
    key-principal?
    (public-key principal-public-key))

  (define-record-type <keyhash-principal>
    (make-keyhash-principal-internal hash-alg hash)
    keyhash-principal?
    (hash-alg principal-hash-alg)
    (hash principal-hash))

  ;; Public constructors
  (define (make-key-principal public-key)
    (make-key-principal-internal public-key))

  (define (make-keyhash-principal alg hash)
    (make-keyhash-principal-internal alg hash))

  ;;; Authorization tags

  (define-record-type <tag>
    (make-tag-internal sexp)
    tag?
    (sexp tag-sexp))

  (define-record-type <all-perms>
    (make-all-perms-internal)
    all-perms?)

  ;; Public constructors
  (define (make-tag sexp)
    (make-tag-internal sexp))

  (define (make-all-perms)
    (make-all-perms-internal))

  ;;; Time validity

  (define-record-type <validity>
    (make-validity not-before not-after)
    validity?
    (not-before validity-not-before)
    (not-after validity-not-after))

  ;;; Certificate

  (define-record-type <cert>
    (make-cert issuer subject tag validity propagate)
    cert?
    (issuer cert-issuer)
    (subject cert-subject)
    (tag cert-tag)
    (validity cert-validity)
    (propagate cert-propagate))

  ;;; Signature

  (define-record-type <signature>
    (make-signature hash-alg cert-hash sig-bytes)
    signature?
    (hash-alg signature-hash-alg)
    (cert-hash signature-cert-hash)
    (sig-bytes signature-sig-bytes))

  ;;; Signed certificate

  (define-record-type <signed-cert>
    (make-signed-cert cert signature)
    signed-cert?
    (cert signed-cert-cert)
    (signature signed-cert-signature))

  ;;; Conversion to/from s-expressions

  (define (principal->sexp principal)
    (cond
     ((key-principal? principal)
      (sexp-bytes (principal-public-key principal)))

     ((keyhash-principal? principal)
      (sexp-list (list
                  (sexp-atom "hash")
                  (sexp-atom (hash-alg->string (principal-hash-alg principal)))
                  (sexp-bytes (principal-hash principal)))))

     (else
      (error "Invalid principal" principal))))

  (define (sexp->principal sexp)
    (cond
     ((sexp-bytes? sexp)
      (make-key-principal (bytes-value sexp)))

     ((sexp-list? sexp)
      (let ((items (list-items sexp)))
        (if (and (>= (length items) 3)
                 (sexp-atom? (car items))
                 (string=? (atom-value (car items)) "hash"))
            (let ((alg-str (atom-value (cadr items)))
                  (hash (bytes-value (caddr items))))
              (make-keyhash-principal (string->hash-alg alg-str) hash))
            (error "Invalid principal s-expression" sexp))))

     (else
      (error "Invalid principal s-expression" sexp))))

  (define (tag->sexp tag)
    (cond
     ((tag? tag)
      (tag-sexp tag))

     ((all-perms? tag)
      (sexp-list (list (sexp-atom "*"))))

     (else
      (error "Invalid tag" tag))))

  (define (sexp->tag sexp)
    (if (and (sexp-list? sexp)
             (= (length (list-items sexp)) 1)
             (sexp-atom? (car (list-items sexp)))
             (string=? (atom-value (car (list-items sexp))) "*"))
        (make-all-perms)
        (make-tag sexp)))

  (define (validity->sexp validity)
    (sexp-list (list
                (sexp-atom "valid")
                (sexp-list (list
                            (sexp-atom "not-before")
                            (sexp-atom (validity-not-before validity))))
                (sexp-list (list
                            (sexp-atom "not-after")
                            (sexp-atom (validity-not-after validity)))))))

  (define (sexp->validity sexp)
    (if (not (sexp-list? sexp))
        (error "Invalid validity s-expression" sexp))
    (let ((items (list-items sexp)))
      (if (and (>= (length items) 3)
               (sexp-atom? (car items))
               (string=? (atom-value (car items)) "valid"))
          (let ((before-sexp (cadr items))
                (after-sexp (caddr items)))
            (let ((not-before
                   (if (and (sexp-list? before-sexp)
                            (= (length (list-items before-sexp)) 2)
                            (sexp-atom? (car (list-items before-sexp)))
                            (string=? (atom-value (car (list-items before-sexp))) "not-before"))
                       (atom-value (cadr (list-items before-sexp)))
                       (error "Invalid not-before" before-sexp)))
                  (not-after
                   (if (and (sexp-list? after-sexp)
                            (= (length (list-items after-sexp)) 2)
                            (sexp-atom? (car (list-items after-sexp)))
                            (string=? (atom-value (car (list-items after-sexp))) "not-after"))
                       (atom-value (cadr (list-items after-sexp)))
                       (error "Invalid not-after" after-sexp))))
              (make-validity not-before not-after)))
          (error "Invalid validity s-expression" sexp))))

  (define (cert->sexp cert)
    (let ((base (list
                 (sexp-atom "cert")
                 (sexp-list (list (sexp-atom "issuer")
                                  (principal->sexp (cert-issuer cert))))
                 (sexp-list (list (sexp-atom "subject")
                                  (principal->sexp (cert-subject cert))))
                 (sexp-list (list (sexp-atom "tag")
                                  (tag->sexp (cert-tag cert)))))))
      (let ((with-validity
             (if (cert-validity cert)
                 (append base (list (validity->sexp (cert-validity cert))))
                 base)))
        (let ((with-propagate
               (if (cert-propagate cert)
                   (append with-validity (list (sexp-list (list (sexp-atom "propagate")))))
                   with-validity)))
          (sexp-list with-propagate)))))

  (define (sexp->cert sexp)
    (if (not (sexp-list? sexp))
        (error "Invalid certificate s-expression" sexp))
    (let ((items (list-items sexp)))
      (if (and (>= (length items) 1)
               (sexp-atom? (car items))
               (string=? (atom-value (car items)) "cert"))
          (let ((issuer #f)
                (subject #f)
                (tag #f)
                (validity #f)
                (propagate #f))
            ;; Parse fields
            (for-each
             (lambda (field)
               (if (sexp-list? field)
                   (let ((field-items (list-items field)))
                     (if (and (>= (length field-items) 1)
                              (sexp-atom? (car field-items)))
                         (let ((field-name (atom-value (car field-items))))
                           (cond
                            ((string=? field-name "issuer")
                             (if (>= (length field-items) 2)
                                 (set! issuer (sexp->principal (cadr field-items)))))

                            ((string=? field-name "subject")
                             (if (>= (length field-items) 2)
                                 (set! subject (sexp->principal (cadr field-items)))))

                            ((string=? field-name "tag")
                             (if (>= (length field-items) 2)
                                 (set! tag (sexp->tag (cadr field-items)))))

                            ((string=? field-name "valid")
                             (set! validity (sexp->validity field)))

                            ((string=? field-name "propagate")
                             (set! propagate #t))))))))
             (cdr items))

            ;; Validate required fields
            (if (and issuer subject tag)
                (make-cert issuer subject tag validity propagate)
                (error "Missing required certificate fields")))
          (error "Invalid certificate s-expression" sexp))))

  (define (signature->sexp sig)
    (sexp-list (list
                (sexp-atom "signature")
                (sexp-list (list
                            (sexp-atom "hash")
                            (sexp-atom (hash-alg->string (signature-hash-alg sig)))
                            (sexp-bytes (signature-cert-hash sig))))
                (sexp-bytes (signature-sig-bytes sig)))))

  (define (signed-cert->sexp sc)
    (sexp-list (list
                (cert->sexp (signed-cert-cert sc))
                (signature->sexp (signed-cert-signature sc)))))

  (define (signed-cert->string sc)
    (sexp->string-indent (signed-cert->sexp sc) ""))

  (define (sexp->signed-cert sexp)
    (if (not (sexp-list? sexp))
        (error "Invalid signed certificate s-expression" sexp))
    (let ((items (list-items sexp)))
      (if (= (length items) 2)
          (let ((cert-sexp (car items))
                (sig-sexp (cadr items)))
            (let ((cert (sexp->cert cert-sexp)))
              (if (and (sexp-list? sig-sexp)
                       (>= (length (list-items sig-sexp)) 1)
                       (sexp-atom? (car (list-items sig-sexp)))
                       (string=? (atom-value (car (list-items sig-sexp))) "signature"))
                  (let ((sig-items (cdr (list-items sig-sexp))))
                    (let ((hash-alg hash-alg-sha512)
                          (cert-hash #f)
                          (sig-bytes #f))
                      ;; Parse signature fields
                      (for-each
                       (lambda (field)
                         (cond
                          ((and (sexp-list? field)
                                (>= (length (list-items field)) 3)
                                (sexp-atom? (car (list-items field)))
                                (string=? (atom-value (car (list-items field))) "hash"))
                           (set! hash-alg (string->hash-alg
                                           (atom-value (cadr (list-items field)))))
                           (set! cert-hash (bytes-value (caddr (list-items field)))))

                          ((sexp-bytes? field)
                           (set! sig-bytes (bytes-value field)))))
                       sig-items)

                      (if (and cert-hash sig-bytes)
                          (make-signed-cert
                           cert
                           (make-signature hash-alg cert-hash sig-bytes))
                          (error "Missing signature fields"))))
                  (error "Invalid signature s-expression" sig-sexp))))
          (error "Invalid signed certificate s-expression" sexp))))

  (define (signed-cert-of-string str)
    (sexp->signed-cert (parse-sexp str)))

  ;;; Certificate operations

  (define (create-cert issuer subject tag #!key validity propagate)
    "Create a new certificate"
    (make-cert issuer subject tag validity (or propagate #f)))

  (define (sign-cert cert private-key)
    "Sign a certificate with a private key"
    ;; Convert cert to canonical s-expression
    (let* ((cert-sexp (cert->sexp cert))
           (canonical (sexp->string cert-sexp)))

      ;; Hash the certificate using SHA-512
      (let ((cert-hash (sha512-hash canonical)))

        ;; Sign the hash
        (let ((sig-bytes (ed25519-sign private-key cert-hash)))

          ;; Create signed certificate
          (make-signed-cert
           cert
           (make-signature hash-alg-sha512 cert-hash sig-bytes))))))

  (define (verify-signed-cert sc public-key)
    "Verify a signed certificate"
    ;; Recompute certificate hash
    (let* ((cert-sexp (cert->sexp (signed-cert-cert sc)))
           (canonical (sexp->string cert-sexp))
           (computed-hash (sha512-hash canonical)))

      ;; Check hash matches
      (let ((sig (signed-cert-signature sc)))
        (if (not (equal? computed-hash (signature-cert-hash sig)))
            #f
            ;; Verify signature
            (ed25519-verify public-key computed-hash (signature-sig-bytes sig))))))

  (define (tag-implies tag1 tag2)
    "Check if tag1 implies tag2 (tag1 >= tag2)"
    (cond
     ((all-perms? tag1) #t)  ; AllPerms grants everything
     ((all-perms? tag2) #f)  ; Nothing but AllPerms grants AllPerms
     ((and (tag? tag1) (tag? tag2))
      ;; Simple equality check for now
      ;; Production should support tag intersection/subset semantics
      (equal? (tag-sexp tag1) (tag-sexp tag2)))
     (else #f)))

  (define (verify-chain root-key certs target-tag)
    "Verify a delegation chain.
     Verifies that:
     1. Each cert is signed by its issuer
     2. Each cert's issuer matches previous cert's subject
     3. Tags are properly delegated (each tag implies the next)
     4. Final cert grants target_tag
     5. All certs allow propagation (except possibly the last)"

    (define (verify-links current-principal remaining-certs current-tag)
      (if (null? remaining-certs)
          ;; End of chain: check if current tag implies target
          (if (tag-implies current-tag target-tag)
              #t
              (error "Tag not granted by certificate chain"))

          ;; Process next certificate
          (let* ((sc (car remaining-certs))
                 (cert (signed-cert-cert sc))
                 (rest (cdr remaining-certs)))

            ;; Check issuer matches current principal
            (let ((issuer (cert-issuer cert)))
              (cond
               ((and (key-principal? current-principal)
                     (key-principal? issuer)
                     (equal? (principal-public-key current-principal)
                             (principal-public-key issuer)))
                #t)

               ((and (keyhash-principal? current-principal)
                     (keyhash-principal? issuer)
                     (equal? (principal-hash current-principal)
                             (principal-hash issuer)))
                #t)

               (else
                (error "Chain break: issuer doesn't match"))))

            ;; Verify signature
            (let ((issuer-key
                   (cond
                    ((key-principal? current-principal)
                     (principal-public-key current-principal))
                    (else
                     (error "Cannot verify with key hash (need actual key)")))))

              (if (not (verify-signed-cert sc issuer-key))
                  (error "Invalid signature")))

            ;; Check tag delegation
            (if (not (tag-implies current-tag (cert-tag cert)))
                (error "Tag not properly delegated"))

            ;; Check propagation allowed (except for last cert)
            (if (and (not (null? rest))
                     (not (cert-propagate cert)))
                (error "Delegation not allowed (propagate=false)"))

            ;; Continue with next link
            (verify-links (cert-subject cert) rest (cert-tag cert)))))

    ;; Start with root key and AllPerms
    (verify-links (make-key-principal root-key) certs (make-all-perms)))

  ) ;; end module

;;;
;;; Example usage:
;;;
;;; (import cert crypto-ffi)
;;;
;;; ;; Generate keys
;;; (define alice-keys (ed25519-keypair))
;;; (define bob-keys (ed25519-keypair))
;;;
;;; ;; Alice delegates read permission to Bob
;;; (define read-tag
;;;   (make-tag (sexp-list (list (sexp-atom "read")
;;;                              (sexp-atom "/data")))))
;;;
;;; (define cert
;;;   (create-cert
;;;     (make-key-principal (car alice-keys))  ; issuer: Alice's public key
;;;     (make-key-principal (car bob-keys))    ; subject: Bob's public key
;;;     read-tag
;;;     propagate: #f))
;;;
;;; (define signed-cert
;;;   (sign-cert cert (cadr alice-keys)))  ; Alice's private key
;;;
;;; ;; Verify Bob has read permission
;;; (define can-read
;;;   (verify-chain (car alice-keys) (list signed-cert) read-tag))
;;;
