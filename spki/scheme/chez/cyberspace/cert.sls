;;; SPKI Scheme - Certificate Types and Operations
;;; Library of Cyberspace - Chez Port
;;;
;;; SPKI certificates with Ed25519 signatures:
;;;   - Creating certificates
;;;   - Signing certificates
;;;   - Verifying certificates
;;;   - Checking delegation chains
;;;
;;; Ported from Chicken's cert.scm.
;;; Changes: module -> library, SRFI-9 -> R6RS records,
;;;          #!key/#!optional -> get-key/get-opt,
;;;          pq-crypto deferred (ed25519 only).

(library (cyberspace cert)
  (export
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
    signature-sig-alg
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

  (import (rnrs)
          (only (chezscheme) format printf)
          (cyberspace sexp)
          (cyberspace crypto-ffi)
          (cyberspace chicken-compatibility chicken)
          (cyberspace chicken-compatibility blob))

  ;;; Hash algorithms
  (define hash-alg-sha512 'sha512)

  (define (hash-alg->string alg)
    (case alg
      ((sha512) "sha512")
      (else (error 'hash-alg->string "Unknown hash algorithm" alg))))

  (define (string->hash-alg str)
    (cond
     ((string=? str "sha512") hash-alg-sha512)
     (else (error 'string->hash-alg "Unknown hash algorithm" str))))

  ;;; Principal: either a key or a hash of a key

  (define-record-type (<key-principal> make-key-principal-internal key-principal?)
    (fields (immutable public-key principal-public-key)))

  (define-record-type (<keyhash-principal> make-keyhash-principal-internal keyhash-principal?)
    (fields (immutable hash-alg principal-hash-alg)
            (immutable hash principal-hash)))

  ;; Public constructors
  (define (make-key-principal public-key)
    (make-key-principal-internal public-key))

  (define (make-keyhash-principal alg hash)
    (make-keyhash-principal-internal alg hash))

  ;;; Authorization tags

  (define-record-type (<tag> make-tag-internal tag?)
    (fields (immutable sexp tag-sexp)))

  (define-record-type (<all-perms> make-all-perms-internal all-perms?))

  ;; Public constructors
  (define (make-tag sexp)
    (make-tag-internal sexp))

  (define (make-all-perms)
    (make-all-perms-internal))

  ;;; Time validity

  (define-record-type (<validity> make-validity validity?)
    (fields (immutable not-before validity-not-before)
            (immutable not-after validity-not-after)))

  ;;; Certificate

  (define-record-type (<cert> make-cert cert?)
    (fields (immutable issuer cert-issuer)
            (immutable subject cert-subject)
            (immutable tag cert-tag)
            (immutable validity cert-validity)
            (immutable propagate cert-propagate)))

  ;;; Signature
  ;;; Supports multiple algorithms: ed25519, ml-dsa-65, sphincs+, hybrid
  ;;; (PQ algorithms deferred in Chez port -- ed25519 only for now)

  (define-record-type (<signature> make-signature-internal signature?)
    (fields (immutable hash-alg signature-hash-alg)
            (immutable cert-hash signature-cert-hash)
            (immutable sig-bytes signature-sig-bytes)
            (immutable sig-alg signature-sig-alg)))

  ;; Backward-compatible constructor (defaults to ed25519)
  (define (make-signature hash-alg cert-hash sig-bytes . opts)
    (let ((sig-alg (get-opt opts 0 'ed25519)))
      (make-signature-internal hash-alg cert-hash sig-bytes sig-alg)))

  ;;; Signed certificate

  (define-record-type (<signed-cert> make-signed-cert signed-cert?)
    (fields (immutable cert signed-cert-cert)
            (immutable signature signed-cert-signature)))

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
      (error 'principal->sexp "Invalid principal" principal))))

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
            (error 'sexp->principal "Invalid principal s-expression" sexp))))

     (else
      (error 'sexp->principal "Invalid principal s-expression" sexp))))

  (define (tag->sexp tag)
    (cond
     ((tag? tag)
      (tag-sexp tag))

     ((all-perms? tag)
      (sexp-list (list (sexp-atom "*"))))

     (else
      (error 'tag->sexp "Invalid tag" tag))))

  (define (sexp->tag sexp)
    (if (and (sexp-list? sexp)
             (= (length (list-items sexp)) 1)
             (sexp-atom? (car (list-items sexp)))
             (string=? (atom-value (car (list-items sexp))) "*"))
        (make-all-perms)
        (make-tag sexp)))

  (define (validity->sexp validity)
    (let ((not-before (validity-not-before validity))
          (not-after (validity-not-after validity)))
      (sexp-list
        (filter (lambda (x) x)
          (list
            (sexp-atom "valid")
            (and not-before
                 (sexp-list (list (sexp-atom "not-before")
                                  (sexp-atom (number->string not-before)))))
            (and not-after
                 (sexp-list (list (sexp-atom "not-after")
                                  (sexp-atom (number->string not-after))))))))))

  (define (sexp->validity sexp)
    (if (not (sexp-list? sexp))
        (error 'sexp->validity "Invalid validity s-expression" sexp))
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
                       (let ((v (atom-value (cadr (list-items before-sexp)))))
                         (or (string->number v) v))
                       (error 'sexp->validity "Invalid not-before" before-sexp)))
                  (not-after
                   (if (and (sexp-list? after-sexp)
                            (= (length (list-items after-sexp)) 2)
                            (sexp-atom? (car (list-items after-sexp)))
                            (string=? (atom-value (car (list-items after-sexp))) "not-after"))
                       (let ((v (atom-value (cadr (list-items after-sexp)))))
                         (or (string->number v) v))
                       (error 'sexp->validity "Invalid not-after" after-sexp))))
              (make-validity not-before not-after)))
          (error 'sexp->validity "Invalid validity s-expression" sexp))))

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
        (error 'sexp->cert "Invalid certificate s-expression" sexp))
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
                (error 'sexp->cert "Missing required certificate fields")))
          (error 'sexp->cert "Invalid certificate s-expression" sexp))))

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
        (error 'sexp->signed-cert "Invalid signed certificate s-expression" sexp))
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
                          (error 'sexp->signed-cert "Missing signature fields"))))
                  (error 'sexp->signed-cert "Invalid signature s-expression" sig-sexp))))
          (error 'sexp->signed-cert "Invalid signed certificate s-expression" sexp))))

  (define (signed-cert-of-string str)
    (sexp->signed-cert (parse-sexp str)))

  ;;; Certificate operations

  ;; Create a new certificate
  (define (create-cert issuer subject tag . opts)
    (let ((validity (get-key opts 'validity: #f))
          (propagate (get-key opts 'propagate: #f)))
      (make-cert issuer subject tag validity (or propagate #f))))

  ;; Sign a certificate with a private key.
  ;; Ed25519 only in Chez port (PQ algorithms deferred).
  (define (sign-cert cert private-key . opts)
    (let ((algorithm (get-opt opts 0 'ed25519))
          (pq-private-key (get-opt opts 1 #f)))

      ;; Convert cert to canonical s-expression
      (let* ((cert-sexp (cert->sexp cert))
             (canonical (sexp->string cert-sexp)))

        ;; Hash the certificate using SHA-512
        (let ((cert-hash (sha512-hash canonical)))

          ;; Sign based on algorithm
          (let ((sig-bytes
                 (case algorithm
                   ((ed25519)
                    (ed25519-sign private-key cert-hash))

                   ((ml-dsa-65 ml-dsa sphincs+ sphincs+-shake-256s hybrid)
                    (error 'sign-cert
                           "Post-quantum algorithms not yet available in Chez port"
                           algorithm))

                   (else
                    (error 'sign-cert "Unknown algorithm" algorithm)))))

            ;; Create signed certificate
            (make-signed-cert
             cert
             (make-signature hash-alg-sha512 cert-hash sig-bytes algorithm)))))))

  ;; Verify a signed certificate.
  ;; Ed25519 only in Chez port (PQ algorithms deferred).
  (define (verify-signed-cert sc public-key . opts)
    (let ((pq-public-key (get-opt opts 0 #f)))

      ;; Recompute certificate hash
      (let* ((cert-sexp (cert->sexp (signed-cert-cert sc)))
             (canonical (sexp->string cert-sexp))
             (computed-hash (sha512-hash canonical)))

        ;; Check hash matches
        (let* ((sig (signed-cert-signature sc))
               (sig-alg (or (signature-sig-alg sig) 'ed25519)))
          (if (not (equal? computed-hash (signature-cert-hash sig)))
              #f
              ;; Verify signature based on algorithm
              (case sig-alg
                ((ed25519)
                 (ed25519-verify public-key computed-hash (signature-sig-bytes sig)))

                ((ml-dsa-65 ml-dsa sphincs+ sphincs+-shake-256s hybrid)
                 (error 'verify-signed-cert
                        "Post-quantum algorithms not yet available in Chez port"
                        sig-alg))

                (else
                 (error 'verify-signed-cert "Unknown signature algorithm" sig-alg))))))))

  ;; Check if tag1 implies tag2 (tag1 >= tag2)
  (define (tag-implies tag1 tag2)
    (cond
     ((all-perms? tag1) #t)  ; AllPerms grants everything
     ((all-perms? tag2) #f)  ; Nothing but AllPerms grants AllPerms
     ((and (tag? tag1) (tag? tag2))
      ;; Structural equality on sexp records
      ;; (R6RS equal? returns #f on opaque records)
      (sexp-equal? (tag-sexp tag1) (tag-sexp tag2)))
     (else #f)))

  ;; Verify a delegation chain:
  ;; 1. Each cert is signed by its issuer
  ;; 2. Each cert's issuer matches previous cert's subject
  ;; 3. Tags are properly delegated (each tag implies the next)
  ;; 4. Final cert grants target_tag
  ;; 5. All certs allow propagation (except possibly the last)
  (define (verify-chain root-key certs target-tag)
    (define (verify-links current-principal remaining-certs current-tag)
      (if (null? remaining-certs)
          ;; End of chain: check if current tag implies target
          (if (tag-implies current-tag target-tag)
              #t
              (error 'verify-chain "Tag not granted by certificate chain"))

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
                (error 'verify-chain "Chain break: issuer doesn't match"))))

            ;; Verify signature
            (let ((issuer-key
                   (cond
                    ((key-principal? current-principal)
                     (principal-public-key current-principal))
                    (else
                     (error 'verify-chain "Cannot verify with key hash (need actual key)")))))

              (if (not (verify-signed-cert sc issuer-key))
                  (error 'verify-chain "Invalid signature")))

            ;; Check tag delegation
            (if (not (tag-implies current-tag (cert-tag cert)))
                (error 'verify-chain "Tag not properly delegated"))

            ;; Check propagation allowed (except for last cert)
            (if (and (not (null? rest))
                     (not (cert-propagate cert)))
                (error 'verify-chain "Delegation not allowed (propagate=false)"))

            ;; Continue with next link
            (verify-links (cert-subject cert) rest (cert-tag cert)))))

    ;; Start with root key and AllPerms
    (verify-links (make-key-principal root-key) certs (make-all-perms)))

) ;; end library
