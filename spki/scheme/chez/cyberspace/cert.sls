;;; SPKI Scheme - Certificate Types and Operations
;;; Chez Scheme Port
;;;
;;; SPKI certificates and operations for:
;;; - Creating certificates
;;; - Signing certificates (Ed25519, ML-DSA, SPHINCS+, hybrid)
;;; - Verifying certificates
;;; - Checking delegation chains
;;;
;;; Follows SPKI/SDSI specification with Ed25519 signatures.
;;;
;;; Ported from Chicken's cert.scm.
;;; Changes: module -> library, SRFI-9 records -> R6RS,
;;;          #!key/#!optional -> rest + get-key/get-opt,
;;;          srfi-13/srfi-14 removed (unused in practice).

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
          (only (chezscheme) format)
          (cyberspace chicken-compatibility blob)
          (cyberspace chicken-compatibility chicken)
          (cyberspace sexp)
          (cyberspace crypto-ffi)
          (cyberspace pq-crypto))

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

  (define-record-type (key-principal make-key-principal key-principal?)
    (fields (immutable public-key principal-public-key)))

  (define-record-type (keyhash-principal make-keyhash-principal keyhash-principal?)
    (fields (immutable hash-alg principal-hash-alg)
            (immutable hash principal-hash)))

  ;;; Authorization tags

  (define-record-type (tag make-tag tag?)
    (fields (immutable sexp tag-sexp)))

  (define-record-type (all-perms make-all-perms all-perms?)
    (fields))

  ;;; Time validity

  (define-record-type (validity make-validity validity?)
    (fields (immutable not-before validity-not-before)
            (immutable not-after validity-not-after)))

  ;;; Certificate

  (define-record-type (cert make-cert cert?)
    (fields (immutable issuer cert-issuer)
            (immutable subject cert-subject)
            (immutable tag cert-tag)
            (immutable validity cert-validity)
            (immutable propagate cert-propagate)))

  ;;; Signature
  ;;; Supports: ed25519, ml-dsa-65, sphincs+, hybrid

  (define-record-type (signature make-signature-internal signature?)
    (fields (immutable hash-alg signature-hash-alg)
            (immutable cert-hash signature-cert-hash)
            (immutable sig-bytes signature-sig-bytes)
            (immutable sig-alg signature-sig-alg)))

  ;; Backward-compatible constructor (defaults to ed25519)
  (define (make-signature hash-alg cert-hash sig-bytes . rest)
    (let ((sig-alg (get-opt rest 0 'ed25519)))
      (make-signature-internal hash-alg cert-hash sig-bytes sig-alg)))

  ;;; Signed certificate

  (define-record-type (signed-cert make-signed-cert signed-cert?)
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

  (define (sexp->principal sx)
    (cond
     ((sexp-bytes? sx)
      (make-key-principal (bytes-value sx)))

     ((sexp-list? sx)
      (let ((items (list-items sx)))
        (if (and (>= (length items) 3)
                 (sexp-atom? (car items))
                 (string=? (atom-value (car items)) "hash"))
            (let ((alg-str (atom-value (cadr items)))
                  (hash (bytes-value (caddr items))))
              (make-keyhash-principal (string->hash-alg alg-str) hash))
            (error 'sexp->principal "Invalid principal s-expression" sx))))

     (else
      (error 'sexp->principal "Invalid principal s-expression" sx))))

  (define (tag->sexp tg)
    (cond
     ((tag? tg)
      (tag-sexp tg))

     ((all-perms? tg)
      (sexp-list (list (sexp-atom "*"))))

     (else
      (error 'tag->sexp "Invalid tag" tg))))

  (define (sexp->tag sx)
    (if (and (sexp-list? sx)
             (= (length (list-items sx)) 1)
             (sexp-atom? (car (list-items sx)))
             (string=? (atom-value (car (list-items sx))) "*"))
        (make-all-perms)
        (make-tag sx)))

  (define (validity->sexp v)
    (let ((not-before (validity-not-before v))
          (not-after (validity-not-after v)))
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

  (define (sexp->validity sx)
    (when (not (sexp-list? sx))
      (error 'sexp->validity "Invalid validity s-expression" sx))
    (let ((items (list-items sx)))
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
                       (error 'sexp->validity "Invalid not-before" before-sexp)))
                  (not-after
                   (if (and (sexp-list? after-sexp)
                            (= (length (list-items after-sexp)) 2)
                            (sexp-atom? (car (list-items after-sexp)))
                            (string=? (atom-value (car (list-items after-sexp))) "not-after"))
                       (atom-value (cadr (list-items after-sexp)))
                       (error 'sexp->validity "Invalid not-after" after-sexp))))
              (make-validity not-before not-after)))
          (error 'sexp->validity "Invalid validity s-expression" sx))))

  (define (cert->sexp c)
    (let ((base (list
                 (sexp-atom "cert")
                 (sexp-list (list (sexp-atom "issuer")
                                  (principal->sexp (cert-issuer c))))
                 (sexp-list (list (sexp-atom "subject")
                                  (principal->sexp (cert-subject c))))
                 (sexp-list (list (sexp-atom "tag")
                                  (tag->sexp (cert-tag c)))))))
      (let ((with-validity
             (if (cert-validity c)
                 (append base (list (validity->sexp (cert-validity c))))
                 base)))
        (let ((with-propagate
               (if (cert-propagate c)
                   (append with-validity (list (sexp-list (list (sexp-atom "propagate")))))
                   with-validity)))
          (sexp-list with-propagate)))))

  (define (sexp->cert sx)
    (when (not (sexp-list? sx))
      (error 'sexp->cert "Invalid certificate s-expression" sx))
    (let ((items (list-items sx)))
      (if (and (>= (length items) 1)
               (sexp-atom? (car items))
               (string=? (atom-value (car items)) "cert"))
          (let ((issuer #f)
                (subject #f)
                (tg #f)
                (v #f)
                (propagate #f))
            ;; Parse fields
            (for-each
             (lambda (field)
               (when (sexp-list? field)
                 (let ((field-items (list-items field)))
                   (when (and (>= (length field-items) 1)
                              (sexp-atom? (car field-items)))
                     (let ((field-name (atom-value (car field-items))))
                       (cond
                        ((string=? field-name "issuer")
                         (when (>= (length field-items) 2)
                           (set! issuer (sexp->principal (cadr field-items)))))

                        ((string=? field-name "subject")
                         (when (>= (length field-items) 2)
                           (set! subject (sexp->principal (cadr field-items)))))

                        ((string=? field-name "tag")
                         (when (>= (length field-items) 2)
                           (set! tg (sexp->tag (cadr field-items)))))

                        ((string=? field-name "valid")
                         (set! v (sexp->validity field)))

                        ((string=? field-name "propagate")
                         (set! propagate #t))))))))
             (cdr items))

            ;; Validate required fields
            (if (and issuer subject tg)
                (make-cert issuer subject tg v propagate)
                (error 'sexp->cert "Missing required certificate fields")))
          (error 'sexp->cert "Invalid certificate s-expression" sx))))

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

  (define (sexp->signed-cert sx)
    (when (not (sexp-list? sx))
      (error 'sexp->signed-cert "Invalid signed certificate s-expression" sx))
    (let ((items (list-items sx)))
      (if (= (length items) 2)
          (let ((cert-sx (car items))
                (sig-sx (cadr items)))
            (let ((c (sexp->cert cert-sx)))
              (if (and (sexp-list? sig-sx)
                       (>= (length (list-items sig-sx)) 1)
                       (sexp-atom? (car (list-items sig-sx)))
                       (string=? (atom-value (car (list-items sig-sx))) "signature"))
                  (let ((sig-items (cdr (list-items sig-sx))))
                    (let ((ha hash-alg-sha512)
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
                           (set! ha (string->hash-alg
                                     (atom-value (cadr (list-items field)))))
                           (set! cert-hash (bytes-value (caddr (list-items field)))))

                          ((sexp-bytes? field)
                           (set! sig-bytes (bytes-value field)))))
                       sig-items)

                      (if (and cert-hash sig-bytes)
                          (make-signed-cert
                           c
                           (make-signature ha cert-hash sig-bytes))
                          (error 'sexp->signed-cert "Missing signature fields"))))
                  (error 'sexp->signed-cert "Invalid signature s-expression" sig-sx))))
          (error 'sexp->signed-cert "Invalid signed certificate s-expression" sx))))

  (define (signed-cert-of-string str)
    (sexp->signed-cert (parse-sexp str)))

  ;;; Certificate operations

  (define (create-cert issuer subject tg . opts)
    "Create a new certificate"
    (let ((v (get-key opts 'validity: #f))
          (propagate (get-key opts 'propagate: #f)))
      (make-cert issuer subject tg v (or propagate #f))))

  (define (sign-cert c private-key . rest)
    "Sign a certificate with a private key.
     algorithm: ed25519 (default), ml-dsa-65, sphincs+, hybrid
     For hybrid: provide both private-key (ed25519) and pq-private-key (ml-dsa)"
    (let ((algorithm (get-opt rest 0 'ed25519))
          (pq-private-key (get-opt rest 1 #f)))
      ;; Convert cert to canonical s-expression
      (let* ((cert-sx (cert->sexp c))
             (canonical (sexp->string cert-sx)))

        ;; Hash the certificate using SHA-512
        (let ((cert-hash (sha512-hash canonical)))

          ;; Sign based on algorithm
          (let ((sig-bytes
                 (case algorithm
                   ((ed25519)
                    (ed25519-sign private-key cert-hash))

                   ((ml-dsa-65 ml-dsa)
                    (ml-dsa-sign cert-hash private-key))

                   ((sphincs+ sphincs+-shake-256s)
                    (sphincs+-sign cert-hash private-key))

                   ((hybrid)
                    (unless pq-private-key
                      (error 'sign-cert "Hybrid requires both ed25519 and ml-dsa private keys"))
                    `(hybrid-signature
                      (ed25519 ,(ed25519-sign private-key cert-hash))
                      (ml-dsa ,(ml-dsa-sign cert-hash pq-private-key))))

                   (else
                    (error 'sign-cert "Unknown algorithm" algorithm)))))

            ;; Create signed certificate
            (make-signed-cert
             c
             (make-signature hash-alg-sha512 cert-hash sig-bytes algorithm)))))))

  (define (verify-signed-cert sc public-key . rest)
    "Verify a signed certificate.
     For hybrid signatures: provide both public-key (ed25519) and pq-public-key (ml-dsa)"
    (let ((pq-public-key (get-opt rest 0 #f)))
      ;; Recompute certificate hash
      (let* ((cert-sx (cert->sexp (signed-cert-cert sc)))
             (canonical (sexp->string cert-sx))
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

                ((ml-dsa-65 ml-dsa)
                 (ml-dsa-verify computed-hash (signature-sig-bytes sig) public-key))

                ((sphincs+ sphincs+-shake-256s)
                 (sphincs+-verify computed-hash (signature-sig-bytes sig) public-key))

                ((hybrid)
                 (let ((hybrid-sig (signature-sig-bytes sig)))
                   (unless pq-public-key
                     (error 'verify-signed-cert "Hybrid requires both ed25519 and ml-dsa public keys"))
                   (and (pair? hybrid-sig)
                        (eq? (car hybrid-sig) 'hybrid-signature)
                        (let ((ed-sig (cadr (assq 'ed25519 (cdr hybrid-sig))))
                              (pq-sig (cadr (assq 'ml-dsa (cdr hybrid-sig)))))
                          (and ed-sig pq-sig
                               (ed25519-verify public-key computed-hash ed-sig)
                               (ml-dsa-verify computed-hash pq-sig pq-public-key))))))

                (else
                 (error 'verify-signed-cert "Unknown signature algorithm" sig-alg))))))))

  (define (tag-implies tag1 tag2)
    "Check if tag1 implies tag2 (tag1 >= tag2)"
    (cond
     ((all-perms? tag1) #t)
     ((all-perms? tag2) #f)
     ((and (tag? tag1) (tag? tag2))
      (equal? (tag-sexp tag1) (tag-sexp tag2)))
     (else #f)))

  (define (verify-chain root-key certs target-tag)
    "Verify a delegation chain."

    (define (verify-links current-principal remaining-certs current-tag)
      (if (null? remaining-certs)
          ;; End of chain: check if current tag implies target
          (if (tag-implies current-tag target-tag)
              #t
              (error 'verify-chain "Tag not granted by certificate chain"))

          ;; Process next certificate
          (let* ((sc (car remaining-certs))
                 (c (signed-cert-cert sc))
                 (rest-certs (cdr remaining-certs)))

            ;; Check issuer matches current principal
            (let ((iss (cert-issuer c)))
              (cond
               ((and (key-principal? current-principal)
                     (key-principal? iss)
                     (equal? (principal-public-key current-principal)
                             (principal-public-key iss)))
                #t)

               ((and (keyhash-principal? current-principal)
                     (keyhash-principal? iss)
                     (equal? (principal-hash current-principal)
                             (principal-hash iss)))
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

              (when (not (verify-signed-cert sc issuer-key))
                (error 'verify-chain "Invalid signature")))

            ;; Check tag delegation
            (when (not (tag-implies current-tag (cert-tag c)))
              (error 'verify-chain "Tag not properly delegated"))

            ;; Check propagation allowed (except for last cert)
            (when (and (not (null? rest-certs))
                       (not (cert-propagate c)))
              (error 'verify-chain "Delegation not allowed (propagate=false)"))

            ;; Continue with next link
            (verify-links (cert-subject c) rest-certs (cert-tag c)))))

    ;; Start with root key and AllPerms
    (verify-links (make-key-principal root-key) certs (make-all-perms)))

) ;; end library
