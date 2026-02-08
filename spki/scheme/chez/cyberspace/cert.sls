;;; SPKI Scheme - Certificate Types and Operations (Chez Port)
;;; Library of Cyberspace
;;;
;;; SPKI certificates with Ed25519 signatures:
;;;   - Creating certificates
;;;   - Signing certificates
;;;   - Verifying certificates
;;;   - Checking delegation chains
;;;
;;; Post-quantum signature paths (ML-DSA, SPHINCS+) are guarded
;;; pending port of pq-crypto.  Ed25519 is fully operational.
;;;
;;; Ported from cert.scm.
;;; Copyright (c) 2026 Yoyodyne. See LICENSE.

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
          (only (chezscheme) printf format with-output-to-string void)
          (cyberspace sexp)
          (cyberspace crypto-ffi))

  ;; ============================================================
  ;; Hash algorithms
  ;; ============================================================

  (define hash-alg-sha512 'sha512)

  (define (hash-alg->string alg)
    (case alg
      ((sha512) "sha512")
      (else (error 'hash-alg->string "Unknown hash algorithm" alg))))

  (define (string->hash-alg str)
    (cond
     ((string=? str "sha512") hash-alg-sha512)
     (else (error 'string->hash-alg "Unknown hash algorithm" str))))

  ;; ============================================================
  ;; Principal: either a key or a hash of a key
  ;; ============================================================

  (define *key-principal-tag* (list 'key-principal))
  (define *keyhash-principal-tag* (list 'keyhash-principal))

  (define (make-key-principal public-key)
    (vector *key-principal-tag* public-key))

  (define (key-principal? x)
    (and (vector? x) (= (vector-length x) 2)
         (eq? (vector-ref x 0) *key-principal-tag*)))

  (define (principal-public-key p) (vector-ref p 1))

  (define (make-keyhash-principal hash-alg hash)
    (vector *keyhash-principal-tag* hash-alg hash))

  (define (keyhash-principal? x)
    (and (vector? x) (= (vector-length x) 3)
         (eq? (vector-ref x 0) *keyhash-principal-tag*)))

  (define (principal-hash-alg p) (vector-ref p 1))
  (define (principal-hash p) (vector-ref p 2))

  ;; ============================================================
  ;; Authorization tags
  ;; ============================================================

  (define *tag-tag* (list 'tag))
  (define *all-perms-tag* (list 'all-perms))

  (define (make-tag sexp) (vector *tag-tag* sexp))
  (define (tag? x)
    (and (vector? x) (= (vector-length x) 2)
         (eq? (vector-ref x 0) *tag-tag*)))
  (define (tag-sexp t) (vector-ref t 1))

  (define (make-all-perms) (vector *all-perms-tag*))
  (define (all-perms? x)
    (and (vector? x) (= (vector-length x) 1)
         (eq? (vector-ref x 0) *all-perms-tag*)))

  ;; ============================================================
  ;; Time validity
  ;; ============================================================

  (define *validity-tag* (list 'validity))

  (define (make-validity not-before not-after)
    (vector *validity-tag* not-before not-after))

  (define (validity? x)
    (and (vector? x) (= (vector-length x) 3)
         (eq? (vector-ref x 0) *validity-tag*)))

  (define (validity-not-before v) (vector-ref v 1))
  (define (validity-not-after v) (vector-ref v 2))

  ;; ============================================================
  ;; Certificate
  ;; ============================================================

  (define *cert-tag* (list 'cert))

  (define (make-cert issuer subject tag validity propagate)
    (vector *cert-tag* issuer subject tag validity propagate))

  (define (cert? x)
    (and (vector? x) (= (vector-length x) 6)
         (eq? (vector-ref x 0) *cert-tag*)))

  (define (cert-issuer c) (vector-ref c 1))
  (define (cert-subject c) (vector-ref c 2))
  (define (cert-tag c) (vector-ref c 3))
  (define (cert-validity c) (vector-ref c 4))
  (define (cert-propagate c) (vector-ref c 5))

  ;; ============================================================
  ;; Signature
  ;; ============================================================

  (define *sig-tag* (list 'signature))

  (define (make-signature hash-alg cert-hash sig-bytes . rest)
    (let ((sig-alg (if (null? rest) 'ed25519 (car rest))))
      (vector *sig-tag* hash-alg cert-hash sig-bytes sig-alg)))

  (define (signature? x)
    (and (vector? x) (= (vector-length x) 5)
         (eq? (vector-ref x 0) *sig-tag*)))

  (define (signature-hash-alg s) (vector-ref s 1))
  (define (signature-cert-hash s) (vector-ref s 2))
  (define (signature-sig-bytes s) (vector-ref s 3))
  (define (signature-sig-alg s) (vector-ref s 4))

  ;; ============================================================
  ;; Signed certificate
  ;; ============================================================

  (define *signed-cert-tag* (list 'signed-cert))

  (define (make-signed-cert cert signature)
    (vector *signed-cert-tag* cert signature))

  (define (signed-cert? x)
    (and (vector? x) (= (vector-length x) 3)
         (eq? (vector-ref x 0) *signed-cert-tag*)))

  (define (signed-cert-cert sc) (vector-ref sc 1))
  (define (signed-cert-signature sc) (vector-ref sc 2))

  ;; ============================================================
  ;; Conversion to/from s-expressions
  ;; ============================================================

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

  (define (tag->sexp tag)
    (cond
     ((tag? tag) (tag-sexp tag))
     ((all-perms? tag)
      (sexp-list (list (sexp-atom "*"))))
     (else
      (error 'tag->sexp "Invalid tag" tag))))

  (define (sexp->tag sx)
    (if (and (sexp-list? sx)
             (= (length (list-items sx)) 1)
             (sexp-atom? (car (list-items sx)))
             (string=? (atom-value (car (list-items sx))) "*"))
        (make-all-perms)
        (make-tag sx)))

  (define (validity->sexp val)
    (let ((not-before (validity-not-before val))
          (not-after (validity-not-after val)))
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
    (if (not (sexp-list? sx))
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

  (define (sexp->cert sx)
    (if (not (sexp-list? sx))
        (error 'sexp->cert "Invalid certificate s-expression" sx))
    (let ((items (list-items sx)))
      (if (and (>= (length items) 1)
               (sexp-atom? (car items))
               (string=? (atom-value (car items)) "cert"))
          (let ((issuer #f)
                (subject #f)
                (tag #f)
                (validity #f)
                (propagate #f))
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
            (if (and issuer subject tag)
                (make-cert issuer subject tag validity propagate)
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
    (if (not (sexp-list? sx))
        (error 'sexp->signed-cert "Invalid signed certificate s-expression" sx))
    (let ((items (list-items sx)))
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
          (error 'sexp->signed-cert "Invalid signed certificate s-expression" sx))))

  (define (signed-cert-of-string str)
    (sexp->signed-cert (parse-sexp str)))

  ;; ============================================================
  ;; Certificate operations
  ;; ============================================================

  (define (create-cert issuer subject tag . opts)
    "Create a new certificate.
     (create-cert issuer subject tag validity: v propagate: #t)"
    (let ((validity (let loop ((r opts))
                      (cond ((null? r) #f)
                            ((null? (cdr r)) #f)
                            ((eq? (car r) 'validity:) (cadr r))
                            (else (loop (cddr r))))))
          (propagate (let loop ((r opts))
                       (cond ((null? r) #f)
                             ((null? (cdr r)) #f)
                             ((eq? (car r) 'propagate:) (cadr r))
                             (else (loop (cddr r)))))))
      (make-cert issuer subject tag validity (or propagate #f))))

  (define (sign-cert cert private-key . rest)
    "Sign a certificate with a private key.
     (sign-cert cert sk)               -- Ed25519 (default)
     (sign-cert cert sk 'ml-dsa-65)    -- Post-quantum (not yet ported)"
    (let ((algorithm (if (null? rest) 'ed25519 (car rest))))
      (let* ((cert-sx (cert->sexp cert))
             (canonical (sexp->string cert-sx))
             (cert-hash (sha512-hash canonical)))
        (let ((sig-bytes
               (case algorithm
                 ((ed25519)
                  (ed25519-sign private-key cert-hash))
                 ((ml-dsa-65 ml-dsa sphincs+ sphincs+-shake-256s hybrid)
                  (error 'sign-cert
                         "Post-quantum signatures not yet ported to Chez"
                         algorithm))
                 (else
                  (error 'sign-cert "Unknown algorithm" algorithm)))))
          (make-signed-cert
           cert
           (make-signature hash-alg-sha512 cert-hash sig-bytes algorithm))))))

  (define (verify-signed-cert sc public-key . rest)
    "Verify a signed certificate."
    (let* ((cert-sx (cert->sexp (signed-cert-cert sc)))
           (canonical (sexp->string cert-sx))
           (computed-hash (sha512-hash canonical))
           (sig (signed-cert-signature sc))
           (sig-alg (or (signature-sig-alg sig) 'ed25519)))
      (if (not (bytevector=? computed-hash (signature-cert-hash sig)))
          #f
          (case sig-alg
            ((ed25519)
             (ed25519-verify public-key computed-hash (signature-sig-bytes sig)))
            ((ml-dsa-65 ml-dsa sphincs+ sphincs+-shake-256s hybrid)
             (error 'verify-signed-cert
                    "Post-quantum verification not yet ported to Chez"
                    sig-alg))
            (else
             (error 'verify-signed-cert "Unknown signature algorithm" sig-alg))))))

  (define (tag-implies tag1 tag2)
    "Check if tag1 implies tag2 (tag1 >= tag2)."
    (cond
     ((all-perms? tag1) #t)
     ((all-perms? tag2) #f)
     ((and (tag? tag1) (tag? tag2))
      (equal? (tag-sexp tag1) (tag-sexp tag2)))
     (else #f)))

  (define (verify-chain root-key certs target-tag)
    ;; Verify a delegation chain.
    (define (verify-links current-principal remaining-certs current-tag)
      (if (null? remaining-certs)
          (if (tag-implies current-tag target-tag)
              #t
              (error 'verify-chain "Tag not granted by certificate chain"))
          (let* ((sc (car remaining-certs))
                 (cert (signed-cert-cert sc))
                 (rest (cdr remaining-certs)))
            ;; Check issuer matches
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
            ;; Check propagation
            (if (and (not (null? rest))
                     (not (cert-propagate cert)))
                (error 'verify-chain "Delegation not allowed (propagate=false)"))
            ;; Continue
            (verify-links (cert-subject cert) rest (cert-tag cert)))))

    (verify-links (make-key-principal root-key) certs (make-all-perms)))

) ;; end library
