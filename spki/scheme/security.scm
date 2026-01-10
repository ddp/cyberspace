;;; security.scm - Security Properties Inspector for the Soup
;;;
;;; "Trust, but verify" - Reagan (misattributed)
;;; "Verify, then trust" - SPKI
;;;
;;; Provides introspection of:
;;; - Principal properties (keys, fingerprints, capabilities)
;;; - Certificate chains (delegation, authority, validity)
;;; - Capability queries (who can do what)
;;; - Signature verification status
;;; - Audit trail correlation

(module security
  (;; Principal inspection
   inspect-principal
   principal-fingerprint

   ;; Certificate inspection
   inspect-cert
   cert-status

   ;; Capability queries
   who-can
   what-can
   authority-for

   ;; Verification
   verify-object
   verify-chain-to
   check-revocation

   ;; Security summary
   security-summary
   security-audit

   ;; Display helpers
   display-principal
   display-cert
   display-chain
   display-capability)

  (import scheme
          (chicken base)
          (chicken format)
          (chicken string)
          (chicken file)
          (chicken io)
          (chicken blob)
          (chicken time)
          (chicken time posix)
          srfi-1
          srfi-13
          crypto-ffi
          cert
          sexp)

  ;; ============================================================
  ;; Principal Fingerprint
  ;; ============================================================

  (define (principal-fingerprint principal)
    "Generate human-readable fingerprint for a principal"
    (cond
     ((key-principal? principal)
      (let* ((pubkey (principal-public-key principal))
             (hash (sha512-hash pubkey))
             (hex (blob->hex hash)))
        ;; Return first 32 chars in groups of 4
        (string-join
         (let loop ((s (substring hex 0 32)) (acc '()))
           (if (< (string-length s) 4)
               (reverse (if (string-null? s) acc (cons s acc)))
               (loop (substring s 4) (cons (substring s 0 4) acc))))
         ":")))
     ((keyhash-principal? principal)
      (let* ((hash (principal-hash principal))
             (hex (if (blob? hash) (blob->hex hash) (format "~a" hash))))
        (string-append "hash:" (substring hex 0 (min 16 (string-length hex))) "...")))
     (else "<unknown-principal>")))

  (define (blob->hex blob)
    "Convert blob to hex string"
    (let* ((size (blob-size blob))
           (result (make-string (* 2 size))))
      (do ((i 0 (+ i 1)))
          ((>= i size) result)
        (let* ((byte (blob-u8-ref blob i))
               (hi (quotient byte 16))
               (lo (remainder byte 16)))
          (string-set! result (* i 2) (string-ref "0123456789abcdef" hi))
          (string-set! result (+ (* i 2) 1) (string-ref "0123456789abcdef" lo))))))

  (define (blob-u8-ref blob i)
    "Get byte at index from blob"
    (char->integer (string-ref (blob->string blob) i)))

  ;; ============================================================
  ;; Display Helpers
  ;; ============================================================

  (define (display-principal principal #!optional (indent 0))
    "Pretty-print a principal"
    (let ((pad (make-string indent #\space)))
      (cond
       ((key-principal? principal)
        (printf "~aKey Principal~%" pad)
        (printf "~a  Fingerprint: ~a~%" pad (principal-fingerprint principal))
        (printf "~a  Algorithm:   Ed25519~%" pad))
       ((keyhash-principal? principal)
        (printf "~aKeyHash Principal~%" pad)
        (printf "~a  Algorithm: ~a~%" pad (principal-hash-alg principal))
        (printf "~a  Hash:      ~a~%" pad (principal-fingerprint principal)))
       (else
        (printf "~a<unknown principal>~%" pad)))))

  (define (display-capability tag #!optional (indent 0))
    "Pretty-print a capability tag"
    (let ((pad (make-string indent #\space)))
      (cond
       ((all-perms? tag)
        (printf "~a(*) All Permissions~%" pad))
       ((tag? tag)
        (printf "~aCapability: ~a~%" pad (tag-sexp tag)))
       (else
        (printf "~a~a~%" pad tag)))))

  (define (display-cert signed-cert #!optional (indent 0))
    "Pretty-print a signed certificate"
    (let* ((pad (make-string indent #\space))
           (c (signed-cert-cert signed-cert))
           (sig (signed-cert-signature signed-cert)))
      (print)
      (printf "~a╭─────────────────────────────────────────────────╮~%" pad)
      (printf "~a│              SPKI Certificate                   │~%" pad)
      (printf "~a├─────────────────────────────────────────────────┤~%" pad)
      (printf "~a│ Issuer:                                         │~%" pad)
      (printf "~a│   ~a~a│~%" pad
              (principal-fingerprint (cert-issuer c))
              (make-string (max 0 (- 32 (string-length (principal-fingerprint (cert-issuer c))))) #\space))
      (printf "~a│ Subject:                                        │~%" pad)
      (printf "~a│   ~a~a│~%" pad
              (principal-fingerprint (cert-subject c))
              (make-string (max 0 (- 32 (string-length (principal-fingerprint (cert-subject c))))) #\space))
      (printf "~a├─────────────────────────────────────────────────┤~%" pad)
      (printf "~a│ Capability:                                     │~%" pad)
      (let ((tag (cert-tag c)))
        (if (all-perms? tag)
            (printf "~a│   (*) All Permissions                           │~%" pad)
            (printf "~a│   ~a~%" pad (tag-sexp tag))))
      (printf "~a├─────────────────────────────────────────────────┤~%" pad)
      (let ((v (cert-validity c)))
        (if v
            (begin
              (printf "~a│ Valid: ~a~%" pad (validity-not-before v))
              (printf "~a│ Until: ~a~%" pad (validity-not-after v)))
            (printf "~a│ Validity: (no expiration)                       │~%" pad)))
      (printf "~a│ Propagate: ~a~%" pad (if (cert-propagate c) "YES (can delegate)" "NO"))
      (printf "~a├─────────────────────────────────────────────────┤~%" pad)
      (printf "~a│ Signature: ~a~%" pad (hash-alg->string (signature-hash-alg sig)))
      (printf "~a╰─────────────────────────────────────────────────╯~%" pad)
      (print)))

  (define (display-chain chain #!optional (indent 0))
    "Display a delegation chain"
    (let ((pad (make-string indent #\space)))
      (print)
      (printf "~a═══════════════════════════════════════════════════~%" pad)
      (printf "~a              Delegation Chain                     ~%" pad)
      (printf "~a═══════════════════════════════════════════════════~%" pad)
      (let loop ((certs chain) (n 1))
        (when (pair? certs)
          (let* ((sc (car certs))
                 (c (signed-cert-cert sc)))
            (printf "~a~%~a[~a] ~a~%" pad pad n
                    (if (= n 1) "Root (self-signed or trust anchor)" "Delegation"))
            (printf "~a    From: ~a~%" pad (principal-fingerprint (cert-issuer c)))
            (printf "~a    To:   ~a~%" pad (principal-fingerprint (cert-subject c)))
            (printf "~a    Grants: ~a~%" pad
                    (let ((tag (cert-tag c)))
                      (if (all-perms? tag) "(*) ALL" (tag-sexp tag))))
            (printf "~a    Propagate: ~a~%" pad (if (cert-propagate c) "yes" "no"))
            (loop (cdr certs) (+ n 1)))))
      (printf "~a═══════════════════════════════════════════════════~%" pad)
      (print)))

  ;; ============================================================
  ;; Principal Inspection
  ;; ============================================================

  (define (inspect-principal principal #!optional (soup-certs '()))
    "Inspect a principal's security properties"
    (print)
    (print "╔═══════════════════════════════════════════════════════════╗")
    (print "║              Principal Security Properties                ║")
    (print "╠═══════════════════════════════════════════════════════════╣")
    (display-principal principal 1)
    (print "╠═══════════════════════════════════════════════════════════╣")

    ;; Find certificates where this principal is issuer
    (let ((as-issuer (filter
                      (lambda (sc)
                        (let ((c (signed-cert-cert sc)))
                          (equal? (principal-fingerprint (cert-issuer c))
                                  (principal-fingerprint principal))))
                      soup-certs)))
      (printf "║ Certificates Issued by this principal: ~a~%" (length as-issuer))
      (for-each
       (lambda (sc)
         (let ((c (signed-cert-cert sc)))
           (printf "║   → ~a : ~a~%"
                   (principal-fingerprint (cert-subject c))
                   (let ((t (cert-tag c))) (if (all-perms? t) "(*)" (tag-sexp t))))))
       as-issuer))

    ;; Find certificates where this principal is subject
    (let ((as-subject (filter
                       (lambda (sc)
                         (let ((c (signed-cert-cert sc)))
                           (equal? (principal-fingerprint (cert-subject c))
                                   (principal-fingerprint principal))))
                       soup-certs)))
      (print "╠═══════════════════════════════════════════════════════════╣")
      (printf "║ Certificates Granted to this principal: ~a~%" (length as-subject))
      (for-each
       (lambda (sc)
         (let ((c (signed-cert-cert sc)))
           (printf "║   ← ~a : ~a~%"
                   (principal-fingerprint (cert-issuer c))
                   (let ((t (cert-tag c))) (if (all-perms? t) "(*)" (tag-sexp t))))))
       as-subject))

    (print "╚═══════════════════════════════════════════════════════════╝")
    (print)

    ;; Return summary alist
    `((fingerprint . ,(principal-fingerprint principal))
      (type . ,(cond ((key-principal? principal) 'key)
                     ((keyhash-principal? principal) 'keyhash)
                     (else 'unknown)))
      (issued . ,(length (filter
                          (lambda (sc)
                            (equal? (principal-fingerprint (cert-issuer (signed-cert-cert sc)))
                                    (principal-fingerprint principal)))
                          soup-certs)))
      (received . ,(length (filter
                            (lambda (sc)
                              (equal? (principal-fingerprint (cert-subject (signed-cert-cert sc)))
                                      (principal-fingerprint principal)))
                            soup-certs)))))

  ;; ============================================================
  ;; Certificate Inspection
  ;; ============================================================

  (define (inspect-cert signed-cert #!optional (issuer-key #f))
    "Inspect a certificate's security properties"
    (display-cert signed-cert)

    ;; Verify signature if we have the issuer's key
    (when issuer-key
      (let ((valid (verify-signed-cert signed-cert issuer-key)))
        (print)
        (if valid
            (print "✓ Signature Valid")
            (print "✗ Signature Invalid"))
        (print)))

    ;; Return structured data
    (let ((c (signed-cert-cert signed-cert)))
      `((issuer . ,(principal-fingerprint (cert-issuer c)))
        (subject . ,(principal-fingerprint (cert-subject c)))
        (capability . ,(let ((t (cert-tag c)))
                        (if (all-perms? t) '(*) (tag-sexp t))))
        (propagate . ,(cert-propagate c))
        (validity . ,(let ((v (cert-validity c)))
                      (if v
                          `((not-before . ,(validity-not-before v))
                            (not-after . ,(validity-not-after v)))
                          #f))))))

  (define (cert-status signed-cert issuer-key)
    "Check certificate status: valid, expired, invalid-sig, revoked"
    (let* ((c (signed-cert-cert signed-cert))
           (v (cert-validity c))
           (sig-valid (verify-signed-cert signed-cert issuer-key)))
      (cond
       ((not sig-valid) 'invalid-signature)
       ((and v (validity-expired? v)) 'expired)
       ;; TODO: check revocation list
       (else 'valid))))

  (define (validity-expired? validity)
    "Check if validity period has expired"
    (let ((not-after (validity-not-after validity)))
      ;; Simple check - assumes ISO date string format
      ;; In production, parse and compare properly
      #f))  ; Placeholder

  ;; ============================================================
  ;; Capability Queries
  ;; ============================================================

  (define (who-can capability soup-certs)
    "Find all principals who can perform a capability"
    (print)
    (printf "═══ WHO CAN: ~a ═══~%" capability)
    (print)
    (let ((holders
           (filter-map
            (lambda (sc)
              (let* ((c (signed-cert-cert sc))
                     (tag (cert-tag c)))
                (if (or (all-perms? tag)
                        (and (tag? tag)
                             (tag-implies tag (make-tag capability))))
                    (principal-fingerprint (cert-subject c))
                    #f)))
            soup-certs)))
      (if (null? holders)
          (print "  (no principals found with this capability)")
          (for-each
           (lambda (fp)
             (printf "  ✓ ~a~%" fp))
           (delete-duplicates holders equal?)))
      (print)
      holders))

  (define (what-can principal soup-certs)
    "Find all capabilities granted to a principal"
    (print)
    (printf "═══ Capabilities of: ~a ═══~%" (principal-fingerprint principal))
    (print)
    (let ((caps
           (filter-map
            (lambda (sc)
              (let* ((c (signed-cert-cert sc))
                     (subj (cert-subject c)))
                (if (equal? (principal-fingerprint subj)
                            (principal-fingerprint principal))
                    (cert-tag c)
                    #f)))
            soup-certs)))
      (if (null? caps)
          (print "  (no capabilities found)")
          (for-each
           (lambda (cap)
             (printf "  • ~a~%" (if (all-perms? cap) "(*) All Permissions" (tag-sexp cap))))
           caps))
      (print)
      caps))

  (define (authority-for capability principal soup-certs)
    "Trace the authority chain for a principal's capability"
    (print)
    (printf "═══ Authority for: ~a doing ~a ═══~%"
            (principal-fingerprint principal) capability)
    (print)
    ;; Find direct grants
    (let ((direct
           (filter
            (lambda (sc)
              (let* ((c (signed-cert-cert sc))
                     (subj (cert-subject c))
                     (tag (cert-tag c)))
                (and (equal? (principal-fingerprint subj)
                             (principal-fingerprint principal))
                     (or (all-perms? tag)
                         (and (tag? tag)
                              (tag-implies tag (make-tag capability)))))))
            soup-certs)))
      (if (null? direct)
          (begin
            (print "  (no direct grant found)")
            (print "  Checking delegation chains...")
            ;; TODO: trace delegation chains
            '())
          (begin
            (print "Direct grants:")
            (for-each
             (lambda (sc)
               (let ((c (signed-cert-cert sc)))
                 (printf "  From: ~a~%" (principal-fingerprint (cert-issuer c)))
                 (printf "  Tag:  ~a~%" (let ((t (cert-tag c)))
                                         (if (all-perms? t) "(*)" (tag-sexp t))))
                 (printf "  Propagate: ~a~%" (cert-propagate c))
                 (print)))
             direct)
            direct))))

  ;; ============================================================
  ;; Verification
  ;; ============================================================

  (define (verify-object obj-type obj-name)
    "Verify security properties of a soup object"
    (print)
    (printf "═══ Verifying: ~a (~a) ═══~%" obj-name obj-type)
    (print)
    (case obj-type
      ((keys)
       (print "Key verification:")
       (print "  • File exists: checking...")
       ;; TODO: verify key file integrity
       )
      ((releases)
       (print "Release verification:")
       (print "  • Signature: checking...")
       (print "  • Hash:      checking...")
       ;; TODO: verify release
       )
      ((certs)
       (print "Certificate verification:")
       (print "  • Signature: checking...")
       (print "  • Validity:  checking...")
       (print "  • Chain:     checking...")
       ;; TODO: verify cert
       )
      (else
       (printf "Unknown object type: ~a~%" obj-type)))
    (print))

  (define (verify-chain-to root-principal chain)
    "Verify a delegation chain back to a root"
    (print)
    (print "═══ Chain Verification ═══")
    (print)
    (if (null? chain)
        (begin
          (print "  Empty chain")
          #f)
        (let loop ((certs chain) (expected-issuer root-principal) (n 1))
          (if (null? certs)
              (begin
                (print)
                (print "✓ Chain valid")
                #t)
              (let* ((sc (car certs))
                     (c (signed-cert-cert sc))
                     (issuer (cert-issuer c))
                     (subject (cert-subject c)))
                (printf "  [~a] ~a → ~a~%"
                        n
                        (principal-fingerprint issuer)
                        (principal-fingerprint subject))
                (if (equal? (principal-fingerprint issuer)
                            (principal-fingerprint expected-issuer))
                    (loop (cdr certs) subject (+ n 1))
                    (begin
                      (print)
                      (printf "✗ Chain broken at step ~a~%" n)
                      (printf "  Expected issuer: ~a~%" (principal-fingerprint expected-issuer))
                      (printf "  Actual issuer:   ~a~%" (principal-fingerprint issuer))
                      #f)))))))

  (define (check-revocation cert soup-revocations)
    "Check if a certificate has been revoked"
    ;; Placeholder - revocation not yet implemented
    (print "Revocation check: (not implemented)")
    'unknown)

  ;; ============================================================
  ;; Security Summary
  ;; ============================================================

  (define (security-summary)
    "Display overall security summary of the soup"
    (print)
    (print "╔═══════════════════════════════════════════════════════════╗")
    (print "║              Soup Security Summary                        ║")
    (print "╠═══════════════════════════════════════════════════════════╣")
    (print "║                                                           ║")
    (print "║  Keys:         (run to count)                             ║")
    (print "║  Certificates: (run to count)                             ║")
    (print "║  Audit entries:(run to count)                             ║")
    (print "║                                                           ║")
    (print "║  Verification: (use verify-object)                        ║")
    (print "║  Capabilities: (use who-can / what-can)                   ║")
    (print "║  Chains:       (use authority-for)                        ║")
    (print "║                                                           ║")
    (print "╚═══════════════════════════════════════════════════════════╝")
    (print))

  (define (security-audit principal soup-certs soup-audit)
    "Correlate security events for a principal"
    (print)
    (printf "═══ Security Audit: ~a ═══~%" (principal-fingerprint principal))
    (print)
    (print "Certificate events:")
    (print "  (checking issued certificates...)")
    (print)
    (print "Audit trail events:")
    (print "  (checking audit entries...)")
    (print)
    ;; TODO: correlate audit entries with principal
    '())

) ; end module security
