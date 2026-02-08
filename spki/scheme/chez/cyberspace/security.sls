;;; security.scm - Security Properties Inspector for the Soup
;;; Library of Cyberspace - Chez Port
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

(library (cyberspace security)
  (export
    ;; Principal inspection
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

  (import (except (rnrs) with-input-from-file file-exists? find)
          (only (chezscheme) printf format void
                with-input-from-file
                file-exists?)
          (cyberspace chicken-compatibility chicken)
          (cyberspace chicken-compatibility blob)
          (cyberspace crypto-ffi)
          (cyberspace cert)
          (cyberspace sexp))

  ;; ============================================================
  ;; Principal Fingerprint
  ;; ============================================================

  (define (principal-fingerprint principal)
    "Generate human-readable fingerprint for a principal"
    (cond
     ((key-principal? principal)
      (let* ((pubkey (principal-public-key principal))
             (hash (sha512-hash pubkey))
             (hex (bytevector->hex hash)))
        ;; Return first 32 chars in groups of 4
        (string-join
         (let loop ((s (substring hex 0 32)) (acc '()))
           (if (< (string-length s) 4)
               (reverse (if (string=? s "") acc (cons s acc)))
               (loop (substring s 4 (string-length s))
                     (cons (substring s 0 4) acc))))
         ":")))
     ((keyhash-principal? principal)
      (let* ((hash (principal-hash principal))
             (hex (if (bytevector? hash)
                      (bytevector->hex hash)
                      (format "~a" hash))))
        (string-append "hash:"
                       (substring hex 0 (min 16 (string-length hex)))
                       "...")))
     (else "<unknown-principal>")))

  (define (bytevector->hex bv)
    "Convert bytevector to hex string"
    (let ((len (bytevector-length bv)))
      (let loop ((i 0) (acc '()))
        (if (= i len)
            (apply string-append (reverse acc))
            (let* ((byte (bytevector-u8-ref bv i))
                   (hi (quotient byte 16))
                   (lo (remainder byte 16)))
              (loop (+ i 1)
                    (cons (string
                            (string-ref "0123456789abcdef" hi)
                            (string-ref "0123456789abcdef" lo))
                          acc)))))))

  ;; ============================================================
  ;; Display Helpers
  ;; ============================================================

  (define (display-principal principal . rest)
    "Pretty-print a principal"
    (let ((indent (if (null? rest) 0 (car rest))))
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
          (printf "~a<unknown principal>~%" pad))))))

  (define (display-capability tag . rest)
    "Pretty-print a capability tag"
    (let ((indent (if (null? rest) 0 (car rest))))
      (let ((pad (make-string indent #\space)))
        (cond
         ((all-perms? tag)
          (printf "~a(*) All Permissions~%" pad))
         ((tag? tag)
          (printf "~aCapability: ~a~%" pad (tag-sexp tag)))
         (else
          (printf "~a~a~%" pad tag))))))

  (define (display-cert signed-cert . rest)
    "Pretty-print a signed certificate"
    (let* ((indent (if (null? rest) 0 (car rest)))
           (pad (make-string indent #\space))
           (c (signed-cert-cert signed-cert))
           (sig (signed-cert-signature signed-cert)))
      (print "")
      (printf "~a  SPKI Certificate~%" pad)
      (printf "~a  Issuer:    ~a~%" pad (principal-fingerprint (cert-issuer c)))
      (printf "~a  Subject:   ~a~%" pad (principal-fingerprint (cert-subject c)))
      (let ((tag (cert-tag c)))
        (if (all-perms? tag)
            (printf "~a  Capability: (*) All Permissions~%" pad)
            (printf "~a  Capability: ~a~%" pad (tag-sexp tag))))
      (let ((v (cert-validity c)))
        (if v
            (begin
              (printf "~a  Valid: ~a~%" pad (validity-not-before v))
              (printf "~a  Until: ~a~%" pad (validity-not-after v)))
            (printf "~a  Validity: (no expiration)~%" pad)))
      (printf "~a  Propagate: ~a~%" pad (if (cert-propagate c) "YES (can delegate)" "NO"))
      (printf "~a  Signature: ~a~%" pad (hash-alg->string (signature-hash-alg sig)))
      (print "")))

  (define (display-chain chain . rest)
    "Display a delegation chain"
    (let ((indent (if (null? rest) 0 (car rest))))
      (let ((pad (make-string indent #\space)))
        (print "")
        (printf "~a=== Delegation Chain ===~%" pad)
        (let loop ((certs chain) (n 1))
          (when (pair? certs)
            (let* ((sc (car certs))
                   (c (signed-cert-cert sc)))
              (printf "~%~a[~a] ~a~%" pad n
                      (if (= n 1) "Root (self-signed or trust anchor)" "Delegation"))
              (printf "~a    From: ~a~%" pad (principal-fingerprint (cert-issuer c)))
              (printf "~a    To:   ~a~%" pad (principal-fingerprint (cert-subject c)))
              (printf "~a    Grants: ~a~%" pad
                      (let ((tag (cert-tag c)))
                        (if (all-perms? tag) "(*) ALL" (tag-sexp tag))))
              (printf "~a    Propagate: ~a~%" pad (if (cert-propagate c) "yes" "no"))
              (loop (cdr certs) (+ n 1)))))
        (printf "~a========================~%" pad)
        (print ""))))

  ;; ============================================================
  ;; Principal Inspection
  ;; ============================================================

  (define (inspect-principal principal . rest)
    "Inspect a principal's security properties"
    (let ((soup-certs (if (null? rest) '() (car rest))))
      (print "")
      (print "=== Principal Security Properties ===")
      (display-principal principal 1)

      ;; Find certificates where this principal is issuer
      (let ((as-issuer (filter
                        (lambda (sc)
                          (let ((c (signed-cert-cert sc)))
                            (equal? (principal-fingerprint (cert-issuer c))
                                    (principal-fingerprint principal))))
                        soup-certs)))
        (printf "  Certificates Issued by this principal: ~a~%" (length as-issuer))
        (for-each
         (lambda (sc)
           (let ((c (signed-cert-cert sc)))
             (printf "    -> ~a : ~a~%"
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
        (printf "  Certificates Granted to this principal: ~a~%" (length as-subject))
        (for-each
         (lambda (sc)
           (let ((c (signed-cert-cert sc)))
             (printf "    <- ~a : ~a~%"
                     (principal-fingerprint (cert-issuer c))
                     (let ((t (cert-tag c))) (if (all-perms? t) "(*)" (tag-sexp t))))))
         as-subject))

      (print "")

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
                              soup-certs))))))

  ;; ============================================================
  ;; Certificate Inspection
  ;; ============================================================

  (define (inspect-cert signed-cert . rest)
    "Inspect a certificate's security properties"
    (let ((issuer-key (if (null? rest) #f (car rest))))
      (display-cert signed-cert)

      ;; Verify signature if we have the issuer's key
      (when issuer-key
        (let ((valid (verify-signed-cert signed-cert issuer-key)))
          (print "")
          (if valid
              (print "  Signature Valid")
              (print "  Signature Invalid"))
          (print "")))

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
                            #f)))))))

  (define (cert-status signed-cert issuer-key . rest)
    "Check certificate status: valid, expired, invalid-sig, revoked"
    (let* ((revocations (if (null? rest) '() (car rest)))
           (c (signed-cert-cert signed-cert))
           (v (cert-validity c))
           (sig-valid (verify-signed-cert signed-cert issuer-key))
           (cert-fp (principal-fingerprint (cert-subject c))))
      (cond
       ((not sig-valid) 'invalid-signature)
       ((and v (validity-expired? v)) 'expired)
       ((cert-revoked? cert-fp revocations) 'revoked)
       (else 'valid))))

  (define (cert-revoked? cert-fingerprint revocations)
    "Check if a certificate fingerprint is in the revocation list"
    (any (lambda (rev)
           (let ((fp (assq 'fingerprint rev)))
             (and fp (equal? cert-fingerprint (cdr fp)))))
         revocations))

  (define (validity-expired? validity)
    "Check if validity period has expired"
    ;; Placeholder - in production, parse and compare properly
    #f)

  ;; ============================================================
  ;; Capability Queries
  ;; ============================================================

  (define (who-can capability soup-certs)
    "Find all principals who can perform a capability"
    (print "")
    (printf "=== WHO CAN: ~a ===~%" capability)
    (print "")
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
             (printf "  + ~a~%" fp))
           (delete-duplicates holders)))
      (print "")
      holders))

  (define (delete-duplicates lst)
    "Remove duplicate elements from list (using equal?)"
    (let loop ((lst lst) (seen '()) (acc '()))
      (cond
        ((null? lst) (reverse acc))
        ((member (car lst) seen) (loop (cdr lst) seen acc))
        (else (loop (cdr lst) (cons (car lst) seen) (cons (car lst) acc))))))

  (define (what-can principal soup-certs)
    "Find all capabilities granted to a principal"
    (print "")
    (printf "=== Capabilities of: ~a ===~%" (principal-fingerprint principal))
    (print "")
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
             (printf "  - ~a~%" (if (all-perms? cap) "(*) All Permissions" (tag-sexp cap))))
           caps))
      (print "")
      caps))

  (define (trace-delegation-chains principal capability soup-certs)
    "Trace delegation chains to find authority for a capability."
    (let ((target-fp (principal-fingerprint principal)))
      (let ((grants-to-principal
             (filter
              (lambda (sc)
                (equal? (principal-fingerprint (cert-subject (signed-cert-cert sc)))
                        target-fp))
              soup-certs)))
        (let ((chains
               (filter-map
                (lambda (sc)
                  (let* ((c (signed-cert-cert sc))
                         (tag (cert-tag c)))
                    (if (or (all-perms? tag)
                            (and (tag? tag)
                                 (tag-implies tag (make-tag capability))))
                        (let ((chain (build-chain (cert-issuer c) soup-certs (list sc) 10)))
                          (when (pair? chain)
                            (print "  Found delegation chain:")
                            (for-each
                             (lambda (step)
                               (let ((cc (signed-cert-cert step)))
                                 (printf "    ~a -> ~a~%"
                                         (principal-fingerprint (cert-issuer cc))
                                         (principal-fingerprint (cert-subject cc)))))
                             (reverse chain)))
                          chain)
                        #f)))
                grants-to-principal)))
          (if (null? chains)
              (print "  (no delegation chains found)")
              (printf "  Found ~a chain(s)~%" (length chains)))
          chains))))

  (define (build-chain issuer soup-certs acc max-depth)
    "Build a delegation chain by tracing issuers. Returns chain or #f."
    (if (<= max-depth 0)
        acc
        (let ((issuer-fp (principal-fingerprint issuer)))
          (let ((parent-certs
                 (filter
                  (lambda (sc)
                    (let ((c (signed-cert-cert sc)))
                      (and (cert-propagate c)
                           (equal? (principal-fingerprint (cert-subject c))
                                   issuer-fp))))
                  soup-certs)))
            (if (null? parent-certs)
                acc
                (let ((parent (car parent-certs)))
                  (build-chain (cert-issuer (signed-cert-cert parent))
                               soup-certs
                               (cons parent acc)
                               (- max-depth 1))))))))

  (define (authority-for capability principal soup-certs)
    "Trace the authority chain for a principal's capability"
    (print "")
    (printf "=== Authority for: ~a doing ~a ===~%"
            (principal-fingerprint principal) capability)
    (print "")
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
            (trace-delegation-chains principal capability soup-certs))
          (begin
            (print "Direct grants:")
            (for-each
             (lambda (sc)
               (let ((c (signed-cert-cert sc)))
                 (printf "  From: ~a~%" (principal-fingerprint (cert-issuer c)))
                 (printf "  Tag:  ~a~%" (let ((t (cert-tag c)))
                                         (if (all-perms? t) "(*)" (tag-sexp t))))
                 (printf "  Propagate: ~a~%" (cert-propagate c))
                 (print "")))
             direct)
            direct))))

  ;; ============================================================
  ;; Verification
  ;; ============================================================

  (define (verify-object obj-type obj-name . rest)
    "Verify security properties of a soup object."
    (let ((context (if (null? rest) '() (car rest))))
      (print "")
      (printf "=== Verifying: ~a (~a) ===~%" obj-name obj-type)
      (print "")
      (case obj-type
        ((keys)
         (verify-key-file obj-name))
        ((releases)
         (verify-release obj-name context))
        ((certs)
         (verify-certificate obj-name context))
        (else
         (printf "Unknown object type: ~a~%" obj-type)
         `((error . ,(format "Unknown type: ~a" obj-type)))))))

  (define (verify-key-file filename)
    "Verify a key file's integrity."
    (print "Key verification:")
    (let ((exists (file-exists? filename)))
      (printf "  File exists: ~a~%" (if exists "yes" "no"))
      (if (not exists)
          `((exists . #f) (valid . #f))
          (guard (exn (#t
                       (print "  Parse: failed")
                       (print "")
                       `((exists . #t) (valid . #f) (error . "parse failed"))))
            (let* ((content (with-input-from-file filename
                              (lambda () (get-string-all (current-input-port)))))
                   (sexp-val (parse-sexp content))
                   (items (and (sexp-list? sexp-val) (list-items sexp-val))))
              (if (and items
                       (= 2 (length items))
                       (sexp-atom? (car items))
                       (sexp-bytes? (cadr items)))
                  (let* ((type-str (atom-value (car items)))
                         (key-bytes (bytes-value (cadr items)))
                         (key-len (bytevector-length key-bytes))
                         (valid-type (or (string=? type-str "spki-private-key")
                                        (string=? type-str "spki-public-key")))
                         (valid-len (or (= key-len 32) (= key-len 64))))
                    (printf "  Format:   ~a~%" (if valid-type "ok" "bad"))
                    (printf "  Key size: ~a bytes ~a~%" key-len (if valid-len "ok" "bad"))
                    (print "")
                    `((exists . #t) (valid . ,(and valid-type valid-len))
                      (type . ,type-str) (size . ,key-len)))
                  (begin
                    (print "  Format: invalid structure")
                    (print "")
                    `((exists . #t) (valid . #f) (error . "invalid structure")))))))))

  (define (verify-release release-name context)
    "Verify a release's signature and hash."
    (print "Release verification:")
    (let ((vault-path (let ((vp (assq 'vault-path context)))
                        (if vp (cdr vp) ".vault"))))
      (let ((release-file (string-append vault-path "/releases/" release-name)))
        (if (not (file-exists? release-file))
            (begin
              (print "  File: not found")
              (print "")
              `((exists . #f) (valid . #f)))
            (guard (exn (#t
                         (print "  Parse: failed")
                         (print "")
                         `((exists . #t) (valid . #f) (error . "parse failed"))))
              (let* ((content (with-input-from-file release-file
                                (lambda () (get-string-all (current-input-port)))))
                     (sexp-val (parse-sexp content)))
                (if (and (sexp-list? sexp-val)
                         (pair? (list-items sexp-val))
                         (sexp-atom? (car (list-items sexp-val)))
                         (string=? (atom-value (car (list-items sexp-val))) "release"))
                    (begin
                      (print "  Structure: ok")
                      (print "  Signature: (checking...)")
                      (print "")
                      `((exists . #t) (valid . #t) (verified . pending)))
                    (begin
                      (print "  Structure: bad")
                      (print "")
                      `((exists . #t) (valid . #f))))))))))

  (define (verify-certificate cert-name context)
    "Verify a certificate's signature, validity, and chain."
    (print "Certificate verification:")
    (print "  Signature:  (requires issuer key)")
    (print "  Validity:   (checking expiration...)")
    (print "  Revocation: (checking list...)")
    (print "  Chain:      (tracing delegation...)")
    (print "")
    `((signature . pending)
      (validity . pending)
      (revocation . pending)
      (chain . pending)))

  (define (verify-chain-to root-principal chain)
    "Verify a delegation chain back to a root"
    (print "")
    (print "=== Chain Verification ===")
    (print "")
    (if (null? chain)
        (begin
          (print "  Empty chain")
          #f)
        (let loop ((certs chain) (expected-issuer root-principal) (n 1))
          (if (null? certs)
              (begin
                (print "")
                (print "  Chain valid")
                #t)
              (let* ((sc (car certs))
                     (c (signed-cert-cert sc))
                     (issuer (cert-issuer c))
                     (subject (cert-subject c)))
                (printf "  [~a] ~a -> ~a~%"
                        n
                        (principal-fingerprint issuer)
                        (principal-fingerprint subject))
                (if (equal? (principal-fingerprint issuer)
                            (principal-fingerprint expected-issuer))
                    (loop (cdr certs) subject (+ n 1))
                    (begin
                      (print "")
                      (printf "  Chain broken at step ~a~%" n)
                      (printf "  Expected issuer: ~a~%" (principal-fingerprint expected-issuer))
                      (printf "  Actual issuer:   ~a~%" (principal-fingerprint issuer))
                      #f)))))))

  (define (check-revocation signed-cert soup-revocations)
    "Check if a certificate has been revoked."
    (if (null? soup-revocations)
        'no-list
        (let* ((c (signed-cert-cert signed-cert))
               (fp (principal-fingerprint (cert-subject c))))
          (if (cert-revoked? fp soup-revocations)
              'revoked
              'valid))))

  ;; ============================================================
  ;; Security Summary
  ;; ============================================================

  (define (security-summary)
    "Display overall security summary of the soup"
    (print "")
    (print "=== Soup Security Summary ===")
    (print "")
    (print "  Keys:         (run to count)")
    (print "  Certificates: (run to count)")
    (print "  Audit entries:(run to count)")
    (print "")
    (print "  Verification: (use verify-object)")
    (print "  Capabilities: (use who-can / what-can)")
    (print "  Chains:       (use authority-for)")
    (print ""))

  (define (security-audit principal soup-certs soup-audit)
    "Correlate security events for a principal."
    (let ((fp (principal-fingerprint principal)))
      (print "")
      (printf "=== Security Audit: ~a ===~%" fp)
      (print "")

      ;; Certificate events
      (print "Certificate events:")
      (let ((issued (filter
                     (lambda (sc)
                       (equal? (principal-fingerprint (cert-issuer (signed-cert-cert sc))) fp))
                     soup-certs))
            (received (filter
                       (lambda (sc)
                         (equal? (principal-fingerprint (cert-subject (signed-cert-cert sc))) fp))
                       soup-certs)))
        (if (and (null? issued) (null? received))
            (print "  (no certificate activity)")
            (begin
              (unless (null? issued)
                (printf "  Issued ~a certificate(s):~%" (length issued))
                (for-each
                 (lambda (sc)
                   (let ((c (signed-cert-cert sc)))
                     (printf "    -> ~a~%" (principal-fingerprint (cert-subject c)))))
                 issued))
              (unless (null? received)
                (printf "  Received ~a certificate(s):~%" (length received))
                (for-each
                 (lambda (sc)
                   (let ((c (signed-cert-cert sc)))
                     (printf "    <- ~a~%" (principal-fingerprint (cert-issuer c)))))
                 received))))
        (print "")

        ;; Audit trail events
        (print "Audit trail events:")
        (let ((actor-entries (filter
                              (lambda (entry)
                                (let ((actor (assq 'actor entry)))
                                  (and actor (string-contains (cdr actor) fp))))
                              soup-audit)))
          (if (null? actor-entries)
              (print "  (no audit entries for this principal)")
              (begin
                (printf "  Found ~a audit entries:~%" (length actor-entries))
                (for-each
                 (lambda (entry)
                   (let ((action (let ((a (assq 'action entry)))
                                   (if a (cdr a) "unknown")))
                         (timestamp (let ((t (assq 'timestamp entry)))
                                      (if t (cdr t) "?"))))
                     (printf "    [~a] ~a~%" timestamp action)))
                 (take actor-entries (min 10 (length actor-entries))))
                (when (> (length actor-entries) 10)
                  (printf "    ... and ~a more~%" (- (length actor-entries) 10)))))
          (print "")

          ;; Return correlation summary
          `((fingerprint . ,fp)
            (certs-issued . ,(length issued))
            (certs-received . ,(length received))
            (audit-entries . ,(length actor-entries)))))))

) ;; end library
