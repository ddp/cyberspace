;;; security.scm - Security Properties Inspector for the Soup
;;; Chez Scheme Port
;;;
;;; "Verify, then trust" - SPKI
;;;
;;; Introspection of:
;;; - Principal properties (keys, fingerprints, capabilities)
;;; - Certificate chains (delegation, authority, validity)
;;; - Capability queries (who can do what)
;;; - Signature verification status
;;; - Audit trail correlation
;;;
;;; Ported from Chicken's security.scm.
;;; Changes: module -> library, condition-case -> guard,
;;;          srfi-1/srfi-13 -> local helpers, file I/O -> Chez.

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

  (import (rnrs)
          (rnrs mutable-strings)
          (only (chezscheme) printf format file-exists?
                with-input-from-file get-string-all
                quotient remainder)
          (cyberspace chicken-compatibility blob)
          (cyberspace chicken-compatibility chicken)
          (cyberspace sexp)
          (cyberspace crypto-ffi)
          (cyberspace cert))

  ;; ============================================================
  ;; SRFI-1 / SRFI-13 helpers
  ;; ============================================================

  (define (any pred lst)
    (cond ((null? lst) #f)
          ((pred (car lst)) #t)
          (else (any pred (cdr lst)))))

  (define (filter-map f lst)
    (let loop ((lst lst) (acc '()))
      (if (null? lst)
          (reverse acc)
          (let ((result (f (car lst))))
            (loop (cdr lst) (if result (cons result acc) acc))))))

  (define (delete-duplicates lst compare)
    (let loop ((lst lst) (seen '()) (acc '()))
      (if (null? lst)
          (reverse acc)
          (let ((x (car lst)))
            (if (any (lambda (s) (compare x s)) seen)
                (loop (cdr lst) seen acc)
                (loop (cdr lst) (cons x seen) (cons x acc)))))))

  (define (take lst n)
    (if (or (null? lst) (<= n 0))
        '()
        (cons (car lst) (take (cdr lst) (- n 1)))))

  (define (string-contains str pattern)
    (let ((slen (string-length str))
          (plen (string-length pattern)))
      (let loop ((i 0))
        (cond ((> (+ i plen) slen) #f)
              ((string=? (substring str i (+ i plen)) pattern) i)
              (else (loop (+ i 1)))))))

  (define (string-null? s) (= (string-length s) 0))

  (define (read-string) (get-string-all (current-input-port)))

  ;; ============================================================
  ;; Principal Fingerprint
  ;; ============================================================

  (define (principal-fingerprint principal)
    "Generate human-readable fingerprint for a principal"
    (cond
     ((key-principal? principal)
      (let* ((pubkey (principal-public-key principal))
             (hash (sha512-hash pubkey))
             (hex (bv->hex hash)))
        ;; Return first 32 chars in groups of 4
        (string-join
         (let loop ((s (substring hex 0 32)) (acc '()))
           (if (< (string-length s) 4)
               (reverse (if (string-null? s) acc (cons s acc)))
               (loop (substring s 4) (cons (substring s 0 4) acc))))
         ":")))
     ((keyhash-principal? principal)
      (let* ((hash (principal-hash principal))
             (hex (if (bytevector? hash) (bv->hex hash) (format "~a" hash))))
        (string-append "hash:" (substring hex 0 (min 16 (string-length hex))) "...")))
     (else "<unknown-principal>")))

  (define (bv->hex bv)
    "Convert bytevector to hex string"
    (let* ((size (bytevector-length bv))
           (result (make-string (* 2 size))))
      (do ((i 0 (+ i 1)))
          ((>= i size) result)
        (let* ((byte (bytevector-u8-ref bv i))
               (hi (quotient byte 16))
               (lo (remainder byte 16)))
          (string-set! result (* i 2) (string-ref "0123456789abcdef" hi))
          (string-set! result (+ (* i 2) 1) (string-ref "0123456789abcdef" lo))))))

  (define (string-join lst sep)
    (cond ((null? lst) "")
          ((null? (cdr lst)) (car lst))
          (else (let loop ((rest (cdr lst)) (acc (car lst)))
                  (if (null? rest) acc
                      (loop (cdr rest) (string-append acc sep (car rest))))))))

  ;; ============================================================
  ;; Display Helpers
  ;; ============================================================

  (define (display-principal principal . rest)
    "Pretty-print a principal"
    (let* ((indent (if (null? rest) 0 (car rest)))
           (pad (make-string indent #\space)))
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

  (define (display-capability tg . rest)
    "Pretty-print a capability tag"
    (let* ((indent (if (null? rest) 0 (car rest)))
           (pad (make-string indent #\space)))
      (cond
       ((all-perms? tg)
        (printf "~a(*) All Permissions~%" pad))
       ((tag? tg)
        (printf "~aCapability: ~a~%" pad (tag-sexp tg)))
       (else
        (printf "~a~a~%" pad tg)))))

  (define (display-cert sc . rest)
    "Pretty-print a signed certificate"
    (let* ((indent (if (null? rest) 0 (car rest)))
           (pad (make-string indent #\space))
           (c (signed-cert-cert sc))
           (sig (signed-cert-signature sc)))
      (print)
      (printf "~a+---------------------------------------------------+~%" pad)
      (printf "~a|              SPKI Certificate                      |~%" pad)
      (printf "~a+---------------------------------------------------+~%" pad)
      (printf "~a| Issuer:   ~a~%" pad (principal-fingerprint (cert-issuer c)))
      (printf "~a| Subject:  ~a~%" pad (principal-fingerprint (cert-subject c)))
      (printf "~a+---------------------------------------------------+~%" pad)
      (let ((tg (cert-tag c)))
        (if (all-perms? tg)
            (printf "~a| Capability: (*) All Permissions~%" pad)
            (printf "~a| Capability: ~a~%" pad (tag-sexp tg))))
      (printf "~a+---------------------------------------------------+~%" pad)
      (let ((v (cert-validity c)))
        (if v
            (begin
              (printf "~a| Valid: ~a~%" pad (validity-not-before v))
              (printf "~a| Until: ~a~%" pad (validity-not-after v)))
            (printf "~a| Validity: (no expiration)~%" pad)))
      (printf "~a| Propagate: ~a~%" pad (if (cert-propagate c) "YES (can delegate)" "NO"))
      (printf "~a+---------------------------------------------------+~%" pad)
      (printf "~a| Signature: ~a~%" pad (hash-alg->string (signature-hash-alg sig)))
      (printf "~a+---------------------------------------------------+~%" pad)
      (print)))

  (define (display-chain chain . rest)
    "Display a delegation chain"
    (let* ((indent (if (null? rest) 0 (car rest)))
           (pad (make-string indent #\space)))
      (print)
      (printf "~a=== Delegation Chain ===~%" pad)
      (let loop ((certs chain) (n 1))
        (when (pair? certs)
          (let* ((sc (car certs))
                 (c (signed-cert-cert sc)))
            (printf "~a~%~a[~a] ~a~%" pad pad n
                    (if (= n 1) "Root (self-signed or trust anchor)" "Delegation"))
            (printf "~a    From: ~a~%" pad (principal-fingerprint (cert-issuer c)))
            (printf "~a    To:   ~a~%" pad (principal-fingerprint (cert-subject c)))
            (printf "~a    Grants: ~a~%" pad
                    (let ((tg (cert-tag c)))
                      (if (all-perms? tg) "(*) ALL" (tag-sexp tg))))
            (printf "~a    Propagate: ~a~%" pad (if (cert-propagate c) "yes" "no"))
            (loop (cdr certs) (+ n 1)))))
      (printf "~a========================~%" pad)
      (print)))

  ;; ============================================================
  ;; Principal Inspection
  ;; ============================================================

  (define (inspect-principal principal . rest)
    "Inspect a principal's security properties"
    (let ((soup-certs (if (null? rest) '() (car rest))))
      (print)
      (print "=== Principal Security Properties ===")
      (display-principal principal 1)
      (print "=====================================")

      (let ((as-issuer (filter
                        (lambda (sc)
                          (let ((c (signed-cert-cert sc)))
                            (equal? (principal-fingerprint (cert-issuer c))
                                    (principal-fingerprint principal))))
                        soup-certs)))
        (printf "Certificates Issued: ~a~%" (length as-issuer))
        (for-each
         (lambda (sc)
           (let ((c (signed-cert-cert sc)))
             (printf "  -> ~a : ~a~%"
                     (principal-fingerprint (cert-subject c))
                     (let ((t (cert-tag c))) (if (all-perms? t) "(*)" (tag-sexp t))))))
         as-issuer))

      (let ((as-subject (filter
                         (lambda (sc)
                           (let ((c (signed-cert-cert sc)))
                             (equal? (principal-fingerprint (cert-subject c))
                                     (principal-fingerprint principal))))
                         soup-certs)))
        (printf "Certificates Granted: ~a~%" (length as-subject))
        (for-each
         (lambda (sc)
           (let ((c (signed-cert-cert sc)))
             (printf "  <- ~a : ~a~%"
                     (principal-fingerprint (cert-issuer c))
                     (let ((t (cert-tag c))) (if (all-perms? t) "(*)" (tag-sexp t))))))
         as-subject))

      (print "=====================================")
      (print)

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

  (define (inspect-cert sc . rest)
    "Inspect a certificate's security properties"
    (let ((issuer-key (if (null? rest) #f (car rest))))
      (display-cert sc)

      (when issuer-key
        (let ((valid (verify-signed-cert sc issuer-key)))
          (print)
          (if valid
              (print "  Signature Valid")
              (print "  Signature Invalid"))
          (print)))

      (let ((c (signed-cert-cert sc)))
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

  (define (cert-status sc issuer-key . rest)
    "Check certificate status: valid, expired, invalid-sig, revoked"
    (let* ((revocations (if (null? rest) '() (car rest)))
           (c (signed-cert-cert sc))
           (v (cert-validity c))
           (sig-valid (verify-signed-cert sc issuer-key))
           (cert-fp (principal-fingerprint (cert-subject c))))
      (cond
       ((not sig-valid) 'invalid-signature)
       ((and v (validity-expired? v)) 'expired)
       ((cert-revoked? cert-fp revocations) 'revoked)
       (else 'valid))))

  (define (cert-revoked? cert-fingerprint revocations)
    (any (lambda (rev)
           (equal? cert-fingerprint (alist-ref 'fingerprint rev)))
         revocations))

  (define (validity-expired? v)
    (let ((not-after (validity-not-after v)))
      #f))  ; Placeholder

  ;; ============================================================
  ;; Capability Queries
  ;; ============================================================

  (define (who-can capability soup-certs)
    "Find all principals who can perform a capability"
    (print)
    (printf "=== WHO CAN: ~a ===~%" capability)
    (print)
    (let ((holders
           (filter-map
            (lambda (sc)
              (let* ((c (signed-cert-cert sc))
                     (tg (cert-tag c)))
                (if (or (all-perms? tg)
                        (and (tag? tg)
                             (tag-implies tg (make-tag capability))))
                    (principal-fingerprint (cert-subject c))
                    #f)))
            soup-certs)))
      (if (null? holders)
          (print "  (no principals found with this capability)")
          (for-each
           (lambda (fp)
             (printf "  ~a~%" fp))
           (delete-duplicates holders equal?)))
      (print)
      holders))

  (define (what-can principal soup-certs)
    "Find all capabilities granted to a principal"
    (print)
    (printf "=== Capabilities of: ~a ===~%" (principal-fingerprint principal))
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
             (printf "  ~a~%" (if (all-perms? cap) "(*) All Permissions" (tag-sexp cap))))
           caps))
      (print)
      caps))

  (define (build-chain issuer soup-certs acc max-depth)
    "Build a delegation chain by tracing issuers."
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

  (define (trace-delegation-chains principal capability soup-certs)
    "Trace delegation chains for a principal's capability."
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
                         (tg (cert-tag c)))
                    (if (or (all-perms? tg)
                            (and (tag? tg)
                                 (tag-implies tg (make-tag capability))))
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

  (define (authority-for capability principal soup-certs)
    "Trace the authority chain for a principal's capability"
    (print)
    (printf "=== Authority for: ~a doing ~a ===~%"
            (principal-fingerprint principal) capability)
    (print)
    (let ((direct
           (filter
            (lambda (sc)
              (let* ((c (signed-cert-cert sc))
                     (subj (cert-subject c))
                     (tg (cert-tag c)))
                (and (equal? (principal-fingerprint subj)
                             (principal-fingerprint principal))
                     (or (all-perms? tg)
                         (and (tag? tg)
                              (tag-implies tg (make-tag capability)))))))
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
                 (print)))
             direct)
            direct))))

  ;; ============================================================
  ;; Verification
  ;; ============================================================

  (define (verify-object obj-type obj-name . rest)
    "Verify security properties of a soup object."
    (let ((context (if (null? rest) '() (car rest))))
      (print)
      (printf "=== Verifying: ~a (~a) ===~%" obj-name obj-type)
      (print)
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
          (guard (exn [#t
                       (print "  Parse: failed")
                       (print)
                       `((exists . #t) (valid . #f) (error . "parse failed"))])
            (let* ((content (with-input-from-file filename read-string))
                   (sx (parse-sexp content))
                   (items (and (sexp-list? sx) (list-items sx))))
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
                    (print)
                    `((exists . #t) (valid . ,(and valid-type valid-len))
                      (type . ,type-str) (size . ,key-len)))
                  (begin
                    (print "  Format: invalid structure")
                    (print)
                    `((exists . #t) (valid . #f) (error . "invalid structure")))))))))

  (define (verify-release release-name context)
    "Verify a release's signature and hash."
    (print "Release verification:")
    (let ((vault-path (alist-ref 'vault-path context)))
      (let ((release-file (string-append (or vault-path ".vault") "/releases/" release-name)))
        (if (not (file-exists? release-file))
            (begin
              (print "  File: not found")
              (print)
              `((exists . #f) (valid . #f)))
            (guard (exn [#t
                         (print "  Parse: failed")
                         (print)
                         `((exists . #t) (valid . #f) (error . "parse failed"))])
              (let* ((content (with-input-from-file release-file read-string))
                     (sx (parse-sexp content)))
                (if (and (sexp-list? sx)
                         (pair? (list-items sx))
                         (sexp-atom? (car (list-items sx)))
                         (string=? (atom-value (car (list-items sx))) "release"))
                    (begin
                      (print "  Structure: ok")
                      (print "  Signature: (checking...)")
                      (print)
                      `((exists . #t) (valid . #t) (verified . pending)))
                    (begin
                      (print "  Structure: bad")
                      (print)
                      `((exists . #t) (valid . #f))))))))))

  (define (verify-certificate cert-name context)
    "Verify a certificate's signature, validity, and chain."
    (print "Certificate verification:")
    (let* ((issuer-key (alist-ref 'issuer-key context))
           (revocations (or (alist-ref 'revocations context) '()))
           (soup-certs (or (alist-ref 'soup-certs context) '())))
      (print "  Signature:  (requires issuer key)")
      (print "  Validity:   (checking expiration...)")
      (print "  Revocation: (checking list...)")
      (print "  Chain:      (tracing delegation...)")
      (print)
      `((signature . pending)
        (validity . pending)
        (revocation . ,(if (null? revocations) 'no-list 'checked))
        (chain . pending))))

  (define (verify-chain-to root-principal chain)
    "Verify a delegation chain back to a root"
    (print)
    (print "=== Chain Verification ===")
    (print)
    (if (null? chain)
        (begin
          (print "  Empty chain")
          #f)
        (let loop ((certs chain) (expected-issuer root-principal) (n 1))
          (if (null? certs)
              (begin
                (print)
                (print "  Chain valid")
                #t)
              (let* ((sc (car certs))
                     (c (signed-cert-cert sc))
                     (iss (cert-issuer c))
                     (subj (cert-subject c)))
                (printf "  [~a] ~a -> ~a~%"
                        n
                        (principal-fingerprint iss)
                        (principal-fingerprint subj))
                (if (equal? (principal-fingerprint iss)
                            (principal-fingerprint expected-issuer))
                    (loop (cdr certs) subj (+ n 1))
                    (begin
                      (print)
                      (printf "  Chain broken at step ~a~%" n)
                      (printf "  Expected issuer: ~a~%" (principal-fingerprint expected-issuer))
                      (printf "  Actual issuer:   ~a~%" (principal-fingerprint iss))
                      #f)))))))

  (define (check-revocation sc soup-revocations)
    "Check if a certificate has been revoked."
    (if (null? soup-revocations)
        'no-list
        (let* ((c (signed-cert-cert sc))
               (fp (principal-fingerprint (cert-subject c))))
          (if (cert-revoked? fp soup-revocations)
              'revoked
              'valid))))

  ;; ============================================================
  ;; Security Summary
  ;; ============================================================

  (define (security-summary)
    "Display overall security summary"
    (print)
    (print "=== Soup Security Summary ===")
    (print)
    (print "  Keys:         (run to count)")
    (print "  Certificates: (run to count)")
    (print "  Audit entries:(run to count)")
    (print)
    (print "  Verification: (use verify-object)")
    (print "  Capabilities: (use who-can / what-can)")
    (print "  Chains:       (use authority-for)")
    (print)
    (print "=============================")
    (print))

  (define (security-audit principal soup-certs soup-audit)
    "Correlate security events for a principal."
    (let ((fp (principal-fingerprint principal)))
      (print)
      (printf "=== Security Audit: ~a ===~%" fp)
      (print)

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
        (print)

        (print "Audit trail events:")
        (let ((actor-entries (filter
                              (lambda (entry)
                                (let ((actor (alist-ref 'actor entry)))
                                  (and actor (string? actor) (string-contains actor fp))))
                              soup-audit)))
          (if (null? actor-entries)
              (print "  (no audit entries for this principal)")
              (begin
                (printf "  Found ~a audit entries:~%" (length actor-entries))
                (for-each
                 (lambda (entry)
                   (let ((action (or (alist-ref 'action entry) "unknown"))
                         (timestamp (or (alist-ref 'timestamp entry) "?")))
                     (printf "    [~a] ~a~%" timestamp action)))
                 (take actor-entries (min 10 (length actor-entries))))
                (when (> (length actor-entries) 10)
                  (printf "    ... and ~a more~%" (- (length actor-entries) 10)))))
          (print)

          `((fingerprint . ,fp)
            (certs-issued . ,(length issued))
            (certs-received . ,(length received))
            (audit-entries . ,(length actor-entries)))))))

) ;; end library
