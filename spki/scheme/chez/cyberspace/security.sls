;;; security.sls - Security Properties Inspector for the Soup
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
;;;
;;; Ported from Chicken's security.scm.
;;; Changes: module -> library, #!optional -> get-opt, condition-case -> guard,
;;;          (chicken file/io) -> Chez equivalents.

(library (cyberspace security)
  (export
    inspect-principal
    principal-fingerprint
    inspect-cert
    cert-status
    iso8601->seconds
    validity-expired?
    cert-revoked?
    who-can
    what-can
    authority-for
    verify-object
    verify-chain-to
    check-revocation
    security-summary
    security-audit
    display-principal
    display-cert
    display-chain
    display-capability)

  (import (except (rnrs) find)
          (only (chezscheme)
                printf format
                with-output-to-string
                time-second current-time)
          (cyberspace crypto-ffi)
          (cyberspace cert)
          (cyberspace sexp)
          (cyberspace chicken-compatibility blob)
          (cyberspace chicken-compatibility chicken))

  ;; ============================================================
  ;; Helpers
  ;; ============================================================

  (define (any pred lst)
    (and (not (null? lst))
         (or (pred (car lst))
             (any pred (cdr lst)))))

  (define (filter-map proc lst)
    (let loop ((lst lst) (acc '()))
      (if (null? lst) (reverse acc)
          (let ((result (proc (car lst))))
            (if result
                (loop (cdr lst) (cons result acc))
                (loop (cdr lst) acc))))))

  (define (delete-duplicates lst eq-fn)
    (let loop ((lst lst) (seen '()))
      (if (null? lst) (reverse seen)
          (if (any (lambda (s) (eq-fn s (car lst))) seen)
              (loop (cdr lst) seen)
              (loop (cdr lst) (cons (car lst) seen))))))

  (define (find pred lst)
    (cond
      ((null? lst) #f)
      ((pred (car lst)) (car lst))
      (else (find pred (cdr lst)))))

  (define (string-contains haystack needle)
    (let ((hlen (string-length haystack))
          (nlen (string-length needle)))
      (let loop ((i 0))
        (cond
          ((> (+ i nlen) hlen) #f)
          ((string=? (substring haystack i (+ i nlen)) needle) i)
          (else (loop (+ i 1)))))))

  (define (current-seconds) (time-second (current-time)))

  (define (string-null? s) (= 0 (string-length s)))

  ;; ============================================================
  ;; ISO 8601 / Validity
  ;; ============================================================

  (define (iso8601->seconds datestr)
    "Parse ISO 8601 date (YYYY-MM-DDThh:mm:ssZ) to approximate Unix epoch seconds."
    (let* ((year  (string->number (substring datestr 0 4)))
           (month (string->number (substring datestr 5 7)))
           (day   (string->number (substring datestr 8 10)))
           (hour  (string->number (substring datestr 11 13)))
           (min   (string->number (substring datestr 14 16)))
           (sec   (string->number (substring datestr 17 19)))
           ;; Days per month (non-leap approximation, leap years handled below)
           (mdays '#(0 31 28 31 30 31 30 31 31 30 31 30 31))
           ;; Years since epoch
           (y (- year 1970))
           ;; Leap years between 1970 and year
           (leap-years (- (div (- year 1) 4) (div 1969 4)
                          (- (div (- year 1) 100) (div 1969 100))
                          (- (- (div (- year 1) 400) (div 1969 400))))))
      (let* ((days-from-years (+ (* y 365) leap-years))
             ;; Days from months in current year
             (is-leap (and (= 0 (mod year 4))
                           (or (not (= 0 (mod year 100)))
                               (= 0 (mod year 400)))))
             (days-from-months
              (let loop ((m 1) (d 0))
                (if (>= m month) d
                    (loop (+ m 1)
                          (+ d (vector-ref mdays m)
                             (if (and (= m 2) is-leap) 1 0))))))
             (total-days (+ days-from-years days-from-months (- day 1))))
        (+ (* total-days 86400) (* hour 3600) (* min 60) sec))))

  (define (validity-expired? validity)
    "Check if validity period has expired."
    (and validity
         (let ((not-after (validity-not-after validity)))
           (and not-after
                (cond
                 ((number? not-after)
                  (> (current-seconds) not-after))
                 ((and (string? not-after) (>= (string-length not-after) 19))
                  (> (current-seconds) (iso8601->seconds not-after)))
                 (else #f))))))

  (define (string-join lst sep)
    (if (null? lst) ""
        (let loop ((rest (cdr lst)) (acc (car lst)))
          (if (null? rest) acc
              (loop (cdr rest) (string-append acc sep (car rest)))))))

  ;; ============================================================
  ;; Principal Fingerprint
  ;; ============================================================

  (define (blob->hex blob)
    (let* ((vec (blob->u8vector blob))
           (len (u8vector-length vec)))
      (let loop ((i 0) (acc '()))
        (if (= i len) (apply string-append (reverse acc))
            (let* ((byte (u8vector-ref vec i))
                   (hi (div byte 16))
                   (lo (mod byte 16)))
              (loop (+ i 1)
                    (cons (string (string-ref "0123456789abcdef" hi)
                                  (string-ref "0123456789abcdef" lo))
                          acc)))))))

  (define (principal-fingerprint principal)
    (cond
     ((key-principal? principal)
      (let* ((pubkey (principal-public-key principal))
             (hash (sha512-hash pubkey))
             (hex (blob->hex hash)))
        (string-join
         (let loop ((s (substring hex 0 32)) (acc '()))
           (if (< (string-length s) 4)
               (reverse (if (string-null? s) acc (cons s acc)))
               (loop (substring s 4 (string-length s)) (cons (substring s 0 4) acc))))
         ":")))
     ((keyhash-principal? principal)
      (let* ((hash (principal-hash principal))
             (hex (if (bytevector? hash) (blob->hex hash) (format #f "~a" hash))))
        (string-append "hash:" (substring hex 0 (min 16 (string-length hex))) "...")))
     (else "<unknown-principal>")))

  ;; ============================================================
  ;; Display Helpers
  ;; ============================================================

  (define (display-principal principal . rest)
    (let ((indent (get-opt rest 0 0)))
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
    (let ((indent (get-opt rest 0 0)))
      (let ((pad (make-string indent #\space)))
        (cond
         ((all-perms? tag)
          (printf "~a(*) All Permissions~%" pad))
         ((tag? tag)
          (printf "~aCapability: ~a~%" pad (tag-sexp tag)))
         (else
          (printf "~a~a~%" pad tag))))))

  (define (display-cert signed-cert . rest)
    (let ((indent (get-opt rest 0 0)))
      (let* ((pad (make-string indent #\space))
             (c (signed-cert-cert signed-cert))
             (sig (signed-cert-signature signed-cert)))
        (print)
        (printf "~a+---------------------------------------------------+~%" pad)
        (printf "~a|              SPKI Certificate                      |~%" pad)
        (printf "~a+---------------------------------------------------+~%" pad)
        (printf "~a| Issuer:   ~a~%" pad (principal-fingerprint (cert-issuer c)))
        (printf "~a| Subject:  ~a~%" pad (principal-fingerprint (cert-subject c)))
        (printf "~a+---------------------------------------------------+~%" pad)
        (printf "~a| Capability: ~a~%" pad
                (let ((tag (cert-tag c)))
                  (if (all-perms? tag) "(*) All Permissions" (tag-sexp tag))))
        (let ((v (cert-validity c)))
          (if v
              (begin
                (printf "~a| Valid: ~a~%" pad (validity-not-before v))
                (printf "~a| Until: ~a~%" pad (validity-not-after v)))
              (printf "~a| Validity: (no expiration)~%" pad)))
        (printf "~a| Propagate: ~a~%" pad (if (cert-propagate c) "YES" "NO"))
        (printf "~a| Signature: ~a~%" pad (hash-alg->string (signature-hash-alg sig)))
        (printf "~a+---------------------------------------------------+~%" pad)
        (print))))

  (define (display-chain chain . rest)
    (let ((indent (get-opt rest 0 0)))
      (let ((pad (make-string indent #\space)))
        (print)
        (printf "~a=== Delegation Chain ===~%" pad)
        (let loop ((certs chain) (n 1))
          (when (pair? certs)
            (let* ((sc (car certs))
                   (c (signed-cert-cert sc)))
              (printf "~a[~a] ~a~%" pad n
                      (if (= n 1) "Root" "Delegation"))
              (printf "~a    From: ~a~%" pad (principal-fingerprint (cert-issuer c)))
              (printf "~a    To:   ~a~%" pad (principal-fingerprint (cert-subject c)))
              (printf "~a    Grants: ~a~%" pad
                      (let ((tag (cert-tag c)))
                        (if (all-perms? tag) "(*) ALL" (tag-sexp tag))))
              (printf "~a    Propagate: ~a~%" pad (if (cert-propagate c) "yes" "no"))
              (loop (cdr certs) (+ n 1)))))
        (printf "~a========================~%" pad)
        (print))))

  ;; ============================================================
  ;; Principal Inspection
  ;; ============================================================

  (define (inspect-principal principal . rest)
    (let ((soup-certs (get-opt rest 0 '())))
      (print)
      (print "=== Principal Security Properties ===")
      (display-principal principal 1)

      (let ((as-issuer (filter
                        (lambda (sc)
                          (equal? (principal-fingerprint (cert-issuer (signed-cert-cert sc)))
                                  (principal-fingerprint principal)))
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
                           (equal? (principal-fingerprint (cert-subject (signed-cert-cert sc)))
                                   (principal-fingerprint principal)))
                         soup-certs)))
        (printf "Certificates Granted: ~a~%" (length as-subject))
        (for-each
         (lambda (sc)
           (let ((c (signed-cert-cert sc)))
             (printf "  <- ~a : ~a~%"
                     (principal-fingerprint (cert-issuer c))
                     (let ((t (cert-tag c))) (if (all-perms? t) "(*)" (tag-sexp t))))))
         as-subject))

      `((fingerprint . ,(principal-fingerprint principal))
        (type . ,(cond ((key-principal? principal) 'key)
                       ((keyhash-principal? principal) 'keyhash)
                       (else 'unknown))))))

  ;; ============================================================
  ;; Certificate Inspection
  ;; ============================================================

  (define (inspect-cert signed-cert . rest)
    (let ((issuer-key (get-opt rest 0 #f)))
      (display-cert signed-cert)
      (when issuer-key
        (let ((valid (verify-signed-cert signed-cert issuer-key)))
          (print (if valid "Signature Valid" "Signature Invalid"))))
      (let ((c (signed-cert-cert signed-cert)))
        `((issuer . ,(principal-fingerprint (cert-issuer c)))
          (subject . ,(principal-fingerprint (cert-subject c)))
          (capability . ,(let ((t (cert-tag c)))
                          (if (all-perms? t) '(*) (tag-sexp t))))
          (propagate . ,(cert-propagate c))))))

  (define (cert-status signed-cert issuer-key . rest)
    (let ((revocations (get-opt rest 0 '())))
      (let* ((c (signed-cert-cert signed-cert))
             (sig-valid (verify-signed-cert signed-cert issuer-key))
             (cert-fp (principal-fingerprint (cert-subject c))))
        (cond
         ((not sig-valid) 'invalid-signature)
         ((cert-revoked? cert-fp revocations) 'revoked)
         ((validity-expired? (cert-validity c)) 'expired)
         (else 'valid)))))

  (define (cert-revoked? cert-fingerprint revocations)
    (any (lambda (rev)
           (equal? cert-fingerprint (alist-ref 'fingerprint rev)))
         revocations))

  ;; ============================================================
  ;; Capability Queries
  ;; ============================================================

  (define (who-can capability soup-certs)
    (print)
    (printf "=== WHO CAN: ~a ===~%" capability)
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
          (print "  (no principals found)")
          (for-each (lambda (fp) (printf "  + ~a~%" fp))
                    (delete-duplicates holders equal?)))
      (print)
      holders))

  (define (what-can principal soup-certs)
    (print)
    (printf "=== Capabilities of: ~a ===~%" (principal-fingerprint principal))
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
             (printf "  * ~a~%" (if (all-perms? cap) "(*) All Permissions" (tag-sexp cap))))
           caps))
      (print)
      caps))

  (define (authority-for capability principal soup-certs)
    (print)
    (printf "=== Authority for: ~a doing ~a ===~%"
            (principal-fingerprint principal) capability)
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
          (begin (print "  (no direct grant found)") '())
          (begin
            (print "Direct grants:")
            (for-each
             (lambda (sc)
               (let ((c (signed-cert-cert sc)))
                 (printf "  From: ~a~%" (principal-fingerprint (cert-issuer c)))
                 (printf "  Tag:  ~a~%" (let ((t (cert-tag c)))
                                         (if (all-perms? t) "(*)" (tag-sexp t))))))
             direct)
            direct))))

  ;; ============================================================
  ;; Verification
  ;; ============================================================

  (define (verify-object obj-type obj-name . rest)
    (let ((context (get-opt rest 0 '())))
      (print)
      (printf "=== Verifying: ~a (~a) ===~%" obj-name obj-type)
      (case obj-type
        ((keys) (verify-key-file obj-name))
        ((releases) (verify-release obj-name context))
        ((certs) (verify-certificate obj-name context))
        (else
         (printf "Unknown object type: ~a~%" obj-type)
         `((error . ,(format #f "Unknown type: ~a" obj-type)))))))

  (define (verify-key-file filename)
    (print "Key verification:")
    (let ((exists (file-exists? filename)))
      (printf "  * File exists: ~a~%" (if exists "yes" "no"))
      (if (not exists)
          `((exists . #f) (valid . #f))
          (guard (exn [#t
                       (print "  * Parse: failed")
                       `((exists . #t) (valid . #f) (error . "parse failed"))])
            (let* ((content (with-input-from-file filename
                              (lambda () (get-string-all (current-input-port)))))
                   (sexp (parse-sexp content))
                   (items (and (sexp-list? sexp) (list-items sexp))))
              (if (and items
                       (= 2 (length items))
                       (sexp-atom? (car items))
                       (sexp-bytes? (cadr items)))
                  (let* ((type-str (atom-value (car items)))
                         (key-bytes (bytes-value (cadr items)))
                         (key-len (blob-size key-bytes))
                         (valid-type (or (string=? type-str "spki-private-key")
                                        (string=? type-str "spki-public-key")))
                         (valid-len (or (= key-len 32) (= key-len 64))))
                    (printf "  * Format:   ~a~%" (if valid-type "ok" "bad"))
                    (printf "  * Key size: ~a bytes ~a~%" key-len (if valid-len "ok" "bad"))
                    `((exists . #t) (valid . ,(and valid-type valid-len))
                      (type . ,type-str) (size . ,key-len)))
                  (begin
                    (print "  * Format: bad (invalid structure)")
                    `((exists . #t) (valid . #f)))))))))

  (define (verify-release release-name context)
    (print "Release verification: pending")
    `((exists . pending) (valid . pending)))

  (define (verify-certificate cert-name context)
    (print "Certificate verification: pending")
    `((signature . pending) (validity . pending)))

  (define (verify-chain-to root-principal chain)
    (print)
    (print "=== Chain Verification ===")
    (if (null? chain)
        (begin (print "  Empty chain") #f)
        (let loop ((certs chain) (expected-issuer root-principal) (n 1))
          (if (null? certs)
              (begin (print "Chain valid") #t)
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
                      (printf "Chain broken at step ~a~%" n)
                      #f)))))))

  (define (check-revocation signed-cert soup-revocations)
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
    (print)
    (print "=== Soup Security Summary ===")
    (print "  Keys:         (run to count)")
    (print "  Certificates: (run to count)")
    (print "  Audit entries:(run to count)")
    (print "  Use: who-can / what-can / authority-for")
    (print))

  (define (security-audit principal soup-certs soup-audit)
    (let ((fp (principal-fingerprint principal)))
      (print)
      (printf "=== Security Audit: ~a ===~%" fp)

      (let ((issued (filter
                     (lambda (sc)
                       (equal? (principal-fingerprint (cert-issuer (signed-cert-cert sc))) fp))
                     soup-certs))
            (received (filter
                       (lambda (sc)
                         (equal? (principal-fingerprint (cert-subject (signed-cert-cert sc))) fp))
                       soup-certs)))

        (printf "Certificates issued: ~a~%" (length issued))
        (printf "Certificates received: ~a~%" (length received))

        (let ((actor-entries (filter
                              (lambda (entry)
                                (let ((actor (alist-ref 'actor entry)))
                                  (and actor (string? actor) (string-contains actor fp))))
                              soup-audit)))
          (printf "Audit entries: ~a~%" (length actor-entries))
          (print)

          `((fingerprint . ,fp)
            (certs-issued . ,(length issued))
            (certs-received . ,(length received))
            (audit-entries . ,(length actor-entries)))))))

) ;; end library
