;;; audit.sls - Cryptographic Audit Trail (Chez Port)
;;; Library of Cyberspace
;;;
;;; Future-proof audit encoding with:
;;; - Content-addressed entries (tamper-evident)
;;; - Chained structure (append-only log)
;;; - SPKI authorization (who had permission)
;;; - Dual context (human + machine readable)
;;; - Cryptographic seals (Ed25519, with PQ guards)
;;;
;;; Ported from audit.scm.
;;; Changes:
;;;   - define-record-type -> tagged vectors
;;;   - irregex -> manual string parsing for time specs
;;;   - (chicken file) -> Chez file-exists? / directory-list / system mkdir
;;;   - (chicken time posix) -> manual epoch<->ISO conversion
;;;   - pq-crypto paths guarded (not yet ported)
;;;
;;; Copyright (c) 2026 Yoyodyne. See LICENSE.

(library (cyberspace audit)
  (export
    ;; Core operations
    audit-init
    audit-append
    audit-verify
    audit-read
    audit-chain
    audit-config

    ;; Query interface (VMS ANALYZE/AUDIT style)
    audit-query
    audit-all-entries
    audit-by-actor
    audit-by-action
    audit-by-timerange

    ;; Summary and aggregation
    audit-summary
    audit-group-by

    ;; ASCII plotting
    audit-plot
    audit-histogram

    ;; Time utilities
    parse-time-spec

    ;; Export formats
    audit-export-sexp
    audit-export-human

    ;; Entry accessors (for external use)
    entry-id
    entry-timestamp
    entry-sequence
    entry-actor
    entry-action
    entry-context
    action-verb
    action-object)

  (import (except (rnrs) with-output-to-file with-input-from-file file-exists? list-sort flush-output-port find)
          (only (chezscheme)
                printf format void
                with-output-to-string with-output-to-file with-input-from-file
                file-exists? file-directory? directory-list
                list-sort flush-output-port getenv system
                make-time time-second current-time
                inexact->exact)
          (cyberspace chicken-compatibility chicken)
          (cyberspace chicken-compatibility blob)
          (cyberspace chicken-compatibility hashtable)
          (cyberspace crypto-ffi))

  ;; ============================================================
  ;; Audit Entry Records (tagged vectors)
  ;; ============================================================

  ;; Entry: #(tag id timestamp sequence parent-id actor action context environment seal)
  (define *entry-tag* (list 'audit-entry))
  (define (make-audit-entry id ts seq parent actor action ctx env seal)
    (vector *entry-tag* id ts seq parent actor action ctx env seal))
  (define (audit-entry? x)
    (and (vector? x) (>= (vector-length x) 10) (eq? (vector-ref x 0) *entry-tag*)))
  (define (entry-id e)          (vector-ref e 1))
  (define (entry-timestamp e)   (vector-ref e 2))
  (define (entry-sequence e)    (vector-ref e 3))
  (define (entry-parent-id e)   (vector-ref e 4))
  (define (entry-actor e)       (vector-ref e 5))
  (define (entry-action e)      (vector-ref e 6))
  (define (entry-context e)     (vector-ref e 7))
  (define (entry-environment e) (vector-ref e 8))
  (define (entry-seal e)        (vector-ref e 9))

  ;; Actor: #(tag principal authorization-chain)
  (define *actor-tag* (list 'audit-actor))
  (define (make-audit-actor principal auth-chain)
    (vector *actor-tag* principal auth-chain))
  (define (audit-actor? x)
    (and (vector? x) (>= (vector-length x) 3) (eq? (vector-ref x 0) *actor-tag*)))
  (define (actor-principal a)            (vector-ref a 1))
  (define (actor-authorization-chain a)  (vector-ref a 2))

  ;; Action: #(tag verb object parameters)
  (define *action-tag* (list 'audit-action))
  (define (make-audit-action verb object params)
    (vector *action-tag* verb object params))
  (define (audit-action? x)
    (and (vector? x) (>= (vector-length x) 4) (eq? (vector-ref x 0) *action-tag*)))
  (define (action-verb a)       (vector-ref a 1))
  (define (action-object a)     (vector-ref a 2))
  (define (action-parameters a) (vector-ref a 3))

  ;; Context: #(tag motivation relates-to language)
  (define *context-tag* (list 'audit-context))
  (define (make-audit-context motivation relates-to language)
    (vector *context-tag* motivation relates-to language))
  (define (audit-context? x)
    (and (vector? x) (>= (vector-length x) 4) (eq? (vector-ref x 0) *context-tag*)))
  (define (context-motivation c) (vector-ref c 1))
  (define (context-relates-to c) (vector-ref c 2))
  (define (context-language c)   (vector-ref c 3))

  ;; Seal: #(tag algorithm content-hash signature)
  (define *seal-tag* (list 'audit-seal))
  (define (make-audit-seal algorithm content-hash signature)
    (vector *seal-tag* algorithm content-hash signature))
  (define (audit-seal? x)
    (and (vector? x) (>= (vector-length x) 4) (eq? (vector-ref x 0) *seal-tag*)))
  (define (seal-algorithm s)    (vector-ref s 1))
  (define (seal-content-hash s) (vector-ref s 2))
  (define (seal-signature s)    (vector-ref s 3))

  ;; ============================================================
  ;; Configuration
  ;; ============================================================

  (define *audit-config*
    '((audit-dir . ".vault/audit")
      (current-sequence . 0)
      (signing-key . #f)))

  (define (audit-config key . rest)
    "Get or set audit configuration."
    (if (pair? rest)
        (begin
          (set! *audit-config* (alist-update key (car rest) *audit-config*))
          (car rest))
        (alist-ref key *audit-config*)))

  (define (audit-init . opts)
    "Initialize audit trail."
    (let ((signing-key (get-key opts 'signing-key: #f))
          (audit-dir   (get-key opts 'audit-dir: #f)))
      (when signing-key
        (audit-config 'signing-key signing-key))
      (when audit-dir
        (audit-config 'audit-dir audit-dir))
      (let ((dir (audit-config 'audit-dir)))
        (unless (file-exists? dir)
          (system (string-append "mkdir -p " dir)))
        (print "Audit trail initialized: " dir))))

  ;; ============================================================
  ;; Time Utilities
  ;; ============================================================

  ;; Zero-pad a number to width characters
  (define (pad-zero n width)
    (let ((s (number->string n)))
      (if (< (string-length s) width)
          (string-append (make-string (- width (string-length s)) #\0) s)
          s)))

  ;; Convert epoch seconds to ISO-8601 UTC string
  ;; Uses Hinnant's civil_from_days algorithm
  (define (seconds->string secs)
    (let* ((z (+ (quotient secs 86400) 719468))
           (era (quotient (if (>= z 0) z (- z 146096)) 146097))
           (doe (- z (* era 146097)))
           (yoe (quotient (+ doe (- (quotient doe 1460))
                             (quotient doe 36524)
                             (- (quotient doe 146096)))
                          365))
           (y (+ yoe (* era 400)))
           (doy (- doe (- (+ (* 365 yoe) (quotient yoe 4))
                          (quotient yoe 100))))
           (mp (quotient (+ (* 5 doy) 2) 153))
           (d (+ (- doy (quotient (+ (* 153 mp) 2) 5)) 1))
           (m (+ mp (if (< mp 10) 3 -9)))
           (yr (+ y (if (<= m 2) 1 0)))
           (tod (modulo secs 86400))
           (h (quotient tod 3600))
           (min (quotient (modulo tod 3600) 60))
           (sec (modulo tod 60)))
      (string-append (pad-zero yr 4) "-" (pad-zero m 2) "-" (pad-zero d 2)
                     "T" (pad-zero h 2) ":" (pad-zero min 2) ":" (pad-zero sec 2))))

  ;; Convert ISO-8601 date to epoch seconds (inverse of above)
  ;; Uses Hinnant's days_from_civil algorithm
  (define (iso->epoch yr m d h min sec)
    (let* ((yr2 (if (<= m 2) (- yr 1) yr))
           (m2 (if (<= m 2) (+ m 9) (- m 3)))
           (era (quotient (if (>= yr2 0) yr2 (- yr2 399)) 400))
           (yoe (- yr2 (* era 400)))
           (doy (quotient (- (* (+ (* 153 m2) 2) 1) 1) 5))
           (doe (+ (* 365 yoe) (quotient yoe 4) (- (quotient yoe 100)) doy (- d 1)))
           (days (+ (* era 146097) doe -719468)))
      (+ (* days 86400) (* h 3600) (* min 60) sec)))

  (define (parse-time-spec spec)
    "Parse time specification to epoch seconds.
     Accepts: '1h' '24h' '7d' '30d' or ISO date or epoch number."
    (let ((now (current-seconds)))
      (cond
        ;; Already a number (epoch)
        ((number? spec) spec)

        ;; Relative time: digits followed by h/d/m/w
        ((and (string? spec)
              (> (string-length spec) 1)
              (let ((last (string-ref spec (- (string-length spec) 1))))
                (memv last '(#\h #\d #\m #\w)))
              (let ((digits (string-drop-right spec 1)))
                (string->number digits)))
         => (lambda (n)
              (let ((unit (string-ref spec (- (string-length spec) 1))))
                (- now (* n (case unit
                              ((#\h) 3600)
                              ((#\d) 86400)
                              ((#\m) 60)
                              ((#\w) 604800)
                              (else 3600)))))))

        ;; ISO date: YYYY-MM-DD
        ((and (string? spec) (= (string-length spec) 10)
              (char=? (string-ref spec 4) #\-)
              (char=? (string-ref spec 7) #\-))
         (let ((parts (string-split spec "-")))
           (iso->epoch (string->number (car parts))
                       (string->number (cadr parts))
                       (string->number (caddr parts))
                       0 0 0)))

        ;; ISO datetime: YYYY-MM-DDTHH:MM:SS
        ((and (string? spec) (= (string-length spec) 19)
              (char=? (string-ref spec 10) #\T))
         (let* ((date-time (string-split spec "T"))
                (date-parts (string-split (car date-time) "-"))
                (time-parts (string-split (cadr date-time) ":")))
           (iso->epoch (string->number (car date-parts))
                       (string->number (cadr date-parts))
                       (string->number (caddr date-parts))
                       (string->number (car time-parts))
                       (string->number (cadr time-parts))
                       (string->number (caddr time-parts)))))

        ;; Default: 24h ago
        (else (- now 86400)))))

  (define (timestamp->epoch ts)
    "Convert audit timestamp string to epoch seconds."
    (if (and (string? ts)
             (>= (string-length ts) 19)
             (char=? (string-ref ts 10) #\T))
        (parse-time-spec (substring ts 0 19))
        (current-seconds)))

  ;; ============================================================
  ;; Audit Entry Creation
  ;; ============================================================

  (define (audit-append . opts)
    "Append entry to audit trail.
     Keywords: actor: action: motivation: relates-to: signing-key:
               algorithm: pq-signing-key: auth-chain:"
    (let ((actor          (get-key opts 'actor: #f))
          (action         (get-key opts 'action: #f))
          (motivation     (get-key opts 'motivation: #f))
          (relates-to     (get-key opts 'relates-to: #f))
          (signing-key    (get-key opts 'signing-key: #f))
          (algorithm      (get-key opts 'algorithm: 'ed25519))
          (pq-signing-key (get-key opts 'pq-signing-key: #f))
          (auth-chain     (get-key opts 'auth-chain: '())))

      (unless action
        (error 'audit-append "Action required for audit entry"))

      (let* ((sequence (+ 1 (audit-config 'current-sequence)))
             (parent-id (get-latest-entry-id))
             (timestamp (seconds->string (current-seconds)))
             (key (or signing-key (audit-config 'signing-key))))

        (unless key
          (error 'audit-append "No signing key configured"))

        ;; Build entry components
        (let ((actor-obj (make-audit-actor actor auth-chain))
              (action-obj (make-audit-action
                            (car action)
                            (if (pair? (cdr action)) (cadr action) #f)
                            (if (and (pair? (cdr action))
                                     (pair? (cddr action)))
                                (cddr action)
                                '())))
              (context-obj (make-audit-context motivation relates-to "en"))
              (env-obj (get-environment-snapshot)))

          ;; Create unsealed entry for hashing
          (let ((unsealed-entry
                  (list 'audit-entry
                        (list 'timestamp timestamp)
                        (list 'sequence sequence)
                        (list 'parent-id parent-id)
                        (list 'actor (actor->sexp actor-obj))
                        (list 'action (action->sexp action-obj))
                        (list 'context (context->sexp context-obj))
                        (list 'environment env-obj))))

            ;; Compute content hash
            (let* ((content-str (with-output-to-string
                                  (lambda () (write unsealed-entry))))
                   (content-hash (sha512-hash (string->utf8 content-str)))
                   (hash-hex (bytevector->hex content-hash))
                   (id (string-append "sha512:" (substring hash-hex 0 32)))

                   ;; Sign the content hash
                   (signature
                     (case algorithm
                       ((ed25519)
                        (ed25519-sign key content-hash))
                       ((ml-dsa-65 ml-dsa sphincs+ sphincs+-shake-256s hybrid)
                        (error 'audit-append
                               "Post-quantum signatures not yet ported to Chez"
                               algorithm))
                       (else
                        (error 'audit-append "Unknown algorithm" algorithm))))

                   (seal-alg-name
                     (case algorithm
                       ((ed25519) "ed25519-sha512")
                       (else "unknown")))

                   (seal-obj (make-audit-seal seal-alg-name content-hash signature))

                   (entry (make-audit-entry
                            id timestamp sequence parent-id
                            actor-obj action-obj context-obj env-obj seal-obj)))

              ;; Save entry
              (save-audit-entry entry)

              ;; Update sequence counter
              (audit-config 'current-sequence sequence)

              (print "Audit entry created: " id)
              entry))))))

  ;; ============================================================
  ;; Entry Persistence
  ;; ============================================================

  (define (save-audit-entry entry)
    "Save audit entry to disk."
    (let* ((dir (audit-config 'audit-dir))
           (filename (string-append dir "/" (number->string (entry-sequence entry)) ".sexp")))
      (with-output-to-file filename
        (lambda ()
          (write (entry->sexp entry))
          (newline)))))

  (define (get-latest-entry-id)
    "Get ID of latest audit entry."
    (let ((dir (audit-config 'audit-dir)))
      (if (and (file-exists? dir) (file-directory? dir))
          (let ((files (list-sort string<? (directory-list dir))))
            (if (null? files)
                #f
                (let ((latest (car (reverse files))))
                  (let ((entry (read-audit-file (string-append dir "/" latest))))
                    (if entry (entry-id entry) #f)))))
          #f)))

  (define (read-audit-file filename)
    "Read audit entry from file."
    (if (file-exists? filename)
        (guard (exn [#t #f])
          (let ((sexp (with-input-from-file filename read)))
            (sexp->entry sexp)))
        #f))

  ;; ============================================================
  ;; S-Expression Conversion
  ;; ============================================================

  (define (actor->sexp actor)
    `(actor
      (principal ,(actor-principal actor))
      (authorization-chain ,@(actor-authorization-chain actor))))

  (define (action->sexp action)
    `(action
      (verb ,(action-verb action))
      ,@(if (action-object action)
            `((object ,(action-object action)))
            '())
      ,@(if (not (null? (action-parameters action)))
            `((parameters ,@(action-parameters action)))
            '())))

  (define (context->sexp context)
    `(context
      ,@(if (context-motivation context)
            `((motivation ,(context-motivation context)))
            '())
      ,@(if (context-relates-to context)
            `((relates-to ,(context-relates-to context)))
            '())
      (language ,(context-language context))))

  (define (seal->sexp seal)
    `(seal
      (algorithm ,(seal-algorithm seal))
      (content-hash ,(bytevector->hex (seal-content-hash seal)))
      (signature ,(bytevector->hex (seal-signature seal)))))

  (define (entry->sexp entry)
    `(audit-entry
      (id ,(entry-id entry))
      (timestamp ,(entry-timestamp entry))
      (sequence ,(entry-sequence entry))
      ,@(if (entry-parent-id entry)
            `((parent-id ,(entry-parent-id entry)))
            '())
      ,(actor->sexp (entry-actor entry))
      ,(action->sexp (entry-action entry))
      ,(context->sexp (entry-context entry))
      (environment ,@(entry-environment entry))
      ,(seal->sexp (entry-seal entry))))

  (define (sexp->actor sexp)
    (if (and (pair? sexp) (eq? 'actor (car sexp)))
        (let ((principal (cadr (assq 'principal (cdr sexp))))
              (auth-chain-sexp (assq 'authorization-chain (cdr sexp))))
          (make-audit-actor
            principal
            (if auth-chain-sexp (cdr auth-chain-sexp) '())))
        (make-audit-actor #f '())))

  (define (sexp->action sexp)
    (if (and (pair? sexp) (eq? 'action (car sexp)))
        (let ((verb (cadr (assq 'verb (cdr sexp))))
              (object (let ((o (assq 'object (cdr sexp))))
                        (if o (cadr o) #f)))
              (params (let ((p (assq 'parameters (cdr sexp))))
                        (if p (cdr p) '()))))
          (make-audit-action verb object params))
        (make-audit-action 'unknown #f '())))

  (define (sexp->context sexp)
    (if (and (pair? sexp) (eq? 'context (car sexp)))
        (let ((motivation (let ((m (assq 'motivation (cdr sexp))))
                            (if m (cadr m) #f)))
              (relates-to (let ((r (assq 'relates-to (cdr sexp))))
                            (if r (cadr r) #f)))
              (language (let ((l (assq 'language (cdr sexp))))
                          (if l (cadr l) "en"))))
          (make-audit-context motivation relates-to language))
        (make-audit-context #f #f "en")))

  (define (sexp->seal sexp)
    (if (and (pair? sexp) (eq? 'seal (car sexp)))
        (let ((algorithm (cadr (assq 'algorithm (cdr sexp))))
              (value (let ((v (assq 'value (cdr sexp))))
                       (if v (cadr v) #f)))
              (chain (let ((c (assq 'chain (cdr sexp))))
                       (if c (cadr c) #f))))
          (make-audit-seal algorithm value chain))
        (make-audit-seal "ed25519-sha512" #f #f)))

  (define (sexp->entry sexp)
    (if (and (pair? sexp) (eq? 'audit-entry (car sexp)))
        (let* ((fields (cdr sexp))
               (id (cadr (assq 'id fields)))
               (timestamp (cadr (assq 'timestamp fields)))
               (sequence (cadr (assq 'sequence fields)))
               (parent-id (let ((p (assq 'parent-id fields)))
                            (if p (cadr p) #f)))
               (actor (sexp->actor (assq 'actor fields)))
               (action (sexp->action (assq 'action fields)))
               (context (sexp->context (assq 'context fields)))
               (env (let ((e (assq 'environment fields)))
                      (if e (cdr e) '())))
               (seal (sexp->seal (assq 'seal fields))))
          (make-audit-entry id timestamp sequence parent-id
                            actor action context env seal))
        #f))

  ;; ============================================================
  ;; Verification
  ;; ============================================================

  (define (audit-verify entry . opts)
    "Verify cryptographic seal on audit entry."
    (let* ((public-key    (get-key opts 'public-key: #f))
           (pq-public-key (get-key opts 'pq-public-key: #f))
           (key (or public-key (actor-principal (entry-actor entry)))))

      (unless key
        (error 'audit-verify "No public key for verification"))

      ;; Reconstruct content for verification
      (let ((unsealed-entry
              (list 'audit-entry
                    (list 'timestamp (entry-timestamp entry))
                    (list 'sequence (entry-sequence entry))
                    (list 'parent-id (entry-parent-id entry))
                    (list 'actor (actor->sexp (entry-actor entry)))
                    (list 'action (action->sexp (entry-action entry)))
                    (list 'context (context->sexp (entry-context entry)))
                    (list 'environment (entry-environment entry)))))

        (let* ((content-str (with-output-to-string
                              (lambda () (write unsealed-entry))))
               (computed-hash (sha512-hash (string->utf8 content-str)))
               (seal (entry-seal entry))
               (seal-alg (seal-algorithm seal))
               (stored-hash (seal-content-hash seal))
               (signature (seal-signature seal)))

          ;; Verify hash matches
          (if (not (bytevector=? computed-hash stored-hash))
              (begin
                (print "x Hash mismatch")
                #f)
              ;; Verify signature
              (let ((verified
                      (cond
                        ((string=? seal-alg "ed25519-sha512")
                         (ed25519-verify key computed-hash signature))
                        ((or (string=? seal-alg "ml-dsa-65-sha512")
                             (string=? seal-alg "sphincs+-sha512")
                             (string=? seal-alg "hybrid-sha512"))
                         (error 'audit-verify
                                "Post-quantum verification not yet ported"
                                seal-alg))
                        (else
                         (print "x Unknown seal algorithm: " seal-alg)
                         #f))))
                (if verified
                    (begin
                      (print "v Audit entry verified: " (entry-id entry)
                             " (" seal-alg ")")
                      #t)
                    (begin
                      (print "x Signature invalid")
                      #f))))))))

  (define (audit-chain . opts)
    "Verify entire audit chain."
    (let ((verify-key (get-key opts 'verify-key: #f))
          (dir (audit-config 'audit-dir)))
      (if (and (file-exists? dir) (file-directory? dir))
          (let ((files (list-sort string<? (directory-list dir))))
            (for-each
              (lambda (file)
                (let ((entry (read-audit-file (string-append dir "/" file))))
                  (when entry
                    (audit-verify entry 'public-key: verify-key))))
              files))
          (print "No audit trail found"))))

  ;; ============================================================
  ;; Query Interface
  ;; ============================================================

  (define (audit-read . opts)
    "Read specific audit entry."
    (let ((sequence (get-key opts 'sequence: #f))
          (id       (get-key opts 'id: #f))
          (dir (audit-config 'audit-dir)))
      (cond
        (sequence
          (read-audit-file (string-append dir "/" (number->string sequence) ".sexp")))
        (id
          (audit-search-by-id dir id))
        (else
          (error 'audit-read "Must specify sequence: or id:")))))

  (define (audit-search-by-id dir id)
    "Search audit files for entry with given ID prefix."
    (if (and (file-exists? dir) (file-directory? dir))
        (let ((files (filter (lambda (f) (string-suffix? ".sexp" f))
                             (directory-list dir))))
          (let loop ((files files))
            (if (null? files)
                #f
                (let ((entry (read-audit-file (string-append dir "/" (car files)))))
                  (if (and entry (string-prefix? id (entry-id entry)))
                      entry
                      (loop (cdr files)))))))
        #f))

  (define (audit-all-entries)
    "Load all audit entries from disk."
    (let ((dir (audit-config 'audit-dir)))
      (if (and (file-exists? dir) (file-directory? dir))
          (let ((files (list-sort string<?
                         (filter (lambda (f) (string-suffix? ".sexp" f))
                                 (directory-list dir)))))
            (filter-map
              (lambda (file)
                (read-audit-file (string-append dir "/" file)))
              files))
          '())))

  (define (match-criterion entry criterion)
    "Match single entry against one criterion."
    (let ((key (car criterion))
          (val (cadr criterion)))
      (case key
        ((type verb action)
         (let ((entry-verb (action-verb (entry-action entry))))
           (cond
             ((symbol? val) (eq? entry-verb val))
             ((string? val) (string=? (symbol->string entry-verb) val))
             (else #f))))

        ((object)
         (let ((entry-obj (action-object (entry-action entry))))
           (cond
             ((not entry-obj) #f)
             ((string? val)
              (if (string-suffix? "*" val)
                  (string-prefix? (string-drop-right val 1) entry-obj)
                  (string=? entry-obj val)))
             (else (equal? entry-obj val)))))

        ((since after)
         (let ((ts (timestamp->epoch (entry-timestamp entry)))
               (threshold (parse-time-spec val)))
           (>= ts threshold)))

        ((before until)
         (let ((ts (timestamp->epoch (entry-timestamp entry)))
               (threshold (parse-time-spec val)))
           (<= ts threshold)))

        ((sequence seq)
         (cond
           ((number? val) (= (entry-sequence entry) val))
           ((list? val)
            (and (>= (entry-sequence entry) (car val))
                 (<= (entry-sequence entry) (cadr val))))
           (else #f)))

        ((and)
         (every (lambda (c) (match-criterion entry c)) (cdr criterion)))

        ((or)
         (any (lambda (c) (match-criterion entry c)) (cdr criterion)))

        ((not)
         (not (match-criterion entry (cadr criterion))))

        (else #f))))

  (define (audit-query entries . criteria)
    "Filter entries by criteria list."
    (if (null? criteria)
        entries
        (filter
          (lambda (entry)
            (every (lambda (c) (match-criterion entry c)) criteria))
          entries)))

  (define (audit-by-actor actor-principal)
    (filter
      (lambda (entry)
        (equal? (actor-principal (entry-actor entry)) actor-principal))
      (audit-all-entries)))

  (define (audit-by-action verb)
    (audit-query (audit-all-entries) `(type ,verb)))

  (define (audit-by-timerange start end)
    (audit-query (audit-all-entries)
                 `(since ,start) `(before ,end)))

  ;; ============================================================
  ;; Summary and Aggregation
  ;; ============================================================

  (define (audit-group-by entries field)
    "Group entries by field (type, hour, day)."
    (let ((groups (make-hash-table)))
      (for-each
        (lambda (entry)
          (let ((key (case field
                       ((type verb action)
                        (action-verb (entry-action entry)))
                       ((hour)
                        (let ((ts (timestamp->epoch (entry-timestamp entry))))
                          (quotient ts 3600)))
                       ((day date)
                        (let ((ts (timestamp->epoch (entry-timestamp entry))))
                          (quotient ts 86400)))
                       ((sequence)
                        (entry-sequence entry))
                       (else 'unknown))))
            (hash-table-set! groups key
                             (cons entry (hash-table-ref/default groups key '())))))
        entries)
      (map (lambda (k)
             (let ((entries (hash-table-ref groups k)))
               (list k (length entries) entries)))
           (hash-table-keys groups))))

  (define (audit-pad-left str len char)
    (let ((slen (string-length str)))
      (if (>= slen len)
          str
          (string-append (make-string (- len slen) char) str))))

  (define (audit-to-string x)
    (cond
      ((string? x) x)
      ((symbol? x) (symbol->string x))
      ((number? x) (number->string x))
      (else (with-output-to-string (lambda () (write x))))))

  (define (audit-summary entries . rest)
    "Print summary of audit entries."
    (let* ((by (if (null? rest) 'type (car rest)))
           (groups (audit-group-by entries by))
           (sorted (list-sort (lambda (a b) (> (cadr a) (cadr b))) groups))
           (total (length entries))
           (max-count (if (null? sorted) 0 (apply max (map cadr sorted)))))

      (printf "\nAudit Summary: ~a entries\n\n" total)
      (printf "By ~a:\n" by)

      (for-each
        (lambda (group)
          (let* ((key (car group))
                 (count (cadr group))
                 (bar-width (if (zero? max-count)
                                0
                                (inexact->exact (floor (* 24.0 (/ count max-count))))))
                 (bar (make-string bar-width #\x2588)))  ; Unicode full block
            (printf "  ~a~a ~a\n"
                    (let ((s (audit-to-string key)))
                      (string-append s (make-string (max 1 (- 12 (string-length s))) #\space)))
                    (audit-pad-left (number->string count) 4 #\space)
                    bar)))
        sorted)
      (newline)))

  ;; ============================================================
  ;; ASCII Plotting
  ;; ============================================================

  (define *vbar-chars* '#("" "\x2581;" "\x2582;" "\x2583;" "\x2584;" "\x2585;" "\x2586;" "\x2587;" "\x2588;"))

  (define (audit-histogram buckets width height)
    "Generate ASCII histogram from bucket counts."
    (let* ((counts (map cdr buckets))
           (max-count (if (null? counts) 1 (apply max 1 counts)))
           (scale (/ (- height 1.0) max-count)))

      ;; Print from top to bottom
      (let loop ((row (- height 1)))
        (when (>= row 0)
          (let ((threshold (* row (/ max-count (- height 1)))))
            (if (zero? (modulo row 2))
                (printf "~a |" (audit-pad-left (number->string (inexact->exact (round threshold))) 4 #\space))
                (printf "     |")))
          ;; Bar segments
          (for-each
            (lambda (count)
              (let ((bar-height (* count scale)))
                (display
                  (cond
                    ((> bar-height row) "\x2588;")
                    ((> bar-height (- row 1))
                     (let ((frac (- bar-height (floor bar-height))))
                       (vector-ref *vbar-chars*
                                   (inexact->exact (min 8 (floor (* frac 8)))))))
                    (else " ")))))
            counts)
          (newline)
          (loop (- row 1))))

      ;; X-axis
      (printf "   0 +~a\n" (make-string (length buckets) #\-))

      ;; Labels
      (display "      ")
      (for-each
        (lambda (label)
          (display (let ((s (audit-to-string label)))
                     (if (> (string-length s) 2) (substring s 0 2) s))))
        (map car buckets))
      (newline)))

  (define (audit-plot entries . opts)
    "Plot audit activity as ASCII histogram."
    (let* ((bucket-spec (get-key opts 'bucket: "1h"))
           (span-spec   (get-key opts 'span: "24h"))
           (width       (get-key opts 'width: 24))
           (height      (get-key opts 'height: 8))
           (now (current-seconds))
           (span-secs (- now (parse-time-spec span-spec)))
           (bucket-secs (let ((unit (string-take-right bucket-spec 1))
                              (num-str (string-drop-right bucket-spec 1)))
                          (* (or (string->number num-str) 1)
                             (cond ((string=? unit "h") 3600)
                                   ((string=? unit "d") 86400)
                                   ((string=? unit "m") 60)
                                   (else 3600)))))
           (num-buckets (max 1 (quotient span-secs bucket-secs)))
           (bucket-counts (make-vector num-buckets 0))
           (start-time (- now span-secs)))

      ;; Count entries per bucket
      (for-each
        (lambda (entry)
          (let* ((ts (timestamp->epoch (entry-timestamp entry)))
                 (age (- now ts)))
            (when (and (>= ts start-time) (< ts now))
              (let ((idx (min (- num-buckets 1)
                              (max 0 (quotient (- ts start-time) bucket-secs)))))
                (vector-set! bucket-counts idx
                             (+ 1 (vector-ref bucket-counts idx)))))))
        entries)

      (let ((buckets
              (let loop ((i 0) (result '()))
                (if (>= i num-buckets)
                    (reverse result)
                    (loop (+ i 1)
                          (cons (cons (number->string i) (vector-ref bucket-counts i))
                                result))))))

        (printf "\nAudit Activity (~a, ~a buckets)\n\n" span-spec bucket-spec)
        (audit-histogram buckets width height))))

  ;; ============================================================
  ;; Export Formats
  ;; ============================================================

  (define (audit-export-sexp . opts)
    "Export entire audit trail as S-expressions."
    (let ((dir (audit-config 'audit-dir))
          (out (get-key opts 'output: "audit-export.sexp")))
      (with-output-to-file out
        (lambda ()
          (print "(audit-trail")
          (let ((files (list-sort string<? (directory-list dir))))
            (for-each
              (lambda (file)
                (let ((entry (read-audit-file (string-append dir "/" file))))
                  (when entry
                    (write (entry->sexp entry))
                    (newline))))
              files))
          (print ")")))))

  (define (audit-export-human . opts)
    "Export audit trail in human-readable format."
    (let ((dir (audit-config 'audit-dir))
          (out (get-key opts 'output: "audit-export.txt")))
      (with-output-to-file out
        (lambda ()
          (print "Audit Trail - Library of Cyberspace")
          (print "===================================")
          (print "")
          (let ((files (list-sort string<? (directory-list dir))))
            (for-each
              (lambda (file)
                (let ((entry (read-audit-file (string-append dir "/" file))))
                  (when entry
                    (print "Entry #" (entry-sequence entry))
                    (print "  ID: " (entry-id entry))
                    (print "  Time: " (entry-timestamp entry))
                    (print "  Action: " (action-verb (entry-action entry)))
                    (when (context-motivation (entry-context entry))
                      (print "  Why: " (context-motivation (entry-context entry))))
                    (print ""))))
              files))))))

  ;; ============================================================
  ;; Utilities
  ;; ============================================================

  (define (bytevector->hex bv)
    "Convert bytevector to hex string."
    (string-concatenate
      (map (lambda (b)
             (let ((hex (number->string b 16)))
               (if (= 1 (string-length hex))
                   (string-append "0" hex)
                   hex)))
           (let ((len (bytevector-length bv)))
             (let loop ((i 0) (acc '()))
               (if (= i len)
                   (reverse acc)
                   (loop (+ i 1) (cons (bytevector-u8-ref bv i) acc))))))))

  (define (get-environment-snapshot)
    "Capture current environment."
    `((platform ,(or (getenv "OSTYPE") "unknown"))
      (timestamp ,(current-seconds))))

) ;; end library
