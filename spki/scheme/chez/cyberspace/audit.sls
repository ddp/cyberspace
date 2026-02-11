;;; audit.sls - Cryptographic Audit Trail for Library of Cyberspace
;;; Chez Scheme Port
;;;
;;; Future-proof audit encoding with:
;;; - Content-addressed entries (tamper-evident)
;;; - Chained structure (append-only log)
;;; - SPKI authorization (who had permission)
;;; - Dual context (human + machine readable)
;;; - Cryptographic seals (Ed25519, ML-DSA, SPHINCS+, or hybrid signatures)
;;;
;;; Ported from Chicken's audit.scm.
;;; Changes: module -> library, (chicken *) -> compat shims,
;;;          #!key/#!optional -> get-key/get-opt, srfi-69 -> chez hash tables,
;;;          irregex -> simple string matching.

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

  (import (rnrs)
          (only (chezscheme)
                printf format
                with-output-to-string
                file-directory? directory-list mkdir
                getenv sort
                current-time time-second
                date-and-time)
          (cyberspace crypto-ffi)
          (cyberspace pq-crypto)
          (cyberspace chicken-compatibility blob)
          (cyberspace chicken-compatibility chicken))

  ;;; ============================================================================
  ;;; SRFI-1 helpers
  ;;; ============================================================================

  (define (every pred lst)
    (or (null? lst)
        (and (pred (car lst))
             (every pred (cdr lst)))))

  (define (any pred lst)
    (and (not (null? lst))
         (or (pred (car lst))
             (any pred (cdr lst)))))

  (define (filter-map proc lst)
    (let loop ((lst lst) (acc '()))
      (if (null? lst)
          (reverse acc)
          (let ((result (proc (car lst))))
            (if result
                (loop (cdr lst) (cons result acc))
                (loop (cdr lst) acc))))))

  ;;; ============================================================================
  ;;; String helpers (replacing srfi-13 and chicken irregex)
  ;;; ============================================================================

  (define (string-prefix? prefix str)
    (and (>= (string-length str) (string-length prefix))
         (string=? (substring str 0 (string-length prefix)) prefix)))

  (define (string-suffix? suffix str)
    (and (>= (string-length str) (string-length suffix))
         (string=? (substring str (- (string-length str) (string-length suffix))
                              (string-length str))
                   suffix)))

  (define (string-drop-right str n)
    (substring str 0 (max 0 (- (string-length str) n))))

  (define (string-take-right str n)
    (let ((len (string-length str)))
      (substring str (max 0 (- len n)) len)))

  (define (string-concatenate lst)
    (apply string-append lst))

  ;;; ============================================================================
  ;;; File/time helpers
  ;;; ============================================================================

  (define (directory-exists? path)
    (and (file-exists? path) (file-directory? path)))

  (define (create-directory path recursive?)
    (when recursive?
      (let loop ((parts (string-split-on-char path #\/)) (current ""))
        (unless (null? parts)
          (let ((next (if (string=? current "")
                          (car parts)
                          (string-append current "/" (car parts)))))
            (unless (or (string=? next "") (directory-exists? next))
              (guard (exn [#t #f])
                (mkdir next #o755)))
            (loop (cdr parts) next)))))
    (unless (directory-exists? path)
      (guard (exn [#t #f])
        (mkdir path #o755))))

  (define (string-split-on-char str ch)
    (let loop ((i 0) (start 0) (acc '()))
      (cond
        ((= i (string-length str))
         (reverse (if (= start i) acc (cons (substring str start i) acc))))
        ((char=? (string-ref str i) ch)
         (loop (+ i 1) (+ i 1)
               (if (= start i) acc (cons (substring str start i) acc))))
        (else
         (loop (+ i 1) start acc)))))

  (define (directory path)
    (if (directory-exists? path)
        (directory-list path)
        '()))

  (define (current-seconds)
    (time-second (current-time)))

  (define (seconds->string secs)
    (date-and-time))

  (define (sprintf fmt . args)
    (apply format #f fmt args))

  ;;; ============================================================================
  ;;; Audit Entry Structure
  ;;; ============================================================================

  (define-record-type <audit-entry>
    (fields (immutable id entry-id)
            (immutable timestamp entry-timestamp)
            (immutable sequence entry-sequence)
            (immutable parent-id entry-parent-id)
            (immutable actor entry-actor)
            (immutable action entry-action)
            (immutable context entry-context)
            (immutable environment entry-environment)
            (immutable seal entry-seal)))

  (define (make-audit-entry-internal id timestamp sequence parent-id
                                     actor action context environment seal)
    (make-<audit-entry> id timestamp sequence parent-id
                        actor action context environment seal))

  (define-record-type <audit-actor>
    (fields (immutable principal actor-principal)
            (immutable authorization-chain actor-authorization-chain)))

  (define (make-audit-actor principal authorization-chain)
    (make-<audit-actor> principal authorization-chain))

  (define-record-type <audit-action>
    (fields (immutable verb action-verb)
            (immutable object action-object)
            (immutable parameters action-parameters)))

  (define (make-audit-action verb object parameters)
    (make-<audit-action> verb object parameters))

  (define-record-type <audit-context>
    (fields (immutable motivation context-motivation)
            (immutable relates-to context-relates-to)
            (immutable language context-language)))

  (define (make-audit-context motivation relates-to language)
    (make-<audit-context> motivation relates-to language))

  (define-record-type <audit-seal>
    (fields (immutable algorithm seal-algorithm)
            (immutable content-hash seal-content-hash)
            (immutable signature seal-signature)))

  (define (make-audit-seal algorithm content-hash signature)
    (make-<audit-seal> algorithm content-hash signature))

  ;;; ============================================================================
  ;;; Configuration
  ;;; ============================================================================

  (define *audit-config*
    '((audit-dir . ".vault/audit")
      (current-sequence . 0)
      (signing-key . #f)))

  (define (audit-config key . rest)
    "Get or set audit configuration"
    (let ((value (get-opt rest 0 #f)))
      (if value
          (begin
            (set! *audit-config* (alist-update key value *audit-config*))
            value)
          (alist-ref key *audit-config*))))

  (define (audit-init . opts)
    "Initialize audit trail"
    (let ((signing-key (get-key opts 'signing-key: #f))
          (audit-dir (get-key opts 'audit-dir: #f)))
      (when signing-key
        (audit-config 'signing-key signing-key))
      (when audit-dir
        (audit-config 'audit-dir audit-dir))
      (let ((dir (audit-config 'audit-dir)))
        (create-directory dir #t)
        (print "Audit trail initialized: " dir))))

  ;;; ============================================================================
  ;;; Audit Entry Creation
  ;;; ============================================================================

  (define (audit-append . opts)
    "Append entry to audit trail"
    (let ((actor (get-key opts 'actor: #f))
          (action (get-key opts 'action: #f))
          (motivation (get-key opts 'motivation: #f))
          (relates-to (get-key opts 'relates-to: #f))
          (signing-key (get-key opts 'signing-key: #f))
          (algorithm (get-key opts 'algorithm: 'ed25519))
          (pq-signing-key (get-key opts 'pq-signing-key: #f))
          (auth-chain (get-key opts 'auth-chain: '())))

      (unless action
        (error 'audit-append "Action required for audit entry"))

      (let* ((sequence (+ 1 (audit-config 'current-sequence)))
             (parent-id (get-latest-entry-id))
             (timestamp (seconds->string (current-seconds)))
             (key (or signing-key (audit-config 'signing-key))))

        (unless key
          (error 'audit-append "No signing key configured"))

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

          (let ((unsealed-entry
                 (list 'audit-entry
                      (list 'timestamp timestamp)
                      (list 'sequence sequence)
                      (list 'parent-id parent-id)
                      (list 'actor (actor->sexp actor-obj))
                      (list 'action (action->sexp action-obj))
                      (list 'context (context->sexp context-obj))
                      (list 'environment env-obj))))

            (let* ((content-str (with-output-to-string
                                 (lambda () (write unsealed-entry))))
                   (content-hash (sha512-hash content-str))
                   (hash-hex (blob->hex content-hash))
                   (id (string-append "sha512:" (substring hash-hex 0 32)))

                   (signature
                    (case algorithm
                      ((ed25519)
                       (ed25519-sign key content-hash))
                      ((ml-dsa-65 ml-dsa)
                       (ml-dsa-sign content-hash key))
                      ((sphincs+ sphincs+-shake-256s)
                       (sphincs+-sign content-hash key))
                      ((hybrid)
                       (unless pq-signing-key
                         (error 'audit-append "Hybrid requires pq-signing-key"))
                       `(hybrid-signature
                         (ed25519 ,(ed25519-sign key content-hash))
                         (ml-dsa ,(ml-dsa-sign content-hash pq-signing-key))))
                      (else
                       (error 'audit-append "Unknown algorithm" algorithm))))

                   (seal-alg-name
                    (case algorithm
                      ((ed25519) "ed25519-sha512")
                      ((ml-dsa-65 ml-dsa) "ml-dsa-65-sha512")
                      ((sphincs+ sphincs+-shake-256s) "sphincs+-sha512")
                      ((hybrid) "hybrid-sha512")
                      (else "unknown")))

                   (seal-obj (make-audit-seal seal-alg-name content-hash signature))

                   (entry (make-audit-entry-internal
                           id timestamp sequence parent-id
                           actor-obj action-obj context-obj env-obj seal-obj)))

              (save-audit-entry entry)
              (audit-config 'current-sequence sequence)
              (print "Audit entry created: " id)
              entry))))))

  ;;; ============================================================================
  ;;; Entry Persistence
  ;;; ============================================================================

  (define (save-audit-entry entry)
    "Save audit entry to disk"
    (let* ((dir (audit-config 'audit-dir))
           (filename (sprintf "~a/~a.sexp" dir (entry-sequence entry))))
      (with-output-to-file filename
        (lambda ()
          (write (entry->sexp entry))
          (newline)))))

  (define (get-latest-entry-id)
    "Get ID of latest audit entry"
    (let ((dir (audit-config 'audit-dir)))
      (if (directory-exists? dir)
          (let ((files (sort string<? (directory dir))))
            (if (null? files)
                #f
                (let ((latest (car (reverse files))))
                  (let ((entry (read-audit-file (sprintf "~a/~a" dir latest))))
                    (if entry
                        (entry-id entry)
                        #f)))))
          #f)))

  (define (read-audit-file filename)
    "Read audit entry from file"
    (if (file-exists? filename)
        (let ((sexp (with-input-from-file filename read)))
          (sexp->entry sexp))
        #f))

  ;;; ============================================================================
  ;;; S-Expression Conversion
  ;;; ============================================================================

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
      (content-hash ,(blob->hex (seal-content-hash seal)))
      (signature ,(blob->hex (seal-signature seal)))))

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
               (evidence (let ((e (assq 'evidence fields)))
                          (if e (cdr e) '())))
               (seal (sexp->seal (assq 'seal fields))))
          (make-audit-entry-internal id timestamp sequence parent-id
                                    actor action context evidence seal))
        #f))

  ;;; ============================================================================
  ;;; Verification
  ;;; ============================================================================

  (define (audit-verify entry . opts)
    "Verify cryptographic seal on audit entry."
    (let ((public-key (get-key opts 'public-key: #f))
          (pq-public-key (get-key opts 'pq-public-key: #f)))
      (let ((key (or public-key
                     (actor-principal (entry-actor entry)))))
        (unless key
          (error 'audit-verify "No public key for verification"))

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
                 (computed-hash (sha512-hash content-str))
                 (seal (entry-seal entry))
                 (seal-alg (seal-algorithm seal))
                 (stored-hash (seal-content-hash seal))
                 (signature (seal-signature seal)))

            (if (not (equal? computed-hash stored-hash))
                (begin (print "Hash mismatch") #f)
                (let ((verified
                       (cond
                        ((string=? seal-alg "ed25519-sha512")
                         (ed25519-verify key computed-hash signature))
                        ((string=? seal-alg "ml-dsa-65-sha512")
                         (ml-dsa-verify computed-hash signature key))
                        ((string=? seal-alg "sphincs+-sha512")
                         (sphincs+-verify computed-hash signature key))
                        ((string=? seal-alg "hybrid-sha512")
                         (unless pq-public-key
                           (error 'audit-verify "Hybrid requires pq-public-key"))
                         (and (pair? signature)
                              (eq? (car signature) 'hybrid-signature)
                              (let ((ed-sig (cadr (assq 'ed25519 (cdr signature))))
                                    (pq-sig (cadr (assq 'ml-dsa (cdr signature)))))
                                (and ed-sig pq-sig
                                     (ed25519-verify key computed-hash ed-sig)
                                     (ml-dsa-verify computed-hash pq-sig pq-public-key)))))
                        (else
                         (print "Unknown seal algorithm: " seal-alg)
                         #f))))
                  (if verified
                      (begin
                        (print "Audit entry verified: " (entry-id entry)
                               " (" seal-alg ")")
                        #t)
                      (begin
                        (print "Signature invalid")
                        #f)))))))))

  (define (audit-chain . opts)
    "Verify entire audit chain"
    (let ((verify-key (get-key opts 'verify-key: #f))
          (dir (audit-config 'audit-dir)))
      (if (directory-exists? dir)
          (let ((files (sort string<? (directory dir))))
            (for-each
             (lambda (file)
               (let ((entry (read-audit-file (sprintf "~a/~a" dir file))))
                 (when entry
                   (audit-verify entry 'public-key: verify-key))))
             files))
          (print "No audit trail found"))))

  ;;; ============================================================================
  ;;; Query Interface
  ;;; ============================================================================

  (define (audit-read . opts)
    "Read specific audit entry"
    (let ((sequence (get-key opts 'sequence: #f))
          (id (get-key opts 'id: #f))
          (dir (audit-config 'audit-dir)))
      (cond
       (sequence
        (read-audit-file (sprintf "~a/~a.sexp" dir sequence)))
       (id
        (audit-search-by-id dir id))
       (else
        (error 'audit-read "Must specify sequence or id")))))

  (define (audit-search-by-id dir id)
    (let ((files (filter (lambda (f) (string-suffix? ".sexp" f))
                         (directory dir))))
      (let loop ((files files))
        (if (null? files)
            #f
            (let ((entry (read-audit-file
                          (string-append dir "/" (car files)))))
              (if (and entry
                       (<audit-entry>? entry)
                       (string-prefix? id (entry-id entry)))
                  entry
                  (loop (cdr files))))))))

  ;;; ============================================================================
  ;;; Time Parsing
  ;;; ============================================================================

  (define (parse-time-spec spec)
    "Parse time specification to epoch seconds.
     Accepts: '1h' '24h' '7d' '30d' or epoch number."
    (let ((now (current-seconds)))
      (cond
       ;; Relative time: match digit+unit pattern
       ((and (string? spec) (> (string-length spec) 1)
             (let ((unit (string-take-right spec 1))
                   (num-str (string-drop-right spec 1)))
               (and (string->number num-str)
                    (member unit '("h" "d" "m" "w"))
                    (cons (string->number num-str) unit))))
        => (lambda (pair)
             (let ((n (car pair))
                   (unit (cdr pair)))
               (- now (* n (cond
                            ((string=? unit "h") 3600)
                            ((string=? unit "d") 86400)
                            ((string=? unit "m") 60)
                            ((string=? unit "w") 604800)
                            (else 3600)))))))
       ((number? spec) spec)
       (else (- now 86400)))))

  (define (timestamp->epoch ts)
    "Convert audit timestamp string to epoch seconds (best effort)."
    (if (string? ts) (current-seconds) (current-seconds)))

  ;;; ============================================================================
  ;;; Query Engine
  ;;; ============================================================================

  (define (audit-all-entries)
    "Load all audit entries from disk."
    (let ((dir (audit-config 'audit-dir)))
      (if (directory-exists? dir)
          (let ((files (sort string<?
                             (filter (lambda (f) (string-suffix? ".sexp" f))
                                     (directory dir)))))
            (filter-map
             (lambda (file)
               (read-audit-file (sprintf "~a/~a" dir file)))
             files))
          '())))

  (define (match-criterion entry criterion)
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
    (audit-query (audit-all-entries) `(since ,start) `(before ,end)))

  ;;; ============================================================================
  ;;; Summary and Aggregation
  ;;; ============================================================================

  (define (audit-group-by entries field)
    "Group entries by field (type, hour, day)."
    (let ((groups (make-hashtable equal-hash equal?)))
      (for-each
       (lambda (entry)
         (let ((key (case field
                      ((type verb action)
                       (action-verb (entry-action entry)))
                      ((hour)
                       (let ((ts (timestamp->epoch (entry-timestamp entry))))
                         (div ts 3600)))
                      ((day date)
                       (let ((ts (timestamp->epoch (entry-timestamp entry))))
                         (div ts 86400)))
                      ((sequence)
                       (entry-sequence entry))
                      (else 'unknown))))
           (hashtable-set! groups key
                           (cons entry (hashtable-ref groups key '())))))
       entries)
      (map (lambda (k)
             (let ((entries (hashtable-ref groups k '())))
               (list k (length entries) entries)))
           (vector->list (hashtable-keys groups)))))

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
    (let* ((by (get-opt rest 0 'type))
           (groups (audit-group-by entries by))
           (sorted (sort (lambda (a b) (> (cadr a) (cadr b))) groups))
           (total (length entries))
           (max-count (if (null? sorted) 0 (apply max (map cadr sorted)))))

      (printf "~%Audit Summary: ~a entries~%~%" total)
      (printf "By ~a:~%" by)

      (for-each
       (lambda (group)
         (let* ((key (car group))
                (count (cadr group))
                (bar-width (if (zero? max-count)
                              0
                              (exact (floor (* 24.0 (/ count max-count))))))
                (bar (make-string bar-width #\#)))
           (printf "  ~a~a ~a~%"
                   (let ((s (audit-to-string key)))
                     (string-append s (make-string (max 1 (- 12 (string-length s))) #\space)))
                   (audit-pad-left (number->string count) 4 #\space)
                   bar)))
       sorted)
      (newline)))

  ;;; ============================================================================
  ;;; ASCII Plotting
  ;;; ============================================================================

  (define (audit-histogram buckets width height)
    "Generate ASCII histogram from bucket counts."
    (let* ((counts (map cdr buckets))
           (max-count (if (null? counts) 1 (apply max 1 counts)))
           (scale (/ (- height 1.0) max-count)))

      (let loop ((row (- height 1)))
        (when (>= row 0)
          (let ((threshold (* row (/ max-count (- height 1)))))
            (if (zero? (mod row 2))
                (printf "~a |"
                        (audit-pad-left (number->string (exact (round threshold))) 4 #\space))
                (display "     |"))
            (for-each
             (lambda (count)
               (let ((bar-height (* count scale)))
                 (display
                  (cond
                   ((> bar-height row) "#")
                   (else " ")))))
             counts)
            (newline))
          (loop (- row 1))))

      (printf "   0 +~a~%" (make-string (length buckets) #\-))

      (display "      ")
      (for-each
       (lambda (label)
         (display (if (> (string-length (audit-to-string label)) 2)
                      (substring (audit-to-string label) 0 2)
                      (audit-to-string label))))
       (map car buckets))
      (newline)))

  (define (audit-plot entries . opts)
    "Plot audit activity as ASCII histogram."
    (let* ((bucket (get-key opts 'bucket: "1h"))
           (span (get-key opts 'span: "24h"))
           (width (get-key opts 'width: 24))
           (height (get-key opts 'height: 8))
           (now (current-seconds))
           (span-secs (- now (parse-time-spec span)))
           (bucket-secs (let ((unit (string-take-right bucket 1))
                              (n (string->number (string-drop-right bucket 1))))
                          (cond
                            ((string=? unit "h") (* n 3600))
                            ((string=? unit "d") (* n 86400))
                            ((string=? unit "m") (* n 60))
                            (else 3600))))
           (num-buckets (max 1 (div span-secs bucket-secs)))
           (bucket-counts (make-vector num-buckets 0))
           (start-time (- now span-secs)))

      (for-each
       (lambda (entry)
         (let* ((ts (timestamp->epoch (entry-timestamp entry)))
                (age (- now ts)))
           (when (and (>= ts start-time) (< ts now))
             (let ((bucket-idx (min (- num-buckets 1)
                                   (max 0 (div (- ts start-time) bucket-secs)))))
               (vector-set! bucket-counts bucket-idx
                           (+ 1 (vector-ref bucket-counts bucket-idx)))))))
       entries)

      (let ((buckets
             (let loop ((i 0) (result '()))
               (if (>= i num-buckets)
                   (reverse result)
                   (loop (+ i 1)
                         (cons (cons (number->string i) (vector-ref bucket-counts i))
                               result))))))
        (printf "~%Audit Activity (~a, ~a buckets)~%~%" span bucket)
        (audit-histogram buckets width height))))

  ;;; ============================================================================
  ;;; Export Formats
  ;;; ============================================================================

  (define (audit-export-sexp . opts)
    "Export entire audit trail as S-expressions"
    (let ((output (get-key opts 'output: "audit-export.sexp"))
          (dir (audit-config 'audit-dir)))
      (with-output-to-file output
        (lambda ()
          (print "(audit-trail")
          (let ((files (sort string<? (directory dir))))
            (for-each
             (lambda (file)
               (let ((entry (read-audit-file (sprintf "~a/~a" dir file))))
                 (when entry
                   (write (entry->sexp entry))
                   (newline))))
             files))
          (print ")")))))

  (define (audit-export-human . opts)
    "Export audit trail in human-readable format"
    (let ((output (get-key opts 'output: "audit-export.txt"))
          (dir (audit-config 'audit-dir)))
      (with-output-to-file output
        (lambda ()
          (print "Audit Trail - Library of Cyberspace")
          (print "===================================")
          (print "")
          (let ((files (sort string<? (directory dir))))
            (for-each
             (lambda (file)
               (let ((entry (read-audit-file (sprintf "~a/~a" dir file))))
                 (when entry
                   (print "Entry #" (entry-sequence entry))
                   (print "  ID: " (entry-id entry))
                   (print "  Time: " (entry-timestamp entry))
                   (print "  Action: " (action-verb (entry-action entry)))
                   (when (context-motivation (entry-context entry))
                     (print "  Why: " (context-motivation (entry-context entry))))
                   (print ""))))
             files))))))

  ;;; ============================================================================
  ;;; Utility Functions
  ;;; ============================================================================

  (define (blob->hex blob)
    "Convert blob to hex string"
    (string-concatenate
     (map (lambda (b)
            (let ((hex (number->string b 16)))
              (if (= 1 (string-length hex))
                  (string-append "0" hex)
                  hex)))
          (let ((vec (blob->u8vector blob)))
            (let loop ((i 0) (acc '()))
              (if (>= i (u8vector-length vec))
                  (reverse acc)
                  (loop (+ i 1) (cons (u8vector-ref vec i) acc))))))))

  (define (get-environment-snapshot)
    "Capture current environment"
    `((platform ,(or (getenv "OSTYPE") "unknown"))
      (timestamp ,(current-seconds))))

) ;; end library
