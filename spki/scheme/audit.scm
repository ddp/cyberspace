;;; audit.scm - Cryptographic Audit Trail for Library of Cyberspace
;;;
;;; Future-proof audit encoding with:
;;; - Content-addressed entries (tamper-evident)
;;; - Chained structure (append-only log)
;;; - SPKI authorization (who had permission)
;;; - Dual context (human + machine readable)
;;; - Cryptographic seals (Ed25519, ML-DSA, SPHINCS+, or hybrid signatures)

(module audit
  (;; Core operations
   audit-init
   audit-append
   audit-verify
   audit-read
   audit-chain

   ;; Query interface (VMS ANALYZE/AUDIT style)
   audit-query            ; (audit-query entries criteria)
   audit-all-entries      ; Load all entries from disk
   audit-by-actor
   audit-by-action
   audit-by-timerange

   ;; Summary and aggregation
   audit-summary          ; (audit-summary entries)
   audit-group-by         ; (audit-group-by entries field)

   ;; ASCII plotting
   audit-plot             ; (audit-plot entries bucket-spec span-spec)
   audit-histogram        ; (audit-histogram buckets width height)

   ;; Time utilities
   parse-time-spec        ; Parse "1h", "24h", "7d", or ISO date

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

  (import scheme
          (chicken base)
          (chicken file)
          (chicken file posix)
          (chicken format)
          (chicken port)
          (chicken process-context)
          (chicken sort)
          (chicken time)
          (chicken time posix)
          (chicken blob)
          (chicken string)
          (chicken irregex)
          srfi-1   ; list utilities
          srfi-4   ; u8vectors
          srfi-13  ; string utilities
          srfi-69  ; hash tables
          crypto-ffi
          pq-crypto)

  ;;; ============================================================================
  ;;; Audit Entry Structure
  ;;; ============================================================================

  (define-record-type <audit-entry>
    (make-audit-entry-internal id timestamp sequence parent-id
                               actor action context environment seal)
    audit-entry?
    (id entry-id)
    (timestamp entry-timestamp)
    (sequence entry-sequence)
    (parent-id entry-parent-id)
    (actor entry-actor)
    (action entry-action)
    (context entry-context)
    (environment entry-environment)
    (seal entry-seal))

  (define-record-type <audit-actor>
    (make-audit-actor principal authorization-chain)
    audit-actor?
    (principal actor-principal)
    (authorization-chain actor-authorization-chain))

  (define-record-type <audit-action>
    (make-audit-action verb object parameters)
    audit-action?
    (verb action-verb)
    (object action-object)
    (parameters action-parameters))

  (define-record-type <audit-context>
    (make-audit-context motivation relates-to language)
    audit-context?
    (motivation context-motivation)
    (relates-to context-relates-to)
    (language context-language))

  (define-record-type <audit-seal>
    (make-audit-seal algorithm content-hash signature)
    audit-seal?
    (algorithm seal-algorithm)
    (content-hash seal-content-hash)
    (signature seal-signature))

  ;;; ============================================================================
  ;;; Configuration
  ;;; ============================================================================

  (define *audit-config*
    '((audit-dir . ".vault/audit")
      (current-sequence . 0)
      (signing-key . #f)))

  (define (audit-config key #!optional value)
    "Get or set audit configuration"
    (if value
        (begin
          (set! *audit-config* (alist-update key value *audit-config*))
          value)
        (alist-ref key *audit-config*)))

  (define (audit-init #!key signing-key audit-dir)
    "Initialize audit trail"
    (when signing-key
      (audit-config 'signing-key signing-key))
    (when audit-dir
      (audit-config 'audit-dir audit-dir))

    (let ((dir (audit-config 'audit-dir)))
      (create-directory dir #t)
      (print "Audit trail initialized: " dir)))

  ;;; ============================================================================
  ;;; Audit Entry Creation
  ;;; ============================================================================

  (define (audit-append #!key actor action motivation relates-to signing-key
                              (algorithm 'ed25519) pq-signing-key
                              (auth-chain '()))
    "Append entry to audit trail

     actor: SPKI principal (public key blob)
     action: (verb object . parameters) e.g., (seal-commit \"file.scm\" ...)
     motivation: Human-readable explanation
     relates-to: Related entries or concepts
     signing-key: Private key for signing (blob)
     algorithm: ed25519 (default), ml-dsa-65, sphincs+, hybrid
     pq-signing-key: For hybrid, the ML-DSA private key
     auth-chain: Authorization chain (list of cert references)"

    (unless action
      (error "Action required for audit entry"))

    ;; Get current sequence and parent
    (let* ((sequence (+ 1 (audit-config 'current-sequence)))
           (parent-id (get-latest-entry-id))
           (timestamp (seconds->string (current-seconds)))
           (key (or signing-key (audit-config 'signing-key))))

      (unless key
        (error "No signing key configured"))

      ;; Build entry components
      (let ((actor-obj (make-audit-actor actor auth-chain))
            (action-obj (make-audit-action
                         (car action)
                         (if (pair? (cdr action)) (cadr action) #f)
                         (if (and (pair? (cdr action))
                                  (pair? (cddr action)))
                             (cddr action)
                             '())))
            (context-obj (make-audit-context
                          motivation
                          relates-to
                          "en"))
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
                 (content-hash (sha512-hash content-str))
                 (hash-hex (blob->hex content-hash))
                 (id (string-append "sha512:" (substring hash-hex 0 32)))

                 ;; Sign the content hash (algorithm-aware)
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

                 ;; Create seal with algorithm info
                 (seal-alg-name
                  (case algorithm
                    ((ed25519) "ed25519-sha512")
                    ((ml-dsa-65 ml-dsa) "ml-dsa-65-sha512")
                    ((sphincs+ sphincs+-shake-256s) "sphincs+-sha512")
                    ((hybrid) "hybrid-sha512")
                    (else "unknown")))

                 (seal-obj (make-audit-seal seal-alg-name
                                           content-hash
                                           signature))

                 ;; Complete entry
                 (entry (make-audit-entry-internal
                         id timestamp sequence parent-id
                         actor-obj action-obj context-obj env-obj seal-obj)))

            ;; Save entry
            (save-audit-entry entry)

            ;; Update sequence counter
            (audit-config 'current-sequence sequence)

            (print "Audit entry created: " id)
            entry)))))

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
          (let ((files (sort (directory dir) string<?)))
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
    "Convert S-expression to actor"
    (if (and (pair? sexp) (eq? 'actor (car sexp)))
        (let ((principal (cadr (assq 'principal (cdr sexp))))
              (auth-chain-sexp (assq 'authorization-chain (cdr sexp))))
          (make-audit-actor
           principal
           (if auth-chain-sexp (cdr auth-chain-sexp) '())))
        (make-audit-actor #f '())))

  (define (sexp->action sexp)
    "Convert S-expression to action"
    (if (and (pair? sexp) (eq? 'action (car sexp)))
        (let ((verb (cadr (assq 'verb (cdr sexp))))
              (object (let ((o (assq 'object (cdr sexp))))
                       (if o (cadr o) #f)))
              (params (let ((p (assq 'parameters (cdr sexp))))
                       (if p (cdr p) '()))))
          (make-audit-action verb object params))
        (make-audit-action 'unknown #f '())))

  (define (sexp->context sexp)
    "Convert S-expression to context"
    (if (and (pair? sexp) (eq? 'context (car sexp)))
        (let ((motivation (let ((m (assq 'motivation (cdr sexp))))
                           (if m (cadr m) #f)))
              (relates-to (let ((r (assq 'relates-to (cdr sexp))))
                           (if r (cadr r) #f)))
              (language (cadr (assq 'language (cdr sexp)))))
          (make-audit-context motivation relates-to language))
        (make-audit-context #f #f "en")))

  (define (sexp->seal sexp)
    "Convert S-expression to seal"
    (if (and (pair? sexp) (eq? 'seal (car sexp)))
        (let ((algorithm (cadr (assq 'algorithm (cdr sexp))))
              (value (let ((v (assq 'value (cdr sexp))))
                      (if v (cadr v) #f)))
              (chain (let ((c (assq 'chain (cdr sexp))))
                      (if c (cadr c) #f))))
          (make-audit-seal algorithm value chain))
        (make-audit-seal "ed25519-sha512" #f #f)))

  (define (sexp->entry sexp)
    "Convert S-expression to audit entry"
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

  (define (audit-verify entry #!key public-key pq-public-key)
    "Verify cryptographic seal on audit entry.
     For hybrid seals: provide both public-key (ed25519) and pq-public-key (ml-dsa)"
    (let ((key (or public-key
                   ;; Extract key from actor
                   (actor-principal (entry-actor entry)))))

      (unless key
        (error "No public key for verification"))

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
               (computed-hash (sha512-hash content-str))
               (seal (entry-seal entry))
               (seal-alg (seal-algorithm seal))
               (stored-hash (seal-content-hash seal))
               (signature (seal-signature seal)))

          ;; Verify hash matches
          (if (not (equal? computed-hash stored-hash))
              (begin
                (print "✗ Hash mismatch")
                #f)
              ;; Verify signature based on algorithm
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
                       (print "✗ Unknown seal algorithm: " seal-alg)
                       #f))))
                (if verified
                    (begin
                      (print "✓ Audit entry verified: " (entry-id entry)
                             " (" seal-alg ")")
                      #t)
                    (begin
                      (print "✗ Signature invalid")
                      #f))))))))

  (define (audit-chain #!key verify-key)
    "Verify entire audit chain"
    (let ((dir (audit-config 'audit-dir)))
      (if (directory-exists? dir)
          (let ((files (sort (directory dir) string<?)))
            (for-each
             (lambda (file)
               (let ((entry (read-audit-file (sprintf "~a/~a" dir file))))
                 (when entry
                   (audit-verify entry public-key: verify-key))))
             files))
          (print "No audit trail found"))))

  ;;; ============================================================================
  ;;; Query Interface
  ;;; ============================================================================

  (define (audit-read #!key sequence id)
    "Read specific audit entry"
    (let ((dir (audit-config 'audit-dir)))
      (cond
       (sequence
        (read-audit-file (sprintf "~a/~a.sexp" dir sequence)))
       (id
        ;; Search all audit files for matching ID
        (audit-search-by-id dir id))
       (else
        (error "Must specify sequence or id")))))

  (define (audit-search-by-id dir id)
    "Search audit files for entry with given ID (sha512:... prefix)."
    (let ((files (glob (string-append dir "/*.sexp"))))
      (let loop ((files files))
        (if (null? files)
            #f  ; Not found
            (let ((entry (read-audit-file (car files))))
              (if (and entry
                       (list? entry)
                       (let ((seal (assq 'seal entry)))
                         (and seal
                              (let ((entry-id (assq 'id (cdr seal))))
                                (and entry-id
                                     (string-prefix? id (cadr entry-id)))))))
                  entry
                  (loop (cdr files))))))))

  ;;; ============================================================================
  ;;; Time Parsing (VMS /SINCE and /BEFORE style)
  ;;; ============================================================================

  (define (parse-time-spec spec)
    "Parse time specification to epoch seconds.
     Accepts: '1h' '24h' '7d' '30d' or ISO date 'YYYY-MM-DD' or 'YYYY-MM-DDTHH:MM:SS'"
    (let ((now (current-seconds)))
      (cond
       ;; Relative time: 1h, 24h, 7d, etc.
       ((and (string? spec)
             (irregex-match '(: (submatch (+ digit)) (submatch (or "h" "d" "m" "w"))) spec))
        => (lambda (m)
             (let ((n (string->number (irregex-match-substring m 1)))
                   (unit (irregex-match-substring m 2)))
               (- now (* n (case (string->symbol unit)
                            ((h) 3600)
                            ((d) 86400)
                            ((m) 60)
                            ((w) 604800)
                            (else 3600)))))))
       ;; ISO date: YYYY-MM-DD
       ((and (string? spec)
             (irregex-match '(: (= 4 digit) "-" (= 2 digit) "-" (= 2 digit)) spec))
        (let ((parts (string-split spec "-")))
          (local-time->seconds
           (vector 0 0 0
                   (string->number (caddr parts))   ; day
                   (- (string->number (cadr parts)) 1)  ; month (0-based)
                   (- (string->number (car parts)) 1900) ; year
                   0 0 #f 0))))
       ;; ISO datetime: YYYY-MM-DDTHH:MM:SS
       ((and (string? spec)
             (irregex-match '(: (= 4 digit) "-" (= 2 digit) "-" (= 2 digit)
                               "T" (= 2 digit) ":" (= 2 digit) ":" (= 2 digit)) spec))
        (let* ((date-time (string-split spec "T"))
               (date-parts (string-split (car date-time) "-"))
               (time-parts (string-split (cadr date-time) ":")))
          (local-time->seconds
           (vector (string->number (caddr time-parts))  ; sec
                   (string->number (cadr time-parts))   ; min
                   (string->number (car time-parts))    ; hour
                   (string->number (caddr date-parts))  ; day
                   (- (string->number (cadr date-parts)) 1)  ; month
                   (- (string->number (car date-parts)) 1900) ; year
                   0 0 #f 0))))
       ;; Already a number (epoch)
       ((number? spec) spec)
       ;; Default: 24h ago
       (else (- now 86400)))))

  (define (timestamp->epoch ts)
    "Convert audit timestamp string to epoch seconds."
    (if (and (string? ts)
             (irregex-match '(: (= 4 digit) "-" (= 2 digit) "-" (= 2 digit)
                               "T" (= 2 digit) ":" (= 2 digit) ":" (= 2 digit)) ts))
        (parse-time-spec ts)
        (current-seconds)))  ; fallback

  ;;; ============================================================================
  ;;; Query Engine (VMS ANALYZE/AUDIT /SELECT style)
  ;;; ============================================================================

  (define (audit-all-entries)
    "Load all audit entries from disk."
    (let ((dir (audit-config 'audit-dir)))
      (if (directory-exists? dir)
          (let ((files (sort (filter (lambda (f) (string-suffix? ".sexp" f))
                                     (directory dir))
                             string<?)))
            (filter-map
             (lambda (file)
               (read-audit-file (sprintf "~a/~a" dir file)))
             files))
          '())))

  (define (match-criterion entry criterion)
    "Match single entry against one criterion.
     Criteria: (type sync) (status success) (since '1h') (before '7d') (verb commit)"
    (let ((key (car criterion))
          (val (cadr criterion)))
      (case key
        ;; Action verb matching
        ((type verb action)
         (let ((entry-verb (action-verb (entry-action entry))))
           (cond
            ((symbol? val) (eq? entry-verb val))
            ((string? val) (string=? (symbol->string entry-verb) val))
            (else #f))))

        ;; Object matching (what was acted upon)
        ((object)
         (let ((entry-obj (action-object (entry-action entry))))
           (cond
            ((not entry-obj) #f)
            ((string? val)
             (if (string-suffix? "*" val)
                 (string-prefix? (string-drop-right val 1) entry-obj)
                 (string=? entry-obj val)))
            (else (equal? entry-obj val)))))

        ;; Time range - since
        ((since after)
         (let ((ts (timestamp->epoch (entry-timestamp entry)))
               (threshold (parse-time-spec val)))
           (>= ts threshold)))

        ;; Time range - before
        ((before until)
         (let ((ts (timestamp->epoch (entry-timestamp entry)))
               (threshold (parse-time-spec val)))
           (<= ts threshold)))

        ;; Sequence number
        ((sequence seq)
         (cond
          ((number? val) (= (entry-sequence entry) val))
          ((list? val)  ; range: (100 200)
           (and (>= (entry-sequence entry) (car val))
                (<= (entry-sequence entry) (cadr val))))
          (else #f)))

        ;; Boolean combinators
        ((and)
         (every (lambda (c) (match-criterion entry c)) (cdr criterion)))

        ((or)
         (any (lambda (c) (match-criterion entry c)) (cdr criterion)))

        ((not)
         (not (match-criterion entry (cadr criterion))))

        ;; Default: unknown criterion matches nothing
        (else #f))))

  (define (audit-query entries . criteria)
    "Filter entries by criteria list.
     (audit-query entries '(type sync) '(since \"1h\"))
     (audit-query entries '(and (type sync) (since \"24h\")))"
    (if (null? criteria)
        entries
        (filter
         (lambda (entry)
           (every (lambda (c) (match-criterion entry c)) criteria))
         entries)))

  ;; Legacy query functions (now implemented via audit-query)
  (define (audit-by-actor actor-principal)
    "Find all entries by specific actor"
    (filter
     (lambda (entry)
       (equal? (actor-principal (entry-actor entry)) actor-principal))
     (audit-all-entries)))

  (define (audit-by-action verb)
    "Find all entries for specific action verb"
    (audit-query (audit-all-entries) `(type ,verb)))

  (define (audit-by-timerange start end)
    "Find all entries in time range"
    (audit-query (audit-all-entries)
                 `(since ,start)
                 `(before ,end)))

  ;;; ============================================================================
  ;;; Summary and Aggregation (VMS /SUMMARY style)
  ;;; ============================================================================

  (define (audit-group-by entries field)
    "Group entries by field (type, hour, day).
     Returns alist: ((group-key count entries) ...)"
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
    "Pad string on left to given length."
    (let ((slen (string-length str)))
      (if (>= slen len)
          str
          (string-append (make-string (- len slen) char) str))))

  (define (audit-to-string x)
    "Convert anything to string."
    (cond
     ((string? x) x)
     ((symbol? x) (symbol->string x))
     ((number? x) (number->string x))
     (else (with-output-to-string (lambda () (write x))))))

  (define (audit-summary entries #!optional (by 'type))
    "Print summary of audit entries.
     (audit-summary entries)        - by type
     (audit-summary entries 'hour)  - by hour"
    (let* ((groups (audit-group-by entries by))
           (sorted (sort groups (lambda (a b) (> (cadr a) (cadr b)))))
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
                              (inexact->exact (floor (* 24.0 (/ count max-count))))))
                (bar (make-string bar-width #\█)))
           (printf "  ~a~a ~a  ~a~%"
                   (let ((s (audit-to-string key)))
                     (string-append s (make-string (max 1 (- 12 (string-length s))) #\space)))
                   (audit-pad-left (number->string count) 4 #\space)
                   bar
                   "")))
       sorted)
      (newline)))

  ;;; ============================================================================
  ;;; ASCII Plotting (VMS /GRAPH style)
  ;;; ============================================================================

  ;; Vertical bar characters (eighth blocks for 8 levels)
  (define *vbar-chars* '#("" "▁" "▂" "▃" "▄" "▅" "▆" "▇" "█"))

  (define (audit-histogram buckets width height)
    "Generate ASCII histogram from bucket counts.
     buckets: list of (label . count)
     width: character width
     height: character height"
    (let* ((counts (map cdr buckets))
           (labels (map car buckets))
           (max-count (if (null? counts) 1 (apply max 1 counts)))
           (scale (/ (- height 1.0) max-count)))

      ;; Print from top to bottom
      (let loop ((row (- height 1)))
        (when (>= row 0)
          (let ((threshold (* row (/ max-count (- height 1)))))
            ;; Y-axis label (every other row)
            (if (zero? (modulo row 2))
                (printf "~a │" (audit-pad-left (number->string (inexact->exact (round threshold))) 4 #\space))
                (print "     │"))
            ;; Bar segments
            (for-each
             (lambda (count)
               (let ((bar-height (* count scale)))
                 (display
                  (cond
                   ((> bar-height row) "█")
                   ((> bar-height (- row 1))
                    (let ((frac (- bar-height (floor bar-height))))
                      (vector-ref *vbar-chars*
                                  (inexact->exact (min 8 (floor (* frac 8)))))))
                   (else " ")))))
             counts)
            (newline))
          (loop (- row 1))))

      ;; X-axis
      (printf "   0 └~a~%" (make-string (length buckets) #\─))

      ;; Labels (abbreviated)
      (display "      ")
      (for-each
       (lambda (label)
         (display (if (> (string-length (audit-to-string label)) 2)
                      (substring (audit-to-string label) 0 2)
                      (audit-to-string label))))
       labels)
      (newline)))

  (define (audit-plot entries #!key
                     (bucket "1h")
                     (span "24h")
                     (width 24)
                     (height 8))
    "Plot audit activity as ASCII histogram.
     (audit-plot entries)
     (audit-plot entries bucket: \"1h\" span: \"24h\")"
    (let* ((now (current-seconds))
           (span-secs (- now (parse-time-spec span)))
           (bucket-secs (case (string->symbol (string-take-right bucket 1))
                         ((h) (* (string->number (string-drop-right bucket 1)) 3600))
                         ((d) (* (string->number (string-drop-right bucket 1)) 86400))
                         ((m) (* (string->number (string-drop-right bucket 1)) 60))
                         (else 3600)))
           (num-buckets (max 1 (quotient span-secs bucket-secs)))
           (bucket-counts (make-vector num-buckets 0))
           (start-time (- now span-secs)))

      ;; Count entries per bucket
      (for-each
       (lambda (entry)
         (let* ((ts (timestamp->epoch (entry-timestamp entry)))
                (age (- now ts)))
           (when (and (>= ts start-time) (< ts now))
             (let ((bucket-idx (min (- num-buckets 1)
                                   (max 0 (quotient (- ts start-time) bucket-secs)))))
               (vector-set! bucket-counts bucket-idx
                           (+ 1 (vector-ref bucket-counts bucket-idx)))))))
       entries)

      ;; Build bucket list with labels
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

  (define (audit-export-sexp #!key output)
    "Export entire audit trail as S-expressions"
    (let ((dir (audit-config 'audit-dir))
          (out (or output "audit-export.sexp")))
      (with-output-to-file out
        (lambda ()
          (print "(audit-trail")
          (let ((files (sort (directory dir) string<?)))
            (for-each
             (lambda (file)
               (let ((entry (read-audit-file (sprintf "~a/~a" dir file))))
                 (when entry
                   (write (entry->sexp entry))
                   (newline))))
             files))
          (print ")")))))

  (define (audit-export-human #!key output)
    "Export audit trail in human-readable format"
    (let ((dir (audit-config 'audit-dir))
          (out (or output "audit-export.txt")))
      (with-output-to-file out
        (lambda ()
          (print "Audit Trail - Library of Cyberspace")
          (print "===================================")
          (print "")
          (let ((files (sort (directory dir) string<?)))
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
          (u8vector->list (blob->u8vector blob)))))

  (define (get-environment-snapshot)
    "Capture current environment"
    `((platform ,(or (get-environment-variable "OSTYPE") "unknown"))
      (timestamp ,(current-seconds))))

  ) ;; end module audit
