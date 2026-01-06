;;; audit.scm - Cryptographic Audit Trail for Library of Cyberspace
;;;
;;; Future-proof audit encoding with:
;;; - Content-addressed entries (tamper-evident)
;;; - Chained structure (append-only log)
;;; - SPKI authorization (who had permission)
;;; - Dual context (human + machine readable)
;;; - Cryptographic seals (Ed25519 signatures)

(module audit
  (;; Core operations
   audit-init
   audit-append
   audit-verify
   audit-read
   audit-chain

   ;; Query interface
   audit-by-actor
   audit-by-action
   audit-by-timerange

   ;; Export formats
   audit-export-sexp
   audit-export-human)

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
          srfi-1   ; list utilities
          srfi-4   ; u8vectors
          srfi-13  ; string utilities
          crypto-ffi)

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

  (define (audit-append #!key actor action motivation relates-to signing-key)
    "Append entry to audit trail

     actor: SPKI principal (public key blob)
     action: (verb object . parameters) e.g., (seal-commit \"file.scm\" ...)
     motivation: Human-readable explanation
     relates-to: Related entries or concepts
     signing-key: Private key for signing (blob)"

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
      (let ((actor-obj (make-audit-actor actor '()))  ; TODO: auth chain
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

                 ;; Sign the content hash
                 (signature (ed25519-sign key content-hash))

                 ;; Create seal
                 (seal-obj (make-audit-seal "ed25519-sha512"
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

  (define (sexp->entry sexp)
    "Convert S-expression to audit entry"
    ;; Simplified - full implementation would parse all fields
    (if (and (pair? sexp) (eq? 'audit-entry (car sexp)))
        (let ((id (cadr (assq 'id (cdr sexp))))
              (timestamp (cadr (assq 'timestamp (cdr sexp))))
              (sequence (cadr (assq 'sequence (cdr sexp))))
              (parent-id (let ((p (assq 'parent-id (cdr sexp))))
                          (if p (cadr p) #f))))
          ;; Return simplified entry - full parser would reconstruct all fields
          (make-audit-entry-internal id timestamp sequence parent-id
                                    (make-audit-actor #f '())
                                    (make-audit-action 'unknown #f '())
                                    (make-audit-context #f #f "en")
                                    '()
                                    (make-audit-seal "ed25519-sha512" #f #f)))
        #f))

  ;;; ============================================================================
  ;;; Verification
  ;;; ============================================================================

  (define (audit-verify entry #!key public-key)
    "Verify cryptographic seal on audit entry"
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
               (stored-hash (seal-content-hash seal))
               (signature (seal-signature seal)))

          ;; Verify hash matches
          (if (not (equal? computed-hash stored-hash))
              (begin
                (print "✗ Hash mismatch")
                #f)
              ;; Verify signature
              (if (ed25519-verify key computed-hash signature)
                  (begin
                    (print "✓ Audit entry verified: " (entry-id entry))
                    #t)
                  (begin
                    (print "✗ Signature invalid")
                    #f)))))))

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
        ;; TODO: Search by ID
        (error "Search by ID not yet implemented"))
       (else
        (error "Must specify sequence or id")))))

  (define (audit-by-actor actor-principal)
    "Find all entries by specific actor"
    ;; TODO: Implement
    '())

  (define (audit-by-action verb)
    "Find all entries for specific action verb"
    ;; TODO: Implement
    '())

  (define (audit-by-timerange start end)
    "Find all entries in time range"
    ;; TODO: Implement
    '())

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
          (print "AUDIT TRAIL - Library of Cyberspace")
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
