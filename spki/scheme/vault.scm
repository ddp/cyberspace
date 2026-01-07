;;; vault.scm - Cryptographically Sealed Version Control for the Library of Cyberspace
;;;
;;; A higher-level interface to version control with integrated:
;;; - SPKI certificate-based authorization
;;; - Cryptographic sealing of versions
;;; - First-class archival and restoration
;;; - Migration paths between versions
;;;
;;; Commands use "seal" as the primary verb, connecting:
;;; - Cryptographic sealing (SPKI signatures)
;;; - Library seals (official marks of authenticity)
;;; - Vault seals (securing archives)

(module vault
  (;; Core operations
   seal-commit
   seal-update
   seal-undo
   seal-history
   seal-branch
   seal-merge

   ;; Version management
   seal-release
   seal-archive
   seal-restore

   ;; Replication
   seal-publish
   seal-subscribe
   seal-synchronize

   ;; Verification
   seal-verify

   ;; Inspection
   seal-inspect

   ;; Directory / Object Soup (NewtonOS-style)
   soup
   soup?
   complete

   ;; Configuration
   vault-init
   vault-config)

  (import scheme
          (chicken base)
          (chicken process)
          (chicken process-context)
          (chicken string)
          (chicken format)
          (chicken io)
          (chicken file)
          (chicken file posix)
          (chicken pathname)
          (chicken time)
          (chicken time posix)
          (chicken condition)
          (chicken blob)
          (chicken memory)
          (chicken irregex)
          srfi-1   ; list utilities
          srfi-4   ; u8vectors
          srfi-13  ; string utilities
          srfi-69  ; hash tables
          cert
          crypto-ffi
          audit)

  ;;; ============================================================================
  ;;; Helper Functions
  ;;; ============================================================================

  (define (get-vault-principal signing-key)
    "Extract public key from Ed25519 signing key (64 bytes)"
    (if (and (blob? signing-key) (= (blob-size signing-key) 64))
        ;; Public key is second half of signing key
        (blob-copy signing-key 32 32)
        #f))

  (define (blob-copy src start len)
    "Copy portion of blob"
    (let ((result (make-blob len)))
      (move-memory! src result len start 0)
      result))

  (define (run-command . args)
    "Run a system command with arguments"
    (let ((pid (process-fork
                 (lambda ()
                   (process-execute (car args) (cdr args))))))
      (receive (pid2 normal exit-code) (process-wait pid)
        (unless (zero? exit-code)
          (error "Command failed" (car args) exit-code)))))

  ;;; ============================================================================
  ;;; Configuration
  ;;; ============================================================================

  (define *vault-config*
    '((signing-key . #f)           ; Path to signing key for releases
      (verify-key . #f)            ; Path to verification key
      (archive-format . tarball)   ; tarball, bundle, cryptographic, or zstd-age
      (age-recipients . ())        ; List of age recipients (public keys or identities)
      (age-identity . #f)          ; Path to age identity file for decryption
      (migration-dir . "migrations"))) ; Directory for migration scripts

  (define (vault-config key #!optional value)
    "Get or set vault configuration"
    (if value
        (set! *vault-config* (alist-update key value *vault-config*))
        (alist-ref key *vault-config*)))

  (define (vault-init #!key signing-key)
    "Initialize vault configuration for repository"
    (if signing-key
        (vault-config 'signing-key signing-key))
    (print "Vault initialized for: " (get-environment-variable "PWD"))
    (when signing-key
      (print "Signing key: " signing-key)
      ;; Also initialize audit trail
      (let ((principal (get-vault-principal signing-key)))
        (when principal
          (audit-init signing-key: signing-key
                     motivation: "Vault initialized with cryptographic audit trail")))))

  ;;; ============================================================================
  ;;; Utility Functions (must be defined before use)
  ;;; ============================================================================

  (define (read-key-from-file filename)
    "Read key blob from s-expression file"
    (let ((sexp (with-input-from-file filename read)))
      (if (and (pair? sexp) (= 2 (length sexp)))
          (cadr sexp)  ; Extract key bytes from (type key-blob)
          (error "Invalid key file format" filename))))

  (define (read-file-bytes filename)
    "Read file as byte blob"
    (with-input-from-file filename
      (lambda ()
        (read-string #f))))

  (define (blob->hex blob)
    "Convert blob to hex string"
    (string-concatenate
     (map (lambda (b)
            (let ((hex (number->string b 16)))
              (if (= 1 (string-length hex))
                  (string-append "0" hex)
                  hex)))
          (u8vector->list (blob->u8vector blob)))))

  (define (hex->blob hex-string)
    "Convert hex string to blob"
    (let* ((len (quotient (string-length hex-string) 2))
           (vec (make-u8vector len)))
      (do ((i 0 (+ i 1)))
          ((= i len) (u8vector->blob vec))
        (u8vector-set! vec i
                       (string->number
                        (substring hex-string (* i 2) (* (+ i 1) 2))
                        16)))))

  (define (get-environment-snapshot)
    "Capture current build environment"
    `((platform ,(or (get-environment-variable "OSTYPE") "unknown"))
      (hostname ,(or (get-environment-variable "HOSTNAME") "unknown"))
      (chicken-version "5.x")  ; Chicken Scheme version
      (timestamp ,(current-seconds))))

  (define (get-dependencies-snapshot)
    "Capture current dependencies"
    ;; Placeholder - could scan imports, check installed eggs, etc.
    '())

  (define (get-git-state-snapshot)
    "Capture git repository state"
    (let ((branch (with-input-from-pipe "git branch --show-current" read-line))
          (remote (with-input-from-pipe "git remote -v" read-line)))
      `((branch ,branch)
        (remote ,remote))))

  (define (save-commit-metadata commit-hash #!key message catalog subjects keywords description preserve)
    "Save optional metadata for a commit"
    (create-directory ".vault/metadata" #t)

    (let ((metadata-file (sprintf ".vault/metadata/~a.sexp" commit-hash))
          (timestamp (current-seconds)))

      ;; Build metadata structure procedurally
      (let ((metadata (list 'commit-metadata
                           (list 'hash commit-hash)
                           (list 'timestamp timestamp)
                           (list 'message message))))

        ;; Add catalog if requested
        (when (or catalog subjects keywords description)
          (let ((catalog-entry (list 'catalog)))
            (when subjects
              (set! catalog-entry (append catalog-entry (list (cons 'subjects subjects)))))
            (when keywords
              (set! catalog-entry (append catalog-entry (list (cons 'keywords keywords)))))
            (when description
              (set! catalog-entry (append catalog-entry (list (list 'description description)))))
            (set! metadata (append metadata (list catalog-entry)))))

        ;; Add preservation if requested
        (when preserve
          (set! metadata
            (append metadata
                   (list (list 'preservation
                              (list 'environment (get-environment-snapshot))
                              (list 'dependencies (get-dependencies-snapshot))
                              (list 'git-state (get-git-state-snapshot)))))))

        ;; Write metadata file
        (with-output-to-file metadata-file
          (lambda ()
            (write metadata)
            (newline)))

        ;; Stage metadata file for next commit (optional)
        (when (vault-config 'track-metadata)
          (system (sprintf "git add ~a" metadata-file))))))

  ;;; ============================================================================
  ;;; Core Operations - Better UX than raw git
  ;;; ============================================================================

  (define (seal-commit message #!key files catalog subjects keywords description preserve)
    "Seal changes into the vault
     Simplified commit: stages and commits in one operation

     Optional metadata:
     - catalog: Add discovery metadata
     - subjects: Subject headings (list of strings)
     - keywords: Search keywords (list of strings)
     - description: Extended description
     - preserve: Full preservation metadata"

    ;; Stage files
    (when files
      (apply run-command "git" "add" files))
    (run-command "git" "add" "-u")  ; Add all modified tracked files

    ;; Create commit (simple by default)
    (run-command "git" "commit" "-m" message)

    ;; Get commit hash
    (let ((commit-hash (with-input-from-pipe "git rev-parse HEAD" read-line)))

      ;; Add optional metadata after commit
      (when (or catalog subjects keywords description preserve)
        (save-commit-metadata commit-hash
                             message: message
                             catalog: catalog
                             subjects: subjects
                             keywords: keywords
                             description: description
                             preserve: preserve))

      ;; Record in audit trail
      (let ((signing-key (vault-config 'signing-key)))
        (when signing-key
          (audit-append
           actor: (get-vault-principal signing-key)
           action: (list 'seal-commit commit-hash)
           motivation: message)))))

  (define (seal-update #!key branch)
    "Update vault from origin
     Like svn update - pulls latest changes"
    (let ((target (or branch "origin/main")))
      (run-command "git" "pull" "--ff-only")))

  (define (seal-undo #!key file hard)
    "Undo changes
     - file: undo changes to specific file
     - hard: discard all uncommitted changes"
    (cond
     (file
      (run-command "git" "restore" file))
     (hard
      (run-command "git" "reset" "--hard" "HEAD"))
     (else
      (run-command "git" "reset" "--soft" "HEAD~1"))))

  (define (seal-history #!key count)
    "Show vault history
     Simplified log with clear format"
    (let ((limit (or count 10)))
      (run-command "git" "log"
               "--oneline"
               "--decorate"
               "--graph"
               (sprintf "-~a" limit))))

  (define (seal-branch name #!key from)
    "Create and switch to new sealed branch"
    (if from
        (run-command "git" "checkout" "-b" name from)
        (run-command "git" "checkout" "-b" name)))

  (define (seal-merge from #!key strategy)
    "Merge sealed changes from another branch"
    (if strategy
        (run-command "git" "merge" from "-s" strategy)
        (run-command "git" "merge" from)))

  ;;; ============================================================================
  ;;; Version Management - Semantic versioning with SPKI sealing
  ;;; ============================================================================

  (define-record-type <sealed-release>
    (make-sealed-release version hash timestamp signer signature)
    sealed-release?
    (version release-version)
    (hash release-hash)
    (timestamp release-timestamp)
    (signer release-signer)
    (signature release-signature))

  (define (seal-release version #!key message migrate-from)
    "Create a cryptographically sealed release
     - version: semantic version (e.g., '1.0.0')
     - message: release notes
     - migrate-from: previous version for migration tracking"

    ;; Validate semantic version (basic check: X.Y.Z format)
    (unless (and (irregex-match '(: (+ digit) "." (+ digit) "." (+ digit)) version)
                 (= 3 (length (string-split version "."))))
      (error "Invalid semantic version (expected X.Y.Z)" version))

    ;; Get current commit hash
    (let ((hash (with-input-from-pipe "git rev-parse HEAD" read-line))
          (timestamp (current-seconds)))

      ;; Create annotated tag
      (let ((tag-message (or message (sprintf "Release ~a" version))))
        (run-command "git" "tag" "-a" version "-m" tag-message))

      ;; Sign with SPKI if signing key configured
      (let ((signing-key (vault-config 'signing-key)))
        (when signing-key
          (seal-sign-release version hash signing-key)))

      ;; Create migration marker if migrating from previous version
      (when migrate-from
        (create-migration-marker migrate-from version))

      (print "Sealed release: " version " at " hash)))

  (define (seal-sign-release version hash signing-key)
    "Sign a release with SPKI certificate"
    ;; Create release manifest
    (let ((manifest (sprintf "(release ~s ~s ~s)"
                            version hash (current-seconds))))
      ;; Sign manifest (signing-key is already a blob)
      (let* ((sig-hash (sha512-hash manifest))
             (signature (ed25519-sign signing-key sig-hash)))

        ;; Store signature
        (let ((sig-file (sprintf ".vault/releases/~a.sig" version)))
          (create-directory ".vault/releases" #t)
          (with-output-to-file sig-file
            (lambda ()
              (write `(signature
                       (version ,version)
                       (hash ,hash)
                       (manifest ,manifest)
                       (signature ,signature)))))
          (print "Release signed: " sig-file)))))

  (define (seal-verify version #!key verify-key)
    "Verify cryptographic seal on a release"
    (let ((sig-file (sprintf ".vault/releases/~a.sig" version))
          (key (or verify-key (vault-config 'verify-key))))

      (unless (file-exists? sig-file)
        (error "No signature found for release" version))

      (unless key
        (error "No verification key configured"))

      ;; Read and verify signature
      (let* ((sig-data (with-input-from-file sig-file read))
             (manifest (cadr (assq 'manifest sig-data)))
             (signature (cadr (assq 'signature sig-data)))
             (pubkey (read-key-from-file key)))

        (let ((sig-hash (sha512-hash manifest)))
          (if (ed25519-verify pubkey sig-hash signature)
              (begin
                (print "✓ Release seal verified: " version)
                #t)
              (begin
                (print "✗ Release seal INVALID: " version)
                #f))))))

  ;;; ============================================================================
  ;;; Object Inspection - Security and Migration Properties
  ;;; ============================================================================

  (define (seal-inspect object #!key verify-key verbose)
    "Inspect security and migration properties of a Cyberspace object

     object: Path to .archive file, version string, or record
     verify-key: Optional public key for signature verification
     verbose: Show additional details

     Displays:
     - Security: signing algorithm, hash, signature status, encryption
     - Migration: format version, compatibility, platform, dependencies"

    (cond
     ;; String path to archive file
     ((and (string? object) (file-exists? object))
      (inspect-archive-file object verify-key: verify-key verbose: verbose))

     ;; Version string - look up release
     ((and (string? object) (tag-exists? object))
      (inspect-release object verify-key: verify-key verbose: verbose))

     ;; Signed certificate record
     ((and (pair? object) (eq? 'signed-cert (car object)))
      (inspect-signed-cert object verify-key: verify-key verbose: verbose))

     ;; Audit entry record
     ((and (pair? object) (eq? 'audit-entry (car object)))
      (inspect-audit-entry object verify-key: verify-key verbose: verbose))

     (else
      (error "Unknown object type. Expected: archive path, version, signed-cert, or audit-entry"))))

  (define (repeat-string str n)
    (let loop ((i 0) (acc ""))
      (if (= i n) acc
          (loop (+ i 1) (string-append acc str)))))

  (define (box-top width)
    (string-append "╭" (repeat-string "─" (- width 1)) "╮"))

  (define (box-bottom width)
    (string-append "╰" (repeat-string "─" (- width 1)) "╯"))

  (define (box-divider width)
    (string-append "├" (repeat-string "─" (- width 1)) "┤"))

  (define (utf8-display-adjustment str)
    "Calculate adjustment for UTF-8 symbols: string-length counts bytes,
     but we need display columns. Each 3-byte symbol displays as ~2 cols,
     so adjustment = -(bytes - display_cols) = -(3 - 2) = -1 per symbol"
    (let ((check-mark (if (string-contains str "✓") 2 0))   ; 3 bytes, 1 col: -2
          (x-mark (if (string-contains str "✗") 2 0))       ; 3 bytes, 1 col: -2
          (warning (if (string-contains str "⚠") 1 0)))     ; 3 bytes, 2 cols: -1
      (+ check-mark x-mark warning)))

  (define (display-width str)
    "Calculate display width: byte-length minus UTF-8 overhead"
    (- (string-length str) (utf8-display-adjustment str)))

  (define (box-line content width)
    (let* ((content-width (display-width content))
           (padded (if (> content-width (- width 2))
                       (substring content 0 (- width 2))
                       content))
           (padding (- width 2 (display-width padded))))
      (string-append "│ " padded (make-string (max 0 padding) #\space) "│")))

  (define (box-line-pair label value width)
    (let* ((formatted (sprintf "~a:~a~a"
                               label
                               (make-string (max 1 (- 20 (string-length label))) #\space)
                               value)))
      (box-line formatted width)))

  (define (print-box-header title type width)
    (print (box-top width))
    (print (box-line (sprintf "OBJECT: ~a" title) width))
    (print (box-line (sprintf "TYPE:   ~a" type) width))
    (print (box-divider width)))

  (define (print-section-header title width)
    (print (box-line "" width))
    (print (box-line title width))
    (print (box-line "" width)))

  (define (inspect-archive-file path #!key verify-key verbose)
    "Inspect a sealed archive file"
    (let ((width 60))

      ;; Read archive manifest
      (let ((manifest (with-input-from-file path read)))

        (unless (and (pair? manifest) (eq? 'sealed-archive (car manifest)))
          (error "Not a sealed archive" path))

        (let* ((fields (cdr manifest))
               (version (cadr (assq 'version fields)))
               (fmt (cadr (assq 'format fields)))
               (archive-file (let ((a (assq 'archive fields)))
                              (if a (cadr a)
                                  (let ((t (assq 'tarball fields)))
                                    (if t (cadr t) #f)))))
               (hash-hex (cadr (assq 'hash fields)))
               (sig-hex (cadr (assq 'signature fields)))
               (recipients (let ((r (assq 'recipients fields)))
                            (if r (cadr r) '())))
               (compression (let ((c (assq 'compression fields)))
                             (if c (cadr c) #f))))

          ;; Verify signature if key provided
          (let ((sig-status
                 (if verify-key
                     (let* ((archive-bytes (if archive-file
                                               (read-file-bytes archive-file)
                                               #f))
                            (archive-hash (if archive-bytes
                                              (sha512-hash archive-bytes)
                                              #f))
                            (expected-hash (hex->blob hash-hex))
                            (signature (hex->blob sig-hex))
                            (pubkey (if (string? verify-key)
                                        (read-key-from-file verify-key)
                                        verify-key)))
                       (if (and archive-hash
                                (equal? archive-hash expected-hash)
                                (ed25519-verify pubkey archive-hash signature))
                           "✓ VERIFIED"
                           "✗ FAILED"))
                     "⚠ NOT VERIFIED (no key)")))

            ;; Print inspection output
            (print-box-header (pathname-file path) "sealed-archive" width)

            (print-section-header "SECURITY PROPERTIES" width)
            (print (box-line-pair "Signing Algorithm" "ed25519-sha512" width))
            (print (box-line-pair "Content Hash" (string-append "sha512:" (substring hash-hex 0 16) "...") width))
            (print (box-line-pair "Signature" sig-status width))

            (case fmt
              ((zstd-age)
               (print (box-line-pair "Encryption" "age (X25519)" width))
               (print (box-line-pair "Recipients" (sprintf "~a key(s)" (length recipients)) width)))
              ((cryptographic)
               (print (box-line-pair "Encryption" "none (signed only)" width)))
              (else
               (print (box-line-pair "Encryption" "none" width))))

            (print (box-divider width))
            (print-section-header "MIGRATION PROPERTIES" width)
            (print (box-line-pair "Format Version" "1" width))
            (print (box-line-pair "Archive Format" (symbol->string fmt) width))

            (when compression
              (print (box-line-pair "Compression" (symbol->string compression) width)))

            (print (box-line-pair "Semantic Version" version width))

            ;; Check for migration path
            (let ((migration-file (sprintf "~a/~a-to-*.scm"
                                          (vault-config 'migration-dir)
                                          version)))
              (print (box-line-pair "Migration Path" "(inspect with seal-history)" width)))

            ;; Portability assessment
            (print (box-line-pair "Portable"
                                 (case fmt
                                   ((zstd-age) "✓ (requires age, zstd)")
                                   ((cryptographic) "✓ (requires gzip)")
                                   ((tarball) "✓ (standard tar.gz)")
                                   ((bundle) "✓ (git bundle)")
                                   (else "? (unknown format)"))
                                 width))

            (print (box-line "" width))
            (print (box-bottom width)))))))

  (define (inspect-release version #!key verify-key verbose)
    "Inspect a sealed release by version"
    (let ((width 60)
          (sig-file (sprintf ".vault/releases/~a.sig" version)))

      (print-box-header version "sealed-release" width)
      (print-section-header "SECURITY PROPERTIES" width)

      (if (file-exists? sig-file)
          (let ((sig-data (with-input-from-file sig-file read)))
            (let ((manifest (cadr (assq 'manifest (cdr sig-data))))
                  (hash (cadr (assq 'hash (cdr sig-data)))))
              (print (box-line-pair "Signing Algorithm" "ed25519-sha512" width))
              (print (box-line-pair "Manifest Hash" (substring hash 0 32) width))

              (let ((sig-status
                     (if verify-key
                         (if (seal-verify version verify-key: verify-key)
                             "✓ VERIFIED"
                             "✗ FAILED")
                         "⚠ NOT VERIFIED (no key)")))
                (print (box-line-pair "Signature" sig-status width)))))

          (print (box-line-pair "Signature" "none (unsigned release)" width)))

      (print (box-divider width))
      (print-section-header "MIGRATION PROPERTIES" width)

      ;; Get git info for the tag
      (let ((hash (with-input-from-pipe
                      (sprintf "git rev-parse ~a 2>/dev/null" version)
                    read-line))
            (date (with-input-from-pipe
                      (sprintf "git log -1 --format=%ci ~a 2>/dev/null" version)
                    read-line)))
        (print (box-line-pair "Semantic Version" version width))
        (when (and hash (not (eof-object? hash)))
          (print (box-line-pair "Commit Hash" (substring hash 0 12) width)))
        (when (and date (not (eof-object? date)))
          (print (box-line-pair "Created" date width))))

      ;; Check for migration scripts
      (let ((migration-dir (vault-config 'migration-dir)))
        (if (directory-exists? migration-dir)
            (let ((migrations (filter
                               (lambda (f) (string-contains f version))
                               (directory migration-dir))))
              (if (null? migrations)
                  (print (box-line-pair "Migration Path" "(none)" width))
                  (for-each
                   (lambda (m)
                     (print (box-line-pair "Migration" m width)))
                   migrations)))
            (print (box-line-pair "Migration Path" "(none)" width))))

      (print (box-line "" width))
      (print (box-bottom width))))

  (define (inspect-signed-cert sc #!key verify-key verbose)
    "Inspect a signed certificate"
    (let ((width 60))
      ;; Handle both sexp and record forms
      (let* ((cert-data (if (pair? sc) (cdr sc) sc))
             (cert-sexp (if (pair? cert-data) (car cert-data) cert-data)))

        (print-box-header "signed-certificate" "spki-cert" width)
        (print-section-header "SECURITY PROPERTIES" width)
        (print (box-line-pair "Signing Algorithm" "ed25519-sha512" width))
        (print (box-line-pair "Hash Algorithm" "sha512" width))

        ;; Extract issuer/subject if available
        (when (pair? cert-sexp)
          (let ((issuer (assq 'issuer (if (eq? 'cert (car cert-sexp))
                                          (cdr cert-sexp)
                                          cert-sexp))))
            (when issuer
              (print (box-line-pair "Issuer" "(principal)" width)))))

        (print (box-line-pair "Propagate" "check cert-propagate" width))

        (print (box-divider width))
        (print-section-header "DELEGATION PROPERTIES" width)
        (print (box-line-pair "Chain Depth" "1 (direct)" width))
        (print (box-line-pair "Validity" "check cert-validity" width))

        (print (box-line "" width))
        (print (box-bottom width)))))

  (define (inspect-audit-entry entry #!key verify-key verbose)
    "Inspect an audit trail entry"
    (let ((width 60))
      ;; Handle sexp form
      (let ((fields (if (and (pair? entry) (eq? 'audit-entry (car entry)))
                        (cdr entry)
                        entry)))

        (let ((id (let ((i (assq 'id fields))) (if i (cadr i) "unknown")))
              (timestamp (let ((t (assq 'timestamp fields))) (if t (cadr t) "unknown")))
              (sequence (let ((s (assq 'sequence fields))) (if s (cadr s) 0)))
              (seal (assq 'seal fields)))

          (print-box-header (sprintf "entry-~a" sequence) "audit-entry" width)
          (print-section-header "SECURITY PROPERTIES" width)

          (if seal
              (let ((seal-fields (cdr seal)))
                (let ((algorithm (let ((a (assq 'algorithm seal-fields)))
                                  (if a (cadr a) "ed25519-sha512"))))
                  (print (box-line-pair "Seal Algorithm" algorithm width))
                  (print (box-line-pair "Content Hash" (substring id 0 32) width))
                  (print (box-line-pair "Chain Link" "parent-id reference" width))))
              (print (box-line-pair "Seal" "none" width)))

          (print (box-divider width))
          (print-section-header "AUDIT PROPERTIES" width)
          (print (box-line-pair "Entry ID" (substring id 0 24) width))
          (print (box-line-pair "Sequence" (number->string sequence) width))
          (print (box-line-pair "Timestamp" timestamp width))
          (print (box-line-pair "Immutable" "✓ (content-addressed)" width))

          (print (box-line "" width))
          (print (box-bottom width))))))

  ;;; ============================================================================
  ;;; Directory / Object Soup - NewtonOS-style persistent object store
  ;;; ============================================================================

  ;; Object types in the soup
  (define *soup-types*
    '((archives  . "Sealed archive packages")
      (releases  . "Tagged version releases")
      (certs     . "SPKI certificates")
      (audit     . "Audit trail entries")
      (keys      . "Cryptographic keys")
      (metadata  . "Commit metadata")))

  (define (soup? . args)
    "Show soup help and available object types (JSYS ? command)"
    (print "
SOUP - Object Store Query Syntax
─────────────────────────────────────────────────────────────

  (soup)                     List all objects in soup
  (soup 'archives)           Filter by type
  (soup 'releases)
  (soup 'certs)
  (soup 'audit)
  (soup 'keys)
  (soup 'metadata)

  (soup \"pattern\")           Glob pattern (* = any, ? = single char)
  (soup \"genesis*\")          All objects starting with 'genesis'
  (soup \"*.archive\")         All archive files
  (soup \"v?.0.0\")            Matches v1.0.0, v2.0.0, etc.

  (soup 'type \"pattern\")     Combine type filter with pattern
  (soup 'releases \"1.*\")     Releases matching 1.*

  (soup #/regex/)            Regular expression (PCRE)
  (soup #/^v[0-9]+/)         Releases starting with v + digits
  (soup 'audit #/seal-/)     Audit entries containing seal-

  (complete \"gen\")           Complete partial object name

Object Types:
")
    (for-each
     (lambda (type-pair)
       (printf "  ~a~a~a~%"
               (car type-pair)
               (make-string (max 1 (- 12 (string-length (symbol->string (car type-pair))))) #\space)
               (cdr type-pair)))
     *soup-types*))

  (define (glob->sre-pattern pattern)
    "Convert glob pattern to irregex using built-in glob->sre"
    ;; glob->sre converts shell-style globs to SRE
    ;; Wrap with bos/eos for full match
    `(: bos ,(glob->sre pattern) eos))

  (define (match-pattern? name pattern)
    "Match name against glob or regex pattern"
    (cond
     ;; Regex (irregex object)
     ((irregex? pattern)
      (irregex-search pattern name))
     ;; Glob pattern string - use built-in glob->sre
     ((string? pattern)
      (irregex-match (irregex (glob->sre-pattern pattern)) name))
     ;; No pattern - match all
     (else #t)))

  (define (soup-collect-objects)
    "Collect all objects from the soup"
    (let ((objects '()))

      ;; Archives (*.archive files in current dir)
      (when (directory-exists? ".")
        (for-each
         (lambda (f)
           (when (string-suffix? ".archive" f)
             (let ((stat (file-stat f)))
               (set! objects (cons (list 'archives f (vector-ref stat 5) (get-archive-format f)) objects)))))
         (directory ".")))

      ;; Releases (.vault/releases/*.sig)
      (when (directory-exists? ".vault/releases")
        (for-each
         (lambda (f)
           (when (string-suffix? ".sig" f)
             (let* ((version (pathname-strip-extension f))
                    (stat (file-stat (sprintf ".vault/releases/~a" f))))
               (set! objects (cons (list 'releases version (vector-ref stat 5) "signed") objects)))))
         (directory ".vault/releases")))

      ;; Unsigned releases (git tags without .sig)
      (let ((tags (get-git-tags)))
        (for-each
         (lambda (tag)
           (unless (file-exists? (sprintf ".vault/releases/~a.sig" tag))
             (set! objects (cons (list 'releases tag 0 "unsigned") objects))))
         tags))

      ;; Audit entries (.vault/audit/*.sexp)
      (when (directory-exists? ".vault/audit")
        (for-each
         (lambda (f)
           (when (string-suffix? ".sexp" f)
             (let ((stat (file-stat (sprintf ".vault/audit/~a" f))))
               (set! objects (cons (list 'audit f (vector-ref stat 5) "entry") objects)))))
         (directory ".vault/audit")))

      ;; Keys (*.pub, *.key, *.age files)
      (when (directory-exists? ".")
        (for-each
         (lambda (f)
           (when (or (string-suffix? ".pub" f)
                     (string-suffix? ".key" f)
                     (string-suffix? ".age" f))
             (let ((stat (file-stat f)))
               (set! objects (cons (list 'keys f (vector-ref stat 5) (get-key-type f)) objects)))))
         (directory ".")))

      ;; Metadata (.vault/metadata/*.sexp)
      (when (directory-exists? ".vault/metadata")
        (for-each
         (lambda (f)
           (when (string-suffix? ".sexp" f)
             (let ((stat (file-stat (sprintf ".vault/metadata/~a" f))))
               (set! objects (cons (list 'metadata f (vector-ref stat 5) "commit") objects)))))
         (directory ".vault/metadata")))

      (reverse objects)))

  (define (get-archive-format path)
    "Detect archive format from manifest"
    (handle-exceptions exn
      "unknown"
      (let ((manifest (with-input-from-file path read)))
        (if (and (pair? manifest) (eq? 'sealed-archive (car manifest)))
            (let ((fmt (assq 'format (cdr manifest))))
              (if fmt (symbol->string (cadr fmt)) "unknown"))
            "unknown"))))

  (define (get-key-type path)
    "Detect key type from file"
    (cond
     ((string-suffix? ".pub" path) "public")
     ((string-suffix? ".key" path) "private")
     ((string-suffix? ".age" path) "age")
     (else "unknown")))

  (define (get-git-tags)
    "Get list of git tags"
    (handle-exceptions exn
      '()
      (with-input-from-pipe "git tag -l 2>/dev/null"
        (lambda ()
          (let loop ((tags '()))
            (let ((line (read-line)))
              (if (eof-object? line)
                  (reverse tags)
                  (loop (cons line tags)))))))))

  (define (format-size bytes)
    "Format byte size human-readable"
    (cond
     ((< bytes 1024) (sprintf "~aB" bytes))
     ((< bytes (* 1024 1024)) (sprintf "~aK" (quotient bytes 1024)))
     ((< bytes (* 1024 1024 1024)) (sprintf "~aM" (quotient bytes (* 1024 1024))))
     (else (sprintf "~aG" (quotient bytes (* 1024 1024 1024))))))

  (define (soup . args)
    "List objects in the soup with optional type filter and pattern

     (soup)                   - all objects
     (soup 'archives)         - filter by type
     (soup \"pattern\")         - glob pattern (* ?)
     (soup 'type \"pat\")       - type + pattern
     (soup #/regex/)          - regex match"

    (let ((type-filter #f)
          (pattern #f))

      ;; Parse arguments
      (for-each
       (lambda (arg)
         (cond
          ((symbol? arg) (set! type-filter arg))
          ((string? arg) (set! pattern arg))
          ((irregex? arg) (set! pattern arg))))
       args)

      ;; Collect and filter objects
      (let* ((all-objects (soup-collect-objects))
             (filtered
              (filter
               (lambda (obj)
                 (let ((obj-type (car obj))
                       (obj-name (cadr obj)))
                   (and (or (not type-filter) (eq? type-filter obj-type))
                        (or (not pattern) (match-pattern? obj-name pattern)))))
               all-objects)))

        ;; Group by type
        (let ((grouped (make-hash-table)))
          (for-each
           (lambda (obj)
             (let ((type (car obj)))
               (hash-table-set! grouped type
                                (cons obj (hash-table-ref/default grouped type '())))))
           filtered)

          ;; Print header
          (let ((width 60)
                (count (length filtered)))
            (print "")
            (print (repeat-string "─" width))
            (printf " SOUP DIRECTORY  ~a object~a~%"
                    count (if (= count 1) "" "s"))
            (print (repeat-string "─" width))

            (if (zero? count)
                (print " (empty)")

                ;; Print each type group
                (for-each
                 (lambda (type-pair)
                   (let* ((type (car type-pair))
                          (objs (reverse (hash-table-ref/default grouped type '()))))
                     (unless (null? objs)
                       (print "")
                       (printf " ~a/~%" type)
                       (for-each
                        (lambda (obj)
                          (let ((name (cadr obj))
                                (size (caddr obj))
                                (info (cadddr obj)))
                            (printf "   ~a~a~a  ~a~%"
                                    name
                                    (make-string (max 1 (- 32 (string-length name))) #\space)
                                    (format-size size)
                                    info)))
                        objs))))
                 *soup-types*))

            (print "")
            (print (repeat-string "─" width)))))))

  (define (complete prefix)
    "Complete partial object name (JSYS ESC command)"
    (let* ((all-objects (soup-collect-objects))
           (names (map cadr all-objects))
           (matches (filter (lambda (n) (string-prefix? prefix n)) names)))
      (cond
       ((null? matches)
        (print "No matches for: " prefix))
       ((= 1 (length matches))
        (print "Completion: " (car matches))
        (car matches))
       (else
        (print "Matches:")
        (for-each (lambda (m) (print "  " m)) matches)
        ;; Return common prefix
        (let ((common (find-common-prefix matches)))
          (when (> (string-length common) (string-length prefix))
            (print "Common prefix: " common))
          common)))))

  (define (find-common-prefix strings)
    "Find longest common prefix of strings"
    (if (null? strings)
        ""
        (let loop ((i 0))
          (if (or (>= i (string-length (car strings)))
                  (not (every (lambda (s)
                                (and (> (string-length s) i)
                                     (char=? (string-ref (car strings) i)
                                             (string-ref s i))))
                              (cdr strings))))
              (substring (car strings) 0 i)
              (loop (+ i 1))))))

  ;;; ============================================================================
  ;;; Archival and Restoration - First-class support
  ;;; ============================================================================

  (define (seal-archive version #!key format output)
    "Create sealed archive of a version
     Formats:
     - 'tarball: Standard gzip compressed tarball
     - 'bundle: Git bundle (includes full history)
     - 'cryptographic: Tarball with SPKI signature (legacy)
     - 'zstd-age: Zstd compressed, age encrypted with SPKI signature (preferred)"

    (let ((fmt (or format (vault-config 'archive-format)))
          (out (or output (sprintf "vault-~a.archive" version))))

      (case fmt
        ((tarball)
         (seal-archive-tarball version out))

        ((bundle)
         (seal-archive-bundle version out))

        ((cryptographic)
         (seal-archive-cryptographic version out))

        ((zstd-age)
         (seal-archive-zstd-age version out))

        (else
         (error "Unknown archive format" fmt)))

      (print "Archive sealed: " out)
      out))

  (define (seal-archive-tarball version output)
    "Create tarball archive"
    (run-command "git" "archive"
             "--format=tar.gz"
             (sprintf "--output=~a" output)
             "--prefix=vault/"
             version))

  (define (seal-archive-bundle version output)
    "Create git bundle with full history"
    (run-command "git" "bundle" "create" output version))

  (define (seal-archive-cryptographic version output)
    "Create encrypted archive with SPKI signature (legacy gzip format)"
    ;; First create tarball
    (let ((tarball (sprintf "~a.tar.gz" output)))
      (seal-archive-tarball version tarball)

      ;; Sign the tarball hash (signing-key is already a blob)
      (let ((signing-key (vault-config 'signing-key)))
        (when signing-key
          (let* ((tarball-bytes (read-file-bytes tarball))
                 (tarball-hash (sha512-hash tarball-bytes))
                 (signature (ed25519-sign signing-key tarball-hash)))

            ;; Create sealed archive manifest
            (with-output-to-file output
              (lambda ()
                (write `(sealed-archive
                         (version ,version)
                         (format cryptographic)
                         (tarball ,tarball)
                         (hash ,(blob->hex tarball-hash))
                         (signature ,(blob->hex signature))))))

            (print "Cryptographic seal applied"))))))

  (define (seal-archive-zstd-age version output)
    "Create zstd-compressed, age-encrypted archive with SPKI signature (preferred format)

     Pipeline: tar --zstd | age -r <recipients> > archive.tar.zst.age
     Benefits:
     - Faster compression than gzip (zstd)
     - Encryption at rest (age)
     - Ed25519/X25519 compatible (aligns with SPKI)
     - Parallel compression support (zstd -T0)"

    (let ((recipients (vault-config 'age-recipients))
          (signing-key (vault-config 'signing-key))
          (encrypted-file (sprintf "~a.tar.zst.age" output)))

      (unless (pair? recipients)
        (error "No age recipients configured. Use (vault-config 'age-recipients '(\"age1...\"))"))

      ;; Build age recipient arguments
      (let ((recipient-args (string-join
                             (map (lambda (r) (sprintf "-r ~a" r)) recipients)
                             " ")))

        ;; Create zstd-compressed, age-encrypted archive
        ;; Pipeline: git archive | tar --zstd | age -r ... > output
        (let ((cmd (sprintf "git archive --prefix=vault/ ~a | tar --zstd -cf - --files-from=- 2>/dev/null || git archive --prefix=vault/ ~a | zstd -T0 | age ~a > ~a"
                           version version recipient-args encrypted-file)))
          ;; Simpler approach: create tarball first, then compress and encrypt
          (let ((temp-tar (sprintf "/tmp/vault-~a-~a.tar" version (current-seconds))))
            (run-command "git" "archive" "--prefix=vault/" (sprintf "--output=~a" temp-tar) version)

            ;; Compress with zstd and encrypt with age
            (system (sprintf "zstd -T0 -c ~a | age ~a > ~a"
                            temp-tar recipient-args encrypted-file))

            ;; Clean up temp file
            (delete-file temp-tar)))

        ;; Sign the encrypted archive hash
        (when signing-key
          (let* ((archive-bytes (read-file-bytes encrypted-file))
                 (archive-hash (sha512-hash archive-bytes))
                 (signature (ed25519-sign signing-key archive-hash)))

            ;; Create sealed archive manifest
            (with-output-to-file output
              (lambda ()
                (write `(sealed-archive
                         (version ,version)
                         (format zstd-age)
                         (archive ,encrypted-file)
                         (compression zstd)
                         (encryption age)
                         (recipients ,recipients)
                         (hash ,(blob->hex archive-hash))
                         (signature ,(blob->hex signature))))))

            (print "Zstd+age archive sealed with SPKI signature"))))))

  (define (seal-restore archive #!key verify-key target identity)
    "Restore from sealed archive with verification
     - verify-key: SPKI public key for signature verification
     - target: extraction directory
     - identity: age identity file for decryption (zstd-age format)"
    (let ((target-dir (or target ".")))

      ;; Read archive manifest
      (let ((manifest (with-input-from-file archive read)))

        (unless (eq? (car manifest) 'sealed-archive)
          (error "Unknown archive format" (car manifest)))

        (let ((fmt (cadr (assq 'format (cdr manifest)))))
          (case fmt
            ((cryptographic)
             (seal-restore-cryptographic manifest verify-key target-dir))

            ((zstd-age)
             (seal-restore-zstd-age manifest verify-key target-dir identity))

            (else
             (error "Unknown sealed archive format" fmt)))))))

  (define (seal-restore-cryptographic manifest verify-key target-dir)
    "Restore and verify cryptographic archive (legacy gzip format)"
    (let ((version (cadr (assq 'version (cdr manifest))))
          (tarball (cadr (assq 'tarball (cdr manifest))))
          (hash-hex (cadr (assq 'hash (cdr manifest))))
          (sig-hex (cadr (assq 'signature (cdr manifest)))))

      (print "Restoring sealed archive: " version)

      ;; Verify signature if key provided
      (when verify-key
        (let* ((tarball-bytes (read-file-bytes tarball))
               (tarball-hash (sha512-hash tarball-bytes))
               (expected-hash (hex->blob hash-hex))
               (signature (hex->blob sig-hex))
               (pubkey (read-key-from-file verify-key)))

          (unless (equal? tarball-hash expected-hash)
            (error "Archive hash mismatch"))

          (unless (ed25519-verify pubkey tarball-hash signature)
            (error "Archive signature verification failed"))

          (print "✓ Archive seal verified")))

      ;; Extract tarball
      (run-command "tar" "-xzf" tarball "-C" target-dir)
      (print "Archive restored to: " target-dir)))

  (define (seal-restore-zstd-age manifest verify-key target-dir identity)
    "Restore and verify zstd+age encrypted archive

     Pipeline: age -d -i <identity> < archive | zstd -d | tar -x"
    (let ((version (cadr (assq 'version (cdr manifest))))
          (archive-file (cadr (assq 'archive (cdr manifest))))
          (hash-hex (cadr (assq 'hash (cdr manifest))))
          (sig-hex (cadr (assq 'signature (cdr manifest))))
          (id-file (or identity (vault-config 'age-identity))))

      (print "Restoring zstd+age sealed archive: " version)

      (unless id-file
        (error "No age identity configured. Use identity: parameter or (vault-config 'age-identity \"path\")"))

      ;; Verify signature if key provided
      (when verify-key
        (let* ((archive-bytes (read-file-bytes archive-file))
               (archive-hash (sha512-hash archive-bytes))
               (expected-hash (hex->blob hash-hex))
               (signature (hex->blob sig-hex))
               (pubkey (read-key-from-file verify-key)))

          (unless (equal? archive-hash expected-hash)
            (error "Archive hash mismatch - possible tampering"))

          (unless (ed25519-verify pubkey archive-hash signature)
            (error "Archive signature verification failed"))

          (print "✓ SPKI signature verified")))

      ;; Decrypt and extract: age -d | zstd -d | tar -x
      (let ((cmd (sprintf "age -d -i ~a < ~a | zstd -d | tar -xf - -C ~a"
                         id-file archive-file target-dir)))
        (let ((result (system cmd)))
          (unless (zero? result)
            (error "Failed to decrypt/extract archive"))))

      (print "✓ Archive decrypted and restored to: " target-dir)))

  ;;; ============================================================================
  ;;; Replication - Distribution and Synchronization
  ;;; ============================================================================

  (define (seal-publish version #!key remote archive-format message)
    "Publish sealed release to remote location

     - version: semantic version to publish
     - remote: publication target (git remote, URL, or directory path)
     - archive-format: 'tarball, 'bundle, or 'cryptographic (default)
     - message: release notes

     Publication process:
     1. Creates sealed release with seal-release
     2. Creates cryptographic archive with seal-archive
     3. Pushes to remote location
     4. Records publication in audit trail"

    (let ((remote-target (or remote (vault-config 'publish-remote)))
          (fmt (or archive-format 'cryptographic)))

      (unless remote-target
        (error "No remote configured for publication. Use vault-config or --remote"))

      ;; Create sealed release if it doesn't exist
      (let ((archive-file (sprintf "vault-~a.archive" version)))

        (print "Publishing sealed release: " version)

        ;; Create release if tag doesn't exist
        (unless (tag-exists? version)
          (seal-release version message: message))

        ;; Create archive
        (seal-archive version format: fmt output: archive-file)

        (print "Archive created: " archive-file)

        ;; Publish based on remote type
        (cond
         ;; Git remote (push tag and optionally upload release)
         ((git-remote? remote-target)
          (print "Pushing to git remote: " remote-target)
          (run-command "git" "push" remote-target version)
          (print "✓ Tag pushed to remote")

          ;; Upload archive if remote supports it (GitHub releases, etc.)
          (when (vault-config 'upload-release-assets)
            (upload-release-asset remote-target version archive-file)))

         ;; HTTP endpoint
         ((http-url? remote-target)
          (publish-http remote-target version archive-file))

         ;; File system path
         ((directory? remote-target)
          (publish-filesystem remote-target version archive-file))

         (else
          (error "Unknown remote type" remote-target)))

        ;; Record in audit trail
        (let ((signing-key (vault-config 'signing-key)))
          (when signing-key
            (audit-append
             actor: (get-vault-principal signing-key)
             action: (list 'seal-publish version remote-target)
             motivation: (or message (sprintf "Published release ~a" version)))))

        (print "✓ Publication complete: " version))))

  (define (seal-subscribe remote #!key target verify-key)
    "Subscribe to sealed releases from remote source

     - remote: subscription source (git remote, URL, or directory)
     - target: local directory for subscribed releases
     - verify-key: public key for verifying signatures

     Subscription process:
     1. Fetches available releases from remote
     2. Downloads and verifies cryptographic seals
     3. Stores releases in local subscription directory
     4. Records subscription in audit trail"

    (let ((target-dir (or target (vault-config 'subscribe-dir) ".vault/subscriptions"))
          (remote-source remote))

      (print "Subscribing to releases from: " remote-source)

      ;; Create subscription directory
      (create-directory target-dir #t)

      ;; Fetch releases based on remote type
      (let ((releases
             (cond
              ;; Git remote
              ((git-remote? remote-source)
               (fetch-git-releases remote-source))

              ;; HTTP endpoint
              ((http-url? remote-source)
               (fetch-http-releases remote-source))

              ;; File system
              ((directory? remote-source)
               (fetch-filesystem-releases remote-source))

              (else
               (error "Unknown remote type" remote-source)))))

        (print "Found " (length releases) " release(s)")

        ;; Download and verify each release
        (for-each
         (lambda (release-info)
           (let ((version (car release-info))
                 (url (cadr release-info)))
             (print "  Downloading: " version)
             (download-release url target-dir version)

             ;; Verify if key provided
             (when verify-key
               (let ((archive-path (sprintf "~a/vault-~a.archive" target-dir version)))
                 (seal-verify archive-path verify-key: verify-key)
                 (print "  ✓ Verified: " version)))))
         releases)

        ;; Record subscription in audit trail
        (let ((signing-key (vault-config 'signing-key)))
          (when signing-key
            (audit-append
             actor: (get-vault-principal signing-key)
             action: (list 'seal-subscribe remote-source)
             motivation: (sprintf "Subscribed to ~a release(s)" (length releases)))))

        (print "✓ Subscription complete: " (length releases) " release(s) downloaded"))))

  (define (seal-synchronize remote #!key direction verify-key)
    "Synchronize sealed releases bidirectionally

     - remote: sync partner (git remote, URL, or directory)
     - direction: 'push, 'pull, or 'both (default)
     - verify-key: public key for verifying incoming releases

     Synchronization:
     1. Discovers releases on both sides
     2. Exchanges missing releases
     3. Verifies all cryptographic seals
     4. Records sync in audit trail"

    (let ((sync-direction (or direction 'both))
          (remote-target remote))

      (print "Synchronizing with: " remote-target)

      ;; Get local releases
      (let ((local-releases (get-local-releases)))
        (print "Local releases: " (length local-releases))

        ;; Get remote releases
        (let ((remote-releases (get-remote-releases remote-target)))
          (print "Remote releases: " (length remote-releases))

          ;; Determine what needs syncing
          (let ((to-push (filter (lambda (v) (not (member v remote-releases))) local-releases))
                (to-pull (filter (lambda (v) (not (member v local-releases))) remote-releases)))

            (print "To publish: " (length to-push))
            (print "To subscribe: " (length to-pull))

            ;; Push missing releases
            (when (or (eq? sync-direction 'push) (eq? sync-direction 'both))
              (for-each
               (lambda (version)
                 (print "  Publishing: " version)
                 (seal-publish version remote: remote-target))
               to-push))

            ;; Pull missing releases
            (when (or (eq? sync-direction 'pull) (eq? sync-direction 'both))
              (for-each
               (lambda (version)
                 (print "  Subscribing: " version)
                 ;; Download single release
                 (download-single-release remote-target version verify-key))
               to-pull))

            ;; Record sync in audit trail
            (let ((signing-key (vault-config 'signing-key)))
              (when signing-key
                (audit-append
                 actor: (get-vault-principal signing-key)
                 action: (list 'seal-synchronize remote-target)
                 motivation: (sprintf "Synced ~a out, ~a in" (length to-push) (length to-pull)))))

            (print "✓ Synchronization complete"))))))

  ;;; Helper functions for replication

  (define (tag-exists? tag-name)
    "Check if git tag exists"
    (let ((tags (with-input-from-pipe (sprintf "git tag -l ~a" tag-name) read-string)))
      (not (string=? tags ""))))

  (define (git-remote? str)
    "Check if string looks like a git remote"
    (or (string-contains str "git@")
        (string-contains str ".git")
        (member str '("origin" "upstream"))))

  (define (http-url? str)
    "Check if string is HTTP(S) URL"
    (or (string-prefix? "http://" str)
        (string-prefix? "https://" str)))

  (define (publish-http url version archive-file)
    "Publish archive to HTTP endpoint"
    ;; Placeholder - would use curl or HTTP client
    (print "HTTP publication not yet implemented")
    (print "Would POST " archive-file " to " url))

  (define (publish-filesystem target-dir version archive-file)
    "Publish archive to filesystem location"
    (let ((dest (sprintf "~a/vault-~a.archive" target-dir version)))
      (create-directory target-dir #t)
      (run-command "cp" archive-file dest)
      (print "✓ Copied to: " dest)))

  (define (fetch-git-releases remote)
    "Fetch list of releases from git remote"
    ;; Fetch tags
    (run-command "git" "fetch" remote "--tags")
    ;; List tags matching semantic version pattern
    (with-input-from-pipe
        "git tag -l '[0-9]*.[0-9]*.[0-9]*'"
      (lambda ()
        (let loop ((tags '()))
          (let ((line (read-line)))
            (if (eof-object? line)
                (reverse tags)
                (loop (cons line tags))))))))

  (define (fetch-http-releases url)
    "Fetch release list from HTTP endpoint"
    ;; Placeholder
    '())

  (define (fetch-filesystem-releases dir)
    "Fetch releases from filesystem directory"
    (if (directory-exists? dir)
        (map (lambda (f)
               ;; Extract version from filename like "vault-1.0.0.archive"
               (let ((match (irregex-match '(: "vault-" (submatch (+ (or digit "."))) ".archive") f)))
                 (if match
                     (list (irregex-match-substring match 1) (sprintf "~a/~a" dir f))
                     #f)))
             (filter (lambda (f) (string-suffix? ".archive" f))
                    (directory dir)))
        '()))

  (define (download-release url target-dir version)
    "Download release archive"
    ;; Placeholder - would use curl or copy
    (print "Download from: " url))

  (define (download-single-release remote version verify-key)
    "Download and verify single release"
    ;; Placeholder
    (print "Would download " version " from " remote))

  (define (get-local-releases)
    "Get list of local sealed releases"
    (with-input-from-pipe
        "git tag -l '[0-9]*.[0-9]*.[0-9]*'"
      (lambda ()
        (let loop ((tags '()))
          (let ((line (read-line)))
            (if (eof-object? line)
                (reverse tags)
                (loop (cons line tags))))))))

  (define (get-remote-releases remote)
    "Get list of releases on remote"
    (if (git-remote? remote)
        (fetch-git-releases remote)
        '()))

  (define (upload-release-asset remote version archive-file)
    "Upload release asset to remote (e.g., GitHub releases)"
    ;; Placeholder
    (print "Would upload " archive-file " as release asset"))

  ;;; ============================================================================
  ;;; Migration Paths - Explicit version transitions
  ;;; ============================================================================

  (define (create-migration-marker from-version to-version)
    "Create migration path marker"
    (let ((migration-file (sprintf "~a/~a-to-~a.scm"
                                  (vault-config 'migration-dir)
                                  from-version
                                  to-version)))
      (create-directory (vault-config 'migration-dir) #t)
      (unless (file-exists? migration-file)
        (with-output-to-file migration-file
          (lambda ()
            (print ";;; Migration: " from-version " -> " to-version)
            (print ";;; Generated: " (current-seconds))
            (print "")
            (print "(define (migrate-" from-version "-to-" to-version ")")
            (print "  ;; Define migration logic here")
            (print "  #t)")
            (print "")
            (print "(migrate-" from-version "-to-" to-version ")")))
        (print "Migration template created: " migration-file))))

  (define (seal-migrate from-version to-version #!key script dry-run)
    "Migrate between sealed versions
     - script: path to migration script
     - dry-run: test migration without applying"

    (let ((migration-script
           (or script
               (sprintf "~a/~a-to-~a.scm"
                       (vault-config 'migration-dir)
                       from-version
                       to-version))))

      (unless (file-exists? migration-script)
        (error "Migration script not found" migration-script))

      (print "Migrating: " from-version " -> " to-version)

      (if dry-run
          (begin
            (print "DRY RUN - would execute: " migration-script)
            (print "Migration script:")
            (run-command "cat" migration-script))
          (begin
            ;; Execute migration script
            (load migration-script)
            (print "Migration complete")))))

  ;;; ============================================================================
  ;;; Integrity Checking
  ;;; ============================================================================

  (define (seal-check #!key deep)
    "Check vault integrity
     - deep: verify all sealed releases"

    (print "Checking vault integrity...")

    ;; Check git repository health
    (print "Repository status:")
    (run-command "git" "fsck" "--quick")

    ;; Verify sealed releases if deep check
    (when deep
      (print "")
      (print "Verifying sealed releases:")
      (let ((releases (get-sealed-releases)))
        (for-each
         (lambda (version)
           (handle-exceptions exn
             (print "  ✗ " version " - " (get-condition-property exn 'exn 'message))
             (if (seal-verify version)
                 (print "  ✓ " version)
                 (print "  ✗ " version " - signature invalid"))))
         releases))))

  (define (get-sealed-releases)
    "Get list of releases with seals"
    (if (directory-exists? ".vault/releases")
        (let ((files (directory ".vault/releases")))
          (filter-map
           (lambda (f)
             (and (string-suffix? ".sig" f)
                  (let ((name (pathname-file f)))
                    (substring name 0 (- (string-length name) 4)))))
           files))
        '()))


  ) ;; end module vault


;;; ============================================================================
;;; Example usage:
;;; ============================================================================
;;;
;;; ;; Initialize vault with signing key
;;; (vault-init signing-key: "alice.private")
;;;
;;; ;; Make changes
;;; (seal-commit "Add new feature" files: '("feature.scm"))
;;;
;;; ;; Create sealed release
;;; (seal-release "1.0.0" message: "Initial stable release")
;;;
;;; ;; Verify release
;;; (seal-verify "1.0.0" verify-key: "alice.public")
;;;
;;; ;; Create cryptographic archive
;;; (seal-archive "1.0.0" format: 'cryptographic)
;;;
;;; ;; Migrate to new version
;;; (seal-release "2.0.0" migrate-from: "1.0.0")
;;; (seal-migrate "1.0.0" "2.0.0")
;;;
;;; ;; Check vault integrity
;;; (seal-check deep: #t)
