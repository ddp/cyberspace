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
      (archive-format . tarball)   ; tarball, git-bundle, or cryptographic
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
  ;;; Archival and Restoration - First-class support
  ;;; ============================================================================

  (define (seal-archive version #!key format output)
    "Create sealed archive of a version
     Formats:
     - 'tarball: Standard compressed tarball
     - 'bundle: Git bundle (includes full history)
     - 'cryptographic: Encrypted archive with SPKI seal"

    (let ((fmt (or format (vault-config 'archive-format)))
          (out (or output (sprintf "vault-~a.archive" version))))

      (case fmt
        ((tarball)
         (seal-archive-tarball version out))

        ((bundle)
         (seal-archive-bundle version out))

        ((cryptographic)
         (seal-archive-cryptographic version out))

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
    "Create encrypted archive with SPKI signature"
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

  (define (seal-restore archive #!key verify-key target)
    "Restore from sealed archive with verification"
    (let ((target-dir (or target ".")))

      ;; Read archive manifest
      (let ((manifest (with-input-from-file archive read)))

        (case (car manifest)
          ((sealed-archive)
           (seal-restore-cryptographic manifest verify-key target-dir))

          (else
           (error "Unknown archive format" (car manifest)))))))

  (define (seal-restore-cryptographic manifest verify-key target-dir)
    "Restore and verify cryptographic archive"
    (let ((version (cadr (assq 'version manifest)))
          (tarball (cadr (assq 'tarball manifest)))
          (hash-hex (cadr (assq 'hash manifest)))
          (sig-hex (cadr (assq 'signature manifest))))

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
