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
   soup-stat
   soup-hash
   soup-merkle-hash-file
   soup-dual-hash-file
   soup-prove-chunk
   soup-verify-chunk
   soup-releases
   soup-du
   soup-find
   soup-query
   soup-inspect
   soup-collect-objects
   soup-create
   soup-get
   soup-delete
   soup-gc
   *default-realm-period*
   hex-abbrev
   complete
   ask

   ;; Cross-module reflection
   seek                   ; Search hash across soup, audit, wormhole
   dashboard              ; Unified status view

   ;; Node Roles (Memo-037)
   node-probe
   node-role
   node-can?
   node-announce
   *node-roles*
   *node-operations*
   probe-system-capabilities
   measure-weave
   weave-stratum
   *weave-strata*
   recommend-role

   ;; Keystore (Memo-041)
   keystore-create
   keystore-unlock
   keystore-lock
   keystore-status
   keystore-change-passphrase
   keystore-export-public
   keystore-path
   keystore-exists?

   ;; Lamport Clock (Memo-012)
   lamport-tick!
   lamport-time
   lamport-send
   lamport-receive!
   lamport-save!
   lamport-load!
   lamport-format

   ;; Realm naming
   realm-name
   set-realm-name!

   ;; Realm membership (Memo-050) - cert-based
   realm-affiliated?
   realm-membership-cert
   cert-valid?
   store-membership-cert!
   revoke-membership!

   ;; Address parsing (Memo-041)
   parse-address
   address?
   address-principal
   address-role
   address-capabilities
   address-path
   address->string
   make-address

   ;; Configuration
   vault-init
   vault-config
   get-vault-principal

   ;; Provenance (introspectable)
   vault-license
   vault-copyright

   ;; Capability Set (weave self-awareness)
   capability-add!
   capability-remove!
   capability?
   capabilities
   capability-intersect
   capability-difference
   capability-audit-enable!)

  (import scheme
          (chicken base)
          (chicken process)
          (chicken process-context)
          (chicken string)
          (chicken format)
          (chicken io)
          (chicken port)
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
          (chicken sort)  ; sorting
          srfi-69  ; hash tables
          (chicken type)  ; for type declarations
          cert
          crypto-ffi
          audit
          os)

  ;;; ============================================================================
  ;;; Type Declarations
  ;;; ============================================================================
  ;;
  ;; Explicit types help the scrutinizer avoid exponential inference.
  ;; Ada got this right: declare everything, infer nothing.

  (: format-size (number -> string))
  (: soup-summary-archives (list -> string))
  (: soup-summary-releases (list -> string))
  (: soup-summary-audit (list -> string))
  (: soup-summary-keys (list -> string))
  (: soup-summary-metadata (list -> string))
  (: soup-summary-certs (list -> string))
  (: soup-summary-identity (list -> string))

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

  ;; Vault provenance - embedded copyright and license (introspectable)
  (define *vault-provenance*
    '((copyright . "Copyright (c) 2026 ddp@eludom.net")
      (license . "MIT")
      (license-status . "unpublished-proprietary")
      (license-note . "License applies upon public release")
      (project . "Library of Cyberspace")))

  (define (vault-license)
    "Return vault license and copyright information (introspectable metadata)"
    *vault-provenance*)

  (define (vault-copyright)
    "Return copyright string"
    (alist-ref 'copyright *vault-provenance*))

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
  ;;; Keystore (Memo-041)
  ;;; ============================================================================
  ;;;
  ;;; The keystore is the inner vault - where cryptographic identity lives.
  ;;; Private keys are encrypted at rest with Argon2id + XSalsa20-Poly1305.

  ;; Keystore state (unlocked key in memory, zeroed on lock)
  (define *keystore-unlocked* #f)      ; Ed25519 secret key when unlocked
  (define *keystore-public* #f)        ; Ed25519 public key (always available after create)

  (define (keystore-path)
    "Return path to keystore directory"
    ".vault/keystore")

  (define (keystore-key-path)
    ".vault/keystore/realm.key")

  (define (keystore-pub-path)
    ".vault/keystore/realm.pub")

  (define (keystore-exists?)
    "Check if keystore has been created"
    (file-exists? (keystore-key-path)))

  (define (keystore-create passphrase)
    "Create new realm identity with passphrase protection"
    (when (keystore-exists?)
      (error "Keystore already exists. Use keystore-change-passphrase to update."))

    ;; Create keystore directory
    (let ((ks-dir (keystore-path)))
      (unless (directory-exists? ks-dir)
        (create-directory ks-dir #t)))

    ;; Generate Ed25519 keypair
    (let* ((keypair (ed25519-keypair))
           (public-key (car keypair))
           (secret-key (cadr keypair))
           ;; Generate salt for Argon2id
           (salt (random-bytes 16))
           ;; Derive encryption key from passphrase
           (enc-key (argon2id-hash passphrase salt))
           ;; Encrypt secret key
           (nonce (random-bytes secretbox-noncebytes))
           (ciphertext (secretbox-encrypt secret-key nonce enc-key)))
      (session-stat! 'encrypts)

      ;; Write encrypted private key
      (with-output-to-file (keystore-key-path)
        (lambda ()
          (write `(realm-private-key
                   (version 1)
                   (algorithm "ed25519")
                   (kdf "argon2id")
                   (salt ,salt)
                   (nonce ,nonce)
                   (ciphertext ,ciphertext)))
          (newline)))

      ;; Write public key (plaintext)
      (with-output-to-file (keystore-pub-path)
        (lambda ()
          (write `(realm-public-key
                   (version 1)
                   (algorithm "ed25519")
                   (public-key ,public-key)
                   (created ,(current-seconds))))
          (newline)))

      ;; Zero the encryption key
      (memzero! enc-key)

      ;; Store in memory (unlocked after creation)
      (set! *keystore-public* public-key)
      (set! *keystore-unlocked* secret-key)

      ;; Update vault config
      (vault-config 'signing-key secret-key)

      ;; Return principal
      (print "Realm created: ed25519:" (blob->hex public-key))
      public-key))

  (define (keystore-unlock passphrase)
    "Unlock keystore with passphrase"
    (unless (keystore-exists?)
      (error "No keystore found. Use keystore-create first."))

    (if *keystore-unlocked*
        (begin
          (print "Keystore already unlocked.")
          *keystore-public*)
        ;; Read encrypted key file
        (let* ((key-data (with-input-from-file (keystore-key-path) read))
               (salt (cadr (assq 'salt (cdr key-data))))
               (nonce (cadr (assq 'nonce (cdr key-data))))
               (ciphertext (cadr (assq 'ciphertext (cdr key-data))))
               ;; Derive decryption key
               (dec-key (argon2id-hash passphrase salt))
               ;; Decrypt
               (secret-key (secretbox-decrypt ciphertext nonce dec-key)))
          (session-stat! 'decrypts)

          ;; Zero the decryption key
          (memzero! dec-key)

          (if secret-key
              (begin
                ;; Load public key
                (let* ((pub-data (with-input-from-file (keystore-pub-path) read))
                       (public-key (cadr (assq 'public-key (cdr pub-data)))))
                  (set! *keystore-public* public-key)
                  (set! *keystore-unlocked* secret-key)
                  (vault-config 'signing-key secret-key)
                  (session-stat! 'unlocks)
                  (print "Keystore unlocked: ed25519:" (blob->hex public-key))
                  public-key))
              (begin
                (print "Error: Wrong passphrase")
                #f)))))

  (define (keystore-lock)
    "Lock keystore, zero secret key from memory"
    (when *keystore-unlocked*
      (memzero! *keystore-unlocked*)
      (set! *keystore-unlocked* #f)
      (vault-config 'signing-key #f)
      (print "Keystore locked."))
    #t)

  (define (keystore-status)
    "Return keystore status"
    (cond
     ((not (keystore-exists?))
      '(keystore (status none)))
     (*keystore-unlocked*
      `(keystore
        (status unlocked)
        (principal ,(string-append "ed25519:" (blob->hex *keystore-public*)))))
     (else
      ;; Read public key from file
      (let* ((pub-data (with-input-from-file (keystore-pub-path) read))
             (public-key (cadr (assq 'public-key (cdr pub-data)))))
        `(keystore
          (status locked)
          (principal ,(string-append "ed25519:" (blob->hex public-key))))))))

  (define (keystore-change-passphrase old-passphrase new-passphrase)
    "Change keystore passphrase"
    ;; First unlock with old passphrase
    (let ((secret-key (or *keystore-unlocked*
                          (keystore-unlock old-passphrase))))
      (unless secret-key
        (error "Wrong passphrase"))

      ;; Generate new salt and encrypt with new passphrase
      (let* ((salt (random-bytes 16))
             (enc-key (argon2id-hash new-passphrase salt))
             (nonce (random-bytes secretbox-noncebytes))
             (ciphertext (secretbox-encrypt secret-key nonce enc-key)))
        (session-stat! 'encrypts)

        ;; Write new encrypted key
        (with-output-to-file (keystore-key-path)
          (lambda ()
            (write `(realm-private-key
                     (version 1)
                     (algorithm "ed25519")
                     (kdf "argon2id")
                     (salt ,salt)
                     (nonce ,nonce)
                     (ciphertext ,ciphertext)))
            (newline)))

        ;; Zero encryption key
        (memzero! enc-key)

        (print "Passphrase changed.")
        #t)))

  (define (keystore-export-public)
    "Export public key (safe to share)"
    (if (keystore-exists?)
        (with-input-from-file (keystore-pub-path) read)
        (error "No keystore found")))

  ;;; ============================================================================
  ;;; Realm Naming
  ;;; ============================================================================
  ;;;
  ;;; Realms can have human-readable names (like hostnames for IP addresses).
  ;;; The name is stored in .vault/realm-name as a simple string.

  (define (realm-name-path)
    ".vault/realm-name")

  (define (realm-name)
    "Get the realm's human-readable name, or #f if unnamed"
    (let ((path (realm-name-path)))
      (if (file-exists? path)
          (string-trim-both (with-input-from-file path read-string))
          #f)))

  (define (set-realm-name! name)
    "Set the realm's human-readable name"
    (unless (directory-exists? ".vault")
      (error "No vault found. Create one first."))
    (with-output-to-file (realm-name-path)
      (lambda () (display name) (newline)))
    (print "Realm named: " name)
    name)

  ;;; ============================================================================
  ;;; Realm Membership (Memo-050) - Certificate-Based
  ;;; ============================================================================
  ;;;
  ;;; Membership is proven by a signed enrollment certificate in the soup.
  ;;; No certificate = wilderness. Expired certificate = wilderness.
  ;;; Certificates have lifetimes (default 1 year) and require renewal.
  ;;;
  ;;; Storage: .vault/certs/membership.sexp
  ;;; Format: (signed-enrollment-cert (spki-cert ...) (signature ...))

  (define (certs-path)
    ".vault/certs")

  (define (membership-cert-path)
    ".vault/certs/membership.sexp")

  (define (realm-membership-cert)
    "Get the membership certificate, or #f if none exists"
    (let ((path (membership-cert-path)))
      (if (file-exists? path)
          (with-input-from-file path read)
          #f)))

  (define (cert-valid? cert)
    "Check if certificate is within its validity period"
    (and cert
         (pair? cert)
         (eq? (car cert) 'signed-enrollment-cert)
         (let* ((body (cadr cert))                    ; (spki-cert ...)
                (body-fields (cdr body))              ; ((issuer ...) (subject ...) ...)
                (validity (assq 'validity body-fields)))
           (and validity
                (let ((not-before (assq 'not-before (cdr validity)))
                      (not-after (assq 'not-after (cdr validity)))
                      (now (current-seconds)))
                  (and (or (not not-before) (<= (cadr not-before) now))
                       (or (not not-after) (< now (cadr not-after)))))))))

  (define (realm-affiliated?)
    "Return #t if this node has a valid membership certificate"
    (cert-valid? (realm-membership-cert)))

  (define (store-membership-cert! cert)
    "Store membership certificate in the vault.
     cert: signed-enrollment-cert s-expression"
    (unless (directory-exists? ".vault")
      (error "No vault found. Create one first."))
    (unless (directory-exists? (certs-path))
      (create-directory (certs-path)))
    (with-output-to-file (membership-cert-path)
      (lambda () (write cert) (newline)))
    cert)

  (define (revoke-membership!)
    "Revoke membership, return to Wilderness. Keys are retained."
    (let ((path (membership-cert-path)))
      (when (file-exists? path)
        (delete-file path)
        (print "Membership revoked. You are now in the Wilderness."))))

  ;;; ============================================================================
  ;;; Soup Object Store (Memo-002 Section 2.3)
  ;;; ============================================================================
  ;;;
  ;;; Objects are born with their destiny. Lifetime is intrinsic:
  ;;;   temporary  - explicit duration, garbage collected when expired
  ;;;   default    - realm's standard period, garbage collected when expired
  ;;;   archivable - active period, then migrates to vault with transition record

  ;; Default realm period: 1 year (365 days in seconds)
  (define *default-realm-period* 31536000)

  (define (soup-path)
    ".vault/soup")

  (define (ensure-soup-dir!)
    "Create .vault/soup directory if needed"
    (unless (directory-exists? ".vault")
      (error "No vault found. Create one first."))
    (unless (directory-exists? (soup-path))
      (create-directory (soup-path))))

  (define (soup-object-path id)
    "Get path to a soup object by ID"
    (sprintf "~a/~a.sexp" (soup-path) id))

  (define (generate-soup-id content)
    "Generate a unique ID for a soup object based on content hash + timestamp"
    (let* ((data (sprintf "~a~a" content (current-seconds)))
           (hash (blob->hex (blake2b-hash data)))
           (short-hash (substring hash 0 12)))
      short-hash))

  (define (soup-create content #!key
                       (lifetime 'default)
                       (expires #f)
                       (tags '())
                       (name #f))
    "Create a new object in the soup with specified lifetime.

     content: any s-expression to store
     lifetime: 'temporary, 'default, or 'archivable
     expires: explicit expiration time (seconds since epoch) for 'temporary
     tags: list of symbols for categorization
     name: optional human-readable name

     Returns: object ID

     Examples:
       (soup-create '(note \"hello\") lifetime: 'temporary expires: (+ (current-seconds) 3600))
       (soup-create '(draft \"work in progress\") lifetime: 'default)
       (soup-create '(document \"important\") lifetime: 'archivable)"
    (ensure-soup-dir!)
    (let* ((now (current-seconds))
           (id (or name (generate-soup-id content)))
           (expiration (case lifetime
                         ((temporary)
                          (or expires
                              (error "soup-create: 'temporary requires expires: parameter")))
                         ((default)
                          (+ now *default-realm-period*))
                         ((archivable)
                          (+ now *default-realm-period*))  ; active period
                         (else
                          (error "soup-create: lifetime must be 'temporary, 'default, or 'archivable"))))
           (obj `(soup-object
                   (id ,id)
                   (created ,now)
                   (expires ,expiration)
                   (lifetime ,lifetime)
                   (tags ,tags)
                   (content ,content))))
      (with-output-to-file (soup-object-path id)
        (lambda () (write obj) (newline)))
      id))

  (define (soup-get id)
    "Retrieve a soup object by ID. Returns #f if not found or expired."
    (let ((path (soup-object-path id)))
      (if (file-exists? path)
          (let ((obj (with-input-from-file path read)))
            (if (and (pair? obj) (eq? 'soup-object (car obj)))
                (let* ((fields (cdr obj))
                       (expires (cadr (assq 'expires fields)))
                       (now (current-seconds)))
                  (if (< now expires)
                      obj
                      #f))  ; expired
                #f))
          #f)))

  (define (soup-delete id)
    "Delete a soup object by ID."
    (let ((path (soup-object-path id)))
      (when (file-exists? path)
        (delete-file path)
        #t)))

  (define (soup-gc)
    "Garbage collect expired soup objects.
     Archivable objects are migrated to vault instead of deleted.
     Returns: (deleted migrated) counts"
    (let ((deleted 0)
          (migrated 0)
          (now (current-seconds)))
      (when (directory-exists? (soup-path))
        (for-each
          (lambda (f)
            (when (string-suffix? ".sexp" f)
              (let* ((path (sprintf "~a/~a" (soup-path) f))
                     (obj (handle-exceptions exn #f
                            (with-input-from-file path read))))
                (when (and obj (pair? obj) (eq? 'soup-object (car obj)))
                  (let* ((fields (cdr obj))
                         (expires (cadr (assq 'expires fields)))
                         (lifetime (cadr (assq 'lifetime fields))))
                    (when (>= now expires)
                      (if (eq? lifetime 'archivable)
                          ;; Migrate to vault with transition record
                          (begin
                            (soup-migrate-to-vault! obj path)
                            (set! migrated (+ migrated 1)))
                          ;; Delete expired temporary/default objects
                          (begin
                            (delete-file path)
                            (set! deleted (+ deleted 1))))))))))
          (directory (soup-path))))
      (list deleted migrated)))

  (define (soup-migrate-to-vault! obj source-path)
    "Migrate an archivable object to the vault with transition record.
     The transition record includes a BLAKE2b hash of the content for
     provenance verification - proving the archived content matches what
     was active in the realm."
    (let* ((fields (cdr obj))
           (id (cadr (assq 'id fields)))
           (created (cadr (assq 'created fields)))
           (expires (cadr (assq 'expires fields)))
           (content (cadr (assq 'content fields)))
           (now (current-seconds))
           ;; Hash the content for provenance verification
           (content-str (with-output-to-string (lambda () (write content))))
           (content-hash (blob->hex (blake2b-hash (string->blob content-str))))
           (vault-obj `(vault-object
                         (content ,content)
                         (transition
                           (active-from ,created)
                           (active-until ,expires)
                           (preserved ,now)
                           (realm ,(realm-name))
                           (origin ,(hostname))
                           (source-id ,id)
                           (hash ,content-hash)))))
      ;; Store in .vault/archive/
      (unless (directory-exists? ".vault/archive")
        (create-directory ".vault/archive"))
      (with-output-to-file (sprintf ".vault/archive/~a.sexp" id)
        (lambda () (write vault-obj) (newline)))
      ;; Remove from soup
      (delete-file source-path)))

  ;;; ============================================================================
  ;;; Lamport Clock (Memo-012)
  ;;; ============================================================================
  ;;;
  ;;; Time in the weave is measured in lambda ticks, not wall-clock time.
  ;;; The clock increments monotonically on every event.
  ;;; Federation sync uses happened-before, not synchronized clocks.

  ;; The global Lamport clock for this node
  (define *lamport-counter* 0)

  (define (lamport-clock-path)
    ".vault/lamport-clock")

  (define (lamport-tick!)
    "Increment clock for local event. Returns new time."
    (set! *lamport-counter* (+ 1 *lamport-counter*))
    *lamport-counter*)

  (define (lamport-time)
    "Current Lamport time (λ ticks since genesis)."
    *lamport-counter*)

  (define (lamport-send message)
    "Attach timestamp to outgoing message. Increments clock."
    (lamport-tick!)
    `((lamport-time . ,*lamport-counter*)
      (payload . ,message)))

  (define (lamport-receive! timestamped-message)
    "Update clock on message receipt. Returns payload."
    (let ((remote-time (cdr (assq 'lamport-time timestamped-message))))
      (set! *lamport-counter*
            (+ 1 (max *lamport-counter* remote-time)))
      (cdr (assq 'payload timestamped-message))))

  (define (lamport-save!)
    "Persist clock to vault (survives restarts)."
    (when (directory-exists? ".vault")
      (with-output-to-file (lamport-clock-path)
        (lambda ()
          (write `(lamport-clock (counter ,*lamport-counter*)))
          (newline)))))

  (define (lamport-load!)
    "Load clock from vault. Called at startup."
    (let ((path (lamport-clock-path)))
      (when (file-exists? path)
        (let ((data (with-input-from-file path read)))
          (when (and (pair? data) (eq? (car data) 'lamport-clock))
            (let ((counter-pair (assq 'counter (cdr data))))
              (when counter-pair
                (set! *lamport-counter* (cadr counter-pair)))))))))

  (define (lamport-format)
    "Human-readable Lamport time with SI prefix for large values."
    (let ((t *lamport-counter*))
      (cond
        ((< t 1000) (sprintf "λ ~a" t))
        ((< t 1000000) (sprintf "λ ~ak" (quotient t 1000)))
        ((< t 1000000000) (sprintf "λ ~am" (quotient t 1000000)))
        (else (sprintf "λ ~ag" (quotient t 1000000000))))))

  ;;; ============================================================================
  ;;; Capability Set (Weave Self-Awareness)
  ;;; ============================================================================
  ;;;
  ;;; Tracks what this node can do. Used for gossip negotiation and introspection.
  ;;; Capabilities are symbols registered at module load or runtime.

  (define *capabilities* (make-hash-table eq?))
  (define *capability-audit* #f)  ; Set to signing-key to enable auditing

  (define (capability-add! cap)
    "Register a capability this node supports."
    (hash-table-set! *capabilities* cap #t)
    (when *capability-audit*
      (audit-append
        actor: (get-vault-principal *capability-audit*)
        action: `(capability-add ,cap)
        motivation: "Capability registered"
        signing-key: *capability-audit*))
    cap)

  (define (capability-remove! cap)
    "Remove a capability."
    (hash-table-delete! *capabilities* cap)
    (when *capability-audit*
      (audit-append
        actor: (get-vault-principal *capability-audit*)
        action: `(capability-remove ,cap)
        motivation: "Capability removed"
        signing-key: *capability-audit*)))

  (define (capability? cap)
    "Check if this node has a capability."
    (hash-table-exists? *capabilities* cap))

  (define (capabilities)
    "List all capabilities as a sorted list."
    (sort (hash-table-keys *capabilities*)
          (lambda (a b) (string<? (symbol->string a) (symbol->string b)))))

  (define (capability-intersect caps1 caps2)
    "Set intersection: capabilities both have."
    (filter (lambda (c) (memq c caps2)) caps1))

  (define (capability-difference caps1 caps2)
    "Set difference: capabilities in caps1 but not caps2."
    (filter (lambda (c) (not (memq c caps2))) caps1))

  (define (capability-audit-enable! signing-key)
    "Enable signed attestations for capability changes.
     Your key is the notary."
    (set! *capability-audit* signing-key)
    'audit-enabled)

  ;; Register core capabilities at load time
  (capability-add! 'ed25519-sign)
  (capability-add! 'ed25519-verify)
  (capability-add! 'sha256-hash)
  (capability-add! 'argon2id-kdf)
  (capability-add! 'chacha20-poly1305)
  (capability-add! 'lamport-clock)
  (capability-add! 'spki-certs)
  (capability-add! 'audit-trail)

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
        ;; Track bytes written
        (when (file-exists? metadata-file)
          (session-stat! 'writes)
          (session-stat! 'bytes-written (file-size metadata-file)))

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
    (session-stat! 'commits)
    (lamport-tick!)  ; Memo-012: tick the weave clock

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
           motivation: message)))
      ;; Persist the weave clock
      (lamport-save!)))

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

  (define (seal-release version #!key name message migrate-from)
    "Create a cryptographically sealed release
     - version: semantic version (e.g., '1.0.0')
     - name: release codename (e.g., 'genesis')
     - message: release notes
     - migrate-from: previous version for migration tracking"

    ;; Validate semantic version (basic check: X.Y.Z format)
    (unless (and (irregex-match '(: (+ digit) "." (+ digit) "." (+ digit)) version)
                 (= 3 (length (string-split version "."))))
      (error "Invalid semantic version (expected X.Y.Z)" version))

    ;; Get current commit hash
    (let ((hash (with-input-from-pipe "git rev-parse HEAD" read-line))
          (timestamp (current-seconds)))

      ;; Create annotated tag with name if provided
      (let ((tag-message (or message
                             (if name
                                 (sprintf "Release ~a (~a)" version name)
                                 (sprintf "Release ~a" version)))))
        (run-command "git" "tag" "-a" version "-m" tag-message))

      ;; Sign with SPKI if signing key configured
      (let ((signing-key (vault-config 'signing-key)))
        (when signing-key
          (seal-sign-release version name hash signing-key)))

      ;; Create migration marker if migrating from previous version
      (when migrate-from
        (create-migration-marker migrate-from version))

      (if name
          (print "Sealed release: " version " (" name ") at " hash)
          (print "Sealed release: " version " at " hash))))

  (define (seal-sign-release version name hash signing-key)
    "Sign a release with SPKI certificate"
    ;; Create release manifest
    (let ((manifest (if name
                        (sprintf "(release ~s ~s ~s ~s)" version name hash (current-seconds))
                        (sprintf "(release ~s ~s ~s)" version hash (current-seconds)))))
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
                       ,@(if name `((name ,name)) '())
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
                (print "✗ Release seal Invalid: " version)
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

  ;; Box-drawing functions are now centralized in os.scm
  ;; Use: (make-box width *box-rounded*) and box-top, box-line, etc.
  ;; Local wrappers for vault's simpler width-based API:

  (define (repeat-string str n)
    "Repeat a string n times"
    (let loop ((i 0) (acc ""))
      (if (= i n) acc
          (loop (+ i 1) (string-append acc str)))))

  (define (vault-box-top width)
    "Top border with rounded corners"
    (string-append "╭" (make-string (- width 1) #\─) "╮"))

  (define (vault-box-bottom width)
    "Bottom border with rounded corners"
    (string-append "╰" (make-string (- width 1) #\─) "╯"))

  (define (vault-box-divider width)
    "Horizontal divider"
    (string-append "├" (make-string (- width 1) #\─) "┤"))

  (define (vault-box-line content width)
    "Content line with padding using centralized display-width"
    (let* ((content-width (string-display-width content))
           (padded (if (> content-width (- width 2))
                       (substring content 0 (- width 2))
                       content))
           (padding (- width 2 (string-display-width padded))))
      (string-append "│ " padded (make-string (max 0 padding) #\space) "│")))

  (define (box-line-pair label value width)
    (let* ((formatted (sprintf "~a:~a~a"
                               label
                               (make-string (max 1 (- 20 (string-display-width label))) #\space)
                               value)))
      (vault-box-line formatted width)))

  (define (print-box-header title type width)
    (print (vault-box-top width))
    (print (vault-box-line (sprintf "object: ~a" title) width))
    (print (vault-box-line (sprintf "type:   ~a" type) width))
    (print (vault-box-divider width)))

  (define (print-section-header title width)
    (print (vault-box-line "" width))
    (print (vault-box-line title width))
    (print (vault-box-line "" width)))

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
                           "✓ Verified"
                           "✗ Failed"))
                     "⚠ Not Verified (no key)")))

            ;; Print inspection output
            (print-box-header (pathname-file path) "sealed-archive" width)

            (print-section-header "Security Properties" width)
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

            (print (vault-box-divider width))
            (print-section-header "Migration Properties" width)
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

            (print (vault-box-line "" width))
            (print (vault-box-bottom width)))))))

  (define (inspect-release version #!key verify-key verbose)
    "Inspect a sealed release by version"
    (let ((width 60)
          (sig-file (sprintf ".vault/releases/~a.sig" version)))

      (print-box-header version "sealed-release" width)
      (print-section-header "Security Properties" width)

      (if (file-exists? sig-file)
          (let ((sig-data (with-input-from-file sig-file read)))
            (let ((manifest (cadr (assq 'manifest (cdr sig-data))))
                  (hash (cadr (assq 'hash (cdr sig-data)))))
              (print (box-line-pair "Signing Algorithm" "ed25519-sha512" width))
              (print (box-line-pair "Manifest Hash" (substring hash 0 32) width))

              (let ((sig-status
                     (if verify-key
                         (if (seal-verify version verify-key: verify-key)
                             "✓ Verified"
                             "✗ Failed")
                         "⚠ Not Verified (no key)")))
                (print (box-line-pair "Signature" sig-status width)))))

          (print (box-line-pair "Signature" "none (unsigned release)" width)))

      (print (vault-box-divider width))
      (print-section-header "Migration Properties" width)

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

      (print (vault-box-line "" width))
      (print (vault-box-bottom width))))

  (define (inspect-signed-cert sc #!key verify-key verbose)
    "Inspect a signed certificate"
    (let ((width 60))
      ;; Handle both sexp and record forms
      (let* ((cert-data (if (pair? sc) (cdr sc) sc))
             (cert-sexp (if (pair? cert-data) (car cert-data) cert-data)))

        (print-box-header "signed-certificate" "spki-cert" width)
        (print-section-header "Security Properties" width)
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

        (print (vault-box-divider width))
        (print-section-header "Delegation Properties" width)
        (print (box-line-pair "Chain Depth" "1 (direct)" width))
        (print (box-line-pair "Validity" "check cert-validity" width))

        (print (vault-box-line "" width))
        (print (vault-box-bottom width)))))

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
          (print-section-header "Security Properties" width)

          (if seal
              (let ((seal-fields (cdr seal)))
                (let ((algorithm (let ((a (assq 'algorithm seal-fields)))
                                  (if a (cadr a) "ed25519-sha512"))))
                  (print (box-line-pair "Seal Algorithm" algorithm width))
                  (print (box-line-pair "Content Hash" (substring id 0 32) width))
                  (print (box-line-pair "Chain Link" "parent-id reference" width))))
              (print (box-line-pair "Seal" "none" width)))

          (print (vault-box-divider width))
          (print-section-header "Audit Properties" width)
          (print (box-line-pair "Entry ID" (substring id 0 24) width))
          (print (box-line-pair "Sequence" (number->string sequence) width))
          (print (box-line-pair "Timestamp" timestamp width))
          (print (box-line-pair "Immutable" "✓ (content-addressed)" width))

          (print (vault-box-line "" width))
          (print (vault-box-bottom width))))))

  ;;; ============================================================================
  ;;; Address Parsing (Memo-041)
  ;;; ============================================================================
  ;;;
  ;;; Cyberspace object addresses:
  ;;;   @principal:/path                    - basic addressing
  ;;;   @principal+role:/path               - with role context
  ;;;   @principal+{cap1,cap2}:/path        - with explicit capabilities
  ;;;   @principal+role{cap1,cap2}:/path    - role refined to specific caps
  ;;;
  ;;; Grammar:
  ;;;   address     = "@" principal [ "+" context ] ":" path
  ;;;   principal   = "ed25519:" hexstring | hexstring
  ;;;   context     = role [ "{" capabilities "}" ] | "{" capabilities "}"
  ;;;   role        = identifier
  ;;;   capabilities = capability { "," capability }
  ;;;   capability  = identifier [ "(" arguments ")" ]
  ;;;   path        = "/" segment { "/" segment }

  ;; Address record type
  (define (make-address principal role capabilities path)
    "Create an address record"
    (list 'address principal role capabilities path))

  (define (address? obj)
    "Check if object is an address"
    (and (pair? obj) (eq? (car obj) 'address)))

  (define (address-principal addr)
    "Get principal from address"
    (if (address? addr) (list-ref addr 1) #f))

  (define (address-role addr)
    "Get role from address (may be #f)"
    (if (address? addr) (list-ref addr 2) #f))

  (define (address-capabilities addr)
    "Get capabilities list from address (may be empty)"
    (if (address? addr) (list-ref addr 3) '()))

  (define (address-path addr)
    "Get path from address"
    (if (address? addr) (list-ref addr 4) #f))

  (define (address->string addr)
    "Convert address back to string form"
    (if (not (address? addr))
        (error "Not an address" addr)
        (let ((principal (address-principal addr))
              (role (address-role addr))
              (caps (address-capabilities addr))
              (path (address-path addr)))
          (string-append
           "@" principal
           (cond
            ;; Role with caps: +role{caps}
            ((and role (not (null? caps)))
             (string-append "+" role "{" (string-intersperse caps ",") "}"))
            ;; Role only: +role
            (role
             (string-append "+" role))
            ;; Caps only: +{caps}
            ((not (null? caps))
             (string-append "+{" (string-intersperse caps ",") "}"))
            ;; Neither
            (else ""))
           ":" path))))

  (define (parse-capabilities str)
    "Parse capability list from string like 'read,write,delegate(read,write)'.
     Handles nested parentheses in delegate(...) expressions."
    (if (or (not str) (string=? str ""))
        '()
        (let loop ((chars (string->list str))
                   (current '())
                   (depth 0)
                   (result '()))
          (cond
           ;; End of string
           ((null? chars)
            (if (null? current)
                (reverse result)
                (reverse (cons (string-trim-both (list->string (reverse current)))
                               result))))
           ;; Opening paren - increase depth
           ((char=? (car chars) #\()
            (loop (cdr chars) (cons (car chars) current) (+ depth 1) result))
           ;; Closing paren - decrease depth
           ((char=? (car chars) #\))
            (loop (cdr chars) (cons (car chars) current) (- depth 1) result))
           ;; Comma at depth 0 - split here
           ((and (char=? (car chars) #\,) (= depth 0))
            (loop (cdr chars)
                  '()
                  0
                  (cons (string-trim-both (list->string (reverse current)))
                        result)))
           ;; Regular character
           (else
            (loop (cdr chars) (cons (car chars) current) depth result))))))

  (define (parse-address str)
    "Parse a cyberspace address string into components
     Returns: (address principal role capabilities path) or #f on failure

     Examples:
       @ed25519:7f3a...:/releases/1.0.3
       @7f3a...+curator:/collections
       @7f3a...+{read,write}:/objects
       @7f3a...+curator{read}:/collections"
    (if (not (string-prefix? "@" str))
        #f
        (let* ((without-at (substring str 1))
               ;; Find the colon that separates principal+context from path
               ;; Must find last colon after any {} group
               (colon-pos (let loop ((i 0) (depth 0) (last-colon #f))
                            (if (>= i (string-length without-at))
                                last-colon
                                (let ((c (string-ref without-at i)))
                                  (cond
                                   ((char=? c #\{) (loop (+ i 1) (+ depth 1) last-colon))
                                   ((char=? c #\}) (loop (+ i 1) (- depth 1) last-colon))
                                   ((and (char=? c #\:) (= depth 0))
                                    (loop (+ i 1) depth i))
                                   (else (loop (+ i 1) depth last-colon))))))))
          (if (not colon-pos)
              #f
              (let* ((before-colon (substring without-at 0 colon-pos))
                     (path (substring without-at (+ colon-pos 1)))
                     ;; Check for + separator
                     (plus-pos (string-index before-colon #\+)))
                (if (not plus-pos)
                    ;; Simple case: @principal:/path
                    (make-address before-colon #f '() path)
                    ;; Has context: @principal+context:/path
                    (let* ((principal (substring before-colon 0 plus-pos))
                           (context (substring before-colon (+ plus-pos 1)))
                           ;; Check for {caps}
                           (brace-pos (string-index context #\{)))
                      (if (not brace-pos)
                          ;; Role only: +role
                          (make-address principal context '() path)
                          ;; Has braces
                          (let* ((role-part (if (= brace-pos 0)
                                               #f  ; +{caps} with no role
                                               (substring context 0 brace-pos)))
                                 ;; Extract contents between { and }
                                 (caps-str (let ((end (string-index context #\})))
                                            (if end
                                                (substring context (+ brace-pos 1) end)
                                                "")))
                                 (caps (parse-capabilities caps-str)))
                            (make-address principal role-part caps path))))))))))

  ;; Note: string-index from srfi-13 used for char lookup

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
      (metadata  . "Commit metadata")
      (forge     . "Compiled module metadata")
      (objects   . "User-created soup objects")))

  (define (soup? . args)
    "Show soup help and available object types (JSYS ? command)"
    (print "
SOUP - Object Store Query Syntax
─────────────────────────────────────────────────────────────

  (soup)                     Compact tree view with summaries
  (soup 'full)               Detailed listing of all objects

  (soup 'archives)           Drill down to type
  (soup 'releases)
  (soup 'certs)
  (soup 'audit)
  (soup 'keys)
  (soup 'metadata)
  (soup 'forge)

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
    (session-stat! 'reads)
    (let ((objects '()))

      ;; Archives (*.archive files in current dir)
      (when (directory-exists? ".")
        (for-each
         (lambda (f)
           (when (string-suffix? ".archive" f)
             (let ((stat (file-stat f)))
               (set! objects (cons (list 'archives f (vector-ref stat 5) (get-archive-crypto f)) objects)))))
         (directory ".")))

      ;; Releases (.vault/releases/*.sig)
      (when (directory-exists? ".vault/releases")
        (for-each
         (lambda (f)
           (when (string-suffix? ".sig" f)
             (let* ((version (pathname-strip-extension f))
                    (stat (file-stat (sprintf ".vault/releases/~a" f))))
               (set! objects (cons (list 'releases version (vector-ref stat 5) (get-release-crypto version)) objects)))))
         (directory ".vault/releases")))

      ;; Unsigned releases (git tags without .sig)
      (let ((tags (get-git-tags)))
        (for-each
         (lambda (tag)
           (unless (file-exists? (sprintf ".vault/releases/~a.sig" tag))
             (set! objects (cons (list 'releases tag 0 '("unsigned")) objects))))
         tags))

      ;; Audit entries (.vault/audit/*.sexp)
      (when (directory-exists? ".vault/audit")
        (for-each
         (lambda (f)
           (when (string-suffix? ".sexp" f)
             (let ((stat (file-stat (sprintf ".vault/audit/~a" f))))
               (set! objects (cons (list 'audit f (vector-ref stat 5) (get-audit-crypto (sprintf ".vault/audit/~a" f))) objects)))))
         (directory ".vault/audit")))

      ;; Keys (*.pub, *.key, *.age files)
      (when (directory-exists? ".")
        (for-each
         (lambda (f)
           (when (or (string-suffix? ".pub" f)
                     (string-suffix? ".key" f)
                     (string-suffix? ".age" f))
             (let ((stat (file-stat f)))
               (set! objects (cons (list 'keys f (vector-ref stat 5) (get-key-crypto f)) objects)))))
         (directory ".")))

      ;; Metadata (.vault/metadata/*.sexp)
      (when (directory-exists? ".vault/metadata")
        (for-each
         (lambda (f)
           (when (string-suffix? ".sexp" f)
             (let ((stat (file-stat (sprintf ".vault/metadata/~a" f))))
               (set! objects (cons (list 'metadata f (vector-ref stat 5) '("sexp")) objects)))))
         (directory ".vault/metadata")))

      ;; Certificates (.vault/certs/*.sexp) - membership, delegation, etc.
      (when (directory-exists? ".vault/certs")
        (for-each
         (lambda (f)
           (when (string-suffix? ".sexp" f)
             (let ((stat (file-stat (sprintf ".vault/certs/~a" f))))
               (set! objects (cons (list 'certs f (vector-ref stat 5) (get-cert-info (sprintf ".vault/certs/~a" f))) objects)))))
         (directory ".vault/certs")))

      ;; Node identity (.vault/node.sexp) - local, not replicated
      (when (file-exists? ".vault/node.sexp")
        (let ((stat (file-stat ".vault/node.sexp")))
          (set! objects (cons (list 'identity "node" (vector-ref stat 5) (get-node-info)) objects))))

      ;; Forge metadata (.forge/*.meta) - compiled module info
      (when (directory-exists? ".forge")
        (for-each
         (lambda (f)
           (when (string-suffix? ".meta" f)
             (let* ((path (sprintf ".forge/~a" f))
                    (stat (file-stat path))
                    (module (pathname-strip-extension f)))
               (set! objects (cons (list 'forge module (vector-ref stat 5) (get-forge-info path)) objects)))))
         (directory ".forge")))

      ;; Soup objects (.vault/soup/*.sexp) - user-created objects with lifetimes
      (when (directory-exists? ".vault/soup")
        (for-each
         (lambda (f)
           (when (string-suffix? ".sexp" f)
             (let* ((path (sprintf ".vault/soup/~a" f))
                    (stat (file-stat path))
                    (id (pathname-strip-extension f)))
               (set! objects (cons (list 'objects id (vector-ref stat 5) (get-soup-object-info path)) objects)))))
         (directory ".vault/soup")))

      (reverse objects)))

  (define (get-node-info)
    "Extract node identity attributes for soup listing"
    (handle-exceptions exn
      '("unknown")
      (let ((data (with-input-from-file ".vault/node.sexp" read)))
        (if (and (pair? data) (eq? 'node-identity (car data)))
            (let* ((fields (cdr data))
                   (name (assq 'name fields))
                   (role (assq 'role fields)))
              (list (if name (cadr name) "unknown")
                    (if role (symbol->string (cadr role)) "unknown")))
            '("invalid")))))

  (define (get-node-identity)
    "Get full node identity for inspection"
    (handle-exceptions exn
      #f
      (let ((data (with-input-from-file ".vault/node.sexp" read)))
        (if (and (pair? data) (eq? 'node-identity (car data)))
            (cdr data)
            #f))))

  (define (get-soup-object-info path)
    "Extract soup object attributes for listing"
    (handle-exceptions exn
      '("unknown")
      (let ((data (with-input-from-file path read)))
        (if (and (pair? data) (eq? 'soup-object (car data)))
            (let* ((fields (cdr data))
                   (lifetime (assq 'lifetime fields))
                   (expires (assq 'expires fields))
                   (tags (assq 'tags fields))
                   (now (current-seconds))
                   (remaining (if expires
                                  (max 0 (- (cadr expires) now))
                                  0))
                   (days (quotient remaining 86400)))
              (list (if lifetime (symbol->string (cadr lifetime)) "?")
                    (sprintf "~ad" days)
                    (if (and tags (pair? (cadr tags)))
                        (string-intersperse (map symbol->string (cadr tags)) ",")
                        "")))
            '("invalid")))))

  (define (get-cert-info path)
    "Extract certificate attributes for soup listing"
    (handle-exceptions exn
      '("unknown")
      (let ((data (with-input-from-file path read)))
        (if (and (pair? data) (eq? 'signed-enrollment-cert (car data)))
            (let* ((body (cadr data))
                   (body-fields (if (and (pair? body) (eq? 'spki-cert (car body)))
                                    (cdr body)
                                    '()))
                   (name (assq 'name body-fields))
                   (role (assq 'role body-fields))
                   (validity (assq 'validity body-fields))
                   (not-after (and validity (assq 'not-after (cdr validity)))))
              (list (if name (symbol->string (cadr name)) "?")
                    (if role (symbol->string (cadr role)) "?")
                    (if not-after
                        (let ((remaining (- (cadr not-after) (current-seconds))))
                          (if (> remaining 0)
                              (sprintf "~ad" (quotient remaining 86400))
                              "expired"))
                        "no-expiry")))
            '("not-enrollment-cert")))))

  (define (get-forge-info path)
    "Extract forge metadata attributes for soup listing"
    (handle-exceptions exn
      '("unknown")
      (let ((data (with-input-from-file path read)))
        (if (pair? data)
            (let* ((metrics (assq 'metrics data))
                   (loc (and metrics (assq 'loc (cdr metrics))))
                   (lambdas (and metrics (assq 'lambdas (cdr metrics))))
                   (loc/lambda (and metrics (assq 'loc/lambda (cdr metrics))))
                   (so-size (assq 'so-size data))
                   (compile-ms (assq 'compile-time-ms data)))
              (list (if loc (sprintf "~aL" (cdr loc)) "?")
                    (if lambdas (sprintf "~aλ" (cdr lambdas)) "?")
                    (if loc/lambda (sprintf "~a/λ" (cdr loc/lambda)) "?")
                    (if so-size (format-size (cdr so-size)) "?")))
            '("invalid")))))

  (define (get-archive-crypto path)
    "Extract crypto attributes from archive manifest"
    (handle-exceptions exn
      '("unknown")
      (let ((manifest (with-input-from-file path read)))
        (if (and (pair? manifest) (eq? 'sealed-archive (car manifest)))
            (let* ((fields (cdr manifest))
                   (fmt (assq 'format fields))
                   (hash (assq 'hash fields))
                   (ts (assq 'timestamp fields))
                   (format-sym (if fmt (cadr fmt) 'unknown))
                   (attrs (case format-sym
                            ((zstd-age) '("age" "zstd" "sha256"))
                            ((cryptographic) '("gzip" "sha256"))
                            ((tarball) '("tar" "gzip"))
                            ((bundle) '("git-bundle"))
                            (else '("unknown")))))
              (append attrs
                      (if hash (list (sprintf "~a.." (substring (cadr hash) 0 8))) '())
                      (if ts (list (format-timestamp (cadr ts))) '())))
            '("unknown")))))

  (define (get-release-crypto version)
    "Extract crypto attributes from signed release"
    (let ((sig-file (sprintf ".vault/releases/~a.sig" version)))
      (if (file-exists? sig-file)
          (handle-exceptions exn
            '("ed25519" "sha512")
            (let* ((sig-data (with-input-from-file sig-file read))
                   (hash (assq 'hash (cdr sig-data))))
              (append '("ed25519" "sha512")
                      (if hash (list (sprintf "~a.." (substring (cadr hash) 0 8))) '()))))
          '("unsigned"))))

  (define (byte->hex b)
    "Convert byte to 2-char hex string"
    (let ((hex "0123456789abcdef"))
      (string (string-ref hex (quotient b 16))
              (string-ref hex (remainder b 16)))))

  (define (bytes->hex bytes n)
    "Convert first n bytes to hex string"
    (apply string-append
           (map (lambda (i)
                  (byte->hex (char->integer (string-ref bytes i))))
                (iota (min n (string-length bytes))))))

  (define (extract-identity path)
    "Extract identity from key filename (e.g., alice.pub -> alice)"
    (pathname-strip-extension (pathname-file path)))

  (define (get-key-crypto path)
    "Extract crypto attributes from key file"
    (handle-exceptions exn
      '("unknown")
      (let* ((stat (file-stat path))
             (mtime (vector-ref stat 8))
             (size (vector-ref stat 5))
             (date (format-timestamp mtime))
             (identity (extract-identity path))
             (content (with-input-from-file path read-string))
             (key-bytes (string-length content))
             ;; Compute sha256 fingerprint of full key
             (key-hash-blob (sha256-hash content))
             (key-hash-bytes (blob->string key-hash-blob))
             (fp-hex (bytes->hex key-hash-bytes 8)))
        (cond
         ((string-suffix? ".pub" path)
          (list "ed25519/256" "public" "sign"
                (sprintf "sha256:~a.." fp-hex)
                (sprintf "id:~a" identity)
                date))
         ((string-suffix? ".key" path)
          (list "ed25519/256" "private" "sign"
                (sprintf "sha256:~a.." fp-hex)
                (sprintf "id:~a" identity)
                date))
         ((string-suffix? ".age" path)
          (list "x25519/256" "age" "encrypt"
                (sprintf "sha256:~a.." fp-hex)
                (sprintf "id:~a" identity)
                date))
         (else '("unknown"))))))

  (define (get-audit-crypto path)
    "Extract crypto attributes from audit entry"
    (handle-exceptions exn
      '("entry")
      (let ((entry (with-input-from-file path read)))
        (if (and (pair? entry) (pair? (cdr entry)))
            (let* ((fields (cdr entry))
                   (seal (assq 'seal fields))
                   (ts (assq 'timestamp fields))
                   (id (assq 'id fields)))
              (append
               (if seal '("ed25519" "sha512" "sealed") '("entry"))
               (if (and id (> (string-length (cadr id)) 8))
                   (list (sprintf "~a.." (substring (cadr id) 0 8)))
                   '())
               (if ts (list (format-timestamp (cadr ts))) '())))
            '("entry")))))

  (define (format-timestamp ts)
    "Format timestamp for display"
    (handle-exceptions exn
      ""
      (let ((t (if (number? ts) ts (string->number ts))))
        (if t
            (time->string (seconds->local-time t) "%Y-%m-%d")
            ""))))

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

  ;;; ============================================================================
  ;;; Soup Tree View - Compact display with smart summaries
  ;;; ============================================================================

  (define (pad-left str len #!optional (char #\space))
    "Pad string on left to given length"
    (let ((slen (string-length str)))
      (if (>= slen len)
          str
          (string-append (make-string (- len slen) char) str))))

  ;; Sparkline characters (Unicode block elements, as strings for UTF-8)
  (define *sparkline-chars* '#("▁" "▂" "▃" "▄" "▅" "▆" "▇" "█"))

  (define (sparkline values width)
    "Generate ASCII sparkline from values (list of numbers)"
    (if (or (null? values) (every zero? values))
        (make-string width #\─)
        (let* ((max-val (apply max values))
               (scale (if (zero? max-val) 1 (/ 7.0 max-val))))
          (apply string-append
                 (map (lambda (v)
                        (vector-ref *sparkline-chars*
                                    (inexact->exact (min 7 (floor (* v scale))))))
                      (take-right-pad values width 0))))))

  (define (take-right-pad lst n default)
    "Take last n elements, pad with default if needed"
    (let ((len (length lst)))
      (if (>= len n)
          (take-right lst n)
          (append (make-list (- n len) default) lst))))

  (define (soup-summary-archives objs)
    "Smart summary for archives"
    (if (null? objs)
        ""
        (let ((total (apply + (map caddr objs))))
          (format-size total))))

  (define (soup-summary-releases objs)
    "Smart summary for releases - signed vs unsigned"
    (if (null? objs)
        ""
        (let* ((signed (filter (lambda (o)
                                 (let ((info (cadddr o)))
                                   (not (member "unsigned" (if (list? info) info '())))))
                               objs))
               (unsigned (- (length objs) (length signed))))
          (cond
           ((zero? unsigned) (sprintf "~a signed" (length signed)))
           ((zero? (length signed)) "unsigned")
           (else (sprintf "~a signed, ~a pending" (length signed) unsigned))))))

  (define (soup-summary-audit objs)
    "Smart summary for audit - sparkline of activity"
    (if (null? objs)
        ""
        (let* ((now (current-seconds))
               (buckets 8)
               (bucket-size 3600)  ; 1 hour per bucket
               (counts (make-vector buckets 0)))
          ;; Extract timestamps and bucket them
          (for-each
           (lambda (o)
             (let* ((name (cadr o))
                    ;; Extract timestamp from sync-TIMESTAMP.sexp
                    (ts-match (irregex-search "sync-([0-9]+)" name)))
               (when ts-match
                 (let* ((ts (string->number (irregex-match-substring ts-match 1)))
                        (age (- now ts))
                        (bucket (min (- buckets 1) (max 0 (quotient age bucket-size)))))
                   (vector-set! counts bucket (+ 1 (vector-ref counts bucket)))))))
           objs)
          ;; Reverse so newest is on right
          (let ((vals (reverse (vector->list counts))))
            (sprintf "~a (~ah)" (sparkline vals buckets) (* buckets (/ bucket-size 3600)))))))

  (define (soup-summary-keys objs)
    "Smart summary for keys - identity names"
    (if (null? objs)
        ""
        (let* ((identities (filter-map
                            (lambda (o)
                              (let* ((info (cadddr o))
                                     (id-str (find (lambda (s)
                                                     (and (string? s)
                                                          (string-prefix? "id:" s)))
                                                   (if (list? info) info '()))))
                                (and id-str (substring id-str 3))))
                            objs))
               (unique (delete-duplicates identities)))
          (if (<= (length unique) 4)
              (string-intersperse unique ", ")
              (sprintf "~a identities" (length unique))))))

  (define (soup-summary-metadata objs)
    "Smart summary for metadata"
    (if (null? objs)
        ""
        (sprintf "~a entries" (length objs))))

  (define (soup-summary-certs objs)
    "Smart summary for certificates"
    (if (null? objs)
        ""
        (sprintf "~a certs" (length objs))))

  (define (soup-summary-identity objs)
    "Smart summary for identity"
    (if (null? objs)
        ""
        (let ((info (cadddr (car objs))))
          (if (and (list? info) (>= (length info) 2))
              (sprintf "~a (~a)" (car info) (cadr info))
              "configured"))))

  (define (soup-summary-forge objs)
    "Smart summary for forge metadata - total LOC and average λ-density"
    (if (null? objs)
        ""
        (let* ((total-loc 0)
               (total-lambdas 0))
          ;; Sum up LOC and lambdas from info lists
          (for-each
           (lambda (o)
             (let ((info (cadddr o)))
               (when (and (list? info) (>= (length info) 2))
                 (let ((loc-str (car info))
                       (lambda-str (cadr info)))
                   (when (string-suffix? "L" loc-str)
                     (set! total-loc (+ total-loc
                                        (or (string->number (substring loc-str 0 (- (string-length loc-str) 1))) 0))))
                   (when (string-suffix? "λ" lambda-str)
                     (set! total-lambdas (+ total-lambdas
                                            (or (string->number (substring lambda-str 0 (- (string-length lambda-str) 2))) 0))))))))
           objs)
          (if (> total-lambdas 0)
              (sprintf "~aL ~aλ (~a/λ)" total-loc total-lambdas (quotient total-loc total-lambdas))
              (sprintf "~a modules" (length objs))))))

  (define (soup-get-summary type objs)
    "Get smart summary for a type"
    (case type
      ((archives) (soup-summary-archives objs))
      ((releases) (soup-summary-releases objs))
      ((audit) (soup-summary-audit objs))
      ((keys) (soup-summary-keys objs))
      ((metadata) (soup-summary-metadata objs))
      ((certs) (soup-summary-certs objs))
      ((identity) (soup-summary-identity objs))
      ((forge) (soup-summary-forge objs))
      (else "")))

  (define (soup-tree-view grouped types)
    "Display compact tree view of soup"
    (let* ((non-empty (filter (lambda (t)
                                (not (null? (hash-table-ref/default grouped (car t) '()))))
                              types))
           (total (apply + (map (lambda (t)
                                  (length (hash-table-ref/default grouped (car t) '())))
                                types)))
           (last-idx (- (length non-empty) 1)))
      (if (zero? total)
          (let ((name (realm-name)))
            (if name
                (printf "~%Empty (realm: ~a)~%" name)
                (printf "~%Empty~%")))
          (begin
            (printf "~%Soup~%")
            (let loop ((remaining non-empty) (idx 0))
        (unless (null? remaining)
          (let* ((type-pair (car remaining))
                 (type (car type-pair))
                 (objs (reverse (hash-table-ref/default grouped type '())))
                 (count (length objs))
                 (summary (soup-get-summary type objs))
                 (branch (if (= idx last-idx) "└─" "├─"))
                 (type-str (symbol->string type))
                 (padding (make-string (max 1 (- 12 (string-length type-str))) #\space)))
            (printf "~a ~a/~a~a~a~a~%"
                    branch
                    type-str
                    padding
                    (pad-left (number->string count) 3)
                    (if (string=? summary "") "" "   ")
                    summary))
          (loop (cdr remaining) (+ idx 1))))))))

  (define (soup . args)
    "List objects in the soup with optional type filter and pattern

     (soup)                   - compact tree view
     (soup 'full)             - detailed listing of all objects
     (soup 'archives)         - drill down to type
     (soup \"pattern\")         - glob pattern (* ?)
     (soup 'type \"pat\")       - type + pattern
     (soup #/regex/)          - regex match"

    (let ((type-filter #f)
          (pattern #f)
          (full-view #f))

      ;; Parse arguments
      (for-each
       (lambda (arg)
         (cond
          ((eq? arg 'full) (set! full-view #t))
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

          ;; Include identity type in the types list for display
          (let ((all-types (append *soup-types* '((identity . "Node identity")))))

            ;; Compact tree view (no args) vs detailed view (type/pattern/full)
            (if (and (not type-filter) (not pattern) (not full-view))
                ;; Compact tree view
                (soup-tree-view grouped all-types)

                ;; Detailed view
                (let ((width 60)
                      (count (length filtered)))
                  (print "")
                  (print (repeat-string "─" width))
                  (printf " Soup Directory  ~a object~a~%"
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
                             ;; Only columnify if 4+ items
                             (let* ((use-cols (>= (length objs) 4))
                                    (max-name (if use-cols
                                                  (apply max (map (lambda (o) (string-length (cadr o))) objs))
                                                  0)))
                               (for-each
                                (lambda (obj)
                                  (let ((name (cadr obj))
                                        (size (caddr obj))
                                        (info (cadddr obj)))
                                    (let ((attrs (if (list? info)
                                                      (string-intersperse info " ")
                                                      info)))
                                      (if use-cols
                                          (printf "   ~a,~a ~a, ~a~%"
                                                  name
                                                  (make-string (- max-name (string-length name)) #\space)
                                                  (format-size size)
                                                  attrs)
                                          (printf "   ~a, ~a, ~a~%"
                                                  name
                                                  (format-size size)
                                                  attrs)))))
                                objs)))))
                       all-types))

                  (print "")
                  (print (repeat-string "─" width)))))))))

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
  ;;; Extended Soup Introspection
  ;;; ============================================================================

  (define (soup-stat name)
    "Detailed status of a soup object (like stat(1))"
    (let* ((all-objects (soup-collect-objects))
           (obj (find (lambda (o) (equal? (cadr o) name)) all-objects))
           (w 58))  ; box width
      ;; Local helpers using vault-box-line for proper Unicode handling
      (define (line content) (print (vault-box-line content w)))
      (define (field label value)
        (line (sprintf "~a~a~a"
                       label
                       (make-string (max 1 (- 12 (string-display-width label))) #\space)
                       value)))
      (if (not obj)
          (print "Object not found: " name)
          (let ((type (car obj))
                (size (caddr obj))
                (info (cadddr obj)))
            (print "")
            (print (vault-box-top w))
            (line name)
            (print (vault-box-divider w))
            (field "Type:" (symbol->string type))
            (field "Size:" (format-size size))

            ;; Type-specific details
            (case type
              ((releases)
               (let* ((tag-commit (get-tag-commit name))
                      (sig-file (sprintf ".vault/releases/~a.sig" name))
                      (has-sig (file-exists? sig-file))
                      (archive-file (find-archive-for-release name))
                      (has-archive (and archive-file (file-exists? archive-file))))
                 (field "Git Tag:" (if tag-commit "yes" "no"))
                 (when tag-commit
                   (field "Commit:" (string-append (substring tag-commit 0 12) "..")))
                 (field "Signed:" (if has-sig "yes" "no"))
                 (when has-sig
                   (field "Sig File:" sig-file))
                 (field "Archived:" (if has-archive "yes" "no"))
                 (when has-archive
                   (let ((arch-stat (file-stat archive-file)))
                     (field "Archive:" (sprintf "~a (~a)" archive-file
                                                (format-size (vector-ref arch-stat 5))))))))

              ((archives)
               (let* ((path name)
                      (hash (soup-hash-file path)))
                 (field "Path:" path)
                 (field "SHA-512:" (string-append (substring hash 0 24) ".."))
                 (let ((manifest (get-archive-manifest path)))
                   (when manifest
                     (let ((fmt (assq 'format manifest))
                           (ts (assq 'timestamp manifest)))
                       (when fmt
                         (field "Format:" (symbol->string (cadr fmt))))
                       (when ts
                         (field "Created:" (format-timestamp (cadr ts)))))))))

              ((keys)
               (let* ((hash (soup-hash-file name))
                      (fp (substring hash 0 16)))
                 (field "Fingerprint:" (string-append "sha512:" fp ".."))
                 (field "Algorithm:" (cond ((string-suffix? ".pub" name) "Ed25519 public")
                                           ((string-suffix? ".key" name) "Ed25519 private")
                                           ((string-suffix? ".age" name) "X25519 age")
                                           (else "unknown")))))

              ((audit)
               (let ((entry (get-audit-entry name)))
                 (when entry
                   (let ((id (assq 'id entry))
                         (action (assq 'action entry))
                         (ts (assq 'timestamp entry)))
                     (when id
                       (field "ID:" (cadr id)))
                     (when action
                       (field "Action:" (sprintf "~a" (cadr action))))
                     (when ts
                       (field "Timestamp:" (format-timestamp (cadr ts))))))))

              ((identity)
               (let* ((node-data (get-node-identity))
                      (name-f (and node-data (assq 'name node-data)))
                      (role (and node-data (assq 'role node-data)))
                      (hw (and node-data (assq 'hardware node-data))))
                 (when name-f
                   (field "Node:" (cadr name-f)))
                 (when role
                   (field "Role:" (symbol->string (cadr role))))
                 (when hw
                   (let ((hw-list (if (pair? (cdr hw)) (cadr hw) '())))
                     (when (and (list? hw-list) (assq 'cpu hw-list))
                       (field "CPU:" (cadr (assq 'cpu hw-list))))
                     (when (and (list? hw-list) (assq 'memory-gb hw-list))
                       (field "Memory:" (sprintf "~aGB" (cadr (assq 'memory-gb hw-list))))))))))

            (print (vault-box-bottom w))
            (print "")))))

  (define (soup-hash-file path)
    "Compute SHA-512 hash of file (legacy)"
    (handle-exceptions exn
      "error"
      (let ((content (with-input-from-file path (lambda () (read-string)))))
        (blob->hex (sha512-hash (string->blob content))))))

  (define (soup-merkle-hash-file path)
    "Compute Merkle root hash of file (quantum-resistant, Memo-047)"
    (handle-exceptions exn
      "error"
      (let ((content (with-input-from-file path (lambda () (read-string)))))
        (blob->hex (merkle-root (string->blob content))))))

  (define (soup-dual-hash-file path)
    "Compute both SHA-512 and Merkle root hashes (transition period, Memo-047)"
    (handle-exceptions exn
      (cons "error" "error")
      (let* ((content (with-input-from-file path (lambda () (read-string))))
             (hashes (dual-hash (string->blob content))))
        (cons (blob->hex (car hashes))
              (blob->hex (cdr hashes))))))

  (define (soup-prove-chunk path chunk-index)
    "Generate inclusion proof for a chunk of a file (Memo-047)
     Returns merkle-proof or #f if index invalid"
    (handle-exceptions exn #f
      (let ((content (with-input-from-file path (lambda () (read-string)))))
        (merkle-prove (string->blob content) chunk-index))))

  (define (soup-verify-chunk path chunk-index proof)
    "Verify inclusion proof against a file's Merkle root (Memo-047)
     Returns #t if chunk is proven to be part of the file"
    (handle-exceptions exn #f
      (let* ((content (with-input-from-file path (lambda () (read-string))))
             (root (merkle-root (string->blob content))))
        (and (= chunk-index (merkle-proof-chunk-index proof))
             (merkle-verify-proof root proof)))))

  (define (blob->hex b)
    "Convert blob to hex string"
    (let ((vec (blob->u8vector b)))
      (apply string-append
             (map (lambda (i)
                    (let ((byte (u8vector-ref vec i)))
                      (string-append
                       (string (string-ref "0123456789abcdef" (quotient byte 16)))
                       (string (string-ref "0123456789abcdef" (remainder byte 16))))))
                  (iota (u8vector-length vec))))))

  (define (hex-abbrev hex #!optional (prefix-bytes 4) (suffix-bytes 4))
    "Abbreviate long hex string: 0xAAAA...0xBBBB (network byte order preserved)
     For human display of long binary blobs. Always 8 hex chars per side."
    (let ((prefix-chars (* prefix-bytes 2))
          (suffix-chars (* suffix-bytes 2))
          (len (string-length hex)))
      (if (<= len (+ prefix-chars suffix-chars 4))
          hex  ; Short enough, no abbreviation needed
          (string-append
           "0x" (substring hex 0 prefix-chars)
           "..."
           "0x" (substring hex (- len suffix-chars) len)))))

  (define (get-tag-commit tag)
    "Get commit hash for a git tag"
    (handle-exceptions exn #f
      (with-input-from-pipe (sprintf "git rev-list -n1 ~a 2>/dev/null" tag) read-line)))

  (define (find-archive-for-release version)
    "Find archive file for a release version"
    (let ((patterns (list (sprintf "vault-~a.archive" version)
                          (sprintf "~a.archive" version)
                          (sprintf "genesis-~a.archive" version))))
      (find file-exists? patterns)))

  (define (get-archive-manifest path)
    "Read archive manifest if it's a sealed archive"
    (handle-exceptions exn #f
      (let ((data (with-input-from-file path read)))
        (if (and (pair? data) (eq? 'sealed-archive (car data)))
            (cdr data)
            #f))))

  (define (get-audit-entry name)
    "Read audit entry from file"
    (handle-exceptions exn #f
      (let ((path (if (string-prefix? ".vault/audit/" name)
                      name
                      (sprintf ".vault/audit/~a" name))))
        (let ((data (with-input-from-file path read)))
          (if (pair? data) (cdr data) #f)))))

  (define (soup-hash name)
    "Compute and display hashes of an object (SHA-512 + Merkle root)"
    (session-stat! 'hashes)
    (let* ((all-objects (soup-collect-objects))
           (obj (find (lambda (o) (equal? (cadr o) name)) all-objects)))
      (if (not obj)
          (print "Object not found: " name)
          (let ((type (car obj))
                (path (case (car obj)
                        ((archives keys) name)
                        ((releases) (sprintf ".vault/releases/~a.sig" name))
                        ((audit) (sprintf ".vault/audit/~a" name))
                        (else name))))
            (if (file-exists? path)
                (let ((hashes (soup-dual-hash-file path)))
                  (print "")
                  (printf "sha512:~a~%" (car hashes))   ; Legacy
                  (printf "shake256:~a~%" (cdr hashes)) ; Quantum-resistant (Memo-047)
                  (printf "  ~a (~a)~%" name (format-size (caddr obj)))
                  (print "")
                  (car hashes))  ; Return legacy hash for compatibility
                (print "File not found: " path))))))

  (define (soup-releases)
    "Detailed view of all releases with status"
    (let* ((tags (get-git-tags))
           (max-tag-len (if (null? tags) 10 (apply max (map string-length tags))))
           (col-width (max 20 (+ max-tag-len 3))))
      (print "")
      (print "╭────────────────────────────────────────────────────────────────────────────╮")
      (print "│ Releases                                                                   │")
      (print "├────────────────────────────────────────────────────────────────────────────┤")
      (printf "│ ~a~aCommit       Signed  Archived  Date       │~%"
              "Version"
              (make-string (- col-width 7) #\space))
      (print "├────────────────────────────────────────────────────────────────────────────┤")

      (for-each
       (lambda (tag)
         (let* ((commit (get-tag-commit tag))
                (commit-short (if commit (substring commit 0 8) "--------"))
                (sig-file (sprintf ".vault/releases/~a.sig" tag))
                (has-sig (file-exists? sig-file))
                (archive (find-archive-for-release tag))
                (has-archive (and archive (file-exists? archive)))
                (date (or (get-tag-date tag) "          ")))
           (printf "│ ~a~a~a    ~a       ~a         ~a │~%"
                   tag
                   (make-string (- col-width (string-length tag)) #\space)
                   commit-short
                   (if has-sig "✓" "✗")
                   (if has-archive "✓" "✗")
                   date)))
       (sort tags string>?))

      (print "╰────────────────────────────────────────────────────────────────────────────╯")
      (print "")))

  (define (get-tag-date tag)
    "Get creation date of git tag"
    (handle-exceptions exn #f
      (let ((ts (with-input-from-pipe
                 (sprintf "git log -1 --format=%ct ~a 2>/dev/null" tag)
                 read-line)))
        (if (and ts (not (eof-object? ts)))
            (format-timestamp (string->number ts))
            #f))))

  (define (soup-du)
    "Disk usage summary (like du(1))"
    (let ((all-objects (soup-collect-objects))
          (by-type (make-hash-table))
          (total 0)
          (w 42))  ; box width
      (define (line content) (print (vault-box-line content w)))
      (define (row size label)
        (let ((size-str (format-size size)))
          (line (sprintf "~a~a~a"
                         size-str
                         (make-string (max 1 (- 10 (string-display-width size-str))) #\space)
                         label))))

      ;; Sum by type
      (for-each
       (lambda (obj)
         (let ((type (car obj))
               (size (caddr obj)))
           (set! total (+ total size))
           (hash-table-set! by-type type
                            (+ size (hash-table-ref/default by-type type 0)))))
       all-objects)

      (print "")
      (print (vault-box-top w))
      (line "Soup Disk Usage")
      (print (vault-box-divider w))

      (for-each
       (lambda (type)
         (let ((size (hash-table-ref/default by-type type 0)))
           (when (> size 0)
             (row size (symbol->string type)))))
       '(archives releases keys audit metadata identity))

      (print (vault-box-divider w))
      (row total "TOTAL")
      (print (vault-box-bottom w))
      (print "")))

  (define (soup-find . criteria)
    "Find objects matching criteria
     (soup-find size: '> 1000000)      - larger than 1MB
     (soup-find type: 'archives)       - by type
     (soup-find name: \"*2.0*\")         - by name pattern
     (soup-find signed: #t)            - signed releases only
     (soup-find hash: \"abc123\")        - by hash prefix"
    (let ((all-objects (soup-collect-objects))
          (type-filter #f)
          (size-filter #f)
          (name-filter #f)
          (signed-filter #f)
          (hash-filter #f))

      ;; Parse keyword args
      (let loop ((args criteria))
        (unless (null? args)
          (case (car args)
            ((type:) (set! type-filter (cadr args)) (loop (cddr args)))
            ((size:) (set! size-filter (cadr args)) (loop (cddr args)))
            ((name:) (set! name-filter (cadr args)) (loop (cddr args)))
            ((signed:) (set! signed-filter (cadr args)) (loop (cddr args)))
            ((hash:) (set! hash-filter (cadr args)) (loop (cddr args)))
            (else (loop (cdr args))))))

      ;; Filter
      (let ((results
             (filter
              (lambda (obj)
                (let ((type (car obj))
                      (name (cadr obj))
                      (size (caddr obj))
                      (info (cadddr obj)))
                  (and (or (not type-filter) (eq? type type-filter))
                       (or (not size-filter)
                           (case (car size-filter)
                             ((>) (> size (cadr size-filter)))
                             ((<) (< size (cadr size-filter)))
                             ((=) (= size (cadr size-filter)))
                             (else #t)))
                       (or (not name-filter) (match-pattern? name name-filter))
                       (or (not signed-filter)
                           (if signed-filter
                               (not (member "unsigned" info))
                               (member "unsigned" info))))))
              all-objects)))

        ;; Display results
        (print "")
        (printf "Found ~a object~a:~%" (length results) (if (= 1 (length results)) "" "s"))
        (for-each
         (lambda (obj)
           (printf "  ~a/~a (~a)~%" (car obj) (cadr obj) (format-size (caddr obj))))
         results)
        (print "")
        results)))

  ;;; ============================================================================
  ;;; soup-query - S-expression pattern matching (Newton-style)
  ;;; ============================================================================
  ;;;
  ;;; Query syntax:
  ;;;   (soup-query '(type archives))           - by type
  ;;;   (soup-query '(name "*.tar.gz"))         - glob pattern
  ;;;   (soup-query '(name #/regex/))           - regex pattern
  ;;;   (soup-query '(size > 1000000))          - size comparison
  ;;;   (soup-query '(signed))                  - signed objects
  ;;;   (soup-query '(not (signed)))            - unsigned objects
  ;;;   (soup-query '(and (type releases)       - compound query
  ;;;                     (size > 1000)))
  ;;;   (soup-query '(or (name "*.archive")
  ;;;                    (name "*.tar.gz")))
  ;;;   (soup-query '(has-field principal))     - objects with field
  ;;;
  ;;; Returns list of matching objects.

  (define (soup-query query #!optional (silent #f))
    "Query soup using S-expression patterns (Newton-style)

     Patterns:
       (type TYPE)              - match object type
       (name PATTERN)           - glob or regex on name
       (size OP VALUE)          - size comparison (> < = >= <=)
       (signed)                 - has signature
       (has-field FIELD)        - object has field in info
       (and PATTERN ...)        - all patterns must match
       (or PATTERN ...)         - any pattern must match
       (not PATTERN)            - pattern must not match

     Examples:
       (soup-query '(type archives))
       (soup-query '(and (type releases) (signed)))
       (soup-query '(or (name \"*.archive\") (name \"*.tar.gz\")))
       (soup-query '(size > 1000000))"
    (session-stat! 'queries)

    (define (eval-query pattern obj)
      "Evaluate query pattern against object"
      (let ((type (car obj))
            (name (cadr obj))
            (size (caddr obj))
            (info (cadddr obj)))
        (cond
         ;; Type match
         ((and (pair? pattern) (eq? (car pattern) 'type))
          (eq? type (cadr pattern)))

         ;; Name pattern (glob or regex)
         ((and (pair? pattern) (eq? (car pattern) 'name))
          (match-pattern? name (cadr pattern)))

         ;; Size comparison
         ((and (pair? pattern) (eq? (car pattern) 'size))
          (let ((op (cadr pattern))
                (val (caddr pattern)))
            (case op
              ((>) (> size val))
              ((<) (< size val))
              ((=) (= size val))
              ((>=) (>= size val))
              ((<=) (<= size val))
              (else #f))))

         ;; Signed check
         ((and (pair? pattern) (eq? (car pattern) 'signed))
          (not (member "unsigned" info)))

         ;; Unsigned check (sugar)
         ((and (pair? pattern) (eq? (car pattern) 'unsigned))
          (member "unsigned" info))

         ;; Has field check
         ((and (pair? pattern) (eq? (car pattern) 'has-field))
          (member (symbol->string (cadr pattern)) info))

         ;; AND - all must match
         ((and (pair? pattern) (eq? (car pattern) 'and))
          (every (lambda (p) (eval-query p obj)) (cdr pattern)))

         ;; OR - any must match
         ((and (pair? pattern) (eq? (car pattern) 'or))
          (any (lambda (p) (eval-query p obj)) (cdr pattern)))

         ;; NOT - must not match
         ((and (pair? pattern) (eq? (car pattern) 'not))
          (not (eval-query (cadr pattern) obj)))

         ;; Type shorthand - bare symbol matches type
         ((symbol? pattern)
          (eq? type pattern))

         ;; String shorthand - matches name
         ((string? pattern)
          (match-pattern? name pattern))

         ;; Unknown pattern
         (else
          (print "Warning: unknown query pattern: " pattern)
          #f))))

    (let* ((all-objects (soup-collect-objects))
           (results (filter (lambda (obj) (eval-query query obj)) all-objects)))

      (unless silent
        (print "")
        (printf "Query: ~s~%" query)
        (printf "Found ~a object~a:~%" (length results) (if (= 1 (length results)) "" "s"))
        (for-each
         (lambda (obj)
           (printf "  ~a/~a (~a)~%" (car obj) (cadr obj) (format-size (caddr obj))))
         results)
        (print ""))

      results))

  (define (gzip-file? path)
    "Check if file has gzip magic bytes (1f 8b)"
    (handle-exceptions exn #f
      (call-with-input-file path
        (lambda (port)
          (let ((b1 (read-byte port))
                (b2 (read-byte port)))
            (and (= b1 #x1f) (= b2 #x8b)))))))

  (define (soup-inspect name)
    "Interactive object inspector - returns a procedure for subcommands
     Usage:
       (define i (soup-inspect \"2.0.0\"))
       (i 'help)     - show available commands
       (i 'stat)     - detailed status
       (i 'view)     - view content
       (i 'hash)     - show SHA-512 hash
       (i 'verify)   - verify integrity/signature
       (i 'export)   - export to file
       (i 'history)  - show related audit entries"
    (let* ((all-objects (soup-collect-objects))
           (obj (find (lambda (o) (equal? (cadr o) name)) all-objects)))
      (if (not obj)
          (begin
            (print "Object not found: " name)
            #f)
          (let* ((type (car obj))
                 (size (caddr obj))
                 (info (cadddr obj))
                 (path (case type
                         ((archives keys) name)
                         ((releases) (or (find-archive-for-release name)
                                        (sprintf ".vault/releases/~a.sig" name)))
                         ((audit) (sprintf ".vault/audit/~a" name))
                         ((metadata) name)
                         (else name))))

            ;; Show entry banner
            (let ((w 61))
              (define (line content) (print (vault-box-line content w)))
              (print "")
              (print (vault-box-top w))
              (line (sprintf "Inspector: ~a" name))
              (line (sprintf "Type: ~a   Size: ~a" type (format-size size)))
              (print (vault-box-divider w))
              (line "Commands: 'help 'stat 'view 'hash 'verify 'export 'history")
              (print (vault-box-bottom w))
              (print ""))

            ;; Return inspector closure
            (lambda (cmd . args)
              (case cmd
                ((help ?)
                 (print "")
                 (print "Inspector commands:")
                 (print "  'stat     - detailed object status")
                 (print "  'view     - view content (first 50 lines)")
                 (print "  'view-all - view entire content")
                 (print "  'hash     - compute SHA-512 hash")
                 (print "  'verify   - verify integrity/signature")
                 (print "  'export   - export to file")
                 (print "  'history  - related audit entries")
                 (print "  'path     - show filesystem path")
                 (print "  'raw      - return raw S-expression data")
                 (print ""))

                ((stat)
                 (soup-stat name))

                ((hash)
                 (if (file-exists? path)
                     (let ((hash (soup-hash-file path)))
                       (print "")
                       (printf "sha512:~a~%" (hex-abbrev hash))
                       (printf "       ~a~%" hash)
                       (print "")
                       hash)
                     (print "No file at path: " path)))

                ((view)
                 (if (file-exists? path)
                     (let ((is-binary (or (string-suffix? ".tar.gz" path)
                                         (string-suffix? ".tar.zst" path)
                                         (string-suffix? ".age" path)
                                         (string-suffix? ".key" path)
                                         (string-suffix? ".pub" path)
                                         ;; Check for gzip magic in .archive files
                                         (and (string-suffix? ".archive" path)
                                              (gzip-file? path)))))
                       (if is-binary
                           (begin
                             (print "")
                             (print "Binary file - use 'raw or 'hash instead")
                             (print ""))
                           (begin
                             (print "")
                             (print "─── Content (first 50 lines) ───")
                             (handle-exceptions exn
                               (print "(error reading file - may be binary)")
                               (with-input-from-file path
                                 (lambda ()
                                   (let loop ((n 0))
                                     (let ((line (read-line)))
                                       (unless (or (eof-object? line) (>= n 50))
                                         (let ((safe-line (string-map
                                                           (lambda (c)
                                                             (if (or (char<? c #\space)
                                                                     (char>? c #\~))
                                                                 #\.
                                                                 c))
                                                           line)))
                                           (let ((num-str (number->string (+ n 1))))
                                             (printf "~a│ ~a~%"
                                                     (string-append (make-string (- 4 (string-length num-str)) #\space) num-str)
                                                     safe-line))
                                           (loop (+ n 1)))))))))
                             (print "─────────────────────────────────")
                             (print ""))))
                     (print "No file at path: " path)))

                ((view-all)
                 (if (file-exists? path)
                     (let ((is-binary (or (string-suffix? ".tar.gz" path)
                                         (string-suffix? ".tar.zst" path)
                                         (string-suffix? ".age" path)
                                         (string-suffix? ".key" path)
                                         (string-suffix? ".pub" path)
                                         (and (string-suffix? ".archive" path)
                                              (gzip-file? path)))))
                       (if is-binary
                           (begin
                             (print "")
                             (print "Binary file - use 'raw or 'hash instead")
                             (print ""))
                           (begin
                             (print "")
                             (print "─── Full Content ───")
                             (handle-exceptions exn
                               (print "(error reading file - may be binary)")
                               (with-input-from-file path
                                 (lambda ()
                                   (let loop ((n 0))
                                     (let ((line (read-line)))
                                       (unless (eof-object? line)
                                         (let ((safe-line (string-map
                                                           (lambda (c)
                                                             (if (or (char<? c #\space)
                                                                     (char>? c #\~))
                                                                 #\.
                                                                 c))
                                                           line)))
                                           (let ((num-str (number->string (+ n 1))))
                                             (printf "~a│ ~a~%"
                                                     (string-append (make-string (- 4 (string-length num-str)) #\space) num-str)
                                                     safe-line))
                                           (loop (+ n 1)))))))))
                             (print "────────────────────")
                             (print ""))))
                     (print "No file at path: " path)))

                ((verify)
                 (case type
                   ((releases)
                    (let ((version name))
                      (print "")
                      (print "Verifying release " version "...")
                      (let* ((tag-commit (get-tag-commit version))
                             (sig-file (sprintf ".vault/releases/~a.sig" version))
                             (has-sig (file-exists? sig-file))
                             (archive (find-archive-for-release version))
                             (has-archive (and archive (file-exists? archive))))
                        (printf "  Git tag:     ~a~%" (if tag-commit "✓" "✗"))
                        (printf "  Signature:   ~a~%" (if has-sig "✓" "✗"))
                        (printf "  Archive:     ~a~%" (if has-archive "✓" "✗"))
                        (when has-archive
                          (let ((manifest (get-archive-manifest archive)))
                            (when manifest
                              (let ((stored-hash (assq 'hash manifest)))
                                (when stored-hash
                                  (print "  Verifying archive hash...")
                                  (let* ((tarball (assq 'tarball manifest))
                                         (tarball-path (if tarball (cadr tarball) #f)))
                                    (if (and tarball-path (file-exists? tarball-path))
                                        (let ((computed (soup-hash-file tarball-path)))
                                          (if (string-contains computed (cadr stored-hash))
                                              (print "  Archive integrity: ✓")
                                              (print "  Archive integrity: ✗ Mismatch")))
                                        (print "  Tarball not found"))))))))
                        (print ""))))

                   ((archives)
                    (print "")
                    (print "Verifying archive " name "...")
                    (let ((manifest (get-archive-manifest name)))
                      (if manifest
                          (begin
                            (print "  Manifest: ✓")
                            (let ((hash-entry (assq 'hash manifest)))
                              (when hash-entry
                                (printf "  Stored hash: ~a...~%"
                                        (substring (cadr hash-entry) 0 32)))))
                          (print "  Not a sealed archive (no manifest)")))
                    (print ""))

                   (else
                    (print "Verification not applicable for type: " type))))

                ((export)
                 (let ((dest (if (null? args)
                                 (sprintf "/tmp/soup-export-~a" name)
                                 (car args))))
                   (if (file-exists? path)
                       (begin
                         (system (sprintf "cp ~s ~s" path dest))
                         (printf "Exported to: ~a~%" dest))
                       (print "No file to export"))))

                ((history)
                 (print "")
                 (print "Related audit entries:")
                 (let ((audit-dir ".vault/audit"))
                   (when (directory-exists? audit-dir)
                     (let ((entries (directory audit-dir)))
                       (for-each
                        (lambda (entry-file)
                          (let ((entry-path (string-append audit-dir "/" entry-file)))
                            (handle-exceptions exn #f
                              (let ((data (with-input-from-file entry-path read)))
                                (when (and (pair? data)
                                           (eq? 'audit-entry (car data)))
                                  (let* ((entry (cdr data))
                                         (action (assq 'action entry)))
                                    (when (and action
                                               (string-contains
                                                (sprintf "~a" action)
                                                name))
                                      (printf "  ~a: ~a~%"
                                              entry-file
                                              (cadr action)))))))))
                        entries))))
                 (print ""))

                ((path)
                 (print "")
                 (printf "Path: ~a~%" path)
                 (printf "Exists: ~a~%" (if (file-exists? path) "yes" "no"))
                 (print "")
                 path)

                ((raw)
                 (if (file-exists? path)
                     (handle-exceptions exn
                       (begin
                         (print "Not valid S-expression")
                         #f)
                       (with-input-from-file path read))
                     (begin
                       (print "File not found")
                       #f)))

                (else
                 (printf "Unknown command: ~a (try 'help)~%" cmd))))))))

  ;;; ============================================================================
  ;;; Cross-Module Reflection
  ;;; ============================================================================

  (define (seek query)
    "Search for a hash or identifier across soup, audit, and wormhole stores.
     Returns alist of matches: ((soup . results) (audit . results) (wormhole . results))

     (seek \"sha512:abc123\")  - search by hash prefix
     (seek \"2.0.0\")          - search by name/version"
    (let ((soup-results '())
          (audit-results '())
          (wormhole-results '()))

      ;; Search soup objects
      (for-each
       (lambda (obj)
         (let* ((name (cadr obj))
                (path (case (car obj)
                        ((archives keys) name)
                        ((releases) (sprintf ".vault/releases/~a.sig" name))
                        ((audit) (sprintf ".vault/audit/~a" name))
                        (else name)))
                (hash (and (file-exists? path)
                           (handle-exceptions exn #f
                             (soup-hash-file path)))))
           ;; Match by name or hash prefix
           (when (or (string-contains name query)
                     (and hash (string-prefix? query hash))
                     (and hash (string-prefix? (string-append "sha512:" query) hash)))
             (set! soup-results (cons `(soup ,(car obj) ,name ,hash) soup-results)))))
       (soup-collect-objects))

      ;; Search audit entries
      (let ((dir (audit-config 'audit-dir)))
        (when (directory-exists? dir)
          (for-each
           (lambda (file)
             (when (string-suffix? ".sexp" file)
               (let ((entry (handle-exceptions exn #f
                              (audit-read sequence: (string->number
                                                      (car (string-split file ".")))))))
                 (when entry
                   (let* ((id (entry-id entry))
                          (action (entry-action entry))
                          (obj (and action (action-object action))))
                     (when (or (and id (string-contains id query))
                               (and obj (string? obj) (string-contains obj query)))
                       (set! audit-results
                             (cons `(audit ,(entry-sequence entry) ,id ,obj)
                                   audit-results))))))))
           (directory dir))))

      ;; Search wormhole introspection store (handle module not loaded)
      (handle-exceptions exn #f
        (hash-table-for-each
         wormhole#*introspection-store*
         (lambda (hash intro)
           (when (string-contains hash query)
             (set! wormhole-results
                   (cons `(introspection ,hash
                                         ,(wormhole#introspection-provenance intro))
                         wormhole-results))))))

      ;; Return categorized results
      `((soup . ,(reverse soup-results))
        (audit . ,(reverse audit-results))
        (wormhole . ,(reverse wormhole-results)))))

  (define (dashboard . args)
    "Unified status dashboard across soup, audit, wormhole, and session.
     The 'what's going on?' view. Use (dashboard 'full) to show all session stats."
    (let* ((show-all? (and (pair? args) (eq? (car args) 'full)))
           (w 72)
           (col 20)  ; consistent column width for all sections
           (b (make-box w *box-rounded*))
           (fmt-row (lambda (key val)
                      (let* ((key-str (if (symbol? key) (symbol->string key) key))
                             (val-str (cond ((number? val)
                                             (if (> val 1000000)
                                                 (format-size val)
                                                 (number->string val)))
                                            (else (sprintf "~a" val)))))
                        (box-print b (sprintf "  ~a~a~a"
                                              key-str
                                              (make-string (max 1 (- col (string-length key-str))) #\space)
                                              val-str))))))

      ;; Collect soup objects first (this increments 'reads counter)
      ;; so session-stats reflects the dashboard's own activity
      (let* ((soup-objects (soup-collect-objects))
             (soup-by-type (make-hash-table)))
        (for-each
         (lambda (obj) (hash-table-set! soup-by-type (car obj)
                                        (+ 1 (hash-table-ref/default soup-by-type (car obj) 0))))
         soup-objects)

        ;; Now capture session stats (after soup read)
        (let* ((stats (session-stats))
               (non-zero (filter (lambda (s) (not (equal? (cdr s) 0))) stats))
               (session-to-show (if show-all? stats non-zero))
               (zeros (- (length stats) (length non-zero))))

          ;; Header
          (print "")
          (print (box-top b "Dashboard"))

          ;; Session stats - show non-zero by default, all with 'full
          (box-print b "Session")
          (if (null? stats)
              (box-print b "  (no activity)")
              (begin
                (for-each (lambda (stat) (fmt-row (car stat) (cdr stat))) session-to-show)
                (when (and (not show-all?) (> zeros 0))
                  (box-print b (sprintf "  ... and ~a zeros (use 'full)" zeros)))))

          (print (box-separator b))

          ;; Soup summary (use pre-collected data)
          (box-print b "Soup")
          (if (null? soup-objects)
              (box-print b "  (empty)")
              (for-each
               (lambda (type)
                 (let ((count (hash-table-ref/default soup-by-type type 0)))
                   (when (> count 0)
                     (fmt-row type count))))
               '(archives releases keys audit metadata certs forge)))

          (print (box-separator b))

      ;; Audit summary
      (box-print b "Audit")
      (let ((dir (audit-config 'audit-dir)))
        (if (and dir (directory-exists? dir))
            (let* ((files (filter (lambda (f) (string-suffix? ".sexp" f)) (directory dir)))
                   (count (length files)))
              (fmt-row "entries" count)
              (fmt-row "directory" dir))
            (box-print b "  (not initialized)")))

      (print (box-separator b))

      ;; Wormhole summary (gracefully handle module not loaded)
      (box-print b "Wormholes")
      (handle-exceptions exn
        (box-print b "  (module not loaded)")
        (let ((paths (hash-table-keys wormhole#*active-wormholes*)))
          (if (null? paths)
              (box-print b "  (none active)")
              (for-each
               (lambda (path)
                 (let* ((wh (hash-table-ref wormhole#*active-wormholes* path))
                        (audit-count (length (wormhole#wormhole-audit-log wh))))
                   (fmt-row (wormhole#wormhole-id wh) (sprintf "~a events" audit-count))))
               paths))
          (let ((intro-count (hash-table-size wormhole#*introspection-store*)))
            (when (> intro-count 0)
              (fmt-row "introspections" intro-count)))))

      (print (box-separator b))

      ;; Keystore status
      (box-print b "Keystore")
      (if (keystore-exists?)
          (fmt-row "status" (if (vault-config 'signing-key) "unlocked" "locked"))
          (box-print b "  (not created)"))

      ;; Lamport clock
      (let ((lt (lamport-time)))
        (when (> lt 0)
          (box-print b (sprintf "  lamport~a~a" (make-string 8 #\space) lt))))

          (print (box-bottom b))
          (print "")))))

  ;;; ============================================================================
  ;;; Node Roles - Memo-037 Implementation
  ;;; ============================================================================

  ;; Role definitions with capability requirements
  (define *node-roles*
    '((coordinator . ((description . "Byzantine consensus, threshold signing")
                      (compute . ((min-cores . 4) (min-ram-gb . 8)))
                      (storage . ((min-gb . 100)))
                      (network . ((max-latency-ms . 50) (min-uptime . 0.99)))))

      (full . ((description . "All vault operations, replication origin")
               (compute . ((min-cores . 2) (min-ram-gb . 4)))
               (storage . ((min-gb . 500)))
               (network . ((max-latency-ms . 200) (min-uptime . 0.95)))))

      (witness . ((description . "Passive storage, hash verification, audit")
                  (compute . ((min-cores . 1) (min-ram-gb . 1)))
                  (storage . ((min-gb . 100)))
                  (network . ((max-latency-ms . 1000) (min-uptime . 0.50)))))

      (archiver . ((description . "Cold storage, offline preservation")
                   (compute . ((min-cores . 1) (min-ram-gb . 0.5)))
                   (storage . ((min-gb . 1000)))
                   (network . ((max-latency-ms . 5000) (min-uptime . 0.10)))))

      (edge . ((description . "Read-only sync, mobile access")
               (compute . ((min-cores . 1) (min-ram-gb . 0.25)))
               (storage . ((min-gb . 1)))
               (network . ((max-latency-ms . 10000) (min-uptime . 0.01)))))))

  ;; Role hierarchy (higher = more capable)
  (define *role-hierarchy* '(coordinator full witness archiver edge))

  ;; Operations and required minimum role
  (define *node-operations*
    '((seal-commit . full)
      (seal-release . full)
      (seal-archive . full)
      (seal-restore . witness)
      (seal-publish . full)
      (seal-subscribe . witness)
      (seal-synchronize . witness)
      (seal-verify . edge)
      (threshold-sign . coordinator)
      (byzantine-vote . coordinator)
      (key-ceremony . coordinator)
      (audit-append . witness)
      (audit-verify . edge)))

  ;; Current node state
  (define *current-node-role* #f)
  (define *node-capabilities* #f)

  (define (node-probe)
    "Probe local system capabilities and display results"
    (let ((caps (probe-system-capabilities)))
      (set! *node-capabilities* caps)

      (print "")
      (print "Node Capability Probe")
      (print (repeat-string "─" 50))

      ;; Compute
      (let ((compute (cdr (assq 'compute caps))))
        (print "")
        (print " Compute")
        (printf "   Cores:     ~a~%" (cdr (assq 'cores compute)))
        (printf "   RAM:       ~a GB~%" (cdr (assq 'ram-gb compute)))
        (printf "   Load:      ~a~%" (cdr (assq 'load-avg compute))))

      ;; Storage
      (let ((storage (cdr (assq 'storage caps))))
        (print "")
        (print " Storage")
        (printf "   Available: ~a GB~%" (cdr (assq 'available-gb storage)))
        (printf "   Type:      ~a~%" (cdr (assq 'type storage))))

      ;; Network
      (let ((network (cdr (assq 'network caps))))
        (print "")
        (print " Network")
        (printf "   Type:      ~a~%" (cdr (assq 'type network)))
        (printf "   Latency:   ~a ms (estimated)~%" (cdr (assq 'latency-ms network))))

      ;; Security
      (let ((security (cdr (assq 'security caps))))
        (print "")
        (print " Security")
        (printf "   Signing key:  ~a~%" (if (cdr (assq 'signing-key security)) "present" "absent"))
        (printf "   Verify key:   ~a~%" (if (cdr (assq 'verify-key security)) "present" "absent")))

      ;; Recommended role
      (let ((recommended (recommend-role caps)))
        (print "")
        (print (repeat-string "─" 50))
        (printf " Recommended Role: ~a~%" recommended)
        (let ((desc (cdr (assq 'description (cdr (assq recommended *node-roles*))))))
          (printf "   ~a~%" desc)))

      (print "")
      caps))

  (define (probe-system-capabilities)
    "Probe actual system capabilities"
    (let ((cores (get-cpu-cores))
          (ram (get-ram-gb))
          (load (get-load-average))
          (weave (measure-weave))
          (storage (get-available-storage-gb))
          (storage-type (detect-storage-type))
          (network-type (detect-network-type))
          (latency (estimate-network-latency)))
      `((compute . ((cores . ,cores)
                    (ram-gb . ,ram)
                    (load-avg . ,load)
                    (weave . ,weave)))
        (storage . ((available-gb . ,storage)
                    (type . ,storage-type)))
        (network . ((type . ,network-type)
                    (latency-ms . ,latency)))
        (security . ((signing-key . ,(and (vault-config 'signing-key) #t))
                     (verify-key . ,(and (vault-config 'verify-key) #t)))))))

  (define (get-cpu-cores)
    "Get number of CPU cores"
    (handle-exceptions exn 1
      (let ((result (with-input-from-pipe "sysctl -n hw.ncpu 2>/dev/null || nproc 2>/dev/null || echo 1" read-line)))
        (if (eof-object? result) 1 (string->number result)))))

  (define (get-ram-gb)
    "Get RAM in GB"
    (handle-exceptions exn 1
      (let ((result (with-input-from-pipe
                        "sysctl -n hw.memsize 2>/dev/null | awk '{print int($1/1073741824)}' || free -g 2>/dev/null | awk '/^Mem:/{print $2}' || echo 1"
                      read-line)))
        (if (eof-object? result) 1 (or (string->number result) 1)))))

  (define (get-load-average)
    "Get 1-minute load average"
    (handle-exceptions exn 0.0
      (let ((result (with-input-from-pipe "uptime | awk -F'load averages?: ' '{print $2}' | awk -F'[, ]' '{print $1}'" read-line)))
        (if (eof-object? result) 0.0 (or (string->number result) 0.0)))))

  (define (get-available-storage-gb)
    "Get available storage in GB"
    (handle-exceptions exn 10
      (let ((result (with-input-from-pipe "df -g . 2>/dev/null | tail -1 | awk '{print $4}' || df -BG . 2>/dev/null | tail -1 | awk '{gsub(/G/,\"\",$4); print $4}' || echo 10" read-line)))
        (if (eof-object? result) 10 (or (string->number result) 10)))))

  (define (detect-storage-type)
    "Detect storage type (ssd/hdd/network/unknown)"
    (handle-exceptions exn 'unknown
      ;; macOS: check if on SSD
      (let ((result (with-input-from-pipe
                        "diskutil info / 2>/dev/null | grep 'Solid State' | grep -c Yes || echo 0"
                      read-line)))
        (if (and (not (eof-object? result))
                 (equal? result "1"))
            'ssd
            'hdd))))

  (define (detect-network-type)
    "Detect network connection type"
    (handle-exceptions exn 'unknown
      ;; Check active network interface
      (let ((result (with-input-from-pipe
                        "networksetup -listnetworkserviceorder 2>/dev/null | grep -E '^\\(1\\)' | head -1 || echo unknown"
                      read-line)))
        (cond
         ((eof-object? result) 'unknown)
         ((string-contains result "Ethernet") 'ethernet)
         ((string-contains result "Wi-Fi") 'wifi)
         ((string-contains result "Thunderbolt") 'ethernet)
         ((string-contains result "USB") 'ethernet)
         (else 'unknown)))))

  (define (estimate-network-latency)
    "Estimate network latency in ms (heuristic based on type)"
    (let ((net-type (detect-network-type)))
      (case net-type
        ((ethernet) 10)
        ((wifi) 30)
        ((satellite) 600)
        ((cellular) 100)
        (else 50))))

  (define (measure-weave)
    "Benchmark crypto ops/second - the node's computational essence.

     Cyberspace terminology for this metric:
       Weave     - how quickly it weaves cryptographic primitives (primary)
       Flux      - computational flow rate
       Pulse     - the node's heartbeat speed
       Forge     - how fast it can forge hashes/seals
       Lattice   - speed through the cryptographic lattice
       Resonance - how fast the node vibrates

     1 unit = 1000 SHA-512 hashes/sec (arbitrary baseline).
     Legacy: VUPS (VAX Units of Performance). Modern systems: 100-10000+."
    (handle-exceptions exn 0.0
      (let* ((test-data (make-blob 64))
             (iterations 5000)
             (start (current-process-milliseconds)))
        (do ((i 0 (+ i 1))) ((= i iterations))
          (sha512-hash test-data))
        (let* ((elapsed (max 1 (- (current-process-milliseconds) start)))
               (ops-per-sec (/ (* iterations 1000.0) elapsed)))
          ;; Round to 1 decimal place
          (/ (round (* (/ ops-per-sec 1000.0) 10)) 10.0)))))

  ;; Memo-056: Weave quantization for federation OPSEC
  ;; Raw weave values are a covert channel - they fingerprint hardware.
  ;; Federation shares only strata, not raw values.

  (define *weave-strata*
    '((constrained . 500)     ; IoT, embedded, RPi
      (standard    . 1000)    ; Laptops, desktops
      (capable     . 2000)    ; Workstations, servers
      (powerful    . 4000)))  ; HPC, GPU-accelerated

  (define (weave-stratum weave)
    "Which stratum of the lattice does this weave occupy? (Memo-056)
     For LOCAL display, use raw weave.
     For FEDERATION, use this to avoid fingerprinting."
    (cond
      ((< weave 500)  'constrained)
      ((< weave 1000) 'standard)
      ((< weave 2000) 'capable)
      (else           'powerful)))

  (define (recommend-role capabilities)
    "Recommend role based on capabilities"
    (let* ((compute (cdr (assq 'compute capabilities)))
           (storage (cdr (assq 'storage capabilities)))
           (network (cdr (assq 'network capabilities)))
           (cores (cdr (assq 'cores compute)))
           (ram (cdr (assq 'ram-gb compute)))
           (storage-gb (cdr (assq 'available-gb storage)))
           (latency (cdr (assq 'latency-ms network))))
      (cond
       ;; Coordinator: high compute, low latency
       ((and (>= cores 4) (>= ram 8) (<= latency 50))
        'coordinator)
       ;; Full: medium compute, high storage
       ((and (>= cores 2) (>= ram 4) (>= storage-gb 500))
        'full)
       ;; Archiver: massive storage, any network
       ((>= storage-gb 1000)
        'archiver)
       ;; Witness: decent storage
       ((>= storage-gb 100)
        'witness)
       ;; Edge: everything else
       (else 'edge))))

  (define (node-role . args)
    "Get or set current node role"
    (cond
     ;; No args: display current role
     ((null? args)
      (let ((role (or *current-node-role*
                      (load-node-role)
                      (recommend-role (or *node-capabilities*
                                         (probe-system-capabilities))))))
        (set! *current-node-role* role)
        (print "")
        (printf "Current role: ~a~%" role)
        (let ((def (assq role *node-roles*)))
          (when def
            (printf "  ~a~%" (cdr (assq 'description (cdr def))))))
        (print "")
        role))

     ;; Set role
     (else
      (let ((new-role (car args)))
        (unless (assq new-role *node-roles*)
          (error "Unknown role. Valid roles:" (map car *node-roles*)))
        (let ((old-role *current-node-role*))
          (set! *current-node-role* new-role)
          (save-node-role new-role)

          ;; Audit the change
          (let ((signing-key (vault-config 'signing-key)))
            (when (and signing-key old-role)
              (audit-append
               actor: (get-vault-principal signing-key)
               action: `(node-role-change ,old-role ,new-role)
               motivation: "Node role changed")))

          (printf "Role set: ~a → ~a~%" (or old-role 'none) new-role)
          new-role)))))

  (define (load-node-role)
    "Load persisted node role"
    (let ((role-file (node-role-file)))
      (if (file-exists? role-file)
          (handle-exceptions exn #f
            (let ((data (with-input-from-file role-file read)))
              (if (and (pair? data) (eq? 'node-config (car data)))
                  (let ((role-entry (assq 'role (cdr data))))
                    (if role-entry (cadr role-entry) #f))
                  #f)))
          #f)))

  (define (save-node-role role)
    "Persist node role"
    (let ((role-file (node-role-file)))
      (create-directory (pathname-directory role-file) #t)
      (with-output-to-file role-file
        (lambda ()
          (write `(node-config
                   (role ,role)
                   (updated ,(current-seconds))))
          (newline)))))

  (define (node-role-file)
    "Get path to node role config file"
    (let ((home (get-environment-variable "HOME")))
      (make-pathname (list home ".cyberspace") "node-role")))

  (define (role-level role)
    "Get numeric level of role in hierarchy"
    (let loop ((roles *role-hierarchy*) (level 0))
      (cond
       ((null? roles) 999)
       ((eq? (car roles) role) level)
       (else (loop (cdr roles) (+ level 1))))))

  (define (node-can? operation)
    "Check if current role permits operation"
    (let* ((current (or *current-node-role* (node-role)))
           (required-entry (assq operation *node-operations*))
           (required (if required-entry (cdr required-entry) 'edge)))
      (let ((can (<= (role-level current) (role-level required))))
        (if can
            (begin
              (printf "✓ ~a: permitted for ~a (requires ~a)~%" operation current required)
              #t)
            (begin
              (printf "✗ ~a: denied for ~a (requires ~a)~%" operation current required)
              #f)))))

  (define (node-announce)
    "Announce role to federation peers"
    (let ((role (or *current-node-role* (node-role)))
          (caps (or *node-capabilities* (probe-system-capabilities)))
          (key (vault-config 'signing-key)))

      (print "")
      (print "Node Role Announcement")
      (print (repeat-string "─" 50))

      (if key
          (let* ((principal (get-vault-principal key))
                 (announcement
                  `(node-role-announcement
                    (principal ,(blob->hex principal))
                    (role ,role)
                    (capabilities ,caps)
                    (timestamp ,(current-seconds)))))

            ;; Sign announcement
            (let* ((ann-bytes (with-output-to-string (lambda () (write announcement))))
                   (ann-hash (sha512-hash ann-bytes))
                   (signature (ed25519-sign key ann-hash)))

              (printf " Principal:  ~a...~%" (substring (blob->hex principal) 0 16))
              (printf " Role:       ~a~%" role)
              (printf " Timestamp:  ~a~%" (current-seconds))
              (printf " Signature:  ~a...~%" (substring (blob->hex signature) 0 16))
              (print "")
              (print " Status: Ready to broadcast (federation not yet implemented)")
              (print "")

              ;; Return signed announcement
              `(signed-announcement
                ,announcement
                (signature ,(blob->hex signature)))))

          (begin
            (print " No signing key configured")
            (print " Run: (vault-init signing-key: <key>)")
            (print "")
            #f))))

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

      ;; Track bytes written
      (when (file-exists? out)
        (session-stat! 'writes)
        (session-stat! 'bytes-written (file-size out)))
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
            (print "Dry Run - would execute: " migration-script)
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

  ;;; ============================================================================
  ;;; Natural Language Soup Query (Memo-038)
  ;;; ============================================================================

  (define *ollama-base* "http://localhost:11434")
  (define *ollama-model* "llama3.2")

  (define (ollama-available?)
    "Check if Ollama is running"
    (handle-exceptions exn #f
      (let ((result (with-input-from-pipe
                     (sprintf "curl -s -o /dev/null -w '%{http_code}' ~a/api/tags 2>/dev/null"
                              *ollama-base*)
                     read-line)))
        (and result (string=? result "200")))))

  (define (ollama-chat model system-prompt user-message)
    "Send chat request to Ollama, return response text"
    (let* ((payload (sprintf "{\"model\":\"~a\",\"messages\":[{\"role\":\"system\",\"content\":~s},{\"role\":\"user\",\"content\":~s}],\"stream\":false}"
                             model system-prompt user-message))
           (cmd (sprintf "curl -s -X POST ~a/api/chat -H 'Content-Type: application/json' -d '~a' 2>/dev/null"
                         *ollama-base*
                         (string-translate* payload '(("'" . "'\"'\"'")))))
           (response (with-input-from-pipe cmd read-string)))
      (if (and response (> (string-length response) 0))
          ;; Extract content from JSON response
          (let ((start (string-contains response "\"content\":\"")))
            (if start
                (let* ((content-start (+ start 11))
                       (rest (substring response content-start))
                       ;; Find end of content string (unescaped quote)
                       (content-end (find-json-string-end rest)))
                  (if content-end
                      (let ((content (substring rest 0 content-end)))
                        ;; Unescape JSON string
                        (string-translate* content
                                           '(("\\n" . "\n")
                                             ("\\\"" . "\"")
                                             ("\\\\" . "\\"))))
                      response))
                response))
          #f)))

  (define (find-json-string-end str)
    "Find end of JSON string (unescaped quote)"
    (let loop ((i 0) (escaped #f))
      (if (>= i (string-length str))
          #f
          (let ((c (string-ref str i)))
            (cond
             (escaped (loop (+ i 1) #f))
             ((char=? c #\\) (loop (+ i 1) #t))
             ((char=? c #\") i)
             (else (loop (+ i 1) #f)))))))

  (define (soup-context)
    "Generate soup context for LLM"
    (let* ((objects (soup-collect-objects))
           (grouped (make-hash-table)))
      ;; Group by type
      (for-each
       (lambda (obj)
         (hash-table-set! grouped (car obj)
                          (cons obj (hash-table-ref/default grouped (car obj) '()))))
       objects)
      ;; Build context string
      (with-output-to-string
        (lambda ()
          (printf "Vault soup contents (~a objects):~%~%" (length objects))
          (for-each
           (lambda (type-pair)
             (let* ((type (car type-pair))
                    (objs (reverse (hash-table-ref/default grouped type '()))))
               (unless (null? objs)
                 (printf "~a/ (~a items):~%" type (length objs))
                 (for-each
                  (lambda (obj)
                    (let ((name (cadr obj))
                          (size (caddr obj))
                          (info (cadddr obj)))
                      (printf "  - ~a (~a) ~a~%"
                              name
                              (format-size size)
                              (if (list? info) (string-intersperse info " ") info))))
                  (if (> (length objs) 10)
                      (append (take objs 5) (list '(... ... ... ("..."))) (take-right objs 3))
                      objs))
                 (newline))))
           (append *soup-types* '((identity . "Node identity"))))))))

  (define (ask question)
    "Ask a natural language question about the soup

     (ask \"what synced recently?\")
     (ask \"who can sign releases?\")
     (ask \"show me unsigned releases\")"
    (if (not (ollama-available?))
        (begin
          (print "")
          (print "Local inference not available.")
          (print "")
          (print "  curl -fsSL https://ollama.com/install.sh | sh")
          (print "  ollama pull " *ollama-model*))
        (let* ((context (soup-context))
               (system-prompt
                (string-append
                 "You are a helpful assistant for the Library of Cyberspace vault system. "
                 "Answer questions about the vault contents based on the context provided. "
                 "Be concise and direct. Use the exact names from the context. "
                 "If asked about timestamps, convert Unix timestamps to readable dates. "
                 "Here is the current vault state:\n\n"
                 context))
               (response (ollama-chat *ollama-model* system-prompt question)))
          (if response
              (begin
                (print "")
                (print response)
                (print ""))
              (print "No response from inference server")))))

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
