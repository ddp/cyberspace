;;; vault.sls - Cryptographically Sealed Version Control for the Library of Cyberspace
;;; Chez Scheme Port
;;;
;;; A higher-level interface to version control with integrated:
;;; - SPKI certificate-based authorization
;;; - Cryptographic sealing of versions
;;; - First-class archival and restoration
;;; - Migration paths between versions
;;;
;;; Phase 1: Core operations (~81 exports, ~2500 lines)
;;; Phase 2 (deferred): soup tree view, soup-inspect, soup-query/find,
;;;   complete, seek, dashboard, Ollama NLP, soup-collect-objects
;;;
;;; Ported from Chicken's vault.scm (4,458 lines, 142 exports).
;;; Changes: module -> library, (chicken *) -> compat shims,
;;;          #!key/#!optional -> get-key/get-opt, srfi-69 -> chez hash tables,
;;;          irregex -> manual string matching, sort arg order reversed,
;;;          read-string -> get-string-all, sprintf -> format.

(library (cyberspace vault)
  (export
    ;; Core operations
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

    ;; Soup CRUD
    soup-create
    soup-get
    soup-delete
    soup-gc
    *default-realm-period*

    ;; Soup hashing & proofs (Memo-047)
    soup-hash-file
    soup-merkle-hash-file
    soup-dual-hash-file
    soup-prove-chunk
    soup-verify-chunk

    ;; Soup display
    soup-releases
    hex-abbrev

    ;; Utilities
    blob->hex
    hex->blob
    format-size
    valid-semver?
    run-command

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

    ;; Realm persistence (enrollment keys + realm state)
    store-enrollment-keypair!
    load-enrollment-keypair
    store-realm-state!
    load-realm-state

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

  (import (rnrs)
          (only (chezscheme)
                format printf with-output-to-string
                file-directory? directory-list mkdir
                getenv sort date-and-time
                current-time time-second time-nanosecond
                system port-length)
          (cyberspace crypto-ffi)
          (cyberspace audit)
          (only (cyberspace os)
                session-stat! hostname)
          (cyberspace chicken-compatibility blob)
          (only (cyberspace chicken-compatibility chicken)
                print conc string-intersperse string-split
                alist-ref alist-update alist-delete
                handle-exceptions get-condition-property
                get-opt get-key)
          (only (cyberspace chicken-compatibility hash-table)
                make-hash-table hash-table-set! hash-table-ref
                hash-table-ref/default hash-table-keys
                hash-table-delete! hash-table-exists?)
          (only (cyberspace chicken-compatibility process)
                with-input-from-pipe read-line))

  ;;; ============================================================================
  ;;; Inlined Helpers
  ;;; ============================================================================
  ;;;
  ;;; SRFI-1, SRFI-13, pathname, I/O, and time helpers inlined at top
  ;;; following the pattern established by keyring.sls and audit.sls.

  ;; -- SRFI-1 list utilities --

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

  (define (iota n)
    (let loop ((i (- n 1)) (acc '()))
      (if (< i 0) acc
          (loop (- i 1) (cons i acc)))))

  (define (take lst n)
    (if (or (zero? n) (null? lst))
        '()
        (cons (car lst) (take (cdr lst) (- n 1)))))

  ;; -- SRFI-13 string utilities --

  (define (string-prefix? prefix str)
    (and (>= (string-length str) (string-length prefix))
         (string=? (substring str 0 (string-length prefix)) prefix)))

  (define (string-suffix? suffix str)
    (and (>= (string-length str) (string-length suffix))
         (string=? (substring str (- (string-length str) (string-length suffix))
                              (string-length str))
                   suffix)))

  (define (string-index str char)
    "Find first index of char in str, or #f"
    (let loop ((i 0))
      (cond
        ((>= i (string-length str)) #f)
        ((char=? (string-ref str i) char) i)
        (else (loop (+ i 1))))))

  (define (string-contains str target)
    "Find first occurrence of target in str, or #f"
    (let ((tlen (string-length target))
          (slen (string-length str)))
      (if (> tlen slen)
          #f
          (let loop ((i 0))
            (cond
              ((> (+ i tlen) slen) #f)
              ((string=? (substring str i (+ i tlen)) target) i)
              (else (loop (+ i 1))))))))

  (define (string-trim-both str)
    "Remove leading and trailing whitespace"
    (let* ((len (string-length str))
           (start (let loop ((i 0))
                    (if (or (>= i len) (not (char-whitespace? (string-ref str i))))
                        i
                        (loop (+ i 1)))))
           (end (let loop ((i (- len 1)))
                  (if (or (< i start) (not (char-whitespace? (string-ref str i))))
                      (+ i 1)
                      (loop (- i 1))))))
      (substring str start end)))

  (define (string-null? s)
    (= 0 (string-length s)))

  ;; -- Pathname utilities --

  (define (pathname-file path)
    "Extract filename from path (without directory)"
    (let loop ((i (- (string-length path) 1)))
      (cond
        ((< i 0) path)
        ((char=? (string-ref path i) #\/)
         (substring path (+ i 1) (string-length path)))
        (else (loop (- i 1))))))

  (define (pathname-directory path)
    "Extract directory from path"
    (let loop ((i (- (string-length path) 1)))
      (cond
        ((< i 0) ".")
        ((char=? (string-ref path i) #\/)
         (substring path 0 i))
        (else (loop (- i 1))))))

  (define (pathname-strip-extension path)
    "Remove file extension from path"
    (let loop ((i (- (string-length path) 1)))
      (cond
        ((< i 0) path)
        ((char=? (string-ref path i) #\.) (substring path 0 i))
        ((char=? (string-ref path i) #\/) path)
        (else (loop (- i 1))))))

  (define (make-pathname dir file)
    "Construct path from directory and filename"
    (let ((dir-str (if (list? dir) (string-intersperse dir "/") dir)))
      (string-append dir-str "/" file)))

  ;; -- File/directory utilities --

  (define (directory-exists? path)
    (and (file-exists? path) (file-directory? path)))

  (define (create-directory path . rest)
    "Create directory, optionally recursive"
    (let ((recursive (if (null? rest) #f (car rest))))
      (if recursive
          (let loop ((parts (string-split-path path)) (current ""))
            (unless (null? parts)
              (let ((next (if (string=? current "")
                              (car parts)
                              (string-append current "/" (car parts)))))
                (unless (or (string=? next "") (directory-exists? next))
                  (guard (exn [#t #f])
                    (mkdir next #o755)))
                (loop (cdr parts) next))))
          (unless (directory-exists? path)
            (mkdir path #o755)))))

  (define (string-split-path str)
    "Split path into components on /"
    (let loop ((i 0) (start 0) (acc '()))
      (cond
        ((= i (string-length str))
         (reverse (if (= start i) acc (cons (substring str start i) acc))))
        ((char=? (string-ref str i) #\/)
         (loop (+ i 1) (+ i 1)
               (if (= start i) acc (cons (substring str start i) acc))))
        (else
         (loop (+ i 1) start acc)))))

  (define (directory path)
    "List directory contents (Chicken compat)"
    (if (directory-exists? path)
        (directory-list path)
        '()))

  ;; -- I/O utilities --

  (define (read-string . rest)
    "Read all available text from current-input-port.
     Handles (read-string) and (read-string #f) forms from Chicken."
    (let ((result (get-string-all (current-input-port))))
      (if (eof-object? result) "" result)))

  (define (read-lines)
    "Read all lines from current-input-port"
    (let loop ((lines '()))
      (let ((line (read-line)))
        (if (eof-object? line)
            (reverse lines)
            (loop (cons line lines))))))

  (define (read-file-bytes filename)
    "Read file contents as bytevector (binary)"
    (let* ((port (open-file-input-port filename))
           (data (get-bytevector-all port)))
      (close-port port)
      (if (eof-object? data)
          (make-bytevector 0)
          data)))

  (define (file-size path)
    "Get file size in bytes"
    (let* ((port (open-file-input-port path))
           (len (port-length port)))
      (close-port port)
      len))

  ;; -- Time utilities --

  (define (current-seconds)
    (time-second (current-time)))

  (define (get-environment-variable name)
    (getenv name))

  (define (current-process-milliseconds)
    "Wall-clock milliseconds (for measure-weave benchmarking)"
    (let ((t (current-time)))
      (+ (* (time-second t) 1000)
         (div (time-nanosecond t) 1000000))))

  (define (format-timestamp ts)
    "Format Unix timestamp as YYYY-MM-DD using system date command"
    (handle-exceptions exn ""
      (let ((t (cond ((number? ts) ts)
                     ((string? ts) (string->number ts))
                     (else #f))))
        (if t
            (let ((result (with-input-from-pipe
                            (format #f "date -r ~a '+%Y-%m-%d' 2>/dev/null || date -d @~a '+%Y-%m-%d' 2>/dev/null || echo ''" t t)
                            read-line)))
              (if (eof-object? result) "" result))
            ""))))

  ;; -- Shell utilities --

  (define (shell-escape s)
    "Escape a string for safe shell use (single-quote wrapping)"
    (string-append
      "'"
      (apply string-append
        (map (lambda (c)
               (if (char=? c #\')
                   "'\\''"
                   (string c)))
             (string->list s)))
      "'"))

  (define (run-command . args)
    "Run a system command with arguments"
    (let ((cmd (string-intersperse (map shell-escape args) " ")))
      (let ((result (system cmd)))
        (unless (zero? result)
          (error 'vault "Command failed" (car args) result)))))

  ;; -- Semver validation (replaces irregex) --

  (define (valid-semver? version)
    "Check if string is valid semantic version X.Y.Z"
    (let ((parts (string-split version ".")))
      (and (= (length parts) 3)
           (every (lambda (p)
                    (and (> (string-length p) 0)
                         (every char-numeric? (string->list p))))
                  parts))))

  ;;; ============================================================================
  ;;; Helper Functions
  ;;; ============================================================================

  (define (get-vault-principal signing-key)
    "Extract public key from Ed25519 signing key (64 bytes)"
    (if (and (blob? signing-key) (= (blob-size signing-key) 64))
        ;; Public key is second half of signing key
        (let ((result (make-blob 32)))
          (move-memory! signing-key result 32 32 0)
          result)
        #f))

  (define (blob->hex b)
    "Convert blob to hex string"
    (let ((vec (blob->u8vector b)))
      (apply string-append
             (map (lambda (i)
                    (let ((byte (u8vector-ref vec i)))
                      (string-append
                       (string (string-ref "0123456789abcdef" (div byte 16)))
                       (string (string-ref "0123456789abcdef" (mod byte 16))))))
                  (iota (u8vector-length vec))))))

  (define (hex->blob hex-string)
    "Convert hex string to blob"
    (let* ((len (div (string-length hex-string) 2))
           (vec (make-u8vector len)))
      (do ((i 0 (+ i 1)))
          ((= i len) (u8vector->blob vec))
        (u8vector-set! vec i
                       (string->number
                        (substring hex-string (* i 2) (* (+ i 1) 2))
                        16)))))

  (define (hex-abbrev hex . rest)
    "Abbreviate long hex string: 0xAAAA...0xBBBB
     For human display of long binary blobs."
    (let ((prefix-bytes (get-opt rest 0 4))
          (suffix-bytes (get-opt rest 1 4)))
      (let ((prefix-chars (* prefix-bytes 2))
            (suffix-chars (* suffix-bytes 2))
            (len (string-length hex)))
        (if (<= len (+ prefix-chars suffix-chars 4))
            hex
            (string-append
             "0x" (substring hex 0 prefix-chars)
             "..."
             "0x" (substring hex (- len suffix-chars) len))))))

  (define (format-size bytes)
    "Format byte size human-readable"
    (cond
     ((< bytes 1024) (format #f "~aB" bytes))
     ((< bytes (* 1024 1024)) (format #f "~aK" (div bytes 1024)))
     ((< bytes (* 1024 1024 1024)) (format #f "~aM" (div bytes (* 1024 1024))))
     (else (format #f "~aG" (div bytes (* 1024 1024 1024))))))

  (define (repeat-string str n)
    "Repeat a string n times"
    (let loop ((i 0) (acc ""))
      (if (= i n) acc
          (loop (+ i 1) (string-append acc str)))))

  (define (read-key-from-file filename)
    "Read key blob from s-expression file"
    (let ((sexp (with-input-from-file filename read)))
      (if (and (pair? sexp) (= 2 (length sexp)))
          (cadr sexp)
          (error 'vault "Invalid key file format" filename))))

  ;;; ============================================================================
  ;;; Configuration
  ;;; ============================================================================

  (define *vault-config*
    '((signing-key . #f)
      (verify-key . #f)
      (archive-format . tarball)
      (age-recipients . ())
      (age-identity . #f)
      (migration-dir . "migrations")))

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

  (define (vault-config key . rest)
    "Get or set vault configuration"
    (let ((value (get-opt rest 0 #f)))
      (if value
          (set! *vault-config* (alist-update key value *vault-config*))
          (alist-ref key *vault-config*))))

  (define (vault-init . opts)
    "Initialize vault configuration for repository"
    (let ((signing-key (get-key opts 'signing-key: #f)))
      (when signing-key
        (vault-config 'signing-key signing-key))
      (print "Vault initialized for: " (get-environment-variable "PWD"))
      (when signing-key
        (print "Signing key: " signing-key)
        (let ((principal (get-vault-principal signing-key)))
          (when principal
            (audit-init 'signing-key: signing-key
                        'motivation: "Vault initialized with cryptographic audit trail"))))))

  ;;; ============================================================================
  ;;; Keystore (Memo-041)
  ;;; ============================================================================
  ;;;
  ;;; The keystore is the inner vault - where cryptographic identity lives.
  ;;; Private keys are encrypted at rest with Argon2id + XSalsa20-Poly1305.

  ;; Keystore state (unlocked key in memory, zeroed on lock)
  (define *keystore-unlocked* #f)
  (define *keystore-public* #f)

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
      (error 'vault "Keystore already exists. Use keystore-change-passphrase to update."))

    ;; Create keystore directory
    (let ((ks-dir (keystore-path)))
      (unless (directory-exists? ks-dir)
        (create-directory ks-dir #t)))

    ;; Generate Ed25519 keypair
    (let* ((keypair (ed25519-keypair))
           (public-key (car keypair))
           (secret-key (cadr keypair))
           (salt (random-bytes 16))
           (enc-key (argon2id-hash passphrase salt))
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
      (error 'vault "No keystore found. Use keystore-create first."))

    (if *keystore-unlocked*
        (begin
          (print "Keystore already unlocked.")
          *keystore-public*)
        ;; Read encrypted key file
        (let* ((key-data (with-input-from-file (keystore-key-path) read))
               (salt (cadr (assq 'salt (cdr key-data))))
               (nonce (cadr (assq 'nonce (cdr key-data))))
               (ciphertext (cadr (assq 'ciphertext (cdr key-data))))
               (dec-key (argon2id-hash passphrase salt))
               (secret-key (secretbox-decrypt ciphertext nonce dec-key)))
          (session-stat! 'decrypts)

          ;; Zero the decryption key
          (memzero! dec-key)

          (if secret-key
              (begin
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
      (let* ((pub-data (with-input-from-file (keystore-pub-path) read))
             (public-key (cadr (assq 'public-key (cdr pub-data)))))
        `(keystore
          (status locked)
          (principal ,(string-append "ed25519:" (blob->hex public-key))))))))

  (define (keystore-change-passphrase old-passphrase new-passphrase)
    "Change keystore passphrase"
    (let ((secret-key (or *keystore-unlocked*
                          (keystore-unlock old-passphrase))))
      (unless secret-key
        (error 'vault "Wrong passphrase"))

      (let* ((salt (random-bytes 16))
             (enc-key (argon2id-hash new-passphrase salt))
             (nonce (random-bytes secretbox-noncebytes))
             (ciphertext (secretbox-encrypt secret-key nonce enc-key)))
        (session-stat! 'encrypts)

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

        (memzero! enc-key)

        (print "Passphrase changed.")
        #t)))

  (define (keystore-export-public)
    "Export public key (safe to share)"
    (if (keystore-exists?)
        (with-input-from-file (keystore-pub-path) read)
        (error 'vault "No keystore found")))

  ;;; ============================================================================
  ;;; Realm Naming
  ;;; ============================================================================

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
      (error 'vault "No vault found. Create one first."))
    (with-output-to-file (realm-name-path)
      (lambda () (display name) (newline)))
    (print "Realm named: " name)
    name)

  ;;; ============================================================================
  ;;; Realm Membership (Memo-050) - Certificate-Based
  ;;; ============================================================================

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
         (let* ((body (cadr cert))
                (body-fields (cdr body))
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
    "Store membership certificate in the vault"
    (unless (directory-exists? ".vault")
      (error 'vault "No vault found. Create one first."))
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
  ;;; Enrollment Key Persistence
  ;;; ============================================================================

  (define (enrollment-pub-path)
    ".vault/keystore/enrollment.pub")

  (define (enrollment-key-path)
    ".vault/keystore/enrollment.key")

  (define (store-enrollment-keypair! pubkey privkey)
    "Persist enrollment keypair (blobs) to vault keystore."
    (unless (directory-exists? ".vault")
      (error 'vault "No vault found. Create one first."))
    (let ((ks-dir (keystore-path)))
      (unless (directory-exists? ks-dir)
        (create-directory ks-dir #t)))
    (with-output-to-file (enrollment-pub-path)
      (lambda ()
        (write `(enrollment-public-key
                  (version 1)
                  (algorithm "ed25519")
                  (public-key ,pubkey)
                  (created ,(current-seconds))))
        (newline)))
    (with-output-to-file (enrollment-key-path)
      (lambda ()
        (write `(enrollment-private-key
                  (version 1)
                  (algorithm "ed25519")
                  (private-key ,privkey)
                  (created ,(current-seconds))))
        (newline))))

  (define (load-enrollment-keypair)
    "Load enrollment keypair from vault. Returns (pubkey privkey) or #f."
    (let ((pub-path (enrollment-pub-path))
          (key-path (enrollment-key-path)))
      (if (and (file-exists? pub-path) (file-exists? key-path))
          (handle-exceptions exn #f
            (let* ((pub-data (with-input-from-file pub-path read))
                   (key-data (with-input-from-file key-path read))
                   (pubkey (cadr (assq 'public-key (cdr pub-data))))
                   (privkey (cadr (assq 'private-key (cdr key-data)))))
              (if (and (blob? pubkey) (blob? privkey))
                  (list pubkey privkey)
                  #f)))
          #f)))

  ;;; ============================================================================
  ;;; Realm State Persistence
  ;;; ============================================================================

  (define (realm-state-path)
    ".vault/realm-state.sexp")

  (define (store-realm-state! master role my-name members)
    "Persist realm state to vault."
    (when (directory-exists? ".vault")
      (with-output-to-file (realm-state-path)
        (lambda ()
          (write `(realm-state
                    (version 1)
                    (master ,master)
                    (role ,role)
                    (my-name ,my-name)
                    (members ,(map car members))
                    (timestamp ,(current-seconds))))
          (newline)))))

  (define (load-realm-state)
    "Load realm state from vault. Returns parsed s-expression or #f."
    (let ((path (realm-state-path)))
      (if (file-exists? path)
          (handle-exceptions exn #f
            (let ((data (with-input-from-file path read)))
              (if (and (pair? data) (eq? (car data) 'realm-state))
                  data
                  #f)))
          #f)))

  ;;; ============================================================================
  ;;; Soup Object Store (Memo-002 Section 2.3)
  ;;; ============================================================================

  ;; Default realm period: 1 year (365 days in seconds)
  (define *default-realm-period* 31536000)

  (define (soup-path)
    ".vault/soup")

  (define (ensure-soup-dir!)
    "Create .vault/soup directory if needed"
    (unless (directory-exists? ".vault")
      (error 'vault "No vault found. Create one first."))
    (unless (directory-exists? (soup-path))
      (create-directory (soup-path))))

  (define (soup-object-path id)
    "Get path to a soup object by ID"
    (format #f "~a/~a.sexp" (soup-path) id))

  (define (generate-soup-id content)
    "Generate a unique ID for a soup object based on content hash + timestamp"
    (let* ((data (format #f "~a~a" content (current-seconds)))
           (hash (blob->hex (blake2b-hash data)))
           (short-hash (substring hash 0 12)))
      short-hash))

  (define (soup-create content . opts)
    "Create a new object in the soup with specified lifetime.

     content: any s-expression to store
     lifetime: 'temporary, 'default, or 'archivable
     expires: explicit expiration time (seconds since epoch) for 'temporary
     tags: list of symbols for categorization
     name: optional human-readable name

     Returns: object ID"
    (let ((lifetime (get-key opts 'lifetime: 'default))
          (expires (get-key opts 'expires: #f))
          (tags (get-key opts 'tags: '()))
          (name (get-key opts 'name: #f)))
      (ensure-soup-dir!)
      (let* ((now (current-seconds))
             (id (or name (generate-soup-id content)))
             (expiration (case lifetime
                           ((temporary)
                            (or expires
                                (error 'vault "soup-create: 'temporary requires expires: parameter")))
                           ((default)
                            (+ now *default-realm-period*))
                           ((archivable)
                            (+ now *default-realm-period*))
                           (else
                            (error 'vault "soup-create: lifetime must be 'temporary, 'default, or 'archivable"))))
             (obj `(soup-object
                     (id ,id)
                     (created ,now)
                     (expires ,expiration)
                     (lifetime ,lifetime)
                     (tags ,tags)
                     (content ,content))))
        (with-output-to-file (soup-object-path id)
          (lambda () (write obj) (newline)))
        id)))

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
                      #f))
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
              (let* ((path (format #f "~a/~a" (soup-path) f))
                     (obj (handle-exceptions exn #f
                            (with-input-from-file path read))))
                (when (and obj (pair? obj) (eq? 'soup-object (car obj)))
                  (let* ((fields (cdr obj))
                         (expires (cadr (assq 'expires fields)))
                         (lifetime (cadr (assq 'lifetime fields))))
                    (when (>= now expires)
                      (if (eq? lifetime 'archivable)
                          (begin
                            (soup-migrate-to-vault! obj path)
                            (set! migrated (+ migrated 1)))
                          (begin
                            (delete-file path)
                            (set! deleted (+ deleted 1))))))))))
          (directory (soup-path))))
      (list deleted migrated)))

  (define (soup-migrate-to-vault! obj source-path)
    "Migrate an archivable object to the vault with transition record."
    (let* ((fields (cdr obj))
           (id (cadr (assq 'id fields)))
           (created (cadr (assq 'created fields)))
           (expires (cadr (assq 'expires fields)))
           (content (cadr (assq 'content fields)))
           (now (current-seconds))
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
      (unless (directory-exists? ".vault/archive")
        (create-directory ".vault/archive"))
      (with-output-to-file (format #f ".vault/archive/~a.sexp" id)
        (lambda () (write vault-obj) (newline)))
      (delete-file source-path)))

  ;;; ============================================================================
  ;;; Lamport Clock (Memo-012)
  ;;; ============================================================================

  (define *lamport-counter* 0)

  (define (lamport-clock-path)
    ".vault/lamport-clock")

  (define (lamport-tick!)
    "Increment clock for local event. Returns new time."
    (set! *lamport-counter* (+ 1 *lamport-counter*))
    *lamport-counter*)

  (define (lamport-time)
    "Current Lamport time."
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
        ((< t 1000) (format #f "\x03bb; ~a" t))
        ((< t 1000000) (format #f "\x03bb; ~ak" (div t 1000)))
        ((< t 1000000000) (format #f "\x03bb; ~am" (div t 1000000)))
        (else (format #f "\x03bb; ~ag" (div t 1000000000))))))

  ;;; ============================================================================
  ;;; Capability Set (Weave Self-Awareness)
  ;;; ============================================================================

  (define *capabilities* (make-hash-table))
  (define *capability-audit* #f)

  (define (capability-add! cap)
    "Register a capability this node supports."
    (hash-table-set! *capabilities* cap #t)
    (when *capability-audit*
      (audit-append
        'actor: (get-vault-principal *capability-audit*)
        'action: `(capability-add ,cap)
        'motivation: "Capability registered"
        'signing-key: *capability-audit*))
    cap)

  (define (capability-remove! cap)
    "Remove a capability."
    (hash-table-delete! *capabilities* cap)
    (when *capability-audit*
      (audit-append
        'actor: (get-vault-principal *capability-audit*)
        'action: `(capability-remove ,cap)
        'motivation: "Capability removed"
        'signing-key: *capability-audit*)))

  (define (capability? cap)
    "Check if this node has a capability."
    (hash-table-exists? *capabilities* cap))

  (define (capabilities)
    "List all capabilities as a sorted list."
    (sort (lambda (a b) (string<? (symbol->string a) (symbol->string b)))
          (hash-table-keys *capabilities*)))

  (define (capability-intersect caps1 caps2)
    "Set intersection: capabilities both have."
    (filter (lambda (c) (memq c caps2)) caps1))

  (define (capability-difference caps1 caps2)
    "Set difference: capabilities in caps1 but not caps2."
    (filter (lambda (c) (not (memq c caps2))) caps1))

  (define (capability-audit-enable! signing-key)
    "Enable signed attestations for capability changes."
    (set! *capability-audit* signing-key)
    'audit-enabled)

  ;; Register core capabilities at load time
  ;; Wrapped in define to satisfy R6RS body ordering (definitions before expressions)
  (define initialize-capabilities
    (begin
      (capability-add! 'ed25519-sign)
      (capability-add! 'ed25519-verify)
      (capability-add! 'sha256-hash)
      (capability-add! 'argon2id-kdf)
      (capability-add! 'chacha20-poly1305)
      (capability-add! 'lamport-clock)
      (capability-add! 'spki-certs)
      (capability-add! 'audit-trail)
      #t))

  ;;; ============================================================================
  ;;; Address Parsing (Memo-041)
  ;;; ============================================================================

  (define (make-address principal role capabilities path)
    "Create an address record"
    (list 'address principal role capabilities path))

  (define (address? obj)
    "Check if object is an address"
    (and (pair? obj) (eq? (car obj) 'address)))

  (define (address-principal addr)
    (if (address? addr) (list-ref addr 1) #f))

  (define (address-role addr)
    (if (address? addr) (list-ref addr 2) #f))

  (define (address-capabilities addr)
    (if (address? addr) (list-ref addr 3) '()))

  (define (address-path addr)
    (if (address? addr) (list-ref addr 4) #f))

  (define (address->string addr)
    "Convert address back to string form"
    (if (not (address? addr))
        (error 'vault "Not an address" addr)
        (let ((principal (address-principal addr))
              (role (address-role addr))
              (caps (address-capabilities addr))
              (path (address-path addr)))
          (string-append
           "@" principal
           (cond
            ((and role (not (null? caps)))
             (string-append "+" role "{" (string-intersperse caps ",") "}"))
            (role
             (string-append "+" role))
            ((not (null? caps))
             (string-append "+{" (string-intersperse caps ",") "}"))
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
           ((null? chars)
            (if (null? current)
                (reverse result)
                (reverse (cons (string-trim-both (list->string (reverse current)))
                               result))))
           ((char=? (car chars) #\()
            (loop (cdr chars) (cons (car chars) current) (+ depth 1) result))
           ((char=? (car chars) #\))
            (loop (cdr chars) (cons (car chars) current) (- depth 1) result))
           ((and (char=? (car chars) #\,) (= depth 0))
            (loop (cdr chars)
                  '()
                  0
                  (cons (string-trim-both (list->string (reverse current)))
                        result)))
           (else
            (loop (cdr chars) (cons (car chars) current) depth result))))))

  (define (parse-address str)
    "Parse a cyberspace address string into components
     Returns: (address principal role capabilities path) or #f on failure"
    (if (not (string-prefix? "@" str))
        #f
        (let* ((without-at (substring str 1 (string-length str)))
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
                     (path (substring without-at (+ colon-pos 1) (string-length without-at)))
                     (plus-pos (string-index before-colon #\+)))
                (if (not plus-pos)
                    (make-address before-colon #f '() path)
                    (let* ((principal (substring before-colon 0 plus-pos))
                           (context (substring before-colon (+ plus-pos 1) (string-length before-colon)))
                           (brace-pos (string-index context #\{)))
                      (if (not brace-pos)
                          (make-address principal context '() path)
                          (let* ((role-part (if (= brace-pos 0)
                                               #f
                                               (substring context 0 brace-pos)))
                                 (caps-str (let ((end (string-index context #\})))
                                            (if end
                                                (substring context (+ brace-pos 1) end)
                                                "")))
                                 (caps (parse-capabilities caps-str)))
                            (make-address principal role-part caps path))))))))))

  ;;; ============================================================================
  ;;; Soup Hashing & Proofs (Memo-047)
  ;;; ============================================================================

  (define (soup-hash-file path)
    "Compute SHA-512 hash of file"
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
    "Generate inclusion proof for a chunk of a file (Memo-047)"
    (handle-exceptions exn #f
      (let ((content (with-input-from-file path (lambda () (read-string)))))
        (merkle-prove (string->blob content) chunk-index))))

  (define (soup-verify-chunk path chunk-index proof)
    "Verify inclusion proof against a file's Merkle root (Memo-047)"
    (handle-exceptions exn #f
      (let* ((content (with-input-from-file path (lambda () (read-string))))
             (root (merkle-root (string->blob content))))
        (and (= chunk-index (merkle-proof-chunk-index proof))
             (merkle-verify-proof root proof)))))

  ;;; ============================================================================
  ;;; Soup Display
  ;;; ============================================================================

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

  (define (get-tag-commit tag)
    "Get commit hash for a git tag"
    (handle-exceptions exn #f
      (let ((result (with-input-from-pipe
                      (format #f "git rev-list -n1 ~a 2>/dev/null" (shell-escape tag))
                      read-line)))
        (if (eof-object? result) #f result))))

  (define (get-tag-date tag)
    "Get creation date of git tag"
    (handle-exceptions exn #f
      (let ((ts (with-input-from-pipe
                 (format #f "git log -1 --format=%ct ~a 2>/dev/null" (shell-escape tag))
                 read-line)))
        (if (and ts (not (eof-object? ts)))
            (format-timestamp (string->number ts))
            #f))))

  (define (find-archive-for-release version)
    "Find archive file for a release version"
    (let ((patterns (list (format #f "vault-~a.archive" version)
                          (format #f "~a.archive" version)
                          (format #f "genesis-~a.archive" version))))
      (let loop ((ps patterns))
        (cond ((null? ps) #f)
              ((file-exists? (car ps)) (car ps))
              (else (loop (cdr ps)))))))

  (define (soup-releases)
    "Detailed view of all releases with status"
    (let* ((tags (get-git-tags))
           (max-tag-len (if (null? tags) 10 (apply max (map string-length tags))))
           (col-width (max 20 (+ max-tag-len 3))))
      (print "")
      (print (string-append
        "╭" (make-string 76 #\-) "╮"))
      (print "│ Releases                                                                   │")
      (print (string-append
        "├" (make-string 76 #\-) "┤"))
      (printf "│ ~a~aCommit       Signed  Archived  Date       │~%"
              "Version"
              (make-string (- col-width 7) #\space))
      (print (string-append
        "├" (make-string 76 #\-) "┤"))

      (for-each
       (lambda (tag)
         (let* ((commit (get-tag-commit tag))
                (commit-short (if commit (substring commit 0 (min 8 (string-length commit))) "--------"))
                (sig-file (format #f ".vault/releases/~a.sig" tag))
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
       ;; sort pred list (Chez order)
       (sort string>? tags))

      (print (string-append
        "╰" (make-string 76 #\-) "╯"))
      (print "")))

  ;;; ============================================================================
  ;;; Core Operations
  ;;; ============================================================================

  (define (get-environment-snapshot)
    "Capture current build environment"
    `((platform ,(or (get-environment-variable "OSTYPE") "unknown"))
      (hostname ,(or (get-environment-variable "HOSTNAME") "unknown"))
      (scheme-version "chez")
      (timestamp ,(current-seconds))))

  (define (get-dependencies-snapshot)
    "Capture current dependencies"
    '())

  (define (get-git-state-snapshot)
    "Capture git repository state"
    (let ((branch (with-input-from-pipe "git branch --show-current" read-line))
          (remote (with-input-from-pipe "git remote -v" read-line)))
      `((branch ,branch)
        (remote ,remote))))

  (define (save-commit-metadata commit-hash . opts)
    "Save optional metadata for a commit"
    (let ((message (get-key opts 'message: #f))
          (catalog (get-key opts 'catalog: #f))
          (subjects (get-key opts 'subjects: #f))
          (keywords (get-key opts 'keywords: #f))
          (description (get-key opts 'description: #f))
          (preserve (get-key opts 'preserve: #f)))
      (create-directory ".vault/metadata" #t)

      (let ((metadata-file (format #f ".vault/metadata/~a.sexp" commit-hash))
            (timestamp (current-seconds)))

        (let ((metadata (list 'commit-metadata
                             (list 'hash commit-hash)
                             (list 'timestamp timestamp)
                             (list 'message message))))

          (when (or catalog subjects keywords description)
            (let ((catalog-entry (list 'catalog)))
              (when subjects
                (set! catalog-entry (append catalog-entry (list (cons 'subjects subjects)))))
              (when keywords
                (set! catalog-entry (append catalog-entry (list (cons 'keywords keywords)))))
              (when description
                (set! catalog-entry (append catalog-entry (list (list 'description description)))))
              (set! metadata (append metadata (list catalog-entry)))))

          (when preserve
            (set! metadata
              (append metadata
                     (list (list 'preservation
                                (list 'environment (get-environment-snapshot))
                                (list 'dependencies (get-dependencies-snapshot))
                                (list 'git-state (get-git-state-snapshot)))))))

          (with-output-to-file metadata-file
            (lambda ()
              (write metadata)
              (newline)))

          (when (file-exists? metadata-file)
            (session-stat! 'writes)
            (session-stat! 'bytes-written (file-size metadata-file)))

          (when (vault-config 'track-metadata)
            (system (format #f "git add ~a" (shell-escape metadata-file))))))))

  (define (seal-commit message . opts)
    "Seal changes into the vault"
    (let ((files (get-key opts 'files: #f))
          (catalog (get-key opts 'catalog: #f))
          (subjects (get-key opts 'subjects: #f))
          (keywords (get-key opts 'keywords: #f))
          (description (get-key opts 'description: #f))
          (preserve (get-key opts 'preserve: #f)))
      (session-stat! 'commits)
      (lamport-tick!)

      (when files
        (apply run-command (cons "git" (cons "add" files))))
      (run-command "git" "add" "-u")

      (run-command "git" "commit" "-m" message)

      (let ((commit-hash (with-input-from-pipe "git rev-parse HEAD" read-line)))

        (when (or catalog subjects keywords description preserve)
          (save-commit-metadata commit-hash
                               'message: message
                               'catalog: catalog
                               'subjects: subjects
                               'keywords: keywords
                               'description: description
                               'preserve: preserve))

        (let ((signing-key (vault-config 'signing-key)))
          (when signing-key
            (audit-append
             'actor: (get-vault-principal signing-key)
             'action: (list 'seal-commit commit-hash)
             'motivation: message)))
        (lamport-save!))))

  (define (seal-update . opts)
    "Update vault from origin"
    (let ((branch (get-key opts 'branch: #f)))
      (let ((target (or branch "origin/main")))
        (run-command "git" "pull" "--ff-only"))))

  (define (seal-undo . opts)
    "Undo changes"
    (let ((file (get-key opts 'file: #f))
          (hard (get-key opts 'hard: #f)))
      (cond
       (file
        (run-command "git" "restore" file))
       (hard
        (run-command "git" "reset" "--hard" "HEAD"))
       (else
        (run-command "git" "reset" "--soft" "HEAD~1")))))

  (define (seal-history . opts)
    "Show vault history"
    (let ((count (get-key opts 'count: #f)))
      (let ((limit (or count 10)))
        (run-command "git" "log"
                 "--oneline"
                 "--decorate"
                 "--graph"
                 (format #f "-~a" limit)))))

  (define (seal-branch name . opts)
    "Create and switch to new sealed branch"
    (let ((from (get-key opts 'from: #f)))
      (if from
          (run-command "git" "checkout" "-b" name from)
          (run-command "git" "checkout" "-b" name))))

  (define (seal-merge from . opts)
    "Merge sealed changes from another branch"
    (let ((strategy (get-key opts 'strategy: #f)))
      (if strategy
          (run-command "git" "merge" from "-s" strategy)
          (run-command "git" "merge" from))))

  ;;; ============================================================================
  ;;; Version Management
  ;;; ============================================================================

  (define-record-type sealed-release
    (fields version hash timestamp signer signature))

  (define (seal-release version . opts)
    "Create a cryptographically sealed release"
    (let ((name (get-key opts 'name: #f))
          (message (get-key opts 'message: #f))
          (migrate-from (get-key opts 'migrate-from: #f)))

      (unless (and (valid-semver? version)
                   (= 3 (length (string-split version "."))))
        (error 'vault "Invalid semantic version (expected X.Y.Z)" version))

      (let ((hash (with-input-from-pipe "git rev-parse HEAD" read-line))
            (timestamp (current-seconds)))

        (let ((tag-message (or message
                               (if name
                                   (format #f "Release ~a (~a)" version name)
                                   (format #f "Release ~a" version)))))
          (run-command "git" "tag" "-a" version "-m" tag-message))

        (let ((signing-key (vault-config 'signing-key)))
          (when signing-key
            (seal-sign-release version name hash signing-key)))

        (when migrate-from
          (create-migration-marker migrate-from version))

        (if name
            (print "Sealed release: " version " (" name ") at " hash)
            (print "Sealed release: " version " at " hash)))))

  (define (seal-sign-release version name hash signing-key)
    "Sign a release with SPKI certificate"
    (let ((manifest (if name
                        (format #f "(release ~s ~s ~s ~s)" version name hash (current-seconds))
                        (format #f "(release ~s ~s ~s)" version hash (current-seconds)))))
      (let* ((sig-hash (sha512-hash manifest))
             (signature (ed25519-sign signing-key sig-hash)))

        (let ((sig-file (format #f ".vault/releases/~a.sig" version)))
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

  (define (seal-verify version . opts)
    "Verify cryptographic seal on a release"
    (let ((verify-key (get-key opts 'verify-key: #f)))
      (let ((sig-file (format #f ".vault/releases/~a.sig" version))
            (key (or verify-key (vault-config 'verify-key))))

        (unless (file-exists? sig-file)
          (error 'vault "No signature found for release" version))

        (unless key
          (error 'vault "No verification key configured"))

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
                  #f)))))))

  ;;; ============================================================================
  ;;; Node Roles - Memo-037
  ;;; ============================================================================

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

  (define *role-hierarchy* '(coordinator full witness archiver edge))

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

  (define *current-node-role* #f)
  (define *node-capabilities* #f)

  (define *weave-strata*
    '((constrained . 500)
      (standard    . 1000)
      (capable     . 2000)
      (powerful    . 4000)))

  (define (weave-stratum weave)
    "Which stratum of the lattice does this weave occupy? (Memo-056)"
    (cond
      ((< weave 500)  'constrained)
      ((< weave 1000) 'standard)
      ((< weave 2000) 'capable)
      (else           'powerful)))

  (define (measure-weave)
    "Benchmark crypto ops/second - the node's computational essence."
    (handle-exceptions exn 0.0
      (let* ((test-data (make-blob 64))
             (iterations 5000)
             (start (current-process-milliseconds)))
        (do ((i 0 (+ i 1))) ((= i iterations))
          (sha512-hash test-data))
        (let* ((elapsed (max 1 (- (current-process-milliseconds) start)))
               (ops-per-sec (/ (* iterations 1000.0) elapsed)))
          (/ (round (* (/ ops-per-sec 1000.0) 10)) 10.0)))))

  (define (get-cpu-cores)
    (handle-exceptions exn 1
      (let ((result (with-input-from-pipe
                      "sysctl -n hw.ncpu 2>/dev/null || nproc 2>/dev/null || echo 1"
                      read-line)))
        (if (eof-object? result) 1 (or (string->number result) 1)))))

  (define (get-ram-gb)
    (handle-exceptions exn 1
      (let ((result (with-input-from-pipe
                      "sysctl -n hw.memsize 2>/dev/null | awk '{print int($1/1073741824)}' || free -g 2>/dev/null | awk '/^Mem:/{print $2}' || echo 1"
                      read-line)))
        (if (eof-object? result) 1 (or (string->number result) 1)))))

  (define (get-load-average)
    (handle-exceptions exn 0.0
      (let ((result (with-input-from-pipe
                      "uptime | awk -F'load averages?: ' '{print $2}' | awk -F'[, ]' '{print $1}'"
                      read-line)))
        (if (eof-object? result) 0.0 (or (string->number result) 0.0)))))

  (define (get-available-storage-gb)
    (handle-exceptions exn 10
      (let ((result (with-input-from-pipe
                      "df -g . 2>/dev/null | tail -1 | awk '{print $4}' || df -BG . 2>/dev/null | tail -1 | awk '{gsub(/G/,\"\",$4); print $4}' || echo 10"
                      read-line)))
        (if (eof-object? result) 10 (or (string->number result) 10)))))

  (define (detect-storage-type)
    (handle-exceptions exn 'unknown
      (let ((result (with-input-from-pipe
                      "diskutil info / 2>/dev/null | grep 'Solid State' | grep -c Yes || echo 0"
                      read-line)))
        (if (and (not (eof-object? result)) (equal? result "1"))
            'ssd
            'hdd))))

  (define (detect-network-type)
    (handle-exceptions exn 'unknown
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
    (let ((net-type (detect-network-type)))
      (case net-type
        ((ethernet) 10)
        ((wifi) 30)
        ((satellite) 600)
        ((cellular) 100)
        (else 50))))

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
       ((and (>= cores 4) (>= ram 8) (<= latency 50))
        'coordinator)
       ((and (>= cores 2) (>= ram 4) (>= storage-gb 500))
        'full)
       ((>= storage-gb 1000)
        'archiver)
       ((>= storage-gb 100)
        'witness)
       (else 'edge))))

  (define (node-probe)
    "Probe local system capabilities and display results"
    (let ((caps (probe-system-capabilities)))
      (set! *node-capabilities* caps)

      (print "")
      (print "Node Capability Probe")
      (print (repeat-string "-" 50))

      (let ((compute (cdr (assq 'compute caps))))
        (print "")
        (print " Compute")
        (printf "   Cores:     ~a~%" (cdr (assq 'cores compute)))
        (printf "   RAM:       ~a GB~%" (cdr (assq 'ram-gb compute)))
        (printf "   Load:      ~a~%" (cdr (assq 'load-avg compute))))

      (let ((storage (cdr (assq 'storage caps))))
        (print "")
        (print " Storage")
        (printf "   Available: ~a GB~%" (cdr (assq 'available-gb storage)))
        (printf "   Type:      ~a~%" (cdr (assq 'type storage))))

      (let ((network (cdr (assq 'network caps))))
        (print "")
        (print " Network")
        (printf "   Type:      ~a~%" (cdr (assq 'type network)))
        (printf "   Latency:   ~a ms (estimated)~%" (cdr (assq 'latency-ms network))))

      (let ((security (cdr (assq 'security caps))))
        (print "")
        (print " Security")
        (printf "   Signing key:  ~a~%" (if (cdr (assq 'signing-key security)) "present" "absent"))
        (printf "   Verify key:   ~a~%" (if (cdr (assq 'verify-key security)) "present" "absent")))

      (let ((recommended (recommend-role caps)))
        (print "")
        (print (repeat-string "-" 50))
        (printf " Recommended Role: ~a~%" recommended)
        (let ((desc (cdr (assq 'description (cdr (assq recommended *node-roles*))))))
          (printf "   ~a~%" desc)))

      (print "")
      caps))

  (define (node-role-file)
    (let ((home (get-environment-variable "HOME")))
      (make-pathname (list home ".cyberspace") "node-role")))

  (define (load-node-role)
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
    (let ((role-file (node-role-file)))
      (create-directory (pathname-directory role-file) #t)
      (with-output-to-file role-file
        (lambda ()
          (write `(node-config
                   (role ,role)
                   (updated ,(current-seconds))))
          (newline)))))

  (define (role-level role)
    (let loop ((roles *role-hierarchy*) (level 0))
      (cond
       ((null? roles) 999)
       ((eq? (car roles) role) level)
       (else (loop (cdr roles) (+ level 1))))))

  (define (node-role . args)
    "Get or set current node role"
    (cond
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

     (else
      (let ((new-role (car args)))
        (unless (assq new-role *node-roles*)
          (error 'vault "Unknown role. Valid roles:" (map car *node-roles*)))
        (let ((old-role *current-node-role*))
          (set! *current-node-role* new-role)
          (save-node-role new-role)

          (let ((signing-key (vault-config 'signing-key)))
            (when (and signing-key old-role)
              (audit-append
               'actor: (get-vault-principal signing-key)
               'action: `(node-role-change ,old-role ,new-role)
               'motivation: "Node role changed")))

          (printf "Role set: ~a -> ~a~%" (or old-role 'none) new-role)
          new-role)))))

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
      (print (repeat-string "-" 50))

      (if key
          (let* ((principal (get-vault-principal key))
                 (announcement
                  `(node-role-announcement
                    (principal ,(blob->hex principal))
                    (role ,role)
                    (capabilities ,caps)
                    (timestamp ,(current-seconds)))))

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

              `(signed-announcement
                ,announcement
                (signature ,(blob->hex signature)))))

          (begin
            (print " No signing key configured")
            (print " Run: (vault-init 'signing-key: <key>)")
            (print "")
            #f))))

  ;;; ============================================================================
  ;;; Archival and Restoration
  ;;; ============================================================================

  (define (seal-archive version . opts)
    "Create sealed archive of a version"
    (let ((fmt (or (get-key opts 'format: #f) (vault-config 'archive-format)))
          (out (or (get-key opts 'output: #f) (format #f "vault-~a.archive" version))))

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
         (error 'vault "Unknown archive format" fmt)))

      (when (file-exists? out)
        (session-stat! 'writes)
        (session-stat! 'bytes-written (file-size out)))
      (print "Archive sealed: " out)
      out))

  (define (seal-archive-tarball version output)
    (run-command "git" "archive"
             "--format=tar.gz"
             (format #f "--output=~a" output)
             "--prefix=vault/"
             version))

  (define (seal-archive-bundle version output)
    (run-command "git" "bundle" "create" output version))

  (define (seal-archive-cryptographic version output)
    "Create encrypted archive with SPKI signature (legacy gzip format)"
    (let ((tarball (format #f "~a.tar.gz" output)))
      (seal-archive-tarball version tarball)

      (let ((signing-key (vault-config 'signing-key)))
        (when signing-key
          (let* ((tarball-bytes (read-file-bytes tarball))
                 (tarball-hash (sha512-hash tarball-bytes))
                 (signature (ed25519-sign signing-key tarball-hash)))

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
    "Create zstd-compressed, age-encrypted archive with SPKI signature"
    (let ((recipients (vault-config 'age-recipients))
          (signing-key (vault-config 'signing-key))
          (encrypted-file (format #f "~a.tar.zst.age" output)))

      (unless (pair? recipients)
        (error 'vault "No age recipients configured. Use (vault-config 'age-recipients '(\"age1...\"))"))

      (let ((recipient-args (string-intersperse
                             (map (lambda (r) (format #f "-r ~a" r)) recipients)
                             " ")))

        (let ((temp-tar (format #f "/tmp/vault-~a-~a.tar" version (current-seconds))))
          (run-command "git" "archive" "--prefix=vault/" (format #f "--output=~a" temp-tar) version)

          (system (format #f "zstd -T0 -c ~a | age ~a > ~a"
                          (shell-escape temp-tar) recipient-args (shell-escape encrypted-file)))

          (delete-file temp-tar))

        (when signing-key
          (let* ((archive-bytes (read-file-bytes encrypted-file))
                 (archive-hash (sha512-hash archive-bytes))
                 (signature (ed25519-sign signing-key archive-hash)))

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

  (define (seal-restore archive . opts)
    "Restore from sealed archive with verification"
    (let ((verify-key (get-key opts 'verify-key: #f))
          (target (get-key opts 'target: #f))
          (identity (get-key opts 'identity: #f)))
      (let ((target-dir (or target ".")))

        (let ((manifest (with-input-from-file archive read)))

          (unless (eq? (car manifest) 'sealed-archive)
            (error 'vault "Unknown archive format" (car manifest)))

          (let ((fmt (cadr (assq 'format (cdr manifest)))))
            (case fmt
              ((cryptographic)
               (seal-restore-cryptographic manifest verify-key target-dir))
              ((zstd-age)
               (seal-restore-zstd-age manifest verify-key target-dir identity))
              (else
               (error 'vault "Unknown sealed archive format" fmt))))))))

  (define (seal-restore-cryptographic manifest verify-key target-dir)
    (let ((version (cadr (assq 'version (cdr manifest))))
          (tarball (cadr (assq 'tarball (cdr manifest))))
          (hash-hex (cadr (assq 'hash (cdr manifest))))
          (sig-hex (cadr (assq 'signature (cdr manifest)))))

      (print "Restoring sealed archive: " version)

      (when verify-key
        (let* ((tarball-bytes (read-file-bytes tarball))
               (tarball-hash (sha512-hash tarball-bytes))
               (expected-hash (hex->blob hash-hex))
               (signature (hex->blob sig-hex))
               (pubkey (read-key-from-file verify-key)))

          (unless (equal? tarball-hash expected-hash)
            (error 'vault "Archive hash mismatch"))

          (unless (ed25519-verify pubkey tarball-hash signature)
            (error 'vault "Archive signature verification failed"))

          (print "✓ Archive seal verified")))

      (run-command "tar" "-xzf" tarball "-C" target-dir)
      (print "Archive restored to: " target-dir)))

  (define (seal-restore-zstd-age manifest verify-key target-dir identity)
    (let ((version (cadr (assq 'version (cdr manifest))))
          (archive-file (cadr (assq 'archive (cdr manifest))))
          (hash-hex (cadr (assq 'hash (cdr manifest))))
          (sig-hex (cadr (assq 'signature (cdr manifest))))
          (id-file (or identity (vault-config 'age-identity))))

      (print "Restoring zstd+age sealed archive: " version)

      (unless id-file
        (error 'vault "No age identity configured. Use 'identity: parameter or (vault-config 'age-identity \"path\")"))

      (when verify-key
        (let* ((archive-bytes (read-file-bytes archive-file))
               (archive-hash (sha512-hash archive-bytes))
               (expected-hash (hex->blob hash-hex))
               (signature (hex->blob sig-hex))
               (pubkey (read-key-from-file verify-key)))

          (unless (equal? archive-hash expected-hash)
            (error 'vault "Archive hash mismatch - possible tampering"))

          (unless (ed25519-verify pubkey archive-hash signature)
            (error 'vault "Archive signature verification failed"))

          (print "✓ SPKI signature verified")))

      (let ((cmd (format #f "age -d -i ~a < ~a | zstd -d | tar -xf - -C ~a"
                         (shell-escape id-file)
                         (shell-escape archive-file)
                         (shell-escape target-dir))))
        (let ((result (system cmd)))
          (unless (zero? result)
            (error 'vault "Failed to decrypt/extract archive"))))

      (print "✓ Archive decrypted and restored to: " target-dir)))

  ;;; ============================================================================
  ;;; Replication
  ;;; ============================================================================

  (define (tag-exists? tag-name)
    "Check if git tag exists"
    (let ((tags (with-input-from-pipe
                  (format #f "git tag -l ~a" (shell-escape tag-name))
                  read-string)))
      (not (string=? (string-trim-both tags) ""))))

  (define (git-remote? str)
    (or (string-contains str "git@")
        (string-contains str ".git")
        (member str '("origin" "upstream"))))

  (define (http-url? str)
    (or (string-prefix? "http://" str)
        (string-prefix? "https://" str)))

  (define (seal-publish version . opts)
    "Publish sealed release to remote location"
    (let ((remote (get-key opts 'remote: #f))
          (archive-format (get-key opts 'archive-format: #f))
          (message (get-key opts 'message: #f)))
      (let ((remote-target (or remote (vault-config 'publish-remote)))
            (fmt (or archive-format 'cryptographic)))

        (unless remote-target
          (error 'vault "No remote configured for publication"))

        (let ((archive-file (format #f "vault-~a.archive" version)))

          (print "Publishing sealed release: " version)

          (unless (tag-exists? version)
            (seal-release version 'message: message))

          (seal-archive version 'format: fmt 'output: archive-file)

          (print "Archive created: " archive-file)

          (cond
           ((git-remote? remote-target)
            (print "Pushing to git remote: " remote-target)
            (run-command "git" "push" remote-target version)
            (print "✓ Tag pushed to remote")

            (when (vault-config 'upload-release-assets)
              (upload-release-asset remote-target version archive-file)))

           ((http-url? remote-target)
            (publish-http remote-target version archive-file))

           ((directory-exists? remote-target)
            (publish-filesystem remote-target version archive-file))

           (else
            (error 'vault "Unknown remote type" remote-target)))

          (let ((signing-key (vault-config 'signing-key)))
            (when signing-key
              (audit-append
               'actor: (get-vault-principal signing-key)
               'action: (list 'seal-publish version remote-target)
               'motivation: (or message (format #f "Published release ~a" version)))))

          (print "✓ Publication complete: " version)))))

  (define (seal-subscribe remote . opts)
    "Subscribe to sealed releases from remote source"
    (let ((target (get-key opts 'target: #f))
          (verify-key (get-key opts 'verify-key: #f)))
      (let ((target-dir (or target (vault-config 'subscribe-dir) ".vault/subscriptions"))
            (remote-source remote))

        (print "Subscribing to releases from: " remote-source)

        (create-directory target-dir #t)

        (let ((releases
               (cond
                ((git-remote? remote-source)
                 (fetch-git-releases remote-source))
                ((http-url? remote-source)
                 (fetch-http-releases remote-source))
                ((directory-exists? remote-source)
                 (fetch-filesystem-releases remote-source))
                (else
                 (error 'vault "Unknown remote type" remote-source)))))

          (print "Found " (length releases) " release(s)")

          (for-each
           (lambda (release-info)
             (let ((version (car release-info))
                   (url (cadr release-info)))
               (print "  Downloading: " version)
               (download-release url target-dir version)

               (when verify-key
                 (let ((archive-path (format #f "~a/vault-~a.archive" target-dir version)))
                   (seal-verify archive-path 'verify-key: verify-key)
                   (print "  ✓ Verified: " version)))))
           releases)

          (let ((signing-key (vault-config 'signing-key)))
            (when signing-key
              (audit-append
               'actor: (get-vault-principal signing-key)
               'action: (list 'seal-subscribe remote-source)
               'motivation: (format #f "Subscribed to ~a release(s)" (length releases)))))

          (print "✓ Subscription complete: " (length releases) " release(s) downloaded")))))

  (define (seal-synchronize remote . opts)
    "Synchronize sealed releases bidirectionally"
    (let ((direction (get-key opts 'direction: #f))
          (verify-key (get-key opts 'verify-key: #f)))
      (let ((sync-direction (or direction 'both))
            (remote-target remote))

        (print "Synchronizing with: " remote-target)

        (let ((local-releases (get-local-releases)))
          (print "Local releases: " (length local-releases))

          (let ((remote-releases (get-remote-releases remote-target)))
            (print "Remote releases: " (length remote-releases))

            (let ((to-push (filter (lambda (v) (not (member v remote-releases))) local-releases))
                  (to-pull (filter (lambda (v) (not (member v local-releases))) remote-releases)))

              (print "To publish: " (length to-push))
              (print "To subscribe: " (length to-pull))

              (when (or (eq? sync-direction 'push) (eq? sync-direction 'both))
                (for-each
                 (lambda (version)
                   (print "  Publishing: " version)
                   (seal-publish version 'remote: remote-target))
                 to-push))

              (when (or (eq? sync-direction 'pull) (eq? sync-direction 'both))
                (for-each
                 (lambda (version)
                   (print "  Subscribing: " version)
                   (download-single-release remote-target version verify-key))
                 to-pull))

              (let ((signing-key (vault-config 'signing-key)))
                (when signing-key
                  (audit-append
                   'actor: (get-vault-principal signing-key)
                   'action: (list 'seal-synchronize remote-target)
                   'motivation: (format #f "Synced ~a out, ~a in"
                                        (length to-push) (length to-pull)))))

              (print "✓ Synchronization complete")))))))

  ;;; Replication helpers

  (define (publish-http url version archive-file)
    (let* ((target (format #f "~a/~a" url version))
           (cmd (format #f "curl -s -f -X PUT -T ~a ~a"
                        (shell-escape archive-file) (shell-escape target)))
           (result (system cmd)))
      (if (= result 0)
          (print "✓ Published " archive-file " to " target)
          (error 'vault "publish-http: curl failed" target result))))

  (define (publish-filesystem target-dir version archive-file)
    (let ((dest (format #f "~a/vault-~a.archive" target-dir version)))
      (create-directory target-dir #t)
      (run-command "cp" archive-file dest)
      (print "✓ Copied to: " dest)))

  (define (fetch-git-releases remote)
    (run-command "git" "fetch" remote "--tags")
    (with-input-from-pipe
        "git tag -l '[0-9]*.[0-9]*.[0-9]*'"
      (lambda ()
        (let loop ((tags '()))
          (let ((line (read-line)))
            (if (eof-object? line)
                (reverse tags)
                (loop (cons line tags))))))))

  (define (fetch-http-releases url)
    (let ((target (format #f "~a/releases.txt" url)))
      (handle-exceptions exn '()
        (let ((lines (with-input-from-pipe
                       (format #f "curl -s -f ~a" (shell-escape target))
                       read-lines)))
          (filter (lambda (s) (not (string=? s ""))) lines)))))

  (define (fetch-filesystem-releases dir)
    "Fetch releases from filesystem directory (replaces irregex version)"
    (if (directory-exists? dir)
        (filter-map
          (lambda (f)
            (and (string-prefix? "vault-" f)
                 (string-suffix? ".archive" f)
                 (let ((version (substring f 6 (- (string-length f) 8))))
                   (list version (string-append dir "/" f)))))
          (filter (lambda (f) (string-suffix? ".archive" f))
                  (directory dir)))
        '()))

  (define (download-release url target-dir version)
    (let* ((dest (format #f "~a/vault-~a.archive" target-dir version))
           (cmd (format #f "curl -s -f -o ~a ~a"
                        (shell-escape dest) (shell-escape url))))
      (create-directory target-dir #t)
      (let ((result (system cmd)))
        (if (= result 0)
            (begin (print "✓ Downloaded to " dest) dest)
            (error 'vault "download-release: curl failed" url result)))))

  (define (download-single-release remote version verify-key)
    (let ((target-dir (or (vault-config 'archive-dir) ".vault/subscriptions")))
      (cond
       ((http-url? remote)
        (let ((url (format #f "~a/vault-~a.archive" remote version)))
          (download-release url target-dir version)))
       ((git-remote? remote)
        (run-command "git" "fetch" remote "tag" version)
        (print "✓ Fetched tag " version " from " remote))
       (else
        (let ((src (format #f "~a/vault-~a.archive" remote version)))
          (download-release src target-dir version))))))

  (define (get-local-releases)
    (with-input-from-pipe
        "git tag -l '[0-9]*.[0-9]*.[0-9]*'"
      (lambda ()
        (let loop ((tags '()))
          (let ((line (read-line)))
            (if (eof-object? line)
                (reverse tags)
                (loop (cons line tags))))))))

  (define (get-remote-releases remote)
    (if (git-remote? remote)
        (fetch-git-releases remote)
        '()))

  (define (upload-release-asset remote version archive-file)
    (if (http-url? remote)
        (publish-http remote version archive-file)
        (print "upload-release-asset: non-HTTP remotes use git push")))

  ;;; ============================================================================
  ;;; Migration Paths
  ;;; ============================================================================

  (define (create-migration-marker from-version to-version)
    "Create migration path marker"
    (let ((migration-file (format #f "~a/~a-to-~a.scm"
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

) ;; end library
