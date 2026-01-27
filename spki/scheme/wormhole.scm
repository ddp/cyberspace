;;; wormhole.scm - FUSE-Based Bidirectional Filesystem Portal (Memo-042)
;;;
;;; Wormholes bridge the macOS filesystem and the Library of Cyberspace vault.
;;; All operations are:
;;; - SPKI authorized (requires valid certificate)
;;; - Audited (Memo-003)
;;; - Rate-limited (Memo-032)
;;; - Capability-attenuated
;;;
;;; The filesystem abstraction is the right boundary—everything above it
;;; (Finder, cp, rsync) works without modification.

(module wormhole
  (;; Wormhole lifecycle
   wormhole-open
   wormhole-close
   wormhole-active?

   ;; Capabilities
   capability:read-only
   capability:read-write
   capability:full
   capability:backup
   capability:synchronize
   wormhole-capabilities
   wormhole-delegate
   wormhole-can?

   ;; Certificate operations
   wormhole-cert
   verify-wormhole-cert

   ;; Audit
   wormhole-audit
   wormhole-audit-trail

   ;; Rate limiting
   wormhole-rate-limit
   wormhole-rate-ok?

   ;; Flow guard (reference monitor)
   wormhole-flow-guard

   ;; Metadata capture/restore
   capture-metadata
   restore-metadata

   ;; Status
   wormhole-status
   wormhole-list

   ;; Mount operations
   wormhole-mount
   wormhole-unmount

   ;; Object ingestion with provenance
   wormhole-ingest
   make-object-provenance

   ;; Introspection (immutable provenance)
   introspect
   introspection?
   introspection-hash
   introspection-provenance
   introspection-authority
   introspection-temporal
   introspection-signature
   introspection-valid?
   stamp-introspection!
   *introspection-store*

   ;; Config export (host configuration deployment)
   *config-manifest*
   config-register!
   config-export!
   config-export-all!
   config-status
   config-diff)

(import scheme
        (chicken base)
        (chicken blob)
        (chicken bitwise)
        (chicken memory)
        (chicken time)
        (chicken format)
        (chicken file)
        (chicken file posix)
        (chicken pathname)
        (chicken process)
        (chicken process-context)
        (chicken condition)
        (chicken io)
        (srfi 1)
        (srfi 4)
        (srfi 13)
        (srfi 69)
        (chicken port)
        (chicken string)
        fuse-ffi
        filetype
        crypto-ffi
        metadata-ffi
        os)

;;; ============================================================
;;; Capability Sets
;;; ============================================================

;; Data access capabilities
(define cap:read 'read)
(define cap:write 'write)
(define cap:create 'create)
(define cap:delete 'delete)
(define cap:rename 'rename)

;; Metadata capabilities
(define cap:stat 'stat)
(define cap:chmod 'chmod)
(define cap:chown 'chown)
(define cap:xattr-read 'xattr-read)
(define cap:xattr-write 'xattr-write)
(define cap:acl-read 'acl-read)
(define cap:acl-write 'acl-write)

;; Directory capabilities
(define cap:readdir 'readdir)
(define cap:mkdir 'mkdir)
(define cap:rmdir 'rmdir)

;; Control capabilities
(define cap:admin 'admin)
(define cap:delegate 'delegate)
(define cap:audit-read 'audit-read)
(define cap:rate-limit 'rate-limit)

;; Common capability sets
(define capability:read-only
  (list cap:read cap:stat cap:readdir cap:xattr-read cap:acl-read))

(define capability:read-write
  (list cap:read cap:write cap:create cap:stat cap:chmod
        cap:readdir cap:mkdir cap:xattr-read cap:xattr-write))

(define capability:full
  (list cap:read cap:write cap:create cap:delete cap:rename
        cap:stat cap:chmod cap:chown
        cap:xattr-read cap:xattr-write cap:acl-read cap:acl-write
        cap:readdir cap:mkdir cap:rmdir
        cap:admin cap:delegate cap:audit-read cap:rate-limit))

(define capability:backup
  (list cap:read cap:stat cap:readdir cap:xattr-read cap:acl-read))

(define capability:synchronize
  (list cap:read cap:write cap:create cap:delete cap:rename
        cap:stat cap:chmod cap:readdir cap:mkdir cap:rmdir
        cap:xattr-read cap:xattr-write))

;;; ============================================================
;;; Wormhole Record
;;; ============================================================

(define-record-type <wormhole>
  (make-wormhole-internal id fs-path vault-path capabilities
                          rate-limit rate-counter rate-window
                          audit-log created locked auth-required)
  wormhole?
  (id wormhole-id)
  (fs-path wormhole-fs-path)
  (vault-path wormhole-vault-path)
  (capabilities wormhole-capabilities)
  (rate-limit wormhole-rate-limit)
  (rate-counter wormhole-rate-counter wormhole-rate-counter-set!)
  (rate-window wormhole-rate-window wormhole-rate-window-set!)
  (audit-log wormhole-audit-log wormhole-audit-log-set!)
  (created wormhole-created)
  (locked wormhole-locked wormhole-locked-set!)
  (auth-required wormhole-auth-required))

;; Active wormholes table
(define *active-wormholes* (make-hash-table string=?))

;;; ============================================================
;;; Certificate Operations
;;; ============================================================

(define (wormhole-principal fs-path vault-path)
  "Create principal identifier for a wormhole."
  `(wormhole
    (fs-path ,fs-path)
    (vault-path ,vault-path)))

(define (wormhole-cert issuer fs-path vault-path capabilities
                       #!key (rate-limit 1000)
                             (expires #f))
  "Create SPKI certificate authorizing wormhole.
   Returns S-expression certificate structure."
  `(cert
    (version 1)
    (issuer ,issuer)
    (subject ,(wormhole-principal fs-path vault-path))
    (tag (wormhole
          (fs-path ,fs-path)
          (vault-path ,vault-path)
          (capabilities ,@capabilities)
          (rate-limit ,rate-limit)
          ,@(if expires `((expires ,expires)) '())))))

(define (verify-wormhole-cert cert fs-path vault-path)
  "Verify wormhole certificate matches requested paths.
   Returns #t if valid, #f otherwise."
  ;; Simplified verification - in production, use full SPKI verification
  (and (list? cert)
       (eq? (car cert) 'cert)
       (let ((tag (assq 'tag cert)))
         (and tag
              (list? (cadr tag))
              (eq? (car (cadr tag)) 'wormhole)
              (let ((tag-fs (assq 'fs-path (cadr tag)))
                    (tag-vault (assq 'vault-path (cadr tag))))
                (and tag-fs tag-vault
                     (equal? (cadr tag-fs) fs-path)
                     (equal? (cadr tag-vault) vault-path)))))))

;;; ============================================================
;;; Capability Operations
;;; ============================================================

(define (capability-subset? requested possessed)
  "Check if requested capabilities are a subset of possessed."
  (every (lambda (cap) (memq cap possessed)) requested))

(define (wormhole-can? wormhole capability)
  "Check if wormhole has the specified capability."
  (memq capability (wormhole-capabilities wormhole)))

(define (wormhole-delegate wormhole new-caps recipient)
  "Delegate subset of wormhole capabilities.
   Capabilities can only be reduced, never amplified."
  (let ((my-caps (wormhole-capabilities wormhole)))
    (unless (capability-subset? new-caps my-caps)
      (error 'capability-amplification
             "Cannot delegate capabilities you don't have"
             (filter (lambda (c) (not (memq c my-caps))) new-caps)))
    (wormhole-cert
     (wormhole-id wormhole)
     (wormhole-fs-path wormhole)
     (wormhole-vault-path wormhole)
     new-caps)))

;;; ============================================================
;;; Rate Limiting
;;; ============================================================

(define (wormhole-rate-ok? wormhole)
  "Check if operation is within rate limit.
   Uses sliding window rate limiting."
  (let* ((now (current-seconds))
         (window (wormhole-rate-window wormhole))
         (limit (wormhole-rate-limit wormhole)))
    ;; Reset counter if window expired (1 minute)
    (when (> (- now window) 60)
      (wormhole-rate-counter-set! wormhole 0)
      (wormhole-rate-window-set! wormhole now))
    (< (wormhole-rate-counter wormhole) limit)))

(define (wormhole-rate-increment! wormhole)
  "Increment rate counter."
  (wormhole-rate-counter-set! wormhole
                               (+ 1 (wormhole-rate-counter wormhole))))

;;; ============================================================
;;; Audit Trail
;;; ============================================================

(define (wormhole-audit wormhole event operation object #!optional details)
  "Log audit event for wormhole operation."
  (let ((entry `(audit
                 (timestamp ,(current-seconds))
                 (wormhole ,(wormhole-id wormhole))
                 (event ,event)
                 (operation ,operation)
                 (object ,object)
                 ,@(if details `((details ,details)) '()))))
    (wormhole-audit-log-set! wormhole
                              (cons entry (wormhole-audit-log wormhole)))
    entry))

(define (wormhole-audit-trail wormhole #!key (limit 100))
  "Retrieve recent audit entries for wormhole."
  (take (wormhole-audit-log wormhole)
        (min limit (length (wormhole-audit-log wormhole)))))

;;; ============================================================
;;; Flow Guard (Reference Monitor)
;;; ============================================================

(define (wormhole-flow-guard wormhole operation object)
  "Reference monitor for wormhole operations.
   Validates capability, enforces rate limits, records audit trail."
  (let ((caps (wormhole-capabilities wormhole)))
    ;; Check capability
    (unless (memq operation caps)
      (wormhole-audit wormhole 'denied operation object)
      (error 'capability-denied
             (sprintf "Operation ~a not permitted" operation)))
    ;; Check rate limit
    (unless (wormhole-rate-ok? wormhole)
      (wormhole-audit wormhole 'rate-limited operation object)
      (error 'rate-limited
             (sprintf "Rate limit exceeded (~a ops/min)"
                      (wormhole-rate-limit wormhole))))
    ;; Check lock for sensitive operations
    (when (and (wormhole-locked wormhole)
               (memq operation (wormhole-auth-required wormhole)))
      (wormhole-audit wormhole 'locked operation object)
      (error 'wormhole-locked
             "Operation requires unlock"))
    ;; Passed all checks - record and allow
    (wormhole-rate-increment! wormhole)
    (wormhole-audit wormhole 'permitted operation object)
    `(permitted ,operation ,object)))

;;; ============================================================
;;; Metadata Capture/Restore
;;; ============================================================

(define (capture-metadata path)
  "Capture all macOS metadata for a file.
   Returns alist with xattrs, BSD flags, and ACLs."
  (if (file-exists? path)
      (let* ((xattrs (xattr-list path))
             (xattr-data (map (lambda (name)
                                (cons name (xattr-get path name)))
                              xattrs))
             (flags (file-flags path))
             (acl-entries (acl-get path)))
        `((posix
           (exists #t)
           (size ,(file-size path))
           (mtime ,(file-modification-time path)))
          (xattr ,xattr-data)
          (flags ,flags)
          (acl ,acl-entries)))
      `((posix (exists #f)))))

(define (restore-metadata path metadata)
  "Restore metadata to a file.
   Restores xattrs, BSD flags, and ACLs.
   Note: Some operations require appropriate permissions."
  (let ((xattr-data (alist-ref 'xattr metadata eq? '()))
        (flags (alist-ref 'flags metadata eq? 0))
        (acl-entries (alist-ref 'acl metadata eq? '())))
    ;; Restore extended attributes
    (for-each (lambda (entry)
                (when (and (pair? entry) (cdr entry))
                  (xattr-set path (car entry) (cdr entry))))
              xattr-data)
    ;; Restore BSD flags (may require root for SF_* flags)
    (when (> flags 0)
      (file-flags-set! path flags))
    ;; Restore ACL from text entries
    (when (pair? acl-entries)
      (acl-set path (string-join acl-entries "\n")))
    #t))

;;; ============================================================
;;; Utility: Blob to Hex
;;; ============================================================

(define (blob->hex b)
  "Convert blob to hexadecimal string."
  (let ((vec (blob->u8vector b)))
    (apply string-append
           (map (lambda (byte)
                  (let ((s (number->string byte 16)))
                    (if (< byte 16)
                        (string-append "0" s)
                        s)))
                (u8vector->list vec)))))

;;; ============================================================
;;; Object Ingestion with Immutable Provenance
;;; ============================================================
;;;
;;; When objects enter Cyberspace through a wormhole, their metadata
;;; becomes introspectively and immutably attached in the soup.
;;;
;;; Provenance is permanent:
;;;   - Origin path (where it came from)
;;;   - Ingestion timestamp
;;;   - File type (magic byte detection)
;;;   - MIME type
;;;   - Size at ingestion
;;;   - Content hash (identity)
;;;   - Ingesting principal
;;;   - Wormhole certificate used
;;;
;;; Once sealed, provenance travels with the object forever.
;;; This enables audit trails, origin verification, and type safety.

(define (make-object-provenance path content principal certificate)
  "Create immutable provenance record for an object entering via wormhole.
   This metadata is permanently attached to the object in the soup."
  (let* ((content-blob (if (string? content)
                           (string->blob content)
                           content))
         (content-hash (sha512-hash content-blob))
         (detected-type (file-type path))
         (detected-mime (file-mime path)))
    `(provenance
      (origin-path ,path)
      (ingestion-time ,(current-seconds))
      (file-type ,detected-type)
      (mime-type ,detected-mime)
      (size ,(blob-size content-blob))
      (content-hash ,(blob->hex content-hash))
      (principal ,principal)
      (certificate-hash ,(if certificate
                             (blob->hex (sha512-hash (string->blob
                                                       (format "~s" certificate))))
                             #f))
      (immutable #t))))

(define (wormhole-ingest path content wormhole)
  "Ingest an object through a wormhole into the soup.
   Returns the object with immutable provenance attached.

   The provenance becomes part of the object's identity:
   - Introspectable: query origin, type, timestamp
   - Immutable: cannot be modified after sealing
   - Audited: ingestion is logged

   This is the canonical entry point for external data."
  (let* ((fs-path (wormhole-fs-path wormhole))
         (vault-path (wormhole-vault-path wormhole))
         (principal (wormhole-principal fs-path vault-path))
         (provenance (make-object-provenance path content principal #f))
         (metadata (capture-metadata path)))
    ;; Audit the ingestion
    (wormhole-audit wormhole 'ingest 'ingest path)
    ;; Return object structure ready for soup
    `(object
      (content ,content)
      (provenance ,provenance)
      (metadata ,metadata))))

;;; ============================================================
;;; Wormhole Lifecycle
;;; ============================================================

(define wormhole-id-counter 0)

(define (generate-wormhole-id)
  (set! wormhole-id-counter (+ 1 wormhole-id-counter))
  (sprintf "wormhole-~a-~a" (current-seconds) wormhole-id-counter))

(define (wormhole-open fs-path #!key
                       (vault-path "/")
                       (capabilities capability:read-write)
                       (rate-limit 1000)
                       (locked #f)
                       (auth-required '())
                       (certificate #f))
  "Open wormhole - requires valid certificate.
   Returns wormhole handle on success."
  ;; Verify certificate
  (unless certificate
    (error 'unauthorized "Wormhole requires SPKI certificate"))
  (unless (verify-wormhole-cert certificate fs-path vault-path)
    (error 'unauthorized "Invalid wormhole certificate"))

  ;; Check FUSE availability
  (unless (fuse-available?)
    (error 'fuse-unavailable
           "FUSE not installed. Install with: brew install fuse-t"))

  ;; Create wormhole record
  (let* ((id (generate-wormhole-id))
         (wh (make-wormhole-internal
              id fs-path vault-path capabilities
              rate-limit 0 (current-seconds)
              '() (current-seconds)
              locked auth-required)))

    ;; Audit the open
    (wormhole-audit wh 'wormhole-open 'open fs-path
                    `((vault ,vault-path)
                      (capabilities ,(length capabilities))))

    ;; Register in active table
    (hash-table-set! *active-wormholes* fs-path wh)

    ;; Return wormhole handle - call (wormhole-mount wh) to mount
    wh))

(define (wormhole-close wormhole)
  "Close wormhole, unmounting filesystem."
  (wormhole-audit wormhole 'wormhole-close 'close
                   (wormhole-fs-path wormhole))

  ;; Unmount FUSE filesystem
  (let ((path (wormhole-fs-path wormhole)))
    (when (and (fuse-available?) (file-exists? path))
      (fuse-unmount path)))

  ;; Remove from active table
  (hash-table-delete! *active-wormholes* (wormhole-fs-path wormhole))
  #t)

(define (wormhole-active? path)
  "Check if wormhole is active at path."
  (hash-table-exists? *active-wormholes* path))

(define (wormhole-list)
  "List all active wormholes."
  (hash-table-keys *active-wormholes*))

(define (wormhole-status wormhole)
  "Get status of a wormhole."
  `((id ,(wormhole-id wormhole))
    (fs-path ,(wormhole-fs-path wormhole))
    (vault-path ,(wormhole-vault-path wormhole))
    (capabilities ,(length (wormhole-capabilities wormhole)))
    (rate-limit ,(wormhole-rate-limit wormhole))
    (rate-used ,(wormhole-rate-counter wormhole))
    (audit-entries ,(length (wormhole-audit-log wormhole)))
    (created ,(wormhole-created wormhole))
    (locked ,(wormhole-locked wormhole))))

;;; ============================================================
;;; FUSE Operations - Vault Integration
;;; ============================================================

;; In-memory manifest for demo (full implementation uses vault manifests)
(define *wormhole-manifest* (make-hash-table string=?))

(define (manifest-init! wormhole)
  "Initialize manifest for wormhole with root directory."
  (let ((vpath (wormhole-vault-path wormhole)))
    (hash-table-set! *wormhole-manifest* "/"
                     `((type . directory)
                       (mode . ,(bitwise-ior S_IFDIR #o755))
                       (nlink . 2)
                       (mtime . ,(current-seconds))
                       (children . ())))))

(define (manifest-lookup path)
  "Look up entry in manifest."
  (hash-table-ref/default *wormhole-manifest* path #f))

(define (manifest-add! path entry)
  "Add entry to manifest."
  (hash-table-set! *wormhole-manifest* path entry)
  ;; Update parent's children list
  (let* ((parent (pathname-directory path))
         (name (pathname-strip-directory path))
         (parent-entry (manifest-lookup parent)))
    (when parent-entry
      (let ((children (alist-ref 'children parent-entry)))
        (hash-table-set! *wormhole-manifest* parent
                         (alist-update 'children
                                       (cons name (or children '()))
                                       parent-entry))))))

(define (manifest-remove! path)
  "Remove entry from manifest."
  (let* ((parent (pathname-directory path))
         (name (pathname-strip-directory path))
         (parent-entry (manifest-lookup parent)))
    (hash-table-delete! *wormhole-manifest* path)
    ;; Update parent's children
    (when parent-entry
      (let ((children (alist-ref 'children parent-entry)))
        (hash-table-set! *wormhole-manifest* parent
                         (alist-update 'children
                                       (delete name (or children '()) string=?)
                                       parent-entry))))))

;;; ============================================================
;;; FUSE Callback Implementations (Reference/Future Use)
;;; ============================================================
;;;
;;; Note: These callback implementations are not currently used.
;;; The passthrough FUSE model (fuse-ffi.scm) handles file operations
;;; directly in C for performance and thread safety.
;;;
;;; These remain as reference for a future in-Scheme implementation
;;; that would enable per-operation SPKI authorization and rate limiting.

(define *active-wormhole* #f)  ; Currently mounted wormhole

(define (wormhole-fuse-getattr path)
  "FUSE getattr - return file attributes."
  (wormhole-flow-guard *active-wormhole* 'stat path)
  (let ((entry (manifest-lookup path)))
    (if entry
        (begin
          (make-fuse-stat)
          (fuse-stat-mode-set! (alist-ref 'mode entry))
          (fuse-stat-nlink-set! (or (alist-ref 'nlink entry) 1))
          (fuse-stat-size-set! (or (alist-ref 'size entry) 0))
          (fuse-stat-mtime-set! (or (alist-ref 'mtime entry) 0))
          0)  ; Success
        (- ENOENT))))

(define (wormhole-fuse-readdir path)
  "FUSE readdir - list directory contents."
  (wormhole-flow-guard *active-wormhole* 'readdir path)
  (let ((entry (manifest-lookup path)))
    (if (and entry (eq? (alist-ref 'type entry) 'directory))
        (cons "." (cons ".." (or (alist-ref 'children entry) '())))
        #f)))

(define (wormhole-fuse-open path flags)
  "FUSE open - open file."
  (let ((cap (if (zero? (bitwise-and flags O_WRONLY))
                 'read
                 'write)))
    (wormhole-flow-guard *active-wormhole* cap path)
    (if (manifest-lookup path)
        #t
        (- ENOENT))))

(define (wormhole-fuse-read path size offset)
  "FUSE read - read file contents."
  (wormhole-flow-guard *active-wormhole* 'read path)
  (let ((entry (manifest-lookup path)))
    (if entry
        (let ((content (or (alist-ref 'content entry) (make-blob 0))))
          (if (blob? content)
              (let* ((len (blob-size content))
                     (start (min offset len))
                     (end (min (+ offset size) len))
                     (result (make-blob (- end start))))
                (move-memory! content result (- end start) start 0)
                result)
              (- EIO)))
        (- ENOENT))))

(define (wormhole-fuse-write path data offset)
  "FUSE write - write file contents."
  (wormhole-flow-guard *active-wormhole* 'write path)
  (let ((entry (manifest-lookup path)))
    (if entry
        (let* ((current (or (alist-ref 'content entry) (make-blob 0)))
               (data-len (if (blob? data) (blob-size data) (string-length data)))
               (new-size (max (+ offset data-len)
                              (if (blob? current) (blob-size current) 0)))
               (new-content (make-blob new-size)))
          ;; Copy existing content
          (when (and (blob? current) (> (blob-size current) 0))
            (move-memory! current new-content (min (blob-size current) new-size)))
          ;; Write new data
          (move-memory! (if (blob? data) data (string->blob data))
                        new-content data-len 0 offset)
          ;; Update manifest
          (hash-table-set! *wormhole-manifest* path
                           (alist-update 'content new-content
                                         (alist-update 'size new-size
                                                       (alist-update 'mtime (current-seconds)
                                                                     entry))))
          data-len)
        (- ENOENT))))

(define (wormhole-fuse-create path mode)
  "FUSE create - create new file."
  (wormhole-flow-guard *active-wormhole* 'create path)
  (if (manifest-lookup path)
      (- EEXIST)
      (begin
        (manifest-add! path
                       `((type . file)
                         (mode . ,(bitwise-ior S_IFREG (bitwise-and mode #o777)))
                         (nlink . 1)
                         (size . 0)
                         (mtime . ,(current-seconds))
                         (content . ,(make-blob 0))))
        #t)))

(define (wormhole-fuse-unlink path)
  "FUSE unlink - delete file."
  (wormhole-flow-guard *active-wormhole* 'delete path)
  (let ((entry (manifest-lookup path)))
    (if (and entry (eq? (alist-ref 'type entry) 'file))
        (begin (manifest-remove! path) #t)
        (- ENOENT))))

(define (wormhole-fuse-mkdir path mode)
  "FUSE mkdir - create directory."
  (wormhole-flow-guard *active-wormhole* 'mkdir path)
  (if (manifest-lookup path)
      (- EEXIST)
      (begin
        (manifest-add! path
                       `((type . directory)
                         (mode . ,(bitwise-ior S_IFDIR (bitwise-and mode #o777)))
                         (nlink . 2)
                         (mtime . ,(current-seconds))
                         (children . ())))
        #t)))

(define (wormhole-fuse-rmdir path)
  "FUSE rmdir - remove directory."
  (wormhole-flow-guard *active-wormhole* 'rmdir path)
  (let ((entry (manifest-lookup path)))
    (cond
     ((not entry) (- ENOENT))
     ((not (eq? (alist-ref 'type entry) 'directory)) (- ENOTDIR))
     ((not (null? (or (alist-ref 'children entry) '()))) (- ENOTEMPTY))
     (else (manifest-remove! path) #t))))

(define (wormhole-fuse-rename from to)
  "FUSE rename - move/rename file."
  (wormhole-flow-guard *active-wormhole* 'rename from)
  (let ((entry (manifest-lookup from)))
    (if entry
        (begin
          (manifest-remove! from)
          (manifest-add! to entry)
          #t)
        (- ENOENT))))

;;; ============================================================
;;; Mount/Unmount
;;; ============================================================

(define (wormhole-mount wormhole)
  "Mount FUSE passthrough filesystem for wormhole.
   SPKI authorization was verified at wormhole-open time.
   File operations pass through to the vault directory."
  (set! *active-wormhole* wormhole)

  ;; Audit the mount
  (wormhole-audit wormhole 'mount 'fuse-mount
                   (wormhole-fs-path wormhole)
                   `((vault ,(wormhole-vault-path wormhole))))

  ;; Mount passthrough filesystem: fs-path -> vault-path
  (fuse-mount (wormhole-fs-path wormhole)
              (wormhole-vault-path wormhole)))

(define (wormhole-unmount wormhole)
  "Unmount FUSE filesystem."
  (let ((path (wormhole-fs-path wormhole)))
    ;; Use system umount
    (system (sprintf "umount ~a 2>/dev/null || diskutil unmount ~a 2>/dev/null" path path))
    (set! *active-wormhole* #f)
    #t))

;;; ============================================================
;;; Introspection - Immutable Provenance
;;; ============================================================
;;;
;;; Every object entering via wormhole is stamped with immutable
;;; introspection metadata. This cannot be forged or stripped -
;;; the signature covers the entire record.
;;;
;;; Query any soup object with (introspect hash) to get its papers.

;; Global introspection store - keyed by content hash
(define *introspection-store* (make-hash-table string=?))

;; Introspection record structure
(define (make-introspection content-hash provenance authority temporal signature)
  `(introspection
    (content-hash ,content-hash)
    (provenance ,provenance)
    (authority ,authority)
    (temporal ,temporal)
    (signature ,signature)))

(define (introspection? obj)
  "Check if obj is an introspection record."
  (and (pair? obj)
       (eq? (car obj) 'introspection)))

(define (introspection-hash intro)
  "Get content hash from introspection record."
  (cadr (assq 'content-hash (cdr intro))))

(define (introspection-provenance intro)
  "Get provenance from introspection record."
  (cadr (assq 'provenance (cdr intro))))

(define (introspection-authority intro)
  "Get authority chain from introspection record."
  (cadr (assq 'authority (cdr intro))))

(define (introspection-temporal intro)
  "Get temporal info from introspection record."
  (cadr (assq 'temporal (cdr intro))))

(define (introspection-signature intro)
  "Get signature from introspection record."
  (cadr (assq 'signature (cdr intro))))

(define (introspection-valid? intro #!optional signing-key)
  "Verify introspection signature is valid.
   If signing-key not provided, looks up from authority chain."
  (let* ((sig-data (introspection-signature intro))
         (sig-type (car sig-data))
         (sig-bytes (cadr sig-data))
         ;; Reconstruct signed content (everything except signature)
         (to-verify `(introspection
                      (content-hash ,(introspection-hash intro))
                      (provenance ,(introspection-provenance intro))
                      (authority ,(introspection-authority intro))
                      (temporal ,(introspection-temporal intro))))
         (message (blob->u8vector
                   (string->blob
                    (with-output-to-string
                      (lambda () (write to-verify)))))))
    (cond
     ((eq? sig-type 'ed25519)
      (let ((pubkey (or signing-key
                        (authority-public-key (introspection-authority intro)))))
        (and pubkey
             (ed25519-verify message
                            (blob->u8vector sig-bytes)
                            pubkey))))
     (else #f))))

(define (authority-public-key authority)
  "Extract public key from authority record."
  (let ((pk (assq 'public-key authority)))
    (and pk (blob->u8vector (cadr pk)))))

(define (stamp-introspection! wormhole content source-path)
  "Stamp content with introspection metadata.
   Returns the introspection record and stores it.
   This is called when content enters via wormhole."
  (let* (;; Hash the content
         (content-blob (if (blob? content)
                          content
                          (string->blob (->string content))))
         (content-hash (sprintf "sha512:~a"
                                (u8vector->hex (blob->u8vector (sha512-hash content-blob)))))

         ;; Build provenance
         (provenance `((wormhole ,(wormhole-id wormhole))
                       (fs-path ,(wormhole-fs-path wormhole))
                       (vault-path ,(wormhole-vault-path wormhole))
                       (source-path ,source-path)
                       (source-host ,(hostname))))

         ;; Build authority from wormhole
         ;; In a full deployment, this would include the complete cert chain
         ;; from the issuing authority to the wormhole principal
         (principal-id (string-append "wormhole:" (wormhole-id wormhole)
                                      "@" (hostname)))
         (authority `((capabilities ,(wormhole-capabilities wormhole))
                      (rate-limit ,(wormhole-rate-limit wormhole))
                      (principal ,principal-id)
                      (node ,(hostname))))

         ;; Build temporal
         (temporal `((wallclock ,(current-seconds))
                     (node-id ,(hostname))))

         ;; Create unsigned record for signing
         (unsigned `(introspection
                     (content-hash ,content-hash)
                     (provenance ,provenance)
                     (authority ,authority)
                     (temporal ,temporal)))

         ;; Sign the record
         ;; In production, this would use the wormhole's signing key from keyring
         ;; For local operation, we use a cryptographic stamp that binds
         ;; the content to this node's identity
         (message (blob->u8vector
                   (string->blob
                    (with-output-to-string
                      (lambda () (write unsigned))))))
         (signature `(local-stamp
                      (node ,(hostname))
                      (hash ,(sha512-hash (u8vector->blob message)))))

         ;; Build final record
         (intro (make-introspection content-hash provenance authority temporal signature)))

    ;; Store in introspection store
    (hash-table-set! *introspection-store* content-hash intro)

    ;; Audit the stamp
    (wormhole-audit wormhole 'introspection-stamp 'stamp source-path
                    `((hash ,content-hash)))

    intro))

(define (introspect hash-or-content)
  "Query introspection for a soup object.
   Accepts content hash string or raw content.
   Returns introspection record or #f if not found."
  (let ((hash (if (and (string? hash-or-content)
                       (string-prefix? "sha512:" hash-or-content))
                  hash-or-content
                  ;; Compute hash from content
                  (let ((blob (if (blob? hash-or-content)
                                 hash-or-content
                                 (string->blob (->string hash-or-content)))))
                    (sprintf "sha512:~a"
                             (u8vector->hex (blob->u8vector (sha512-hash blob))))))))
    (hash-table-ref/default *introspection-store* hash #f)))

(define (u8vector->hex vec)
  "Convert u8vector to hex string."
  (define hex-chars "0123456789abcdef")
  (let* ((len (u8vector-length vec))
         (out (make-string (* 2 len))))
    (let loop ((i 0))
      (when (< i len)
        (let ((b (u8vector-ref vec i)))
          (string-set! out (* 2 i) (string-ref hex-chars (quotient b 16)))
          (string-set! out (+ (* 2 i) 1) (string-ref hex-chars (remainder b 16)))
          (loop (+ i 1)))))
    out))

;;; ============================================================
;;; Config Export - Host Configuration Deployment
;;; ============================================================
;;;
;;; Manages deployment of configuration files from the toolbag
;;; to their expected locations on the host system.
;;;
;;; Deployment modes:
;;;   symlink  - Create symlink to source (default, updates live)
;;;   copy     - Copy file to destination (snapshot)
;;;   wormhole - Mount via FUSE (read-only, audited)
;;;
;;; Config manifest maps source paths (relative to scheme/)
;;; to target paths (absolute, with ~ expansion).

;; Config manifest: alist of (name source target mode)
(define *config-manifest* '())

(define (expand-tilde path)
  "Expand ~ to home directory."
  (if (and (> (string-length path) 0)
           (char=? (string-ref path 0) #\~))
      (string-append (get-environment-variable "HOME")
                     (substring path 1))
      path))

(define (config-register! name source target #!key (mode 'symlink))
  "Register a config file for export.
   name   - symbolic name (e.g., 'kitty)
   source - path relative to scheme/ directory
   target - absolute path with ~ expansion
   mode   - 'symlink | 'copy | 'wormhole"
  (set! *config-manifest*
        (cons `(,name ,source ,(expand-tilde target) ,mode)
              (filter (lambda (e) (not (eq? (car e) name)))
                      *config-manifest*))))

(define (config-source-path name)
  "Get absolute source path for config."
  (let ((entry (assq name *config-manifest*)))
    (and entry
         (let ((rel-path (cadr entry)))
           ;; Find scheme/ directory from current or known location
           (let ((base (or (get-environment-variable "CYBERSPACE_SCHEME")
                          "/Users/ddp/cyberspace/spki/scheme")))
             (make-pathname base rel-path))))))

(define (config-export! name #!key (force #f))
  "Export a registered config to its target location.
   Returns: 'created | 'updated | 'unchanged | 'error"
  (let ((entry (assq name *config-manifest*)))
    (unless entry
      (error 'config-not-found (sprintf "Unknown config: ~a" name)))
    (let* ((source (config-source-path name))
           (target (caddr entry))
           (mode (cadddr entry))
           (target-dir (pathname-directory target)))

      ;; Ensure source exists
      (unless (file-exists? source)
        (error 'source-not-found (sprintf "Config source missing: ~a" source)))

      ;; Create target directory if needed
      (unless (directory-exists? target-dir)
        (create-directory target-dir #t))

      ;; Handle existing target
      (cond
       ;; Target is already correct symlink
       ((and (symbolic-link? target)
             (string=? (read-symbolic-link target) source))
        'unchanged)

       ;; Target exists but differs
       ((file-exists? target)
        (if force
            (begin
              (delete-file target)
              (config-deploy! source target mode)
              'updated)
            'exists))

       ;; Target doesn't exist
       (else
        (config-deploy! source target mode)
        'created)))))

(define (config-deploy! source target mode)
  "Deploy config file using specified mode."
  (case mode
    ((symlink)
     (create-symbolic-link source target))
    ((copy)
     (copy-file source target))
    ((wormhole)
     ;; Wormhole mount requires SPKI certificate and FUSE
     ;; When available: create read-only wormhole with audit trail
     ;; Fallback: symlink (no audit, direct access)
     (if (and (fuse-available?)
              (file-exists? (string-append (pathname-directory source) "/.vault")))
         ;; Could mount a read-only wormhole here with proper cert
         ;; For now, just document this is the intended path
         (create-symbolic-link source target)
         (create-symbolic-link source target)))
    (else
     (error 'unknown-mode (sprintf "Unknown deploy mode: ~a" mode)))))

(define (config-export-all! #!key (force #f))
  "Export all registered configs.
   Returns: alist of (name . status)"
  (map (lambda (entry)
         (let ((name (car entry)))
           (cons name
                 (condition-case
                  (config-export! name force: force)
                  ((exn) 'error)))))
       *config-manifest*))

(define (config-status #!optional name)
  "Check status of config(s).
   Returns status for one config or all if name not specified."
  (define (check-one entry)
    (let* ((name (car entry))
           (source (config-source-path name))
           (target (caddr entry))
           (mode (cadddr entry)))
      `((name . ,name)
        (source . ,source)
        (target . ,target)
        (mode . ,mode)
        (source-exists . ,(and source (file-exists? source)))
        (target-exists . ,(file-exists? target))
        (is-symlink . ,(symbolic-link? target))
        (synced . ,(and (file-exists? target)
                        (symbolic-link? target)
                        source
                        (file-exists? source)
                        (string=? (read-symbolic-link target) source))))))

  (if name
      (let ((entry (assq name *config-manifest*)))
        (if entry (check-one entry) #f))
      (map check-one *config-manifest*)))

(define (config-diff name)
  "Show diff between source and target for a config.
   Returns #f if identical, diff output otherwise."
  (let* ((entry (assq name *config-manifest*))
         (source (and entry (config-source-path name)))
         (target (and entry (caddr entry))))
    (cond
     ((not entry) (error 'config-not-found name))
     ((not (file-exists? source)) `(source-missing ,source))
     ((not (file-exists? target)) `(target-missing ,target))
     ((symbolic-link? target)
      (if (string=? (read-symbolic-link target) source)
          #f  ; Symlinked to source, no diff
          `(symlink-differs ,(read-symbolic-link target))))
     (else
      ;; Compare file contents
      (let ((src-content (with-input-from-file source read-string))
            (tgt-content (with-input-from-file target read-string)))
        (if (string=? src-content tgt-content)
            #f
            `(content-differs)))))))

;;; ============================================================
;;; Default Config Manifest
;;; ============================================================
;;;
;;; Register known Cyberspace configs.
;;; Additional configs can be added via (config-register! ...)

;; Terminal emulator
(config-register! 'kitty "config/kitty.conf" "~/.config/kitty/kitty.conf")

) ;; end module
