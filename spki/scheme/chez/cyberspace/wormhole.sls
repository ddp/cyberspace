;;; wormhole.sls - FUSE-Based Bidirectional Filesystem Portal (Chez Port)
;;; Library of Cyberspace
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
;;;
;;; Ported from wormhole.scm.
;;; Copyright (c) 2026 Yoyodyne. See LICENSE.

(library (cyberspace wormhole)
  (export
    ;; Wormhole lifecycle
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

    ;; Query interface (mirrors soup-query/soup-find)
    wormhole-query          ; (wormhole-query wh criteria...) - filter audit trail
    wormhole-find           ; (wormhole-find wh ...) - find by named criteria
    wormhole-all-audit      ; All audit entries across all wormholes
    *active-wormholes*      ; Hash table of active wormholes

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

  (import (rnrs)
          (only (chezscheme)
                printf format void system
                file-exists? directory-exists?
                current-directory delete-file
                with-output-to-string with-input-from-file
                getenv
                open-process-ports native-transcoder)
          (cyberspace chicken-compatibility chicken)
          (cyberspace chicken-compatibility hashtable)
          (cyberspace fuse-ffi)
          (cyberspace filetype)
          (cyberspace crypto-ffi)
          (cyberspace metadata-ffi)
          (cyberspace os))

  ;; ============================================================
  ;; Local Utilities
  ;; ============================================================

  (define (->string x)
    "Convert any value to string."
    (if (string? x) x
        (with-output-to-string (lambda () (display x)))))

  (define (pathname-directory path)
    "Extract directory part of path."
    (let loop ((i (- (string-length path) 1)))
      (cond ((< i 0) ".")
            ((char=? (string-ref path i) #\/) (substring path 0 i))
            (else (loop (- i 1))))))

  (define (pathname-strip-directory path)
    "Extract filename from path."
    (let loop ((i (- (string-length path) 1)))
      (cond ((< i 0) path)
            ((char=? (string-ref path i) #\/)
             (substring path (+ i 1) (string-length path)))
            (else (loop (- i 1))))))

  (define (pathname-extension path)
    "Extract file extension (without dot), or #f."
    (let ((dot-pos (let loop ((i (- (string-length path) 1)))
                     (cond ((< i 0) #f)
                           ((char=? (string-ref path i) #\.) i)
                           ((char=? (string-ref path i) #\/) #f)
                           (else (loop (- i 1)))))))
      (and dot-pos
           (< (+ dot-pos 1) (string-length path))
           (substring path (+ dot-pos 1) (string-length path)))))

  (define (make-pathname dir file)
    "Join directory and filename."
    (if (or (not dir) (string=? dir ""))
        file
        (if (char=? (string-ref dir (- (string-length dir) 1)) #\/)
            (string-append dir file)
            (string-append dir "/" file))))

  (define (shell-cmd cmd)
    "Run shell command, return trimmed output or #f."
    (guard (exn [#t #f])
      (let-values (((to-stdin from-stdout from-stderr)
                    (open-process-ports cmd 'line (native-transcoder))))
        (let ((result (get-line from-stdout)))
          (close-port to-stdin)
          (close-port from-stdout)
          (close-port from-stderr)
          (if (eof-object? result) #f result)))))

  (define (file-size-via-stat path)
    "Get file size via stat command."
    (let ((result (shell-cmd (string-append "stat -f '%z' " path " 2>/dev/null || "
                                            "stat -c '%s' " path " 2>/dev/null"))))
      (if result (or (string->number result) 0) 0)))

  (define (file-mtime-via-stat path)
    "Get file modification time via stat command."
    (let ((result (shell-cmd (string-append "stat -f '%m' " path " 2>/dev/null || "
                                            "stat -c '%Y' " path " 2>/dev/null"))))
      (if result (or (string->number result) 0) 0)))

  (define (symbolic-link? path)
    "Check if path is a symbolic link."
    (let ((result (shell-cmd (string-append "test -L " path " && echo yes || echo no"))))
      (and result (string=? result "yes"))))

  (define (read-symbolic-link path)
    "Read target of symbolic link."
    (shell-cmd (string-append "readlink " path " 2>/dev/null")))

  (define (create-symbolic-link source target)
    "Create a symbolic link."
    (system (string-append "ln -s " source " " target)))

  (define (copy-file source target)
    "Copy a file."
    (system (string-append "cp " source " " target)))

  (define (read-file-as-string path)
    "Read entire file as string."
    (guard (exn [#t ""])
      (with-input-from-file path
        (lambda ()
          (let loop ((chars '()))
            (let ((c (read-char)))
              (if (eof-object? c)
                  (list->string (reverse chars))
                  (loop (cons c chars)))))))))

  (define (bytevector->hex bv)
    "Convert bytevector to hex string."
    (define hex-chars "0123456789abcdef")
    (let* ((len (bytevector-length bv))
           (out (make-string (* 2 len))))
      (let loop ((i 0))
        (when (< i len)
          (let ((b (bytevector-u8-ref bv i)))
            (string-set! out (* 2 i) (string-ref hex-chars (quotient b 16)))
            (string-set! out (+ (* 2 i) 1) (string-ref hex-chars (remainder b 16)))
            (loop (+ i 1)))))
      out))

  (define (string->bytevector s)
    "Convert string to bytevector (Latin-1)."
    (let* ((len (string-length s))
           (bv (make-bytevector len)))
      (do ((i 0 (+ i 1)))
          ((= i len) bv)
        (bytevector-u8-set! bv i (bitwise-and (char->integer (string-ref s i)) #xff)))))

  ;; ============================================================
  ;; Capability Sets
  ;; ============================================================

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

  ;; ============================================================
  ;; Wormhole Record (tagged vector)
  ;; ============================================================
  ;;
  ;; Layout: #(*wormhole* id fs-path vault-path capabilities
  ;;           rate-limit rate-counter rate-window
  ;;           audit-log created locked auth-required)
  ;; Index:   0          1  2       3          4
  ;;          5          6            7
  ;;          8         9       10     11

  (define *wormhole-tag* '*wormhole*)

  (define (make-wormhole-internal id fs-path vault-path capabilities
                                   rate-lim rate-counter rate-window
                                   audit-log created locked auth-required)
    (vector *wormhole-tag* id fs-path vault-path capabilities
            rate-lim rate-counter rate-window
            audit-log created locked auth-required))

  (define (wormhole? x)
    (and (vector? x)
         (> (vector-length x) 0)
         (eq? (vector-ref x 0) *wormhole-tag*)))

  (define (wormhole-id wh) (vector-ref wh 1))
  (define (wormhole-fs-path wh) (vector-ref wh 2))
  (define (wormhole-vault-path wh) (vector-ref wh 3))
  (define (wormhole-capabilities wh) (vector-ref wh 4))
  (define (wormhole-rate-limit wh) (vector-ref wh 5))
  (define (wormhole-rate-counter wh) (vector-ref wh 6))
  (define (wormhole-rate-counter-set! wh v) (vector-set! wh 6 v))
  (define (wormhole-rate-window wh) (vector-ref wh 7))
  (define (wormhole-rate-window-set! wh v) (vector-set! wh 7 v))
  (define (wormhole-audit-log wh) (vector-ref wh 8))
  (define (wormhole-audit-log-set! wh v) (vector-set! wh 8 v))
  (define (wormhole-created wh) (vector-ref wh 9))
  (define (wormhole-locked wh) (vector-ref wh 10))
  (define (wormhole-locked-set! wh v) (vector-set! wh 10 v))
  (define (wormhole-auth-required wh) (vector-ref wh 11))

  ;; Active wormholes table
  (define *active-wormholes* (make-hash-table string=?))

  ;; ============================================================
  ;; Certificate Operations
  ;; ============================================================

  (define (wormhole-principal fs-path vault-path)
    "Create principal identifier for a wormhole."
    `(wormhole
      (fs-path ,fs-path)
      (vault-path ,vault-path)))

  (define (wormhole-cert issuer fs-path vault-path capabilities . rest)
    "Create SPKI certificate authorizing wormhole.
     Returns S-expression certificate structure.
     Optional keywords: rate-limit: N  expires: time"
    (let ((rate-lim (get-key rest 'rate-limit: 1000))
          (expires (get-key rest 'expires: #f)))
      `(cert
        (version 1)
        (issuer ,issuer)
        (subject ,(wormhole-principal fs-path vault-path))
        (tag (wormhole
              (fs-path ,fs-path)
              (vault-path ,vault-path)
              (capabilities ,@capabilities)
              (rate-limit ,rate-lim)
              ,@(if expires `((expires ,expires)) '()))))))

  (define (verify-wormhole-cert cert fs-path vault-path)
    "Verify wormhole certificate matches requested paths.
     Returns #t if valid, #f otherwise."
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

  ;; ============================================================
  ;; Capability Operations
  ;; ============================================================

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

  ;; ============================================================
  ;; Rate Limiting
  ;; ============================================================

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

  ;; ============================================================
  ;; Audit Trail
  ;; ============================================================

  (define (wormhole-audit wormhole event operation object . rest)
    "Log audit event for wormhole operation."
    (let ((details (if (null? rest) #f (car rest))))
      (let ((entry `(audit
                     (timestamp ,(current-seconds))
                     (wormhole ,(wormhole-id wormhole))
                     (event ,event)
                     (operation ,operation)
                     (object ,object)
                     ,@(if details `((details ,details)) '()))))
        (wormhole-audit-log-set! wormhole
                                  (cons entry (wormhole-audit-log wormhole)))
        entry)))

  (define (wormhole-audit-trail wormhole . rest)
    "Retrieve recent audit entries for wormhole.
     Optional keyword: limit: N (default 100)"
    (let ((limit (get-key rest 'limit: 100)))
      (take (wormhole-audit-log wormhole)
            (min limit (length (wormhole-audit-log wormhole))))))

  ;; ============================================================
  ;; Query Interface
  ;; ============================================================

  (define (wormhole-all-audit)
    "Collect all audit entries across all active wormholes.
     Returns list of (wormhole-id . entry) pairs."
    (apply append
           (map (lambda (path)
                  (let ((wh (hash-table-ref *active-wormholes* path)))
                    (map (lambda (entry)
                           (cons (wormhole-id wh) entry))
                         (wormhole-audit-log wh))))
                (hash-table-keys *active-wormholes*))))

  (define (audit-entry-timestamp entry)
    "Extract timestamp from audit entry."
    (let ((ts (assq 'timestamp (cdr entry))))
      (if ts (cadr ts) 0)))

  (define (audit-entry-event entry)
    "Extract event type from audit entry."
    (let ((ev (assq 'event (cdr entry))))
      (if ev (cadr ev) #f)))

  (define (audit-entry-operation entry)
    "Extract operation from audit entry."
    (let ((op (assq 'operation (cdr entry))))
      (if op (cadr op) #f)))

  (define (audit-entry-object entry)
    "Extract object from audit entry."
    (let ((obj (assq 'object (cdr entry))))
      (if obj (cadr obj) #f)))

  (define (audit-entry-wormhole entry)
    "Extract wormhole id from audit entry."
    (let ((wh (assq 'wormhole (cdr entry))))
      (if wh (cadr wh) #f)))

  (define (wormhole-match-criterion entry criterion)
    "Match single audit entry against one criterion."
    (let ((key (car criterion))
          (val (cadr criterion)))
      (case key
        ;; Event type
        ((event type)
         (eq? (audit-entry-event entry) val))

        ;; Operation
        ((operation op)
         (eq? (audit-entry-operation entry) val))

        ;; Object path (with glob support)
        ((object path)
         (let ((obj (audit-entry-object entry)))
           (cond
            ((not obj) #f)
            ((string? val)
             (if (string-suffix? "*" val)
                 (string-prefix? (string-drop-right val 1) (->string obj))
                 (equal? (->string obj) val)))
            (else (equal? obj val)))))

        ;; Time - since
        ((since after)
         (let* ((ts (audit-entry-timestamp entry))
                (now (current-seconds))
                (threshold (wormhole-parse-time-spec val now)))
           (>= ts threshold)))

        ;; Time - before
        ((before until)
         (let* ((ts (audit-entry-timestamp entry))
                (now (current-seconds))
                (threshold (wormhole-parse-time-spec val now)))
           (<= ts threshold)))

        ;; Wormhole id
        ((wormhole wh)
         (let ((wh-id (audit-entry-wormhole entry)))
           (and wh-id (string-prefix? val (->string wh-id)))))

        ;; Boolean combinators
        ((and)
         (every (lambda (c) (wormhole-match-criterion entry c)) (cdr criterion)))

        ((or)
         (any (lambda (c) (wormhole-match-criterion entry c)) (cdr criterion)))

        ((not)
         (not (wormhole-match-criterion entry (cadr criterion))))

        (else #f))))

  (define (wormhole-parse-time-spec spec now)
    "Parse time spec like '1h' '24h' '7d' to epoch."
    (cond
     ((number? spec) spec)
     ((and (string? spec) (> (string-length spec) 1))
      (let ((n (string->number (substring spec 0 (- (string-length spec) 1))))
            (unit (string-ref spec (- (string-length spec) 1))))
        (if n
            (- now (* n (case unit
                          ((#\h) 3600)
                          ((#\d) 86400)
                          ((#\m) 60)
                          ((#\w) 604800)
                          (else 3600))))
            now)))
     (else now)))

  (define (wormhole-query wormhole . criteria)
    "Filter wormhole audit trail by criteria."
    (let ((entries (wormhole-audit-log wormhole)))
      (if (null? criteria)
          entries
          (filter
           (lambda (entry)
             (every (lambda (c) (wormhole-match-criterion entry c)) criteria))
           entries))))

  (define (wormhole-find wormhole . rest)
    "Find audit entries by named criteria.
     Keywords: event: operation: object: since: before:"
    (let ((event (get-key rest 'event: #f))
          (operation (get-key rest 'operation: #f))
          (object (get-key rest 'object: #f))
          (since (get-key rest 'since: #f))
          (before (get-key rest 'before: #f)))
      (let ((criteria '()))
        (when event
          (set! criteria (cons `(event ,event) criteria)))
        (when operation
          (set! criteria (cons `(operation ,operation) criteria)))
        (when object
          (set! criteria (cons `(object ,object) criteria)))
        (when since
          (set! criteria (cons `(since ,since) criteria)))
        (when before
          (set! criteria (cons `(before ,before) criteria)))
        (apply wormhole-query wormhole criteria))))

  ;; ============================================================
  ;; Flow Guard (Reference Monitor)
  ;; ============================================================

  (define (wormhole-flow-guard wormhole operation object)
    "Reference monitor for wormhole operations.
     Validates capability, enforces rate limits, records audit trail."
    (let ((caps (wormhole-capabilities wormhole)))
      ;; Check capability
      (unless (memq operation caps)
        (wormhole-audit wormhole 'denied operation object)
        (error 'capability-denied
               (string-append "Operation "
                              (->string operation) " not permitted")))
      ;; Check rate limit
      (unless (wormhole-rate-ok? wormhole)
        (wormhole-audit wormhole 'rate-limited operation object)
        (error 'rate-limited
               (string-append "Rate limit exceeded ("
                              (->string (wormhole-rate-limit wormhole))
                              " ops/min)")))
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

  ;; ============================================================
  ;; Metadata Capture/Restore
  ;; ============================================================

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
             (size ,(file-size-via-stat path))
             (mtime ,(file-mtime-via-stat path)))
            (xattr ,xattr-data)
            (flags ,flags)
            (acl ,acl-entries)))
        `((posix (exists #f)))))

  (define (restore-metadata path metadata)
    "Restore metadata to a file."
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

  ;; ============================================================
  ;; Object Ingestion with Immutable Provenance
  ;; ============================================================

  (define (make-object-provenance path content principal certificate)
    "Create immutable provenance record for an object entering via wormhole."
    (let* ((content-bv (if (string? content)
                           (string->bytevector content)
                           content))
           (content-hash (sha512-hash content-bv))
           (detected-type (file-type path))
           (detected-mime (file-mime path)))
      `(provenance
        (origin-path ,path)
        (ingestion-time ,(current-seconds))
        (file-type ,detected-type)
        (mime-type ,detected-mime)
        (size ,(bytevector-length content-bv))
        (content-hash ,(bytevector->hex content-hash))
        (principal ,principal)
        (certificate-hash ,(if certificate
                               (bytevector->hex
                                (sha512-hash
                                 (string->bytevector
                                  (format "~s" certificate))))
                               #f))
        (immutable #t))))

  (define (wormhole-ingest path content wormhole)
    "Ingest an object through a wormhole into the soup."
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

  ;; ============================================================
  ;; Wormhole Lifecycle
  ;; ============================================================

  (define wormhole-id-counter 0)

  (define (generate-wormhole-id)
    (set! wormhole-id-counter (+ 1 wormhole-id-counter))
    (string-append "wormhole-" (->string (current-seconds))
                   "-" (->string wormhole-id-counter)))

  (define (wormhole-open fs-path . rest)
    "Open wormhole - requires valid certificate.
     Returns wormhole handle on success.
     Keywords: vault-path: capabilities: rate-limit: locked: auth-required: certificate:"
    (let ((vault-path (get-key rest 'vault-path: "/"))
          (capabilities (get-key rest 'capabilities: capability:read-write))
          (rate-lim (get-key rest 'rate-limit: 1000))
          (locked (get-key rest 'locked: #f))
          (auth-required (get-key rest 'auth-required: '()))
          (certificate (get-key rest 'certificate: #f)))
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
                  rate-lim 0 (current-seconds)
                  '() (current-seconds)
                  locked auth-required)))

        ;; Audit the open
        (wormhole-audit wh 'wormhole-open 'open fs-path
                        `((vault ,vault-path)
                          (capabilities ,(length capabilities))))

        ;; Register in active table
        (hash-table-set! *active-wormholes* fs-path wh)

        ;; Return wormhole handle
        wh)))

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

  ;; ============================================================
  ;; FUSE Operations - Vault Integration
  ;; ============================================================

  ;; In-memory manifest for demo (full implementation uses vault manifests)
  (define *wormhole-manifest* (make-hash-table string=?))

  (define (manifest-init! wormhole)
    "Initialize manifest for wormhole with root directory."
    (hash-table-set! *wormhole-manifest* "/"
                     `((type . directory)
                       (mode . ,(bitwise-ior S_IFDIR #o755))
                       (nlink . 2)
                       (mtime . ,(current-seconds))
                       (children . ()))))

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
                                         (filter (lambda (c) (not (string=? c name)))
                                                 (or children '()))
                                         parent-entry))))))

  ;; ============================================================
  ;; FUSE Callback Implementations (Reference/Future Use)
  ;; ============================================================

  (define *active-wormhole* #f)

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
            0)
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
                           (content . ,(make-bytevector 0))))
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

  ;; ============================================================
  ;; Mount/Unmount
  ;; ============================================================

  (define (wormhole-mount wormhole)
    "Mount FUSE passthrough filesystem for wormhole."
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
      (system (string-append "umount " path " 2>/dev/null || "
                             "diskutil unmount " path " 2>/dev/null"))
      (set! *active-wormhole* #f)
      #t))

  ;; ============================================================
  ;; Introspection - Immutable Provenance
  ;; ============================================================

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

  (define (introspection-valid? intro . rest)
    "Verify introspection signature is valid."
    (let* ((signing-key (if (null? rest) #f (car rest)))
           (sig-data (introspection-signature intro))
           (sig-type (car sig-data)))
      (cond
       ((eq? sig-type 'ed25519)
        (let* ((sig-bytes (cadr sig-data))
               ;; Reconstruct signed content (everything except signature)
               (to-verify `(introspection
                            (content-hash ,(introspection-hash intro))
                            (provenance ,(introspection-provenance intro))
                            (authority ,(introspection-authority intro))
                            (temporal ,(introspection-temporal intro))))
               (message (string->bytevector
                         (with-output-to-string
                           (lambda () (write to-verify))))))
          (let ((pubkey (or signing-key
                            (authority-public-key (introspection-authority intro)))))
            (and pubkey
                 (ed25519-verify message sig-bytes pubkey)))))
       (else #f))))

  (define (authority-public-key authority)
    "Extract public key from authority record."
    (let ((pk (assq 'public-key authority)))
      (and pk (cadr pk))))

  (define (stamp-introspection! wormhole content source-path)
    "Stamp content with introspection metadata."
    (let* (;; Hash the content
           (content-bv (if (bytevector? content)
                           content
                           (string->bytevector (->string content))))
           (content-hash (string-append "sha512:"
                                        (bytevector->hex (sha512-hash content-bv))))

           ;; Build provenance
           (provenance `((wormhole ,(wormhole-id wormhole))
                         (fs-path ,(wormhole-fs-path wormhole))
                         (vault-path ,(wormhole-vault-path wormhole))
                         (source-path ,source-path)
                         (source-host ,(hostname))))

           ;; Build authority from wormhole
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
           (message (string->bytevector
                     (with-output-to-string
                       (lambda () (write unsigned)))))
           (signature `(local-stamp
                        (node ,(hostname))
                        (hash ,(sha512-hash message))))

           ;; Build final record
           (intro (make-introspection content-hash provenance authority temporal signature)))

      ;; Store in introspection store
      (hash-table-set! *introspection-store* content-hash intro)

      ;; Audit the stamp
      (wormhole-audit wormhole 'introspection-stamp 'stamp source-path
                      `((hash ,content-hash)))

      intro))

  (define (introspect hash-or-content)
    "Query introspection for a soup object."
    (let ((hash (if (and (string? hash-or-content)
                         (string-prefix? "sha512:" hash-or-content))
                    hash-or-content
                    ;; Compute hash from content
                    (let ((bv (if (bytevector? hash-or-content)
                                  hash-or-content
                                  (string->bytevector (->string hash-or-content)))))
                      (string-append "sha512:"
                                     (bytevector->hex (sha512-hash bv)))))))
      (hash-table-ref/default *introspection-store* hash #f)))

  ;; ============================================================
  ;; Config Export - Host Configuration Deployment
  ;; ============================================================

  ;; Config manifest: alist of (name source target mode)
  (define *config-manifest* '())

  (define (expand-tilde path)
    "Expand ~ to home directory."
    (if (and (> (string-length path) 0)
             (char=? (string-ref path 0) #\~))
        (string-append (or (getenv "HOME") "/root")
                       (substring path 1 (string-length path)))
        path))

  (define (config-register! name source target . rest)
    "Register a config file for export.
     Optional keyword: mode: 'symlink | 'copy | 'wormhole"
    (let ((mode (get-key rest 'mode: 'symlink)))
      (set! *config-manifest*
            (cons `(,name ,source ,(expand-tilde target) ,mode)
                  (filter (lambda (e) (not (eq? (car e) name)))
                          *config-manifest*)))))

  (define (config-source-path name)
    "Get absolute source path for config."
    (let ((entry (assq name *config-manifest*)))
      (and entry
           (let ((rel-path (cadr entry)))
             (let ((base (or (getenv "CYBERSPACE_SCHEME")
                            "/Users/ddp/cyberspace/spki/scheme")))
               (make-pathname base rel-path))))))

  (define (config-export! name . rest)
    "Export a registered config to its target location.
     Returns: 'created | 'updated | 'unchanged | 'error
     Optional keyword: force: #t"
    (let ((force (get-key rest 'force: #f)))
      (let ((entry (assq name *config-manifest*)))
        (unless entry
          (error 'config-not-found (string-append "Unknown config: " (->string name))))
        (let* ((source (config-source-path name))
               (target (caddr entry))
               (mode (cadddr entry))
               (target-dir (pathname-directory target)))

          ;; Ensure source exists
          (unless (file-exists? source)
            (error 'source-not-found (string-append "Config source missing: " source)))

          ;; Create target directory if needed
          (unless (directory-exists? target-dir)
            (system (string-append "mkdir -p " target-dir)))

          ;; Handle existing target
          (cond
           ;; Target is already correct symlink
           ((and (symbolic-link? target)
                 (let ((link-target (read-symbolic-link target)))
                   (and link-target (string=? link-target source))))
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
            'created))))))

  (define (config-deploy! source target mode)
    "Deploy config file using specified mode."
    (case mode
      ((symlink)
       (create-symbolic-link source target))
      ((copy)
       (copy-file source target))
      ((wormhole)
       ;; Wormhole mount requires SPKI certificate and FUSE
       ;; Fallback: symlink
       (create-symbolic-link source target))
      (else
       (error 'unknown-mode (string-append "Unknown deploy mode: " (->string mode))))))

  (define (config-export-all! . rest)
    "Export all registered configs.
     Returns: alist of (name . status)
     Optional keyword: force: #t"
    (let ((force (get-key rest 'force: #f)))
      (map (lambda (entry)
             (let ((name (car entry)))
               (cons name
                     (guard (exn [#t 'error])
                       (config-export! name 'force: force)))))
           *config-manifest*)))

  (define (config-status . rest)
    "Check status of config(s).
     Optional arg: name (check one config)"
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
                          (let ((link-target (read-symbolic-link target)))
                            (and link-target (string=? link-target source))))))))

    (let ((name (if (null? rest) #f (car rest))))
      (if name
          (let ((entry (assq name *config-manifest*)))
            (if entry (check-one entry) #f))
          (map check-one *config-manifest*))))

  (define (config-diff name)
    "Show diff between source and target for a config."
    (let* ((entry (assq name *config-manifest*))
           (source (and entry (config-source-path name)))
           (target (and entry (caddr entry))))
      (cond
       ((not entry) (error 'config-not-found name))
       ((not (file-exists? source)) `(source-missing ,source))
       ((not (file-exists? target)) `(target-missing ,target))
       ((symbolic-link? target)
        (let ((link-target (read-symbolic-link target)))
          (if (and link-target (string=? link-target source))
              #f
              `(symlink-differs ,link-target))))
       (else
        ;; Compare file contents
        (let ((src-content (read-file-as-string source))
              (tgt-content (read-file-as-string target)))
          (if (string=? src-content tgt-content)
              #f
              `(content-differs)))))))

  ;; ============================================================
  ;; Default Config Manifest
  ;; ============================================================

  ;; Terminal emulator
  (config-register! 'kitty "config/kitty.conf" "~/.config/kitty/kitty.conf")

) ;; end library
