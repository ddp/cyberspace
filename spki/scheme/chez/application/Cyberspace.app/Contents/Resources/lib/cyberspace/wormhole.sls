;;; wormhole.sls - FUSE-Based Bidirectional Filesystem Portal (Memo-042)
;;; Library of Cyberspace - Chez Scheme Port
;;;
;;; Wormholes bridge the macOS filesystem and the Library of Cyberspace vault.
;;; All operations are:
;;; - SPKI authorized (requires valid certificate)
;;; - Audited (Memo-003)
;;; - Rate-limited (Memo-032)
;;; - Capability-attenuated
;;;
;;; Ported from Chicken's wormhole.scm.
;;; Changes: module -> library, #!key/#!optional -> get-key/get-opt,
;;;          SRFI-9 record -> R6RS record, srfi-1/13/69 inlined/compat,
;;;          blob -> bytevector, sprintf -> format, condition-case -> guard.

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

    ;; Query interface
    wormhole-query
    wormhole-find
    wormhole-all-audit
    active-wormholes

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
    introspection-store

    ;; Config export (host configuration deployment)
    config-manifest
    config-register!
    config-export!
    config-export-all!
    config-status
    config-diff)

  (import (except (rnrs) filter)
          (rnrs mutable-strings)
          (only (chezscheme)
                printf format system
                with-output-to-string
                mkdir getenv
                current-time time-second)
          (cyberspace fuse-ffi)
          (cyberspace filetype)
          (cyberspace crypto-ffi)
          (cyberspace metadata-ffi)
          (cyberspace os)
          (cyberspace chicken-compatibility hash-table)
          (cyberspace chicken-compatibility chicken)
          (cyberspace chicken-compatibility file))

  ;; ============================================================
  ;; Inlined Helpers
  ;; ============================================================

  ;; current-seconds provided by (cyberspace chicken-compatibility file)

  (define (every pred lst)
    (or (null? lst)
        (and (pred (car lst))
             (every pred (cdr lst)))))

  (define (any pred lst)
    (and (not (null? lst))
         (or (pred (car lst))
             (any pred (cdr lst)))))

  (define (filter pred lst)
    (let loop ((l lst) (acc '()))
      (if (null? l) (reverse acc)
          (loop (cdr l)
                (if (pred (car l)) (cons (car l) acc) acc)))))

  (define (take lst n)
    (if (or (null? lst) (<= n 0)) '()
        (cons (car lst) (take (cdr lst) (- n 1)))))

  (define (string-prefix? prefix s)
    (and (<= (string-length prefix) (string-length s))
         (string=? prefix (substring s 0 (string-length prefix)))))

  (define (string-suffix? suffix s)
    (let ((slen (string-length s))
          (xlen (string-length suffix)))
      (and (<= xlen slen)
           (string=? suffix (substring s (- slen xlen) slen)))))

  (define (string-drop-right s n)
    (substring s 0 (max 0 (- (string-length s) n))))

  (define (string-join lst sep)
    (if (null? lst) ""
        (let loop ((rest (cdr lst)) (acc (car lst)))
          (if (null? rest) acc
              (loop (cdr rest) (string-append acc sep (car rest)))))))

  (define (make-pathname dir file)
    (if (or (not dir) (string=? dir ""))
        file
        (string-append dir "/" file)))

  (define (pathname-directory path)
    (let loop ((i (- (string-length path) 1)))
      (cond ((< i 0) "")
            ((char=? (string-ref path i) #\/) (substring path 0 i))
            (else (loop (- i 1))))))

  (define (pathname-strip-directory path)
    (let loop ((i (- (string-length path) 1)))
      (cond ((< i 0) path)
            ((char=? (string-ref path i) #\/) (substring path (+ i 1) (string-length path)))
            (else (loop (- i 1))))))

  ;; directory-exists? provided by (cyberspace chicken-compatibility file)

  (define (bytevector->hex bv)
    (let* ((len (bytevector-length bv))
           (out (make-string (* 2 len))))
      (do ((i 0 (+ i 1))) ((= i len) out)
        (let ((b (bytevector-u8-ref bv i)))
          (string-set! out (* 2 i)
                       (string-ref "0123456789abcdef" (div b 16)))
          (string-set! out (+ (* 2 i) 1)
                       (string-ref "0123456789abcdef" (mod b 16)))))))

  (define (->string x)
    (cond ((string? x) x)
          ((symbol? x) (symbol->string x))
          ((number? x) (number->string x))
          (else (format "~a" x))))

  ;; ============================================================
  ;; Capability Sets
  ;; ============================================================

  (define cap:read 'read)
  (define cap:write 'write)
  (define cap:create 'create)
  (define cap:delete 'delete)
  (define cap:rename 'rename)

  (define cap:stat 'stat)
  (define cap:chmod 'chmod)
  (define cap:chown 'chown)
  (define cap:xattr-read 'xattr-read)
  (define cap:xattr-write 'xattr-write)
  (define cap:acl-read 'acl-read)
  (define cap:acl-write 'acl-write)

  (define cap:readdir 'readdir)
  (define cap:mkdir 'mkdir)
  (define cap:rmdir 'rmdir)

  (define cap:admin 'admin)
  (define cap:delegate 'delegate)
  (define cap:audit-read 'audit-read)
  (define cap:rate-limit 'rate-limit)

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
  ;; Wormhole Record
  ;; ============================================================

  (define-record-type wormhole-rec
    (fields
      (immutable id wormhole-id)
      (immutable fs-path wormhole-fs-path)
      (immutable vault-path wormhole-vault-path)
      (immutable capabilities wormhole-capabilities)
      (immutable rate-limit wormhole-rate-limit)
      (mutable rate-counter wormhole-rate-counter wormhole-rate-counter-set!)
      (mutable rate-window wormhole-rate-window wormhole-rate-window-set!)
      (mutable audit-log wormhole-audit-log wormhole-audit-log-set!)
      (immutable created wormhole-created)
      (mutable locked wormhole-locked wormhole-locked-set!)
      (immutable auth-required wormhole-auth-required)))

  (define (make-wormhole-internal id fs-path vault-path capabilities
                                   rate-lim rate-counter rate-window
                                   audit-log created locked auth-required)
    (make-wormhole-rec id fs-path vault-path capabilities
                       rate-lim rate-counter rate-window
                       audit-log created locked auth-required))

  (define (wormhole? obj) (wormhole-rec? obj))

  ;; Active wormholes table (accessor replaces exported *active-wormholes*)
  (define *active-wormholes* (make-hash-table string=?))
  (define (active-wormholes) *active-wormholes*)

  ;; ============================================================
  ;; Certificate Operations
  ;; ============================================================

  (define (wormhole-principal fs-path vault-path)
    `(wormhole
      (fs-path ,fs-path)
      (vault-path ,vault-path)))

  (define (wormhole-cert issuer fs-path vault-path capabilities . opts)
    (let ((rate-lim (get-key opts 'rate-limit: 1000))
          (expires (get-key opts 'expires: #f)))
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
    (every (lambda (cap) (memq cap possessed)) requested))

  (define (wormhole-can? wormhole capability)
    (memq capability (wormhole-capabilities wormhole)))

  (define (wormhole-delegate wormhole new-caps recipient)
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
    (let* ((now (current-seconds))
           (window (wormhole-rate-window wormhole))
           (limit (wormhole-rate-limit wormhole)))
      (when (> (- now window) 60)
        (wormhole-rate-counter-set! wormhole 0)
        (wormhole-rate-window-set! wormhole now))
      (< (wormhole-rate-counter wormhole) limit)))

  (define (wormhole-rate-increment! wormhole)
    (wormhole-rate-counter-set! wormhole
                                 (+ 1 (wormhole-rate-counter wormhole))))

  ;; ============================================================
  ;; Audit Trail
  ;; ============================================================

  (define (wormhole-audit wormhole event operation object . rest)
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

  (define (wormhole-audit-trail wormhole . opts)
    (let ((limit (get-key opts 'limit: 100)))
      (take (wormhole-audit-log wormhole)
            (min limit (length (wormhole-audit-log wormhole))))))

  ;; ============================================================
  ;; Query Interface
  ;; ============================================================

  (define (wormhole-all-audit)
    (apply append
           (map (lambda (path)
                  (let ((wh (hash-table-ref *active-wormholes* path)))
                    (map (lambda (entry)
                           (cons (wormhole-id wh) entry))
                         (wormhole-audit-log wh))))
                (hash-table-keys *active-wormholes*))))

  (define (audit-entry-timestamp entry)
    (let ((ts (assq 'timestamp (cdr entry))))
      (if ts (cadr ts) 0)))

  (define (audit-entry-event entry)
    (let ((ev (assq 'event (cdr entry))))
      (if ev (cadr ev) #f)))

  (define (audit-entry-operation entry)
    (let ((op (assq 'operation (cdr entry))))
      (if op (cadr op) #f)))

  (define (audit-entry-object entry)
    (let ((obj (assq 'object (cdr entry))))
      (if obj (cadr obj) #f)))

  (define (audit-entry-wormhole entry)
    (let ((wh (assq 'wormhole (cdr entry))))
      (if wh (cadr wh) #f)))

  (define (wormhole-match-criterion entry criterion)
    (let ((key (car criterion))
          (val (cadr criterion)))
      (case key
        ((event type)
         (eq? (audit-entry-event entry) val))
        ((operation op)
         (eq? (audit-entry-operation entry) val))
        ((object path)
         (let ((obj (audit-entry-object entry)))
           (cond
            ((not obj) #f)
            ((string? val)
             (if (string-suffix? "*" val)
                 (string-prefix? (string-drop-right val 1) obj)
                 (string=? obj val)))
            (else (equal? obj val)))))
        ((since after)
         (let* ((ts (audit-entry-timestamp entry))
                (now (current-seconds))
                (threshold (wormhole-parse-time-spec val now)))
           (>= ts threshold)))
        ((before until)
         (let* ((ts (audit-entry-timestamp entry))
                (now (current-seconds))
                (threshold (wormhole-parse-time-spec val now)))
           (<= ts threshold)))
        ((wormhole wh)
         (let ((wh-id (audit-entry-wormhole entry)))
           (and wh-id (string-prefix? val wh-id))))
        ((and)
         (every (lambda (c) (wormhole-match-criterion entry c)) (cdr criterion)))
        ((or)
         (any (lambda (c) (wormhole-match-criterion entry c)) (cdr criterion)))
        ((not)
         (not (wormhole-match-criterion entry (cadr criterion))))
        (else #f))))

  (define (wormhole-parse-time-spec spec now)
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
    (let ((entries (wormhole-audit-log wormhole)))
      (if (null? criteria)
          entries
          (filter
           (lambda (entry)
             (every (lambda (c) (wormhole-match-criterion entry c)) criteria))
           entries))))

  (define (wormhole-find wormhole . opts)
    (let ((event (get-key opts 'event: #f))
          (operation (get-key opts 'operation: #f))
          (object (get-key opts 'object: #f))
          (since (get-key opts 'since: #f))
          (before (get-key opts 'before: #f)))
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
    (let ((caps (wormhole-capabilities wormhole)))
      (unless (memq operation caps)
        (wormhole-audit wormhole 'denied operation object)
        (error 'capability-denied
               (format "Operation ~a not permitted" operation)))
      (unless (wormhole-rate-ok? wormhole)
        (wormhole-audit wormhole 'rate-limited operation object)
        (error 'rate-limited
               (format "Rate limit exceeded (~a ops/min)"
                       (wormhole-rate-limit wormhole))))
      (when (and (wormhole-locked wormhole)
                  (memq operation (wormhole-auth-required wormhole)))
        (wormhole-audit wormhole 'locked operation object)
        (error 'wormhole-locked "Operation requires unlock"))
      (wormhole-rate-increment! wormhole)
      (wormhole-audit wormhole 'permitted operation object)
      `(permitted ,operation ,object)))

  ;; ============================================================
  ;; Metadata Capture/Restore
  ;; ============================================================

  (define (capture-metadata path)
    (if (file-exists? path)
        (let* ((xattrs (xattr-list path))
               (xattr-data (map (lambda (name)
                                  (cons name (xattr-get path name)))
                                xattrs))
               (flags (file-flags path))
               (acl-entries (acl-get path)))
          `((posix
             (exists #t)
             (size 0)
             (mtime ,(current-seconds)))
            (xattr ,xattr-data)
            (flags ,flags)
            (acl ,acl-entries)))
        `((posix (exists #f)))))

  (define (restore-metadata path metadata)
    (let ((xattr-data (alist-ref 'xattr metadata eq? '()))
          (flags (alist-ref 'flags metadata eq? 0))
          (acl-entries (alist-ref 'acl metadata eq? '())))
      (for-each (lambda (entry)
                  (when (and (pair? entry) (cdr entry))
                    (xattr-set path (car entry) (cdr entry))))
                xattr-data)
      (when (> flags 0)
        (file-flags-set! path flags))
      (when (pair? acl-entries)
        (acl-set path (string-join acl-entries "\n")))
      #t))

  ;; ============================================================
  ;; Object Ingestion with Immutable Provenance
  ;; ============================================================

  (define (make-object-provenance path content principal certificate)
    (let* ((content-bv (if (string? content)
                           (string->utf8 content)
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
                                 (string->utf8 (format "~s" certificate))))
                               #f))
        (immutable #t))))

  (define (wormhole-ingest path content wormhole)
    (let* ((fs-path (wormhole-fs-path wormhole))
           (vault-path (wormhole-vault-path wormhole))
           (principal (wormhole-principal fs-path vault-path))
           (provenance (make-object-provenance path content principal #f))
           (metadata (capture-metadata path)))
      (wormhole-audit wormhole 'ingest 'ingest path)
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
    (format "wormhole-~a-~a" (current-seconds) wormhole-id-counter))

  (define (wormhole-open fs-path . opts)
    (let ((vault-path (get-key opts 'vault-path: "/"))
          (capabilities (get-key opts 'capabilities: capability:read-write))
          (rate-lim (get-key opts 'rate-limit: 1000))
          (locked (get-key opts 'locked: #f))
          (auth-required (get-key opts 'auth-required: '()))
          (certificate (get-key opts 'certificate: #f)))
      (unless certificate
        (error 'unauthorized "Wormhole requires SPKI certificate"))
      (unless (verify-wormhole-cert certificate fs-path vault-path)
        (error 'unauthorized "Invalid wormhole certificate"))
      (unless (fuse-available?)
        (error 'fuse-unavailable
               "FUSE not installed. Install with: brew install fuse-t"))
      (let* ((id (generate-wormhole-id))
             (wh (make-wormhole-internal
                  id fs-path vault-path capabilities
                  rate-lim 0 (current-seconds)
                  '() (current-seconds)
                  locked auth-required)))
        (wormhole-audit wh 'wormhole-open 'open fs-path
                        `((vault ,vault-path)
                          (capabilities ,(length capabilities))))
        (hash-table-set! *active-wormholes* fs-path wh)
        wh)))

  (define (wormhole-close wormhole)
    (wormhole-audit wormhole 'wormhole-close 'close
                     (wormhole-fs-path wormhole))
    (let ((path (wormhole-fs-path wormhole)))
      (when (and (fuse-available?) (file-exists? path))
        (fuse-unmount path)))
    (hash-table-delete! *active-wormholes* (wormhole-fs-path wormhole))
    #t)

  (define (wormhole-active? path)
    (hash-table-exists? *active-wormholes* path))

  (define (wormhole-list)
    (hash-table-keys *active-wormholes*))

  (define (wormhole-status wormhole)
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
  ;; FUSE Manifest (In-Memory)
  ;; ============================================================

  (define *wormhole-manifest* (make-hash-table string=?))

  (define (manifest-init! wormhole)
    (hash-table-set! *wormhole-manifest* "/"
                     `((type . directory)
                       (mode . ,(bitwise-ior S_IFDIR #o755))
                       (nlink . 2)
                       (mtime . ,(current-seconds))
                       (children . ()))))

  (define (manifest-lookup path)
    (hash-table-ref/default *wormhole-manifest* path #f))

  (define (manifest-add! path entry)
    (hash-table-set! *wormhole-manifest* path entry)
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
    (let* ((parent (pathname-directory path))
           (name (pathname-strip-directory path))
           (parent-entry (manifest-lookup parent)))
      (hash-table-delete! *wormhole-manifest* path)
      (when parent-entry
        (let ((children (alist-ref 'children parent-entry)))
          (hash-table-set! *wormhole-manifest* parent
                           (alist-update 'children
                                         (filter (lambda (c)
                                                   (not (string=? c name)))
                                                 (or children '()))
                                         parent-entry))))))

  ;; ============================================================
  ;; Mount/Unmount
  ;; ============================================================

  (define *active-wormhole* #f)

  (define (wormhole-mount wormhole)
    (set! *active-wormhole* wormhole)
    (wormhole-audit wormhole 'mount 'fuse-mount
                     (wormhole-fs-path wormhole)
                     `((vault ,(wormhole-vault-path wormhole))))
    (fuse-mount (wormhole-fs-path wormhole)
                (wormhole-vault-path wormhole)))

  (define (wormhole-unmount wormhole)
    (let ((path (wormhole-fs-path wormhole)))
      (system (format "umount ~a 2>/dev/null || diskutil unmount ~a 2>/dev/null" path path))
      (set! *active-wormhole* #f)
      #t))

  ;; ============================================================
  ;; Introspection - Immutable Provenance
  ;; ============================================================

  (define *introspection-store* (make-hash-table string=?))
  (define (introspection-store) *introspection-store*)

  (define (make-introspection-rec content-hash provenance authority temporal signature)
    `(introspection
      (content-hash ,content-hash)
      (provenance ,provenance)
      (authority ,authority)
      (temporal ,temporal)
      (signature ,signature)))

  (define (introspection? obj)
    (and (pair? obj)
         (eq? (car obj) 'introspection)))

  (define (introspection-hash intro)
    (cadr (assq 'content-hash (cdr intro))))

  (define (introspection-provenance intro)
    (cadr (assq 'provenance (cdr intro))))

  (define (introspection-authority intro)
    (cadr (assq 'authority (cdr intro))))

  (define (introspection-temporal intro)
    (cadr (assq 'temporal (cdr intro))))

  (define (introspection-signature intro)
    (cadr (assq 'signature (cdr intro))))

  (define (introspection-valid? intro . rest)
    (let* ((signing-key (if (null? rest) #f (car rest)))
           (sig-data (introspection-signature intro))
           (sig-type (car sig-data))
           (to-verify `(introspection
                        (content-hash ,(introspection-hash intro))
                        (provenance ,(introspection-provenance intro))
                        (authority ,(introspection-authority intro))
                        (temporal ,(introspection-temporal intro))))
           (message (string->utf8
                     (with-output-to-string
                       (lambda () (write to-verify))))))
      (cond
       ((eq? sig-type 'ed25519)
        (let ((pubkey (or signing-key
                          (authority-public-key (introspection-authority intro)))))
          (and pubkey
               (ed25519-verify message
                              (cadr sig-data)
                              pubkey))))
       (else #f))))

  (define (authority-public-key authority)
    (let ((pk (assq 'public-key authority)))
      (and pk (cadr pk))))

  (define (stamp-introspection! wormhole content source-path)
    (let* ((content-bv (if (bytevector? content)
                           content
                           (string->utf8 (->string content))))
           (content-hash (format "sha512:~a"
                                  (bytevector->hex (sha512-hash content-bv))))
           (provenance `((wormhole ,(wormhole-id wormhole))
                         (fs-path ,(wormhole-fs-path wormhole))
                         (vault-path ,(wormhole-vault-path wormhole))
                         (source-path ,source-path)
                         (source-host ,(hostname))))
           (principal-id (string-append "wormhole:" (wormhole-id wormhole)
                                        "@" (hostname)))
           (authority `((capabilities ,(wormhole-capabilities wormhole))
                        (rate-limit ,(wormhole-rate-limit wormhole))
                        (principal ,principal-id)
                        (node ,(hostname))))
           (temporal `((wallclock ,(current-seconds))
                       (node-id ,(hostname))))
           (unsigned `(introspection
                       (content-hash ,content-hash)
                       (provenance ,provenance)
                       (authority ,authority)
                       (temporal ,temporal)))
           (message (string->utf8
                     (with-output-to-string
                       (lambda () (write unsigned)))))
           (signature `(local-stamp
                        (node ,(hostname))
                        (hash ,(sha512-hash message))))
           (intro (make-introspection-rec content-hash provenance authority temporal signature)))
      (hash-table-set! *introspection-store* content-hash intro)
      (wormhole-audit wormhole 'introspection-stamp 'stamp source-path
                      `((hash ,content-hash)))
      intro))

  (define (introspect hash-or-content)
    (let ((hash (if (and (string? hash-or-content)
                         (string-prefix? "sha512:" hash-or-content))
                    hash-or-content
                    (let ((bv (if (bytevector? hash-or-content)
                                 hash-or-content
                                 (string->utf8 (->string hash-or-content)))))
                      (format "sha512:~a"
                               (bytevector->hex (sha512-hash bv)))))))
      (hash-table-ref/default *introspection-store* hash #f)))

  ;; ============================================================
  ;; Config Export - Host Configuration Deployment
  ;; ============================================================

  (define *config-manifest* '())
  (define (config-manifest) *config-manifest*)

  (define (expand-tilde path)
    (if (and (> (string-length path) 0)
             (char=? (string-ref path 0) #\~))
        (string-append (or (getenv "HOME") "")
                       (substring path 1 (string-length path)))
        path))

  (define (config-register! name source target . opts)
    (let ((mode (get-key opts 'mode: 'symlink)))
      (set! *config-manifest*
            (cons `(,name ,source ,(expand-tilde target) ,mode)
                  (filter (lambda (e) (not (eq? (car e) name)))
                          *config-manifest*)))))

  (define (config-source-path name)
    (let ((entry (assq name *config-manifest*)))
      (and entry
           (let ((rel-path (cadr entry)))
             (let ((base (or (getenv "CYBERSPACE_SCHEME")
                            "/Users/ddp/cyberspace/spki/scheme")))
               (make-pathname base rel-path))))))

  (define (config-export! name . opts)
    (let ((force (get-key opts 'force: #f)))
      (let ((entry (assq name *config-manifest*)))
        (unless entry
          (error 'config-not-found (format "Unknown config: ~a" name)))
        (let* ((source (config-source-path name))
               (target (caddr entry))
               (mode (cadddr entry))
               (target-dir (pathname-directory target)))
          (unless (file-exists? source)
            (error 'source-not-found (format "Config source missing: ~a" source)))
          (unless (directory-exists? target-dir)
            (guard (exn [#t #f])
              (mkdir target-dir #o755)))
          (cond
           ((file-exists? target)
            (if force
                (begin
                  (delete-file target)
                  (config-deploy! source target mode)
                  'updated)
                'exists))
           (else
            (config-deploy! source target mode)
            'created))))))

  (define (config-deploy! source target mode)
    (case mode
      ((symlink)
       (system (format "ln -s '~a' '~a'" source target)))
      ((copy)
       (system (format "cp '~a' '~a'" source target)))
      ((wormhole)
       ;; Fallback: symlink when no FUSE
       (system (format "ln -s '~a' '~a'" source target)))
      (else
       (error 'unknown-mode (format "Unknown deploy mode: ~a" mode)))))

  (define (config-export-all! . opts)
    (let ((force (get-key opts 'force: #f)))
      (map (lambda (entry)
             (let ((name (car entry)))
               (cons name
                     (guard (exn [#t 'error])
                       (config-export! name 'force: force)))))
           *config-manifest*)))

  (define (config-status . rest)
    (let ((name (if (null? rest) #f (car rest))))
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
            (target-exists . ,(file-exists? target)))))
      (if name
          (let ((entry (assq name *config-manifest*)))
            (if entry (check-one entry) #f))
          (map check-one *config-manifest*))))

  (define (config-diff name)
    (let* ((entry (assq name *config-manifest*))
           (source (and entry (config-source-path name)))
           (target (and entry (caddr entry))))
      (cond
       ((not entry) (error 'config-not-found name))
       ((not (file-exists? source)) `(source-missing ,source))
       ((not (file-exists? target)) `(target-missing ,target))
       (else
        (let ((src-content (with-input-from-file source
                             (lambda () (get-string-all (current-input-port)))))
              (tgt-content (with-input-from-file target
                             (lambda () (get-string-all (current-input-port))))))
          (if (string=? src-content tgt-content)
              #f
              `(content-differs)))))))

  ;; ============================================================
  ;; Default Config Manifest
  ;; ============================================================

  (config-register! 'kitty "config/kitty.conf" "~/.config/kitty/kitty.conf")

) ;; end library
