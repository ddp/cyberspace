;;; metadata-ffi.sls - File Metadata FFI for Darwin (Chez Port)
;;; Library of Cyberspace
;;;
;;; Provides bindings for extended attributes, BSD flags, and ACLs.
;;; Darwin-specific; other platforms will need separate implementations.
;;;
;;; Uses a C bridge (metadata-bridge.c) loaded via load-shared-object.
;;; When the bridge is not available, all operations return graceful errors.
;;;
;;; Ported from metadata-ffi.scm.
;;; Copyright (c) 2026 Yoyodyne. See LICENSE.

(library (cyberspace metadata-ffi)
  (export
    ;; Extended attributes
    xattr-list
    xattr-get
    xattr-set
    xattr-remove

    ;; BSD file flags
    file-flags
    file-flags-set!

    ;; Flag constants
    UF_NODUMP UF_IMMUTABLE UF_APPEND UF_OPAQUE UF_HIDDEN
    SF_ARCHIVED SF_IMMUTABLE SF_APPEND

    ;; ACL
    acl-get
    acl-set
    acl-text

    ;; Availability
    metadata-ffi-available?)

  (import (except (rnrs) file-exists? find)
          (only (chezscheme)
                printf format void
                load-shared-object foreign-procedure
                file-exists?)
          (cyberspace chicken-compatibility chicken)
          (cyberspace os))

  ;; ============================================================
  ;; Bridge Loading
  ;; ============================================================
  ;;
  ;; metadata-bridge.c provides:
  ;;   metadata_xattr_list(path, buf, buflen) -> int (count)
  ;;   metadata_xattr_get(path, name, buf, buflen) -> int (len)
  ;;   metadata_xattr_set(path, name, val, vallen) -> int (0=ok)
  ;;   metadata_xattr_remove(path, name) -> int (0=ok)
  ;;   metadata_file_flags(path) -> unsigned int
  ;;   metadata_file_flags_set(path, flags) -> int (0=ok)
  ;;   metadata_acl_text(path, buf, buflen) -> int (len)
  ;;   metadata_acl_set(path, text) -> int (0=ok)

  (define *bridge-loaded*
    (guard (exn [#t
      (guard (exn2 [#t #f])
        (load-shared-object "libmetadata-bridge.dylib")
        #t)])
      (load-shared-object "libmetadata-bridge.so")
      #t))

  (define (metadata-ffi-available?)
    "Check if metadata FFI bridge is loaded."
    (if *bridge-loaded* #t #f))

  (define (bridge-check who)
    (unless *bridge-loaded*
      (error who "metadata-bridge not loaded; build with: cc -shared -o libmetadata-bridge.so metadata-bridge.c")))

  ;; ============================================================
  ;; Extended Attributes (via shell fallback)
  ;; ============================================================
  ;;
  ;; When bridge is not loaded, fall back to shell commands:
  ;;   xattr -l <path>          (list)
  ;;   xattr -p <name> <path>   (get)
  ;;   xattr -w <name> <val> <path> (set)
  ;;   xattr -d <name> <path>   (remove)

  (define (xattr-list path)
    "List extended attribute names for a file.
     Returns list of strings, or empty list if none."
    (if *bridge-loaded*
        (begin
          ;; TODO: use FFI when bridge is built
          (xattr-list-shell path))
        (xattr-list-shell path)))

  (define (xattr-list-shell path)
    "List xattrs via shell command."
    (let ((lines (shell-lines (string-append "xattr '" path "' 2>/dev/null"))))
      (or lines '())))

  (define (xattr-get path name)
    "Get extended attribute value.
     Returns string or #f if not found."
    (let ((result (shell-command
                   (string-append "xattr -p '" name "' '" path "' 2>/dev/null"))))
      result))

  (define (xattr-set path name value)
    "Set extended attribute. Value should be string.
     Returns #t on success, #f on failure."
    (let ((val-str (if (string? value) value
                       (error 'xattr-set "Expected string value" value))))
      (shell-success?
       (string-append "xattr -w '" name "' '" val-str "' '" path "'"))))

  (define (xattr-remove path name)
    "Remove extended attribute.
     Returns #t on success, #f on failure."
    (shell-success?
     (string-append "xattr -d '" name "' '" path "' 2>/dev/null")))

  ;; ============================================================
  ;; BSD File Flags
  ;; ============================================================

  ;; User flags (can be set by owner)
  (define UF_NODUMP    #x00000001)  ; do not dump file
  (define UF_IMMUTABLE #x00000002)  ; file may not be changed
  (define UF_APPEND    #x00000004)  ; writes to file may only append
  (define UF_OPAQUE    #x00000008)  ; directory is opaque wrt. union
  (define UF_HIDDEN    #x00008000)  ; file is hidden

  ;; Super-user flags
  (define SF_ARCHIVED  #x00010000)  ; file is archived
  (define SF_IMMUTABLE #x00020000)  ; file may not be changed
  (define SF_APPEND    #x00040000)  ; writes to file may only append

  (define (file-flags path)
    "Get BSD file flags as integer.
     Use bitwise-and with flag constants to test.
     Falls back to stat(1) when bridge is not loaded."
    (if *bridge-loaded*
        (begin
          ;; TODO: use FFI when bridge is built
          (file-flags-shell path))
        (file-flags-shell path)))

  (define (file-flags-shell path)
    "Get file flags via stat command."
    (let ((result (shell-command
                   (string-append "stat -f '%f' '" path "' 2>/dev/null"))))
      (if result
          (or (string->number result) 0)
          0)))

  (define (file-flags-set! path flags)
    "Set BSD file flags.
     Returns #t on success, #f on failure (may require root)."
    (shell-success?
     (string-append "chflags " (number->string flags) " '" path "'")))

  ;; ============================================================
  ;; ACL (Access Control Lists)
  ;; ============================================================

  (define (acl-text path)
    "Get ACL as human-readable text, or #f if no ACL."
    (let ((result (shell-command
                   (string-append "ls -le '" path "' 2>/dev/null | grep -A99 '^ [0-9]'"))))
      (if (and result (> (string-length result) 0))
          result
          #f)))

  (define (acl-get path)
    "Get ACL entries for a file.
     Returns list of ACL entry strings, or empty list if no ACL."
    (let ((text (acl-text path)))
      (if text
          (let ((lines (shell-lines
                        (string-append "ls -le '" path "' 2>/dev/null | grep '^ [0-9]'"))))
            (or lines '()))
          '())))

  (define (acl-set path text)
    "Set ACL from text representation.
     Returns #t on success, #f on failure."
    (if *bridge-loaded*
        (begin
          ;; TODO: use FFI when bridge is built
          (printf "[metadata-ffi] ACL set via bridge not yet available~%")
          #f)
        (begin
          (printf "[metadata-ffi] ACL set requires metadata-bridge.c~%")
          #f)))

) ;; end library
