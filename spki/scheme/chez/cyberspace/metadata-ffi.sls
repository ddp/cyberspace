;;; metadata-ffi.sls - File Metadata FFI for Darwin (Memo-042)
;;;
;;; Provides bindings for extended attributes, BSD flags, and ACLs.
;;; Darwin-specific; other platforms will need separate implementations.
;;;
;;; Build the bridge: cc -shared -o libmetadata-bridge.dylib metadata-bridge.c

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

  (import (rnrs)
          (rnrs mutable-strings)
          (only (chezscheme)
                load-shared-object foreign-procedure
                foreign-alloc foreign-free
                foreign-ref foreign-set!))

  ;; ============================================================
  ;; Library Loading
  ;; ============================================================

  (define *metadata-bridge-loaded*
    (let loop ((paths '("./libmetadata-bridge.dylib"
                        "../libmetadata-bridge.dylib"
                        "libmetadata-bridge.dylib"
                        "./libmetadata-bridge.so"
                        "../libmetadata-bridge.so"
                        "libmetadata-bridge.so")))
      (if (null? paths)
          #f
          (guard (exn [#t (loop (cdr paths))])
            (load-shared-object (car paths))
            #t))))

  (define (metadata-ffi-available?) *metadata-bridge-loaded*)

  ;; ============================================================
  ;; Foreign Procedures
  ;; ============================================================

  (define-syntax define-meta-foreign
    (syntax-rules ()
      [(_ name expr)
       (define name
         (if *metadata-bridge-loaded*
             expr
             (lambda args
               (error 'metadata-ffi
                      "Metadata bridge not loaded -- build libmetadata-bridge"))))]))

  (define-meta-foreign %xattr-list
    (foreign-procedure "metadata_xattr_list" (string void*) void*))

  (define-meta-foreign %xattr-get
    (foreign-procedure "metadata_xattr_get" (string string void*) void*))

  (define-meta-foreign %xattr-set
    (foreign-procedure "metadata_xattr_set" (string string string int) int))

  (define-meta-foreign %xattr-remove
    (foreign-procedure "metadata_xattr_remove" (string string) int))

  (define-meta-foreign %get-flags
    (foreign-procedure "metadata_get_flags" (string) unsigned-int))

  (define-meta-foreign %set-flags
    (foreign-procedure "metadata_set_flags" (string unsigned-int) int))

  (define-meta-foreign %acl-get-text
    (foreign-procedure "metadata_acl_get_text" (string) void*))

  (define-meta-foreign %acl-set-text
    (foreign-procedure "metadata_acl_set_text" (string string) int))

  (define-meta-foreign %meta-free
    (foreign-procedure "metadata_free" (void*) void))

  ;; ============================================================
  ;; Constants
  ;; ============================================================

  ;; User flags
  (define UF_NODUMP    #x00000001)
  (define UF_IMMUTABLE #x00000002)
  (define UF_APPEND    #x00000004)
  (define UF_OPAQUE    #x00000008)
  (define UF_HIDDEN    #x00008000)

  ;; Super-user flags
  (define SF_ARCHIVED  #x00010000)
  (define SF_IMMUTABLE #x00020000)
  (define SF_APPEND    #x00040000)

  ;; ============================================================
  ;; Scheme API
  ;; ============================================================

  (define (xattr-list path)
    "List extended attribute names for a file."
    (if (not *metadata-bridge-loaded*)
        '()
        (let ((len-ptr (foreign-alloc 4)))
          (foreign-set! 'int len-ptr 0 0)
          (let ((buf (%xattr-list path len-ptr)))
            (let ((len (foreign-ref 'int len-ptr 0)))
              (foreign-free len-ptr)
              (if (or (= buf 0) (<= len 0))
                  '()
                  (let ((result (parse-null-separated-string buf len)))
                    (%meta-free buf)
                    result)))))))

  (define (parse-null-separated-string ptr len)
    "Parse a null-separated C string into a list of strings."
    (let loop ((i 0) (start 0) (acc '()))
      (if (>= i len)
          (reverse (if (> i start)
                       (cons (extract-c-string ptr start (- i start)) acc)
                       acc))
          (if (= (foreign-ref 'unsigned-8 ptr i) 0)
              (loop (+ i 1) (+ i 1)
                    (if (> i start)
                        (cons (extract-c-string ptr start (- i start)) acc)
                        acc))
              (loop (+ i 1) start acc)))))

  (define (extract-c-string ptr offset len)
    "Extract a string from a C buffer."
    (let ((s (make-string len)))
      (do ((i 0 (+ i 1)))
          ((= i len) s)
        (string-set! s i (integer->char (foreign-ref 'unsigned-8 ptr (+ offset i)))))))

  (define (xattr-get path name)
    "Get extended attribute value as bytevector, or #f."
    (if (not *metadata-bridge-loaded*)
        #f
        (let ((len-ptr (foreign-alloc 4)))
          (foreign-set! 'int len-ptr 0 0)
          (let ((buf (%xattr-get path name len-ptr)))
            (let ((len (foreign-ref 'int len-ptr 0)))
              (foreign-free len-ptr)
              (if (= buf 0)
                  #f
                  (let ((bv (make-bytevector len)))
                    (do ((i 0 (+ i 1)))
                        ((= i len))
                      (bytevector-u8-set! bv i (foreign-ref 'unsigned-8 buf i)))
                    (%meta-free buf)
                    bv)))))))

  (define (xattr-set path name value)
    "Set extended attribute. Value: bytevector or string."
    (let* ((data (if (string? value) value
                     (utf8->string value)))
           (len (if (string? value) (string-length value)
                    (bytevector-length value))))
      (zero? (%xattr-set path name data len))))

  (define (xattr-remove path name)
    "Remove extended attribute."
    (zero? (%xattr-remove path name)))

  (define (file-flags path)
    "Get BSD file flags as integer."
    (%get-flags path))

  (define (file-flags-set! path flags)
    "Set BSD file flags."
    (zero? (%set-flags path flags)))

  (define (acl-text path)
    "Get ACL as human-readable text, or #f."
    (if (not *metadata-bridge-loaded*)
        #f
        (let ((buf (%acl-get-text path)))
          (if (= buf 0)
              #f
              (let ((result (c-string->string buf)))
                (%meta-free buf)
                result)))))

  (define (c-string->string ptr)
    "Extract null-terminated C string."
    (let loop ((i 0))
      (if (= (foreign-ref 'unsigned-8 ptr i) 0)
          (extract-c-string ptr 0 i)
          (loop (+ i 1)))))

  (define (acl-get path)
    "Get ACL entries as list of strings."
    (let ((text (acl-text path)))
      (if text
          (filter (lambda (s) (> (string-length s) 0))
                  (string-split-newlines text))
          '())))

  (define (string-split-newlines s)
    (let ((len (string-length s)))
      (let loop ((i 0) (start 0) (acc '()))
        (cond
          ((= i len)
           (reverse (if (= start i) acc (cons (substring s start i) acc))))
          ((char=? (string-ref s i) #\newline)
           (loop (+ i 1) (+ i 1)
                 (if (= start i) acc (cons (substring s start i) acc))))
          (else (loop (+ i 1) start acc))))))

  (define (acl-set path text)
    "Set ACL from text representation."
    (zero? (%acl-set-text path text)))

) ;; end library
