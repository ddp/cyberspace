;;; metadata-ffi.scm - File Metadata FFI for Darwin (Memo-042)
;;;
;;; Provides bindings for extended attributes, BSD flags, and ACLs.
;;; Darwin-specific; other platforms will need separate implementations.
;;;
;;; Copyright (c) 2026 Yoyodyne. See LICENSE.

(module metadata-ffi
  (;; Extended attributes
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

   ;; ACL (simplified)
   acl-get
   acl-text

   ;; Availability
   metadata-ffi-available?)

(import scheme
        (chicken base)
        (chicken foreign)
        (chicken blob)
        (chicken memory)
        (chicken string)
        srfi-1
        srfi-4
        srfi-13)

;;; ============================================================
;;; Foreign Includes
;;; ============================================================

#>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/xattr.h>
#include <sys/acl.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>

/* Get list of xattr names, return as null-separated string */
static char* get_xattr_list(const char* path, ssize_t* out_len) {
    ssize_t len = listxattr(path, NULL, 0, XATTR_NOFOLLOW);
    if (len <= 0) {
        *out_len = 0;
        return NULL;
    }
    char* buf = malloc(len);
    if (!buf) {
        *out_len = 0;
        return NULL;
    }
    ssize_t actual = listxattr(path, buf, len, XATTR_NOFOLLOW);
    if (actual < 0) {
        free(buf);
        *out_len = 0;
        return NULL;
    }
    *out_len = actual;
    return buf;
}

/* Get single xattr value */
static char* get_xattr_value(const char* path, const char* name, ssize_t* out_len) {
    ssize_t len = getxattr(path, name, NULL, 0, 0, XATTR_NOFOLLOW);
    if (len < 0) {
        *out_len = 0;
        return NULL;
    }
    if (len == 0) {
        *out_len = 0;
        return strdup("");
    }
    char* buf = malloc(len + 1);
    if (!buf) {
        *out_len = 0;
        return NULL;
    }
    ssize_t actual = getxattr(path, name, buf, len, 0, XATTR_NOFOLLOW);
    if (actual < 0) {
        free(buf);
        *out_len = 0;
        return NULL;
    }
    buf[actual] = '\0';
    *out_len = actual;
    return buf;
}

/* Set xattr value */
static int set_xattr_value(const char* path, const char* name, const char* value, size_t len) {
    return setxattr(path, name, value, len, 0, XATTR_NOFOLLOW);
}

/* Remove xattr */
static int remove_xattr_value(const char* path, const char* name) {
    return removexattr(path, name, XATTR_NOFOLLOW);
}

/* Get BSD file flags from stat */
static unsigned int get_file_flags(const char* path) {
    struct stat st;
    if (lstat(path, &st) < 0) return 0;
    return st.st_flags;
}

/* Set BSD file flags */
static int set_file_flags(const char* path, unsigned int flags) {
    return chflags(path, flags);
}

/* Get ACL as text (caller must free) */
static char* get_acl_text(const char* path) {
    acl_t acl = acl_get_file(path, ACL_TYPE_EXTENDED);
    if (!acl) return NULL;
    char* text = acl_to_text(acl, NULL);
    acl_free(acl);
    if (!text) return NULL;
    char* result = strdup(text);
    acl_free(text);
    return result;
}
<#

;;; ============================================================
;;; Extended Attributes
;;; ============================================================

(define c-get-xattr-list
  (foreign-lambda c-pointer "get_xattr_list" c-string (c-pointer ssize_t)))

(define c-get-xattr-value
  (foreign-lambda c-pointer "get_xattr_value" c-string c-string (c-pointer ssize_t)))

(define c-set-xattr
  (foreign-lambda int "set_xattr_value" c-string c-string scheme-pointer size_t))

(define c-remove-xattr
  (foreign-lambda int "remove_xattr_value" c-string c-string))

(define c-free
  (foreign-lambda void "free" c-pointer))

(define (xattr-list path)
  "List extended attribute names for a file.
   Returns list of strings, or empty list if none."
  (let-location ((len ssize_t 0))
    (let ((buf (c-get-xattr-list path (location len))))
      (if (or (not buf) (<= len 0))
          '()
          (let* ((str (make-string len))
                 (_ (move-memory! buf str len))
                 (names (string-split str "\x00" #t)))
            (c-free buf)
            (filter (lambda (s) (> (string-length s) 0)) names))))))

(define (xattr-get path name)
  "Get extended attribute value.
   Returns blob or #f if not found."
  (let-location ((len ssize_t 0))
    (let ((buf (c-get-xattr-value path name (location len))))
      (if (not buf)
          #f
          (let ((blob (make-blob len)))
            (move-memory! buf blob len)
            (c-free buf)
            blob)))))

(define (xattr-set path name value)
  "Set extended attribute. Value should be blob or string.
   Returns #t on success, #f on failure."
  (let* ((data (if (string? value) (string->blob value) value))
         (len (blob-size data)))
    (zero? (c-set-xattr path name data len))))

(define (xattr-remove path name)
  "Remove extended attribute.
   Returns #t on success, #f on failure."
  (zero? (c-remove-xattr path name)))

;;; ============================================================
;;; BSD File Flags
;;; ============================================================

(define c-get-flags
  (foreign-lambda unsigned-int "get_file_flags" c-string))

(define c-set-flags
  (foreign-lambda int "set_file_flags" c-string unsigned-int))

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
   Use bitwise-and with flag constants to test."
  (c-get-flags path))

(define (file-flags-set! path flags)
  "Set BSD file flags.
   Returns #t on success, #f on failure (may require root)."
  (zero? (c-set-flags path flags)))

;;; ============================================================
;;; ACL (Access Control Lists)
;;; ============================================================

(define c-get-acl-text
  (foreign-lambda c-pointer "get_acl_text" c-string))

(define (acl-get path)
  "Get ACL entries for a file.
   Returns list of ACL entry strings, or empty list if no ACL."
  (let ((text (acl-text path)))
    (if text
        (filter (lambda (s) (> (string-length s) 0))
                (string-split text "\n"))
        '())))

(define (acl-text path)
  "Get ACL as human-readable text, or #f if no ACL."
  (let ((buf (c-get-acl-text path)))
    (if buf
        (let ((str (make-string 4096)))
          ;; Copy and free - assume ACL text < 4K
          (move-memory! buf str 4096)
          (c-free buf)
          (let ((null-pos (string-index str #\null)))
            (if null-pos
                (substring str 0 null-pos)
                str)))
        #f)))

;;; ============================================================
;;; Availability Check
;;; ============================================================

(define (metadata-ffi-available?)
  "Check if metadata FFI is available (Darwin only for now)."
  #t)  ; If this module loads, it's available

) ; end module
