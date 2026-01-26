;;; fuse-ffi.scm - FUSE FFI Bindings for Cyberspace Wormholes (Memo-042)
;;;
;;; Provides low-level bindings to libfuse / FUSE-T for implementing
;;; userspace filesystems. Used by wormhole.scm for vault mounts.
;;;
;;; Installation:
;;;   brew install fuse-t    # Recommended (no kernel extension)
;;;   brew install macfuse   # Alternative (requires kernel extension)
;;;
;;; FUSE-T library: /usr/local/lib/libfuse-t.dylib
;;; macFUSE library: /usr/local/lib/libfuse.dylib

(module fuse-ffi
  (;; Initialization
   fuse-init
   fuse-available?
   fuse-library-path

   ;; Main loop
   fuse-mount
   fuse-unmount
   fuse-loop
   fuse-exit

   ;; Operation callbacks (set these before fuse-mount)
   fuse-set-getattr!
   fuse-set-readdir!
   fuse-set-open!
   fuse-set-read!
   fuse-set-write!
   fuse-set-create!
   fuse-set-unlink!
   fuse-set-mkdir!
   fuse-set-rmdir!
   fuse-set-rename!
   fuse-set-truncate!
   fuse-set-setxattr!
   fuse-set-getxattr!
   fuse-set-listxattr!
   fuse-set-removexattr!

   ;; Stat structure helpers
   make-fuse-stat
   fuse-stat-mode-set!
   fuse-stat-nlink-set!
   fuse-stat-size-set!
   fuse-stat-uid-set!
   fuse-stat-gid-set!
   fuse-stat-atime-set!
   fuse-stat-mtime-set!
   fuse-stat-ctime-set!

   ;; Constants
   S_IFDIR S_IFREG S_IFLNK
   O_RDONLY O_WRONLY O_RDWR O_CREAT O_TRUNC
   ENOENT EACCES EIO EEXIST ENOTDIR EISDIR ENOTEMPTY)

(import scheme
        (chicken base)
        (chicken foreign)
        (chicken blob)
        (chicken memory)
        (chicken format)
        (chicken file)
        (chicken process)
        (srfi 4))

;;; ============================================================
;;; Library Detection
;;; ============================================================

(define (fuse-library-path)
  "Find the FUSE library path. Prefers FUSE-T over macFUSE."
  (cond
    ((file-exists? "/usr/local/lib/libfuse-t.dylib")
     "/usr/local/lib/libfuse-t.dylib")
    ((file-exists? "/opt/homebrew/lib/libfuse-t.dylib")
     "/opt/homebrew/lib/libfuse-t.dylib")
    ((file-exists? "/usr/local/lib/libfuse.dylib")
     "/usr/local/lib/libfuse.dylib")
    ((file-exists? "/opt/homebrew/lib/libfuse.dylib")
     "/opt/homebrew/lib/libfuse.dylib")
    (else #f)))

(define (fuse-available?)
  "Check if FUSE library is available."
  (and (fuse-library-path) #t))

;;; ============================================================
;;; Constants
;;; ============================================================

;; File type bits (from sys/stat.h)
(define S_IFDIR #o0040000)  ; Directory
(define S_IFREG #o0100000)  ; Regular file
(define S_IFLNK #o0120000)  ; Symbolic link

;; Open flags (from fcntl.h)
(define O_RDONLY 0)
(define O_WRONLY 1)
(define O_RDWR   2)
(define O_CREAT  #x0200)
(define O_TRUNC  #x0400)

;; Error codes (from errno.h)
(define ENOENT   2)   ; No such file or directory
(define EACCES  13)   ; Permission denied
(define EIO      5)   ; I/O error
(define EEXIST  17)   ; File exists
(define ENOTDIR 20)   ; Not a directory
(define EISDIR  21)   ; Is a directory
(define ENOTEMPTY 66) ; Directory not empty

;;; ============================================================
;;; Foreign Declarations
;;; ============================================================

#>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/types.h>

/* Check for FUSE availability at compile time */
#if __has_include(<fuse.h>)
#define FUSE_USE_VERSION 26
#include <fuse.h>
#define HAVE_FUSE 1
#else
#define HAVE_FUSE 0
/* Stub definitions when FUSE not available */
struct fuse_operations { int dummy; };
struct fuse_file_info { int flags; };
typedef int (*fuse_fill_dir_t)(void *, const char *, void *, off_t);
#endif

/* Callback storage - set from Scheme */
static C_word scheme_getattr_callback = C_SCHEME_FALSE;
static C_word scheme_readdir_callback = C_SCHEME_FALSE;
static C_word scheme_open_callback = C_SCHEME_FALSE;
static C_word scheme_read_callback = C_SCHEME_FALSE;
static C_word scheme_write_callback = C_SCHEME_FALSE;
static C_word scheme_create_callback = C_SCHEME_FALSE;
static C_word scheme_unlink_callback = C_SCHEME_FALSE;
static C_word scheme_mkdir_callback = C_SCHEME_FALSE;
static C_word scheme_rmdir_callback = C_SCHEME_FALSE;
static C_word scheme_rename_callback = C_SCHEME_FALSE;
static C_word scheme_truncate_callback = C_SCHEME_FALSE;
static C_word scheme_setxattr_callback = C_SCHEME_FALSE;
static C_word scheme_getxattr_callback = C_SCHEME_FALSE;
static C_word scheme_listxattr_callback = C_SCHEME_FALSE;

/* Stat buffer for returning file attributes */
static struct stat fuse_stat_buffer;

/* Initialize stat buffer */
static void init_stat_buffer(void) {
    memset(&fuse_stat_buffer, 0, sizeof(struct stat));
}

/* Stat buffer accessors */
static void set_stat_mode(int mode) { fuse_stat_buffer.st_mode = mode; }
static void set_stat_nlink(int nlink) { fuse_stat_buffer.st_nlink = nlink; }
static void set_stat_size(off_t size) { fuse_stat_buffer.st_size = size; }
static void set_stat_uid(uid_t uid) { fuse_stat_buffer.st_uid = uid; }
static void set_stat_gid(gid_t gid) { fuse_stat_buffer.st_gid = gid; }
static void set_stat_atime(time_t t) { fuse_stat_buffer.st_atime = t; }
static void set_stat_mtime(time_t t) { fuse_stat_buffer.st_mtime = t; }
static void set_stat_ctime(time_t t) { fuse_stat_buffer.st_ctime = t; }

#if HAVE_FUSE
/* Directory entry buffer for readdir */
static void *readdir_buf = NULL;
static fuse_fill_dir_t readdir_filler = NULL;

/* Add directory entry from Scheme */
static int add_dir_entry(const char *name) {
    if (readdir_buf && readdir_filler) {
        return readdir_filler(readdir_buf, name, NULL, 0);
    }
    return -1;
}

/* FUSE operation wrappers */

static int cs_getattr(const char *path, struct stat *stbuf) {
    memset(stbuf, 0, sizeof(struct stat));
    if (strcmp(path, "/") == 0) {
        stbuf->st_mode = S_IFDIR | 0755;
        stbuf->st_nlink = 2;
        return 0;
    }
    return -ENOENT;
}

static int cs_readdir(const char *path, void *buf, fuse_fill_dir_t filler,
                      off_t offset, struct fuse_file_info *fi) {
    (void) offset;
    (void) fi;
    if (strcmp(path, "/") != 0)
        return -ENOENT;
    filler(buf, ".", NULL, 0);
    filler(buf, "..", NULL, 0);
    return 0;
}

static struct fuse_operations cyberspace_ops = {
    .getattr = cs_getattr,
    .readdir = cs_readdir,
};

static struct fuse *fuse_instance = NULL;
static char *mount_point = NULL;
static volatile int fuse_running = 0;

/* Run FUSE - call from Scheme, blocks until unmount */
static int run_fuse(const char *mountpoint) {
    char *argv[] = {"cyberspace", (char*)mountpoint, "-f", NULL};
    int argc = 3;
    mount_point = strdup(mountpoint);
    fuse_running = 1;
    int ret = fuse_main(argc, argv, &cyberspace_ops, NULL);
    fuse_running = 0;
    free(mount_point);
    mount_point = NULL;
    return ret;
}

static int is_fuse_running(void) {
    return fuse_running;
}

#endif /* HAVE_FUSE */
<#

;;; ============================================================
;;; Stat Buffer Management
;;; ============================================================

(define fuse-init-stat
  (foreign-lambda void "init_stat_buffer"))

(define (make-fuse-stat)
  "Initialize a fresh stat buffer."
  (fuse-init-stat))

(define fuse-stat-mode-set!
  (foreign-lambda void "set_stat_mode" int))

(define fuse-stat-nlink-set!
  (foreign-lambda void "set_stat_nlink" int))

(define fuse-stat-size-set!
  (foreign-lambda void "set_stat_size" integer64))

(define fuse-stat-uid-set!
  (foreign-lambda void "set_stat_uid" int))

(define fuse-stat-gid-set!
  (foreign-lambda void "set_stat_gid" int))

(define fuse-stat-atime-set!
  (foreign-lambda void "set_stat_atime" integer64))

(define fuse-stat-mtime-set!
  (foreign-lambda void "set_stat_mtime" integer64))

(define fuse-stat-ctime-set!
  (foreign-lambda void "set_stat_ctime" integer64))

;;; ============================================================
;;; Callback Registration (Scheme-side storage)
;;; ============================================================

;; Scheme-side callback storage
(define *fuse-getattr-callback* #f)
(define *fuse-readdir-callback* #f)
(define *fuse-open-callback* #f)
(define *fuse-read-callback* #f)
(define *fuse-write-callback* #f)
(define *fuse-create-callback* #f)
(define *fuse-unlink-callback* #f)
(define *fuse-mkdir-callback* #f)
(define *fuse-rmdir-callback* #f)
(define *fuse-rename-callback* #f)
(define *fuse-truncate-callback* #f)
(define *fuse-setxattr-callback* #f)
(define *fuse-getxattr-callback* #f)
(define *fuse-listxattr-callback* #f)
(define *fuse-removexattr-callback* #f)

(define (fuse-set-getattr! proc)
  "Set getattr callback. proc: (path) -> stat-alist or #f"
  (set! *fuse-getattr-callback* proc))

(define (fuse-set-readdir! proc)
  "Set readdir callback. proc: (path) -> list of names or #f"
  (set! *fuse-readdir-callback* proc))

(define (fuse-set-open! proc)
  "Set open callback. proc: (path flags) -> #t or error-code"
  (set! *fuse-open-callback* proc))

(define (fuse-set-read! proc)
  "Set read callback. proc: (path size offset) -> blob or error-code"
  (set! *fuse-read-callback* proc))

(define (fuse-set-write! proc)
  "Set write callback. proc: (path data offset) -> bytes-written or error-code"
  (set! *fuse-write-callback* proc))

(define (fuse-set-create! proc)
  "Set create callback. proc: (path mode) -> #t or error-code"
  (set! *fuse-create-callback* proc))

(define (fuse-set-unlink! proc)
  "Set unlink callback. proc: (path) -> #t or error-code"
  (set! *fuse-unlink-callback* proc))

(define (fuse-set-mkdir! proc)
  "Set mkdir callback. proc: (path mode) -> #t or error-code"
  (set! *fuse-mkdir-callback* proc))

(define (fuse-set-rmdir! proc)
  "Set rmdir callback. proc: (path) -> #t or error-code"
  (set! *fuse-rmdir-callback* proc))

(define (fuse-set-rename! proc)
  "Set rename callback. proc: (from to) -> #t or error-code"
  (set! *fuse-rename-callback* proc))

(define (fuse-set-truncate! proc)
  "Set truncate callback. proc: (path size) -> #t or error-code"
  (set! *fuse-truncate-callback* proc))

(define (fuse-set-setxattr! proc)
  "Set setxattr callback. proc: (path name value flags) -> #t or error-code"
  (set! *fuse-setxattr-callback* proc))

(define (fuse-set-getxattr! proc)
  "Set getxattr callback. proc: (path name) -> blob or error-code"
  (set! *fuse-getxattr-callback* proc))

(define (fuse-set-listxattr! proc)
  "Set listxattr callback. proc: (path) -> list of names or error-code"
  (set! *fuse-listxattr-callback* proc))

(define (fuse-set-removexattr! proc)
  "Set removexattr callback. proc: (path name) -> #t or error-code"
  (set! *fuse-removexattr-callback* proc))

;;; ============================================================
;;; Initialization
;;; ============================================================

(define *fuse-initialized* #f)

(define (fuse-init)
  "Initialize FUSE subsystem. Returns #t on success, #f if FUSE unavailable."
  (if (fuse-available?)
      (begin
        (set! *fuse-initialized* #t)
        #t)
      #f))

;;; ============================================================
;;; Mount/Unmount (High-level interface)
;;; ============================================================

;; Note: Full FUSE integration requires running fuse_main in a separate
;; thread and using CHICKEN's callback mechanism for the operation
;; dispatch. This is a simplified interface that documents the API.

;; FFI bindings for run_fuse
(define %run-fuse
  (foreign-lambda int "run_fuse" c-string))

(define %fuse-running?
  (foreign-lambda int "is_fuse_running"))

(define (fuse-mount mountpoint #!key
                    (foreground #t)
                    (debug #f)
                    (allow-other #f))
  "Mount FUSE filesystem at mountpoint.
   WARNING: This blocks until unmounted! Run in separate process for production.
   Returns exit code (0 = success)."
  (unless *fuse-initialized*
    (unless (fuse-init)
      (error 'fuse-mount "FUSE not available. Install with: brew install fuse-t")))

  ;; Create mountpoint if needed
  (unless (file-exists? mountpoint)
    (create-directory mountpoint #t))

  (printf "Mounting FUSE filesystem at ~a~n" mountpoint)
  (printf "  (Ctrl-C to unmount, or `umount ~a` from another terminal)~n" mountpoint)

  ;; This blocks!
  (%run-fuse mountpoint))

(define (fuse-unmount mountpoint)
  "Unmount FUSE filesystem."
  ;; Use diskutil or umount
  (zero? (system (sprintf "umount ~a 2>/dev/null || diskutil unmount ~a 2>/dev/null"
                          mountpoint mountpoint))))

(define (fuse-loop)
  "Run FUSE event loop. Blocks until filesystem is unmounted."
  ;; This would call fuse_loop() in full implementation
  (error 'fuse-loop "FUSE loop requires threading integration"))

(define (fuse-exit)
  "Signal FUSE to exit."
  ;; This would call fuse_exit() in full implementation
  #t)

) ;; end module
