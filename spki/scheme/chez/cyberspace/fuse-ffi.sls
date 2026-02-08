;;; fuse-ffi.sls - FUSE FFI Bindings for Cyberspace Wormholes (Chez Port)
;;; Library of Cyberspace
;;;
;;; Provides low-level bindings to libfuse / FUSE-T for implementing
;;; userspace filesystems. Used by wormhole.sls for vault mounts.
;;;
;;; Installation:
;;;   brew install fuse-t    # Recommended (no kernel extension)
;;;   brew install macfuse   # Alternative (requires kernel extension)
;;;
;;; Requires fuse-bridge.c compiled as shared object:
;;;   See fuse-bridge.c for compilation instructions.
;;;
;;; When the bridge is not available, provides stub implementations
;;; that report FUSE as unavailable (checked by wormhole-open).
;;;
;;; Ported from fuse-ffi.scm.
;;; Copyright (c) 2026 Yoyodyne. See LICENSE.

(library (cyberspace fuse-ffi)
  (export
    ;; Initialization
    fuse-init
    fuse-available?
    fuse-library-path

    ;; Main loop
    fuse-mount
    fuse-unmount
    fuse-loop
    fuse-exit
    fuse-set-source!

    ;; Operation callbacks (legacy, not used in passthrough mode)
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

  (import (except (rnrs) find file-exists?)
          (only (chezscheme)
                printf format void system
                load-shared-object foreign-procedure
                file-exists?
                directory-list
                getenv)
          (cyberspace chicken-compatibility chicken))

  ;; ============================================================
  ;; Library Detection
  ;; ============================================================

  (define (find-fuse-t-lib dir)
    "Find versioned libfuse-t dylib in directory."
    (guard (exn [#t #f])
      (and (file-exists? dir)
           (let ((files (directory-list dir)))
             (let loop ((fs files))
               (cond
                 ((null? fs) #f)
                 ((and (> (string-length (car fs)) 10)
                       (let ((f (car fs)))
                         (and (string=? (substring f 0 10) "libfuse-t-")
                              (let ((len (string-length f)))
                                (and (>= len 6)
                                     (string=? (substring f (- len 6) len) ".dylib"))))))
                  (string-append dir (car fs)))
                 (else (loop (cdr fs)))))))))

  (define (fuse-library-path)
    "Find the FUSE library path. Prefers FUSE-T over macFUSE."
    (cond
      ;; FUSE-T standard install location (versioned)
      ((find-fuse-t-lib "/Library/Application Support/fuse-t/lib/"))
      ;; Homebrew locations
      ((file-exists? "/usr/local/lib/libfuse-t.dylib")
       "/usr/local/lib/libfuse-t.dylib")
      ((file-exists? "/opt/homebrew/lib/libfuse-t.dylib")
       "/opt/homebrew/lib/libfuse-t.dylib")
      ;; macFUSE fallback
      ((file-exists? "/usr/local/lib/libfuse.dylib")
       "/usr/local/lib/libfuse.dylib")
      ((file-exists? "/opt/homebrew/lib/libfuse.dylib")
       "/opt/homebrew/lib/libfuse.dylib")
      ;; Linux libfuse
      ((file-exists? "/usr/lib/libfuse.so")
       "/usr/lib/libfuse.so")
      ((file-exists? "/usr/lib/x86_64-linux-gnu/libfuse.so")
       "/usr/lib/x86_64-linux-gnu/libfuse.so")
      (else #f)))

  (define (fuse-available?)
    "Check if FUSE library is available."
    (and (fuse-library-path) #t))

  ;; ============================================================
  ;; Constants
  ;; ============================================================

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

  ;; ============================================================
  ;; Bridge Loading
  ;; ============================================================

  (define *bridge-loaded* #f)

  (define (try-load-bridge)
    ;; Attempt to load fuse-bridge shared library.
    (let ((paths (list "fuse-bridge.so"
                       "fuse-bridge.dylib"
                       "./fuse-bridge.so"
                       "./fuse-bridge.dylib"
                       "cyberspace/fuse-bridge.so"
                       "cyberspace/fuse-bridge.dylib")))
      (let loop ((ps paths))
        (if (null? ps)
            #f
            (guard (exn [#t (loop (cdr ps))])
              (load-shared-object (car ps))
              #t)))))

  (define dummy (set! *bridge-loaded* (try-load-bridge)))

  ;; ============================================================
  ;; Foreign Bindings
  ;; ============================================================

  (define c-init-stat
    (if *bridge-loaded*
        (foreign-procedure "init_stat_buffer" () void)
        (lambda () (void))))

  (define c-set-stat-mode
    (if *bridge-loaded*
        (foreign-procedure "set_stat_mode" (int) void)
        (lambda (m) (void))))

  (define c-set-stat-nlink
    (if *bridge-loaded*
        (foreign-procedure "set_stat_nlink" (int) void)
        (lambda (n) (void))))

  (define c-set-stat-size
    (if *bridge-loaded*
        (foreign-procedure "set_stat_size" (long-long) void)
        (lambda (s) (void))))

  (define c-set-stat-uid
    (if *bridge-loaded*
        (foreign-procedure "set_stat_uid" (int) void)
        (lambda (u) (void))))

  (define c-set-stat-gid
    (if *bridge-loaded*
        (foreign-procedure "set_stat_gid" (int) void)
        (lambda (g) (void))))

  (define c-set-stat-atime
    (if *bridge-loaded*
        (foreign-procedure "set_stat_atime" (long-long) void)
        (lambda (t) (void))))

  (define c-set-stat-mtime
    (if *bridge-loaded*
        (foreign-procedure "set_stat_mtime" (long-long) void)
        (lambda (t) (void))))

  (define c-set-stat-ctime
    (if *bridge-loaded*
        (foreign-procedure "set_stat_ctime" (long-long) void)
        (lambda (t) (void))))

  (define c-set-source-path
    (if *bridge-loaded*
        (foreign-procedure "set_source_path" (string) void)
        (lambda (p) (void))))

  (define c-run-fuse
    (if *bridge-loaded*
        (foreign-procedure "run_fuse" (string) int)
        (lambda (m) -1)))

  (define c-fuse-running?
    (if *bridge-loaded*
        (foreign-procedure "is_fuse_running" () int)
        (lambda () 0)))

  ;; ============================================================
  ;; Stat Buffer Management
  ;; ============================================================

  (define (make-fuse-stat)
    "Initialize a fresh stat buffer."
    (c-init-stat))

  (define (fuse-stat-mode-set! mode) (c-set-stat-mode mode))
  (define (fuse-stat-nlink-set! nlink) (c-set-stat-nlink nlink))
  (define (fuse-stat-size-set! size) (c-set-stat-size size))
  (define (fuse-stat-uid-set! uid) (c-set-stat-uid uid))
  (define (fuse-stat-gid-set! gid) (c-set-stat-gid gid))
  (define (fuse-stat-atime-set! time) (c-set-stat-atime time))
  (define (fuse-stat-mtime-set! time) (c-set-stat-mtime time))
  (define (fuse-stat-ctime-set! time) (c-set-stat-ctime time))

  ;; ============================================================
  ;; Callback Registration (Scheme-side storage)
  ;; ============================================================

  ;; Scheme-side callback storage (for future in-Scheme FUSE implementation)
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

  ;; ============================================================
  ;; Passthrough Source Path
  ;; ============================================================

  (define (fuse-set-source! path)
    "Set the source directory for passthrough filesystem."
    (c-set-source-path path))

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

  ;; ============================================================
  ;; Initialization
  ;; ============================================================

  (define *fuse-initialized* #f)

  (define (fuse-init)
    "Initialize FUSE subsystem. Returns #t on success, #f if FUSE unavailable."
    (if (fuse-available?)
        (begin
          (set! *fuse-initialized* #t)
          #t)
        #f))

  ;; ============================================================
  ;; Mount/Unmount (High-level interface)
  ;; ============================================================

  (define (fuse-mount mountpoint source-path)
    "Mount FUSE passthrough filesystem.
     mountpoint: where to mount (e.g., /tmp/mywormhole)
     source-path: directory to mirror (e.g., /path/to/vault)
     WARNING: This blocks until unmounted! Run in separate process for production.
     Returns exit code (0 = success)."
    (unless *fuse-initialized*
      (unless (fuse-init)
        (error 'fuse-mount "FUSE not available. Install with: brew install fuse-t")))

    ;; Set source directory
    (fuse-set-source! source-path)

    ;; Create mountpoint if needed
    (unless (file-exists? mountpoint)
      (system (string-append "mkdir -p " mountpoint)))

    (printf "Mounting FUSE passthrough: ~a -> ~a~%" mountpoint source-path)
    (printf "  (Ctrl-C to unmount, or `umount ~a` from another terminal)~%" mountpoint)

    ;; This blocks!
    (c-run-fuse mountpoint))

  (define (fuse-unmount mountpoint)
    "Unmount FUSE filesystem."
    (zero? (system (string-append
                    "umount " mountpoint " 2>/dev/null || "
                    "diskutil unmount " mountpoint " 2>/dev/null"))))

  (define (fuse-loop)
    "Run FUSE event loop. Blocks until filesystem is unmounted."
    (error 'fuse-loop "FUSE loop requires threading integration"))

  (define (fuse-exit)
    "Signal FUSE to exit."
    #t)

) ;; end library
