;;; fuse-ffi.sls - FUSE FFI Bindings for Cyberspace Wormholes (Memo-042)
;;;
;;; Provides low-level bindings to libfuse / FUSE-T for implementing
;;; userspace filesystems. Used by wormhole.sls for vault mounts.
;;;
;;; The FUSE passthrough mode runs entirely in C for performance.
;;; Build: cc -shared -o libfuse-bridge.dylib fuse-bridge.c -lfuse-t
;;;
;;; Note: If FUSE-T is not installed, the module loads but operations
;;; return errors. Check (fuse-available?) before calling mount.

(library (cyberspace fuse-ffi)
  (export
    fuse-init fuse-available? fuse-library-path
    fuse-mount fuse-unmount fuse-loop fuse-exit
    fuse-set-source!
    ;; Callback setters (legacy, for future Scheme-level ops)
    fuse-set-getattr! fuse-set-readdir! fuse-set-open!
    fuse-set-read! fuse-set-write! fuse-set-create!
    fuse-set-unlink! fuse-set-mkdir! fuse-set-rmdir!
    fuse-set-rename! fuse-set-truncate!
    fuse-set-setxattr! fuse-set-getxattr!
    fuse-set-listxattr! fuse-set-removexattr!
    ;; Stat helpers
    make-fuse-stat fuse-stat-mode-set! fuse-stat-nlink-set!
    fuse-stat-size-set! fuse-stat-uid-set! fuse-stat-gid-set!
    fuse-stat-atime-set! fuse-stat-mtime-set! fuse-stat-ctime-set!
    ;; Constants
    S_IFDIR S_IFREG S_IFLNK
    O_RDONLY O_WRONLY O_RDWR O_CREAT O_TRUNC
    ENOENT EACCES EIO EEXIST ENOTDIR EISDIR ENOTEMPTY)

  (import (rnrs)
          (only (chezscheme)
                printf format system
                file-directory? mkdir
                load-shared-object foreign-procedure))

  ;; ============================================================
  ;; Library Detection
  ;; ============================================================

  (define (fuse-library-path)
    (cond
      ((file-exists? "/usr/local/lib/libfuse-t.dylib") "/usr/local/lib/libfuse-t.dylib")
      ((file-exists? "/opt/homebrew/lib/libfuse-t.dylib") "/opt/homebrew/lib/libfuse-t.dylib")
      ((file-exists? "/usr/local/lib/libfuse.dylib") "/usr/local/lib/libfuse.dylib")
      ((file-exists? "/opt/homebrew/lib/libfuse.dylib") "/opt/homebrew/lib/libfuse.dylib")
      (else #f)))

  ;; Try to load fuse-bridge shared library
  (define *fuse-bridge-loaded*
    (let loop ((paths '("./libfuse-bridge.dylib"
                        "../libfuse-bridge.dylib"
                        "libfuse-bridge.dylib"
                        "./libfuse-bridge.so"
                        "../libfuse-bridge.so"
                        "libfuse-bridge.so")))
      (if (null? paths)
          #f
          (guard (exn [#t (loop (cdr paths))])
            (load-shared-object (car paths))
            #t))))

  (define (fuse-available?) (and *fuse-bridge-loaded* (fuse-library-path) #t))

  ;; ============================================================
  ;; Constants
  ;; ============================================================

  (define S_IFDIR  #o0040000)
  (define S_IFREG  #o0100000)
  (define S_IFLNK  #o0120000)
  (define O_RDONLY 0)
  (define O_WRONLY 1)
  (define O_RDWR   2)
  (define O_CREAT  #x0200)
  (define O_TRUNC  #x0400)
  (define ENOENT   2)
  (define EACCES  13)
  (define EIO      5)
  (define EEXIST  17)
  (define ENOTDIR 20)
  (define EISDIR  21)
  (define ENOTEMPTY 66)

  ;; ============================================================
  ;; Foreign Procedures (deferred, only if bridge loaded)
  ;; ============================================================

  (define-syntax define-fuse-foreign
    (syntax-rules ()
      [(_ name expr)
       (define name
         (if *fuse-bridge-loaded*
             expr
             (lambda args
               (error 'fuse-ffi "FUSE bridge not loaded -- build libfuse-bridge"))))]))

  (define-fuse-foreign %set-source-path
    (foreign-procedure "fuse_set_source_path" (string) void))

  (define-fuse-foreign %run-fuse
    (foreign-procedure "fuse_run_mount" (string) int))

  (define-fuse-foreign %fuse-running
    (foreign-procedure "fuse_is_running" () int))

  (define-fuse-foreign %init-stat
    (foreign-procedure "fuse_init_stat_buffer" () void))

  (define-fuse-foreign %set-stat-mode
    (foreign-procedure "fuse_set_stat_mode" (int) void))

  (define-fuse-foreign %set-stat-nlink
    (foreign-procedure "fuse_set_stat_nlink" (int) void))

  (define-fuse-foreign %set-stat-size
    (foreign-procedure "fuse_set_stat_size" (long) void))

  (define-fuse-foreign %set-stat-uid
    (foreign-procedure "fuse_set_stat_uid" (int) void))

  (define-fuse-foreign %set-stat-gid
    (foreign-procedure "fuse_set_stat_gid" (int) void))

  (define-fuse-foreign %set-stat-atime
    (foreign-procedure "fuse_set_stat_atime" (long) void))

  (define-fuse-foreign %set-stat-mtime
    (foreign-procedure "fuse_set_stat_mtime" (long) void))

  (define-fuse-foreign %set-stat-ctime
    (foreign-procedure "fuse_set_stat_ctime" (long) void))

  ;; ============================================================
  ;; Scheme API
  ;; ============================================================

  (define (fuse-set-source! path) (%set-source-path path))
  (define (make-fuse-stat) (%init-stat))
  (define (fuse-stat-mode-set! v) (%set-stat-mode v))
  (define (fuse-stat-nlink-set! v) (%set-stat-nlink v))
  (define (fuse-stat-size-set! v) (%set-stat-size v))
  (define (fuse-stat-uid-set! v) (%set-stat-uid v))
  (define (fuse-stat-gid-set! v) (%set-stat-gid v))
  (define (fuse-stat-atime-set! v) (%set-stat-atime v))
  (define (fuse-stat-mtime-set! v) (%set-stat-mtime v))
  (define (fuse-stat-ctime-set! v) (%set-stat-ctime v))

  ;; Callback setters (Scheme-side storage for future use)
  (define *fuse-callbacks* '())
  (define (fuse-set-getattr! p) (set! *fuse-callbacks* (cons (cons 'getattr p) *fuse-callbacks*)))
  (define (fuse-set-readdir! p) (set! *fuse-callbacks* (cons (cons 'readdir p) *fuse-callbacks*)))
  (define (fuse-set-open! p) (set! *fuse-callbacks* (cons (cons 'open p) *fuse-callbacks*)))
  (define (fuse-set-read! p) (set! *fuse-callbacks* (cons (cons 'read p) *fuse-callbacks*)))
  (define (fuse-set-write! p) (set! *fuse-callbacks* (cons (cons 'write p) *fuse-callbacks*)))
  (define (fuse-set-create! p) (set! *fuse-callbacks* (cons (cons 'create p) *fuse-callbacks*)))
  (define (fuse-set-unlink! p) (set! *fuse-callbacks* (cons (cons 'unlink p) *fuse-callbacks*)))
  (define (fuse-set-mkdir! p) (set! *fuse-callbacks* (cons (cons 'mkdir p) *fuse-callbacks*)))
  (define (fuse-set-rmdir! p) (set! *fuse-callbacks* (cons (cons 'rmdir p) *fuse-callbacks*)))
  (define (fuse-set-rename! p) (set! *fuse-callbacks* (cons (cons 'rename p) *fuse-callbacks*)))
  (define (fuse-set-truncate! p) (set! *fuse-callbacks* (cons (cons 'truncate p) *fuse-callbacks*)))
  (define (fuse-set-setxattr! p) (set! *fuse-callbacks* (cons (cons 'setxattr p) *fuse-callbacks*)))
  (define (fuse-set-getxattr! p) (set! *fuse-callbacks* (cons (cons 'getxattr p) *fuse-callbacks*)))
  (define (fuse-set-listxattr! p) (set! *fuse-callbacks* (cons (cons 'listxattr p) *fuse-callbacks*)))
  (define (fuse-set-removexattr! p) (set! *fuse-callbacks* (cons (cons 'removexattr p) *fuse-callbacks*)))

  ;; ============================================================
  ;; Initialization
  ;; ============================================================

  (define *fuse-initialized* #f)

  (define (fuse-init)
    (if (fuse-available?)
        (begin (set! *fuse-initialized* #t) #t)
        #f))

  ;; ============================================================
  ;; Mount/Unmount
  ;; ============================================================

  (define (directory-exists? path)
    (and (file-exists? path) (file-directory? path)))

  (define (fuse-mount mountpoint source-path)
    (unless *fuse-initialized*
      (unless (fuse-init)
        (error 'fuse-mount "FUSE not available. Install with: brew install fuse-t")))
    (fuse-set-source! source-path)
    (unless (file-exists? mountpoint)
      (mkdir mountpoint #o755))
    (printf "Mounting FUSE passthrough: ~a -> ~a~n" mountpoint source-path)
    (%run-fuse mountpoint))

  (define (fuse-unmount mountpoint)
    (zero? (system (format "umount ~a 2>/dev/null || diskutil unmount ~a 2>/dev/null"
                           mountpoint mountpoint))))

  (define (fuse-loop)
    (error 'fuse-loop "FUSE loop requires threading integration"))

  (define (fuse-exit) #t)

) ;; end library
