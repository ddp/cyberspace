#!/usr/bin/env csi -s
;;; build.scm - Build pipeline for Cyberspace
;;;
;;; Usage:
;;;   ./build.scm           # build all
;;;   ./build.scm library   # just library modules
;;;   ./build.scm repl      # just cyberspace-repl
;;;   ./build.scm app       # just Cyberspace.app

(import scheme
        (chicken base)
        (chicken process)
        (chicken process-context)
        (chicken format)
        (chicken file)
        (chicken file posix)
        (chicken pathname)
        (chicken io)
        (chicken string))

(define *library-modules*
  '(;; Core
    "sexp" "crypto-ffi" "pq-crypto" "fips" "wordlist" "tty-ffi"
    ;; SPKI
    "cert" "capability" "security" "keyring"
    ;; Storage
    "vault" "catalog" "bloom" "audit" "merkle"
    ;; Network
    "gossip" "mdns" "portal"
    ;; Wormhole (FUSE)
    "fuse-ffi" "wormhole"
    ;; Enrollment
    "enroll" "auto-enroll"
    ;; UI
    "os" "ui" "display" "inspector" "info" "edt"
    ;; High-level
    "forum" "seal" "script" "cyberspace"))

(define (run cmd)
  (printf "  ~a~n" cmd)
  (system cmd))

(define (newer? src dst)
  "True if src exists and is newer than dst (or dst doesn't exist)"
  (and (file-exists? src)
       (or (not (file-exists? dst))
           (> (file-modification-time src) (file-modification-time dst)))))

(define (build-library)
  (print "\n=== Building library modules ===")
  (let ((built 0))
    (for-each
      (lambda (mod)
        (let ((src (string-append mod ".scm"))
              (dst (string-append mod ".so")))
          (when (newer? src dst)
            (set! built (+ built 1))
            (printf "~a.so~n" mod)
            ;; crypto-ffi needs libsodium flags
            ;; pq-crypto needs liboqs flags
            (cond
              ((string=? mod "crypto-ffi")
               (run "csc -s -J -O2 crypto-ffi.scm -C \"`pkg-config --cflags libsodium`\" -L \"`pkg-config --libs libsodium`\""))
              ((string=? mod "pq-crypto")
               (run "csc -s -J -O2 pq-crypto.scm -C \"-I/opt/homebrew/include\" -L \"-L/opt/homebrew/lib -loqs -lcrypto\""))
              (else
               (run (sprintf "csc -s -J -O2 ~a" src)))))))
      *library-modules*)
    (when (zero? built)
      (print "  (all modules current)"))))

(define (build-repl)
  (print "\n=== Building repl ===")
  (if (newer? "repl.scm" "repl")
      (run "csc -O2 -d1 repl.scm -o repl")
      (print "  (current)")))

(define (build-app)
  (print "\n=== Building Cyberspace.app ===")
  (let* ((app-dir (make-pathname (current-directory) "darwin/application"))
         (server-src "cyberspace-server.scm")
         (server-dst (make-pathname app-dir "Cyberspace.app/Contents/Resources/cyberspace-server"))
         (main-src (make-pathname app-dir "main.m"))
         (main-dst (make-pathname app-dir "Cyberspace.app/Contents/MacOS/Cyberspace")))
    (if (or (newer? server-src server-dst)
            (newer? main-src main-dst))
        (run (sprintf "cd ~a && ./build.sh" app-dir))
        (print "  (current)"))))

(define (build-all)
  (build-library)
  (build-repl)
  (build-app))

(define (install-eggs)
  "Install eggs from freckles manifest"
  (print "\n=== Installing eggs from freckles ===")
  (if (file-exists? "freckles")
      (let ((eggs (with-input-from-file "freckles"
                    (lambda ()
                      (let loop ((lines '()))
                        (let ((line (read-line)))
                          (if (eof-object? line)
                              (reverse lines)
                              (let ((trimmed (string-trim-both line)))
                                (if (or (string=? trimmed "")
                                        (string-prefix? ";" trimmed))
                                    (loop lines)
                                    (loop (cons trimmed lines)))))))))))
        (for-each
          (lambda (egg)
            (printf "  ~a~n" egg)
            (system (sprintf "chicken-install ~a 2>/dev/null || sudo chicken-install ~a" egg egg)))
          eggs))
      (print "  (no freckles file found)")))

(define (publish-library)
  (print "\n=== Publishing library ===")
  (let ((dest "www.yoyodyne.com:ddp/cyberspace/spki/scheme/"))
    ;; Publish .so modules and import files
    (run (sprintf "rsync -avz --include='*.so' --include='*.import.scm' --exclude='*' . ~a" dest))
    ;; Publish source for reference
    (for-each
      (lambda (mod)
        (let ((src (string-append mod ".scm")))
          (when (file-exists? src)
            (run (sprintf "rsync -avz ~a ~a" src dest)))))
      *library-modules*)))

(define (main args)
  (let ((target (if (pair? args) (car args) "all")))
    (cond
      ((string=? target "eggs")    (install-eggs))
      ((string=? target "library") (build-library))
      ((string=? target "repl")    (build-repl))
      ((string=? target "app")     (build-app))
      ((string=? target "all")     (build-all))
      ((string=? target "publish") (publish-library))
      (else
        (printf "Unknown target: ~a~n" target)
        (print "Usage: ./build.scm [eggs|library|repl|app|all|publish]")
        (exit 1))))
  (print "\nDone."))

(main (command-line-arguments))
