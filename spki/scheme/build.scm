#!/usr/bin/env csi -s
;;; build.scm - Build pipeline for Cyberspace
;;;
;;; Usage:
;;;   ./build.scm           # build all
;;;   ./build.scm library   # just library modules
;;;   ./build.scm repl      # just cyberspace-repl
;;;   ./build.scm app       # just Cyberspace.app
;;;
;;; ============================================================
;;; Build Dependency Graph
;;; ============================================================
;;;
;;; External Dependencies (Homebrew):
;;;   libsodium     - Ed25519, X25519, ChaCha20-Poly1305, SHA-512
;;;   liboqs        - ML-DSA (post-quantum signatures)
;;;   macfuse       - FUSE filesystem support (optional)
;;;
;;; Module Dependency DAG:
;;;
;;;   Level 0 (no deps):
;;;     sexp           S-expression parsing/printing
;;;     tty-ffi        Terminal raw mode, cursor control
;;;     wordlist       BIP-39 mnemonic wordlists
;;;     fips           FIPS mode detection
;;;     filetype       File type detection (magic bytes)
;;;
;;;   Level 1 (core crypto):
;;;     crypto-ffi     libsodium FFI (depends: libsodium)
;;;     pq-crypto      liboqs FFI (depends: liboqs)
;;;
;;;   Level 2 (SPKI primitives):
;;;     cert           SPKI certificates (depends: sexp, crypto-ffi)
;;;     capability     Object capabilities (depends: sexp)
;;;     bloom          Bloom filters (depends: crypto-ffi)
;;;
;;;   Level 3 (storage):
;;;     vault          Encrypted vault (depends: crypto-ffi, sexp, bloom)
;;;     audit          Audit trail (depends: crypto-ffi, sexp)
;;;     merkle         Merkle trees (depends: crypto-ffi)
;;;     catalog        Content catalog (depends: vault, sexp)
;;;
;;;   Level 4 (security):
;;;     security       Security policy (depends: cert, capability)
;;;     keyring        Key management (depends: crypto-ffi, vault)
;;;
;;;   Level 5 (network):
;;;     gossip         Gossip protocol (depends: crypto-ffi, sexp)
;;;     mdns           mDNS discovery (depends: sexp)
;;;     portal         NAT traversal (depends: crypto-ffi)
;;;
;;;   Level 6 (filesystem):
;;;     fuse-ffi       FUSE FFI (depends: macfuse, optional)
;;;     wormhole       FUSE filesystem (depends: fuse-ffi, vault)
;;;
;;;   Level 7 (enrollment):
;;;     enroll         Device enrollment (depends: crypto-ffi, keyring)
;;;     auto-enroll    Auto-enrollment (depends: enroll, mdns)
;;;
;;;   Level 8 (UI):
;;;     os             Platform detection
;;;     ui             User interface (depends: os)
;;;     display        Terminal display (depends: tty-ffi)
;;;     edt            EDT keypad bindings
;;;     inspector      Object inspector (depends: sexp)
;;;     info           System info display (depends: os)
;;;
;;;   Level 9 (applications):
;;;     forum          Message board (depends: vault, gossip)
;;;     seal           Archival sealing (depends: vault, crypto-ffi)
;;;     script         Scripting (depends: sexp)
;;;     forge          Password generation (depends: crypto-ffi)
;;;     cyberspace     Top-level API (depends: everything)
;;;
;;; Build Order:
;;;   Modules are listed in *library-modules* in dependency order.
;;;   A module may only depend on modules listed before it.
;;;
;;; ============================================================

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
  '(;; Core (no deps)
    "sexp" "fips" "wordlist" "tty-ffi" "filetype"
    ;; Crypto (external: libsodium, liboqs)
    "crypto-ffi" "pq-crypto"
    ;; SPKI primitives
    "cert" "capability" "bloom"
    ;; Storage
    "vault" "catalog" "audit" "merkle"
    ;; Security
    "security" "keyring"
    ;; Network
    "gossip" "mdns" "portal" "http"
    ;; Wormhole (FUSE)
    "fuse-ffi" "wormhole"
    ;; Enrollment
    "enroll" "auto-enroll"
    ;; UI
    "os" "ui" "display" "inspector" "info" "edt"
    ;; Applications
    "forum" "seal" "script" "forge" "cyberspace"))

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
               (run "csc -s -J -O2 pq-crypto.scm -C \"-I/opt/homebrew/include\" -L \"-L/opt/homebrew/lib -loqs\""))
              ((string=? mod "fuse-ffi")
               (run "csc -s -J -O2 fuse-ffi.scm -C \"-D_FILE_OFFSET_BITS=64 -I/usr/local/include/fuse\" -L \"-L/usr/local/lib -lfuse\""))
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
