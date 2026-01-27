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
;;;   Level 0 (no cyberspace deps):
;;;     sexp           S-expression parsing/printing
;;;     tty-ffi        Terminal raw mode, cursor control
;;;     filetype       File type detection (magic bytes)
;;;     os             Platform detection (chicken modules only)
;;;
;;;   Level 1 (core crypto):
;;;     crypto-ffi     libsodium FFI (depends: libsodium)
;;;     pq-crypto      liboqs FFI (depends: liboqs)
;;;
;;;   Level 2 (crypto-dependent utilities):
;;;     fips           FIPS self-test (depends: crypto-ffi)
;;;     wordlist       BIP-39 mnemonic wordlists (depends: crypto-ffi)
;;;
;;;   Level 3 (SPKI primitives + audit):
;;;     cert           SPKI certificates (depends: sexp, crypto-ffi)
;;;     capability     Object capabilities (depends: sexp)
;;;     bloom          Bloom filters (depends: crypto-ffi)
;;;     audit          Audit trail (depends: crypto-ffi, pq-crypto)
;;;
;;;   Level 4 (storage):
;;;     vault          Encrypted vault (depends: crypto-ffi, cert, audit, os)
;;;     catalog        Content catalog (depends: vault, sexp)
;;;     merkle         Merkle trees (depends: crypto-ffi)
;;;
;;;   Level 5 (security):
;;;     security       Security policy (depends: cert, capability)
;;;     keyring        Key management (depends: crypto-ffi, vault)
;;;
;;;   Level 6 (network):
;;;     gossip         Gossip protocol (depends: crypto-ffi, sexp)
;;;     mdns           mDNS discovery (depends: sexp)
;;;     portal         NAT traversal (depends: crypto-ffi)
;;;
;;;   Level 7 (filesystem):
;;;     metadata-ffi   macOS metadata FFI
;;;     fuse-ffi       FUSE FFI (depends: macfuse, optional)
;;;     wormhole       FUSE filesystem (depends: fuse-ffi, vault)
;;;
;;;   Level 8 (enrollment):
;;;     enroll         Device enrollment (depends: crypto-ffi, keyring, wordlist)
;;;     auto-enroll    Auto-enrollment (depends: enroll, mdns)
;;;
;;;   Level 9 (UI):
;;;     ui             User interface (depends: os, enroll)
;;;     display        Terminal display (depends: tty-ffi)
;;;     inspector      Object inspector (depends: sexp)
;;;     info           System info display (depends: os)
;;;     edt            EDT keypad bindings
;;;
;;;   Level 10 (applications):
;;;     forum          Message board (depends: vault, gossip)
;;;     seal           Archival sealing (depends: vault, crypto-ffi)
;;;     script         Scripting (depends: sexp)
;;;     forge          Password generation (depends: crypto-ffi, fips)
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
  '(;; Level 0: Core (no cyberspace deps)
    "sexp" "tty-ffi" "filetype" "os"
    ;; Level 1: Crypto (external: libsodium, liboqs)
    "crypto-ffi" "pq-crypto"
    ;; Level 2: Crypto-dependent utilities
    "fips" "wordlist"
    ;; Level 3: SPKI primitives + audit
    "cert" "capability" "bloom" "audit"
    ;; Level 4: Storage (depends on audit, os)
    "vault" "catalog" "merkle"
    ;; Level 5: Security
    "security" "keyring"
    ;; Level 6: Network
    "gossip" "mdns" "portal" "http" "osc" "rnbo"
    ;; Level 7: Wormhole (FUSE)
    "metadata-ffi" "fuse-ffi" "wormhole"
    ;; Level 8: Enrollment
    "enroll" "auto-enroll"
    ;; Level 9: UI
    "ui" "display" "inspector" "info" "edt"
    ;; Level 10: Applications
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
               ;; libsodium via pkg-config, libkeccak from homebrew
               (run "csc -s -J -O2 crypto-ffi.scm -C \"`pkg-config --cflags libsodium` -I/opt/homebrew/include\" -L \"`pkg-config --libs libsodium` -L/opt/homebrew/lib -lkeccak\""))
              ((string=? mod "pq-crypto")
               (run "csc -s -J -O2 pq-crypto.scm -C \"-I/opt/homebrew/include\" -L \"-L/opt/homebrew/lib -loqs -L/opt/homebrew/opt/openssl@3/lib -lcrypto\""))
              ((string=? mod "fuse-ffi")
               ;; Try fuse-t first, fall back to macfuse (libfuse)
               (if (file-exists? "/usr/local/lib/libfuse-t.dylib")
                   (run "csc -s -J -O2 fuse-ffi.scm -C \"-D_FILE_OFFSET_BITS=64 -I/usr/local/include/fuse\" -L \"-L/usr/local/lib -Wl,-rpath,/usr/local/lib -lfuse-t\"")
                   (run "csc -s -J -O2 fuse-ffi.scm -C \"-D_FILE_OFFSET_BITS=64 -I/usr/local/include/fuse\" -L \"-L/usr/local/lib -Wl,-rpath,/usr/local/lib -lfuse\"")))
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
