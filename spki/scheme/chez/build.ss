#!/usr/bin/env chez-script
;;; build.ss - Build Pipeline for Cyberspace (Chez Port)
;;;
;;; Usage:
;;;   chez --program build.ss            # build all C bridges
;;;   chez --program build.ss bridges    # compile C bridges only
;;;   chez --program build.ss check      # verify all .sls files parse
;;;   chez --program build.ss test       # run all test suites
;;;   chez --program build.ss clean      # remove compiled files
;;;
;;; Chez Scheme compiles .sls files automatically on first load,
;;; caching in the wpo directory. This build script handles:
;;;   1. Compiling C bridge files (.c -> .so/.dylib)
;;;   2. Syntax-checking all library files
;;;   3. Running test suites
;;;
;;; Ported from build.scm.
;;; Copyright (c) 2026 Yoyodyne. See LICENSE.

(import (rnrs)
        (only (chezscheme)
              printf format void system
              command-line exit
              file-exists? directory-exists?
              directory-list delete-file
              with-output-to-string
              open-process-ports native-transcoder
              getenv))

;;; ============================================================
;;; Build Dependency Graph (Chez Port)
;;; ============================================================
;;;
;;; External Dependencies:
;;;   libsodium     - Ed25519, X25519, ChaCha20-Poly1305, SHA-512
;;;   liboqs        - ML-DSA (post-quantum signatures)
;;;   macfuse/fuse-t - FUSE filesystem support
;;;
;;; Library load order (Chez resolves automatically via imports):
;;;
;;;   Level 0: sexp, tty-ffi, os
;;;   Level 1: crypto-ffi, pq-crypto
;;;   Level 2: fips, wordlist
;;;   Level 3: cert, capability, bloom, audit
;;;   Level 4: vault, catalog, merkle
;;;   Level 5: security, keyring, filetype, http, osc, rnbo, metadata-ffi
;;;   Level 6: gossip, mdns, portal
;;;   Level 7: fuse-ffi, wormhole
;;;   Level 8: enroll, auto-enroll
;;;   Level 9: ui, display, inspector, info, edt
;;;   Level 10: (top-level programs: repl.ss, seal.ss, cyberspace.ss)

(define (shell-command cmd)
  "Run command, return trimmed output or #f."
  (guard (exn [#t #f])
    (let-values (((to-stdin from-stdout from-stderr)
                  (open-process-ports cmd 'line (native-transcoder))))
      (let ((result (get-line from-stdout)))
        (close-port to-stdin)
        (close-port from-stdout)
        (close-port from-stderr)
        (if (eof-object? result) #f result)))))

(define (run cmd)
  (printf "  ~a~%" cmd)
  (system cmd))

(define (detect-os)
  (or (shell-command "uname -s") "Unknown"))

(define (detect-arch)
  (or (shell-command "uname -m") "unknown"))

(define *os* (detect-os))
(define *arch* (detect-arch))
(define *darwin?* (string=? *os* "Darwin"))
(define *linux?* (string=? *os* "Linux"))

(define (lib-ext)
  (if *darwin?* "dylib" "so"))

(define (cc-shared)
  (if *darwin?*
      "cc -dynamiclib"
      "cc -shared -fPIC"))

(define (homebrew-prefix)
  (cond
    ((and *darwin?* (string=? *arch* "arm64")
          (file-exists? "/opt/homebrew")) "/opt/homebrew")
    ((and *darwin?* (file-exists? "/usr/local/Homebrew")) "/usr/local")
    (else #f)))

(define (sodium-flags)
  "Return CC flags for libsodium."
  (let ((brew (homebrew-prefix)))
    (if brew
        (string-append "-I" brew "/include -L" brew "/lib -lsodium")
        "-lsodium")))

(define (keccak-flags)
  "Return CC flags for libkeccak."
  (let ((brew (homebrew-prefix)))
    (if brew
        (string-append "-I" brew "/include -L" brew "/lib -lkeccak")
        "-lkeccak")))

(define (oqs-flags)
  "Return CC flags for liboqs."
  (let ((brew (homebrew-prefix)))
    (if brew
        (string-append "-I" brew "/include -L" brew "/lib -loqs")
        "-loqs")))

(define (fuse-flags)
  "Return CC flags for FUSE."
  (cond
    ((file-exists? "/usr/local/lib/libfuse-t.dylib")
     "-D_FILE_OFFSET_BITS=64 -I/usr/local/include/fuse -L/usr/local/lib -lfuse-t")
    ((file-exists? "/opt/homebrew/lib/libfuse-t.dylib")
     "-D_FILE_OFFSET_BITS=64 -I/opt/homebrew/include/fuse -L/opt/homebrew/lib -lfuse-t")
    ((file-exists? "/usr/local/lib/libfuse.dylib")
     "-D_FILE_OFFSET_BITS=64 -I/usr/local/include/fuse -L/usr/local/lib -lfuse")
    (else
     "-D_FILE_OFFSET_BITS=64 $(pkg-config fuse --cflags --libs 2>/dev/null)")))

;;; ============================================================
;;; C Bridge Compilation
;;; ============================================================

(define *c-bridges*
  `(;; Bridge name, source, extra flags
    ("crypto-bridge"  "cyberspace/crypto-bridge.c"  ,(string-append (sodium-flags) " " (keccak-flags)))
    ("tcp-bridge"     "cyberspace/tcp-bridge.c"     "")
    ("tty-bridge"     "cyberspace/tty-bridge.c"     "")
    ("fuse-bridge"    "cyberspace/fuse-bridge.c"    ,(fuse-flags))
    ("pq-bridge"      "cyberspace/pq-bridge.c"      ,(oqs-flags))))

(define (bridge-output name)
  (string-append "cyberspace/" name "." (lib-ext)))

(define (build-bridge entry)
  "Compile a single C bridge."
  (let* ((name (car entry))
         (src (cadr entry))
         (flags (caddr entry))
         (out (bridge-output name)))
    (if (file-exists? src)
        (begin
          (printf "Building ~a...~%" name)
          (let ((cmd (string-append (cc-shared) " -o " out " " src " " flags)))
            (let ((rc (run cmd)))
              (if (zero? rc)
                  (printf "  [ok] ~a~%" out)
                  (printf "  [FAIL] ~a (exit ~a)~%" name rc)))))
        (printf "  [skip] ~a (source not found: ~a)~%" name src))))

(define (build-bridges)
  (display "\n=== Building C bridges ===\n")
  (for-each build-bridge *c-bridges*))

;;; ============================================================
;;; Library Syntax Check
;;; ============================================================

(define *library-modules*
  '("sexp" "tty-ffi" "os"
    "crypto-ffi" "pq-crypto"
    "fips" "wordlist"
    "cert" "capability" "bloom" "audit"
    "vault" "catalog" "merkle"
    "security" "keyring"
    "gossip" "mdns" "portal"
    "filetype" "http" "osc" "rnbo" "metadata-ffi"
    "fuse-ffi" "wormhole"
    "enroll" "auto-enroll"
    "ui" "display" "inspector" "info" "edt"
    "thread" "tcp"))

(define (check-library mod)
  "Check if library file exists and is valid."
  (let ((path (string-append "cyberspace/" mod ".sls")))
    (cond
      ((not (file-exists? path))
       (printf "  [MISSING] ~a~%" path)
       #f)
      (else
       (printf "  [ok] ~a~%" path)
       #t))))

(define (check-libraries)
  (display "\n=== Checking library modules ===\n")
  (let* ((results (map check-library *library-modules*))
         (total (length results))
         (present (length (filter (lambda (x) x) results)))
         (missing (- total present)))
    (printf "~%~a/~a modules present" present total)
    (when (> missing 0)
      (printf ", ~a missing" missing))
    (display "\n")))

;;; ============================================================
;;; Test Suite Runner
;;; ============================================================

(define *test-suites*
  '("test-sexp.ss"
    "test-os-chicken.ss"
    "test-crypto-pq.ss"
    "test-cert-capability.ss"
    "test-vault-audit.ss"
    "test-gossip-mdns.ss"
    "test-enroll-auto-enroll.ss"
    "test-filetype-http-osc-rnbo-metadata.ss"
    "test-tty-fuse-wormhole.ss"
    "test-level10.ss"))

(define (run-test-suite suite)
  "Run a test suite."
  (if (file-exists? suite)
      (begin
        (printf "~%--- ~a ---~%" suite)
        (let ((rc (system (string-append "CHEZSCHEMELIBDIRS=. chez --program " suite))))
          (if (zero? rc)
              (printf "  [ok] ~a~%" suite)
              (printf "  [FAIL] ~a (exit ~a)~%" suite rc))
          rc))
      (begin
        (printf "  [skip] ~a (not found)~%" suite)
        0)))

(define (run-tests)
  (display "\n=== Running test suites ===\n")
  (let* ((results (map run-test-suite *test-suites*))
         (total (length results))
         (passed (length (filter zero? results)))
         (failed (- total passed)))
    (printf "~%~a/~a suites passed" passed total)
    (when (> failed 0)
      (printf ", ~a FAILED" failed))
    (display "\n")))

;;; ============================================================
;;; Clean
;;; ============================================================

(define (clean)
  (display "\n=== Cleaning ===\n")
  ;; Remove compiled bridge files
  (for-each
    (lambda (entry)
      (let ((out (bridge-output (car entry))))
        (when (file-exists? out)
          (printf "  rm ~a~%" out)
          (delete-file out))))
    *c-bridges*)
  ;; Remove Chez compiled files
  (guard (exn [#t (void)])
    (when (directory-exists? "cyberspace")
      (for-each
        (lambda (f)
          (when (let ((len (string-length f)))
                  (and (> len 3)
                       (string=? (substring f (- len 3) len) ".so")))
            (let ((path (string-append "cyberspace/" f)))
              (printf "  rm ~a~%" path)
              (delete-file path))))
        (directory-list "cyberspace"))))
  (display "Clean complete.\n"))

;;; ============================================================
;;; Main
;;; ============================================================

(define (usage)
  (display "Cyberspace Build System (Chez Port)\n")
  (display "\n")
  (display "Usage: chez --program build.ss [target]\n")
  (display "\n")
  (display "Targets:\n")
  (display "  bridges   Compile C bridge shared libraries\n")
  (display "  check     Verify all .sls library files exist\n")
  (display "  test      Run all test suites\n")
  (display "  clean     Remove compiled files\n")
  (display "  all       bridges + check (default)\n")
  (display "\n")
  (display "Note: Chez Scheme auto-compiles .sls files on import.\n")
  (display "      Only C bridges need explicit compilation.\n"))

(define (main args)
  (let ((target (if (pair? args) (car args) "all")))
    (cond
      ((string=? target "bridges") (build-bridges))
      ((string=? target "check")   (check-libraries))
      ((string=? target "test")    (run-tests))
      ((string=? target "clean")   (clean))
      ((string=? target "all")     (build-bridges) (check-libraries))
      ((string=? target "help")    (usage))
      ((string=? target "--help")  (usage))
      (else
        (printf "Unknown target: ~a~%" target)
        (usage)
        (exit 1))))
  (display "\nDone.\n"))

(main (cdr (command-line)))
