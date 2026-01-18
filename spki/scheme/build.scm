#!/usr/bin/env csi -s
;;; build.scm - Build pipeline for Cyberspace
;;;
;;; Usage:
;;;   ./build.scm           # build all
;;;   ./build.scm library   # just library modules
;;;   ./build.scm repl      # just repl
;;;   ./build.scm app       # just Cyberspace.app

(import scheme
        (chicken base)
        (chicken process)
        (chicken process-context)
        (chicken format)
        (chicken file)
        (chicken file posix)
        (chicken pathname))

(define *library-modules*
  '(;; Layer 0: No internal dependencies
    "sexp" "crypto-ffi" "fips" "wordlist"
    "display" "inspector" "catalog" "bloom" "os"
    "smelter" "scrutinizer" "board"
    ;; Layer 1: Single deps
    "cert"          ; needs sexp
    "script"        ; needs cert
    "capability"    ; no internal deps
    "keyring"       ; needs display
    "audit"         ; needs crypto-ffi
    "forge"         ; needs smelter
    ;; Layer 2
    "security"      ; needs cert, capability, sexp
    ;; Layer 3
    "vault"         ; needs cert, crypto-ffi, audit, os
    "mdns"          ; needs os
    "portal"        ; needs os
    "enroll"        ; needs crypto-ffi, wordlist
    ;; Layer 4
    "seal"          ; needs vault
    "gossip"        ; needs bloom, catalog, crypto-ffi, os
    ;; Layer 5
    "auto-enroll"   ; needs enroll, capability, mdns, gossip, crypto-ffi
    ;; Layer 6
    "ui"            ; needs enroll, capability, auto-enroll
    ;; Layer 7
    "cyberspace"))  ; needs script

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
            (if (string=? mod "crypto-ffi")
                (run "csc -s -J -O2 crypto-ffi.scm -C \"`pkg-config --cflags libsodium`\" -L \"`pkg-config --libs libsodium`\"")
                (run (sprintf "csc -s -J -O2 ~a" src))))))
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
  (let* ((app-dir (make-pathname (current-directory) "app"))
         (server-src "server.scm")
         (server-dst (make-pathname app-dir "Cyberspace.app/Contents/Resources/server"))
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

(define (publish-library)
  (print "\n=== Publishing library ===")
  (let ((dest "www.yoyodyne.com:public_html/ddp/cyberspace/spki/scheme/"))
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
      ((string=? target "library") (build-library))
      ((string=? target "repl")    (build-repl))
      ((string=? target "app")     (build-app))
      ((string=? target "all")     (build-all))
      ((string=? target "publish") (publish-library))
      (else
        (printf "Unknown target: ~a~n" target)
        (print "Usage: ./build.scm [library|repl|app|all|publish]")
        (exit 1))))
  (print "\nDone."))

(main (command-line-arguments))
