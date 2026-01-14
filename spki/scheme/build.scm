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
        (chicken pathname))

(define *library-modules*
  '(;; Core
    "sexp" "crypto-ffi" "fips" "wordlist"
    ;; SPKI
    "cert" "capability" "security" "keyring"
    ;; Storage
    "vault" "catalog" "bloom" "audit"
    ;; Network
    "gossip" "mdns" "portal"
    ;; Enrollment
    "enroll" "auto-enroll"
    ;; UI
    "os" "ui" "display" "inspector"
    ;; High-level
    "board" "seal" "script" "cyberspace"))

(define (run cmd)
  (printf "  ~a~n" cmd)
  (system cmd))

(define (build-library)
  (print "\n=== Building library modules ===")
  (for-each
    (lambda (mod)
      (let ((src (string-append mod ".scm")))
        (when (file-exists? src)
          (printf "~a.so~n" mod)
          ;; crypto-ffi needs libsodium flags
          (if (string=? mod "crypto-ffi")
              (run "csc -s -J -O2 crypto-ffi.scm -C \"`pkg-config --cflags libsodium`\" -L \"`pkg-config --libs libsodium`\"")
              (run (sprintf "csc -s -J -O2 ~a" src))))))
    *library-modules*))

(define (build-repl)
  (print "\n=== Building cyberspace-repl ===")
  (run "csc -O2 -d1 cyberspace-repl.scm -o cyberspace-repl"))

(define (build-app)
  (print "\n=== Building Cyberspace.app ===")
  (let ((app-dir (make-pathname (current-directory) "app")))
    (run (sprintf "cd ~a && ./build.sh" app-dir))))

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
