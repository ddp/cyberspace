#!/usr/bin/env csi -s
;;; refresh-library.scm - Rebuild all library modules

(import scheme
        (chicken base)
        (chicken process)
        (chicken format)
        (chicken file))

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

(print "=== Rebuilding library modules ===\n")

(for-each
  (lambda (mod)
    (let ((src (string-append mod ".scm")))
      (when (file-exists? src)
        (printf "~a.so\n" mod)
        (if (string=? mod "crypto-ffi")
            (system "csc -s -J -O2 crypto-ffi.scm -C \"`pkg-config --cflags libsodium`\" -L \"`pkg-config --libs libsodium`\"")
            (system (sprintf "csc -s -J -O2 ~a" src))))))
  *library-modules*)

(print "\nDone.")
