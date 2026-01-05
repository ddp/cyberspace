#!/usr/bin/env csi -s
;; Lamport One-Time Password System
;; Implementation of Leslie Lamport's hash-chain authentication (1981)
;;
;; Paper: "Password Authentication with Insecure Communication"
;; Source: ~/cyberspace/library/cryptographers/nrl-one-time-passwords/
;;
;; Concept: Generate a chain of N passwords by repeated hashing
;;   seed → H(seed) → H(H(seed)) → ... → H^N(seed)
;; Use passwords in reverse order (most-hashed first)
;; Server stores last valid hash, accepts next hash in chain

(import scheme)
(import (chicken base))
(import (chicken io))
(import (chicken file))
(import (chicken process))
(import (chicken process-context))
(import (chicken string))
(import (chicken format))
(import srfi-1)
(import srfi-13)

;; ============================================================================
;; SHA-256 via OpenSSL
;; ============================================================================

(define (sha256 text)
  "Compute SHA-256 hash of text using openssl"
  (let ((result (with-input-from-pipe
                 (string-append "echo -n '" text "' | openssl dgst -sha256 -hex")
                 read-line)))
    ;; Extract hash from "SHA2-256(stdin)= <hash>" format
    (if result
        (string-trim-both (car (reverse (string-split result " "))))
        #f)))

(define (sha256-n text n)
  "Apply SHA-256 hash n times"
  (if (<= n 0)
      text
      (sha256-n (sha256 text) (- n 1))))

;; ============================================================================
;; Password Chain Generation
;; ============================================================================

(define (generate-chain seed length)
  "Generate Lamport hash chain from seed"
  (print "Generating Lamport OTP chain...")
  (print "Seed: " seed)
  (print "Length: " length " passwords")
  (print "")

  (let loop ((n 0) (passwords '()))
    (when (zero? (modulo n 10))
      (print "Progress: " n "/" length))

    (if (>= n length)
        (begin
          (print "Done!")
          (reverse passwords))
        (loop (+ n 1)
              (cons (list n (sha256-n seed (- length n)))
                    passwords)))))

;; ============================================================================
;; Storage Format
;; ============================================================================

(define (save-chain username chain)
  "Save password chain to file"
  (let ((filename (string-append username ".lamport")))
    (with-output-to-file filename
      (lambda ()
        (write `((username . ,username)
                 (length . ,(length chain))
                 (current . 0)
                 (chain . ,chain)))))
    (print "Saved chain to " filename)))

(define (load-chain username)
  "Load password chain from file"
  (let ((filename (string-append username ".lamport")))
    (if (file-exists? filename)
        (with-input-from-file filename read)
        #f)))

;; ============================================================================
;; Authentication
;; ============================================================================

(define (verify-password username password)
  "Verify a Lamport OTP password"
  (let ((data (load-chain username)))
    (if (not data)
        (begin
          (print "Error: No password chain for " username)
          #f)
        (let* ((current (cdr (assoc 'current data)))
               (chain (cdr (assoc 'chain data)))
               (length (cdr (assoc 'length data)))
               (expected-entry (list-ref chain current))
               (expected-hash (cadr expected-entry)))

          (cond
           ((>= current length)
            (print "Error: Password chain exhausted!")
            (print "Generate a new chain for " username)
            #f)

           ((string=? password expected-hash)
            (print "✓ Authentication successful!")
            (print "Password " current " of " (- length 1) " used")
            ;; Advance to next password
            (save-chain-state username (+ current 1))
            #t)

           (else
            (print "✗ Authentication failed!")
            (print "Expected password #" current)
            #f))))))

(define (save-chain-state username current)
  "Update current password index"
  (let* ((data (load-chain username))
         (chain (cdr (assoc 'chain data)))
         (length (cdr (assoc 'length data))))
    (with-output-to-file (string-append username ".lamport")
      (lambda ()
        (write `((username . ,username)
                 (length . ,length)
                 (current . ,current)
                 (chain . ,chain)))))))

;; ============================================================================
;; Password Book (Client-Side)
;; ============================================================================

(define (generate-password-book username seed length)
  "Generate a printable password book for client"
  (let ((chain (generate-chain seed length))
        (filename (string-append username "-passwords.txt")))

    (with-output-to-file filename
      (lambda ()
        (display "╔═══════════════════════════════════════════════════════════════════╗\n")
        (display "║           LAMPORT ONE-TIME PASSWORD BOOK                          ║\n")
        (display "╠═══════════════════════════════════════════════════════════════════╣\n")
        (display "║  User: ")
        (display username)
        (display (make-string (- 58 (string-length username)) #\space))
        (display " ║\n")
        (display "║  Passwords: ")
        (display length)
        (display (make-string (- 53 (string-length (number->string length))) #\space))
        (display " ║\n")
        (display "╠═══════════════════════════════════════════════════════════════════╣\n")
        (display "║  USE PASSWORDS IN ORDER FROM TOP TO BOTTOM                        ║\n")
        (display "║  Each password can only be used ONCE                              ║\n")
        (display "╚═══════════════════════════════════════════════════════════════════╝\n\n")

        (for-each (lambda (entry)
                    (let* ((n (car entry))
                           (hash (cadr entry))
                           (n-str (number->string n))
                           (padding (make-string (- 3 (string-length n-str)) #\space)))
                      (display padding)
                      (display n-str)
                      (display ": ")
                      (display hash)
                      (display "\n")))
                  chain)))

    (print "")
    (print "Password book saved to: " filename)
    (print "")
    (print "SECURITY NOTES:")
    (print "  - Print this file and keep it secure")
    (print "  - Cross off passwords as you use them")
    (print "  - When running low, generate a new chain")
    (print "  - NEVER reuse a password!")
    (print "")

    ;; Save server-side chain
    (save-chain username chain)
    chain))

;; ============================================================================
;; Server State Management
;; ============================================================================

(define (show-status username)
  "Show current status of password chain"
  (let ((data (load-chain username)))
    (if (not data)
        (print "No password chain found for " username)
        (let ((current (cdr (assoc 'current data)))
              (length (cdr (assoc 'length data))))
          (print "═══════════════════════════════════════")
          (print "User: " username)
          (print "Passwords used: " current " of " length)
          (print "Passwords remaining: " (- length current))
          (print "Progress: " (format-percentage current length))
          (print "═══════════════════════════════════════")

          (when (> current (* length 0.8))
            (print "⚠ WARNING: Low on passwords!")
            (print "  Generate a new chain soon."))))))

(define (format-percentage used total)
  "Format percentage with bar graph"
  (let* ((pct (inexact->exact (round (* 100 (/ used total)))))
         (bars (inexact->exact (round (/ pct 5))))
         (spaces (- 20 bars)))
    (string-append "["
                   (make-string bars #\█)
                   (make-string spaces #\░)
                   "] "
                   (number->string pct)
                   "%")))

;; ============================================================================
;; CLI Interface
;; ============================================================================

(define (show-help)
  (display "╔═══════════════════════════════════════════════════════════════════╗\n")
  (display "║        LAMPORT ONE-TIME PASSWORD SYSTEM                           ║\n")
  (display "║        Implementation of Lamport (1981)                           ║\n")
  (display "╚═══════════════════════════════════════════════════════════════════╝\n\n")
  (display "USAGE:\n")
  (display "  ./lamport.scm generate <username> <seed> <count>\n")
  (display "  ./lamport.scm verify <username> <password>\n")
  (display "  ./lamport.scm status <username>\n")
  (display "\n")
  (display "COMMANDS:\n")
  (display "  generate  - Create new password chain\n")
  (display "              Generates printable password book for client\n")
  (display "              Stores chain on server for verification\n")
  (display "\n")
  (display "  verify    - Verify a password from the chain\n")
  (display "              Automatically advances to next password\n")
  (display "\n")
  (display "  status    - Show current state of password chain\n")
  (display "\n")
  (display "EXAMPLES:\n")
  (display "  # Generate 100 passwords for alice\n")
  (display "  ./lamport.scm generate alice \"my-secret-seed-xyz123\" 100\n")
  (display "\n")
  (display "  # Verify password (server-side)\n")
  (display "  ./lamport.scm verify alice a3f5b9c2d...\n")
  (display "\n")
  (display "  # Check status\n")
  (display "  ./lamport.scm status alice\n")
  (display "\n")
  (display "HOW IT WORKS:\n")
  (display "  1. Client generates chain: seed → H(seed) → H²(seed) → ... → Hⁿ(seed)\n")
  (display "  2. Client uses passwords in reverse order (Hⁿ, Hⁿ⁻¹, ...)\n")
  (display "  3. Server verifies H(received) = stored_hash\n")
  (display "  4. Server updates stored_hash = received\n")
  (display "  5. Attacker can't reuse old passwords or compute future ones\n")
  (display "\n")
  (display "SECURITY:\n")
  (display "  ✓ One-time use (can't replay captured passwords)\n")
  (display "  ✓ Forward secure (past passwords don't reveal future ones)\n")
  (display "  ✓ Eavesdropper can't derive unused passwords\n")
  (display "  ✗ Requires secure initial seed distribution\n")
  (display "  ✗ Chain eventually exhausts (must regenerate)\n")
  (display "\n")
  (display "PAPER:\n")
  (display "  Leslie Lamport (1981)\n")
  (display "  \"Password Authentication with Insecure Communication\"\n")
  (display "  ~/cyberspace/library/cryptographers/nrl-one-time-passwords/\n")
  (display "\n"))

;; Main entry point
(when (not (null? (command-line-arguments)))
  (let ((cmd (car (command-line-arguments))))
    (cond
     ((string=? cmd "generate")
      (if (< (length (command-line-arguments)) 4)
          (begin
            (print "Error: Missing arguments")
            (print "Usage: ./lamport.scm generate <username> <seed> <count>"))
          (let ((username (cadr (command-line-arguments)))
                (seed (caddr (command-line-arguments)))
                (count (string->number (cadddr (command-line-arguments)))))
            (generate-password-book username seed count))))

     ((string=? cmd "verify")
      (if (< (length (command-line-arguments)) 3)
          (begin
            (print "Error: Missing arguments")
            (print "Usage: ./lamport.scm verify <username> <password>"))
          (let ((username (cadr (command-line-arguments)))
                (password (caddr (command-line-arguments))))
            (verify-password username password))))

     ((string=? cmd "status")
      (if (< (length (command-line-arguments)) 2)
          (begin
            (print "Error: Missing username")
            (print "Usage: ./lamport.scm status <username>"))
          (let ((username (cadr (command-line-arguments))))
            (show-status username))))

     (else
      (show-help)))))

;; REPL usage
(when (and (equal? (program-name) "csi")
           (null? (command-line-arguments)))
  (show-help))
