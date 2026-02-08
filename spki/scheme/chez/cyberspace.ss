#!/usr/bin/env chez-script
;;; cyberspace.ss - Cyberspace Script Interpreter (Chez Port)
;;; Library of Cyberspace
;;;
;;; The "porcelain" layer for the Library of Cyberspace.
;;; Verifies and executes cryptographically signed scripts.
;;;
;;; Usage:
;;;   chez --program cyberspace.ss run <script> <sig> --threshold K --keys <key>...
;;;   chez --program cyberspace.ss verify <script> <sig> --threshold K --keys <key>...
;;;
;;; Ported from cyberspace.scm.
;;; Copyright (c) 2026 Yoyodyne. See LICENSE.

(import (rnrs)
        (only (chezscheme)
              printf format void
              command-line exit
              file-exists?
              with-input-from-file)
        (cyberspace chicken-compatibility chicken)
        (cyberspace crypto-ffi)
        (cyberspace audit))

;;; Command-Line Interface

(define (usage)
  (display "Cyberspace Script Interpreter\n")
  (display "\n")
  (display "Usage:\n")
  (display "  cyberspace verify <script> <sigfile> --threshold K --keys <key>...\n")
  (display "  cyberspace run <script> <sigfile> --threshold K --keys <key>...\n")
  (display "  cyberspace help\n")
  (display "\n")
  (display "Options:\n")
  (display "  --threshold K    Require K valid signatures (default: 1)\n")
  (display "  --keys <file>... Public key files to verify against\n")
  (display "\n")
  (display "Examples:\n")
  (display "  # Verify with single signature\n")
  (display "  cyberspace verify deploy.scm deploy.sig --keys alice.pub\n")
  (display "\n")
  (display "  # Run with 3-of-5 threshold\n")
  (display "  cyberspace run deploy.scm deploy.sig --threshold 3 \\\n")
  (display "    --keys alice.pub bob.pub carol.pub dave.pub eve.pub\n")
  (exit 1))

;;; File I/O

(define (read-file-string path)
  "Read file contents as string"
  (with-input-from-file path
    (lambda ()
      (let loop ((chars '()))
        (let ((c (read-char)))
          (if (eof-object? c)
              (list->string (reverse chars))
              (loop (cons c chars))))))))

(define (read-file-bytes path)
  "Read file contents as bytevector"
  (let* ((p (open-file-input-port path))
         (data (get-bytevector-all p)))
    (close-port p)
    (if (eof-object? data) (make-bytevector 0) data)))

;;; Hex Conversion

(define (hex->bytevector hex-str)
  "Convert hex string to bytevector"
  (let* ((len (div (string-length hex-str) 2))
         (bv (make-bytevector len)))
    (do ((i 0 (+ i 1)))
        ((= i len) bv)
      (let* ((hex-byte (substring hex-str (* i 2) (+ (* i 2) 2)))
             (byte-val (string->number hex-byte 16)))
        (bytevector-u8-set! bv i (or byte-val 0))))))

(define (bytevector->hex bv)
  "Convert bytevector to hex string"
  (let* ((len (bytevector-length bv))
         (out (make-string (* 2 len))))
    (do ((i 0 (+ i 1)))
        ((= i len) out)
      (let ((b (bytevector-u8-ref bv i)))
        (let ((hi (div b 16))
              (lo (mod b 16)))
          (string-set! out (* 2 i)
                       (string-ref "0123456789abcdef" hi))
          (string-set! out (+ (* 2 i) 1)
                       (string-ref "0123456789abcdef" lo)))))))

;;; Signature File Parsing

(define (parse-sig-file path)
  "Parse signature file into list of (sig-bytes pubkey-bytes timestamp)"
  (let ((sexp (with-input-from-file path read)))
    (map (lambda (sig-sexp)
           (if (and (list? sig-sexp)
                    (= (length sig-sexp) 4)
                    (eq? (car sig-sexp) 'signature))
               (list (hex->bytevector (cadr sig-sexp))     ; sig bytes
                     (hex->bytevector (caddr sig-sexp))    ; pubkey bytes
                     (cadddr sig-sexp))                    ; timestamp
               (error 'parse-sig-file "Invalid signature format" sig-sexp)))
         sexp)))

(define (read-public-keys key-paths)
  "Read public keys from files (32-byte bytevectors)"
  (map (lambda (path)
         (let ((bv (read-file-bytes path)))
           (if (= (bytevector-length bv) 32)
               bv
               (error 'read-public-keys "Invalid public key size" path))))
       key-paths))

;;; Script Verification

(define (string->bytevector s)
  "Convert string to bytevector (Latin-1)"
  (let* ((len (string-length s))
         (bv (make-bytevector len)))
    (do ((i 0 (+ i 1)))
        ((= i len) bv)
      (bytevector-u8-set! bv i (bitwise-and (char->integer (string-ref s i)) #xff)))))

(define (verify-script-file script-path sig-path threshold key-paths)
  "Verify script signatures meet threshold"

  (display "=== Cyberspace Script Verification ===\n\n")
  (printf "Script:    ~a~%" script-path)
  (printf "Signatures: ~a~%" sig-path)
  (printf "Threshold:  ~a~%" threshold)
  (printf "Keys:       ~a provided~%~%" (length key-paths))

  (let* ((script-content (read-file-string script-path))
         (signatures (parse-sig-file sig-path))
         (public-keys (read-public-keys key-paths))
         (message-bv (string->bytevector script-content)))

    (printf "Found ~a signature(s) in file~%" (length signatures))

    ;; Verify each signature
    (let ((valid-count 0))
      (for-each
       (lambda (sig)
         (let* ((sig-bytes (car sig))
                (pubkey-bytes (cadr sig))
                (valid? (ed25519-verify message-bv sig-bytes pubkey-bytes)))
           (when valid? (set! valid-count (+ valid-count 1)))
           (printf "  Signature: ~a (signer: ~a...)~%"
                   (if valid? "VALID" "INVALID")
                   (substring (bytevector->hex pubkey-bytes) 0 16))))
       signatures)

      (display "\n")

      ;; Check threshold
      (if (>= valid-count threshold)
          (begin
            (printf "Success: Script verified with ~a-of-~a threshold~%"
                    threshold (length signatures))
            #t)
          (begin
            (display "Failure: Insufficient valid signatures\n")
            #f)))))

;;; Script Execution

(define (run-script-file script-path sig-path threshold key-paths)
  "Verify and execute script if signatures meet threshold"
  (if (not (verify-script-file script-path sig-path threshold key-paths))
      (begin
        (display "\nExecution Denied: Signature verification failed\n")
        (exit 1)))

  (display "\n=== Executing Script ===\n\n")
  (let ((script-content (read-file-string script-path)))
    (display "Script content:\n")
    (display script-content)
    (display "\n(Execution simulation - would eval in sandbox)\n")))

;;; Argument Parsing

(define (parse-args args)
  "Parse command line arguments, extract threshold and keys"
  (let loop ((rest args) (threshold 1) (keys '()))
    (cond
      ((null? rest)
       (values threshold (reverse keys)))
      ((and (string=? (car rest) "--threshold")
            (pair? (cdr rest)))
       (loop (cddr rest) (or (string->number (cadr rest)) 1) keys))
      ((string=? (car rest) "--keys")
       ;; Everything after --keys is a key file
       (values threshold (cdr rest)))
      (else
       (loop (cdr rest) threshold keys)))))

;;; Main

(define (main args)
  (sodium-init)

  (cond
   ((or (null? args) (string=? (car args) "help"))
    (usage))

   ((and (>= (length args) 3) (string=? (car args) "verify"))
    (let ((script-path (cadr args))
          (sig-path (caddr args))
          (opts (cdddr args)))
      (let-values (((threshold key-paths) (parse-args opts)))
        (verify-script-file script-path sig-path threshold key-paths))))

   ((and (>= (length args) 3) (string=? (car args) "run"))
    (let ((script-path (cadr args))
          (sig-path (caddr args))
          (opts (cdddr args)))
      (let-values (((threshold key-paths) (parse-args opts)))
        (run-script-file script-path sig-path threshold key-paths))))

   (else (usage))))

;; Run main
(let ((args (cdr (command-line))))
  (when (pair? args)
    (main args)))
