#!/usr/bin/env csi -s
;;; Cyberspace Script Interpreter
;;;
;;; The "porcelain" layer for the Library of Cyberspace.
;;; Verifies and executes cryptographically signed scripts.
;;;
;;; Philosophy:
;;;   - Scheme is the plumbing (crypto, vault, audit)
;;;   - Cyberspace is the porcelain (human-facing script execution)
;;;   - Scripts must be signed by authorized parties
;;;   - All executions are audited
;;;
;;; Usage:
;;;   cyberspace run <script-file> <sig-file> --threshold K --keys <keyfile>...
;;;   cyberspace verify <script-file> <sig-file> --threshold K --keys <keyfile>...

(import scheme
        (chicken base)
        (chicken file)
        (chicken process-context)
        (chicken format)
        (chicken blob)
        (chicken io)
        script
        crypto-ffi
        audit
        srfi-1
        srfi-4)

;;; Command-Line Interface

(define (usage)
  (print "Cyberspace Script Interpreter")
  (print "")
  (print "Usage:")
  (print "  cyberspace verify <script> <sigfile> --threshold K --keys <key>...")
  (print "  cyberspace run <script> <sigfile> --threshold K --keys <key>...")
  (print "  cyberspace help")
  (print "")
  (print "Options:")
  (print "  --threshold K    Require K valid signatures (default: 1)")
  (print "  --keys <file>... Public key files to verify against")
  (print "")
  (print "Examples:")
  (print "  # Verify with single signature")
  (print "  cyberspace verify deploy.scm deploy.sig --keys alice.pub")
  (print "")
  (print "  # Run with 3-of-5 threshold")
  (print "  cyberspace run deploy.scm deploy.sig --threshold 3 \\")
  (print "    --keys alice.pub bob.pub carol.pub dave.pub eve.pub")
  (exit 1))

;;; File I/O

(define (read-file-string path)
  "Read file contents as string"
  (with-input-from-file path
    (lambda ()
      (read-string))))

(define (read-blob-file path)
  "Read file contents as blob"
  (let ((str (call-with-input-file path
               (lambda (port)
                 (read-string #f port))
               #:binary)))
    (string->blob str)))

;;; Signature File Format
;;;
;;; S-expression format:
;;;   ((signature <hex-sig> <hex-pubkey> <timestamp>)
;;;    (signature <hex-sig> <hex-pubkey> <timestamp>)
;;;    ...)

(define (parse-sig-file path)
  "Parse signature file into list of script-signature records"
  (let ((sexp (with-input-from-file path read)))
    (map (lambda (sig-sexp)
           (if (and (list? sig-sexp)
                    (= (length sig-sexp) 4)
                    (eq? (car sig-sexp) 'signature))
               (make-script-signature
                 (hex->blob (caddr sig-sexp))   ; pubkey-hex
                 (hex->blob (cadr sig-sexp))     ; sig-hex
                 (cadddr sig-sexp))              ; timestamp
               (error "Invalid signature format" sig-sexp)))
         sexp)))

(define (hex->blob hex-str)
  "Convert hex string to blob"
  (let* ((len (quotient (string-length hex-str) 2))
         (vec (make-u8vector len)))
    (do ((i 0 (+ i 1)))
        ((= i len) (u8vector->blob vec))
      (let* ((hex-byte (substring hex-str (* i 2) (+ (* i 2) 2)))
             (byte-val (string->number hex-byte 16)))
        (u8vector-set! vec i byte-val)))))

(define (blob->hex b)
  "Convert blob to hex string"
  (define (byte->hex n)
    (let ((s (number->string n 16)))
      (if (= (string-length s) 1)
          (string-append "0" s)
          s)))
  (let ((vec (blob->u8vector b)))
    (let loop ((i 0) (acc '()))
      (if (= i (u8vector-length vec))
          (apply string-append (reverse acc))
          (loop (+ i 1)
                (cons (byte->hex (u8vector-ref vec i)) acc))))))

(define (read-public-keys key-paths)
  "Read public keys from files (32-byte blobs)"
  (map (lambda (path)
         (let ((blob (read-blob-file path)))
           (if (= (blob-size blob) 32)
               blob
               (error "Invalid public key size" path))))
       key-paths))

;;; Script Verification

(define (verify-script-file script-path sig-path threshold key-paths)
  "Verify script signatures meet threshold"

  (print "=== Cyberspace Script Verification ===\n")
  (print "Script:    " script-path)
  (print "Signatures: " sig-path)
  (print "Threshold:  " threshold)
  (print "Keys:       " (length key-paths) " provided\n")

  (let* ((script-content (read-file-string script-path))
         (signatures (parse-sig-file sig-path))
         (public-keys (read-public-keys key-paths)))

    (print "Found " (length signatures) " signature(s) in file")

    ;; Verify each signature
    (for-each
     (lambda (sig idx)
       (let ((valid? (verify-script script-content sig)))
         (print "  Signature " (+ idx 1) ": "
                (if valid? "✓ VALID" "✗ INVALID")
                " (signer: " (substring (blob->hex (signature-signer sig)) 0 16) "...)")))
     signatures
     (iota (length signatures)))

    (print "")

    ;; Check threshold
    (if (verify-threshold-script script-content signatures threshold)
        (begin
          (print "✓ SUCCESS: Script verified with " threshold "-of-" (length signatures) " threshold")
          #t)
        (begin
          (print "✗ FAILURE: Insufficient valid signatures")
          #f))))

;;; Script Execution

(define (run-script-file script-path sig-path threshold key-paths)
  "Verify and execute script if signatures meet threshold"

  ;; First verify
  (if (not (verify-script-file script-path sig-path threshold key-paths))
      (begin
        (print "\nExecution ABORTED: Signature verification failed")
        (exit 1)))

  ;; Execute
  (print "\n=== Executing Script ===\n")

  (let ((script-content (read-file-string script-path)))
    ;; For prototype: just print what would be executed
    ;; In production: would eval in sandboxed environment
    (print "Script content:")
    (print script-content)
    (print "\n(Execution simulation - would eval in sandbox)")))

;;; Main Entry Point

(define (parse-args args)
  "Parse command line arguments"
  (let* ((threshold-idx (list-index (lambda (x) (equal? x "--threshold")) args))
         (threshold (if threshold-idx
                        (string->number (list-ref args (+ threshold-idx 1)))
                        1))
         (keys-idx (list-index (lambda (x) (equal? x "--keys")) args)))
    (if (not keys-idx)
        (error "Missing --keys option")
        (let ((key-paths (drop args (+ keys-idx 1))))
          (values threshold key-paths)))))

(define (main args)
  (sodium-init)

  (cond
   ((or (null? args) (equal? (car args) "help"))
    (usage))

   ((and (>= (length args) 3) (equal? (car args) "verify"))
    (let ((script-path (cadr args))
          (sig-path (caddr args))
          (opts (cdddr args)))
      (let-values (((threshold key-paths) (parse-args opts)))
        (verify-script-file script-path sig-path threshold key-paths))))

   ((and (>= (length args) 3) (equal? (car args) "run"))
    (let ((script-path (cadr args))
          (sig-path (caddr args))
          (opts (cdddr args)))
      (let-values (((threshold key-paths) (parse-args opts)))
        (run-script-file script-path sig-path threshold key-paths))))

   (else (usage))))

;; Run if invoked as script
(when (and (> (length (command-line-arguments)) 0)
           (member (car (command-line-arguments)) '("help" "verify" "run")))
  (main (command-line-arguments)))
