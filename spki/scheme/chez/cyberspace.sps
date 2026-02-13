#!/usr/bin/env chez --libdirs . --script
;;; Cyberspace Script Interpreter
;;;
;;; The "porcelain" layer for the Library of Cyberspace.
;;; Verifies and executes cryptographically signed scripts.
;;;
;;; Usage:
;;;   cyberspace verify <script> <sigfile> --threshold K --keys <key>...
;;;   cyberspace run <script> <sigfile> --threshold K --keys <key>...

(import (rnrs)
        (only (chezscheme) printf format command-line exit)
        (cyberspace script)
        (cyberspace crypto-ffi)
        (cyberspace audit)
        (cyberspace chicken-compatibility blob)
        (cyberspace chicken-compatibility chicken))

;;; Command-Line Interface

(define (usage)
  (printf "Cyberspace Script Interpreter~%")
  (printf "~%")
  (printf "Usage:~%")
  (printf "  cyberspace verify <script> <sigfile> --threshold K --keys <key>...~%")
  (printf "  cyberspace run <script> <sigfile> --threshold K --keys <key>...~%")
  (printf "  cyberspace help~%")
  (printf "~%")
  (printf "Options:~%")
  (printf "  --threshold K    Require K valid signatures (default: 1)~%")
  (printf "  --keys <file>... Public key files to verify against~%")
  (printf "~%")
  (printf "Examples:~%")
  (printf "  # Verify with single signature~%")
  (printf "  cyberspace verify deploy.scm deploy.sig --keys alice.pub~%")
  (printf "~%")
  (printf "  # Run with 3-of-5 threshold~%")
  (printf "  cyberspace run deploy.scm deploy.sig --threshold 3 \\~%")
  (printf "    --keys alice.pub bob.pub carol.pub dave.pub eve.pub~%")
  (exit 1))

;;; File I/O

(define (read-file-string path)
  (call-with-input-file path
    (lambda (port) (get-string-all port))))

(define (read-blob-file path)
  (let ((bv (call-with-port
              (open-file-input-port path)
              (lambda (port) (get-bytevector-all port)))))
    bv))

;;; Hex conversion

(define (hex-char->int c)
  (cond ((and (char>=? c #\0) (char<=? c #\9))
         (- (char->integer c) (char->integer #\0)))
        ((and (char>=? c #\a) (char<=? c #\f))
         (+ 10 (- (char->integer c) (char->integer #\a))))
        ((and (char>=? c #\A) (char<=? c #\F))
         (+ 10 (- (char->integer c) (char->integer #\A))))
        (else (error 'hex-char->int "Invalid hex character" c))))

(define (hex->blob hex-str)
  (let* ((len (div (string-length hex-str) 2))
         (bv (make-bytevector len)))
    (do ((i 0 (+ i 1)))
        ((= i len) bv)
      (let ((hi (hex-char->int (string-ref hex-str (* i 2))))
            (lo (hex-char->int (string-ref hex-str (+ (* i 2) 1)))))
        (bytevector-u8-set! bv i (+ (* hi 16) lo))))))

(define (blob->hex b)
  (let* ((len (bytevector-length b)))
    (let loop ((i 0) (acc '()))
      (if (= i len)
          (apply string-append (reverse acc))
          (let* ((byte (bytevector-u8-ref b i))
                 (s (number->string byte 16))
                 (s (if (= (string-length s) 1) (string-append "0" s) s)))
            (loop (+ i 1) (cons s acc)))))))

;;; Signature File Format
;;;
;;; S-expression format:
;;;   ((signature <hex-sig> <hex-pubkey> <timestamp>)
;;;    (signature <hex-sig> <hex-pubkey> <timestamp>)
;;;    ...)

(define (parse-sig-file path)
  (let ((sexp (call-with-input-file path read)))
    (map (lambda (sig-sexp)
           (if (and (list? sig-sexp)
                    (= (length sig-sexp) 4)
                    (eq? (car sig-sexp) 'signature))
               (make-script-signature
                 (hex->blob (symbol->string (caddr sig-sexp)))
                 (hex->blob (symbol->string (cadr sig-sexp)))
                 (cadddr sig-sexp))
               (error 'parse-sig-file "Invalid signature format" sig-sexp)))
         sexp)))

(define (read-public-keys key-paths)
  (map (lambda (path)
         (let ((blob (read-blob-file path)))
           (if (= (bytevector-length blob) 32)
               blob
               (error 'read-public-keys "Invalid public key size" path))))
       key-paths))

;;; Script Verification

(define (verify-script-file script-path sig-path threshold key-paths)
  (printf "=== Cyberspace Script Verification ===~%~%")
  (printf "Script:    ~a~%" script-path)
  (printf "Signatures: ~a~%" sig-path)
  (printf "Threshold:  ~a~%" threshold)
  (printf "Keys:       ~a provided~%~%" (length key-paths))

  (let* ((script-content (read-file-string script-path))
         (signatures (parse-sig-file sig-path))
         (public-keys (read-public-keys key-paths)))

    (printf "Found ~a signature(s) in file~%" (length signatures))

    (let loop ((sigs signatures) (idx 0))
      (unless (null? sigs)
        (let* ((sig (car sigs))
               (valid? (verify-script script-content sig)))
          (printf "  Signature ~a: ~a (signer: ~a...)~%"
                  (+ idx 1)
                  (if valid? "VALID" "INVALID")
                  (substring (blob->hex (signature-signer sig)) 0 16)))
        (loop (cdr sigs) (+ idx 1))))

    (printf "~%")

    (if (verify-threshold-script script-content signatures threshold)
        (begin
          (printf "Success: Script verified with ~a-of-~a threshold~%" threshold (length signatures))
          #t)
        (begin
          (printf "Failure: Insufficient valid signatures~%")
          #f))))

;;; Script Execution

(define (run-script-file script-path sig-path threshold key-paths)
  (unless (verify-script-file script-path sig-path threshold key-paths)
    (printf "~%Execution Evaporated: Signature verification failed~%")
    (exit 1))

  (printf "~%=== Executing Script ===~%~%")
  (let ((script-content (read-file-string script-path)))
    (printf "Script content:~%")
    (printf "~a~%" script-content)
    (printf "~%(Execution simulation - would eval in sandbox)~%")))

;;; Argument Parsing

(define (string-prefix? prefix str)
  (let ((plen (string-length prefix)))
    (and (>= (string-length str) plen)
         (string=? prefix (substring str 0 plen)))))

(define (list-index pred lst)
  (let loop ((lst lst) (i 0))
    (cond
      ((null? lst) #f)
      ((pred (car lst)) i)
      (else (loop (cdr lst) (+ i 1))))))

(define (parse-args args)
  (let* ((threshold-idx (list-index (lambda (x) (equal? x "--threshold")) args))
         (threshold (if threshold-idx
                        (string->number (list-ref args (+ threshold-idx 1)))
                        1))
         (keys-idx (list-index (lambda (x) (equal? x "--keys")) args)))
    (unless keys-idx
      (error 'parse-args "Missing --keys option"))
    (let ((key-paths (let loop ((rest (list-tail args (+ keys-idx 1))) (acc '()))
                       (if (or (null? rest) (string-prefix? "--" (car rest)))
                           (reverse acc)
                           (loop (cdr rest) (cons (car rest) acc))))))
      (values threshold key-paths))))

;;; Main

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

(let ((args (cdr (command-line))))
  (if (null? args)
      (usage)
      (main args)))
