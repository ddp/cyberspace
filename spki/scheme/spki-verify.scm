#!/usr/bin/env csi -s
;;; spki-verify: Verify SPKI certificate chain

(import (chicken base)
        (chicken format)
        (chicken file)
        (chicken io)
        (chicken process-context)
        (chicken string)
        (chicken condition)
        sexp
        cert
        crypto-ffi)

(define (usage)
  (print "Usage: spki-verify --root KEYFILE --chain CERTFILE [--chain CERTFILE ...] --tag TAG")
  (print "Verify an SPKI certificate delegation chain.")
  (print "")
  (print "Required:")
  (print "  --root FILE         Root public key file")
  (print "  --chain FILE        Certificate file (can specify multiple)")
  (print "  --tag TAG           Tag to verify (s-expression)")
  (print "")
  (print "  --help              Show this help")
  (print "")
  (print "Example:")
  (print "  spki-verify --root alice.public \\")
  (print "              --chain alice-to-bob.cert \\")
  (print "              --chain bob-to-carol.cert \\")
  (print "              --tag '(read (path /data))'")
  (exit 0))

(define (read-key-file filename)
  "Read a public key file and return the key blob"
  (let ((content (with-input-from-file filename read-string)))
    (let ((sexp (parse-sexp content)))
      (if (and (sexp-list? sexp)
               (= 2 (length (list-items sexp))))
          (let ((items (list-items sexp)))
            (let ((type-atom (car items))
                  (key-bytes (cadr items)))
              (if (and (sexp-atom? type-atom)
                       (string=? (atom-value type-atom) "spki-public-key")
                       (sexp-bytes? key-bytes))
                  (bytes-value key-bytes)
                  (begin
                    (print "Error: Invalid public key file: " filename)
                    (exit 1)))))
          (begin
            (print "Error: Invalid public key file format: " filename)
            (exit 1))))))

(define (read-cert-file filename)
  "Read a certificate file and return signed-cert"
  (let ((content (with-input-from-file filename read-string)))
    (signed-cert-of-string content)))

(define (main args)
  ;; Initialize libsodium
  (sodium-init)

  ;; Parse arguments
  (define root-file #f)
  (define cert-files '())
  (define tag-str #f)

  (let loop ((args args))
    (cond
     ((null? args) #t)

     ((string=? (car args) "--help")
      (usage))

     ((string=? (car args) "--root")
      (if (null? (cdr args))
          (begin
            (print "Error: --root requires an argument")
            (exit 1))
          (begin
            (set! root-file (cadr args))
            (loop (cddr args)))))

     ((string=? (car args) "--chain")
      (if (null? (cdr args))
          (begin
            (print "Error: --chain requires an argument")
            (exit 1))
          (begin
            (set! cert-files (append cert-files (list (cadr args))))
            (loop (cddr args)))))

     ((string=? (car args) "--tag")
      (if (null? (cdr args))
          (begin
            (print "Error: --tag requires an argument")
            (exit 1))
          (begin
            (set! tag-str (cadr args))
            (loop (cddr args)))))

     (else
      (print "Error: Unknown argument: " (car args))
      (usage))))

  ;; Validate required arguments
  (unless (and root-file (not (null? cert-files)) tag-str)
    (print "Error: --root, --chain, and --tag are required")
    (usage))

  ;; Read root key
  (let ((root-key (read-key-file root-file)))

    ;; Read certificate chain
    (let ((certs (map read-cert-file cert-files)))

      ;; Parse target tag
      (let ((tag-sexp (parse-sexp tag-str)))
        (let ((target-tag (make-tag tag-sexp)))

          ;; Display verification info
          (print "Verifying certificate chain...")
          (print "Root key: " root-file)
          (print "Chain length: " (length certs) " certificates")
          (print "Target tag: " tag-str)
          (print "")

          ;; Verify chain
          (handle-exceptions exn
            (begin
              (print "✗ VERIFICATION FAILED: "
                     (if (condition? exn)
                         (get-condition-property exn 'exn 'message)
                         (sprintf "~a" exn)))
              (exit 1))

            (let ((result (verify-chain root-key certs target-tag)))
              (if result
                  (begin
                    (print "✓ VALID: Certificate chain grants authorization")
                    (exit 0))
                  (begin
                    (print "✗ INVALID: Certificate chain does not grant authorization")
                    (exit 1))))))))))

(main (command-line-arguments))
