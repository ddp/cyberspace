#!/usr/bin/env chez --script
;;; spki-verify: Verify SPKI certificate chain
;;; Chez Scheme port

(import (rnrs)
        (only (chezscheme) printf format command-line void)
        (cyberspace sexp)
        (cyberspace cert)
        (cyberspace crypto-ffi))

(define (usage)
  (printf "Usage: spki-verify --root KEYFILE --chain CERTFILE [--chain CERTFILE ...] --tag TAG~%")
  (printf "Verify an SPKI certificate delegation chain.~%")
  (printf "~%")
  (printf "Required:~%")
  (printf "  --root FILE         Root public key file~%")
  (printf "  --chain FILE        Certificate file (can specify multiple)~%")
  (printf "  --tag TAG           Tag to verify (s-expression)~%")
  (printf "~%")
  (printf "  --help              Show this help~%")
  (printf "~%")
  (printf "Example:~%")
  (printf "  spki-verify --root alice.public \\~%")
  (printf "              --chain alice-to-bob.cert \\~%")
  (printf "              --chain bob-to-carol.cert \\~%")
  (printf "              --tag '(read (path /data))'~%")
  (exit 0))

(define (read-key-file filename)
  ;; Read a public key file and return the key bytevector
  (let ((content (with-input-from-file filename
                   (lambda () (get-string-all (current-input-port))))))
    (let ((s (parse-sexp content)))
      (if (and (sexp-list? s)
               (= 2 (length (list-items s))))
          (let ((items (list-items s)))
            (let ((type-atom (car items))
                  (key-bytes (cadr items)))
              (if (and (sexp-atom? type-atom)
                       (string=? (atom-value type-atom) "spki-public-key")
                       (sexp-bytes? key-bytes))
                  (bytes-value key-bytes)
                  (begin
                    (printf "Error: Invalid public key file: ~a~%" filename)
                    (exit 1)))))
          (begin
            (printf "Error: Invalid public key file format: ~a~%" filename)
            (exit 1))))))

(define (read-cert-file filename)
  (let ((content (with-input-from-file filename
                   (lambda () (get-string-all (current-input-port))))))
    (signed-cert-of-string content)))

(define (main args)
  (sodium-init)

  (let ((root-file #f)
        (cert-files '())
        (tag-str #f))

    (let loop ((args args))
      (cond
       ((null? args) (void))

       ((string=? (car args) "--help")
        (usage))

       ((string=? (car args) "--root")
        (if (null? (cdr args))
            (begin (printf "Error: --root requires an argument~%") (exit 1))
            (begin
              (set! root-file (cadr args))
              (loop (cddr args)))))

       ((string=? (car args) "--chain")
        (if (null? (cdr args))
            (begin (printf "Error: --chain requires an argument~%") (exit 1))
            (begin
              (set! cert-files (append cert-files (list (cadr args))))
              (loop (cddr args)))))

       ((string=? (car args) "--tag")
        (if (null? (cdr args))
            (begin (printf "Error: --tag requires an argument~%") (exit 1))
            (begin
              (set! tag-str (cadr args))
              (loop (cddr args)))))

       (else
        (printf "Error: Unknown argument: ~a~%" (car args))
        (usage))))

    (unless (and root-file (not (null? cert-files)) tag-str)
      (printf "Error: --root, --chain, and --tag are required~%")
      (usage))

    (let ((root-key (read-key-file root-file)))
      (let ((certs (map read-cert-file cert-files)))
        (let ((tag-sexp (parse-sexp tag-str)))
          (let ((target-tag (make-tag tag-sexp)))

            (printf "Verifying certificate chain...~%")
            (printf "Root key: ~a~%" root-file)
            (printf "Chain length: ~a certificates~%" (length certs))
            (printf "Target tag: ~a~%" tag-str)
            (printf "~%")

            (guard (exn
                    (#t (printf "x Verification Failed: ~a~%" exn)
                        (exit 1)))

              (let ((result (verify-chain root-key certs target-tag)))
                (if result
                    (begin
                      (printf "Valid: Certificate chain grants authorization~%")
                      (exit 0))
                    (begin
                      (printf "Invalid: Certificate chain does not grant authorization~%")
                      (exit 1)))))))))))

(main (cdr (command-line)))
