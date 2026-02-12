#!/usr/bin/env chez --script
;;; spki-show: Display SPKI certificate in human-readable format
;;; Chez Scheme port

(import (rnrs)
        (only (chezscheme) printf format command-line void)
        (cyberspace sexp)
        (cyberspace cert)
        (cyberspace crypto-ffi))

(define (usage)
  (printf "Usage: spki-show [FILE]~%")
  (printf "Display an SPKI certificate or key in human-readable format.~%")
  (printf "~%")
  (printf "If FILE is omitted, reads from stdin.~%")
  (printf "~%")
  (printf "  --help              Show this help~%")
  (exit 0))

(define (bytevector->hex bv n)
  ;; First n bytes of bytevector as hex string
  (let loop ((i 0) (acc ""))
    (if (>= i (min n (bytevector-length bv)))
        acc
        (loop (+ i 1)
              (string-append acc
                             (let ((b (bytevector-u8-ref bv i)))
                               (format #f "~2,'0x" b)))))))

(define (show-key-hash hash)
  ;; Display first 16 bytes of hash in hex
  (bytevector->hex hash 16))

(define (show-principal principal)
  (cond
   ((key-principal? principal)
    (let* ((key (principal-public-key principal))
           (hash (sha512-hash key)))
      (format #f "Key (hash: ~a)" (show-key-hash hash))))

   ((keyhash-principal? principal)
    (let ((alg (principal-hash-alg principal))
          (hash (principal-hash principal)))
      (format #f "KeyHash (~a: ~a)"
              (hash-alg->string alg)
              (show-key-hash hash))))

   (else
    "Unknown principal type")))

(define (show-tag tag-or-all)
  (cond
   ((tag? tag-or-all)
    (sexp->string (tag-sexp tag-or-all)))
   ((all-perms? tag-or-all)
    "(*)")
   (else
    "Unknown tag type")))

(define (show-validity c)
  (let ((val (cert-validity c)))
    (if val
        (format #f "~a to ~a"
                (validity-not-before val)
                (validity-not-after val))
        "No expiration")))

(define (show-cert c)
  (printf "SPKI Certificate~%")
  (printf "================~%")
  (printf "~%")
  (printf "Issuer:     ~a~%" (show-principal (cert-issuer c)))
  (printf "Subject:    ~a~%" (show-principal (cert-subject c)))
  (printf "Tag:        ~a~%" (show-tag (cert-tag c)))
  (printf "Validity:   ~a~%" (show-validity c))
  (printf "Propagate:  ~a~%" (if (cert-propagate c) "yes" "no"))
  (printf "~%"))

(define (show-signed-cert sc)
  (show-cert (signed-cert-cert sc))
  (printf "Signature~%")
  (printf "---------~%")
  (let ((sig (signed-cert-signature sc)))
    (printf "Algorithm:  ~a~%" (hash-alg->string (signature-hash-alg sig)))
    (printf "Cert hash:  ~a~%" (show-key-hash (signature-cert-hash sig)))
    (printf "Signature:  ~a...~%" (show-key-hash (signature-sig-bytes sig))))
  (printf "~%")
  (printf "S-Expression~%")
  (printf "------------~%")
  (printf "~a~%" (signed-cert->string sc)))

(define (show-key key is-private?)
  (let ((key-type (if is-private? "Private" "Public")))
    (printf "SPKI ~a Key~%" key-type)
    (printf "================~%")
    (printf "~%")
    (let ((pub-key (if is-private?
                       (ed25519-secret-to-public key)
                       key)))
      (let ((hash (sha512-hash pub-key)))
        (printf "Key hash: ~a~%" (show-key-hash hash))))
    (when is-private?
      (printf "~%")
      (printf "Warning: This is a PRIVATE key - keep it secret!~%"))))

(define (main args)
  (sodium-init)

  (let ((filename "-"))
    (let loop ((args args))
      (cond
       ((null? args) (void))
       ((string=? (car args) "--help") (usage))
       (else
        (set! filename (car args))
        (loop (cdr args)))))

    (let ((content (if (string=? filename "-")
                       (get-string-all (current-input-port))
                       (with-input-from-file filename
                         (lambda () (get-string-all (current-input-port)))))))

      (guard (exn
              (#t (printf "Error parsing input: ~a~%" exn)
                  (exit 1)))

        (let ((s (parse-sexp content)))
          (cond
           ;; Private key
           ((and (sexp-list? s)
                 (= 2 (length (list-items s)))
                 (sexp-atom? (car (list-items s)))
                 (string=? (atom-value (car (list-items s))) "spki-private-key")
                 (sexp-bytes? (cadr (list-items s))))
            (show-key (bytes-value (cadr (list-items s))) #t))

           ;; Public key
           ((and (sexp-list? s)
                 (= 2 (length (list-items s)))
                 (sexp-atom? (car (list-items s)))
                 (string=? (atom-value (car (list-items s))) "spki-public-key")
                 (sexp-bytes? (cadr (list-items s))))
            (show-key (bytes-value (cadr (list-items s))) #f))

           ;; Signed cert
           (else
            (let ((sc (signed-cert-of-string content)))
              (show-signed-cert sc)))))))))

(main (cdr (command-line)))
