#!/usr/bin/env chez --libdirs . --script
;;; test-security.ss - Test security.sls port
;;; Exercises fingerprinting, cert-status, validity-expired?, display

(import (rnrs)
        (only (chezscheme) printf format current-time time-second)
        (cyberspace sexp)
        (cyberspace crypto-ffi)
        (cyberspace cert)
        (cyberspace security))

(sodium-init)

(define pass 0)
(define fail 0)

(define (check name result)
  (if result
      (begin
        (printf "  ok: ~a~%" name)
        (set! pass (+ pass 1)))
      (begin
        (printf "  FAIL: ~a~%" name)
        (set! fail (+ fail 1)))))

;; Generate a keypair for testing
(let* ((kp (ed25519-keypair))
       (pub (car kp))
       (priv (cadr kp)))

  ;; Test principal-fingerprint
  (let* ((principal (make-key-principal pub))
         (fp (principal-fingerprint principal)))
    (check "fingerprint is a string"
           (string? fp))
    (check "fingerprint has colons"
           (> (length (let loop ((s fp) (acc '()))
                        (let ((i (let scan ((j 0))
                                   (cond ((>= j (string-length s)) #f)
                                         ((char=? (string-ref s j) #\:) j)
                                         (else (scan (+ j 1)))))))
                          (if i
                              (loop (substring s (+ i 1) (string-length s))
                                    (cons (substring s 0 i) acc))
                              (reverse (cons s acc))))))
              1))
    (check "fingerprint consistent"
           (string=? fp (principal-fingerprint principal))))

  ;; Test keyhash-principal fingerprint
  (let* ((hash (sha512-hash pub))
         (kh (make-keyhash-principal 'sha512 hash))
         (fp (principal-fingerprint kh)))
    (check "keyhash fingerprint starts with hash:"
           (and (>= (string-length fp) 5)
                (string=? (substring fp 0 5) "hash:"))))

  ;; Test validity-expired?
  (let ((past (make-validity 1000000 1577836800))    ; not-after = 2020-01-01
        (future (make-validity 1000000 4102444800)))  ; not-after = 2100-01-01
    (check "past validity is expired"
           (validity-expired? past))
    (check "future validity is not expired"
           (not (validity-expired? future))))

  ;; Test cert-status
  (let* ((kp2 (ed25519-keypair))
         (pub2 (car kp2))
         (priv2 (cadr kp2)))
    (let* ((issuer-principal (make-key-principal pub))
           (subject-principal (make-key-principal pub2))
           (c (create-cert issuer-principal subject-principal
                           (make-tag (sexp-atom "read"))))
           (sc (sign-cert c priv)))

      (check "cert-status valid"
             (eq? 'valid (cert-status sc pub)))

      ;; Test with wrong key
      (check "cert-status invalid-signature"
             (eq? 'invalid-signature (cert-status sc pub2)))

      ;; Test with expired validity
      (let* ((c-expired (create-cert issuer-principal subject-principal
                                     (make-tag (sexp-atom "read"))
                                     'validity: (make-validity 1000000 1577836800)))
             (sc-expired (sign-cert c-expired priv)))
        (check "cert-status expired"
               (eq? 'expired (cert-status sc-expired pub))))

      ;; Test revocation
      (let ((revocations (list `((fingerprint . ,(principal-fingerprint subject-principal))))))
        (check "cert-status revoked"
               (eq? 'revoked (cert-status sc pub revocations))))

      ;; Test who-can
      (let ((holders (who-can (sexp-atom "read") (list sc))))
        (check "who-can finds the subject"
               (= 1 (length holders))))

      ;; Test what-can
      (let ((caps (what-can subject-principal (list sc))))
        (check "what-can finds the tag"
               (= 1 (length caps))))

      ;; Test check-revocation
      (check "check-revocation no-list"
             (eq? 'no-list (check-revocation sc '())))

      ;; Test verify-chain-to
      (check "verify-chain-to single cert"
             (verify-chain-to issuer-principal (list sc)))

      ;; Test display functions don't crash
      (display-principal issuer-principal)
      (display-capability (make-all-perms))
      (display-cert sc)
      (check "display functions completed" #t)

      ;; Test security-summary doesn't crash
      (security-summary)
      (check "security-summary completed" #t))))

(printf "~%Results: ~a passed, ~a failed~%" pass fail)
(when (> fail 0) (exit 1))
