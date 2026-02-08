;;; Cyberspace Script Signing and Verification
;;; Library of Cyberspace - Chez Port
;;;
;;; Provides cryptographic signing for cyberspace scripts with
;;; threshold signature support for distributed governance.
;;;
;;; Tiered Signing Model:
;;;   Development:  Single signature (1-of-1)
;;;   Staging:      Dual signature (2-of-2)
;;;   Production:   Threshold signature (K-of-N)

(library (cyberspace script)
  (export
    sign-script
    verify-script
    threshold-sign-script
    verify-threshold-script
    script-signature?
    make-script-signature
    signature-signer
    signature-value
    signature-timestamp)

  (import (except (rnrs) find)
          (only (chezscheme) printf format void)
          (cyberspace chicken-compatibility chicken)
          (cyberspace crypto-ffi)
          (cyberspace cert))

  ;;; Script Signature Record
  ;;;
  ;;; Tagged vector: #(*script-sig-tag* signer signature timestamp)

  (define *script-sig-tag* (list 'script-signature))

  (define (make-script-signature signer signature timestamp)
    "Create a script signature record"
    (vector *script-sig-tag* signer signature timestamp))

  (define (script-signature? x)
    (and (vector? x) (>= (vector-length x) 4)
         (eq? (vector-ref x 0) *script-sig-tag*)))

  (define (signature-signer sig) (vector-ref sig 1))
  (define (signature-value sig)  (vector-ref sig 2))
  (define (signature-timestamp sig) (vector-ref sig 3))

  ;;; Single Script Signing

  (define (sign-script script-content private-key . rest)
    "Sign script content with a private key

     script-content: string or bytevector
     private-key: 64-byte Ed25519 private key (bytevector)
     Optional: public-key (derived if not provided)

     Returns: script-signature record"

    (let* ((public-key (if (null? rest) #f (car rest)))
           (content-bv (if (string? script-content)
                           (string->utf8 script-content)
                           script-content))
           (pub-key (or public-key
                        (ed25519-secret-to-public private-key)))
           (signature (ed25519-sign private-key content-bv))
           (timestamp (current-seconds)))

      (make-script-signature pub-key signature timestamp)))

  ;;; Single Script Verification

  (define (verify-script script-content signature-record)
    "Verify a script signature

     script-content: string or bytevector
     signature-record: script-signature record

     Returns: #t if valid, #f otherwise"

    (let ((content-bv (if (string? script-content)
                          (string->utf8 script-content)
                          script-content)))
      (ed25519-verify (signature-signer signature-record)
                      content-bv
                      (signature-value signature-record))))

  ;;; Threshold Signature Support
  ;;;
  ;;; Multiple parties sign, require K valid signatures

  (define (threshold-sign-script script-content private-keys public-keys)
    "Create threshold signatures for a script

     script-content: string or bytevector
     private-keys: list of N private keys (bytevectors)
     public-keys: list of N public keys (bytevectors)

     Returns: list of script-signature records"

    (unless (= (length private-keys) (length public-keys))
      (error 'threshold-sign-script
             "Private and public key lists must have same length"))
    (map (lambda (priv pub)
           (sign-script script-content priv pub))
         private-keys
         public-keys))

  (define (verify-threshold-script script-content signature-records threshold)
    "Verify threshold signatures on a script

     script-content: string or bytevector
     signature-records: list of script-signature records
     threshold: minimum number of valid signatures required (K)

     Returns: #t if at least K signatures are valid, #f otherwise"

    (let* ((valid-sigs (filter (lambda (sig)
                                 (verify-script script-content sig))
                               signature-records))
           (valid-count (length valid-sigs)))
      (>= valid-count threshold)))

) ;; end library
