;;; Cyberspace Script Signing and Verification
;;; Chez Scheme Port
;;;
;;; Cryptographic signing for cyberspace scripts with
;;; threshold signature support for distributed governance.
;;;
;;; Tiered Signing Model:
;;;   Development:  Single signature (1-of-1)
;;;   Staging:      Dual signature (2-of-2)
;;;   Production:   Threshold signature (K-of-N)
;;;
;;; Ported from Chicken's script.scm.

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

  (import (rnrs)
          (only (chezscheme) time-second current-time printf format)
          (cyberspace chicken-compatibility blob)
          (cyberspace chicken-compatibility chicken)
          (cyberspace crypto-ffi)
          (cyberspace cert))

  ;;; Script Signature Record

  (define-record-type (script-signature make-script-signature script-signature?)
    (fields (immutable signer signature-signer)
            (immutable value signature-value)
            (immutable timestamp signature-timestamp)))

  ;;; Single Script Signing

  (define (sign-script script-content private-key . rest)
    "Sign script content with a private key.
     Optional public-key argument; derived if not provided."
    (let* ((pub-key (get-opt rest 0 #f))
           (content-bv (if (string? script-content)
                           (string->blob script-content)
                           script-content))
           (pk (or pub-key (ed25519-secret-to-public private-key)))
           (sig (ed25519-sign private-key content-bv))
           (timestamp (time-second (current-time))))
      (make-script-signature pk sig timestamp)))

  ;;; Single Script Verification

  (define (verify-script script-content signature-record)
    "Verify a script signature. Returns #t if valid, #f otherwise."
    (let ((content-bv (if (string? script-content)
                          (string->blob script-content)
                          script-content)))
      (ed25519-verify (signature-signer signature-record)
                      content-bv
                      (signature-value signature-record))))

  ;;; Threshold Signature Support

  (define (threshold-sign-script script-content private-keys public-keys)
    "Create threshold signatures for a script.
     Returns list of script-signature records."
    (unless (= (length private-keys) (length public-keys))
      (error 'threshold-sign-script "Private and public key lists must have same length"))
    (map (lambda (priv pub)
           (sign-script script-content priv pub))
         private-keys
         public-keys))

  (define (verify-threshold-script script-content signature-records threshold)
    "Verify threshold signatures on a script.
     Returns #t if at least K signatures are valid."
    (let* ((valid-sigs (filter (lambda (sig)
                                 (verify-script script-content sig))
                               signature-records))
           (valid-count (length valid-sigs)))
      (>= valid-count threshold)))

) ;; end library
