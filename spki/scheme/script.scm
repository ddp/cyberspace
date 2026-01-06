;;; Cyberspace Script Signing and Verification
;;;
;;; Provides cryptographic signing for cyberspace scripts with
;;; threshold signature support for distributed governance.
;;;
;;; Tiered Signing Model:
;;;   Development:  Single signature (1-of-1)
;;;   Staging:      Dual signature (2-of-2)
;;;   Production:   Threshold signature (K-of-N)

(module script
  (sign-script
   verify-script
   threshold-sign-script
   verify-threshold-script
   script-signature?
   make-script-signature
   signature-signer
   signature-value
   signature-timestamp)

  (import scheme
          (chicken base)
          (chicken time)
          (chicken blob)
          (chicken format)
          crypto-ffi
          cert
          srfi-1
          srfi-4)

  ;;; Script Signature Record
  ;;;
  ;;; Represents a single signature on a script
  ;;; Contains: signer public key, signature value, timestamp

  (define-record-type <script-signature>
    (make-script-signature-internal signer signature timestamp)
    script-signature?
    (signer signature-signer)        ; public key blob
    (signature signature-value)      ; signature blob
    (timestamp signature-timestamp)) ; unix timestamp

  (define (make-script-signature signer signature timestamp)
    "Create a script signature record"
    (make-script-signature-internal signer signature timestamp))

  ;;; Single Script Signing
  ;;;
  ;;; Sign a script with a single private key

  (define (sign-script script-content private-key #!optional public-key)
    "Sign script content with a private key

     script-content: string or blob
     private-key: 64-byte Ed25519 private key (blob)
     public-key: optional 32-byte public key (blob), derived if not provided

     Returns: script-signature record"

    (let* ((content-blob (if (string? script-content)
                             (string->blob script-content)
                             script-content))
           (pub-key (or public-key
                        (ed25519-secret-to-public private-key)))
           (signature (ed25519-sign private-key content-blob))
           (timestamp (current-seconds)))

      (make-script-signature pub-key signature timestamp)))

  ;;; Single Script Verification

  (define (verify-script script-content signature-record)
    "Verify a script signature

     script-content: string or blob
     signature-record: script-signature record

     Returns: #t if valid, #f otherwise"

    (let ((content-blob (if (string? script-content)
                            (string->blob script-content)
                            script-content)))
      (ed25519-verify (signature-signer signature-record)
                     content-blob
                     (signature-value signature-record))))

  ;;; Threshold Signature Support
  ;;;
  ;;; Multiple parties sign, require K valid signatures

  (define (threshold-sign-script script-content private-keys public-keys)
    "Create threshold signatures for a script

     script-content: string or blob
     private-keys: list of N private keys (blobs)
     public-keys: list of N public keys (blobs)

     Returns: list of script-signature records"

    (if (not (= (length private-keys) (length public-keys)))
        (error "Private and public key lists must have same length")
        (map (lambda (priv pub)
               (sign-script script-content priv pub))
             private-keys
             public-keys)))

  (define (verify-threshold-script script-content signature-records threshold)
    "Verify threshold signatures on a script

     script-content: string or blob
     signature-records: list of script-signature records
     threshold: minimum number of valid signatures required (K)

     Returns: #t if at least K signatures are valid, #f otherwise"

    (let* ((valid-sigs (filter (lambda (sig)
                                 (verify-script script-content sig))
                               signature-records))
           (valid-count (length valid-sigs)))

      (if (>= valid-count threshold)
          #t
          (begin
            (when #f ; debug output disabled
              (printf "Threshold verification failed: ~a valid signatures, need ~a\n"
                      valid-count threshold))
            #f))))

  ) ;; end module

;;; Design Notes:
;;;
;;; Threshold Signature Models:
;;;
;;; 1. **Multi-Signature (implemented here)**:
;;;    - Each party has their own keypair
;;;    - K parties must sign independently
;;;    - Verification checks K valid signatures
;;;    - Simple, no key reconstruction needed
;;;    - Good for: governance, approvals, multi-party auth
;;;
;;; 2. **Shamir Key Splitting (future)**:
;;;    - Single private key split into N shares using Shamir
;;;    - K parties reconstruct key and sign once
;;;    - Single signature, but requires key reconstruction
;;;    - Good for: emergency recovery, backup scenarios
;;;
;;; For cyberspace governance, multi-signature is more appropriate:
;;; - Each party maintains their own key
;;;    - No single point of failure
;;;    - Clear audit trail (who signed what)
;;;    - Revocation by key (not by share)
