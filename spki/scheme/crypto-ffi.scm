;;; SPKI Scheme - Crypto FFI to libsodium
;;;
;;; Chicken Scheme bindings to libsodium for Ed25519 signatures.
;;; This provides the same crypto operations as the OCaml TCB,
;;; but from Scheme for the policy layer.
;;;
;;; Architecture:
;;;   Chicken Scheme → crypto-ffi.scm → libsodium (same as OCaml TCB)
;;;
;;; The OCaml TCB exists for Coq verification.
;;; The Scheme FFI exists for policy/tools/human-readable code.
;;; Both use the same underlying crypto: libsodium Ed25519.

(module crypto-ffi
  (sodium-init
   ed25519-keypair
   ed25519-sign
   ed25519-verify
   sha256-hash)

  (import scheme
          (chicken base)
          (chicken foreign)
          (chicken format)
          srfi-4)

  ;; Include libsodium header
  (foreign-declare "#include <sodium.h>")

  ;; Constants from libsodium
  (define crypto-sign-publickeybytes 32)
  (define crypto-sign-secretkeybytes 64)
  (define crypto-sign-bytes 64)
  (define crypto-hash-sha256-bytes 32)

  ;; Initialize libsodium
  ;; Returns: 0 on success, -1 on error, 1 if already initialized
  (define sodium-init
    (foreign-lambda int "sodium_init"))

  ;; Generate Ed25519 keypair
  ;; Returns: (public-key . secret-key) as bytevectors
  (define (ed25519-keypair)
    (let ((pk (make-u8vector crypto-sign-publickeybytes))
          (sk (make-u8vector crypto-sign-secretkeybytes)))
      ((foreign-lambda int "crypto_sign_keypair"
                      scheme-pointer scheme-pointer)
       pk sk)
      (cons pk sk)))

  ;; Sign message with Ed25519
  ;; @param secret-key: 64-byte secret key (bytevector)
  ;; @param message: message to sign (bytevector or string)
  ;; @return signature: 64-byte signature (bytevector)
  (define (ed25519-sign secret-key message)
    (let* ((msg-bytes (if (string? message)
                          (string->u8vector message)
                          message))
           (signature (make-u8vector crypto-sign-bytes))
           (sig-len-ptr (make-u8vector 8)))  ; unsigned long long
      ((foreign-lambda int "crypto_sign_detached"
                      scheme-pointer     ; signature
                      scheme-pointer     ; signature length (out)
                      scheme-pointer     ; message
                      unsigned-integer   ; message length
                      scheme-pointer)    ; secret key
       signature sig-len-ptr msg-bytes (u8vector-length msg-bytes) secret-key)
      signature))

  ;; Verify Ed25519 signature
  ;; @param public-key: 32-byte public key (bytevector)
  ;; @param message: message that was signed (bytevector or string)
  ;; @param signature: 64-byte signature (bytevector)
  ;; @return #t if valid, #f otherwise
  ;;;
  ;;; TCB CRITICAL: This is the core security guarantee.
  ;;; If this returns #t, the signature was created by holder of the private key.
  (define (ed25519-verify public-key message signature)
    (let* ((msg-bytes (if (string? message)
                          (string->u8vector message)
                          message))
           (result ((foreign-lambda int "crypto_sign_verify_detached"
                                   scheme-pointer     ; signature
                                   scheme-pointer     ; message
                                   unsigned-integer   ; message length
                                   scheme-pointer)    ; public key
                    signature msg-bytes (u8vector-length msg-bytes) public-key)))
      ;; crypto_sign_verify_detached returns 0 on success, -1 on failure
      (= result 0)))

  ;; Compute SHA-256 hash
  ;; @param data: data to hash (bytevector or string)
  ;; @return hash: 32-byte hash (bytevector)
  (define (sha256-hash data)
    (let* ((data-bytes (if (string? data)
                           (string->u8vector data)
                           data))
           (hash (make-u8vector crypto-hash-sha256-bytes)))
      ((foreign-lambda int "crypto_hash_sha256"
                      scheme-pointer     ; hash output
                      scheme-pointer     ; data
                      unsigned-integer)  ; data length
       hash data-bytes (u8vector-length data-bytes))
      hash))

  ;; Helper: convert string to u8vector
  (define (string->u8vector str)
    (let* ((len (string-length str))
           (vec (make-u8vector len)))
      (do ((i 0 (+ i 1)))
          ((= i len) vec)
        (u8vector-set! vec i (char->integer (string-ref str i))))))

  ;; Helper: convert u8vector to hex string
  (define (u8vector->hex vec)
    (let ((len (u8vector-length vec)))
      (let loop ((i 0) (acc '()))
        (if (= i len)
            (apply string-append (reverse acc))
            (loop (+ i 1)
                  (cons (sprintf "~x" (u8vector-ref vec i)) acc))))))

  ) ;; end module

;;;
;;; TCB Properties (same as OCaml TCB):
;;;
;;; 1. Signature correctness:
;;;    For all keypairs and messages,
;;;    (ed25519-verify pk msg (ed25519-sign sk msg)) = #t
;;;
;;; 2. Unforgeability:
;;;    If (ed25519-verify pk msg sig) = #t, then
;;;    sig was created by the holder of the corresponding secret key
;;;
;;; 3. Constant-time:
;;;    All operations are constant-time (libsodium guarantee)
;;;
