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
   ed25519-keypair!
   ed25519-keypair
   ed25519-sign
   ed25519-verify
   ed25519-secret-to-public
   sha256-hash
   sha512-hash
   crypto-sign-publickeybytes
   crypto-sign-secretkeybytes
   crypto-sign-bytes)

  (import scheme
          (chicken base)
          (chicken foreign)
          (chicken format)
          (chicken blob)
          (chicken memory representation)
          srfi-4)

  ;; Include libsodium header
  (foreign-declare "#include <sodium.h>")

  ;; Constants from libsodium
  (define crypto-sign-publickeybytes 32)
  (define crypto-sign-secretkeybytes 64)
  (define crypto-sign-bytes 64)
  (define crypto-hash-sha256-bytes 32)
  (define crypto-hash-sha512-bytes 64)

  ;; Initialize libsodium
  ;; Returns: 0 on success, -1 on error, 1 if already initialized
  (define sodium-init
    (foreign-lambda int "sodium_init"))

  ;; Generate Ed25519 keypair (mutating version)
  ;; Takes pre-allocated scheme-objects and fills them with keypair
  ;; @param public-key: 32-byte blob (will be filled)
  ;; @param secret-key: 64-byte blob (will be filled)
  ;; @return: 0 on success, -1 on failure
  (define ed25519-keypair!
    (foreign-lambda int "crypto_sign_keypair"
                    scheme-pointer scheme-pointer))

  ;; Generate Ed25519 keypair (allocating version)
  ;; Creates and returns new keypair as blobs
  ;; @return: list of (public-key secret-key) as blobs
  (define (ed25519-keypair)
    (let ((public-key (make-blob crypto-sign-publickeybytes))
          (secret-key (make-blob crypto-sign-secretkeybytes)))
      (ed25519-keypair! public-key secret-key)
      (list public-key secret-key)))

  ;; Extract public key from secret key
  ;; In Ed25519, the 64-byte secret key contains the 32-byte public key at offset 32
  ;; @param secret-key: 64-byte secret key (blob)
  ;; @return: 32-byte public key (blob)
  (define (ed25519-secret-to-public secret-key)
    (let* ((public-key (make-blob crypto-sign-publickeybytes))
           (sk-vec (blob->u8vector/shared secret-key))
           (pk-vec (blob->u8vector/shared public-key)))
      ;; Copy bytes 32-63 from secret key to public key
      (do ((i 0 (+ i 1)))
          ((= i crypto-sign-publickeybytes) public-key)
        (u8vector-set! pk-vec i (u8vector-ref sk-vec (+ i 32))))))

  ;; Sign message with Ed25519
  ;; @param secret-key: 64-byte secret key (blob)
  ;; @param message: message to sign (blob or string)
  ;; @return signature: 64-byte signature (blob)
  (define (ed25519-sign secret-key message)
    (let* ((msg-bytes (if (string? message)
                          (string->blob message)
                          message))
           (signature (make-blob crypto-sign-bytes))
           (sig-len-ptr (make-blob 8)))  ; unsigned long long
      ((foreign-lambda int "crypto_sign_detached"
                      scheme-pointer     ; signature
                      scheme-pointer     ; signature length (out)
                      scheme-pointer     ; message
                      unsigned-integer   ; message length
                      scheme-pointer)    ; secret key
       signature sig-len-ptr msg-bytes (blob-size msg-bytes) secret-key)
      signature))

  ;; Verify Ed25519 signature
  ;; @param public-key: 32-byte public key (blob)
  ;; @param message: message that was signed (blob or string)
  ;; @param signature: 64-byte signature (blob)
  ;; @return #t if valid, #f otherwise
  ;;;
  ;;; TCB CRITICAL: This is the core security guarantee.
  ;;; If this returns #t, the signature was created by holder of the private key.
  (define (ed25519-verify public-key message signature)
    (let* ((msg-bytes (if (string? message)
                          (string->blob message)
                          message))
           (result ((foreign-lambda int "crypto_sign_verify_detached"
                                   scheme-pointer     ; signature
                                   scheme-pointer     ; message
                                   unsigned-integer   ; message length
                                   scheme-pointer)    ; public key
                    signature msg-bytes (blob-size msg-bytes) public-key)))
      ;; crypto_sign_verify_detached returns 0 on success, -1 on failure
      (= result 0)))

  ;; Compute SHA-256 hash
  ;; @param data: data to hash (blob or string)
  ;; @return hash: 32-byte hash (blob)
  (define (sha256-hash data)
    (let* ((data-bytes (if (string? data)
                           (string->blob data)
                           data))
           (hash (make-blob crypto-hash-sha256-bytes)))
      ((foreign-lambda int "crypto_hash_sha256"
                      scheme-pointer     ; hash output
                      scheme-pointer     ; data
                      unsigned-integer)  ; data length
       hash data-bytes (blob-size data-bytes))
      hash))

  ;; Compute SHA-512 hash
  ;; @param data: data to hash (blob or string)
  ;; @return hash: 64-byte hash (blob)
  (define (sha512-hash data)
    (let* ((data-bytes (if (string? data)
                           (string->blob data)
                           data))
           (hash (make-blob crypto-hash-sha512-bytes)))
      ((foreign-lambda int "crypto_hash_sha512"
                      scheme-pointer     ; hash output
                      scheme-pointer     ; data
                      unsigned-integer)  ; data length
       hash data-bytes (blob-size data-bytes))
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
