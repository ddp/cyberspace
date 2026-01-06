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
   crypto-sign-bytes
   ;; Shamir secret sharing
   shamir-split
   shamir-reconstruct
   shamir-share?
   share-id
   share-threshold
   share-x
   share-y
   ;; GF(256) arithmetic (for testing)
   gf256-add
   gf256-mul
   gf256-div)

  (import scheme
          (chicken base)
          (chicken foreign)
          (chicken format)
          (chicken blob)
          (chicken memory representation)
          (chicken bitwise)
          (chicken random)
          srfi-1   ; list utilities (take)
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

  ;;; ============================================================================
  ;;; Shamir Secret Sharing (GF(256))
  ;;; ============================================================================

  ;; GF(256) arithmetic tables (precomputed for efficiency)
  ;; Using polynomial x^8 + x^4 + x^3 + x + 1 (0x11b)

  (define gf256-exp (make-u8vector 512))
  (define gf256-log (make-u8vector 256))

  (define (init-gf256-tables!)
    "Initialize GF(256) logarithm and exponential tables using generator 3"
    (let ((x 1))
      ;; GF(256) multiplicative group has 255 elements
      ;; Using generator 3 (not 2!) with polynomial 0x11b
      ;; 3^255 = 1, so we stop at i=254 to avoid overwriting log[1]
      (do ((i 0 (+ i 1)))
          ((= i 255))
        (u8vector-set! gf256-exp i x)
        (u8vector-set! gf256-log x i)
        ;; x = x * 3 in GF(256)
        (when (< i 254)
          ;; Multiply by 3 = multiply by 2, then XOR with original
          (let* ((x2 (arithmetic-shift x 1))
                 (x2-reduced (if (>= x2 256)
                                 (bitwise-xor x2 #x11b)
                                 x2)))
            (set! x (bitwise-xor x2-reduced x))))))
    ;; Duplicate exp table for convenience
    (do ((i 255 (+ i 1)))
        ((= i 510))
      (u8vector-set! gf256-exp i (u8vector-ref gf256-exp (- i 255)))))

  ;; Initialize tables on module load
  (init-gf256-tables!)

  (define (gf256-add a b)
    "Add two elements in GF(256)"
    (bitwise-xor a b))

  (define (gf256-mul a b)
    "Multiply two elements in GF(256)"
    (if (or (= a 0) (= b 0))
        0
        (u8vector-ref gf256-exp
                     (modulo (+ (u8vector-ref gf256-log a)
                               (u8vector-ref gf256-log b))
                            255))))

  (define (gf256-div a b)
    "Divide a by b in GF(256)"
    (if (= a 0)
        0
        (u8vector-ref gf256-exp
                     (modulo (- (+ (u8vector-ref gf256-log a) 255)
                               (u8vector-ref gf256-log b))
                            255))))

  (define (gf256-poly-eval coeffs x)
    "Evaluate polynomial at x using Horner's method in GF(256)"
    (let loop ((i (- (length coeffs) 1))
               (result 0))
      (if (< i 0)
          result
          (loop (- i 1)
                (gf256-add (list-ref coeffs i)
                          (gf256-mul result x))))))

  ;; Share record type
  (define-record-type <shamir-share>
    (make-shamir-share-internal id threshold x y)
    shamir-share?
    (id share-id)
    (threshold share-threshold)
    (x share-x)
    (y share-y))

  (define (shamir-split secret #!key (threshold 3) (total 5))
    "Split secret into N shares, requiring K to reconstruct

     secret: blob (e.g., Ed25519 private key)
     threshold: minimum shares needed (K)
     total: total shares to create (N)

     Returns: list of N shares"

    (unless (<= threshold total)
      (error "Threshold must be <= total shares"))

    (unless (> threshold 1)
      (error "Threshold must be > 1"))

    (let* ((secret-bytes (blob->u8vector secret))
           (secret-len (u8vector-length secret-bytes))
           (shares (make-vector total)))

      ;; Initialize all share y-value vectors
      (do ((i 0 (+ i 1)))
          ((= i total))
        (vector-set! shares i (make-u8vector secret-len)))

      ;; For each byte of the secret
      (do ((byte-idx 0 (+ byte-idx 1)))
          ((= byte-idx secret-len))

        ;; Generate ONE random polynomial for this byte
        ;; a[0] = secret byte, a[1..k-1] = random
        (let ((coeffs (make-vector threshold)))
          (vector-set! coeffs 0 (u8vector-ref secret-bytes byte-idx))

          (do ((i 1 (+ i 1)))
              ((= i threshold))
            (vector-set! coeffs i (pseudo-random-integer 256)))

          ;; Evaluate this polynomial at each share's x-value
          (do ((share-num 1 (+ share-num 1)))
              ((> share-num total))
            (u8vector-set! (vector-ref shares (- share-num 1))
                          byte-idx
                          (gf256-poly-eval (vector->list coeffs) share-num)))))

      ;; Convert u8vectors to share records
      (do ((i 0 (+ i 1)))
          ((= i total))
        (vector-set! shares i
                    (make-shamir-share-internal
                      (string->symbol (string-append "share-" (number->string (+ i 1))))
                      threshold
                      (+ i 1)
                      (u8vector->blob (vector-ref shares i)))))

      (vector->list shares)))

  (define (shamir-reconstruct shares)
    "Reconstruct secret from K or more shares

     shares: list of share records

     Returns: reconstructed secret (blob)"

    (when (null? shares)
      (error "Need at least one share"))

    (let* ((threshold (share-threshold (car shares)))
           (num-shares (length shares)))

      (unless (>= num-shares threshold)
        (error (sprintf "Need at least ~a shares, got ~a" threshold num-shares)))

      ;; Take exactly K shares
      (let* ((k-shares (take shares threshold))
             (share-len (blob-size (share-y (car k-shares))))
             (secret (make-u8vector share-len)))

        ;; For each byte position
        (do ((byte-idx 0 (+ byte-idx 1)))
            ((= byte-idx share-len))

          ;; Lagrange interpolation at x=0
          (let ((result 0))
            (do ((i 0 (+ i 1)))
                ((= i threshold))

              (let ((xi (share-x (list-ref k-shares i)))
                    (yi (u8vector-ref (blob->u8vector (share-y (list-ref k-shares i)))
                                     byte-idx)))

                ;; Compute Lagrange basis polynomial at x=0
                (let ((basis 1))
                  (do ((j 0 (+ j 1)))
                      ((= j threshold))
                    (when (not (= i j))
                      (let ((xj (share-x (list-ref k-shares j))))
                        ;; basis *= (0 - xj) / (xi - xj)
                        ;; In GF(256): basis *= xj / (xi ^ xj)
                        (set! basis (gf256-mul basis
                                              (gf256-div xj
                                                        (gf256-add xi xj)))))))

                  ;; result += yi * basis
                  (set! result (gf256-add result (gf256-mul yi basis))))))

            (u8vector-set! secret byte-idx result)))

        (u8vector->blob secret))))

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
