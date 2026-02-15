;;; SPKI Scheme - Post-Quantum Cryptography FFI to liboqs
;;;
;;; Chicken Scheme bindings to liboqs for post-quantum signatures:
;;;   - SPHINCS+-SHAKE-256s (hash-based, conservative)
;;;   - ML-DSA-65 (lattice-based, NIST standard, formerly Dilithium3)
;;;
;;; See Memo-048 for migration strategy and use cases.
;;;
;;; Architecture:
;;;   Chicken Scheme -> pq-crypto.scm -> liboqs
;;;
;;; Security levels (post-quantum):
;;;   SPHINCS+-SHAKE-256s: 128-bit (NIST Level 5)
;;;   ML-DSA-65: 128-bit (NIST Level 3)

(module pq-crypto
  (;; Initialization
   pq-init

   ;; SPHINCS+ (hash-based, conservative)
   sphincs+-keygen
   sphincs+-sign
   sphincs+-verify
   sphincs+-public-key-bytes
   sphincs+-secret-key-bytes
   sphincs+-signature-bytes

   ;; ML-DSA (lattice-based, formerly Dilithium)
   ml-dsa-keygen
   ml-dsa-sign
   ml-dsa-verify
   ml-dsa-public-key-bytes
   ml-dsa-secret-key-bytes
   ml-dsa-signature-bytes

   ;; Hybrid signatures (Ed25519 + SPHINCS+)
   hybrid-sign
   hybrid-verify

   ;; Algorithm info
   pq-algorithm-info
   pq-supported-algorithms)

  (import scheme
          (chicken base)
          (chicken foreign)
          (chicken blob)
          (chicken memory)
          srfi-4)

  ;; Include liboqs headers
  (foreign-declare "
#include <oqs/oqs.h>
#include <string.h>
#include <stdlib.h>

/* Algorithm names - must match liboqs exactly */
#define ALG_SPHINCS \"SPHINCS+-SHAKE-256s-simple\"
#define ALG_MLDSA \"ML-DSA-65\"

/* Debug helper */
static int last_init_error = 0;

/* Cached signature objects for performance */
static OQS_SIG *sphincs_sig = NULL;
static OQS_SIG *mldsa_sig = NULL;

/* Initialize and cache algorithm objects */
static int pq_init_algorithms(void) {
    OQS_init();

    if (!sphincs_sig) {
        sphincs_sig = OQS_SIG_new(ALG_SPHINCS);
        if (!sphincs_sig) {
            last_init_error = 1;
            return -1;
        }
    }

    if (!mldsa_sig) {
        mldsa_sig = OQS_SIG_new(ALG_MLDSA);
        if (!mldsa_sig) {
            last_init_error = 2;
            return -2;
        }
    }

    return 0;
}

/* Check if algorithm is supported */
static int sphincs_supported(void) {
    return OQS_SIG_alg_is_enabled(ALG_SPHINCS);
}

static int mldsa_supported(void) {
    return OQS_SIG_alg_is_enabled(ALG_MLDSA);
}

/* Get algorithm sizes */
static size_t sphincs_pk_bytes(void) {
    return sphincs_sig ? sphincs_sig->length_public_key : 0;
}

static size_t sphincs_sk_bytes(void) {
    return sphincs_sig ? sphincs_sig->length_secret_key : 0;
}

static size_t sphincs_sig_bytes(void) {
    return sphincs_sig ? sphincs_sig->length_signature : 0;
}

static size_t mldsa_pk_bytes(void) {
    return mldsa_sig ? mldsa_sig->length_public_key : 0;
}

static size_t mldsa_sk_bytes(void) {
    return mldsa_sig ? mldsa_sig->length_secret_key : 0;
}

static size_t mldsa_sig_bytes(void) {
    return mldsa_sig ? mldsa_sig->length_signature : 0;
}
")

  ;; Initialize liboqs (call once at startup)
  (define pq-init
    (foreign-lambda int "pq_init_algorithms"))

  ;; ============================================================
  ;; SPHINCS+-SHAKE-256s (hash-based signatures)
  ;; ============================================================

  ;; Size constants (populated after init)
  (define sphincs+-public-key-bytes
    (foreign-lambda size_t "sphincs_pk_bytes"))

  (define sphincs+-secret-key-bytes
    (foreign-lambda size_t "sphincs_sk_bytes"))

  (define sphincs+-signature-bytes
    (foreign-lambda size_t "sphincs_sig_bytes"))

  ;; Keypair generation using blob pointers directly
  (define sphincs+-keypair-raw
    (foreign-safe-lambda* int ((blob pk) (blob sk))
      "if (!sphincs_sig) C_return(-1);
       int result = OQS_SIG_keypair(sphincs_sig, pk, sk) == OQS_SUCCESS ? 0 : -1;
       C_return(result);"))

  ;; Generate SPHINCS+ keypair
  ;; Returns: (values public-key secret-key) as blobs
  (define (sphincs+-keygen)
    "Generate SPHINCS+-SHAKE-256s keypair (post-quantum, hash-based)"
    (let* ((pk-len (sphincs+-public-key-bytes))
           (sk-len (sphincs+-secret-key-bytes)))
      (when (= pk-len 0)
        (error 'sphincs+-keygen "pq-crypto not initialized, call (pq-init) first"))
      (let* ((pk (make-blob pk-len))
             (sk (make-blob sk-len))
             (result (sphincs+-keypair-raw pk sk)))
        (if (= result 0)
            (values pk sk)
            (error 'sphincs+-keygen "keypair generation failed")))))

  ;; Low-level FFI for signing using blobs
  (define sphincs+-sign-raw
    (foreign-safe-lambda* int ((blob sig) (u64vector sig_len_out)
                               (blob msg) (size_t msg_len)
                               (blob sk))
      "if (!sphincs_sig) C_return(-1);
       size_t sig_len;
       OQS_STATUS status = OQS_SIG_sign(sphincs_sig, sig, &sig_len, msg, msg_len, sk);
       if (status == OQS_SUCCESS) {
           sig_len_out[0] = sig_len;
           C_return(0);
       }
       C_return(-1);"))

  ;; Sign message with SPHINCS+
  ;; Returns: signature blob
  (define (sphincs+-sign message secret-key)
    "Sign message with SPHINCS+-SHAKE-256s"
    (let* ((msg-blob (if (blob? message) message (string->blob message)))
           (sig-max-len (sphincs+-signature-bytes))
           (sig (make-blob sig-max-len))
           (sig-len-buf (make-u64vector 1 0)))
      (when (= sig-max-len 0)
        (error 'sphincs+-sign "pq-crypto not initialized"))
      (let ((result (sphincs+-sign-raw sig sig-len-buf msg-blob (blob-size msg-blob) secret-key)))
        (if (= result 0)
            sig  ; SPHINCS+ always produces fixed-size signatures
            (error 'sphincs+-sign "signing failed")))))

  ;; Low-level FFI for verification using blobs
  (define sphincs+-verify-raw
    (foreign-safe-lambda* int ((blob msg) (size_t msg_len)
                               (blob sig) (size_t sig_len)
                               (blob pk))
      "if (!sphincs_sig) C_return(-1);
       int result = OQS_SIG_verify(sphincs_sig, msg, msg_len, sig, sig_len, pk) == OQS_SUCCESS ? 0 : -1;
       C_return(result);"))

  ;; Verify SPHINCS+ signature
  ;; Returns: #t if valid, #f if invalid
  (define (sphincs+-verify message signature public-key)
    "Verify SPHINCS+-SHAKE-256s signature"
    (let ((msg-blob (if (blob? message) message (string->blob message))))
      (= 0 (sphincs+-verify-raw msg-blob (blob-size msg-blob)
                                 signature (blob-size signature)
                                 public-key))))

  ;; ============================================================
  ;; ML-DSA-65 (lattice-based signatures, formerly Dilithium3)
  ;; ============================================================

  ;; Size constants
  (define ml-dsa-public-key-bytes
    (foreign-lambda size_t "mldsa_pk_bytes"))

  (define ml-dsa-secret-key-bytes
    (foreign-lambda size_t "mldsa_sk_bytes"))

  (define ml-dsa-signature-bytes
    (foreign-lambda size_t "mldsa_sig_bytes"))

  ;; Keypair generation using blob pointers directly
  (define ml-dsa-keypair-raw
    (foreign-safe-lambda* int ((blob pk) (blob sk))
      "if (!mldsa_sig) C_return(-1);
       int result = OQS_SIG_keypair(mldsa_sig, pk, sk) == OQS_SUCCESS ? 0 : -1;
       C_return(result);"))

  ;; Generate ML-DSA keypair
  ;; Returns: (values public-key secret-key) as blobs
  (define (ml-dsa-keygen)
    "Generate ML-DSA-65 keypair (post-quantum, lattice-based)"
    (let* ((pk-len (ml-dsa-public-key-bytes))
           (sk-len (ml-dsa-secret-key-bytes)))
      (when (= pk-len 0)
        (error 'ml-dsa-keygen "pq-crypto not initialized, call (pq-init) first"))
      (let* ((pk (make-blob pk-len))
             (sk (make-blob sk-len))
             (result (ml-dsa-keypair-raw pk sk)))
        (if (= result 0)
            (values pk sk)
            (error 'ml-dsa-keygen "keypair generation failed")))))

  ;; Low-level FFI for signing using blobs
  (define ml-dsa-sign-raw
    (foreign-safe-lambda* int ((blob sig) (u64vector sig_len_out)
                               (blob msg) (size_t msg_len)
                               (blob sk))
      "if (!mldsa_sig) C_return(-1);
       size_t sig_len;
       OQS_STATUS status = OQS_SIG_sign(mldsa_sig, sig, &sig_len, msg, msg_len, sk);
       if (status == OQS_SUCCESS) {
           sig_len_out[0] = sig_len;
           C_return(0);
       }
       C_return(-1);"))

  ;; Sign message with ML-DSA
  ;; Returns: signature blob
  (define (ml-dsa-sign message secret-key)
    "Sign message with ML-DSA-65"
    (let* ((msg-blob (if (blob? message) message (string->blob message)))
           (sig-max-len (ml-dsa-signature-bytes))
           (sig (make-blob sig-max-len))
           (sig-len-buf (make-u64vector 1 0)))
      (when (= sig-max-len 0)
        (error 'ml-dsa-sign "pq-crypto not initialized"))
      (let ((result (ml-dsa-sign-raw sig sig-len-buf msg-blob (blob-size msg-blob) secret-key)))
        (if (= result 0)
            sig  ; ML-DSA always produces fixed-size signatures
            (error 'ml-dsa-sign "signing failed")))))

  ;; Low-level FFI for verification using blobs
  (define ml-dsa-verify-raw
    (foreign-safe-lambda* int ((blob msg) (size_t msg_len)
                               (blob sig) (size_t sig_len)
                               (blob pk))
      "if (!mldsa_sig) C_return(-1);
       int result = OQS_SIG_verify(mldsa_sig, msg, msg_len, sig, sig_len, pk) == OQS_SUCCESS ? 0 : -1;
       C_return(result);"))

  ;; Verify ML-DSA signature
  ;; Returns: #t if valid, #f if invalid
  (define (ml-dsa-verify message signature public-key)
    "Verify ML-DSA-65 signature"
    (let ((msg-blob (if (blob? message) message (string->blob message))))
      (= 0 (ml-dsa-verify-raw msg-blob (blob-size msg-blob)
                               signature (blob-size signature)
                               public-key))))

  ;; ============================================================
  ;; Hybrid Signatures (Ed25519 + SPHINCS+)
  ;; ============================================================

  ;; Hybrid signature format:
  ;; (hybrid-signature
  ;;   (ed25519 <64-byte-blob>)
  ;;   (sphincs+ <~7856-byte-blob>))

  (define (hybrid-sign message ed25519-sk sphincs+-sk ed25519-sign-fn)
    "Sign with both Ed25519 and SPHINCS+ for transition security.
     Both signatures must verify for the hybrid to be valid.
     ed25519-sign-fn should be crypto-ffi#ed25519-sign."
    (let ((ed-sig (ed25519-sign-fn message ed25519-sk))
          (pq-sig (sphincs+-sign message sphincs+-sk)))
      `(hybrid-signature
        (ed25519 ,ed-sig)
        (sphincs+ ,pq-sig))))

  (define (hybrid-verify message hybrid-sig ed25519-pk sphincs+-pk ed25519-verify-fn)
    "Verify hybrid signature - BOTH must be valid.
     ed25519-verify-fn should be crypto-ffi#ed25519-verify."
    (and (pair? hybrid-sig)
         (eq? (car hybrid-sig) 'hybrid-signature)
         (let ((ed-sig (cadr (assq 'ed25519 (cdr hybrid-sig))))
               (pq-sig (cadr (assq 'sphincs+ (cdr hybrid-sig)))))
           (and ed-sig pq-sig
                (ed25519-verify-fn message ed-sig ed25519-pk)
                (sphincs+-verify message pq-sig sphincs+-pk)))))

  ;; ============================================================
  ;; Algorithm Information
  ;; ============================================================

  (define (pq-algorithm-info algorithm)
    "Get information about a post-quantum algorithm"
    (case algorithm
      ((sphincs+ sphincs+-shake-256s)
       `((name . "SPHINCS+-SHAKE-256s-simple")
         (type . hash-based)
         (security-level . "NIST Level 5")
         (post-quantum-bits . 128)
         (public-key-bytes . ,(sphincs+-public-key-bytes))
         (secret-key-bytes . ,(sphincs+-secret-key-bytes))
         (signature-bytes . ,(sphincs+-signature-bytes))
         (use-cases . (realm-identity sealed-releases long-term-keys))))
      ((ml-dsa ml-dsa-65 dilithium dilithium3)
       `((name . "ML-DSA-65")
         (type . lattice-based)
         (security-level . "NIST Level 3")
         (post-quantum-bits . 128)
         (public-key-bytes . ,(ml-dsa-public-key-bytes))
         (secret-key-bytes . ,(ml-dsa-secret-key-bytes))
         (signature-bytes . ,(ml-dsa-signature-bytes))
         (use-cases . (capability-certs agent-delegation audit-entries))))
      (else
       (error 'pq-algorithm-info "Unknown algorithm" algorithm))))

  (define (pq-supported-algorithms)
    "List supported post-quantum signature algorithms"
    '(sphincs+-shake-256s ml-dsa-65))

) ; end module
