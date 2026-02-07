;;; SPKI Scheme - Post-Quantum Cryptography FFI to liboqs
;;; Library of Cyberspace - Chez Port
;;;
;;; Chez Scheme bindings to liboqs for post-quantum signatures:
;;;   - SPHINCS+-SHAKE-256s (hash-based, conservative)
;;;   - ML-DSA-65 (lattice-based, NIST standard, formerly Dilithium3)
;;;
;;; See Memo-048 for migration strategy and use cases.
;;;
;;; Architecture:
;;;   Chez Scheme -> foreign-procedure -> liboqs (via C bridge)
;;;
;;; Security levels (post-quantum):
;;;   SPHINCS+-SHAKE-256s: 128-bit (NIST Level 5)
;;;   ML-DSA-65: 128-bit (NIST Level 3)
;;;
;;; Port note: Uses load-shared-object + foreign-procedure for FFI.
;;; The C bridge (pq-bridge.c) wraps liboqs with bytevector-safe APIs.

(library (cyberspace pq-crypto)
  (export
    ;; Initialization
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

  (import (rnrs)
          (only (chezscheme) load-shared-object foreign-procedure
                             printf format void))

  ;; ============================================================
  ;; FFI Bridge
  ;; ============================================================
  ;;
  ;; The PQ crypto bridge requires a C shim (pq-bridge.c) that wraps
  ;; liboqs functions with bytevector-compatible calling conventions.
  ;; Until that bridge is built and liboqs is available, all operations
  ;; raise descriptive errors.

  (define *pq-initialized* #f)

  ;; Try to load the bridge, but don't fail if unavailable
  (define *pq-available*
    (guard (exn (#t #f))
      (load-shared-object "libpq-bridge.so")
      #t))

  ;; ============================================================
  ;; Initialization
  ;; ============================================================

  (define (pq-init)
    "Initialize post-quantum crypto subsystem.
     Returns 0 on success, negative on error."
    (if *pq-available*
        (let ((init-fn (foreign-procedure "pq_init_algorithms" () int)))
          (let ((result (init-fn)))
            (when (= result 0)
              (set! *pq-initialized* #t))
            result))
        (begin
          (set! *pq-initialized* #f)
          -1)))

  (define (pq-check who)
    "Guard: ensure PQ crypto is initialized"
    (unless *pq-initialized*
      (error who "Post-quantum crypto not initialized (call pq-init first, requires liboqs)")))

  ;; ============================================================
  ;; SPHINCS+-SHAKE-256s (hash-based signatures)
  ;; ============================================================

  (define (sphincs+-public-key-bytes)
    (pq-check 'sphincs+-public-key-bytes)
    (let ((f (foreign-procedure "sphincs_pk_bytes" () unsigned-64)))
      (f)))

  (define (sphincs+-secret-key-bytes)
    (pq-check 'sphincs+-secret-key-bytes)
    (let ((f (foreign-procedure "sphincs_sk_bytes" () unsigned-64)))
      (f)))

  (define (sphincs+-signature-bytes)
    (pq-check 'sphincs+-signature-bytes)
    (let ((f (foreign-procedure "sphincs_sig_bytes" () unsigned-64)))
      (f)))

  (define (sphincs+-keygen)
    "Generate SPHINCS+-SHAKE-256s keypair (post-quantum, hash-based).
     Returns: (values public-key secret-key) as bytevectors"
    (pq-check 'sphincs+-keygen)
    (let* ((pk-len (sphincs+-public-key-bytes))
           (sk-len (sphincs+-secret-key-bytes))
           (pk (make-bytevector pk-len))
           (sk (make-bytevector sk-len))
           (keygen-fn (foreign-procedure "pq_sphincs_keygen"
                        (u8* u8*) int))
           (result (keygen-fn pk sk)))
      (if (= result 0)
          (values pk sk)
          (error 'sphincs+-keygen "keypair generation failed"))))

  (define (sphincs+-sign message secret-key)
    "Sign message with SPHINCS+-SHAKE-256s"
    (pq-check 'sphincs+-sign)
    (let* ((msg-bv (if (bytevector? message) message (string->utf8 message)))
           (sig-max-len (sphincs+-signature-bytes))
           (sig (make-bytevector sig-max-len))
           (sign-fn (foreign-procedure "pq_sphincs_sign"
                      (u8* u8* unsigned-64 u8*) int))
           (result (sign-fn sig msg-bv (bytevector-length msg-bv) secret-key)))
      (if (= result 0)
          sig
          (error 'sphincs+-sign "signing failed"))))

  (define (sphincs+-verify message signature public-key)
    "Verify SPHINCS+-SHAKE-256s signature.
     Returns: #t if valid, #f if invalid"
    (pq-check 'sphincs+-verify)
    (let* ((msg-bv (if (bytevector? message) message (string->utf8 message)))
           (verify-fn (foreign-procedure "pq_sphincs_verify"
                        (u8* unsigned-64 u8* unsigned-64 u8*) int))
           (result (verify-fn msg-bv (bytevector-length msg-bv)
                              signature (bytevector-length signature)
                              public-key)))
      (= result 0)))

  ;; ============================================================
  ;; ML-DSA-65 (lattice-based signatures, formerly Dilithium3)
  ;; ============================================================

  (define (ml-dsa-public-key-bytes)
    (pq-check 'ml-dsa-public-key-bytes)
    (let ((f (foreign-procedure "mldsa_pk_bytes" () unsigned-64)))
      (f)))

  (define (ml-dsa-secret-key-bytes)
    (pq-check 'ml-dsa-secret-key-bytes)
    (let ((f (foreign-procedure "mldsa_sk_bytes" () unsigned-64)))
      (f)))

  (define (ml-dsa-signature-bytes)
    (pq-check 'ml-dsa-signature-bytes)
    (let ((f (foreign-procedure "mldsa_sig_bytes" () unsigned-64)))
      (f)))

  (define (ml-dsa-keygen)
    "Generate ML-DSA-65 keypair (post-quantum, lattice-based).
     Returns: (values public-key secret-key) as bytevectors"
    (pq-check 'ml-dsa-keygen)
    (let* ((pk-len (ml-dsa-public-key-bytes))
           (sk-len (ml-dsa-secret-key-bytes))
           (pk (make-bytevector pk-len))
           (sk (make-bytevector sk-len))
           (keygen-fn (foreign-procedure "pq_mldsa_keygen"
                        (u8* u8*) int))
           (result (keygen-fn pk sk)))
      (if (= result 0)
          (values pk sk)
          (error 'ml-dsa-keygen "keypair generation failed"))))

  (define (ml-dsa-sign message secret-key)
    "Sign message with ML-DSA-65"
    (pq-check 'ml-dsa-sign)
    (let* ((msg-bv (if (bytevector? message) message (string->utf8 message)))
           (sig-max-len (ml-dsa-signature-bytes))
           (sig (make-bytevector sig-max-len))
           (sign-fn (foreign-procedure "pq_mldsa_sign"
                      (u8* u8* unsigned-64 u8*) int))
           (result (sign-fn sig msg-bv (bytevector-length msg-bv) secret-key)))
      (if (= result 0)
          sig
          (error 'ml-dsa-sign "signing failed"))))

  (define (ml-dsa-verify message signature public-key)
    "Verify ML-DSA-65 signature.
     Returns: #t if valid, #f if invalid"
    (pq-check 'ml-dsa-verify)
    (let* ((msg-bv (if (bytevector? message) message (string->utf8 message)))
           (verify-fn (foreign-procedure "pq_mldsa_verify"
                        (u8* unsigned-64 u8* unsigned-64 u8*) int))
           (result (verify-fn msg-bv (bytevector-length msg-bv)
                              signature (bytevector-length signature)
                              public-key)))
      (= result 0)))

  ;; ============================================================
  ;; Hybrid Signatures (Ed25519 + SPHINCS+)
  ;; ============================================================

  (define (hybrid-sign message ed25519-sk sphincs+-sk ed25519-sign-fn)
    "Sign with both Ed25519 and SPHINCS+ for transition security.
     Both signatures must verify for the hybrid to be valid.
     ed25519-sign-fn should be crypto-ffi's ed25519-sign."
    (pq-check 'hybrid-sign)
    (let ((ed-sig (ed25519-sign-fn ed25519-sk message))
          (pq-sig (sphincs+-sign message sphincs+-sk)))
      `(hybrid-signature
        (ed25519 ,ed-sig)
        (sphincs+ ,pq-sig))))

  (define (hybrid-verify message hybrid-sig ed25519-pk sphincs+-pk ed25519-verify-fn)
    "Verify hybrid signature - BOTH must be valid.
     ed25519-verify-fn should be crypto-ffi's ed25519-verify."
    (and (pair? hybrid-sig)
         (eq? (car hybrid-sig) 'hybrid-signature)
         (let ((ed-sig (cadr (assq 'ed25519 (cdr hybrid-sig))))
               (pq-sig (cadr (assq 'sphincs+ (cdr hybrid-sig)))))
           (and ed-sig pq-sig
                (ed25519-verify-fn ed25519-pk message ed-sig)
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
         (use-cases . (realm-identity sealed-releases long-term-keys))))
      ((ml-dsa ml-dsa-65 dilithium dilithium3)
       `((name . "ML-DSA-65")
         (type . lattice-based)
         (security-level . "NIST Level 3")
         (post-quantum-bits . 128)
         (use-cases . (capability-certs agent-delegation audit-entries))))
      (else
       (error 'pq-algorithm-info "Unknown algorithm" algorithm))))

  (define (pq-supported-algorithms)
    "List supported post-quantum signature algorithms"
    '(sphincs+-shake-256s ml-dsa-65))

) ;; end library
