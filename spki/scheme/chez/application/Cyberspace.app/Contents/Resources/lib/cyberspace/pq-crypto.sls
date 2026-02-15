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
;;;   Chez Scheme → foreign-procedure → libpq-bridge → liboqs
;;;
;;; Ported from Chicken's pq-crypto.scm.
;;; Changes: inline C (foreign-declare) → separate C bridge (pq-bridge.c),
;;;          foreign-lambda/foreign-safe-lambda* → foreign-procedure,
;;;          blob → bytevector (via compat layer).

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
          (only (chezscheme)
                load-shared-object foreign-procedure format)
          (cyberspace chicken-compatibility blob)
          (cyberspace chicken-compatibility chicken))

  ;; ============================================================
  ;; Library Loading
  ;; ============================================================

  (define *pq-bridge-loaded*
    (let loop ((paths '("./libpq-bridge.dylib"
                        "../libpq-bridge.dylib"
                        "libpq-bridge.dylib"
                        "./libpq-bridge.so"
                        "../libpq-bridge.so"
                        "libpq-bridge.so")))
      (if (null? paths)
          #f  ;; Graceful degradation: PQ crypto unavailable without native bridge
          (guard (exn [#t (loop (cdr paths))])
            (load-shared-object (car paths))
            #t))))

  ;; ============================================================
  ;; Foreign Procedure Declarations
  ;; Deferred: only resolved when *pq-bridge-loaded* is #t
  ;; ============================================================

  (define-syntax define-pq-foreign
    (syntax-rules ()
      [(_ name expr)
       (define name
         (if *pq-bridge-loaded*
             expr
             (lambda args
               (error 'pq-crypto "PQ bridge not loaded -- run build-pq-bridge.sh"))))]))

  ;; Initialization
  (define-pq-foreign %pq-init
    (foreign-procedure "pq_init" () int))

  ;; Size accessors
  (define-pq-foreign %sphincs-pk-bytes
    (foreign-procedure "sphincs_pk_bytes" () unsigned-64))

  (define-pq-foreign %sphincs-sk-bytes
    (foreign-procedure "sphincs_sk_bytes" () unsigned-64))

  (define-pq-foreign %sphincs-sig-bytes
    (foreign-procedure "sphincs_sig_bytes" () unsigned-64))

  (define-pq-foreign %mldsa-pk-bytes
    (foreign-procedure "mldsa_pk_bytes" () unsigned-64))

  (define-pq-foreign %mldsa-sk-bytes
    (foreign-procedure "mldsa_sk_bytes" () unsigned-64))

  (define-pq-foreign %mldsa-sig-bytes
    (foreign-procedure "mldsa_sig_bytes" () unsigned-64))

  ;; SPHINCS+ operations
  (define-pq-foreign %sphincs-keypair
    (foreign-procedure "sphincs_keypair" (u8* u8*) int))

  (define-pq-foreign %sphincs-sign
    (foreign-procedure "sphincs_sign"
      (u8* u8* u8* unsigned-64 u8*) int))

  (define-pq-foreign %sphincs-verify
    (foreign-procedure "sphincs_verify"
      (u8* unsigned-64 u8* unsigned-64 u8*) int))

  ;; ML-DSA operations
  (define-pq-foreign %mldsa-keypair
    (foreign-procedure "mldsa_keypair" (u8* u8*) int))

  (define-pq-foreign %mldsa-sign
    (foreign-procedure "mldsa_sign"
      (u8* u8* u8* unsigned-64 u8*) int))

  (define-pq-foreign %mldsa-verify
    (foreign-procedure "mldsa_verify"
      (u8* unsigned-64 u8* unsigned-64 u8*) int))

  ;; ============================================================
  ;; Initialization
  ;; ============================================================

  (define (pq-init)
    (let ((result (%pq-init)))
      (if (= result 0)
          result
          (error 'pq-init
                 (cond
                   ((= result -1) "Failed to initialize SPHINCS+")
                   ((= result -2) "Failed to initialize ML-DSA-65")
                   (else "Unknown initialization error"))))))

  ;; ============================================================
  ;; SPHINCS+-SHAKE-256s (hash-based signatures)
  ;; ============================================================

  (define (sphincs+-public-key-bytes) (%sphincs-pk-bytes))
  (define (sphincs+-secret-key-bytes) (%sphincs-sk-bytes))
  (define (sphincs+-signature-bytes)  (%sphincs-sig-bytes))

  (define (sphincs+-keygen)
    "Generate SPHINCS+-SHAKE-256s keypair (post-quantum, hash-based)"
    (let ((pk-len (sphincs+-public-key-bytes))
          (sk-len (sphincs+-secret-key-bytes)))
      (when (= pk-len 0)
        (error 'sphincs+-keygen "pq-crypto not initialized, call (pq-init) first"))
      (let ((pk (make-blob pk-len))
            (sk (make-blob sk-len)))
        (let ((result (%sphincs-keypair pk sk)))
          (if (= result 0)
              (values pk sk)
              (error 'sphincs+-keygen "keypair generation failed"))))))

  (define (sphincs+-sign message secret-key)
    "Sign message with SPHINCS+-SHAKE-256s"
    (let* ((msg-blob (if (bytevector? message) message
                         (string->blob message)))
           (sig-max-len (sphincs+-signature-bytes))
           (sig (make-blob sig-max-len))
           (sig-len-buf (make-bytevector 8 0)))  ; size_t output
      (when (= sig-max-len 0)
        (error 'sphincs+-sign "pq-crypto not initialized"))
      (let ((result (%sphincs-sign sig sig-len-buf
                                   msg-blob (blob-size msg-blob)
                                   secret-key)))
        (if (= result 0)
            sig
            (error 'sphincs+-sign "signing failed")))))

  (define (sphincs+-verify message signature public-key)
    "Verify SPHINCS+-SHAKE-256s signature"
    (let ((msg-blob (if (bytevector? message) message
                        (string->blob message))))
      (= 0 (%sphincs-verify msg-blob (blob-size msg-blob)
                             signature (blob-size signature)
                             public-key))))

  ;; ============================================================
  ;; ML-DSA-65 (lattice-based signatures, formerly Dilithium3)
  ;; ============================================================

  (define (ml-dsa-public-key-bytes) (%mldsa-pk-bytes))
  (define (ml-dsa-secret-key-bytes) (%mldsa-sk-bytes))
  (define (ml-dsa-signature-bytes)  (%mldsa-sig-bytes))

  (define (ml-dsa-keygen)
    "Generate ML-DSA-65 keypair (post-quantum, lattice-based)"
    (let ((pk-len (ml-dsa-public-key-bytes))
          (sk-len (ml-dsa-secret-key-bytes)))
      (when (= pk-len 0)
        (error 'ml-dsa-keygen "pq-crypto not initialized, call (pq-init) first"))
      (let ((pk (make-blob pk-len))
            (sk (make-blob sk-len)))
        (let ((result (%mldsa-keypair pk sk)))
          (if (= result 0)
              (values pk sk)
              (error 'ml-dsa-keygen "keypair generation failed"))))))

  (define (ml-dsa-sign message secret-key)
    "Sign message with ML-DSA-65"
    (let* ((msg-blob (if (bytevector? message) message
                         (string->blob message)))
           (sig-max-len (ml-dsa-signature-bytes))
           (sig (make-blob sig-max-len))
           (sig-len-buf (make-bytevector 8 0)))  ; size_t output
      (when (= sig-max-len 0)
        (error 'ml-dsa-sign "pq-crypto not initialized"))
      (let ((result (%mldsa-sign sig sig-len-buf
                                  msg-blob (blob-size msg-blob)
                                  secret-key)))
        (if (= result 0)
            sig
            (error 'ml-dsa-sign "signing failed")))))

  (define (ml-dsa-verify message signature public-key)
    "Verify ML-DSA-65 signature"
    (let ((msg-blob (if (bytevector? message) message
                        (string->blob message))))
      (= 0 (%mldsa-verify msg-blob (blob-size msg-blob)
                            signature (blob-size signature)
                            public-key))))

  ;; ============================================================
  ;; Hybrid Signatures (Ed25519 + SPHINCS+)
  ;; ============================================================

  (define (hybrid-sign message ed25519-sk sphincs+-sk ed25519-sign-fn)
    "Sign with both Ed25519 and SPHINCS+ for transition security.
     Both signatures must verify for the hybrid to be valid.
     ed25519-sign-fn should be crypto-ffi's ed25519-sign."
    (let ((ed-sig (ed25519-sign-fn message ed25519-sk))
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

) ;; end library
