;;; SPKI Scheme - Post-Quantum Cryptography Stub
;;; Chez Scheme Port
;;;
;;; Stub for pq-crypto module.  The full port requires liboqs FFI
;;; bindings which are deferred.  This provides the export signatures
;;; so that cert.sls (and downstream modules) can compile and work
;;; with Ed25519-only certificates.  PQ operations raise errors.
;;;
;;; When liboqs bindings are ready, replace this stub.

(library (cyberspace pq-crypto)
  (export
    pq-init
    ;; SPHINCS+
    sphincs+-keygen
    sphincs+-sign
    sphincs+-verify
    sphincs+-public-key-bytes
    sphincs+-secret-key-bytes
    sphincs+-signature-bytes
    ;; ML-DSA
    ml-dsa-keygen
    ml-dsa-sign
    ml-dsa-verify
    ml-dsa-public-key-bytes
    ml-dsa-secret-key-bytes
    ml-dsa-signature-bytes
    ;; Hybrid
    hybrid-sign
    hybrid-verify
    ;; Algorithm info
    pq-algorithm-info
    pq-supported-algorithms)

  (import (rnrs))

  (define (pq-not-available name)
    (lambda args
      (error name "Post-quantum crypto not yet available in Chez port")))

  (define pq-init (pq-not-available 'pq-init))

  ;; SPHINCS+
  (define sphincs+-keygen (pq-not-available 'sphincs+-keygen))
  (define sphincs+-sign (pq-not-available 'sphincs+-sign))
  (define sphincs+-verify (pq-not-available 'sphincs+-verify))
  (define sphincs+-public-key-bytes 0)
  (define sphincs+-secret-key-bytes 0)
  (define sphincs+-signature-bytes 0)

  ;; ML-DSA
  (define ml-dsa-keygen (pq-not-available 'ml-dsa-keygen))
  (define ml-dsa-sign (pq-not-available 'ml-dsa-sign))
  (define ml-dsa-verify (pq-not-available 'ml-dsa-verify))
  (define ml-dsa-public-key-bytes 0)
  (define ml-dsa-secret-key-bytes 0)
  (define ml-dsa-signature-bytes 0)

  ;; Hybrid
  (define hybrid-sign (pq-not-available 'hybrid-sign))
  (define hybrid-verify (pq-not-available 'hybrid-verify))

  ;; Info
  (define (pq-algorithm-info)
    '((status . stub)
      (note . "Awaiting liboqs FFI port")))

  (define (pq-supported-algorithms)
    '())

) ;; end library
