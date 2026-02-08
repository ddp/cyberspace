/*
 * pq-bridge.c - C shim for Chez Scheme pq-crypto
 * Library of Cyberspace - Chez Port
 *
 * Wraps liboqs post-quantum signature APIs for Chez Scheme.
 * Chez cannot embed C structs or use inline C, so this bridge
 * exposes plain-function interfaces callable via foreign-procedure.
 *
 * Algorithms:
 *   - SPHINCS+-SHAKE-256s-simple (hash-based, NIST Level 5)
 *   - ML-DSA-65 (lattice-based, NIST Level 3)
 *
 * Build: ./build-pq-bridge.sh
 */

#include <stdlib.h>
#include <string.h>
#include <oqs/oqs.h>

/* Cached signature objects (initialized once, reused) */
static OQS_SIG *sphincs_sig = NULL;
static OQS_SIG *mldsa_sig = NULL;

/* Algorithm names - must match liboqs exactly */
#define ALG_SPHINCS "SPHINCS+-SHAKE-256s-simple"
#define ALG_MLDSA   "ML-DSA-65"

/* ============================================================
 * Initialization
 * ============================================================ */

int pq_init(void) {
    OQS_init();

    if (!sphincs_sig) {
        sphincs_sig = OQS_SIG_new(ALG_SPHINCS);
        if (!sphincs_sig)
            return -1;
    }

    if (!mldsa_sig) {
        mldsa_sig = OQS_SIG_new(ALG_MLDSA);
        if (!mldsa_sig)
            return -2;
    }

    return 0;
}

/* ============================================================
 * Size accessors (needed before keygen to allocate buffers)
 * ============================================================ */

size_t sphincs_pk_bytes(void) {
    return sphincs_sig ? sphincs_sig->length_public_key : 0;
}

size_t sphincs_sk_bytes(void) {
    return sphincs_sig ? sphincs_sig->length_secret_key : 0;
}

size_t sphincs_sig_bytes(void) {
    return sphincs_sig ? sphincs_sig->length_signature : 0;
}

size_t mldsa_pk_bytes(void) {
    return mldsa_sig ? mldsa_sig->length_public_key : 0;
}

size_t mldsa_sk_bytes(void) {
    return mldsa_sig ? mldsa_sig->length_secret_key : 0;
}

size_t mldsa_sig_bytes(void) {
    return mldsa_sig ? mldsa_sig->length_signature : 0;
}

/* ============================================================
 * SPHINCS+-SHAKE-256s
 * ============================================================ */

int sphincs_keypair(unsigned char *pk, unsigned char *sk) {
    if (!sphincs_sig) return -1;
    return OQS_SIG_keypair(sphincs_sig, pk, sk) == OQS_SUCCESS ? 0 : -1;
}

int sphincs_sign(unsigned char *sig, size_t *sig_len,
                 const unsigned char *msg, size_t msg_len,
                 const unsigned char *sk) {
    if (!sphincs_sig) return -1;
    return OQS_SIG_sign(sphincs_sig, sig, sig_len, msg, msg_len, sk)
           == OQS_SUCCESS ? 0 : -1;
}

int sphincs_verify(const unsigned char *msg, size_t msg_len,
                   const unsigned char *sig, size_t sig_len,
                   const unsigned char *pk) {
    if (!sphincs_sig) return -1;
    return OQS_SIG_verify(sphincs_sig, msg, msg_len, sig, sig_len, pk)
           == OQS_SUCCESS ? 0 : -1;
}

/* ============================================================
 * ML-DSA-65
 * ============================================================ */

int mldsa_keypair(unsigned char *pk, unsigned char *sk) {
    if (!mldsa_sig) return -1;
    return OQS_SIG_keypair(mldsa_sig, pk, sk) == OQS_SUCCESS ? 0 : -1;
}

int mldsa_sign(unsigned char *sig, size_t *sig_len,
               const unsigned char *msg, size_t msg_len,
               const unsigned char *sk) {
    if (!mldsa_sig) return -1;
    return OQS_SIG_sign(mldsa_sig, sig, sig_len, msg, msg_len, sk)
           == OQS_SUCCESS ? 0 : -1;
}

int mldsa_verify(const unsigned char *msg, size_t msg_len,
                 const unsigned char *sig, size_t sig_len,
                 const unsigned char *pk) {
    if (!mldsa_sig) return -1;
    return OQS_SIG_verify(mldsa_sig, msg, msg_len, sig, sig_len, pk)
           == OQS_SUCCESS ? 0 : -1;
}
