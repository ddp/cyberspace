/* SPKI TCB - Post-Quantum Cryptography FFI Stubs
 *
 * C bindings to liboqs for post-quantum signature operations.
 * Extends the TCB with quantum-resistant signatures.
 *
 * Dependencies:
 * - liboqs (built with OQS_USE_OPENSSL=OFF for minimal TCB)
 * - Supports: ML-DSA-65 (lattice), SLH-DSA (hash-based, formerly SPHINCS+)
 *
 * Security guarantees:
 * - Post-quantum security: NIST Level 3-5 (128-bit quantum security)
 * - No OpenSSL dependency (liboqs built with internal crypto primitives)
 * - Deterministic key generation from secure randomness
 */

#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/fail.h>
#include <oqs/oqs.h>
#include <string.h>

/* Algorithm names - must match liboqs exactly */
#define ALG_MLDSA "ML-DSA-65"
#define ALG_SLHDSA "SPHINCS+-SHAKE-256s-simple"  /* FIPS 205 / SPHINCS+ */

/* Cached signature objects for performance */
static OQS_SIG *mldsa_sig = NULL;
static OQS_SIG *slhdsa_sig = NULL;

/* ============================================================
   Initialization
   ============================================================ */

/* Initialize liboqs and cache signature algorithm objects
 * @return: 0 on success, -1 if ML-DSA unsupported, -2 if SLH-DSA unsupported
 *
 * TCB CRITICAL: Must be called before any other PQ operations.
 */
CAMLprim value caml_pq_init(value unit) {
    CAMLparam1(unit);

    OQS_init();

    /* Initialize ML-DSA-65 */
    if (!mldsa_sig) {
        mldsa_sig = OQS_SIG_new(ALG_MLDSA);
        if (!mldsa_sig) {
            CAMLreturn(Val_int(-1));
        }
    }

    /* Initialize SLH-DSA-SHAKE-256s */
    if (!slhdsa_sig) {
        slhdsa_sig = OQS_SIG_new(ALG_SLHDSA);
        if (!slhdsa_sig) {
            CAMLreturn(Val_int(-2));
        }
    }

    CAMLreturn(Val_int(0));
}

/* Cleanup signature objects (call at shutdown) */
CAMLprim value caml_pq_cleanup(value unit) {
    CAMLparam1(unit);

    if (mldsa_sig) {
        OQS_SIG_free(mldsa_sig);
        mldsa_sig = NULL;
    }

    if (slhdsa_sig) {
        OQS_SIG_free(slhdsa_sig);
        slhdsa_sig = NULL;
    }

    CAMLreturn(Val_unit);
}

/* ============================================================
   ML-DSA-65 (Lattice-based signatures, FIPS 204)
   ============================================================ */

/* Get ML-DSA-65 key and signature sizes
 * Returns: (pk_bytes, sk_bytes, sig_bytes) tuple
 */
CAMLprim value caml_mldsa_sizes(value unit) {
    CAMLparam1(unit);
    CAMLlocal1(result);

    if (!mldsa_sig) {
        caml_failwith("ML-DSA not initialized, call pq_init first");
    }

    result = caml_alloc_tuple(3);
    Store_field(result, 0, Val_long(mldsa_sig->length_public_key));
    Store_field(result, 1, Val_long(mldsa_sig->length_secret_key));
    Store_field(result, 2, Val_long(mldsa_sig->length_signature));

    CAMLreturn(result);
}

/* Generate ML-DSA-65 keypair
 * Returns: (public_key, secret_key) tuple
 * - public_key: 1952 bytes
 * - secret_key: 4032 bytes
 *
 * TCB CRITICAL: Uses system randomness via liboqs randombytes.
 */
CAMLprim value caml_mldsa_keypair(value unit) {
    CAMLparam1(unit);
    CAMLlocal3(result, pk, sk);

    if (!mldsa_sig) {
        caml_failwith("ML-DSA not initialized");
    }

    pk = caml_alloc_string(mldsa_sig->length_public_key);
    sk = caml_alloc_string(mldsa_sig->length_secret_key);

    OQS_STATUS status = OQS_SIG_keypair(mldsa_sig,
        (uint8_t*)Bytes_val(pk),
        (uint8_t*)Bytes_val(sk));

    if (status != OQS_SUCCESS) {
        caml_failwith("ML-DSA keypair generation failed");
    }

    result = caml_alloc_tuple(2);
    Store_field(result, 0, pk);
    Store_field(result, 1, sk);

    CAMLreturn(result);
}

/* Sign message with ML-DSA-65
 * @param secret_key: 4032 bytes
 * @param message: arbitrary length bytes
 * @return signature: 3309 bytes (fixed size)
 *
 * TCB CRITICAL: Lattice-based signature, FIPS 204 standard.
 */
CAMLprim value caml_mldsa_sign(value secret_key, value message) {
    CAMLparam2(secret_key, message);
    CAMLlocal1(signature);

    if (!mldsa_sig) {
        caml_failwith("ML-DSA not initialized");
    }

    size_t sig_len;
    signature = caml_alloc_string(mldsa_sig->length_signature);

    OQS_STATUS status = OQS_SIG_sign(mldsa_sig,
        (uint8_t*)Bytes_val(signature), &sig_len,
        (const uint8_t*)Bytes_val(message), caml_string_length(message),
        (const uint8_t*)Bytes_val(secret_key));

    if (status != OQS_SUCCESS) {
        caml_failwith("ML-DSA signing failed");
    }

    CAMLreturn(signature);
}

/* Verify ML-DSA-65 signature
 * @param public_key: 1952 bytes
 * @param message: arbitrary length bytes
 * @param signature: 3309 bytes
 * @return bool: true if valid, false otherwise
 *
 * TCB CRITICAL: Core post-quantum security guarantee.
 */
CAMLprim value caml_mldsa_verify(value public_key, value message, value signature) {
    CAMLparam3(public_key, message, signature);

    if (!mldsa_sig) {
        caml_failwith("ML-DSA not initialized");
    }

    OQS_STATUS status = OQS_SIG_verify(mldsa_sig,
        (const uint8_t*)Bytes_val(message), caml_string_length(message),
        (const uint8_t*)Bytes_val(signature), caml_string_length(signature),
        (const uint8_t*)Bytes_val(public_key));

    CAMLreturn(Val_bool(status == OQS_SUCCESS));
}

/* ============================================================
   SLH-DSA-SHAKE-256s (Hash-based signatures, FIPS 205)
   Formerly known as SPHINCS+
   ============================================================ */

/* Get SLH-DSA-SHAKE-256s key and signature sizes
 * Returns: (pk_bytes, sk_bytes, sig_bytes) tuple
 */
CAMLprim value caml_slhdsa_sizes(value unit) {
    CAMLparam1(unit);
    CAMLlocal1(result);

    if (!slhdsa_sig) {
        caml_failwith("SLH-DSA not initialized, call pq_init first");
    }

    result = caml_alloc_tuple(3);
    Store_field(result, 0, Val_long(slhdsa_sig->length_public_key));
    Store_field(result, 1, Val_long(slhdsa_sig->length_secret_key));
    Store_field(result, 2, Val_long(slhdsa_sig->length_signature));

    CAMLreturn(result);
}

/* Generate SLH-DSA-SHAKE-256s keypair
 * Returns: (public_key, secret_key) tuple
 * - public_key: 64 bytes
 * - secret_key: 128 bytes
 *
 * TCB CRITICAL: Hash-based signature, conservative security assumption.
 */
CAMLprim value caml_slhdsa_keypair(value unit) {
    CAMLparam1(unit);
    CAMLlocal3(result, pk, sk);

    if (!slhdsa_sig) {
        caml_failwith("SLH-DSA not initialized");
    }

    pk = caml_alloc_string(slhdsa_sig->length_public_key);
    sk = caml_alloc_string(slhdsa_sig->length_secret_key);

    OQS_STATUS status = OQS_SIG_keypair(slhdsa_sig,
        (uint8_t*)Bytes_val(pk),
        (uint8_t*)Bytes_val(sk));

    if (status != OQS_SUCCESS) {
        caml_failwith("SLH-DSA keypair generation failed");
    }

    result = caml_alloc_tuple(2);
    Store_field(result, 0, pk);
    Store_field(result, 1, sk);

    CAMLreturn(result);
}

/* Sign message with SLH-DSA-SHAKE-256s
 * @param secret_key: 128 bytes
 * @param message: arbitrary length bytes
 * @return signature: ~29792 bytes (large but conservative)
 *
 * TCB CRITICAL: Hash-based signature, FIPS 205 standard.
 * Larger signatures but only relies on hash function security.
 */
CAMLprim value caml_slhdsa_sign(value secret_key, value message) {
    CAMLparam2(secret_key, message);
    CAMLlocal1(signature);

    if (!slhdsa_sig) {
        caml_failwith("SLH-DSA not initialized");
    }

    size_t sig_len;
    signature = caml_alloc_string(slhdsa_sig->length_signature);

    OQS_STATUS status = OQS_SIG_sign(slhdsa_sig,
        (uint8_t*)Bytes_val(signature), &sig_len,
        (const uint8_t*)Bytes_val(message), caml_string_length(message),
        (const uint8_t*)Bytes_val(secret_key));

    if (status != OQS_SUCCESS) {
        caml_failwith("SLH-DSA signing failed");
    }

    CAMLreturn(signature);
}

/* Verify SLH-DSA-SHAKE-256s signature
 * @param public_key: 64 bytes
 * @param message: arbitrary length bytes
 * @param signature: ~29792 bytes
 * @return bool: true if valid, false otherwise
 *
 * TCB CRITICAL: Core post-quantum security guarantee.
 * Conservative: only relies on SHAKE-256 hash security.
 */
CAMLprim value caml_slhdsa_verify(value public_key, value message, value signature) {
    CAMLparam3(public_key, message, signature);

    if (!slhdsa_sig) {
        caml_failwith("SLH-DSA not initialized");
    }

    OQS_STATUS status = OQS_SIG_verify(slhdsa_sig,
        (const uint8_t*)Bytes_val(message), caml_string_length(message),
        (const uint8_t*)Bytes_val(signature), caml_string_length(signature),
        (const uint8_t*)Bytes_val(public_key));

    CAMLreturn(Val_bool(status == OQS_SUCCESS));
}

/*
 * TCB Post-Quantum Extension Statistics:
 * - Lines of C: ~300
 * - Dependencies: liboqs (built without OpenSSL)
 * - Algorithms: ML-DSA-65 (FIPS 204), SLH-DSA-SHAKE-256s (FIPS 205)
 * - Security: NIST Level 3-5 post-quantum (128-bit quantum security)
 *
 * Total TCB Dependencies: libsodium + liboqs (both minimal, audited)
 *
 * Migration Strategy:
 * - Phase 1: Hybrid signatures (Ed25519 + PQ) for transition
 * - Phase 2: Pure PQ signatures after Q-Day
 * - SLH-DSA: Conservative choice (hash-only assumptions)
 * - ML-DSA: Efficient choice (lattice-based, smaller signatures)
 */
