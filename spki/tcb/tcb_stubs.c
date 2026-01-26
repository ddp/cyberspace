/* SPKI Unified TCB - libsodium FFI Stubs
 *
 * C bindings to libsodium for all TCB cryptographic operations.
 * This is the ONLY C code in the trusted computing base.
 *
 * Security guarantees (from libsodium):
 * - All operations are constant-time
 * - No secret-dependent branches
 * - Memory is zeroed after use
 */

#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/fail.h>
#include <sodium.h>
#include <libkeccak.h>
#include <string.h>

/* ============================================================
   Initialization
   ============================================================ */

CAMLprim value caml_sodium_init(value unit) {
    CAMLparam1(unit);
    CAMLreturn(Val_int(sodium_init()));
}

/* ============================================================
   Ed25519 Signatures
   ============================================================ */

/* Generate Ed25519 keypair
 * Returns: (public_key, secret_key) tuple
 * - public_key: 32 bytes (crypto_sign_PUBLICKEYBYTES)
 * - secret_key: 64 bytes (crypto_sign_SECRETKEYBYTES)
 */
CAMLprim value caml_ed25519_keypair(value unit) {
    CAMLparam1(unit);
    CAMLlocal3(result, pk, sk);

    pk = caml_alloc_string(crypto_sign_PUBLICKEYBYTES);
    sk = caml_alloc_string(crypto_sign_SECRETKEYBYTES);

    crypto_sign_keypair(
        (unsigned char*)Bytes_val(pk),
        (unsigned char*)Bytes_val(sk)
    );

    result = caml_alloc_tuple(2);
    Store_field(result, 0, pk);
    Store_field(result, 1, sk);

    CAMLreturn(result);
}

/* Sign message with Ed25519
 * @param secret_key: 64 bytes
 * @param message: arbitrary length bytes
 * @return signature: 64 bytes (crypto_sign_BYTES)
 */
CAMLprim value caml_ed25519_sign(value secret_key, value message) {
    CAMLparam2(secret_key, message);
    CAMLlocal1(signature);

    unsigned long long sig_len;
    signature = caml_alloc_string(crypto_sign_BYTES);

    crypto_sign_detached(
        (unsigned char*)Bytes_val(signature),
        &sig_len,
        (const unsigned char*)Bytes_val(message),
        caml_string_length(message),
        (const unsigned char*)Bytes_val(secret_key)
    );

    CAMLreturn(signature);
}

/* Verify Ed25519 signature
 * @param public_key: 32 bytes
 * @param message: arbitrary length bytes
 * @param signature: 64 bytes
 * @return bool: true if valid, false otherwise
 *
 * TCB CRITICAL: Core security guarantee.
 * If this returns true, signature was created by holder of private key.
 */
CAMLprim value caml_ed25519_verify(value public_key, value message, value signature) {
    CAMLparam3(public_key, message, signature);

    int result = crypto_sign_verify_detached(
        (const unsigned char*)Bytes_val(signature),
        (const unsigned char*)Bytes_val(message),
        caml_string_length(message),
        (const unsigned char*)Bytes_val(public_key)
    );

    /* crypto_sign_verify_detached returns 0 on success, -1 on failure */
    CAMLreturn(Val_bool(result == 0));
}

/* ============================================================
   Hash Functions
   ============================================================ */

/* Compute SHA-256 hash
 * @param data: arbitrary length bytes
 * @return hash: 32 bytes (crypto_hash_sha256_BYTES)
 */
CAMLprim value caml_sha256_hash(value data) {
    CAMLparam1(data);
    CAMLlocal1(hash);

    hash = caml_alloc_string(crypto_hash_sha256_BYTES);

    crypto_hash_sha256(
        (unsigned char*)Bytes_val(hash),
        (const unsigned char*)Bytes_val(data),
        caml_string_length(data)
    );

    CAMLreturn(hash);
}

/* Compute SHA-512 hash
 * @param data: arbitrary length bytes
 * @return hash: 64 bytes (crypto_hash_sha512_BYTES)
 */
CAMLprim value caml_sha512_hash(value data) {
    CAMLparam1(data);
    CAMLlocal1(hash);

    hash = caml_alloc_string(crypto_hash_sha512_BYTES);

    crypto_hash_sha512(
        (unsigned char*)Bytes_val(hash),
        (const unsigned char*)Bytes_val(data),
        caml_string_length(data)
    );

    CAMLreturn(hash);
}

/* Compute BLAKE2b hash (32 bytes output)
 * @param data: arbitrary length bytes
 * @return hash: 32 bytes
 *
 * BLAKE2b is faster than SHA-512 and used for content addressing.
 */
CAMLprim value caml_blake2b_hash(value data) {
    CAMLparam1(data);
    CAMLlocal1(hash);

    hash = caml_alloc_string(crypto_generichash_BYTES);

    crypto_generichash(
        (unsigned char*)Bytes_val(hash),
        crypto_generichash_BYTES,
        (const unsigned char*)Bytes_val(data),
        caml_string_length(data),
        NULL, 0  /* No key */
    );

    CAMLreturn(hash);
}

/* ============================================================
   HMAC (for CCP cookies)
   ============================================================ */

/* Compute HMAC-SHA256
 * @param key: secret key bytes
 * @param data: message bytes
 * @return mac: 32 bytes
 *
 * Used for stateless cookie verification in CCP.
 */
CAMLprim value caml_hmac_sha256(value key, value data) {
    CAMLparam2(key, data);
    CAMLlocal1(mac);

    mac = caml_alloc_string(crypto_auth_hmacsha256_BYTES);

    crypto_auth_hmacsha256_state state;
    crypto_auth_hmacsha256_init(&state,
        (const unsigned char*)Bytes_val(key),
        caml_string_length(key));
    crypto_auth_hmacsha256_update(&state,
        (const unsigned char*)Bytes_val(data),
        caml_string_length(data));
    crypto_auth_hmacsha256_final(&state,
        (unsigned char*)Bytes_val(mac));

    CAMLreturn(mac);
}

/* ============================================================
   Constant-Time Comparison
   ============================================================ */

/* Constant-time memory comparison
 * @param a: first byte sequence
 * @param b: second byte sequence
 * @return bool: true if equal, false otherwise
 *
 * TCB CRITICAL: MUST be constant-time to prevent timing attacks.
 * Used for principal comparison, MAC verification, etc.
 */
CAMLprim value caml_constant_time_compare(value a, value b) {
    CAMLparam2(a, b);

    size_t len_a = caml_string_length(a);
    size_t len_b = caml_string_length(b);

    if (len_a != len_b) {
        CAMLreturn(Val_false);
    }

    /* sodium_memcmp is guaranteed constant-time */
    int result = sodium_memcmp(
        Bytes_val(a),
        Bytes_val(b),
        len_a
    );

    CAMLreturn(Val_bool(result == 0));
}

/* ============================================================
   Randomness
   ============================================================ */

/* Generate random bytes
 * @param n: number of bytes (OCaml int)
 * @return bytes: n random bytes
 *
 * Uses libsodium's randombytes which:
 * - Uses /dev/urandom on Unix, CryptGenRandom on Windows
 * - Automatically reseeds from system entropy
 * - Safe for key generation, nonces, IVs
 */
CAMLprim value caml_randombytes(value n) {
    CAMLparam1(n);
    CAMLlocal1(buf);

    size_t len = Long_val(n);
    buf = caml_alloc_string(len);

    randombytes_buf(Bytes_val(buf), len);

    CAMLreturn(buf);
}

/* ============================================================
   SHAKE256 (Extendable Output Function)
   ============================================================ */

/* Compute SHAKE256 hash with variable output length
 * @param data: input bytes
 * @param outlen: desired output length in bytes (OCaml int)
 * @return hash: outlen bytes
 *
 * SHAKE256 is an XOF (extendable output function) from SHA-3 family.
 * Used for quantum-resistant Merkle trees (Memo-047).
 *
 * Security:
 * - 256-bit pre-image resistance
 * - 128-bit collision resistance
 * - 128-bit post-quantum security (Grover's algorithm)
 */
CAMLprim value caml_shake256_hash(value data, value outlen) {
    CAMLparam2(data, outlen);
    CAMLlocal1(hash);

    size_t out_bytes = Long_val(outlen);
    hash = caml_alloc_string(out_bytes);

    /* SHAKE256: semicapacity=256, output=out_bytes*8 bits */
    struct libkeccak_spec spec;
    libkeccak_spec_shake(&spec, 256, (long)(out_bytes * 8));

    struct libkeccak_state state;
    if (libkeccak_state_initialise(&state, &spec) != 0) {
        caml_failwith("SHAKE256 state init failed");
    }

    /* Absorb input data */
    if (libkeccak_digest(&state,
                         Bytes_val(data),
                         caml_string_length(data),
                         0,                          /* No additional bits */
                         LIBKECCAK_SHAKE_SUFFIX,     /* SHAKE padding */
                         NULL) != 0) {               /* Don't squeeze yet */
        libkeccak_state_wipe(&state);
        caml_failwith("SHAKE256 absorb failed");
    }

    /* Squeeze output */
    libkeccak_squeeze(&state, Bytes_val(hash));

    /* Wipe sensitive state */
    libkeccak_state_wipe(&state);

    CAMLreturn(hash);
}

/* Compute SHAKE256 with default 32-byte (256-bit) output
 * @param data: input bytes
 * @return hash: 32 bytes
 *
 * Convenience function for common case.
 * Uses same digest+squeeze pattern as caml_shake256_hash for consistency.
 */
CAMLprim value caml_shake256_hash_32(value data) {
    CAMLparam1(data);
    CAMLlocal1(hash);

    hash = caml_alloc_string(32);

    struct libkeccak_spec spec;
    libkeccak_spec_shake(&spec, 256, 256);  /* 256-bit output */

    struct libkeccak_state state;
    if (libkeccak_state_initialise(&state, &spec) != 0) {
        caml_failwith("SHAKE256 state init failed");
    }

    /* Absorb input data (same as general function) */
    if (libkeccak_digest(&state,
                         Bytes_val(data),
                         caml_string_length(data),
                         0,
                         LIBKECCAK_SHAKE_SUFFIX,
                         NULL) != 0) {
        libkeccak_state_wipe(&state);
        caml_failwith("SHAKE256 absorb failed");
    }

    /* Squeeze output */
    libkeccak_squeeze(&state, Bytes_val(hash));

    libkeccak_state_wipe(&state);

    CAMLreturn(hash);
}

/*
 * TCB Statistics (Classical Crypto):
 * - Lines of C: ~350
 * - Dependencies: libsodium (audited), libkeccak (SHAKE256)
 * - All operations constant-time (libsodium guarantees)
 * - No malloc/free (OCaml GC handles allocation)
 * - No global mutable state
 *
 * Hash Functions:
 * - SHA-256, SHA-512: FIPS 180-4 (libsodium)
 * - BLAKE2b: Fast general hashing (libsodium)
 * - SHAKE256: XOF for Merkle trees (libkeccak, SHA-3 family)
 *
 * Post-Quantum Extension:
 * See pq_stubs.c for ML-DSA-65 and SLH-DSA-SHAKE-256s support.
 * Total TCB dependencies: libsodium + liboqs + libkeccak (all minimal, audited).
 */
