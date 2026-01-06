/* SPKI TCB - libsodium FFI Stubs
 *
 * C bindings to libsodium for Ed25519 operations.
 * These are the only crypto operations in the TCB.
 */

#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/fail.h>
#include <sodium.h>
#include <string.h>

/* Initialize libsodium */
CAMLprim value caml_sodium_init(value unit) {
    CAMLparam1(unit);
    CAMLreturn(Val_int(sodium_init()));
}

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
        (unsigned char*)String_val(pk),
        (unsigned char*)String_val(sk)
    );

    result = caml_alloc_tuple(2);
    Store_field(result, 0, pk);
    Store_field(result, 1, sk);

    CAMLreturn(result);
}

/* Sign message with Ed25519
 * @param secret_key: 64 bytes
 * @param message: arbitrary length
 * @return signature: 64 bytes (crypto_sign_BYTES)
 */
CAMLprim value caml_ed25519_sign(value secret_key, value message) {
    CAMLparam2(secret_key, message);
    CAMLlocal1(signature);

    unsigned long long sig_len;
    signature = caml_alloc_string(crypto_sign_BYTES);

    crypto_sign_detached(
        (unsigned char*)String_val(signature),
        &sig_len,
        (const unsigned char*)String_val(message),
        caml_string_length(message),
        (const unsigned char*)String_val(secret_key)
    );

    CAMLreturn(signature);
}

/* Verify Ed25519 signature
 * @param public_key: 32 bytes
 * @param message: arbitrary length
 * @param signature: 64 bytes
 * @return bool: true if valid, false otherwise
 *
 * TCB CRITICAL: This is the core security guarantee.
 * If this returns true, the signature was created by holder of private key.
 */
CAMLprim value caml_ed25519_verify(value public_key, value message, value signature) {
    CAMLparam3(public_key, message, signature);

    int result = crypto_sign_verify_detached(
        (const unsigned char*)String_val(signature),
        (const unsigned char*)String_val(message),
        caml_string_length(message),
        (const unsigned char*)String_val(public_key)
    );

    /* crypto_sign_verify_detached returns 0 on success, -1 on failure */
    CAMLreturn(Val_bool(result == 0));
}

/* Compute SHA-512 hash
 * @param data: arbitrary length
 * @return hash: 64 bytes (crypto_hash_sha512_BYTES)
 */
CAMLprim value caml_sha512_hash(value data) {
    CAMLparam1(data);
    CAMLlocal1(hash);

    hash = caml_alloc_string(crypto_hash_sha512_BYTES);

    crypto_hash_sha512(
        (unsigned char*)String_val(hash),
        (const unsigned char*)String_val(data),
        caml_string_length(data)
    );

    CAMLreturn(hash);
}

/*
 * TCB Size: ~100 lines of C
 * Dependencies: libsodium only
 * Security: All operations constant-time (libsodium guarantees)
 */
