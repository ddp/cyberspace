/* SPKI TCB - C API Export Stubs for Chicken Scheme
 *
 * These C functions wrap the OCaml TCB and can be called from Chicken Scheme FFI.
 * They provide a stable C ABI boundary between Scheme and the verified OCaml core.
 *
 * Architecture:
 *   Chicken Scheme → C FFI → export_stubs.c → export.ml → signature.ml → libsodium
 */

#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/callback.h>
#include <caml/alloc.h>
#include <string.h>

/* Initialize OCaml runtime and TCB */
static int tcb_initialized = 0;

void spki_tcb_init(void) {
    if (!tcb_initialized) {
        char *argv[] = { "spki_tcb", NULL };
        caml_startup(argv);
        tcb_initialized = 1;
    }
}

/* Generate Ed25519 keypair
 * @param public_key_out: caller-allocated 32-byte buffer
 * @param secret_key_out: caller-allocated 64-byte buffer
 * @return 0 on success, -1 on failure
 */
int spki_tcb_keypair_generate(unsigned char *public_key_out, unsigned char *secret_key_out) {
    CAMLparam0();
    CAMLlocal1(result);

    static value *tcb_keypair_gen = NULL;
    if (tcb_keypair_gen == NULL) {
        tcb_keypair_gen = caml_named_value("tcb_keypair_generate");
    }

    if (tcb_keypair_gen == NULL) {
        CAMLreturnT(int, -1);
    }

    value pk_val = caml_alloc_string(32);
    value sk_val = caml_alloc_string(64);

    int ret = Int_val(caml_callback2(*tcb_keypair_gen, pk_val, sk_val));

    if (ret == 0) {
        memcpy(public_key_out, String_val(pk_val), 32);
        memcpy(secret_key_out, String_val(sk_val), 64);
    }

    CAMLreturnT(int, ret);
}

/* Sign message with Ed25519
 * @param secret_key: 64-byte secret key
 * @param message: message to sign
 * @param message_len: length of message
 * @param signature_out: caller-allocated 64-byte buffer
 * @return 0 on success, -1 on failure
 */
int spki_tcb_sign(const unsigned char *secret_key,
                  const unsigned char *message, int message_len,
                  unsigned char *signature_out) {
    CAMLparam0();
    CAMLlocal4(sk_val, msg_val, sig_val, result);

    static value *tcb_sign_fn = NULL;
    if (tcb_sign_fn == NULL) {
        tcb_sign_fn = caml_named_value("tcb_sign");
    }

    if (tcb_sign_fn == NULL) {
        CAMLreturnT(int, -1);
    }

    sk_val = caml_alloc_string(64);
    memcpy(String_val(sk_val), secret_key, 64);

    msg_val = caml_alloc_string(message_len);
    memcpy(String_val(msg_val), message, message_len);

    sig_val = caml_alloc_string(64);

    result = caml_callback4(*tcb_sign_fn, sk_val, msg_val, Val_int(message_len), sig_val);
    int ret = Int_val(result);

    if (ret == 0) {
        memcpy(signature_out, String_val(sig_val), 64);
    }

    CAMLreturnT(int, ret);
}

/* Verify Ed25519 signature
 * @param public_key: 32-byte public key
 * @param message: message that was signed
 * @param message_len: length of message
 * @param signature: 64-byte signature
 * @return 1 if valid, 0 if invalid, -1 on error
 *
 * TCB CRITICAL: This is the core security guarantee.
 */
int spki_tcb_verify(const unsigned char *public_key,
                    const unsigned char *message, int message_len,
                    const unsigned char *signature) {
    CAMLparam0();
    CAMLlocal4(pk_val, msg_val, sig_val, result);

    static value *tcb_verify_fn = NULL;
    if (tcb_verify_fn == NULL) {
        tcb_verify_fn = caml_named_value("tcb_verify");
    }

    if (tcb_verify_fn == NULL) {
        CAMLreturnT(int, -1);
    }

    pk_val = caml_alloc_string(32);
    memcpy(String_val(pk_val), public_key, 32);

    msg_val = caml_alloc_string(message_len);
    memcpy(String_val(msg_val), message, message_len);

    sig_val = caml_alloc_string(64);
    memcpy(String_val(sig_val), signature, 64);

    result = caml_callback4(*tcb_verify_fn, pk_val, msg_val, Val_int(message_len), sig_val);

    CAMLreturnT(int, Int_val(result));
}

/* Hash data with SHA-256
 * @param data: data to hash
 * @param data_len: length of data
 * @param hash_out: caller-allocated 32-byte buffer
 * @return 0 on success, -1 on failure
 */
int spki_tcb_hash(const unsigned char *data, int data_len, unsigned char *hash_out) {
    CAMLparam0();
    CAMLlocal3(data_val, hash_val, result);

    static value *tcb_hash_fn = NULL;
    if (tcb_hash_fn == NULL) {
        tcb_hash_fn = caml_named_value("tcb_hash");
    }

    if (tcb_hash_fn == NULL) {
        CAMLreturnT(int, -1);
    }

    data_val = caml_alloc_string(data_len);
    memcpy(String_val(data_val), data, data_len);

    hash_val = caml_alloc_string(32);

    result = caml_callback3(*tcb_hash_fn, data_val, Val_int(data_len), hash_val);
    int ret = Int_val(result);

    if (ret == 0) {
        memcpy(hash_out, String_val(hash_val), 32);
    }

    CAMLreturnT(int, ret);
}
