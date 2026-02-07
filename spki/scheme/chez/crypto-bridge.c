/*
 * crypto-bridge.c - C shim for Chez Scheme crypto-ffi
 * Library of Cyberspace - Chez Port
 *
 * Wraps library APIs that use stack-allocated structs which Chez
 * cannot create via foreign-procedure.  Currently only SHAKE256
 * (via libkeccak).
 *
 * All libsodium functions are called directly from Chez since they
 * use simple pointer/integer arguments.
 *
 * Build: ./build-crypto-bridge.sh
 */

#include <stdlib.h>
#include <string.h>
#include <libkeccak.h>

/*
 * SHAKE256 hash with specified output length.
 *
 * Uses libkeccak's multi-step API:
 *   spec_shake → state_initialise → digest → squeeze → wipe
 *
 * Returns 0 on success, -1 on failure.
 */
int shake256_hash_c(unsigned char *out, size_t outlen,
                    const unsigned char *in, size_t inlen) {
    struct libkeccak_spec spec;
    struct libkeccak_state state;

    libkeccak_spec_shake(&spec, 256, (long)(outlen * 8));

    if (libkeccak_state_initialise(&state, &spec) != 0)
        return -1;

    if (libkeccak_digest(&state, (const char *)in, inlen, 0,
                         LIBKECCAK_SHAKE_SUFFIX, NULL) != 0) {
        libkeccak_state_wipe(&state);
        return -1;
    }

    libkeccak_squeeze(&state, (char *)out);
    libkeccak_state_wipe(&state);
    return 0;
}
