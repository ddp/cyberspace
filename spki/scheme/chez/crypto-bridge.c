/*
 * crypto-bridge.c - Minimal C shim for Chez Scheme crypto FFI
 * Library of Cyberspace - Chez Port
 *
 * Most libsodium functions are called directly via foreign-procedure.
 * This shim only contains functions that can't be called directly:
 *   - shake256_hash_c: uses libkeccak struct API
 *
 * Build: clang -shared -lsodium -lkeccak -o libcrypto-bridge.dylib crypto-bridge.c
 *
 * Copyright (c) 2026 Yoyodyne. See LICENSE.
 */

#include <sodium.h>
#include <libkeccak.h>
#include <stdlib.h>
#include <string.h>

/* SHAKE256 hash with specified output length.
   Cannot be called from FFI because libkeccak uses stack-allocated structs. */
int shake256_hash(unsigned char *out, size_t outlen,
                  const unsigned char *in, size_t inlen) {
    struct libkeccak_spec spec;
    struct libkeccak_state state;

    libkeccak_spec_shake(&spec, 256, (long)(outlen * 8));

    if (libkeccak_state_initialise(&state, &spec) != 0)
        return -1;

    if (libkeccak_digest(&state, (const char*)in, inlen, 0,
                         LIBKECCAK_SHAKE_SUFFIX, NULL) != 0) {
        libkeccak_state_wipe(&state);
        return -1;
    }

    libkeccak_squeeze(&state, (char*)out);
    libkeccak_state_wipe(&state);
    return 0;
}
