#!/bin/bash
# Build libcrypto-bridge.dylib for Chez Scheme crypto FFI
# Library of Cyberspace - Chez Port
#
# This builds the minimal C shim containing only functions that can't
# be called directly via foreign-procedure (SHAKE256 uses libkeccak structs).
#
# Most libsodium functions are called directly -- no bridge needed.

set -e

cd "$(dirname "$0")"

echo "Building libcrypto-bridge.dylib..."
clang -shared -o libcrypto-bridge.dylib \
    -lsodium -lkeccak \
    crypto-bridge.c

echo "Done: libcrypto-bridge.dylib"
ls -la libcrypto-bridge.dylib
