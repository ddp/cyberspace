#!/bin/bash
# Build the crypto bridge shared library for Chez Scheme
# Library of Cyberspace - Chez Port
#
# Produces libcrypto-bridge.dylib wrapping libkeccak for SHAKE256.
# Libsodium functions are called directly from Chez (no bridge needed).
#
# Usage: ./build-crypto-bridge.sh
#
# Copyright (c) 2026 Yoyodyne. See LICENSE.

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
SRC="$SCRIPT_DIR/crypto-bridge.c"
OUT="$SCRIPT_DIR/libcrypto-bridge.dylib"

# Detect Homebrew prefix
if [ -d /opt/homebrew ]; then
    BREW_PREFIX=/opt/homebrew
elif [ -d /usr/local/Homebrew ]; then
    BREW_PREFIX=/usr/local
else
    echo "Warning: Homebrew not found, trying system paths"
    BREW_PREFIX=""
fi

ARCH=$(uname -m)
echo "Building crypto-bridge for $ARCH..."

# Compile
if [ -n "$BREW_PREFIX" ]; then
    cc -shared \
        -I"$BREW_PREFIX/include" \
        -L"$BREW_PREFIX/lib" \
        -lkeccak \
        -o "$OUT" \
        "$SRC"
else
    cc -shared \
        -lkeccak \
        -o "$OUT" \
        "$SRC"
fi

echo "Built: $OUT"
echo ""
echo "Test with:"
echo "  cd $SCRIPT_DIR"
echo "  scheme --libdirs ."
echo "  (import (cyberspace crypto-ffi))"
echo "  (sodium-init)"
