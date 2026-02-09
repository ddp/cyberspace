#!/bin/bash
# Build the post-quantum bridge shared library for Chez Scheme
# Library of Cyberspace - Chez Port
#
# Produces libpq-bridge.dylib wrapping liboqs for SPHINCS+ and ML-DSA.
#
# Usage: ./build-pq-bridge.sh
#
# Requires: brew install liboqs

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
SRC="$SCRIPT_DIR/pq-bridge.c"
OUT="$SCRIPT_DIR/libpq-bridge.dylib"

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
echo "Building pq-bridge for $ARCH..."

# Compile
if [ -n "$BREW_PREFIX" ]; then
    cc -shared \
        -I"$BREW_PREFIX/include" \
        -L"$BREW_PREFIX/lib" \
        -loqs \
        -o "$OUT" \
        "$SRC"
else
    cc -shared \
        -loqs \
        -o "$OUT" \
        "$SRC"
fi

echo "Built: $OUT"
echo ""
echo "Test with:"
echo "  cd $SCRIPT_DIR"
echo "  scheme --libdirs ."
echo "  (import (cyberspace pq-crypto))"
echo "  (pq-init)"
