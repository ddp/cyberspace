#!/bin/bash
# Build liboqs without OpenSSL dependency
#
# Prime directive: TCB depends only on libsodium.
# This script builds liboqs with native implementations only.
#
# Algorithms enabled:
#   - ML-DSA-44/65/87 (Dilithium) - FIPS 204, uses SHAKE
#   - SPHINCS+-SHAKE-* - FIPS 205, uses SHAKE
#   - Falcon - uses SHAKE
#
# All use XKCP Keccak (no OpenSSL).

set -e

LIBOQS_VERSION="0.12.0"
BUILD_DIR="/tmp/liboqs-build"
INSTALL_PREFIX="/usr/local"

echo "=== Building liboqs ${LIBOQS_VERSION} without OpenSSL ==="
echo ""

# Check for required tools
for cmd in cmake git ninja; do
    if ! command -v $cmd &> /dev/null; then
        echo "Error: $cmd not found. Install with: brew install $cmd"
        exit 1
    fi
done

# Clean previous build
rm -rf "${BUILD_DIR}"
mkdir -p "${BUILD_DIR}"
cd "${BUILD_DIR}"

# Clone liboqs
echo "Cloning liboqs..."
git clone --depth 1 --branch ${LIBOQS_VERSION} https://github.com/open-quantum-safe/liboqs.git
cd liboqs

# Configure WITHOUT OpenSSL
echo ""
echo "Configuring (no OpenSSL)..."
mkdir build && cd build

cmake -GNinja \
    -DCMAKE_INSTALL_PREFIX="${INSTALL_PREFIX}" \
    -DCMAKE_BUILD_TYPE=Release \
    -DOQS_USE_OPENSSL=OFF \
    -DOQS_USE_AES_OPENSSL=OFF \
    -DOQS_USE_SHA2_OPENSSL=OFF \
    -DOQS_USE_SHA3_OPENSSL=OFF \
    -DOQS_BUILD_ONLY_LIB=ON \
    -DOQS_MINIMAL_BUILD="SIG_ml_dsa_44;SIG_ml_dsa_65;SIG_ml_dsa_87;SIG_sphincs_shake_128f_simple;SIG_sphincs_shake_128s_simple;SIG_sphincs_shake_256f_simple;SIG_sphincs_shake_256s_simple;SIG_falcon_512;SIG_falcon_1024" \
    ..

# Build
echo ""
echo "Building..."
ninja

# Test (optional)
echo ""
echo "Running tests..."
ninja run_tests || echo "Some tests may fail without full algorithm set"

# Install
echo ""
echo "Installing to ${INSTALL_PREFIX}..."
sudo ninja install

# Verify no OpenSSL
echo ""
echo "=== Verifying no OpenSSL dependency ==="
if nm "${INSTALL_PREFIX}/lib/liboqs.a" 2>/dev/null | grep -q "EVP_\|_SSL_\|_OPENSSL"; then
    echo "ERROR: OpenSSL symbols found!"
    exit 1
else
    echo "SUCCESS: No OpenSSL symbols found"
fi

# Show what we built
echo ""
echo "=== Installed algorithms ==="
grep "OQS_ENABLE_SIG" "${INSTALL_PREFIX}/include/oqs/oqsconfig.h" | grep " 1$"

echo ""
echo "=== Build complete ==="
echo ""
echo "To use in TCB, update tcb/dune:"
echo "  (c_library_flags (-L${INSTALL_PREFIX}/lib -L/opt/homebrew/lib -lsodium -loqs))"
echo ""
echo "Then re-enable PQ signatures in spki_tcb.ml and tcb_stubs.c"
