#!/bin/bash
# Install Cyberspace native on current node
# Compiles everything for the local architecture
#
# Usage: ./install-native.sh
#
# Copyright (c) 2026 Yoyodyne. See LICENSE.

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ARCH=$(uname -m)
OS=$(uname -s)
HOST=$(hostname -s)

echo "Installing Cyberspace on $HOST ($ARCH/$OS)"
echo ""

cd "$SCRIPT_DIR"

# Check for Chicken Scheme
if ! command -v csc &> /dev/null; then
    echo "Error: Chicken Scheme (csc) not found"
    echo "Install with: brew install chicken"
    exit 1
fi

# Check for libsodium
if ! pkg-config --exists libsodium 2>/dev/null; then
    if [ ! -f /usr/local/lib/libsodium.a ] && [ ! -f /opt/homebrew/lib/libsodium.a ]; then
        echo "Error: libsodium not found"
        echo "Install with: brew install libsodium"
        exit 1
    fi
fi

echo "1. Compiling modules..."

# Detect libsodium location
if [ -d /opt/homebrew/lib ]; then
    SODIUM_FLAGS="-I/opt/homebrew/include -L/opt/homebrew/lib -L -lsodium"
elif [ -d /usr/local/lib ]; then
    SODIUM_FLAGS="-I/usr/local/include -L/usr/local/lib -L -lsodium"
else
    SODIUM_FLAGS="-L -lsodium"
fi

# Build crypto-ffi first (needs libsodium)
echo "  crypto-ffi..."
csc -shared -J crypto-ffi.scm $SODIUM_FLAGS 2>/dev/null || {
    echo "  Warning: crypto-ffi failed, trying alternate flags..."
    csc -shared -J crypto-ffi.scm -L -lsodium
}

# Build remaining modules in dependency order
MODULES="fips sexp os vault audit cert wordlist mdns bloom catalog enroll gossip security keyring capability auto-enroll ui inspector portal forum display"

for mod in $MODULES; do
    if [ -f "$mod.scm" ]; then
        echo "  $mod..."
        csc -shared -J "$mod.scm" 2>/dev/null || echo "  Warning: $mod skipped"
    fi
done

echo ""
echo "2. Compiling REPL..."
csc -O2 repl.scm -o repl 2>&1 | grep -c "^Warning" | xargs -I{} echo "  ({} warnings)"
ln -sf repl cs 2>/dev/null || true

echo ""
echo "3. Building native app..."
if [ "$OS" = "Darwin" ]; then
    cd app
    ./build.sh

    # Symlink to ~/Applications if it exists
    if [ -d "$HOME/Applications" ]; then
        echo ""
        echo "4. Installing to ~/Applications..."
        ln -sf "$SCRIPT_DIR/app/Cyberspace.app" "$HOME/Applications/Cyberspace.app"
        echo "  ~/Applications/Cyberspace.app -> app bundle"
    fi
    cd ..
else
    echo "  Linux native app: not yet implemented"
fi

echo ""
echo "Done. Cyberspace installed natively on $HOST ($ARCH)"
echo ""
echo "Run with:"
echo "  ./cs              - Terminal REPL"
echo "  open ~/Applications/Cyberspace.app  - GUI (macOS)"
