#!/bin/bash
# Install Cyberspace system-wide on Linux
# Installs to /usr/local by default
#
# Copyright (c) 2026 Yoyodyne. See LICENSE.

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
CHEZ_DIR="$SCRIPT_DIR/../../chez"
PREFIX="${PREFIX:-/usr/local}"

APP_NAME="cyberspace"
BIN_DIR="$PREFIX/bin"
SHARE_DIR="$PREFIX/share/$APP_NAME"
DESKTOP_DIR="$PREFIX/share/applications"
ICON_DIR="$PREFIX/share/icons/hicolor"

echo "Installing Cyberspace to $PREFIX..."

# Check if built
if [ ! -f "$SCRIPT_DIR/build/$APP_NAME" ]; then
    echo "Error: Application not built. Run ./build.sh first"
    exit 1
fi

# Check for root/sudo
if [ "$EUID" -ne 0 ]; then
    echo "Error: This script must be run as root (use sudo)"
    exit 1
fi

# Create directories
echo "  Creating directories..."
mkdir -p "$BIN_DIR"
mkdir -p "$SHARE_DIR"
mkdir -p "$DESKTOP_DIR"

# Install binary
echo "  Installing binary..."
install -m 755 "$SCRIPT_DIR/build/$APP_NAME" "$BIN_DIR/"

# Install Chez Scheme server and libraries
echo "  Installing Chez Scheme backend..."
if [ -d "$CHEZ_DIR/application" ]; then
    cp "$CHEZ_DIR/application/cyberspace-server.sps" "$SHARE_DIR/"
    mkdir -p "$SHARE_DIR/cyberspace"
    cp -r "$CHEZ_DIR/cyberspace/"*.sls "$SHARE_DIR/cyberspace/" 2>/dev/null || true

    # Copy compatibility layer
    if [ -d "$CHEZ_DIR/cyberspace/chicken-compatibility" ]; then
        mkdir -p "$SHARE_DIR/cyberspace/chicken-compatibility"
        cp "$CHEZ_DIR/cyberspace/chicken-compatibility/"*.sls \
           "$SHARE_DIR/cyberspace/chicken-compatibility/" 2>/dev/null || true
    fi

    # Copy FFI bridges
    for lib in libcrypto-bridge.so libtcp-bridge.so; do
        if [ -f "$CHEZ_DIR/$lib" ]; then
            cp "$CHEZ_DIR/$lib" "$SHARE_DIR/"
        fi
    done
fi

# Install desktop file
echo "  Installing desktop entry..."
install -m 644 "$SCRIPT_DIR/cyberspace.desktop" "$DESKTOP_DIR/"

# Update desktop database
if command -v update-desktop-database &> /dev/null; then
    update-desktop-database -q "$DESKTOP_DIR"
fi

# Install icon (if available)
if [ -f "$SCRIPT_DIR/cyberspace.svg" ]; then
    echo "  Installing icon..."
    mkdir -p "$ICON_DIR/scalable/apps"
    cp "$SCRIPT_DIR/cyberspace.svg" "$ICON_DIR/scalable/apps/com.yoyodyne.cyberspace.svg"

    if command -v gtk-update-icon-cache &> /dev/null; then
        gtk-update-icon-cache -q "$ICON_DIR"
    fi
fi

echo ""
echo "✓ Installation complete!"
echo ""
echo "Run from terminal:"
echo "  $APP_NAME"
echo ""
echo "Or launch from application menu:"
echo "  Activities → Cyberspace"
echo ""
echo "Uninstall with:"
echo "  sudo ./uninstall.sh"
