#!/bin/bash
# Build Cyberspace for Linux
# GTK4 + WebKitGTK + libadwaita
#
# Copyright (c) 2026 Yoyodyne. See LICENSE.

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
BUILD_DIR="$SCRIPT_DIR/build"
APP_NAME="cyberspace"

echo "Building Cyberspace for Linux..."

# Check dependencies
echo "  Checking dependencies..."
for cmd in gcc pkg-config; do
    if ! command -v $cmd &> /dev/null; then
        echo "Error: $cmd not found"
        echo "Install build tools: sudo dnf install gcc pkg-config"
        exit 1
    fi
done

# Check for required libraries
for lib in gtk4 webkit2gtk-4.1 libadwaita-1; do
    if ! pkg-config --exists $lib; then
        echo "Error: $lib not found"
        echo "Install dependencies:"
        echo "  sudo dnf install gtk4-devel webkit2gtk4.1-devel libadwaita-devel"
        exit 1
    fi
done

# Create build directory
mkdir -p "$BUILD_DIR"

# Compile
echo "  Compiling $APP_NAME..."
gcc -o "$BUILD_DIR/$APP_NAME" \
    "$SCRIPT_DIR/main.c" \
    $(pkg-config --cflags --libs gtk4 webkit2gtk-4.1 libadwaita-1) \
    -Wall -Wextra -O2

if [ $? -eq 0 ]; then
    echo "  ✓ Build successful: $BUILD_DIR/$APP_NAME"

    # Make executable
    chmod +x "$BUILD_DIR/$APP_NAME"

    # Show info
    echo ""
    echo "Application built successfully!"
    echo ""
    echo "Run with:"
    echo "  $BUILD_DIR/$APP_NAME"
    echo ""
    echo "Or install system-wide:"
    echo "  sudo ./install.sh"
else
    echo "  ✗ Build failed"
    exit 1
fi
