#!/bin/bash
# Build Cyberspace.app for macOS
# Library of Cyberspace - Native GUI Shell
#
# Copyright (c) 2026 Yoyodyne. See LICENSE.

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
APP_NAME="Cyberspace"
APP_BUNDLE="$SCRIPT_DIR/$APP_NAME.app"
CONTENTS="$APP_BUNDLE/Contents"
MACOS="$CONTENTS/MacOS"
RESOURCES="$CONTENTS/Resources"

echo "Building $APP_NAME.app..."

# Create directory structure
mkdir -p "$MACOS"
mkdir -p "$RESOURCES"

# Compile main.m
echo "  Compiling main.m..."
clang -fobjc-arc \
    -framework Cocoa \
    -framework WebKit \
    -framework Security \
    -framework GSS \
    -framework UserNotifications \
    -o "$MACOS/$APP_NAME" \
    "$SCRIPT_DIR/main.m"

# Copy Info.plist (already in place from directory structure)
if [ ! -f "$CONTENTS/Info.plist" ]; then
    echo "  Warning: Info.plist not found"
fi

# Create PkgInfo
echo -n "APPLCYSM" > "$CONTENTS/PkgInfo"

# Copy app icon
if [ -f "$SCRIPT_DIR/Cyberspace.icns" ]; then
    cp "$SCRIPT_DIR/Cyberspace.icns" "$RESOURCES/"
    echo "  Copied app icon"
elif [ ! -f "$RESOURCES/Cyberspace.icns" ]; then
    echo "  Note: No app icon (Cyberspace.icns) - using default"
fi

# Copy Scheme server — prefer Chez, fall back to Chicken
SCHEME_DIR="$SCRIPT_DIR/../.."
CHEZ_DIR="$SCHEME_DIR/chez"

if [ -f "$CHEZ_DIR/app/cyberspace-server.sps" ]; then
    echo "  Bundling Chez backend..."
    cp "$CHEZ_DIR/app/cyberspace-server.sps" "$RESOURCES/"

    # Copy Chez libraries
    mkdir -p "$RESOURCES/cyberspace/chicken-compatibility"
    cp "$CHEZ_DIR"/cyberspace/*.sls "$RESOURCES/cyberspace/"
    cp "$CHEZ_DIR"/cyberspace/chicken-compatibility/*.sls "$RESOURCES/cyberspace/chicken-compatibility/"

    # Copy C bridge dylibs
    for lib in libcrypto-bridge.dylib libtcp-bridge.dylib; do
        [ -f "$CHEZ_DIR/$lib" ] && cp "$CHEZ_DIR/$lib" "$RESOURCES/"
    done

elif [ -f "$SCHEME_DIR/server.scm" ]; then
    echo "  Bundling Chicken backend..."
    cp "$SCHEME_DIR/server.scm" "$RESOURCES/cyberspace-server.scm"

    # Try to compile if csc is available
    if command -v csc &> /dev/null; then
        echo "  Compiling cyberspace-server..."
        cd "$SCHEME_DIR"
        csc -O2 -o "$RESOURCES/cyberspace-server" server.scm 2>/dev/null || {
            echo "  Note: Server compilation skipped (will use interpreted)"
        }
        cd "$SCRIPT_DIR"
    fi
fi

# Sign for local development (ad-hoc)
echo "  Signing (ad-hoc)..."
codesign --force --deep --sign - "$APP_BUNDLE" 2>/dev/null || true

echo "Done. Run with: open $APP_BUNDLE"
echo ""
echo "Or from command line:"
echo "  $MACOS/$APP_NAME"
