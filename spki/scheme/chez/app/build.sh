#!/bin/bash
# Build Cyberspace.app for macOS (Chez Scheme backend)
# Library of Cyberspace - Native GUI Shell
#
# Builds the same Cocoa/WebKit app shell as the Chicken version,
# but bundles the Chez Scheme server and libraries instead.
#
# Copyright (c) 2026 Yoyodyne. See LICENSE.

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
CHEZ_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
DARWIN_DIR="$SCRIPT_DIR/../../darwin/application"
APP_NAME="Cyberspace"
APP_BUNDLE="$DARWIN_DIR/$APP_NAME.app"
CONTENTS="$APP_BUNDLE/Contents"
MACOS="$CONTENTS/MacOS"
RESOURCES="$CONTENTS/Resources"

echo "Building $APP_NAME.app (Chez backend)..."

# Create directory structure
mkdir -p "$MACOS"
mkdir -p "$RESOURCES"

# Compile main.m (shared with Chicken version)
echo "  Compiling main.m..."
clang -fobjc-arc \
    -framework Cocoa \
    -framework WebKit \
    -framework Security \
    -framework GSS \
    -framework UserNotifications \
    -o "$MACOS/$APP_NAME" \
    "$DARWIN_DIR/main.m"

# Copy Info.plist (already in place from directory structure)
if [ ! -f "$CONTENTS/Info.plist" ]; then
    echo "  Warning: Info.plist not found"
fi

# Create PkgInfo
echo -n "APPLCYSM" > "$CONTENTS/PkgInfo"

# Copy app icon
if [ -f "$DARWIN_DIR/Cyberspace.icns" ]; then
    cp "$DARWIN_DIR/Cyberspace.icns" "$RESOURCES/"
    echo "  Copied app icon"
elif [ ! -f "$RESOURCES/Cyberspace.icns" ]; then
    echo "  Note: No app icon (Cyberspace.icns) - using default"
fi

# Copy Chez server script
echo "  Copying Chez server script..."
cp "$SCRIPT_DIR/cyberspace-server.sps" "$RESOURCES/"

# Copy Chez libraries
echo "  Copying Chez libraries..."
mkdir -p "$RESOURCES/cyberspace/chicken-compatibility"
cp "$CHEZ_DIR"/cyberspace/*.sls "$RESOURCES/cyberspace/"
cp "$CHEZ_DIR"/cyberspace/chicken-compatibility/*.sls "$RESOURCES/cyberspace/chicken-compatibility/"

# Copy C bridge dylibs
echo "  Copying C bridges..."
for lib in libcrypto-bridge.dylib libtcp-bridge.dylib; do
    if [ -f "$CHEZ_DIR/$lib" ]; then
        cp "$CHEZ_DIR/$lib" "$RESOURCES/"
        echo "    $lib"
    else
        echo "  Warning: $lib not found in $CHEZ_DIR"
    fi
done

# Remove any stale Chicken artifacts
rm -f "$RESOURCES/cyberspace-server" "$RESOURCES/cyberspace-server.scm"

# Sign for local development (ad-hoc)
echo "  Signing (ad-hoc)..."
codesign --force --deep --sign - "$APP_BUNDLE" 2>/dev/null || true

echo "Done. Run with: open $APP_BUNDLE"
echo ""
echo "Or from command line:"
echo "  $MACOS/$APP_NAME"
