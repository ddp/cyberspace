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
    -o "$MACOS/$APP_NAME" \
    "$SCRIPT_DIR/main.m"

# Copy Info.plist (already in place from directory structure)
if [ ! -f "$CONTENTS/Info.plist" ]; then
    echo "  Warning: Info.plist not found"
fi

# Create PkgInfo
echo -n "APPLCYCK" > "$CONTENTS/PkgInfo"

# Copy app icon
if [ -f "$SCRIPT_DIR/Cyberspace.icns" ]; then
    cp "$SCRIPT_DIR/Cyberspace.icns" "$RESOURCES/"
    echo "  Copied app icon"
elif [ ! -f "$RESOURCES/Cyberspace.icns" ]; then
    echo "  Note: No app icon (Cyberspace.icns) - using default"
fi

# Note: App uses PTY connection to Chicken REPL (cs), no bundled server needed
echo "  Native PTY app - no server bundling needed"

# Sign for local development (ad-hoc with entitlements)
echo "  Signing (ad-hoc with entitlements)..."
if [ -f "$SCRIPT_DIR/Cyberspace.entitlements" ]; then
    codesign --force --deep --sign - --entitlements "$SCRIPT_DIR/Cyberspace.entitlements" "$APP_BUNDLE" 2>/dev/null || true
else
    codesign --force --deep --sign - "$APP_BUNDLE" 2>/dev/null || true
fi

echo "Done. Run with: open $APP_BUNDLE"
echo ""
echo "Or from command line:"
echo "  $MACOS/$APP_NAME"
