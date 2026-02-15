#!/bin/bash
# Build Cyberspace.app for macOS (Chicken Scheme backend)
# Library of Cyberspace - Native PTY Shell
#
# Creates the entire .app bundle from scratch.
# App connects to Chicken REPL (cs) via PTY.
#
# Copyright (c) 2026 Yoyodyne. See LICENSE.

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
APP_NAME="Cyberspace"
APP_BUNDLE="$SCRIPT_DIR/$APP_NAME.app"
CONTENTS="$APP_BUNDLE/Contents"
MACOS="$CONTENTS/MacOS"
RESOURCES="$CONTENTS/Resources"

echo "Building $APP_NAME.app (Chicken, PTY)..."

# Create directory structure
mkdir -p "$MACOS"
mkdir -p "$RESOURCES"

# Compile main.m
echo "  Compiling main.m..."
clang -fobjc-arc \
    -framework Cocoa \
    -o "$MACOS/$APP_NAME" \
    "$SCRIPT_DIR/main.m"

# Create Info.plist
cat > "$CONTENTS/Info.plist" << 'EOF'
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
    <key>CFBundleExecutable</key>
    <string>Cyberspace</string>
    <key>CFBundleIdentifier</key>
    <string>net.eludom.cyberspace</string>
    <key>CFBundleName</key>
    <string>Cyberspace</string>
    <key>CFBundlePackageType</key>
    <string>APPL</string>
    <key>CFBundleSignature</key>
    <string>CYCK</string>
    <key>CFBundleShortVersionString</key>
    <string>0.9.12</string>
    <key>CFBundleVersion</key>
    <string>1</string>
    <key>LSMinimumSystemVersion</key>
    <string>10.14</string>
    <key>NSHighResolutionCapable</key>
    <true/>
    <key>CFBundleIconFile</key>
    <string>Cyberspace</string>
    <key>NSPrincipalClass</key>
    <string>NSApplication</string>
</dict>
</plist>
EOF

# Create PkgInfo
echo -n "APPLCYCK" > "$CONTENTS/PkgInfo"

# Copy app icon
if [ -f "$SCRIPT_DIR/Cyberspace.icns" ]; then
    cp "$SCRIPT_DIR/Cyberspace.icns" "$RESOURCES/"
    echo "  Copied app icon"
else
    echo "  Note: No app icon (Cyberspace.icns) - using default"
fi

# Sign for local development (ad-hoc with entitlements)
echo "  Signing (ad-hoc with entitlements)..."
if [ -f "$SCRIPT_DIR/Cyberspace.entitlements" ]; then
    codesign --force --deep --sign - --entitlements "$SCRIPT_DIR/Cyberspace.entitlements" "$APP_BUNDLE" 2>/dev/null || true
else
    codesign --force --deep --sign - "$APP_BUNDLE" 2>/dev/null || true
fi

echo "Done. Run with: open $APP_BUNDLE"
