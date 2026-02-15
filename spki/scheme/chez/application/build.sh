#!/bin/bash
# Build Cyberspace.app for macOS (Chez Scheme backend)
# Library of Cyberspace - Native GUI Shell
#
# Embeds Chez Scheme directly via C bridge (scheme-bridge.c).
# No HTTP server, no WebSocket, no WebView.
#
# Copyright (c) 2026 Yoyodyne. See LICENSE.

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
APP_NAME="Cyberspace"
APP_BUNDLE="$SCRIPT_DIR/$APP_NAME.app"
CONTENTS="$APP_BUNDLE/Contents"
MACOS="$CONTENTS/MacOS"
RESOURCES="$CONTENTS/Resources"

# Chez Scheme paths
CHEZ_LIB="/opt/homebrew/lib"
CHEZ_INCLUDE="/opt/homebrew/Cellar/chezscheme/10.3.0/lib/csv10.3.0/tarm64osx"

echo "Building $APP_NAME.app (Chez Scheme, embedded)..."

# Create directory structure
mkdir -p "$MACOS"
mkdir -p "$RESOURCES"

# Compile the bridge and main
echo "  Compiling scheme-bridge.c..."
clang -c -I"$CHEZ_INCLUDE" -o "$SCRIPT_DIR/scheme-bridge.o" "$SCRIPT_DIR/scheme-bridge.c"

echo "  Compiling main-native.m..."
clang -fobjc-arc \
    -framework Cocoa \
    -I"$CHEZ_INCLUDE" \
    -o "$MACOS/$APP_NAME" \
    "$SCRIPT_DIR/main-native.m" \
    "$SCRIPT_DIR/scheme-bridge.o" \
    "$CHEZ_INCLUDE/libkernel.a" \
    "$CHEZ_INCLUDE/libz.a" \
    "$CHEZ_INCLUDE/liblz4.a" \
    -liconv \
    -lncurses \
    -lm

# Create Info.plist
cat > "$CONTENTS/Info.plist" << 'EOF'
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
    <key>CFBundleExecutable</key>
    <string>Cyberspace</string>
    <key>CFBundleIdentifier</key>
    <string>com.yoyodyne.cyberspace.chez</string>
    <key>CFBundleName</key>
    <string>Cyberspace</string>
    <key>CFBundlePackageType</key>
    <string>APPL</string>
    <key>CFBundleSignature</key>
    <string>CYCZ</string>
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
echo -n "APPLCYCZ" > "$CONTENTS/PkgInfo"

# Copy app icon if available
if [ -f "$SCRIPT_DIR/Cyberspace.icns" ]; then
    cp "$SCRIPT_DIR/Cyberspace.icns" "$RESOURCES/"
    echo "  Copied app icon"
elif [ -f "$SCRIPT_DIR/../../chicken/application/Cyberspace.icns" ]; then
    cp "$SCRIPT_DIR/../../chicken/application/Cyberspace.icns" "$RESOURCES/"
    echo "  Copied app icon from darwin/"
fi

# Copy Chez Scheme boot files
echo "  Copying boot files..."
mkdir -p "$RESOURCES/boot"
cp "$CHEZ_INCLUDE/petite.boot" "$RESOURCES/boot/"
cp "$CHEZ_INCLUDE/scheme.boot" "$RESOURCES/boot/"

# Copy Cyberspace library
echo "  Copying Cyberspace library..."
mkdir -p "$RESOURCES/lib"
cp -r "$SCRIPT_DIR/../cyberspace" "$RESOURCES/lib/"

# Copy native bridges
echo "  Copying native bridges..."
cp "$SCRIPT_DIR/../libcrypto-bridge.dylib" "$RESOURCES/" 2>/dev/null || echo "    (crypto bridge not found)"
cp "$SCRIPT_DIR/../libtcp-bridge.dylib" "$RESOURCES/" 2>/dev/null || echo "    (tcp bridge not found)"

# Sign for local development
echo "  Signing (ad-hoc)..."
codesign --force --deep --sign - "$APP_BUNDLE" 2>/dev/null || true

echo "Done. Run with: open $APP_BUNDLE"
echo ""
echo "Or from command line:"
echo "  $MACOS/$APP_NAME"
