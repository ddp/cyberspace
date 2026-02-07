#!/bin/bash
# Build the Objective-C bridge shared library for Chez Scheme
# Library of Cyberspace - Chez Port
#
# Produces libobjc-bridge.dylib which Chez loads via load-shared-object.
#
# Usage: ./build-objc-bridge.sh
#
# Copyright (c) 2026 Yoyodyne. See LICENSE.

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
SRC="$SCRIPT_DIR/objc-bridge.m"
OUT="$SCRIPT_DIR/libobjc-bridge.dylib"

# Detect architecture
ARCH=$(uname -m)
echo "Building objc-bridge for $ARCH..."

# Compile
# -shared: produce dylib
# -fobjc-arc: automatic reference counting (matches app/main.m)
# -framework Foundation: NSString, NSArray, NSDictionary, etc.
# -framework Cocoa: NSApplication, NSWindow, NSView (UI)
clang -shared -fobjc-arc \
    -framework Foundation \
    -framework Cocoa \
    -framework WebKit \
    -framework Security \
    -o "$OUT" \
    "$SRC"

echo "Built: $OUT"
echo ""
echo "Test with:"
echo "  cd $SCRIPT_DIR"
echo "  scheme --library-directory . --program test-objc.ss"
