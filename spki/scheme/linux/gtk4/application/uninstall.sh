#!/bin/bash
# Uninstall Cyberspace from Linux
#
# Copyright (c) 2026 Yoyodyne. See LICENSE.

set -e

PREFIX="${PREFIX:-/usr/local}"
APP_NAME="cyberspace"

echo "Uninstalling Cyberspace from $PREFIX..."

# Check for root/sudo
if [ "$EUID" -ne 0 ]; then
    echo "Error: This script must be run as root (use sudo)"
    exit 1
fi

# Remove files
rm -f "$PREFIX/bin/$APP_NAME"
rm -rf "$PREFIX/share/$APP_NAME"
rm -f "$PREFIX/share/applications/cyberspace.desktop"
rm -f "$PREFIX/share/icons/hicolor/scalable/apps/com.yoyodyne.cyberspace.svg"

# Update caches
if command -v update-desktop-database &> /dev/null; then
    update-desktop-database -q "$PREFIX/share/applications"
fi

if command -v gtk-update-icon-cache &> /dev/null; then
    gtk-update-icon-cache -q "$PREFIX/share/icons/hicolor"
fi

echo "✓ Uninstalled successfully"
