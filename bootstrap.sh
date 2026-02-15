#!/bin/bash
# Bootstrap Cyberspace after git clone
# Builds both macOS native apps from source.
#
# Usage: git clone ... && cd cyberspace && ./bootstrap.sh

set -e

echo "Bootstrapping Cyberspace..."
echo ""

# Build Chicken app (PTY terminal)
if [ -f spki/scheme/chicken/application/build.sh ]; then
    echo "=== Chicken app (PTY terminal) ==="
    (cd spki/scheme/chicken/application && bash build.sh)
    echo ""
fi

# Build Chez app (embedded REPL)
if [ -f spki/scheme/chez/application/build.sh ]; then
    echo "=== Chez app (embedded REPL) ==="
    (cd spki/scheme/chez/application && bash build.sh)
    echo ""
fi

echo "Done. Both apps ready in:"
echo "  spki/scheme/chicken/application/Cyberspace.app"
echo "  spki/scheme/chez/application/Cyberspace.app"
