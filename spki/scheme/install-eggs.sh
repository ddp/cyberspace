#!/bin/sh
# Install eggs from vendored local copies - no network required
# "Reflections on Trusting Trust" - freeze production tools
set -e

EGGS_DIR="$(cd "$(dirname "$0")/eggs" && pwd)"
ORIG_DIR="$(pwd)"

for egg in srfi-1 srfi-13 srfi-14 srfi-18 srfi-69; do
    echo "=== Installing $egg ==="
    cd "$EGGS_DIR/$egg"
    chicken-install
    cd "$ORIG_DIR"
done

echo "Done. Run: cyberspace"
