#!/bin/sh
# Install eggs from vendored local copies - no network required
# "Reflections on Trusting Trust" - freeze production tools
# Order matters: dependencies first
set -e

EGGS_DIR="$(cd "$(dirname "$0")/eggs" && pwd)"
ORIG_DIR="$(pwd)"

# srfi-14 before srfi-13 (srfi-13 depends on srfi-14)
for egg in srfi-14 srfi-1 srfi-13 srfi-18 srfi-69; do
    echo "=== Installing $egg ==="
    cd "$EGGS_DIR/$egg"
    chicken-install -no-install-dependencies
    cd "$ORIG_DIR"
done

echo "Done. Run: cyberspace"
