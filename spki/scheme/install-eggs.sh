#\!/bin/sh
# Install required eggs for Cyberspace Scheme
set -e

EGGS="srfi-1 srfi-4 srfi-13 srfi-14 srfi-18 srfi-69"

echo "Installing Cyberspace Scheme dependencies..."
for egg in $EGGS; do
    echo "  $egg"
    chicken-install "$egg"
done

echo "Done. Run: cyberspace"
