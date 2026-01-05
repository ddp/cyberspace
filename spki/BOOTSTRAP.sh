#!/bin/bash
# Bootstrap script for SPKI CLI tools

set -e

echo "SPKI Bootstrap"
echo "=============="
echo

# Check if opam is installed
if ! command -v opam &> /dev/null; then
    echo "Error: opam not found"
    echo "Install with: brew install opam"
    exit 1
fi

echo "✓ opam found"

# Initialize opam if needed
if [ ! -d ~/.opam ]; then
    echo "Initializing opam..."
    opam init --auto-setup
else
    echo "✓ opam initialized"
fi

# Ensure we're using the right opam environment
eval $(opam env)

# Check if dune is installed
if ! command -v dune &> /dev/null; then
    echo "Installing dune..."
    opam install -y dune
else
    echo "✓ dune found"
fi

# Install dependencies
echo "Installing dependencies..."
opam install -y cryptokit base64 alcotest

echo
echo "✓ Bootstrap complete!"
echo
echo "Next steps:"
echo "  make build   # Build SPKI tools"
echo "  make test    # Run tests"
echo "  make install # Install to ~/bin"
echo
echo "Then read CLI-GUIDE.md for usage instructions"
