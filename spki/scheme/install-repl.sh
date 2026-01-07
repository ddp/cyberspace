#!/bin/bash
# Install cyberspace-repl to ~/bin
#
# Creates a wrapper that invokes the REPL from the correct directory
# so all the .so modules are found.

SCHEME_DIR="$(cd "$(dirname "$0")" && pwd)"
TARGET="${HOME}/bin/cyberspace"

mkdir -p "${HOME}/bin"

cat > "$TARGET" << EOF
#!/bin/bash
# Cyberspace REPL launcher
cd "$SCHEME_DIR"
exec ./cyberspace-repl "\$@"
EOF

chmod +x "$TARGET"

echo "Installed: $TARGET"
echo ""
echo "Make sure ~/bin is in your PATH:"
echo "  export PATH=\"\$HOME/bin:\$PATH\""
echo ""
echo "Then run: cyberspace"
