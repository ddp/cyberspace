#!/bin/bash
# Install cyberspace REPL to ~/bin
#
# Compiles the REPL for fast startup, then creates a launcher wrapper.
# The compiled binary runs from the scheme directory to find .so modules.

set -e

SCHEME_DIR="$(cd "$(dirname "$0")" && pwd)"
TARGET="${HOME}/bin/cyberspace"
BINARY="cyberspace-bin"

cd "$SCHEME_DIR"

echo "=== Compiling Cyberspace REPL ==="
echo "Source: repl.scm"
echo ""

# Compile with optimizations
# -O2: Good optimization level
# -d1: Include debugging info for meaningful backtraces
time csc -O2 -d1 repl.scm -o "$BINARY"

echo ""
echo "Compiled: $BINARY ($(du -h "$BINARY" | cut -f1))"

# Create launcher wrapper
mkdir -p "${HOME}/bin"

cat > "$TARGET" << EOF
#!/bin/bash
# Cyberspace REPL launcher (compiled)
cd "$SCHEME_DIR"
exec ./$BINARY "\$@"
EOF

chmod +x "$TARGET"

echo ""
echo "Installed: $TARGET"
echo ""
echo "Make sure ~/bin is in your PATH:"
echo "  export PATH=\"\$HOME/bin:\$PATH\""
echo ""
echo "Usage:"
echo "  cyberspace              # compiled (fast startup)"
echo "  ./repl       # interpreted (for development)"
