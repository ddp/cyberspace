#!/bin/sh
# Build TCP bridge shared library for Chez Scheme gossip port.
#
# Usage: ./build-tcp-bridge.sh
#
# Produces: libtcp-bridge.so (Linux) or libtcp-bridge.dylib (macOS)

set -e

OS=$(uname -s)
case "$OS" in
    Darwin)
        EXT="dylib"
        LDFLAGS="-dynamiclib"
        ;;
    Linux)
        EXT="so"
        LDFLAGS="-shared -fPIC"
        ;;
    *)
        echo "Unsupported OS: $OS"
        exit 1
        ;;
esac

cc $LDFLAGS -O2 -o libtcp-bridge.$EXT tcp-bridge.c

echo "Built libtcp-bridge.$EXT"
