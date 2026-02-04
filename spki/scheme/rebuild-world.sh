#!/bin/bash
# Rebuild all Cyberspace modules from scratch
# Usage: ./rebuild-world.sh

set -e
cd "$(dirname "$0")"

echo "Cleaning..."
rm -f *.so *.import.scm repl cs

echo "Building bootstrap modules..."
csc -shared -J tty-ffi.scm
csc -shared -J eggs/lineage/lineage.scm
csc -shared -J edt.scm
csc -shared -J sexp.scm
csc -shared -J os.scm
csc -shared -J fips.scm
csc -shared -J text.scm
csc -shared -J wordlist.scm
csc -shared -J bloom.scm
csc -shared -J display.scm

echo "Building crypto modules..."
csc -shared -J crypto-ffi.scm -I/opt/homebrew/include -L/opt/homebrew/lib -L -lsodium -L -lkeccak
csc -shared -J pq-crypto.scm -I/opt/homebrew/include -L/opt/homebrew/lib -L -loqs -L -lcrypto

echo "Building core modules..."
csc -shared -J cert.scm
csc -shared -J audit.scm
csc -shared -J catalog.scm
csc -shared -J vault.scm
csc -shared -J security.scm
csc -shared -J keyring.scm
csc -shared -J capability.scm
csc -shared -J mdns.scm
csc -shared -J enroll.scm
csc -shared -J gossip.scm
csc -shared -J auto-enroll.scm
csc -shared -J ui.scm
csc -shared -J inspector.scm
csc -shared -J portal.scm
csc -shared -J forum.scm
csc -shared -J info.scm

echo "Building REPL..."
csc -O2 repl.scm -o repl
ln -sf repl cs

echo "Done! Run ./cs or ./repl"
