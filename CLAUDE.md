# CLAUDE.md

This file provides guidance to Claude Code when working with this repository.

## Repository Overview

Cyberspace is a distributed systems research platform combining cryptographic
security, capability-based authorization, and federated replication. Built on
Chicken Scheme with an OCaml trusted computing base, it implements SPKI/SDSI
certificate infrastructure, anti-entropy gossip protocols, and a
cryptographically-sealed vault -- all accessible through an interactive REPL.

**Architect**: ddp@eludom.net / derrell@mit.edu
**Philosophy**: "Peace for all mankind: cooperative computing without enclosure"
**Lineage**: VAXcluster (1984) -> DSSA (1989) -> SPKI (1999) -> Cyberspace (2026)

## Project Structure

```
cyberspace/
  spki/
    scheme/           # Main codebase (~94 Scheme files, ~71K LOC)
      build.scm       # Build system (targets: eggs, library, repl, app, all)
      repl.scm        # Interactive REPL entry point
      docs/notes/     # 61 architectural memos in S-expression format
      app/            # macOS Cyberspace.app
    src/              # OCaml SPKI core library (types, crypto, s-expr parsing)
    bin/              # OCaml executables (spki_cert, spki_keygen, spki_show, spki_verify)
    test/             # OCaml tests (alcotest + qcheck-core)
    coq/              # Rocq formal proofs for TCB components
    Makefile          # OCaml build: make build|test|install|clean
  implementations/    # Reference crypto implementations (ChaCha20, Poly1305, Merkle, Lamport)
  api/                # RESTful HTTP server (Spiffy + intarweb)
  library/            # 312+ research PDFs organized by topic (~968 MB)
  bin/                # Utility scripts (sync, metrics, generate-library-index)
  .emacs              # Emacs configuration (~700 lines)
  .zshrc              # Zsh configuration (~250 lines)
```

## Build Commands

### Scheme (primary codebase)

```bash
cd spki/scheme
./build.scm all          # Build everything (eggs, library, repl)
./build.scm repl         # Build REPL only
./build.scm library      # Build all library modules (.so files)
./build.scm eggs         # Install Chicken egg dependencies
```

Module compilation order is defined in build.scm with 10 dependency levels
(Level 0: sexp, tty-ffi, os -> Level 10: forum, seal, forge, cyberspace).

### OCaml (trusted computing base)

```bash
cd spki
make build               # dune build
make test                # dune runtest (alcotest + qcheck-core)
make install             # Install tools to ~/bin
dune build @fmt --auto-promote   # Format OCaml code
```

### Running the REPL

```bash
./spki/scheme/repl       # or ./cs (symlink)
# Options: --sync, --clean, --rebuild, --boot=<level>, --eval='<expr>'
```

### Tests

```bash
# OCaml
cd spki && dune runtest --verbose

# Scheme (individual test files)
csi -s spki/scheme/test-sexp.scm
csi -s spki/scheme/test-sodium.scm
csi -s spki/scheme/test-shamir.scm
csi -s spki/scheme/test-vault-simple.scm

# Cluster test (two terminals)
# Terminal 1: ./spki/scheme/test-cluster.sh alpha 4433
# Terminal 2: ./spki/scheme/test-cluster.sh beta 4434 localhost 4433

# API
cd api && ./test-api.sh
```

## Key Subsystems

### Cryptography (crypto-ffi.scm, pq-crypto.scm)
- Ed25519 signatures, X25519 key exchange via libsodium FFI
- ChaCha20-Poly1305 AEAD, SHA-512, BLAKE2b
- ML-DSA-65 post-quantum signatures via liboqs FFI
- FIPS randomness self-tests (fips.scm)

### SPKI/SDSI Certificates (cert.scm, capability.scm)
- S-expression encoded authorization certificates
- Direct delegation (no CA hierarchy)
- Certificate chain validation and tag intersection
- Capability-based access control

### Vault (vault.scm)
- Cryptographically sealed version control
- Operations: seal-commit, seal-release, seal-archive, seal-verify
- Newton-style soup: transient queryable object workspace
- Merkle tree verification for integrity

### Gossip Protocol (gossip.scm)
- Three-layer anti-entropy convergence (Memo-0010):
  1. Bloom filter exchange (fast, approximate)
  2. Merkle tree diff (precise, logarithmic)
  3. Object transfer (actual data)
- Lamport-timestamped I/O
- mDNS peer discovery (mdns.scm)

### Auto-Enrollment (auto-enroll.scm, enroll.scm)
- mDNS/Bonjour node discovery
- Capability-based master election ("most capable wins")
- Hardware introspection and scoring
- SPKI certificate issuance for enrolled nodes

### Forge (forge.scm)
- Markov chain pronounceable password generator
- Heritage: Derrell Piper & Jon Callas, VAX/VMS 6.0 (~1991)
- 50+ language digraph databases
- Entropy tracking in decibits

### Audit (audit.scm)
- Tamper-evident hash-chained audit trails
- Bloom filters for gossip convergence (bloom.scm)

### Keyring (keyring.scm)
- Key material management
- Hardware attestation
- Sealed secrets

## Trusted Computing Base (TCB)

**Principle**: "If it's in the TCB, it's in OCaml. Otherwise it's in Scheme."

- OCaml: ~3,600 lines (signature verification, crypto primitives)
- C FFI: ~960 lines (libsodium, liboqs, libkeccak bindings)
- Rocq proofs: ~1,260 lines (formal verification)
- Total: ~5,800 lines

External dependencies: libsodium (audited), liboqs (no OpenSSL), libkeccak

## Dependencies

### OCaml (spki.opam)
- OCaml >= 4.14, Dune >= 3.0
- base64 >= 3.5.0, conf-libsodium >= 1
- alcotest, qcheck-core (testing), odoc (docs)

### Chicken Scheme
- srfi-1, srfi-4, srfi-13, srfi-14, srfi-18, srfi-69
- spiffy, intarweb, uri-common, medea (HTTP/JSON)
- tty-ffi, lineage (terminal/line editing)

## Code Conventions

### Scheme
- Classic Lisp style: lowercase with hyphens, 2-space indentation
- Chicken module system with explicit exports
- `;;` for section headers, `;` for inline comments
- Constant-time operations for crypto (no secret-dependent branches)
- S-expressions as universal data format

### OCaml
- 2-space indentation, explicit type annotations
- Pattern matching over if/then/else
- Module-based organization, functional style (immutability preferred)
- Format with `dune build @fmt --auto-promote`

### Elisp
- 4-space indentation, `ddp-` namespace prefix
- Lexical binding enabled, 72-column fill
- `try-require` for optional packages, `with-eval-after-load` for deferred config

## Architectural Memos

61 memos in `spki/scheme/docs/notes/` define the system architecture. Key ones:

- **Memo-0002**: Architecture (VAXcluster lineage, TCB strategy)
- **Memo-0003**: SPKI Authorization
- **Memo-0005**: Audit Trail
- **Memo-0006**: Vault Architecture
- **Memo-0007**: Replication Layer
- **Memo-0010**: Metadata Levels (gossip convergence layers)
- **Memo-0012**: Federation
- **Memo-0013**: Byzantine Consensus
- **Memo-0037**: Mobile Agents
- **Memo-0045**: Security Architecture
- **Memo-0047**: Quantum-Resistant Merkle Trees
- **Memo-0052**: Compilation
- **Memo-0059**: Quantum-Day Migration

## Dotfile Configuration

`.emacs` and `.zshrc` are designed to be symlinked from `~`:

```bash
ln -s ~/cyberspace/.emacs ~/.emacs
ln -s ~/cyberspace/.zshrc ~/.zshrc
```

Key Emacs features: SLY (Common Lisp), tuareg + merlin (OCaml), paredit
(Scheme), custom keymap (`C-c d` prefix), TRAMP multi-hop SSH.

## Library Index

312+ research PDFs in `library/`. Regenerate the permuted KWIC index after
adding documents:

```bash
bin/generate-library-index
```

## Important Notes

- Private keys never exposed to the Librarian (sign via subprocess)
- Master key in API server is a placeholder -- change in production
- The REPL has two modes: command mode (English verbs) and Scheme mode (full power)
- `bin/sync` is the global synchronization primitive; resolves master from
  env var, config file, or defaults to fluffy.eludom.net
- Memo-0060 is the user's dissertation notes -- DO NOT EDIT
