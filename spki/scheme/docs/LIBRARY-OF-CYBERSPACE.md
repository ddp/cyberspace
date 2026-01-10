# Library of Cyberspace
## Preservation Architecture Documentation

**Version:** 1.0
**Date:** January 2026
**Status:** Sealed and Cataloged

---

## Table of Contents

1. [Overview](#overview)
2. [Architecture](#architecture)
3. [Vault System](#vault-system)
4. [Audit Trail](#audit-trail)
5. [SPKI Integration](#spki-integration)
6. [Progressive Metadata](#progressive-metadata)
7. [Cryptographic Details](#cryptographic-details)
8. [Usage Examples](#usage-examples)
9. [Future-Proof Design](#future-proof-design)

---

## Overview

The **Library of Cyberspace** is a preservation architecture for software artifacts, combining:

- **Cryptographic sealing** (Ed25519 signatures)
- **Content-addressed storage** (SHA-512 hashing)
- **SPKI authorization** (decentralized permissions)
- **Dual-context metadata** (human motivation + machine environment)
- **Future-proof encoding** (S-expressions, self-describing)

### Core Principles

1. **Authenticity** - Cryptographic signatures verify origin
2. **Integrity** - Content-addressing detects tampering
3. **Preservation** - Progressive metadata for future restoration
4. **Discoverability** - Catalog metadata for search and indexing
5. **Offline-first** - No network dependencies for verification

---

## Architecture

```
Library of Cyberspace
├── Vault System (vault.scm)
│   ├── Version Control (Git wrapper)
│   ├── Cryptographic Sealing (Ed25519)
│   ├── Progressive Metadata
│   └── Migration Paths
├── Audit Trail (audit.scm)
│   ├── Content-Addressed Entries
│   ├── Chained Structure
│   ├── SPKI Authorization
│   └── Dual Context
└── SPKI Infrastructure (cert.scm, crypto-ffi.scm)
    ├── Key Generation
    ├── Certificate Creation
    └── Signature Verification
```

### Module Dependency Graph

Build order follows strict topological sort by dependency level:

```
Level 0 ──┬── os ──────────────────────────────┬── Level 1 ──┬── audit ────┐
          ├── crypto-ffi ──────────────────────┤             ├── wordlist ─┼─┐
          ├── sexp ─────────────────┐          │             ├── bloom ────┼─┼─┐
          ├── mdns                  │          │             └── catalog ──┼─┼─┤
          ├── app-bundle            │          │                           │ │ │
          └── codesign              │          │                           │ │ │
                                    └──────────┴── Level 2 ── cert ────────┘ │ │
                                                             enroll ─────────┘ │
                                                             gossip ───────────┘
                                                             security ─────────┤
                                                                    │          │
                                               Level 3 ── vault ────┴──────────┘
```

**Level 0** - No cyberspace module dependencies:
- `os` — OS introspection ("know thyself" - platform, arch, features)
- `crypto-ffi` — libsodium foundation (Ed25519, SHA-512, BLAKE2b)
- `sexp` — S-expression parser/printer
- `mdns` — Local network discovery
- `app-bundle` — macOS .app bundle generation
- `codesign` — macOS code signing and notarization

**Level 1** - Depends on crypto-ffi only:
- `audit` — Tamper-evident logging with content-addressed entries
- `wordlist` — FIPS-181 pronounceable verification codes
- `bloom` — Probabilistic set membership (blocked, counting variants)
- `catalog` — Merkle tree inventory for federation convergence

**Level 2** - Depends on Levels 0+1:
- `cert` — SPKI certificates (← sexp + crypto-ffi)
- `enroll` — Node enrollment and presence (← crypto-ffi + wordlist)
- `gossip` — Anti-entropy gossip protocol (← bloom + catalog + crypto-ffi)
- `security` — Soup security inspector (← cert + sexp + crypto-ffi)

**Level 3** - Full stack:
- `vault` — Cryptographically sealed version control (← cert + crypto-ffi + audit)

### Design Philosophy

The architecture follows these design principles:

- **Semantic versioning over dates** - Versions convey meaning (1.0.0)
- **Explicit over implicit** - Migration paths are declared, not inferred
- **Simple by default** - Minimal metadata unless requested
- **Offline-capable** - All verification works without network
- **Self-describing** - Data explains itself for future systems

---

## Vault System

### Overview

The **Vault** provides cryptographically sealed version control with:

- Better UX than raw Git (inspired by SVN simplicity, Darcs innovations)
- SPKI certificate-based authorization
- First-class archival and restoration
- Migration paths between versions

### The "Seal" Metaphor

Commands use **seal** as the primary verb, connecting:

1. **Cryptographic sealing** - SPKI signatures authenticate versions
2. **Library seals** - Official marks of authenticity (like wax seals on documents)
3. **Vault seals** - Securing archives for preservation

### Core Operations

| Command | Purpose | Example |
|---------|---------|---------|
| `seal-commit` | Create sealed version | `seal commit "Add feature"` |
| `seal-update` | Pull latest changes | `seal update` |
| `seal-undo` | Revert changes | `seal undo --file vault.scm` |
| `seal-history` | View commit log | `seal history --count 20` |
| `seal-branch` | Create branch | `seal branch feature-x` |
| `seal-merge` | Merge branches | `seal merge feature-x` |

### Version Management

| Command | Purpose | Example |
|---------|---------|---------|
| `seal-release` | Create semantic version | `seal release 1.0.0` |
| `seal-verify` | Verify cryptographic seal | `seal verify 1.0.0` |
| `seal-archive` | Create archive | `seal archive 1.0.0 --format cryptographic` |
| `seal-restore` | Restore from archive | `seal restore archive.seal` |
| `seal-migrate` | Execute migration | `seal migrate 1.0.0 2.0.0` |
| `seal-check` | Verify integrity | `seal check --deep` |

### Archive Formats

1. **Tarball** - Standard tar.gz (git archive)
2. **Bundle** - Git bundle with full history
3. **Cryptographic** - Encrypted + SPKI signature

---

## Audit Trail

### Overview

The **Audit Trail** provides tamper-evident logging with:

- Content-addressed entries (SHA-512)
- Chained structure (append-only)
- SPKI authorization tracking
- Cryptographic seals (Ed25519)

### Entry Structure

Every audit entry contains:

```scheme
(audit-entry
  (id "sha512:HASH")              ; Content-addressed ID
  (timestamp "...")                ; Human-readable time
  (sequence N)                     ; Entry number
  (parent-id "sha512:...")         ; Chain to previous entry

  (actor                           ; Who performed action
    (principal #${PUBLIC_KEY})
    (authorization-chain))

  (action                          ; What was done
    (verb seal-commit)
    (object "vault.scm")
    (parameters catalog: #t))

  (context                         ; Why it was done
    (motivation "Add vault system")
    (relates-to "preservation-architecture")
    (language "en"))

  (environment                     ; When/where
    (platform "darwin")
    (timestamp 1767676546))

  (seal                            ; Cryptographic proof
    (algorithm "ed25519-sha512")
    (content-hash "...")
    (signature "...")))
```

### Verification Process

1. **Entry Verification**:
   - Reconstruct unsealed entry
   - Compute SHA-512 hash
   - Compare with stored content-hash
   - Verify Ed25519 signature

2. **Chain Verification**:
   - Verify genesis entry (no parent)
   - For each entry: verify seal + check parent link
   - Confirm append-only property

### Query Interface

```scheme
(audit-by-actor principal)        ; Find entries by actor
(audit-by-action verb)             ; Find entries by action
(audit-by-timerange start end)     ; Find entries in time range
```

---

## SPKI Integration

### Simple Public Key Infrastructure

SPKI provides decentralized authorization without central authorities:

- **Principals** - Public keys (Ed25519)
- **Certificates** - Signed statements about permissions
- **Authorization chains** - Delegatable permissions
- **S-expression encoding** - Future-proof, parseable format

### Key Management

```scheme
;; Generate keypair
(define keys (ed25519-keypair))
(define public-key (car keys))
(define private-key (cadr keys))

;; Save keys
(save-keypair public-key private-key "alice")
```

### Certificate Creation

```scheme
;; Create certificate delegating permission
(define cert
  (make-spki-cert
    issuer: alice-public
    subject: bob-public
    tag: '(seal-commit)
    validity: '((not-before "2026-01-01")
                (not-after "2027-01-01"))
    signing-key: alice-private))
```

### Verification

```scheme
;; Verify signature on sealed release
(seal-verify "1.0.0" verify-key: public-key)

;; Verify audit entry
(audit-verify entry public-key: public-key)
```

---

## Progressive Metadata

The vault supports **three levels** of metadata richness:

### Level 1: Minimal (Default)

Just commit messages. Lightweight and simple.

```scheme
(seal-commit "Fix parser bug")
```

Stores:
- Commit message
- Git metadata (hash, author, timestamp)

### Level 2: Catalog (`--catalog`)

Add discovery metadata for future cataloging systems.

```scheme
(seal-commit "Add search functionality"
  catalog: #t
  subjects: '("search" "indexing")
  keywords: '("full-text" "boolean" "ranked")
  description: "Implements full-text search with boolean operators and relevance ranking")
```

Stores (in `.vault/metadata/HASH.sexp`):
- Subject headings (Library of Congress style)
- Keywords (for search/discovery)
- Extended description

### Level 3: Preserve (`--preserve`)

Full preservation metadata for long-term archival.

```scheme
(seal-commit "Archive stable version"
  preserve: #t
  description: "Snapshot for long-term preservation")
```

Stores:
- **Environment snapshot**: OS, platform, tool versions
- **Dependencies**: Libraries with exact versions
- **Git state**: For exact reproduction

### Metadata File Format

```scheme
(commit-metadata
  (hash "abc123...")
  (timestamp 1767676546)
  (message "Add search functionality")

  (catalog
    (subjects "search" "indexing")
    (keywords "full-text" "boolean" "ranked")
    (description "Implements full-text search..."))

  (preservation
    (environment
      (os "Darwin 25.2.0")
      (scheme "Chicken 5.4.0")
      (libsodium "1.0.19"))
    (dependencies
      ("srfi-1" "list utilities")
      ("srfi-13" "string utilities"))
    (git-state
      (branch "main")
      (remote "origin")
      (clean #t))))
```

---

## Cryptographic Details

### Algorithms

| Purpose | Algorithm | Output Size | Library |
|---------|-----------|-------------|---------|
| Hashing | SHA-512 | 512 bits (64 bytes) | libsodium |
| Signing | Ed25519 | 64 bytes | libsodium |
| Verification | Ed25519 | Boolean | libsodium |

### Algorithm Identifiers

Stored in audit entries and sealed releases:
- `"ed25519-sha512"` - Current algorithm
- Enables future algorithm agility (can add new algorithms)

### Key Format

Keys are stored as **blobs** (binary data):

```scheme
;; Public key: 32 bytes
#${103d452f2add9d27b7a5130ec1710312863f188909581b09ae9fb2fb750123f5}

;; Private key: 64 bytes (contains public key)
#${...128 hex digits...}
```

### Signature Format

Ed25519 signatures are 64 bytes:

```scheme
#${a157ae22c6cf2d3dda62106eec7b9770f9ec177ff7e57e51da9cbd96036029da
   47f0991b56f4fa36e2747074034b33f379726f5e3f35d134e29a601c2ce1800a}
```

### Content-Addressed IDs

IDs are `"sha512:FIRST_32_HEX_DIGITS"`:

```scheme
"sha512:4389c2031b428493e13e96dd1da47e77"
```

Full hash stored in seal for verification.

---

## Usage Examples

### Initializing a New Vault

```scheme
#!/usr/bin/env csi -s

(import vault crypto-ffi)

;; Generate signing keypair
(define keys (ed25519-keypair))
(save-keypair (car keys) (cadr keys) "library")

;; Initialize vault
(vault-init signing-key: (cadr keys))

;; Initialize audit trail
(import audit)
(audit-init signing-key: (cadr keys))
(audit-append
  actor: (car keys)
  action: '(vault-init)
  motivation: "Initialize Library of Cyberspace preservation vault"
  relates-to: "preservation-architecture"
  signing-key: (cadr keys))
```

### Creating a Sealed Release

```scheme
;; Make changes
(seal-commit "Add documentation"
  catalog: #t
  subjects: '("documentation" "hyperspec")
  keywords: '("manual" "reference" "api")
  description: "Complete documentation in man/md/html/hyperspec formats"
  files: '("docs/"))

;; Create sealed release
(seal-release "1.0.0"
  message: "Initial stable release with complete documentation")

;; Verify the seal
(seal-verify "1.0.0")

;; Create cryptographic archive
(seal-archive "1.0.0"
  format: 'cryptographic
  output: "library-1.0.0.seal")

;; Record in audit trail
(audit-append
  actor: public-key
  action: '(seal-release "1.0.0")
  motivation: "First stable release of Library of Cyberspace"
  relates-to: "milestone-v1"
  signing-key: private-key)
```

### Migration Between Versions

```scheme
;; Create new version with migration path
(seal-release "2.0.0" migrate-from: "1.0.0")

;; Edit migration script
;; .vault/migrations/1.0.0-to-2.0.0.scm

;; Test migration
(seal-migrate "1.0.0" "2.0.0" dry-run: #t)

;; Execute migration
(seal-migrate "1.0.0" "2.0.0")

;; Verify integrity
(seal-check deep: #t)
```

### Querying Audit Trail

```scheme
;; Read specific entry
(define entry (audit-read sequence: 1))

;; Verify entry
(audit-verify entry public-key: public-key)

;; Export human-readable trail
(audit-export-human output: "audit-trail.txt")

;; Export S-expressions
(audit-export-sexp output: "audit-trail.sexp")
```

---

## Future-Proof Design

### Why S-Expressions?

1. **Human-readable** - Text format, not binary
2. **Self-describing** - Structure is explicit
3. **Simple to parse** - Recursive descent, no complex grammar
4. **Proven longevity** - Used by Lisp for 60+ years
5. **Language-agnostic** - Parseable by any language

### Why Content-Addressing?

1. **Tamper-evident** - Changes break hash
2. **Self-validating** - Can verify without external data
3. **Location-independent** - ID travels with content
4. **Deduplication** - Same content = same ID

### Why Dual Context?

Each entry records:

1. **Human context** - Why was this done?
   - Motivation
   - Related concepts
   - Natural language

2. **Machine context** - What was the environment?
   - Platform details
   - Tool versions
   - Exact configuration

Future systems can understand **both** the intent and the technical details.

### Why SPKI?

1. **Decentralized** - No certificate authorities needed
2. **Simple** - Public keys are principals
3. **Delegatable** - Authorization can be delegated
4. **Offline-capable** - No network lookups required

### Why Ed25519?

1. **Fast** - Efficient signing and verification
2. **Secure** - 128-bit security level (equivalent to 3072-bit RSA)
3. **Deterministic** - Same message always produces same signature
4. **Small** - 32-byte public keys, 64-byte signatures

---

## References

### Standards

- **SPKI/SDSI** - [RFC 2693](https://www.rfc-editor.org/rfc/rfc2693.html)
- **S-Expressions** - [RFC 2940](https://www.rfc-editor.org/rfc/rfc2940.html)
- **Ed25519** - [RFC 8032](https://www.rfc-editor.org/rfc/rfc8032.html)

### Implementation

- **Chicken Scheme** - [https://call-cc.org/](https://call-cc.org/)
- **libsodium** - [https://libsodium.org/](https://libsodium.org/)

### Inspiration

- **Git** - Content-addressed version control
- **Darcs** - Patch theory and explicit dependencies
- **SVN** - Simple user experience
- **Common Lisp HyperSpec** - Beautiful typeset documentation

---

## License

This is free software; see the source for copying conditions.

**Library of Cyberspace Preservation Architecture**
*Sealing knowledge for future generations*
