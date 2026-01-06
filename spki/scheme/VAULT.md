# Vault - Cryptographically Sealed Version Control

A higher-level interface to version control with integrated SPKI-based cryptographic sealing.

## Philosophy

The **seal** metaphor connects three concepts:
- **Cryptographic sealing** - SPKI signatures verify authenticity
- **Library seals** - Official marks of authenticity for the Library of Cyberspace
- **Vault seals** - Securing archives for preservation

## Design Principles

### 1. Simplicity over Git's Complexity

**Git problems:**
- `git checkout` does 3+ different things
- `git reset --soft/--mixed/--hard` - cryptic flags
- HEAD, index, staging, working tree - too many concepts
- SHA hashes are not human-friendly version identifiers

**Vault solutions:**
- Single-purpose commands with clear verbs
- Semantic version numbers (1.0.0) instead of SHA hashes
- Staging happens automatically on commit
- Clear undo semantics

### 2. Integrated Version Management

Unlike git tags (which are just pointers), Vault has first-class versions:
- Semantic versioning enforced (MAJOR.MINOR.PATCH)
- Cryptographic signatures on releases (SPKI certificates)
- Migration paths between versions
- Compliance tracking for implementations

### 3. Archival as First-Class

Not an afterthought - archiving is built-in:
- Multiple formats: tarball, git-bundle, cryptographic
- Cryptographic seals include tamper-evident hashes
- Restoration is verified against seals
- Archives include version provenance

### 4. Authorization via SPKI

Who can publish versions? SPKI certificates provide:
- Key-based authorization for releases
- Delegation chains (Alice authorizes Bob to publish)
- Revocation support
- Tag-based permissions (who can release what)

## Command Reference

### Core Operations

**Simple Mode (default - no metadata burden):**
```bash
# Just like git, quick and simple
seal commit "Add feature X"
seal commit "Fix bug" file1.scm file2.scm
```

**Catalog Mode (discoverable):**
```bash
# Add discovery metadata for library releases
seal commit "Add crypto module" --catalog \
  --subjects cryptography,SPKI \
  --keywords Ed25519,signatures \
  --description "Ed25519 signatures via libsodium"
```

**Preservation Mode (future-proof):**
```bash
# Full metadata for offline migration and long-term preservation
seal commit "Major refactoring" --preserve \
  --catalog \
  --subjects architecture,refactoring \
  --description "Restructure for better modularity"
# Captures: environment, dependencies, git state
```

**More examples:**
```bash

# Update from origin (like git pull)
seal update

# Undo changes
seal undo                    # Undo last commit
seal undo --hard            # Discard all changes
seal undo file.scm          # Restore single file

# View history (clear formatting)
seal history
seal history --count 20

# Branch operations
seal branch feature-x
seal branch hotfix --from v1.0.0
seal merge feature-x
```

### Version Management

```bash
# Create sealed release (enforces semantic versioning)
seal release 1.0.0 --message "Initial stable release"

# Create release with migration tracking
seal release 2.0.0 --migrate-from 1.0.0

# Verify cryptographic seal
seal verify 1.0.0

# Check all sealed releases
seal check --deep
```

### Archival and Restoration

```bash
# Create different archive types
seal archive 1.0.0                              # Default (tarball)
seal archive 1.0.0 --format bundle              # Git bundle
seal archive 1.0.0 --format cryptographic       # With SPKI seal

# Restore from archive
seal restore vault-1.0.0.archive
seal restore vault-1.0.0.archive --target /path/to/restore
```

### Migration Paths

```bash
# Create migration script template
seal release 2.0.0 --migrate-from 1.0.0
# Creates: migrations/1.0.0-to-2.0.0.scm

# Run migration
seal migrate 1.0.0 2.0.0
seal migrate 1.0.0 2.0.0 --dry-run              # Test first
seal migrate 1.0.0 2.0.0 --script custom.scm    # Custom script
```

### Configuration

```bash
# Initialize vault with signing key
seal init --signing-key alice.private

# Configuration stored in .vault/config
```

## Metadata Formats

### Minimal (default)
No extra metadata files created. Just standard git commit:
```
git log shows:
commit 410ce866d8a9...
Author: Alice <alice@example.org>
Date: Mon Jan 5 20:30:00 2026

    Fix bug in parser
```

### Catalog Mode
Creates `.vault/metadata/<hash>.sexp`:
```scheme
(commit-metadata
  (hash "410ce866d8a9...")
  (timestamp 1736132045)
  (message "Add crypto module")
  (catalog
    (subjects "cryptography" "SPKI")
    (keywords "Ed25519" "signatures")
    (description "Ed25519 signatures via libsodium")))
```

### Preservation Mode
Creates comprehensive metadata:
```scheme
(commit-metadata
  (hash "410ce866d8a9...")
  (timestamp 1736132045)
  (message "Major refactoring")
  (catalog
    (subjects "architecture" "refactoring")
    (description "Restructure for better modularity"))
  (preservation
    (environment
      (platform "darwin")
      (hostname "alice-laptop")
      (chicken-version "5.3.0")
      (timestamp 1736132045))
    (dependencies
      ("libsodium" "1.0.18"))
    (git-state
      (branch "main")
      (remote "origin git@github.com:alice/project.git"))))
```

## Sealed Archive Format

Cryptographic archives include:
```scheme
(sealed-archive
  (version "1.0.0")
  (format cryptographic)
  (tarball "vault-1.0.0.tar.gz")
  (hash "9bb2174e57cf2729...")     ; SHA-512 of tarball
  (signature "dfcea22a8fdfc..."))   ; Ed25519 signature
```

On restoration, the system:
1. Verifies hash matches tarball
2. Verifies signature with public key
3. Extracts only if verification passes

## Migration Scripts

Migration scripts are Scheme programs that transform data between versions:

```scheme
;;; Migration: 1.0.0 -> 2.0.0
;;; Generated: 1736132045

(define (migrate-1.0.0-to-2.0.0)
  ;; Example: rename old format to new format
  (when (file-exists? "old-config.scm")
    (rename-file "old-config.scm" "config.scm"))

  ;; Example: transform data structure
  (let ((old-data (read-data "data.scm")))
    (write-data "data.scm" (transform-schema old-data)))

  #t)

(migrate-1.0.0-to-2.0.0)
```

## SPKI Integration

### Signing Releases

When a signing key is configured, releases are automatically sealed:

```bash
seal init --signing-key alice.private
seal release 1.0.0 --message "First release"
```

Creates `.vault/releases/1.0.0.sig`:
```scheme
(signature
  (version "1.0.0")
  (hash "410ce866d8a9...")
  (manifest "(release \"1.0.0\" \"410ce866\" 1736132045)")
  (signature #${...}))  ; Ed25519 signature blob
```

### Verifying Releases

```bash
seal verify 1.0.0 --verify-key alice.public
# ✓ Release seal verified: 1.0.0
```

### Delegation Example

Alice can authorize Bob to sign releases:

```bash
# Alice creates delegation certificate
spki-cert --issuer alice.private \
          --subject bob.public \
          --tag "(release (version *))" \
          --propagate

# Bob can now sign releases
seal init --signing-key bob.private
seal release 2.0.0
```

## Comparison to Other Systems

| Feature | git | svn | darcs | vault |
|---------|-----|-----|-------|-------|
| Simple commands | ✗ | ✓ | ~ | ✓ |
| Human version IDs | ✗ | ✓ | ✗ | ✓ |
| Cryptographic signing | ~ | ✗ | ✗ | ✓ |
| First-class archives | ✗ | ✗ | ✗ | ✓ |
| Migration paths | ✗ | ✗ | ✗ | ✓ |
| Patch algebra | ✗ | ✗ | ✓ | ~ |
| Authorization model | ✗ | ~ | ✗ | ✓ |

## Implementation Status

- [x] Core design and module structure
- [x] Seal command DSL
- [x] Basic git wrapper operations
- [x] SPKI signing integration
- [x] Archive creation and verification
- [x] Migration path tracking
- [ ] Compile and test CLI
- [ ] Test suite for seal operations
- [ ] SPKI delegation for release authorization
- [ ] Encrypted archives (beyond signatures)
- [ ] Patch algebra (darcs-style)
- [ ] Network protocol for vault synchronization

## Philosophy Notes

**On Simplicity:** Like Chicken Scheme itself, Vault prioritizes doing one thing well with minimal conceptual overhead. Git's power comes at the cost of complexity; Vault trades some flexibility for clarity.

**On Security:** SPKI provides decentralized authorization without certificate authorities. Release signing is peer-to-peer, delegation is explicit, and trust is local.

**On Preservation:** The Library of Cyberspace requires long-term archival. Cryptographic seals ensure that what is preserved is authentic, and migration paths ensure it remains accessible.

**On the Seal Metaphor:** A seal is both a closure (sealing something shut) and a mark of authenticity (a wax seal). Both meanings apply: we seal the vault to prevent tampering and seal releases to mark them as official.

---

*"The difference between the almost right word and the right word is really a large matter. 'tis the difference between the lightning bug and the lightning."* — Mark Twain

In version control, **seal** is the lightning.
