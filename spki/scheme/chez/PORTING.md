# Chez Scheme Port

Port of Cyberspace Scheme to Chez Scheme for true SMP threading.

## Why Chez?

- Native OS threads with proper SMP primitives (mutexes, condition variables)
- Fast incremental native-code compiler
- Cisco/Kent Dybvig pedigree - battle-tested
- MIT licensed (open source since 2016)
- R6RS but pragmatic

## Translation Guide

### Module System

| CHICKEN | Chez |
|---------|------|
| `(module name (exports) body)` | `(library (namespace name) (export ...) (import ...) body)` |
| `(import (chicken base))` | `(import (rnrs))` |
| `(import srfi-1)` | `(import (srfi :1))` or inline |

### Common Translations

| CHICKEN | Chez |
|---------|------|
| `(chicken format)` printf | `(only (chezscheme) printf)` |
| `(chicken sort)` sort | `(only (chezscheme) sort)` with swapped args |
| `exact->inexact` | `inexact` |
| `str-downcase` | `string-downcase` (in rnrs) |

### Sort Argument Order

CHICKEN: `(sort list predicate)`
Chez: `(sort predicate list)`

### File Extensions

- `.scm` → `.sls` (library) or `.ss`/`.sps` (script/test)

## Files Ported

### Core Libraries (45 modules)
- `sexp.sls` - S-expression parser/printer. Foundation for all SPKI data.
- `crypto-ffi.sls` - libsodium FFI (Ed25519, SHA-512, BLAKE2b, X25519, SHAKE256, Shamir, Merkle). Uses Chez `foreign-procedure`.
- `cert.sls` - SPKI certificate types, signing, verification, chain delegation. PQ/hybrid support.
- `capability.sls` - Pure Scheme. Capability scoring and master election.
- `security.sls` - Security properties inspector (fingerprinting, cert-status, validity, capability queries).
- `keyring.sls` - Key management (generation, storage, lookup, signing). Multi-algorithm (Ed25519, ML-DSA, SPHINCS+, hybrid).
- `vault.sls` - Encrypted storage, soup operations, dashboard, NLP search.
- `gossip.sls` - Epidemic gossip protocol, bloom/merkle/transfer layers, peer management.
- `query.sls` - Lazy query cursors (Memo-027 Phase 1): sorting, pagination, aggregation.
- `audit.sls` - Audit trail logging and querying.
- `bloom.sls` - Bloom filter for gossip deduplication.
- `merkle.sls` - Merkle tree operations.
- `catalog.sls` - Soup catalog management.
- `filetype.sls` - File type detection.
- `fips.sls` - FIPS 181 pronounceable password generation.
- `wordlist.sls` - Word list for human-readable identifiers.
- `pq-crypto.sls` - Post-quantum crypto stubs (ML-DSA, SPHINCS+).
- `tcp.sls` - TCP networking primitives.
- `script.sls` - Script execution.
- `os.sls` - OS introspection (sysctl, platform detection, resource monitoring).
- `objc.sls` - Objective-C FFI bridge for macOS (NSUserDefaults, notifications).
- `enroll.sls` - Node enrollment, system introspection, certificate management, mDNS presence.
- `forum.sls` - Realm forum (VAX Notes style): topics, replies, sequential numbering.
- `lazy-chunks.sls` - Lazy Merkle chunk loading for huge objects (64KB chunks, LRU cache).
- `piece-table.sls` - Piece table for collaborative editing: insert, delete, undo/redo, OT hooks.
- `portal.sls` - Session lifecycle: statistics, formatting, goodbye ceremony.
- `rope.sls` - Rope data structure: O(log n) insert/delete on large texts.
- `test.sls` - Test framework (assert-true, assert-equal, test-case).
- `auto-enroll.sls` - Auto-enrollment with OS threads (green threads → SMP). Depends on enroll, mdns, gossip.
- `display.sls` - Display/rendering utilities.
- `edt.sls` - EDT editor.
- `forge.sls` - Object forge (creation, transformation).
- `fuse-ffi.sls` - FUSE filesystem FFI bridge.
- `http.sls` - HTTP client/server operations.
- `info.sls` - System and realm information display.
- `inspector.sls` - Object inspector.
- `mdns.sls` - Bonjour/DNS-SD multicast DNS (dns_sd FFI).
- `metadata-ffi.sls` - File metadata FFI (extended attributes, Spotlight).
- `osc.sls` - Open Sound Control protocol.
- `rnbo.sls` - RNBO (Max/MSP) integration.
- `smelter.sls` - Object smelter (decomposition, analysis).
- `text.sls` - Text objects (gap buffer, operations, rendering).
- `tty-ffi.sls` - Terminal FFI (raw mode, size, cursor).
- `ui.sls` - User interface primitives.
- `wormhole.sls` - Peer-to-peer tunneling.

### CLI Tools (4 scripts)
- `spki-keygen.sps` - Generate Ed25519 keypair, save to files.
- `spki-cert.sps` - Create and sign SPKI authorization certificate.
- `spki-show.sps` - Display certificate or key in human-readable format.
- `spki-verify.sps` - Verify SPKI certificate delegation chain.

### Compatibility Shims (6 modules)
- `chicken-compatibility/chicken.sls` - print, conc, alist-ref, handle-exceptions, get-opt, get-key
- `chicken-compatibility/blob.sls` - blob->string, string->blob, blob-size, blob=?, move-memory!
- `chicken-compatibility/base64.sls` - RFC 4648 base64 encode/decode (bytevector I/O)
- `chicken-compatibility/hash-table.sls` - SRFI-69 hash table interface
- `chicken-compatibility/process.sls` - process/shell execution
- `chicken-compatibility/file.sls` - File operations

### C/ObjC Bridges (8 files)
- `crypto-bridge.c` - libsodium FFI (Ed25519, SHA-512, BLAKE2b, X25519, Shamir)
- `tcp-bridge.c` - TCP socket operations
- `tty-bridge.c` - Terminal raw mode, window size, cursor control
- `metadata-bridge.c` - File metadata, extended attributes, Spotlight queries
- `osc-bridge.c` - Open Sound Control UDP send/receive
- `fuse-bridge.c` - FUSE filesystem operations (mount, read, write, readdir)
- `pq-bridge.c` - Post-quantum crypto (ML-DSA, SPHINCS+ stubs)
- `objc-bridge.m` - Objective-C FFI (NSUserDefaults, notifications, system info)

### Test Suite (19 files)
- `tests/test-sexp.sps` - S-expression round-trip (12 tests)
- `tests/test-crypto.sps` - Ed25519 sign/verify, SHA-256, tampering detection
- `tests/test-cert.sps` - Certificate creation, round-trip, signing, tag implication (14 tests)
- `tests/test-security.sps` - ISO 8601 parsing, validity, cert-status, revocation (14 tests)
- `tests/test-shamir.sps` - Shamir secret splitting and reconstruction
- `tests/test-capability.sps` - Capability scoring and election
- `tests/test-bloom.sps` - Bloom filter operations
- `tests/test-gossip.sps` - Gossip protocol
- `tests/test-query.sps` - Query cursors, sorting, pagination, aggregation (16 tests)
- `tests/test-portal.sps` - Session lifecycle, formatting, statistics (30 tests)
- `tests/test-rope.sps` - Rope operations: split, insert, delete, rebalance (39 tests)
- `tests/test-piece-table.sps` - Piece table: CRUD, undo/redo, collaboration (40 tests)
- `tests/test-entropy.sps` - Cryptographic entropy quality (19 tests)
- `tests/test-membership.sps` - Membership lifecycle: join policy, proposals, voting, disbarment (38 tests)
- `test-capability.ss` - Capability scoring (legacy)
- `test-keyring.ss` - Key management (27 tests)
- `test-compat-sexp.ss` - Compatibility S-expression tests
- `test-objc.ss` - Objective-C bridge tests
- `test-security.ss` - Security tests

## Testing

```bash
cd chez
/opt/homebrew/bin/chez --libdirs . tests/run-all.sh  # or individual:
/opt/homebrew/bin/chez --libdirs . tests/test-cert.sps
/opt/homebrew/bin/chez --libdirs . tests/test-security.sps
/opt/homebrew/bin/chez --libdirs . tests/test-query.sps
/opt/homebrew/bin/chez --libdirs . test-keyring.ss
```

## Key Translation Patterns

### Records
CHICKEN SRFI-9: `(define-record-type name (constructor) pred (field accessor))`
Chez R6RS: `(define-record-type <name> (fields (immutable field accessor)))`

Note: R6RS records are opaque — `equal?` returns `#f` even with identical fields.
Use `sexp-equal?` from sexp.sls for structural comparison of sexp records.

### Optional/Keyword Args
CHICKEN: `(define (foo x #!optional (y 10)) ...)`
Chez: `(define (foo x . rest) (let ((y (get-opt rest 0 10))) ...))`

### Condition Handling
CHICKEN: `(condition-case expr (exn () fallback))`
Chez: `(guard (exn [#t fallback]) expr)`

### Docstrings
R6RS forbids expressions before definitions in library bodies.
Convert string docstrings to comments above the function.

### Binary Data
Use bytevectors directly. Never route crypto keys through `utf8->string`
(corrupts bytes > 127). Base64 operates on bytevectors, not strings.

### Import Conflicts
`(rnrs)` provides `file-exists?`, `delete-file`, `with-input-from-file`, etc.
Do NOT import these again from `(chezscheme)` — causes "multiple definitions" error.
Use `(only (chezscheme) ...)` with explicit names that aren't in `(rnrs)`.

### Parameters vs. Procedures
`current-input-port` from `(rnrs)` is a plain procedure, not a Chez parameter.
To use it with `parameterize`, import from `(chezscheme)` instead:
`(except (rnrs) current-input-port)` + `(only (chezscheme) ... current-input-port)`.

### Tagged S-expression Alists
Chicken's `assq` tolerates non-pair elements; Chez R6RS signals an error.
For tagged structures like `(spki-cert (issuer ...) ...)`, use `(cdr body)`
to skip the tag symbol before calling `assq`.

### Signal Handling
Chez lacks `set-signal-handler!` for arbitrary signals. Only
`keyboard-interrupt-handler` (SIGINT) is available as a parameter.
Modules needing SIGTERM/SIGHUP handlers (portal) use no-ops; wrap via
C FFI if full signal support is needed.

### Eval
`(rnrs)` in Chez does not export `eval`. Import it from `(chezscheme)`:
`(import (rnrs) (only (chezscheme) eval))`. No `except` clause needed
since there is no overlap.

## Remaining Work

Application modules (not library code):
- `repl.scm` - The main REPL (4800+ lines, last to port)
- `cyberspace.scm` - Top-level application entry point
- `server.scm` - Server mode
- `seal.scm` - Seal operations CLI

Development utilities (low priority):
- `deploy.scm`, `refresh-library.scm`, `refresh-repl.scm`
- `sanity.scm`, `scrutinize.scm`, `scrutinizer.scm`
- `demo-cyberspace.scm`, `mpe.scm`

## Stats

- 45 library modules (21,383 lines)
- 4 CLI tools (spki-keygen, spki-cert, spki-show, spki-verify)
- 6 compatibility shims
- 8 C/ObjC bridge source files
- 19 test files (14 test suites pass)
- 46 of 58 Chicken modules ported (79%)
- All library-layer dependencies complete; only application shell remains
