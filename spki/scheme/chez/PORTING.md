# Chez Scheme Port

Proof-of-concept port of Cyberspace Scheme to Chez Scheme for true SMP threading.

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

### Core Libraries (22 modules)
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
- `test.sls` - Test framework (assert-true, assert-equal, test-case).

### Compatibility Shims
- `chicken-compatibility/chicken.sls` - print, conc, alist-ref, handle-exceptions, get-opt, get-key
- `chicken-compatibility/blob.sls` - blob->string, string->blob, blob-size, blob=?, move-memory!
- `chicken-compatibility/base64.sls` - RFC 4648 base64 encode/decode (bytevector I/O)
- `chicken-compatibility/hash-table.sls` - SRFI-69 hash table interface
- `chicken-compatibility/process.sls` - process/shell execution
- `chicken-compatibility/file.sls` - File operations

### Test Suite
- `tests/test-sexp.sps` - S-expression round-trip (12 tests)
- `tests/test-crypto.sps` - Ed25519 sign/verify, SHA-256, tampering detection
- `tests/test-cert.sps` - Certificate creation, round-trip, signing, tag implication (14 tests)
- `tests/test-security.sps` - ISO 8601 parsing, validity, cert-status, revocation (14 tests)
- `tests/test-shamir.sps` - Shamir secret splitting and reconstruction
- `tests/test-capability.sps` - Capability scoring and election
- `tests/test-bloom.sps` - Bloom filter operations
- `tests/test-gossip.sps` - Gossip protocol
- `tests/test-query.sps` - Query cursors, sorting, pagination, aggregation (16 tests)
- `test-capability.ss` - Capability scoring (legacy)
- `test-keyring.ss` - Key management (27 tests)

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

## Future Work

Modules requiring FFI translation:
- `mdns.scm` - Bonjour/DNS-SD (dns_sd FFI)

Threading modules needing architecture changes:
- `auto-enroll.scm` - Green threads → OS threads (depends on enroll, mdns, gossip)
- `enroll.scm` - Enrollment protocol (depends on TCP, threading)

Application modules (lower priority):
- `display.scm` - Display utilities
- `http.scm` - HTTP client/server
- `wormhole.scm` - Peer-to-peer tunneling
- `repl.scm` - The main REPL (4800+ lines, last to port)
