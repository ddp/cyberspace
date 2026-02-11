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

- `.scm` → `.sls` (library) or `.ss` (script)

## Files Ported

### Core Libraries
- `sexp.sls` - S-expression parser/printer. Foundation for all SPKI data.
- `crypto-ffi.sls` - libsodium FFI (Ed25519, SHA-512, X25519, Shamir, GF256). Uses Chez `foreign-procedure`.
- `cert.sls` - SPKI certificate types, signing, verification, chain delegation.
- `capability.sls` - Pure Scheme. Capability scoring and master election.
- `security.sls` - Security properties inspector (fingerprinting, cert-status, capability queries).
- `keyring.sls` - Key management (generation, storage, lookup, signing). Ed25519 only.
- `os.sls` - OS introspection (sysctl, platform detection, resource monitoring).
- `objc.sls` - Objective-C FFI bridge for macOS (NSUserDefaults, notifications).

### Compatibility Shims
- `chicken-compatibility/chicken.sls` - print, conc, alist-ref, handle-exceptions, get-opt, get-key
- `chicken-compatibility/blob.sls` - blob->string, string->blob, blob-size, blob=?
- `chicken-compatibility/base64.sls` - RFC 4648 base64 encode/decode (bytevector I/O)
- `chicken-compatibility/hash-table.sls` - SRFI-69 hash table interface
- `chicken-compatibility/process.sls` - process/shell execution

### Test Scripts
- `test-capability.ss` - Capability scoring and election tests
- `test-compat-sexp.ss` - S-expression round-trip tests
- `test-security.ss` - Security inspector tests
- `test-keyring.ss` - Key management tests
- `test-objc.ss` - Objective-C bridge tests

### Next in Queue
- `vault.sls` - Encrypted storage (depends on keyring)

## Testing

```bash
cd chez
/opt/homebrew/bin/chez --libdirs . test-capability.ss
/opt/homebrew/bin/chez --libdirs . test-compat-sexp.ss
```

## Key Translation Patterns

### Records
CHICKEN SRFI-9: `(define-record-type name (constructor) pred (field accessor))`
Chez R6RS: `(define-record-type (<name> constructor pred) (fields (immutable field accessor)))`

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

## Future Work

Modules requiring FFI translation:
- `mdns.scm` - Bonjour/DNS-SD (dns_sd FFI)

Threading modules needing architecture changes:
- `gossip.scm` - Cooperative → preemptive (race conditions to fix)
- `auto-enroll.scm` - Green threads → OS threads
