# SPKI Trusted Computing Base (TCB)

**Prime Directive**: If it's in the TCB, it's in OCaml. Otherwise it's in Chicken Scheme.

## Overview

This directory contains the minimal Trusted Computing Base for SPKI/SDSI - only the cryptographic primitives that MUST be correct and provably secure.

**TCB Size**: ~200 lines of OCaml + C stubs

**TCB Guarantees**:
1. **Signature correctness**: sign/verify round-trip always succeeds
2. **Unforgeability**: valid signatures prove key possession
3. **Key binding**: signatures tied to specific keys
4. **Constant-time**: no timing attacks (libsodium guarantee)

## Architecture

```
┌─────────────────────────────────────┐
│   Chicken Scheme (Everything)      │
│   - Policy, tools, network, UI     │
│   - All user-facing code           │
│   - Human-readable s-expressions   │
└──────────────┬──────────────────────┘
               │ FFI (minimal boundary)
               ▼
┌─────────────────────────────────────┐
│   OCaml TCB (Crypto Only)          │
│   - Ed25519 signatures             │
│   - SHA-512 hashing                │
│   - libsodium bindings             │
│   - Coq-provable core              │
└──────────────┬──────────────────────┘
               │ C FFI
               ▼
┌─────────────────────────────────────┐
│        libsodium                   │
│   - Constant-time crypto           │
│   - Audited implementation         │
└─────────────────────────────────────┘
```

## Files

### Core TCB (OCaml)

**signature.ml** (91 lines)
- OCaml interface to libsodium
- Ed25519 keypair generation, signing, verification
- SHA-512 hashing
- Type-safe wrappers around C bindings

**signature_stubs.c** (114 lines)
- C FFI bindings to libsodium
- `caml_sodium_init()` - initialize libsodium
- `caml_ed25519_keypair()` - generate keypair
- `caml_ed25519_sign()` - create signature
- `caml_ed25519_verify()` - verify signature (TCB CRITICAL)
- `caml_sha512_hash()` - SHA-512 hash

### Export Layer (for Scheme FFI - future)

**export.ml** (104 lines)
- C API exported from OCaml
- Callback registration for Scheme FFI
- Buffer management for cross-language calls

**export_stubs.c** (165 lines)
- C wrappers for Scheme FFI
- Translates between Scheme bytevectors and OCaml bytes

### Testing

**test_signature.ml**
- Test Ed25519 sign/verify round-trip
- Test tampering detection
- Test wrong key rejection
- Test SHA-512 hashing

**dune**
- Build configuration
- Links against libsodium (via Homebrew on macOS)

## Cryptographic Primitives

### Ed25519 Signatures

**Key sizes**:
- Public key: 32 bytes
- Secret key: 64 bytes (32-byte seed + 32-byte public key)
- Signature: 64 bytes

**Properties**:
- Deterministic (same message + key = same signature)
- Fast verification (~70K verifications/second)
- Constant-time (no timing attacks)
- Post-quantum security level: broken by Grover's algorithm (2^128 operations)

**TCB Critical Path**: `ed25519_verify()`
This is the security guarantee. If it returns `true`, the signature was created by the holder of the corresponding private key. No forgery is possible without the private key.

### SHA-512 Hashing

**Hash size**: 64 bytes

**Usage**:
- Key hashes (for SPKI key identifiers)
- Message digests
- Certificate fingerprints

**Properties**:
- Collision-resistant (2^256 operations to find collision)
- Pre-image resistant
- Fast (~300 MB/s)

## Building

```bash
# From spki/ directory
dune build tcb/

# Run tests
dune build tcb/test_signature.exe
./_build/default/tcb/test_signature.exe
```

## Dependencies

**System**:
- libsodium (via Homebrew: `/opt/homebrew/lib/libsodium.dylib`)

**OCaml**:
- OCaml >= 4.14
- dune >= 3.0
- conf-libsodium (opam package)

**No CryptoKit** - we replaced the placeholder RSA implementation with Ed25519 via libsodium.

## Verification Path (Roadmap Month 4)

This TCB is designed for formal verification:

**TLA+ (Protocol)**:
- Specify SPKI certificate chain protocol
- Model check delegation semantics
- Prove safety (no forgery) and liveness (chains verify)

**Coq (Implementation)**:
- Model Ed25519 signature scheme
- Prove signature correctness theorem
- Prove unforgeability theorem
- Extract verified OCaml code

**Theorems to prove**:
```coq
Theorem signature_correct : forall pk sk msg,
  valid_keypair pk sk ->
  verify(pk, msg, sign(sk, msg)) = true.

Theorem no_forgery : forall pk msg sig,
  verify(pk, msg, sig) = true ->
  exists sk, sign(sk, msg) = sig /\ valid_keypair pk sk.
```

## Security Considerations

**What's in the TCB**: Only cryptographic primitives
- Ed25519 signature generation and verification
- SHA-512 hashing
- libsodium initialization

**What's NOT in the TCB**: Everything else
- S-expression parsing (Scheme)
- Certificate chain validation logic (Scheme)
- Policy evaluation (Scheme)
- SDSI name resolution (Scheme)
- CLI tools (Scheme)
- Network protocols (Scheme)

**Why this matters**:
- TCB bugs = security vulnerabilities
- Non-TCB bugs = functionality issues
- Smaller TCB = easier to audit and verify
- Human-readable Scheme policy = easier to audit

## Usage from Scheme

(Future - after Scheme FFI is complete)

```scheme
;; Initialize TCB
(tcb-init)

;; Generate keypair
(define keypair (tcb-keypair-generate))
(define pk (car keypair))
(define sk (cdr keypair))

;; Sign a message
(define msg (string->bytes "The Library of Cyberspace"))
(define sig (tcb-sign sk msg))

;; Verify signature (TCB CRITICAL)
(define valid? (tcb-verify pk msg sig))  ;; => #t

;; Hash data
(define hash (tcb-hash msg))  ;; => 64-byte SHA-512 hash
```

## Performance

**Ed25519** (libsodium benchmarks on Apple M1):
- Keypair generation: ~20K/second
- Signing: ~20K/second
- Verification: ~70K/second

**SHA-512**:
- ~300 MB/s

For SPKI certificate chains, verification is the bottleneck. With 70K verifications/second, we can validate complex delegation chains in microseconds.

## Comparison: Old vs New

**Old** (`spki/src/crypto.ml`):
- 68 lines
- Placeholder RSA via CryptoKit
- Not production-ready
- Not verifiable

**New** (`spki/tcb/`):
- ~200 lines total (OCaml + C)
- Real Ed25519 via libsodium
- Production-ready crypto
- Designed for Coq verification
- SHA-512 instead of SHA-256
- Clean separation: crypto (OCaml) vs policy (Scheme)

## Next Steps

1. **Complete Scheme FFI** - Chicken Scheme can call TCB
2. **S-expressions in Scheme** - Parse/serialize SPKI certificates
3. **Certificate logic in Scheme** - Chain validation, delegation
4. **Policy in Scheme** - Authorization decisions
5. **CLI tools in Scheme** - Replace OCaml tools
6. **TLA+ specification** - Protocol model checking
7. **Coq verification** - Prove TCB correctness

## References

**Ed25519**:
- Bernstein et al. (2011) - "High-speed high-security signatures"
- RFC 8032 - Edwards-Curve Digital Signature Algorithm (EdDSA)

**SPKI/SDSI**:
- Lampson et al. (1996) - "Authentication in Distributed Systems: Theory and Practice"
- Rivest & Lampson (1996) - "SDSI - A Simple Distributed Security Infrastructure"
- RFC 2693 - SPKI Certificate Theory

**libsodium**:
- https://libsodium.gitbook.io/
- NaCl (Bernstein et al.) - "Cryptography in NaCl"

---

**Status**: TCB complete and tested (January 2026)

**Next milestone**: Scheme FFI integration (Month 1, Week 2)
