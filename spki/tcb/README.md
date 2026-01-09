# SPKI Trusted Computing Base (TCB)

**Prime Directive**: If it's in the TCB, it's in OCaml. Otherwise it's in Chicken Scheme.

## Overview

This directory contains the minimal Trusted Computing Base for SPKI/SDSI - only the security-critical code that MUST be correct and provably secure.

**TCB Size**: ~988 lines OCaml + ~266 lines C stubs (1254 total)

**TCB Guarantees**:
1. **Signature correctness**: sign/verify round-trip always succeeds
2. **Unforgeability**: valid signatures prove key possession
3. **Key binding**: signatures tied to specific keys
4. **Constant-time**: no timing attacks (libsodium guarantee)
5. **Certificate chain validation**: monotonic capability attenuation
6. **Audit trail integrity**: hash-chained, signed log entries
7. **FIPS-181 verification**: pronounceable codes for enrollment

**Post-Quantum**: Planned (ML-DSA-65, SPHINCS+-SHAKE) when liboqs builds without OpenSSL.
Prime directive: TCB depends only on libsodium.

## Architecture

```
+-------------------------------------+
|   Chicken Scheme (Everything)       |
|   - Policy, tools, network, UI      |
|   - All user-facing code            |
|   - Human-readable s-expressions    |
+-----------------+-------------------+
                  | FFI (minimal boundary)
                  v
+-------------------------------------+
|   OCaml TCB (Security-Critical)     |
|   - Ed25519 signatures              |
|   - SHA-256/512, BLAKE2b            |
|   - Certificate chain validation    |
|   - Capability tag intersection     |
|   - FIPS-181 verification codes     |
|   - Audit trail (hash-chained)      |
|   - CCP cookie verification         |
+-----------------+-------------------+
                  | C FFI
                  v
+-------------------------------------+
|         libsodium (audited)         |
|   - Constant-time crypto            |
|   - No OpenSSL dependency           |
|   - Single, audited library         |
+-------------------------------------+
```

## Files

### Unified TCB (OCaml)

**spki_tcb.ml** (~1000 lines)
The complete security-critical code:
- **Principals**: Key/KeyHash identity with constant-time comparison
- **Tags**: Capability tags with monotonic intersection (TagAll, TagSet, TagPrefix, TagRange, TagThreshold)
- **Certificates**: SPKI certificate structure and chain validation
- **Authorization**: Single authorization decision point
- **CCP Cookies**: Stateless DoS defense (PHOTURIS-style)
- **Audit Trail**: Hash-chained, signed log entries
- **FIPS-181**: Pronounceable verification codes for enrollment

**tcb_stubs.c** (~260 lines)
C FFI bindings to libsodium:
- Ed25519 keypair generation, signing, verification
- SHA-256, SHA-512, BLAKE2b hashing
- HMAC-SHA256 for cookies
- Constant-time comparison
- Cryptographic random bytes

### Legacy Modules

**signature.ml** (91 lines) - Standalone Ed25519 module
**signature_stubs.c** (114 lines) - libsodium bindings only

### Export Layer (for Scheme FFI)

**export.ml** (104 lines) - C API exported from OCaml
**export_stubs.c** (165 lines) - Scheme FFI wrappers

### Testing

**test_tcb.ml** - 62 tests covering:
- Principal comparison (reflexive, symmetric, transitive)
- Tag intersection (monotonic attenuation)
- All cryptographic primitives (Ed25519, SHA-*, BLAKE2b, HMAC)
- Cookie generation/verification
- Audit trail integrity
- FIPS-181 syllable generation
- Certificate validity checking
- Authorization decisions

**test_signature.ml** - Legacy Ed25519 tests

**dune** - Build configuration (libsodium only)

**build-liboqs.sh** - Script to build liboqs without OpenSSL (for future PQ support)

## Cryptographic Primitives

### Ed25519 Signatures

**Key sizes**:
- Public key: 32 bytes
- Secret key: 64 bytes
- Signature: 64 bytes

**Properties**:
- Deterministic (same message + key = same signature)
- Fast verification (~70K verifications/second)
- Constant-time (no timing attacks)
- Classical security: 128-bit

**TCB Critical Path**: `ed25519_verify()`
If it returns `true`, the signature was created by the holder of the private key.

### Hash Functions

| Algorithm | Output | Use Case |
|-----------|--------|----------|
| SHA-256 | 32 bytes | Content addressing, Merkle trees, FIPS-181 |
| SHA-512 | 64 bytes | Principal hashes, key identifiers |
| BLAKE2b | 32 bytes | Audit trail, fast hashing |

All hashes provide 128-bit quantum security against Grover's algorithm.

### FIPS-181 Verification Codes

Converts public key hashes to pronounceable syllables for verbal verification:
- Pattern: CVC (consonant-vowel-consonant)
- 4 syllables from first 4 bytes of SHA-256
- Example: `bek-fom-riz-tup`

Used during node enrollment (RFC-044) for out-of-band verification.

## Building

```bash
# From spki/ directory
dune build tcb/

# Run all tests (62 tests)
dune exec tcb/test_tcb.exe

# Run legacy signature tests
dune exec tcb/test_signature.exe

# Run full test suite
dune runtest
```

## Dependencies

**System library** (via Homebrew on macOS):
```bash
brew install libsodium
```

**OCaml**:
- OCaml >= 4.14
- dune >= 3.0

**Prime Directive**: TCB depends only on libsodium. No OpenSSL. No other crypto libraries.

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
- ~1254 lines total (988 OCaml + 266 C)
- Real Ed25519 via libsodium
- Production-ready crypto
- Designed for Coq verification
- FIPS-181 verification codes
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
- 62 tests passing
- FIPS-181 verification codes
- Pure libsodium (no OpenSSL)

**Post-Quantum**: Planned when liboqs builds without OpenSSL dependency.
The SHAKE-based variants (ML-DSA, SPHINCS+-SHAKE) use Keccak internally
and don't fundamentally require OpenSSL - just need a clean liboqs build.

**Next milestone**: Scheme FFI integration
