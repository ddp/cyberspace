# RFC-044: Cryptographic Entropy Sources

**Status:** Draft
**Created:** 2026-01-08
**Author:** ddp@eludom.net

## Abstract

All cryptographic operations in Cyberspace require high-quality entropy. This RFC specifies the canonical entropy sources for each platform, ensuring consistent, auditable, and secure randomness across the entire system.

## Motivation

Cryptographic security depends entirely on the quality of random numbers:

- Key generation (Ed25519, X25519)
- Nonce generation (XSalsa20-Poly1305)
- Salt generation (Argon2id)
- Shamir secret sharing
- Challenge-response protocols

Weak or predictable entropy destroys security completely. A realm's sovereignty depends on unpredictable secrets.

## Specification

### Canonical Source: libsodium

All Cyberspace implementations MUST use libsodium's `randombytes_buf()` as the primary entropy source:

```
randombytes_buf(buffer, size)
```

libsodium automatically selects the best available source:
- Linux: `getrandom(2)` syscall, falls back to `/dev/urandom`
- macOS/iOS: `arc4random_buf()`
- Windows: `RtlGenRandom()`
- OpenBSD: `arc4random_buf()` (ChaCha20-based)

### Why libsodium?

1. **Cross-platform consistency** - Same API everywhere
2. **Automatic best-source selection** - No platform-specific code
3. **Initialization safety** - Blocks until entropy available
4. **Fork safety** - Handles process forking correctly
5. **Audited implementation** - Widely reviewed cryptographic library

### Platform Requirements

#### Scheme (CHICKEN)

```scheme
;; crypto-ffi.scm provides:
(define (random-bytes n)
  "Generate n cryptographically secure random bytes"
  (let ((buf (make-blob n)))
    ((foreign-lambda void "randombytes_buf" scheme-pointer unsigned-integer)
     buf n)
    buf))
```

All Scheme code MUST use `random-bytes` from crypto-ffi. NEVER use:
- `(chicken random)` - Uses PRNG, not cryptographically secure
- `/dev/random` directly - Platform-specific, may block
- Custom PRNGs - Unaudited, likely insecure

#### OCaml

**Status: Open Issue**

OCaml implementations should use one of:
- `mirage-crypto-rng` with `Nocrypto.Rng.generate`
- Direct FFI to libsodium via `ctypes`

Decision pending based on:
- Multicore OCaml compatibility
- Domain-local PRNG state handling
- Build system integration (dune vs opam)

### Entropy Initialization

Before ANY cryptographic operation, ensure libsodium is initialized:

```scheme
(define (sodium-init)
  (let ((result ((foreign-lambda int "sodium_init"))))
    (when (= result -1)
      (error "sodium_init failed - entropy source unavailable"))))
```

`sodium_init()` is idempotent and thread-safe. Call it early in program startup.

### Key Generation

All key generation MUST use libsodium's key generation functions, which internally use `randombytes_buf()`:

| Operation | Function |
|-----------|----------|
| Ed25519 signing key | `crypto_sign_keypair()` |
| X25519 key exchange | `crypto_box_keypair()` |
| Symmetric key | `crypto_secretbox_keygen()` |
| Generic random | `randombytes_buf()` |

### Nonce Generation

Nonces MUST be generated fresh for each encryption:

```scheme
(define (generate-nonce)
  (random-bytes (secretbox-noncebytes)))  ;; 24 bytes
```

For XSalsa20-Poly1305 with 24-byte nonces, random nonces are safe:
- 2^192 possible nonces
- Birthday collision after ~2^96 messages
- Practical limit: ~2^64 messages per key (still astronomical)

### Salt Generation

For Argon2id key derivation:

```scheme
(define (generate-salt)
  (random-bytes 16))  ;; crypto_pwhash_SALTBYTES
```

Salts prevent rainbow table attacks. Each salt MUST be unique per derived key.

## Security Considerations

### Entropy Exhaustion

libsodium's `randombytes_buf()` never blocks on modern systems:
- Uses ChaCha20 CSPRNG seeded from OS entropy
- OS entropy pools are continuously replenished
- Hardware RNG (RDRAND/RDSEED) available on modern CPUs

### VM/Container Considerations

Virtual machines may have limited entropy at boot:
- Use `virtio-rng` to pass host entropy to guests
- Ensure `haveged` or `rng-tools` if entropy-limited
- libsodium will block until sufficient entropy available

### Fork Safety

libsodium handles fork correctly:
- Automatic re-seeding after `fork()`
- No duplicate random sequences in child processes

### Deterministic Testing

For reproducible tests ONLY (never production):

```scheme
(define (set-test-seed seed)
  "WARNING: Deterministic mode - testing only"
  ((foreign-lambda void "randombytes_stir")))
```

Production code MUST use true entropy.

## Implementation Notes

### Current Status

| Component | Entropy Source | Status |
|-----------|---------------|--------|
| crypto-ffi.scm | `randombytes_buf()` | Implemented |
| vault.scm (keystore) | `random-bytes` | Implemented |
| OCaml core | TBD | Open Issue |

### Audit Trail

All key generation events should be logged (not the keys themselves):

```scheme
(seal-commit #f
  `(entropy-event
    (type "key-generation")
    (algorithm "ed25519")
    (timestamp ,(current-seconds))
    (entropy-source "libsodium")))
```

### Hardware Entropy

When available, hardware entropy sources enhance security:

| Platform | Hardware RNG |
|----------|-------------|
| Intel/AMD | RDRAND, RDSEED instructions |
| ARM | TRNG (True Random Number Generator) |
| Apple Silicon | Secure Enclave entropy |

libsodium automatically uses hardware entropy when available.

## Migration

### Phase 1: Audit (Current)
- Identify all randomness usage in codebase
- Replace non-libsodium sources

### Phase 2: Standardize
- All Scheme uses `random-bytes` from crypto-ffi
- Document OCaml approach

### Phase 3: Verify
- Entropy quality testing
- Audit logging for key generation

## References

- libsodium documentation: https://doc.libsodium.org/
- NIST SP 800-90A: Recommendations for Random Number Generation
- RFC 4086: Randomness Requirements for Security
- ChaCha20: https://cr.yp.to/chacha.html

## Appendix: Entropy Quality Testing

For paranoid verification:

```bash
# Generate random data
csi -e "(import crypto-ffi) (display (random-bytes 1000000))" > random.bin

# Run NIST statistical tests
ent random.bin
dieharder -a -f random.bin
```

Expected results:
- Entropy: ~7.9999 bits per byte
- Chi-square: p-value 0.01-0.99
- All dieharder tests: PASSED
