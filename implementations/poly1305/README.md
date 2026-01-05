# Poly1305 Message Authentication Code

**Educational implementation of Daniel J. Bernstein's Poly1305 MAC**

From the paper: *"The Poly1305-AES message-authentication code"* (2005)
RFC: *RFC 7539: ChaCha20 and Poly1305 for IETF Protocols* (2015)
Source: `~/cyberspace/library/cryptographers/djb/poly1305-aes-2005.pdf`

## ⚠️ Important Notice

**This is a SIMPLIFIED educational implementation.**

Full Poly1305 requires careful 130-bit modular arithmetic with constant-time guarantees. This implementation demonstrates the concepts but should **NEVER** be used in production.

**For production, use:**
- libsodium (recommended)
- OpenSSL
- BoringSSL

## The Concept

**Poly1305** is a message authentication code (MAC) that computes a 128-bit authentication tag for a message using polynomial evaluation in a prime field.

```
Core idea:
- Treat message as polynomial coefficients
- Evaluate polynomial at secret point r
- Work in prime field (2^130 - 5)
- Add secret s to result
- Output 128-bit tag

tag = ((msg[0]·r^n + msg[1]·r^(n-1) + ... + msg[n]·r^1) mod (2^130-5)) + s
```

**Key Insight:** Polynomial evaluation is fast and provides strong authentication when done in a carefully chosen prime field.

## The Problem Poly1305 Solves

### HMAC-SHA256 Limitations

**Traditional MACs (HMAC):**
```
HMAC-SHA256:
- Two hash computations (inner + outer)
- Slower than dedicated MAC
- Complex implementation
- Harder to make constant-time
```

**Issues:**
- Performance overhead
- Implementation complexity
- Timing attack surface

### Poly1305 Advantages

```
One-time MAC with cipher-derived key:
- Single pass over message
- Very fast (constant-time)
- Simple mathematical structure
- Provable security bounds
```

**Security:**
- ✓ 128-bit security (forgery probability  ≈ 2^-128)
- ✓ Constant-time (with proper implementation)
- ✓ Fast (1-2 cycles/byte on modern CPUs)
- ✓ Provably secure (polynomial evaluation security)
- ✓ Clean mathematical structure

## Quick Start

```bash
cd ~/cyberspace/implementations/poly1305

# Basic MAC computation
./poly1305.scm demo-basic

# MAC properties demonstration
./poly1305.scm demo-properties

# All demonstrations
./poly1305.scm demo-all
```

## How It Works

### 1. Key Structure

Poly1305 uses a 32-byte (256-bit) key split into two parts:

```
Key (32 bytes):
├─ r (16 bytes): Polynomial evaluation point (clamped)
└─ s (16 bytes): Final addition value

Clamping r (RFC 7539):
r &= 0x0ffffffc0ffffffc0ffffffc0fffffff

Why clamp?
- Ensures r has specific bit pattern
- Prevents certain attacks
- Maintains constant-time properties
```

### 2. Message Processing

Process message in 16-byte blocks:

```scheme
accumulator = 0

for each 16-byte block:
  ; Convert block to integer (little-endian) + append 0x01
  block_int = bytes_to_int(block) + 2^(8*block_length)

  ; Add to accumulator
  accumulator = accumulator + block_int

  ; Multiply by r and reduce modulo (2^130 - 5)
  accumulator = (accumulator * r) mod (2^130 - 5)

; Add s
tag = (accumulator + s) mod 2^128
```

**The high bit (0x01):** Added after each block to distinguish different message lengths. Prevents length-extension attacks.

### 3. Prime Field Arithmetic

**Prime:** p = 2^130 - 5

**Why this prime?**
```
2^130 - 5 is prime and has special properties:
- Close to power of 2 → efficient modular reduction
- 130 bits → provides security margin
- -5 allows fast reduction: x mod (2^130 - 5) ≈ (x & mask) + 5·(x >> 130)
```

**Security:** Polynomial evaluation in prime field provides provable security bounds.

### 4. Single-Use Key Requirement

**Critical:** Never reuse Poly1305 key for different messages!

```
Problem: Key reuse vulnerability
If: tag1 = h(msg1)·r + s
    tag2 = h(msg2)·r + s
Then: tag1 - tag2 = (h(msg1) - h(msg2))·r

Attacker can compute r and forge tags!
```

**Solution:** Derive fresh key for each message using ChaCha20 or AES.

## ChaCha20-Poly1305 AEAD

Combining ChaCha20 (encryption) with Poly1305 (authentication) creates Authenticated Encryption with Associated Data:

```
1. Generate Poly1305 key from ChaCha20:
   poly_key = ChaCha20(key, nonce, counter=0)[0:32]

2. Encrypt message:
   ciphertext = ChaCha20(key, nonce, counter=1, plaintext)

3. Compute MAC over AAD and ciphertext:
   tag = Poly1305(poly_key, AAD || ciphertext || lengths)

4. Return (ciphertext, tag)
```

**Properties:**
- ✓ Confidentiality (ChaCha20 encryption)
- ✓ Authentication (Poly1305 MAC)
- ✓ Associated Data (can authenticate non-encrypted data)
- ✓ Nonce-based (never reuse key due to fresh poly_key per nonce)

## Real-World Applications

### TLS 1.3 (2018)

**Cipher suite:** TLS_CHACHA20_POLY1305_SHA256

```
ChaCha20: Encryption
Poly1305: Authentication
SHA-256: Key derivation

Used for:
- Mobile browsers (Chrome, Firefox, Safari)
- IoT devices without AES-NI
- Cloudflare edge servers
```

### WireGuard VPN (2020)

**All traffic encrypted with ChaCha20-Poly1305:**

```
Protocol: Noise_IK
Encryption: ChaCha20-Poly1305
Key exchange: Curve25519

Advantages:
- Fast on all devices
- Simple codebase (4,000 lines vs OpenVPN's 100,000+)
- Auditable
- Constant-time
```

### OpenSSH (2014+)

**Cipher:** `chacha20-poly1305@openssh.com`

```bash
# Use ChaCha20-Poly1305 for SSH
ssh -c chacha20-poly1305@openssh.com user@host
```

**Why SSH adopted it:**
- Fast on embedded systems, routers
- No timing attacks
- Simpler than AES-GCM
- Good performance everywhere

### Signal Protocol

**End-to-end encrypted messaging:**

```
Double Ratchet + ChaCha20-Poly1305
Used by:
- Signal (obviously)
- WhatsApp (1B+ users)
- Facebook Messenger (secret conversations)
- Google Messages (RCS encryption)
```

### Google QUIC / HTTP/3

**Default encryption:**

```
Initial keys: ChaCha20-Poly1305 (mobile) or AES-128-GCM (desktop)
0-RTT: ChaCha20-Poly1305

Powers:
- YouTube
- Gmail
- Google Search
- All Google services on mobile
```

## Security Properties

### ✓ Guarantees

**1. Forgery Resistance**
```
Probability of forging valid tag: ≈ 2^-128
Even after seeing many (message, tag) pairs
Provably secure under polynomial evaluation
```

**2. Constant-Time (with proper implementation)**
```
No secret-dependent branches
No table lookups
All operations: add, multiply, modulo
→ Immune to timing attacks
```

**3. Fast Performance**
```
Software: 1-2 cycles/byte (modern CPUs)
Compare HMAC-SHA256: 5-10 cycles/byte
3-5× faster than HMAC
```

**4. Deterministic**
```
Same (key, message) → same tag (always)
Useful for debugging
Predictable behavior
```

**5. Provable Security**
```
Security bound: forgery probability ≤ (message_blocks + 1) / 2^106
For 1GB message (2^24 blocks): probability ≤ 2^-82
Much better than brute-force 2^-128
```

### ✗ Limitations

**1. Single-Use Key Requirement**

```
NEVER reuse Poly1305 key with different messages!

Correct usage:
for each message:
  poly_key = ChaCha20(master_key, nonce, counter=0)[0:32]  # Fresh key
  tag = Poly1305(poly_key, message)

Incorrect usage (INSECURE):
poly_key = fixed_key  # WRONG!
for each message:
  tag = Poly1305(poly_key, message)  # Key reuse → broken!
```

**2. Requires Cipher for Key Derivation**

```
Can't use Poly1305 standalone securely
Must pair with:
- ChaCha20 (RFC 7539)
- AES (original Poly1305-AES)
- Other cipher

Reason: Need fresh key per message
```

**3. No Built-In Nonce**

```
Poly1305 itself doesn't handle nonces
Nonce management delegated to cipher (ChaCha20)
AEAD construction required for full security
```

**4. Implementation Complexity**

```
Requires 130-bit arithmetic
Must be constant-time
Modular reduction by (2^130 - 5) is tricky
Easy to implement incorrectly

→ Use audited library (libsodium, OpenSSL)
```

## Comparison to Other MACs

| Property | Poly1305 | HMAC-SHA256 | AES-GCM |
|----------|----------|-------------|---------|
| Speed (software) | 1-2 cyc/byte | 5-10 cyc/byte | 3-4 cyc/byte (w/ PCLMUL) |
| Speed (no HW accel) | 1-2 cyc/byte | 5-10 cyc/byte | 15-20 cyc/byte |
| Security | 128-bit | 256-bit | 128-bit |
| Key reuse | ✗ Single-use only | ✓ Can reuse | ✗ Nonce-based |
| Constant-time | ✓ (if implemented right) | Medium difficulty | ✗ (GCM timing leaks) |
| Standardization | RFC 7539 (IETF) | FIPS 198-1 (NIST) | NIST SP 800-38D |
| Provable security | ✓ Polynomial eval | ✗ Heuristic | ✓ (GHASH) |

**When to use Poly1305:**
- With ChaCha20 for AEAD
- Need maximum performance
- Constant-time requirement
- Modern protocol design

**When to use HMAC:**
- Standalone MAC needed
- Key reuse required
- Government compliance (FIPS)
- Existing infrastructure

**When to use AES-GCM:**
- Hardware AES-GCM available
- Existing AES-based system
- Government compliance
- Disk encryption

## Poly1305 vs HMAC

### Design Philosophy

**HMAC:** Generic construction from hash function
```
HMAC-H(key, message) = H((key ⊕ opad) || H((key ⊕ ipad) || message))

Properties:
- Two hash computations
- Works with any hash (SHA-256, SHA-3, etc.)
- No specific mathematical structure
- Security from hash function security
```

**Poly1305:** Purpose-built MAC
```
Poly1305(key, message) = (polynomial_eval(message, r) mod p) + s

Properties:
- Single pass over message
- Specific mathematical structure (polynomial)
- Provable security bounds
- Optimized for performance
```

### Performance

**On x86-64 (cycles per byte):**

| MAC | Software (no HW) | With HW accel |
|-----|------------------|---------------|
| Poly1305 | 1.5-2 | 1.5-2 (same) |
| HMAC-SHA256 | 6-8 | 6-8 (same) |
| HMAC-SHA1 | 4-5 | 4-5 (same) |

**Conclusion:** Poly1305 is 3-4× faster than HMAC

### Security

**HMAC Security:**
```
Based on hash function security
SHA-256: 256-bit output, 128-bit security (birthday bound)
Proven security in random oracle model
```

**Poly1305 Security:**
```
Based on polynomial evaluation
128-bit tag, 128-bit security
Proven security bound: ≤ (ℓ + 1) / 2^106 (ℓ = message blocks)
Concrete security bound (not just asymptotic)
```

## The Mathematics

### Polynomial Evaluation

Poly1305 evaluates polynomial modulo prime:

```
Message blocks: m₁, m₂, ..., mₙ (each 128 bits + 1-bit padding)
Secret point: r (clamped 128-bit value)
Secret offset: s (128-bit value)

Polynomial:
h(m) = m₁·r^n + m₂·r^(n-1) + ... + mₙ·r

Tag:
t = (h(m) mod (2^130 - 5)) + s  mod 2^128
```

### Why This Works (Security)

**Polynomial Collision:**

For two different messages m ≠ m', the tags collide if:

```
h(m) + s ≡ h(m') + s  (mod 2^128)
h(m) ≡ h(m')          (mod p where p = 2^130-5)
```

This means `(h(m) - h(m'))` is divisible by p.

But `h(m) - h(m')` is a non-zero polynomial of degree ≤ n.

**Schwartz-Zippel Lemma:** Non-zero polynomial of degree n has at most n roots.

Therefore: Collision probability ≤ n / p ≈ n / 2^130

For n ≈ 2^24 blocks (16MB message): collision prob ≈ 2^-106

**Conclusion:** Forgery is computationally infeasible.

### Clamping r

Clamping ensures r has specific form:

```
r &= 0x0ffffffc0ffffffc0ffffffc0fffffff

Effect:
- Top 4 bits of each 32-bit word = 0
- Bottom 2 bits of 2nd, 3rd, 4th words = 0

Example:
Original r:  0x85d6be7857556d337f4452fe42d506a8
Clamped r:   0x05d6be7807556d330f4452fc02d50608
             ^         ^         ^         ^
             Top 4 = 0 Bottom 2 = 0
```

**Why clamp?**
- Simplifies constant-time implementation
- Prevents certain mathematical attacks
- Ensures multiplications don't overflow 130 bits

## Implementation Notes

### This Implementation

**Status:** Educational/simplified

**What's simplified:**
- No proper 130-bit arithmetic
- No constant-time guarantees
- No proper modular reduction by (2^130 - 5)
- Placeholder polynomial evaluation

**What's demonstrated:**
- Key structure (r and s)
- Clamping operation
- Block-by-block processing
- High-bit padding
- Final addition

**Educational value:**
- Understand Poly1305 concepts
- See MAC properties
- Learn about single-use keys
- Appreciate implementation complexity

### Production Implementation Requirements

**For production Poly1305:**

1. **130-bit Arithmetic**
   - Proper bignum library
   - Or use limb representation (e.g., 5 × 26-bit limbs)
   - Constant-time operations

2. **Modular Reduction**
   - Efficient reduction mod (2^130 - 5)
   - Barrett reduction or Montgomery multiplication
   - Avoid timing leaks

3. **Constant-Time**
   - No secret-dependent branches
   - No secret-dependent memory access
   - Verify with tools (ctgrind, dudect)

4. **Testing**
   - RFC 7539 test vectors
   - Known-answer tests
   - Cross-validate against libsodium

**Recommended:** Use libsodium's `crypto_onetimeauth_poly1305()`

## Research Lineage

```
Carter-Wegman MAC (1979)
"Universal hashing"
  → One-time MAC construction
    ↓
Poly1305-AES (Bernstein 2005)
"The Poly1305-AES message-authentication code"
  → Fast polynomial MAC
  → AES for key derivation
    ↓
RFC 7539 (2015)
"ChaCha20 and Poly1305 for IETF Protocols"
  → ChaCha20-Poly1305 AEAD
  → Replaces AES with ChaCha20
    ↓
TLS 1.3 (2018)
  → Mandatory cipher suite
    ↓
WireGuard (2020)
  → Modern VPN protocol
    ↓
Production Deployment (2020s)
  → Google, Cloudflare, Signal, OpenSSH
```

**45+ years** from Carter-Wegman MACs to ubiquitous Poly1305 deployment

## Educational Value

This implementation demonstrates:

**1. Polynomial MACs**
- Polynomial evaluation for authentication
- Prime field arithmetic
- Provable security bounds

**2. One-Time MACs**
- Carter-Wegman construction
- Key derivation necessity
- Fresh key per message

**3. Cryptographic Engineering**
- Constant-time requirements
- Implementation pitfalls
- Test vector validation

**4. AEAD Construction**
- Combining encryption + authentication
- ChaCha20-Poly1305 design
- Modern protocol requirements

## Files

```
poly1305/
├── README.md           (this file)
└── poly1305.scm        (simplified implementation)
```

## Dependencies

- Chicken Scheme 5.x
- srfi-4 (homogeneous numeric vectors)
- srfi-13 (string libraries)

## Future Enhancements

**Proper Implementation:**
- [ ] Full 130-bit arithmetic
- [ ] Constant-time operations
- [ ] Proper modular reduction
- [ ] RFC 7539 test vectors
- [ ] Cross-validation with libsodium

**ChaCha20-Poly1305 AEAD:**
- [ ] Integrate with ChaCha20 implementation
- [ ] AEAD construction (encrypt-then-MAC)
- [ ] Associated data support
- [ ] Length encoding

**Applications:**
- [ ] File authentication
- [ ] Network packet authentication
- [ ] Integration with capability system

## Security Warning

**⚠️ DO NOT USE THIS IMPLEMENTATION IN PRODUCTION ⚠️**

This is an educational, simplified implementation that:
- ✗ Does NOT use constant-time arithmetic
- ✗ Does NOT properly implement 130-bit modular reduction
- ✗ Does NOT pass RFC 7539 test vectors
- ✗ WILL leak secrets via timing
- ✗ WILL be vulnerable to forgery attacks

**For production, use:**
- **libsodium** (recommended): `crypto_onetimeauth_poly1305()`
- **OpenSSL**: `EVP_PKEY_new_mac_key()` with Poly1305
- **BoringSSL**: ChaCha20-Poly1305 AEAD

**Why?**
- Constant-time implementation is subtle
- 130-bit arithmetic requires expertise
- Production libraries are audited
- Timing attacks are real

## License

Public domain. Based on Daniel J. Bernstein's Poly1305 design (public domain) and RFC 7539 specification.

---

**"Fast, provably secure, single-use message authentication."**
—The Poly1305 philosophy

**From research to production:**
Carter-Wegman (1979) → Poly1305-AES (2005) → RFC 7539 (2015) → TLS 1.3 (2018) → Everywhere (2020s)
