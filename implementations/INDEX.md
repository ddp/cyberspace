# Cyberspace Implementations

**Practical implementations of research from the Library of Cyberspace**

This directory contains working code that implements ideas from the research papers collected in `~/cyberspace/library/`. Each implementation demonstrates how foundational computer science research translates into practical systems.

## Philosophy

> "Research papers are not just history—they're blueprints for building systems."

The Library of Cyberspace contains decades of foundational research. This directory brings those ideas to life through working implementations.

## Implementations

### Lamport One-Time Passwords (`lamport-otp/`)

**From**: Leslie Lamport (1981), "Password Authentication with Insecure Communication"
**Paper Location**: `~/cyberspace/library/cryptographers/nrl-one-time-passwords/`

**What It Does**:
- Hash-chain authentication system
- One-time password generation and verification
- Resistant to eavesdropping and replay attacks

**Status**: ✅ Working implementation in Chicken Scheme

**Quick Start**:
```bash
cd lamport-otp
./lamport.scm generate alice "secret-seed" 100
./lamport.scm verify alice <password-from-book>
./lamport.scm status alice
```

**Research → Practice**:
- Demonstrates cryptographic hash properties (one-way functions)
- Shows forward security (past passwords don't reveal future ones)
- Illustrates practical security protocol design
- Still relevant 40+ years later (blockchain, Git use hash chains)

### Merkle Trees (`merkle-tree/`)

**From**: Ralph Merkle (1979), "A Certified Digital Signature"
**Paper Location**: `~/cyberspace/library/cryptographers/merkle/`

**What It Does**:
- Build Merkle trees for authenticated data structures
- Generate and verify inclusion proofs (O(log n))
- Content-addressable storage (Git-like)
- Create commit snapshots

**Status**: ✅ Working implementation in Chicken Scheme

**Quick Start**:
```bash
cd merkle-tree
./merkle.scm build "alice" "bob" "carol" "dave"
./merkle.scm prove "bob" "alice" "bob" "carol" "dave"
./merkle.scm commit "Initial commit" file1.txt file2.txt
```

**Research → Practice**:
- Powers Git (content-addressable storage, commits, trees, blobs)
- Powers Bitcoin (Merkle tree of transactions in each block)
- Powers IPFS (Merkle DAG for distributed storage)
- Powers Certificate Transparency (append-only logs)
- Single root hash authenticates entire dataset

### Capability-Based Authentication (`capabilities/`)

**From**: Butler Lampson & others (1970s-1980s), "Protection" (1971), "Authentication in Distributed Systems" (1992)
**Paper Location**: `~/cyberspace/library/cryptographers/lampson/`

**What It Does**:
- Unforgeable access tokens (HMAC-signed)
- Delegation with attenuation (subset of rights)
- Time-limited access (expiry timestamps)
- No ambient authority (possession = authority)

**Status**: ✅ Working implementation in Chicken Scheme

**Quick Start**:
```bash
cd capabilities
./capabilities.scm demo-basic        # Basic operations
./capabilities.scm demo-serialize    # Unforgeable tokens
./capabilities.scm demo-delegation   # Delegation chain
./capabilities.scm demo-expiry       # Time-limited access
```

**Research → Practice**:
- Powers seL4 microkernel (capability-based OS)
- Powers CloudFlare Workers (V8 isolates with capabilities)
- Powers Amazon S3 pre-signed URLs (time-limited capability tokens)
- Powers WebAssembly WASI (capability-based system interface)
- Demonstrates "don't separate designation from authority"

### ChaCha20 Stream Cipher (`chacha20/`)

**From**: Daniel J. Bernstein (2008), "ChaCha, a variant of Salsa20"
**RFC**: RFC 7539 (2015), "ChaCha20 and Poly1305 for IETF Protocols"
**Paper Location**: `~/cyberspace/library/cryptographers/djb/chacha20-2008.pdf`

**What It Does**:
- Fast, secure stream cipher using ARX operations
- 256-bit key, 96-bit nonce, 32-bit counter
- Constant-time (no timing attacks)
- 20 rounds of quarter-round mixing

**Status**: ✅ Working implementation in Chicken Scheme

**Quick Start**:
```bash
cd chacha20
./chacha20.scm test         # RFC 7539 test vectors
./chacha20.scm demo-basic   # Basic encryption
./chacha20.scm demo-stream  # Stream cipher properties
./chacha20.scm demo-nonce   # Nonce importance
```

**Research → Practice**:
- Powers TLS 1.3 (ChaCha20-Poly1305 cipher suite)
- Powers WireGuard VPN (all encrypted tunnels)
- Powers Google QUIC/HTTP/3 (default cipher)
- Powers OpenSSH (chacha20-poly1305@openssh.com)
- Used by Signal, WhatsApp end-to-end encryption
- ARX construction: constant-time, no cache-timing attacks

### Poly1305 MAC (`poly1305/`)

**From**: Daniel J. Bernstein (2005), "The Poly1305-AES message-authentication code"
**RFC**: RFC 7539 (2015), "ChaCha20 and Poly1305 for IETF Protocols"
**Paper Location**: `~/cyberspace/library/cryptographers/djb/poly1305-aes-2005.pdf`

**What It Does**:
- Fast message authentication code (MAC)
- Polynomial evaluation in prime field (2^130 - 5)
- 128-bit authentication tag
- Single-use key (derived from ChaCha20 or AES)

**Status**: ⚠️ Educational implementation (simplified, not production-ready)

**Quick Start**:
```bash
cd poly1305
./poly1305.scm demo-basic       # Basic MAC computation
./poly1305.scm demo-properties  # MAC properties
```

**Research → Practice**:
- Powers TLS 1.3 (with ChaCha20 as AEAD)
- Powers WireGuard VPN (ChaCha20-Poly1305 AEAD)
- Powers OpenSSH (chacha20-poly1305@openssh.com)
- Used in Signal, WhatsApp (ChaCha20-Poly1305)
- Polynomial MAC: provable security, 1-2 cycles/byte

**Note**: Full implementation requires careful 130-bit constant-time arithmetic. This is an educational demonstration of concepts.

## Future Implementations

### Cryptographic File System (`cfs/`)

**From**: Matt Blaze (1993), "A Cryptographic File System for Unix"
**Paper Location**: `~/cyberspace/library/cryptographers/blaze/`

**Planned Features**:
- Transparent encryption for directories
- Modern crypto (AES instead of DES)
- Password-based key derivation

### Microkernel IPC (`l4-ipc/`)

**From**: Jochen Liedtke (1993), "Improving IPC by Kernel Design"
**Paper Location**: `~/cyberspace/library/verified-systems/l4-microkernel/`

**Planned Features**:
- Fast inter-process communication
- Demonstrates minimality principle
- Educational microkernel concepts

## Design Principles

### 1. Faithful to Research

Each implementation should:
- Reference the original paper
- Explain the core concept
- Maintain the spirit of the design
- Note where we deviate (e.g., modern crypto vs 1980s DES)

### 2. Practical and Usable

Code should be:
- Runnable on modern systems
- Well-documented
- Demonstrative (shows the idea clearly)
- Educational (helps understand the paper)

### 3. Simple Over Complex

Following the Scheme aesthetic:
- Clear, readable code
- Minimal dependencies
- Composable functions
- REPL-friendly

### 4. Security Conscious

When implementing cryptographic systems:
- Use modern, secure primitives
- Don't roll your own crypto (use OpenSSL, libsodium, etc.)
- Document security properties and limitations
- Note attacks and mitigations

## Educational Value

These implementations demonstrate:

**Cryptography Concepts**:
- Hash chains (Lamport OTP)
- Merkle trees (content addressing)
- HMAC authentication (capabilities)
- Unforgeable tokens (capabilities)
- Stream ciphers (ChaCha20)
- ARX construction (ChaCha20)
- Public-key systems (future)
- Zero-knowledge proofs (future)

**System Design**:
- Microkernel architecture
- Capability-based security
- File system encryption
- Network protocols

**Software Engineering**:
- Protocol design
- State management
- Error handling
- Testing security properties

## Research Lineage

Each implementation connects to a lineage of research:

```
Lamport OTP (1981)
    → S/KEY (Bellcore 1995)
    → OPIE (NRL 1995)
    → RFC 2289 (IETF 1998)
    → Modern 2FA (TOTP, HOTP)
    → Blockchain (Bitcoin, Ethereum)

Merkle Trees (1979)
    → Git (2005)
    → Bitcoin (2009)
    → IPFS (2014)
    → Certificate Transparency (2013)

Capabilities (1970s)
    → seL4 (2009)
    → CloudFlare Workers (2018)
    → WebAssembly capabilities (2020s)
```

## Contributing New Implementations

To add a new implementation:

1. **Pick a paper** from `~/cyberspace/library/`
2. **Create directory**: `implementations/<name>/`
3. **Write code**: Implement the core concept
4. **Document thoroughly**:
   - README.md explaining the concept
   - Reference to original paper
   - Usage examples
   - Security considerations
5. **Test it**: Demonstrate it works
6. **Update this INDEX.md**

### Implementation Checklist

- [ ] References original paper(s)
- [ ] Explains core concept clearly
- [ ] Includes working code
- [ ] Has comprehensive README
- [ ] Documents security properties
- [ ] Provides usage examples
- [ ] Notes limitations and future work

## Connection to the Library

Each implementation should link back to research:

| Implementation | Papers | Library Location | Status |
|---------------|--------|------------------|--------|
| Lamport OTP | Lamport 1981, OPIE 1995 | `library/cryptographers/nrl-one-time-passwords/` | ✅ |
| Merkle Tree | Merkle 1979 | `library/cryptographers/merkle/` | ✅ |
| Capability Auth | Lampson 1971, DSSA 1992 | `library/cryptographers/lampson/` | ✅ |
| ChaCha20 | Bernstein 2008, RFC 7539 | `library/cryptographers/djb/` | ✅ |
| Poly1305 | Bernstein 2005, RFC 7539 | `library/cryptographers/djb/` | ⚠️ |
| CFS | Blaze 1993 | `library/cryptographers/blaze/` | 📋 |
| L4 IPC | Liedtke 1993 | `library/verified-systems/l4-microkernel/` | 📋 |

## Research → Practice Pipeline

```
┌─────────────────┐
│  Library        │  Papers, RFCs, standards
│  (Research)     │  Historical context
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│  Librarian      │  AI-powered search
│  (Discovery)    │  "Find papers about X"
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│  Implementations│  Working code
│  (Practice)     │  Demonstrates concepts
└─────────────────┘
```

The cycle:
1. **Discover** research via Librarian queries
2. **Study** papers in Library
3. **Implement** concepts in practice
4. **Learn** by building

## Status

**✅ Implemented**:
- Lamport One-Time Passwords (hash-chain authentication)
- Merkle Trees (authenticated data structures, content-addressable storage)
- Capability-Based Authentication (unforgeable tokens, delegation, time-limited access)
- ChaCha20 Stream Cipher (ARX construction, constant-time encryption)

**⚠️ Educational (Simplified)**:
- Poly1305 MAC (polynomial message authentication - concept demonstration)

**🚧 In Progress**:
- (None currently)

**📋 Planned**:
- Lamport Signatures (hash-based digital signatures)
- Lamport Clocks (logical time for distributed systems)
- ChaCha20-Poly1305 AEAD (full authenticated encryption)
- Cryptographic File System (transparent encryption)
- L4-style IPC (microkernel messaging)

## License & Attribution

Each implementation:
- Attributes original authors and papers
- Respects original licenses
- Adds own code under permissive license
- Clearly separates research from implementation

Most foundational research papers are in public domain or have permissive educational use.

---

**"Standing on the shoulders of giants—and implementing their ideas."**

*Weaving Cyberspace into existence through practical implementations of foundational research.*
