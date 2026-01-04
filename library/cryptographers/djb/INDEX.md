# Daniel J. Bernstein (djb) - Cryptography Papers

**Collection Date**: 2026-01-03
**Location**: ~/cyberspace/library/cryptographers/djb/
**Total Size**: ~3.2 MB

## Overview

Daniel J. Bernstein is a mathematician and cryptographer known for creating several widely-used cryptographic primitives including Curve25519, Ed25519, Salsa20, ChaCha20, and the NaCl cryptography library. His work emphasizes both security and performance, with particular attention to side-channel resistance and high-speed implementations.

## Papers Collected

### Elliptic Curve Cryptography

**curve25519-2006.pdf** (224 KB)
- **Title**: "Curve25519: new Diffie-Hellman speed records"
- **Published**: 2006, PKC 2006 proceedings
- **Significance**: Introduced Curve25519, a highly efficient elliptic curve for Diffie-Hellman key exchange
- **Award**: 2022 PKC Test-of-Time Award
- **Source**: https://cr.yp.to/ecdh/curve25519-20060209.pdf

**ed25519-2011.pdf** (471 KB)
- **Title**: "High-speed high-security signatures"
- **Published**: 2011
- **Significance**: Ed25519 signature scheme based on Edwards curves, widely adopted in SSH, TLS, cryptocurrencies
- **Source**: https://ed25519.cr.yp.to/ed25519-20110926.pdf

### Stream Ciphers

**salsa20-family-2007.pdf** (172 KB)
- **Title**: "The Salsa20 family of stream ciphers"
- **Published**: 2007
- **Significance**: Foundational paper on Salsa20 design decisions and cipher family
- **Source**: https://cr.yp.to/snuffle/salsafamily-20071225.pdf

**salsa20-spec.pdf** (74 KB)
- **Title**: "Salsa20 specification"
- **Significance**: Formal specification of the Salsa20 hash function, expansion function, and encryption function
- **Source**: https://cr.yp.to/snuffle/spec.pdf

**chacha20-2008.pdf** (109 KB)
- **Title**: "ChaCha, a variant of Salsa20"
- **Published**: 2008
- **Significance**: ChaCha20 improved upon Salsa20 with better diffusion; now used in TLS and WireGuard
- **Source**: https://cr.yp.to/chacha/chacha-20080128.pdf

### Message Authentication

**poly1305-aes-2005.pdf** (1.4 MB)
- **Title**: "The Poly1305-AES message-authentication code"
- **Published**: 2005, FSE 2005 proceedings
- **Significance**: High-speed MAC used in combination with ChaCha20 in modern protocols
- **Source**: https://cr.yp.to/mac/poly1305-20050329.pdf

### Cryptographic Libraries

**nacl-security-impact-2011.pdf** (280 KB)
- **Title**: "The security impact of a new cryptographic library"
- **Authors**: Daniel J. Bernstein, Tanja Lange, Peter Schwabe
- **Published**: 2011, LatinCrypt 2012 proceedings
- **Significance**: Describes NaCl (Networking and Cryptography library) design philosophy
- **Source**: https://cryptojedi.org/papers/coolnacl-20111201.pdf

### Security Analysis

**cache-timing-attacks-aes-2005.pdf** (416 KB)
- **Title**: "Cache-timing attacks on AES"
- **Published**: 2005
- **Significance**: Demonstrated practical side-channel attacks against AES implementations
- **Impact**: Changed how cryptographic software is implemented (constant-time requirements)
- **Source**: https://cr.yp.to/antiforgery/cachetiming-20050414.pdf

## Key Contributions

### Cryptographic Primitives
- **Curve25519**: Fast, secure elliptic curve Diffie-Hellman
- **Ed25519**: Edwards curve digital signature algorithm
- **Salsa20/ChaCha20**: High-speed stream ciphers
- **Poly1305**: Fast message authentication code

### Design Philosophy
- **High performance**: Optimized implementations without sacrificing security
- **Side-channel resistance**: Constant-time operations to prevent timing attacks
- **Simplicity**: Clean, auditable code and clear specifications
- **Public domain**: Most work released without patents or restrictive licenses

## Adoption

Bernstein's work has been adopted widely:
- **TLS 1.3**: ChaCha20-Poly1305 cipher suite
- **SSH**: Ed25519 host keys and user authentication
- **WireGuard VPN**: Curve25519 and ChaCha20-Poly1305
- **Signal Protocol**: Curve25519 for key agreement
- **Cryptocurrencies**: Ed25519 signatures (Stellar, Cardano, others)
- **libsodium**: Popular crypto library based on NaCl

## Related Work

- **Post-quantum cryptography**: NTRU Prime, SPHINCS+
- **Safe curves**: Criteria for secure elliptic curve selection
- **qmail**: Secure mail transfer agent
- **djbdns**: Secure DNS implementation

## Additional Resources

- **Personal website**: https://cr.yp.to/
- **Papers index**: https://cr.yp.to/papers.html
- **Google Scholar**: Highly cited cryptography researcher
- **Competitions**: eSTREAM (Salsa20), NIST post-quantum crypto

## Citation Examples

When citing these works:

**Curve25519**:
Bernstein, D. J. (2006). Curve25519: new Diffie-Hellman speed records. In Public Key Cryptography-PKC 2006 (pp. 207-228). Springer.

**Ed25519**:
Bernstein, D. J., Duif, N., Lange, T., Schwabe, P., & Yang, B. Y. (2011). High-speed high-security signatures. Journal of Cryptographic Engineering, 2(2), 77-89.

**ChaCha20**:
Bernstein, D. J. (2008). ChaCha, a variant of Salsa20. Workshop Record of SASC, 8, 3-5.

---

**Collection Notes**: These papers represent some of the most influential work in modern cryptography, combining rigorous security analysis with practical, high-performance implementations. Bernstein's emphasis on resistance to side-channel attacks has fundamentally changed how cryptographic software is developed.

**Curator**: Collected 2026-01-03 for cyberspace library on distributed systems security and cryptographic protocols.
