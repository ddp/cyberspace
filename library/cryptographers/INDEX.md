# Cryptographers Collection - Foundational Papers and Protocols

**Collection Date**: 2026-01-03
**Location**: ~/cyberspace/library/cryptographers/
**Total Size**: ~40 MB
**Collections**: 16 subdirectories
**Files**: 80+ papers, RFCs, and standards

## Overview

This collection brings together foundational papers and protocol specifications from twelve of the most influential figures and developments in modern cryptography and network security. From the birth of public-key cryptography in 1976 to modern elliptic curve implementations, from anonymous digital cash to distributed authentication, from IPsec key management to Kerberos authentication, from the first TCP/IP security analysis to the crypto wars of the 1990s, these documents trace the evolution of cryptographic and network security systems that secure today's Internet.

## Collections

### 1. Diffie-Hellman (~260 KB, 1 paper)
**Path**: `diffie-hellman/`

**"New Directions in Cryptography"** (1976)
- Whitfield Diffie & Martin E. Hellman
- Introduced public-key cryptography
- Diffie-Hellman key exchange
- 2015 ACM Turing Award

**Why It Matters**: This single paper changed cryptography forever. Every HTTPS connection, SSH session, and encrypted message starts with ideas from this paper.

**See**: [diffie-hellman/INDEX.md](diffie-hellman/INDEX.md)

### 2. Daniel J. Bernstein (djb) (~3.2 MB, 8 papers)
**Path**: `djb/`

**Modern Cryptographic Primitives**:
- Curve25519 (2006) - Fast elliptic curve Diffie-Hellman
- Ed25519 (2011) - High-speed signatures
- Salsa20/ChaCha20 (2007-2008) - Stream ciphers
- Poly1305-AES (2005) - Message authentication
- NaCl library (2011) - Cryptography engineering
- Cache-timing attacks (2005) - Side-channel analysis

**Why It Matters**: djb's work powers modern secure communications (TLS 1.3, WireGuard, Signal). His focus on performance and side-channel resistance changed how cryptography is implemented.

**See**: [djb/INDEX.md](djb/INDEX.md)

### 3. Bruce Schneier (~1 MB, 2 papers)
**Path**: `schneier/`

**Symmetric Cryptography and Hash Functions**:
- Twofish (1998) - AES finalist block cipher
- Skein (2010) - SHA-3 finalist hash function
- Applied Cryptography (book) - Cryptography "bible"

**Why It Matters**: Schneier's algorithms are deployed worldwide, and his books educated generations of cryptographers and security professionals.

**See**: [schneier/INDEX.md](schneier/INDEX.md)

### 4. Philip Zimmermann (~1.3 MB, 2 documents)
**Path**: `zimmermann/`

**Email Encryption and Privacy**:
- PGP Introduction to Cryptography - Comprehensive crypto primer
- "Cryptography for the Internet" (1998) - Scientific American article
- Pretty Good Privacy (PGP) - First widely-available strong encryption

**Why It Matters**: Zimmermann made military-grade encryption accessible to everyone, sparked policy changes in crypto export laws, and demonstrated that privacy is a human right.

**See**: [zimmermann/INDEX.md](zimmermann/INDEX.md)

### 5. SSH Designers (~220 KB, 4 RFCs)
**Path**: `ssh-designers/`

**Secure Remote Access Protocol**:
- RFC 4251 - SSH Protocol Architecture
- RFC 4252 - SSH Authentication Protocol
- RFC 4253 - SSH Transport Layer Protocol
- RFC 4254 - SSH Connection Protocol
- Created by Tatu Ylönen (1995)

**Why It Matters**: SSH replaced insecure remote login (telnet, rlogin) and became the standard for secure system administration. Every developer and sysadmin uses it daily.

**See**: [ssh-designers/INDEX.md](ssh-designers/INDEX.md)

### 6. Steven M. Bellovin (~810 KB, 4 papers)
**Path**: `bellovin/`

**Network Security and Protocol Analysis**:
- "Security Problems in the TCP/IP Protocol Suite" (1989) - First comprehensive TCP/IP security analysis
- "There be Dragons" (1992) - Early Internet security threats
- "Distributed Firewalls" (1999) - Beyond perimeter defense
- "Using the Domain Name System for System Break-ins" (1995) - DNS security

**Why It Matters**: Bellovin's 1989 TCP/IP security paper is one of the most influential in network security history. He identified fundamental flaws in Internet protocols that are still relevant today, co-authored the definitive book on firewalls, and served on the Privacy and Civil Liberties Oversight Board.

**See**: [bellovin/INDEX.md](bellovin/INDEX.md)

### 7. Matt Blaze (~5.1 MB, 5 papers)
**Path**: `blaze/`

**Cryptography and Key Escrow Analysis**:
- "Protocol Failure in the Escrowed Encryption Standard" (1994) - Discovered Clipper chip flaw
- "Key Escrow from a Safe Distance" (2011) - Crypto wars retrospective
- "A Cryptographic File System for Unix" (1993) - First practical Unix encrypted filesystem
- "Key Management in an Encrypting File System" (1994) - CFS key management
- "Safecracking for the Computer Scientist" (2004) - Physical security analysis

**Why It Matters**: Blaze's discovery of the Clipper chip vulnerability helped end government key escrow proposals in the 1990s. His CFS pioneered practical file system encryption. He remains a leading voice against encryption backdoors and serves on the Tor Project board.

**See**: [blaze/INDEX.md](blaze/INDEX.md)

### 8. David Chaum (~1.8 MB, 4 papers)
**Path**: `chaum/`

**Digital Cash and Anonymous Communications**:
- "Blind Signatures for Untraceable Payments" (1982) - Invented blind signatures
- "Untraceable Electronic Cash" (1988) - Digital cash with double-spending detection
- "Untraceable Electronic Mail, Return Addresses, and Digital Pseudonyms" (1981) - Mix networks
- "The Dining Cryptographers Problem" (1988) - Unconditional anonymity

**Why It Matters**: Chaum is the "father of online anonymity" and "godfather of cryptocurrency." His 1982 work on blind signatures enabled untraceable digital payments decades before Bitcoin. His mix networks are the foundation for Tor. He founded DigiCash and created eCash, the first digital currency (1995).

**See**: [chaum/INDEX.md](chaum/INDEX.md)

### 9. Donald Eastlake (~280 KB, 4 RFCs)
**Path**: `eastlake/`

**DNS Security and Cryptographic Standards**:
- RFC 2535 - DNSSEC (Domain Name System Security Extensions, 1999)
- RFC 2845 - TSIG (DNS Transaction Authentication, 2000)
- RFC 4086 - Randomness Requirements for Security (2005, BCP)
- RFC 2536 - DSA in DNS (1999)

**Why It Matters**: Eastlake authored 107 RFCs, making him one of the most prolific IETF contributors. His DNSSEC specifications secure the Domain Name System, while RFC 4086 is the authoritative guide on cryptographic randomness. His work underpins Internet infrastructure security.

**See**: [eastlake/INDEX.md](eastlake/INDEX.md)

### 10. Butler Lampson (~700 KB, 5 papers)
**Path**: `lampson/`

**Authentication and Distributed Systems Security**:
- "Protection" (1971) - Foundational security paper on access control
- "The Digital Distributed System Security Architecture" (1989) - DSSA with Kaufman, Gasser, Goldstein
- "Authentication in Distributed Systems: Theory and Practice" (1992) - "Speaks for" logic
- "SDSI: A Simple Distributed Security Infrastructure" (1996) - With Rivest
- "SPKI Certificate Theory" (1999, RFC 2693) - With Ylönen, Rivest, Ellison

**Why It Matters**: Lampson is a 2013 Turing Award winner (with Leslie Lamport). His 1971 "Protection" paper introduced capabilities and access control concepts still used today. DSSA pioneered distributed security without central authority. His work with Rivest on SDSI/SPKI provides an alternative to X.509 PKI.

**See**: [lampson/INDEX.md](lampson/INDEX.md)

### 11. Charlie Kaufman (~1 MB, 3 RFCs)
**Path**: `kaufman/`

**IPsec, IKE, and Distributed Authentication**:
- RFC 1507 - DASS (Distributed Authentication Security Service, 1993)
- RFC 5996 - IKEv2 (Internet Key Exchange Protocol v2, 2010)
- RFC 7296 - IKEv2 Internet Standard (2014)
- DSSA co-author (1989) - With Lampson, Gasser, Goldstein

**Why It Matters**: Kaufman designed IKE (Internet Key Exchange), which secures millions of VPN connections worldwide. Co-authored DSSA at DEC. Wrote "Network Security: Private Communication in a Public World" with Radia Perlman. His IKEv2 protocol is the standard for modern VPNs on mobile devices and in cloud infrastructure.

**See**: [kaufman/INDEX.md](kaufman/INDEX.md)

### 12. Key Management Protocols (~1.2 MB, 12 RFCs and documents)
**Path**: `key-management-protocols/`

**Three Approaches to IPsec/Network Key Management**:

**Photuris** (191 KB, 2 RFCs):
- RFC 2522 - Session-Key Management Protocol (1999)
- RFC 2523 - Extended Schemes and Attributes (1999)
- Cookie-based DoS protection (inspired IKEv2)
- Perfect forward secrecy by default
- Lost to IKE but influenced later protocols

**SKIP** (75 KB, 1 Internet Draft):
- draft-ietf-ipsec-skip-06 - Simple Key Management for IP
- Zero-round-trip key establishment
- Stateless operation
- Never standardized (key escrow concerns)

**Kerberos** (881 KB, 6 RFCs):
- RFC 1510 - Kerberos V5 (1993, historic)
- RFC 4120 - Updated Kerberos V5 (2005)
- RFC 3961 - Encryption and Checksum Specifications
- RFC 3962 - AES Encryption for Kerberos
- RFC 4121 - GSS-API Mechanism
- RFC 4556 - PKINIT (Public Key Initial Authentication)
- Symmetric-key authentication protocol
- Centralized KDC (Key Distribution Center)
- Enterprise standard (Active Directory)

**Why It Matters**: These three protocols represent different philosophies for key management and authentication. Photuris and SKIP competed with IKE for IPsec key management in the 1990s—IKE won, but Photuris's cookie mechanism lives on in IKEv2, DTLS, and QUIC. Kerberos took a completely different approach: centralized, symmetric-key authentication that became the foundation of enterprise authentication (Microsoft Active Directory). Together they show the evolution and tradeoffs in key management: stateless vs stateful, centralized vs distributed, symmetric vs asymmetric cryptography.

**See**: [key-management-protocols/photuris/INDEX.md](key-management-protocols/photuris/INDEX.md), [key-management-protocols/skip/INDEX.md](key-management-protocols/skip/INDEX.md), [key-management-protocols/kerberos/INDEX.md](key-management-protocols/kerberos/INDEX.md)

### 13. Ralph Merkle (~13 MB, 5 papers)
**Path**: `merkle/`

**Hash Trees and Public-Key Cryptography Foundations**:
- "Merkle's Puzzles" (1975 draft, published 1978) - Original public-key crypto work (predates Diffie-Hellman by 2 years!)
- PhD Thesis: "Secrecy, Authentication, and Public Key Systems" (1979) - Comprehensive treatment
- **"A Certified Digital Signature" (1979, published CRYPTO '89)** - THE MERKLE TREE PAPER - Foundation for Git, Bitcoin, IPFS
- "Protocols for Public Key Cryptosystems" (1980) - Practical protocols
- "One Way Hash Functions and DES" (1989) - Merkle-Damgård construction (basis for SHA-1, SHA-2, MD5)

**Why It Matters**: Merkle independently invented public-key cryptography in 1974, predating Diffie-Hellman by 2 years (though DH published first in 1976). More importantly, his 1979 hash tree (Merkle tree) construction is fundamental to modern distributed systems: Git uses Merkle trees for content-addressed storage, Bitcoin for transaction verification, IPFS for distributed storage, and Certificate Transparency for auditable logs. **In the quantum era, Merkle's mathematics endures** - hash-based signatures remain secure against quantum computers while RSA/ECC fall to Shor's algorithm.

**See**: [merkle/INDEX.md](merkle/INDEX.md)

### 14. Post-Quantum Cryptography and Signatures (~10 MB, 9 papers and standards)
**Path**: `post-quantum-signatures/`

**Quantum-Resistant Cryptography**:
- **NIST FIPS 203 (2024)** - ML-KEM (lattice-based key encapsulation, replaces Diffie-Hellman)
- **NIST FIPS 204 (2024)** - ML-DSA (lattice-based signatures, replaces RSA/ECDSA)
- **NIST FIPS 205 (2024)** - SLH-DSA (hash-based signatures from SPHINCS+, based on Merkle's work)
- SPHINCS: Practical Stateless Hash-Based Signatures (2015, NIST workshop)
- Hash-Based Signatures Overview (IACR 2023/411)
- Stateless Hash-Based Signatures for Security Keys (IACR 2025/298 - latest research)
- Oded Regev: "On Lattices, Learning with Errors" (2009) - **Foundation for lattice crypto** (basis for FIPS 203/204)
- NTRU: "A Ring-Based Public Key Cryptosystem" (1998) - First practical lattice cryptosystem
- Hash-Based Signatures: Outline for New Standard (NIST 2015)

**Why It Matters**: Shor's algorithm (1997) shows that large-scale quantum computers will break RSA, Diffie-Hellman, and elliptic curve cryptography. NIST finalized three post-quantum standards in August 2024: two based on lattice problems (FIPS 203/204) and one based on hash functions (FIPS 205). **Merkle's hash-based signatures from 1979 become the quantum-resistant conservative choice** - FIPS 205 is literally an evolution of Merkle trees. The lattice-based standards build on Regev's 2005/2009 Learning With Errors (LWE) work. This collection shows the mathematical foundations and the path to standardization.

**See**: [post-quantum-signatures/INDEX.md](post-quantum-signatures/INDEX.md)

### 15. Quantum Algorithms (~374 KB, 2 papers)
**Path**: `quantum-algorithms/`

**The Quantum Threat to Cryptography**:
- **Peter Shor: "Polynomial-Time Algorithms for Prime Factorization"** (1997, arXiv quant-ph/9508027)
  - Breaks RSA (factoring in polynomial time)
  - Breaks Diffie-Hellman (discrete log in polynomial time)
  - Breaks elliptic curve crypto (ECDLP in polynomial time)
  - Catalyzed post-quantum cryptography research
- **Lov Grover: "A Fast Quantum Mechanical Algorithm for Database Search"** (1996, STOC '96)
  - Quadratic speedup for unstructured search O(√N)
  - Weakens symmetric crypto (AES-128 → 64-bit effective security)
  - Weakens hash functions (SHA-256 collision resistance halved)
  - Solution: Double key sizes (AES-256, SHA-512)

**Why It Matters**: These two papers define why we need post-quantum cryptography. Shor's algorithm (1994/1997) completely breaks all number-theory-based public-key crypto. Grover's algorithm (1996) weakens but doesn't break symmetric crypto and hash functions. **Result**: Public-key crypto must move to quantum-resistant alternatives (lattice-based, hash-based, code-based), while symmetric crypto just needs larger keys (256-bit minimum). Merkle's hash-based signatures survive quantum attack while Diffie-Hellman falls.

**See**: [quantum-algorithms/INDEX.md](quantum-algorithms/INDEX.md)

### 16. NRL One-Time Passwords (~410 KB, 4 papers and RFCs)
**Path**: `nrl-one-time-passwords/`

**Hash-Based Authentication Without Public Keys**:
- **Leslie Lamport: "Password Authentication with Insecure Communication" (1981)** - THE FOUNDATIONAL PAPER for one-time passwords
- RFC 1938 - S/KEY One-Time Password System (Neil Haller, 1996)
- RFC 2289 - Updated One-Time Password System (Haller & Metz, 1998)
- **OPIE: "One-time Passwords In Everything" (NRL, USENIX 1995)** - Naval Research Laboratory enhancement to S/KEY
- RFC 2444 - OTP SASL Mechanism (1998)

**Why It Matters**: Lamport's 1981 paper showed how to authenticate securely using only hash functions, even when attackers can eavesdrop on all communications and read the server's password file. His hash chain construction (password = H^n(secret), authenticate with H^(n-1), H^(n-2), etc.) became the basis for S/KEY (Bellcore) and OPIE (Naval Research Laboratory). **Connection to Merkle**: Both use hash functions as the only cryptographic primitive - no need for public-key crypto. Modern descendants include TOTP (Google Authenticator), HOTP (hardware tokens), and FIDO2/WebAuthn. NRL's broader contributions include IPsec, IPv6 security, and network security tools.

**See**: [nrl-one-time-passwords/INDEX.md](nrl-one-time-passwords/INDEX.md)

## Thematic Connections

### Public-Key Cryptography
1. **Foundation**: Diffie-Hellman (1976) - Original concept
2. **Application**: Zimmermann PGP - Email encryption implementation
3. **Modern**: djb Curve25519/Ed25519 - High-performance variants
4. **Deployment**: SSH - Remote login with public key authentication

### Stream Ciphers and Block Ciphers
- **Block Cipher**: Schneier Twofish - AES competition finalist
- **Stream Cipher**: djb Salsa20/ChaCha20 - Modern high-speed design
- **Deployment**: TLS 1.3, WireGuard VPN

### Hash Functions and MACs
- **Hash**: Schneier Skein - SHA-3 competition finalist
- **MAC**: djb Poly1305 - High-speed message authentication
- **Combined**: ChaCha20-Poly1305 AEAD cipher

### Security Analysis
- **Side Channels**: djb cache-timing attacks - Changed implementation practices
- **Cryptanalysis**: Schneier's algorithm analysis - Security evaluation methods
- **Protocol Analysis**: Bellovin TCP/IP security - Network protocol vulnerabilities
- **Real-World Security**: Zimmermann PGP - Usable security for everyone
- **Physical Security**: Blaze safecracking - Cross-domain security analysis

### Network and Protocol Security
- **TCP/IP Vulnerabilities**: Bellovin (1989) - Foundational protocol security analysis
- **Firewall Architecture**: Bellovin distributed firewalls - Defense in depth
- **DNS Security**: Bellovin DNS attacks - Critical infrastructure vulnerabilities
- **Secure Protocols**: SSH as response to problems Bellovin identified

### Crypto Policy and Civil Liberties
- **Clipper Chip**: Blaze's protocol failure discovery - Ended key escrow
- **PGP Export**: Zimmermann's legal battle - Crypto export reform
- **Crypto Wars**: Bellovin, Blaze opposition to government backdoors
- **Modern Debates**: Lessons from 1990s apply to current encryption policy

### Key Management and Authentication
- **Distributed Authentication**: Lampson DSSA, Kaufman DASS - Public-key based, no central authority
- **IPsec Key Management Competition**: Photuris vs SKIP vs IKE - Different approaches to session key establishment
- **Centralized Authentication**: Kerberos - Symmetric-key, KDC-based, enterprise scale
- **Hybrid Approaches**: PKINIT (Kerberos with public-key), IKEv2 (borrowed Photuris cookies)
- **VPN Security**: IKEv2 (Kaufman) won standardization, secures millions of connections
- **Enterprise Security**: Kerberos/Active Directory authentication for Windows domains
- **Design Philosophies**: Stateless (SKIP) vs stateful (IKE), centralized (Kerberos) vs distributed (DSSA)

### Distributed Security Architecture
- **DSSA (1989)**: Lampson, Kaufman, Gasser, Goldstein - No central authority, public-key based
- **DASS (1993)**: Kaufman - Distributed authentication service at DEC
- **SDSI/SPKI**: Lampson, Rivest - Alternative to X.509 PKI
- **Kerberos**: MIT - Centralized alternative using symmetric keys and trusted KDC
- **Contrast**: Kerberos centralized vs DSSA/DASS distributed approaches

## Timeline of Innovations

**1971**: Lampson - "Protection" paper (access control, capabilities)
**1976**: Diffie-Hellman - Public-key cryptography invented
**1981**: Chaum - Mix networks for anonymous email
**1982**: Chaum - Blind signatures for untraceable payments
**1988**: Chaum - Untraceable electronic cash (with Fiat, Naor)
**1988**: Chaum - Dining cryptographers problem
**1989**: Bellovin - First comprehensive TCP/IP security analysis
**1989**: DSSA - Digital Distributed System Security Architecture (Lampson, Kaufman, Gasser, Goldstein)
**1991**: Zimmermann PGP - First widespread public-key encryption
**1992**: Blaze CFS - Cryptographic File System for Unix
**1992**: Bellovin - "There be Dragons" Internet security analysis
**1992**: Lampson - Authentication in distributed systems (with Abadi, Burrows, Wobber)
**1993**: Blaze - CFS paper at first ACM CCS conference
**1993**: Kaufman - DASS (RFC 1507)
**1993**: Kerberos V5 - Original specification (RFC 1510)
**1994**: Blaze - Discovered Clipper chip key escrow flaw
**1994**: Schneier Blowfish - Fast, free block cipher
**1994**: Bellovin & Cheswick - First firewalls book
**1995**: Ylönen SSH-1 - Secure remote login protocol
**1995**: Bellovin - DNS security vulnerabilities
**1995**: DigiCash eCash - First digital currency (Chaum)
**1996**: Lampson - SDSI (with Rivest)
**1998**: Schneier Twofish - AES finalist
**1999**: Bellovin - Distributed firewalls concept
**1999**: Eastlake - DNSSEC (RFC 2535)
**1999**: Photuris - IPsec key management (RFC 2522-2523)
**1999**: Lampson - SPKI/SDSI (RFC 2693, with Ylönen, Rivest, Ellison)
**2000**: Eastlake - TSIG (RFC 2845)
**2004**: Blaze - Safecracking for computer scientists
**2005**: djb Poly1305 - High-speed MAC
**2005**: djb Cache-timing attacks - Side-channel vulnerabilities discovered
**2005**: Eastlake - Randomness Requirements (RFC 4086, BCP)
**2005**: Kerberos V5 - Updated specification (RFC 4120, obsoletes 1510)
**2005**: Kerberos - AES encryption (RFC 3962)
**2006**: djb Curve25519 - Modern elliptic curve cryptography
**2006**: SSH-2 RFCs published - Standardized protocol
**2006**: PKINIT - Public-key initial auth for Kerberos (RFC 4556)
**2008**: djb ChaCha20 - Improved stream cipher
**2010**: Schneier Skein - SHA-3 finalist
**2010**: Kaufman - IKEv2 (RFC 5996)
**2011**: djb Ed25519 - Modern signature algorithm
**2011**: djb NaCl - Easy-to-use crypto library
**2011**: Blaze - Crypto wars retrospective paper
**2014**: Kaufman - IKEv2 Internet Standard (RFC 7296)

## Impact on Modern Security

### TLS/HTTPS (Web Security)
- Diffie-Hellman key exchange (or ECDH variant)
- RSA or Ed25519 certificates
- ChaCha20-Poly1305 or AES-GCM ciphers
- SHA-256/384 hashing

### SSH (System Administration)
- Ed25519 host keys and user keys
- Curve25519 key exchange
- AES or ChaCha20 encryption
- HMAC-SHA2 or Poly1305 MACs

### VPNs (WireGuard)
- Curve25519 for key exchange
- ChaCha20-Poly1305 for encryption/authentication
- No configuration options - one secure choice

### Messaging (Signal, WhatsApp)
- Curve25519 for key agreement
- Ed25519 for identity keys
- AES-GCM or ChaCha20-Poly1305

### Email (PGP/GPG)
- RSA or Ed25519 keys
- AES symmetric encryption
- SHA-2 hashing
- Web of Trust key validation

## Educational Value

### For Cryptography Students
- **Start**: Diffie-Hellman paper - Foundational concepts
- **Algorithms**: Schneier papers - Cipher design principles
- **Modern**: djb papers - High-performance, secure implementations
- **Practical**: Zimmermann PGP - Real-world application
- **Protocols**: SSH RFCs - Complete protocol specification

### For Security Professionals
- **Theory**: All papers provide security analysis and proofs
- **Practice**: Implementation guidance and pitfalls
- **Standards**: RFC specifications for deployments
- **History**: Understanding why things are designed as they are

### For Developers
- **NaCl**: djb's library design - API design for security
- **SSH**: Protocol architecture - Layered security design
- **PGP**: Zimmermann's hybrid approach - Combining primitives
- **Side Channels**: djb's attack paper - Implementation security

## Related Collections in Cyberspace Library

### DSSA-NCSC Papers
- Butler Lampson co-authored DSSA (also co-author with Diffie on some work)
- Public-key infrastructure and distributed authentication
- Contemporary to early PGP development

### Lamport Papers
- Distributed systems security foundations
- Byzantine fault tolerance
- Temporal logic for protocol verification

### SPKI
- Alternative to X.509 certificates
- Tatu Ylönen co-authored SPKI/SDSI specifications (RFC 2693)
- Simpler authorization model

## File Statistics

```
cryptographers/
├── bellovin/               (4 files, 810 KB)
│   ├── INDEX.md
│   ├── distributed-firewalls-1999.pdf
│   ├── dns-break-ins-1995.pdf
│   ├── tcpip-security-problems-1989.pdf
│   └── there-be-dragons-1992.pdf
├── blaze/                  (5 files, 5.1 MB)
│   ├── INDEX.md
│   ├── cfs-cryptographic-file-system-1993.pdf
│   ├── cfs-key-management-1994.pdf
│   ├── clipper-protocol-failure-1994.pdf
│   ├── key-escrow-retrospective-2011.pdf
│   └── safecracking-2004.pdf
├── chaum/                  (4 files, 1.8 MB)
│   ├── INDEX.md
│   ├── blind-signatures-1982.pdf
│   ├── dining-cryptographers-1988.pdf
│   ├── untraceable-electronic-cash-1988.pdf
│   └── untraceable-email-mix-1981.pdf
├── diffie-hellman/         (1 file, 260 KB)
│   ├── INDEX.md
│   └── diffie-hellman-1976-new-directions-in-cryptography.pdf
├── djb/                    (8 files, 3.2 MB)
│   ├── INDEX.md
│   ├── cache-timing-attacks-aes-2005.pdf
│   ├── chacha20-2008.pdf
│   ├── curve25519-2006.pdf
│   ├── ed25519-2011.pdf
│   ├── nacl-security-impact-2011.pdf
│   ├── poly1305-aes-2005.pdf
│   ├── salsa20-family-2007.pdf
│   └── salsa20-spec.pdf
├── eastlake/               (4 files, 280 KB)
│   ├── INDEX.md
│   ├── rfc2535-dnssec-1999.txt
│   ├── rfc2536-dsa-dns-1999.txt
│   ├── rfc2845-tsig-2000.txt
│   └── rfc4086-randomness-2005.txt
├── kaufman/                (3 files, 1 MB)
│   ├── INDEX.md
│   ├── rfc1507-dass-1993.txt
│   ├── rfc5996-ikev2-2010.txt
│   └── rfc7296-ikev2-2014.txt
├── key-management-protocols/ (12 files, 1.2 MB)
│   ├── kerberos/           (6 files, 881 KB)
│   │   ├── INDEX.md
│   │   ├── rfc1510-kerberos-v5-1993.txt
│   │   ├── rfc3961-encryption-checksum-2005.txt
│   │   ├── rfc3962-aes-encryption-2005.txt
│   │   ├── rfc4120-kerberos-v5-2005.txt
│   │   ├── rfc4121-gss-api-v2-2005.txt
│   │   └── rfc4556-pkinit-2006.txt
│   ├── photuris/           (2 files, 191 KB)
│   │   ├── INDEX.md
│   │   ├── rfc2522-photuris-session-key-1999.txt
│   │   └── rfc2523-photuris-extended-schemes-1999.txt
│   └── skip/               (1 file, 75 KB)
│       ├── INDEX.md
│       └── draft-ietf-ipsec-skip-06.txt
├── lampson/                (5 files, 700 KB)
│   ├── INDEX.md
│   ├── authentication-distributed-systems-1992.pdf
│   ├── dssa-1989.pdf
│   ├── protection-1971.pdf
│   ├── sdsi-1996.pdf
│   └── spki-certificate-theory-1999.pdf
├── schneier/               (2 files, 1.0 MB)
│   ├── INDEX.md
│   ├── skein-hash-function-2010.pdf
│   └── twofish-128bit-cipher-1998.pdf
├── ssh-designers/          (4 files, 220 KB)
│   ├── INDEX.md
│   ├── rfc4251-ssh-architecture.txt
│   ├── rfc4252-ssh-authentication.txt
│   ├── rfc4253-ssh-transport.txt
│   └── rfc4254-ssh-connection.txt
└── zimmermann/             (2 files, 1.3 MB)
    ├── INDEX.md
    ├── cryptography-for-internet-sciam-1998.pdf
    └── pgp-intro-to-crypto.pdf
```

## Online Resources

### Official Websites
- **Bellovin**: https://www.cs.columbia.edu/~smb/ - Papers, publications, CV
- **Blaze**: https://www.mattblaze.org/ - Papers, research, blog
- **djb**: https://cr.yp.to/ - Papers, software, research
- **Diffie**: https://whitfielddiffie.com/ - Biography, patents, talks
- **Hellman**: https://ee.stanford.edu/~hellman/ - Publications, peace work
- **Schneier**: https://www.schneier.com/ - Blog, books, academic papers
- **Zimmermann**: https://philzimmermann.com/ - Essays, projects
- **Ylönen**: https://ylonen.org/ - SSH bibliography, research

### Standards Organizations
- **IETF**: https://datatracker.ietf.org/ - RFCs and Internet standards
- **NIST**: https://csrc.nist.gov/ - Crypto standards and competitions

### Software Implementations
- **OpenSSH**: https://www.openssh.com/
- **GnuPG**: https://gnupg.org/
- **libsodium**: https://libsodium.org/ (NaCl-based)
- **WireGuard**: https://www.wireguard.com/

## Awards and Recognition

### Turing Award Winners (ACM)
- **Diffie & Hellman** (2015): "For fundamental contributions to modern cryptography"
- **Lamport & Lampson** (2013): Related distributed systems work

### National Academy of Engineering
- **Steven Bellovin** (2001): "Contributions to network applications and security"

### Internet Hall of Fame
- **Philip Zimmermann** (2012): Pioneer category

### National Cybersecurity Hall of Fame
- **Steven Bellovin** (2012)

### Other Recognition
- **Bellovin**: USENIX Lifetime Achievement Award (2007), Privacy and Civil Liberties Oversight Board (2013-2017)
- **Blaze**: NSF CAREER Award, expert witness, Tor Project board
- **djb**: Multiple academic awards, Test-of-Time awards
- **Schneier**: EFF Pioneer Award, widespread influence
- **Ylönen**: SSH adoption worldwide, IETF contributions

## Further Reading

### Books
- **Applied Cryptography** - Bruce Schneier (1996)
- **Cryptography Engineering** - Ferguson, Schneier, Kohno (2010)
- **Firewalls and Internet Security** - Cheswick, Bellovin, Rubin (1994, 2003)
- **Thinking Security** - Steven M. Bellovin (2016)
- **The Code Book** - Simon Singh (includes Diffie-Hellman history)

### Papers Not in This Collection
- RSA paper (1978) - Rivest, Shamir, Adleman
- Elliptic curve cryptography (1985) - Miller, Koblitz
- AES Rijndael (2000) - Daemen, Rijmen
- Bitcoin paper (2008) - Satoshi Nakamoto (uses ECDSA)

### Related Topics
- Post-quantum cryptography (NIST competition ongoing)
- Zero-knowledge proofs
- Homomorphic encryption
- Secure multi-party computation

---

**Collection Purpose**: This collection preserves seminal works in modern cryptography, from the birth of public-key cryptography to state-of-the-art implementations. Together, these papers tell the story of how cryptography evolved from a military secret to an essential technology protecting billions of people's privacy and security every day.

**Curator**: Collected 2026-01-03 for cyberspace library on distributed systems security and cryptographic protocols.

**Last Updated**: 2026-01-04
