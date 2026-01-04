# SKIP - Simple Key Management for Internet Protocol

**Collection Date**: 2026-01-04
**Location**: ~/cyberspace/library/cryptographers/key-management-protocols/skip/
**Total Size**: ~75 KB

## Overview

SKIP (Simple Key Management for Internet Protocol) was a key management protocol developed at Sun Microsystems in the mid-1990s as an alternative to IKE for IPsec. Unlike traditional key exchange protocols, SKIP was designed to be completely stateless with zero setup overhead—nodes could begin encrypted communication immediately without prior negotiation. While innovative, SKIP never achieved IETF standardization (remaining an Internet Draft) and saw limited deployment, primarily due to key escrow concerns and the success of IKE.

## Documents Collected

### Protocol Specification (Internet Draft)

**draft-ietf-ipsec-skip-06.txt** (75 KB)
- **Draft**: draft-ietf-ipsec-skip-06
- **Title**: "SKIP - Securing the Internet Using Key Encryption"
- **Authors**: Ashar Aziz, Tom Markson, Hemma Prafullchandra (Sun Microsystems)
- **Date**: Expired (never became RFC)
- **Status**: Internet Draft (Experimental, Never Standardized)
- **Significance**: Stateless key management for IPsec with zero setup overhead
- **Source**: https://www.ietf.org/archive/id/draft-ietf-ipsec-skip-06.txt

**Note**: SKIP never advanced to RFC status, remaining an Internet Draft. This represents the most complete specification (version 6).

## Key Contributions

### Zero-Round-Trip Key Establishment
- **No Handshake**: Nodes can send encrypted packets immediately
- **Stateless Operation**: No session state required
- **Efficiency**: Eliminates handshake latency
- **Innovation**: Radical departure from traditional key exchange

### Certificate-Based Key Distribution
- **Public Key Infrastructure**: Relies on certificates for authentication
- **Kerberos-like Efficiency**: Fast operations using cached certificates
- **Decentralized**: No online third party needed after certificate issuance

### Master Key + Traffic Keys
- **Long-term Master Key**: Derived from Diffie-Hellman using cached public keys
- **Traffic Keys**: Derived from master key using nonces
- **Key Hierarchy**: Separates long-term authentication from session encryption

## Protocol Design

### How SKIP Works

Unlike IKE or Photuris, SKIP has no "negotiation phase":

**Traditional Protocols (IKE, Photuris)**:
```
1. Handshake: Negotiate algorithms, exchange keys (multiple round trips)
2. Data Transfer: Use negotiated keys
```

**SKIP**:
```
1. Data Transfer: Just start sending encrypted packets
   - Include your certificate name in packet header
   - Receiver looks up sender's public key (from cache or certificate server)
   - Receiver derives shared master key (DH with own private key + sender's public key)
   - Receiver derives traffic key from master key + packet nonce
   - Receiver decrypts packet
```

### Packet Format

**SKIP Header** (added to IP packets):
```
+------------------+
| Next Header      | (identifies following header)
| Encrypted Flag   | (indicates if payload encrypted)
| Algorithm ID     | (which encryption/auth algorithms)
| Source NSID      | (Name Space Identifier for sender certificate)
| Dest NSID        | (optional, for receiver certificate)
| Master Key ID    | (which cached master key to use)
| Nonce            | (used to derive traffic key from master key)
+------------------+
| Encrypted Payload (ESP) or Authenticated Payload (AH)
+------------------+
```

### Key Derivation

**Master Key**:
```
Master_Key_AB = g^(a*b) mod p
  where: A's private key = a, A's public key = g^a
         B's private key = b, B's public key = g^b
  (This is Diffie-Hellman)
```

**Traffic Key**:
```
Traffic_Key = HASH(Master_Key_AB || Nonce || Algorithm_ID)
  where: Nonce changes for each packet or session
```

This allows:
- **Perfect Forward Secrecy**: If nonces are ephemeral
- **Efficiency**: Reuse master key (expensive DH) across many traffic keys
- **Stateless**: Receiver can derive keys on demand

## Advantages

### Zero Latency
- **Immediate Communication**: No handshake required
- **No Setup Overhead**: Start encrypting first packet
- **Connectionless**: Works perfectly with UDP, doesn't waste RTT on TCP

### Stateless Operation
- **No State Maintenance**: Server doesn't track sessions
- **Scalability**: Ideal for servers with many clients
- **Crash Recovery**: No state to lose or restore

### Simplicity
- **No Negotiation**: No complex algorithm negotiation
- **Predictable**: Always use same algorithms (configured per node)
- **Easier Implementation**: Less protocol complexity than IKE

## Disadvantages (Why SKIP Failed)

### Key Escrow Concerns

**The Fatal Flaw**: SKIP's design made it attractive for key escrow:

- Master keys derived from long-term DH keys
- With key escrow, government could derive master keys
- Government could then derive all traffic keys
- Essentially: escrow sender's private key → decrypt all communications

During 1990s Crypto Wars:
- Clipper chip controversy was ongoing
- IETF community suspicious of escrow-friendly designs
- SKIP's architecture seen as "too convenient" for surveillance
- Killed political support in IETF

### Lack of Perfect Forward Secrecy (as typically deployed)

- Master key derived from long-term keys
- If private key compromised, all past traffic decryptable (if nonces predictable)
- While SKIP *could* use ephemeral nonces, typical implementations didn't
- IKE's ephemeral DH provided better PFS by default

### Certificate Distribution Problem

- SKIP requires certificates for all communicating parties
- Certificate infrastructure immature in 1990s
- Certificate lookup/caching adds complexity
- "Stateless" only after certificates cached

### No Algorithm Negotiation

- **Rigid**: All nodes must agree on algorithms in advance
- **Inflexible**: Can't adapt to different security requirements
- **Upgrade Path**: Difficult to add new algorithms

### Replay Attack Vulnerability

- Nonces must be carefully managed to prevent replays
- Without state, difficult to reject replayed packets
- IKE's sequence numbers easier to implement correctly

## Historical Context

### IPsec Key Management Competition (1995-1998)

**SKIP's Position**:
- **Strongest Selling Point**: Zero setup overhead (unique among competitors)
- **Corporate Backing**: Sun Microsystems heavily promoted it
- **Technical Innovation**: Truly novel approach

**Why IKE Won**:
1. **Key Escrow Concerns**: Post-Clipper era, IETF hostile to escrow-friendly designs
2. **Feature Completeness**: IKE supported more scenarios (NAT traversal, etc.)
3. **Forward Secrecy**: IKE's PFS more robust
4. **Broader Support**: More vendors backed IKE
5. **Government Preferences**: Military/government preferred IKE's flexibility

### Deployment History

**Limited Adoption**:
- **Sun Solaris**: SKIP shipped with Solaris (Sun's own OS)
- **Export Restrictions**: Crypto export laws limited distribution
- **Network Effect**: Once IKE gained traction, SKIP couldn't compete

**Current Status**:
- **Obsolete**: No modern deployments
- **Historical Artifact**: Studied for protocol design lessons
- **Patents Expired**: Sun's SKIP patents have expired

## Authors

### Ashar Aziz
- **Affiliation**: Sun Microsystems (1990s), later founded FireEye
- **Role**: Primary SKIP designer and architect
- **Contributions**: Stateless key management concept, SKIP protocol design
- **Later Work**: Founded FireEye (cybersecurity company) in 2004

### Tom Markson
- **Affiliation**: Sun Microsystems
- **Role**: SKIP co-designer
- **Contributions**: Protocol specification, implementation

### Hemma Prafullchandra
- **Affiliation**: Sun Microsystems
- **Role**: SKIP co-designer
- **Contributions**: Cryptographic design, specification

## Technical Innovations

### Master Key Caching
- Pre-compute expensive Diffie-Hellman operations
- Cache results for reuse
- Amortize crypto cost across many packets

### Nonce-Based Key Derivation
- Derive per-packet or per-session keys from master key
- Lightweight operation (just a hash)
- Allows key refresh without expensive DH

### Certificate-Based Authentication
- Public key infrastructure for identity
- Decentralized trust model
- Scalable (compared to preshared keys)

## Lessons Learned

### Protocol Design

**Positive Lessons**:
- **Stateless Can Work**: SKIP proved zero-RTT key establishment viable
- **Caching Useful**: Pre-computation and caching can improve performance
- **Simplicity Valuable**: Avoiding negotiation reduces complexity

**Negative Lessons**:
- **Key Escrow Optics**: Protocol design must consider surveillance implications
- **PFS Critical**: Perfect forward secrecy increasingly important (Snowden validated this)
- **Flexibility Needed**: Algorithms must be negotiable, not hardcoded
- **Replay Protection**: Stateless replay protection is hard

### Political Lessons

- **Crypto Wars Impact**: 1990s key escrow debates shaped protocol adoption
- **IETF Culture**: Community values privacy and resists surveillance-friendly designs
- **Timing Matters**: SKIP arrived during peak Clipper chip controversy

## Modern Parallels

### Zero-RTT in Modern Protocols

SKIP's zero-RTT idea lives on in:

**TLS 1.3 (RFC 8446)**:
- **0-RTT Mode**: Client can send encrypted data in first flight
- **Resumption**: Uses cached session tickets
- **Tradeoff**: 0-RTT vulnerable to replay (like SKIP)

**QUIC (RFC 9000)**:
- **0-RTT Connection Establishment**: Similar to SKIP's goals
- **Connection ID**: Cached state for stateless operation
- **Crypto**: Based on TLS 1.3

**Difference**: Modern protocols use ephemeral keys for PFS, unlike SKIP's long-term master keys.

### Stateless Protocols

**DNS over HTTPS (DoH)**:
- Stateless (HTTP)
- Encrypted (TLS)
- Similar philosophy to SKIP (but with modern crypto)

**DTLS (Datagram TLS)**:
- Can operate with minimal state
- Cookie-based DoS protection (Photuris-inspired)

## Related Work in This Collection

### IPsec Key Management
- **photuris/**: Photuris (another IPsec key management alternative)
  - Cookie-based DoS protection
  - Stateful but efficient
- **kaufman/**: IKEv2 (the winner of key management competition)
  - rfc5996-ikev2-2010.txt: Industry standard
  - rfc7296-ikev2-2014.txt: Internet Standard

### Authentication and PKI
- **lampson/**: SDSI/SPKI certificate alternatives
  - spki-certificate-theory-1999.pdf: RFC 2693
- **chaum/**: Digital signatures and trust
- **kerberos/**: Symmetric key authentication (different approach)

### Foundational Crypto
- **diffie-hellman/**: Key exchange foundation for SKIP's master keys
- **schneier/**: Cryptographic algorithm design

### Privacy and Surveillance
- **blaze/**: Clipper chip analysis (context for SKIP's key escrow concerns)
  - clipper-protocol-failure-1994.pdf
  - key-escrow-retrospective-2011.pdf
- **chaum/**: Privacy-preserving protocols

## Citation Examples

When citing SKIP:

**Internet Draft**:
Aziz, A., Markson, T., & Prafullchandra, H. (1996). SKIP - Securing the Internet Using Key Encryption (Internet Draft draft-ietf-ipsec-skip-06). IETF.

**Note**: Since SKIP never became an RFC, it's cited as an Internet Draft. Some papers cite earlier versions (draft-ietf-ipsec-skip-04, etc.) depending on when they were written.

## Further Reading

### IETF Resources
- **IETF IPsec WG Archives**: Historical discussions from 1995-1998
- **Draft Archive**: Multiple SKIP draft versions

### Academic Papers
- Papers comparing SKIP vs IKE vs Photuris (mid-1990s literature)
- Security analyses of SKIP (replay attacks, key management)

### Historical Context
- Crypto Wars history (1990s)
- Clipper chip controversy
- IPsec standardization process

---

**Collection Notes**: SKIP represents a bold attempt to rethink key management, eliminating handshake overhead through stateless operation. While it failed to achieve standardization—partly due to key escrow concerns during the Crypto Wars—its zero-RTT concept lives on in modern protocols like TLS 1.3 and QUIC. SKIP teaches important lessons about protocol design tradeoffs (stateless vs PFS), and the political dimensions of cryptographic protocol standardization.

**Curator**: Collected 2026-01-04 for cyberspace library on key management protocols and cryptographic standards.
