# One-Time Passwords and NRL Security Research

This collection contains papers and RFCs related to one-time password systems, particularly the work done at the Naval Research Laboratory (NRL) and the foundational work by Leslie Lamport and the Bellcore team.

## The One-Time Password Problem

Traditional password authentication is vulnerable to:
- **Eavesdropping**: Attacker intercepts password on the network
- **Replay attacks**: Attacker reuses captured password
- **Server compromise**: Attacker steals password database

One-time passwords (OTPs) solve this by making each password valid for only a single authentication. Even if intercepted, a used OTP cannot be replayed.

## Foundational Work

### lamport-password-authentication-1981.pdf
**Password Authentication with Insecure Communication**
- Leslie Lamport, Communications of the ACM, November 1981
- **THE FOUNDATIONAL PAPER** for one-time passwords
- Shows how to authenticate securely even when:
  - Attacker can read system's password file
  - Attacker can eavesdrop on all communications
- Uses hash chains: password = hash^n(seed)
- Each authentication uses hash^(n-1), hash^(n-2), etc.
- Server stores hash^n and works backwards
- Basis for S/KEY, OPIE, and modern OTP systems

**Lamport's Hash Chain:**
```
User picks secret: S
Computes: H^100(S) = H(H(H(...H(S)...)))
Server stores: H^100(S)

Login 1: User sends H^99(S), server checks H(H^99(S)) == H^100(S) ✓
Login 2: User sends H^98(S), server checks H(H^98(S)) == H^99(S) ✓
...
Login 100: User sends S, server checks H(S) == H^1(S) ✓
```

## Bellcore S/KEY System

### rfc1938-otp-system-1996.txt
**RFC 1938: A One-Time Password System**
- Neil Haller, May 1996
- S/KEY specification (Bellcore implementation of Lamport's scheme)
- Uses MD4 or MD5 hash function
- 64-bit passwords encoded as 6 short words for human readability
- Example: "ROME MUG FRED SCAN LIVE LACE"
- Widely deployed in 1990s Unix systems

### rfc2289-otp-system-1998.txt
**RFC 2289: A One-Time Password System**
- Neil Haller and Craig Metz, February 1998
- Updates and obsoletes RFC 1938
- Adds SHA-1 hash function support
- Improved word encoding dictionary
- Standard OTP format still used today

## Naval Research Laboratory (NRL) Work

### opie-nrl-usenix-1995.txt
**One-Time Passwords in Everything (OPIE): Experiences with Building and Using Strong Authentication**
- Craig Metz, Randall Atkinson, Dan McDonald (NRL)
- USENIX Security Symposium, 1995
- **OPIE = NRL's enhancement of S/KEY**
- Developed at US Naval Research Laboratory
- Improvements over S/KEY:
  - Better integration with system services
  - Support for FTP with OTPs
  - Stronger hash algorithms
  - Cleaner codebase and API
  - Better handling of edge cases

**NRL Security Research:**
The Naval Research Laboratory has been a major contributor to Internet security:
- **OPIE**: One-time passwords
- **IPsec**: Original implementation and research
- **IPv6 security**: Early security analysis
- **Secure routing protocols**: Research and implementation

### rfc2444-otp-sasl-1998.txt
**RFC 2444: The One-Time-Password SASL Mechanism**
- Chris Newman, October 1998
- Integrates OTP into SASL (Simple Authentication and Security Layer)
- Enables OTP for: IMAP, POP3, ACAP, LDAPv3, SMTP
- Formal specification for OTP in modern protocols

## Historical Timeline

1. **1981**: Lamport invents one-time passwords (hash chains)
2. **Late 1980s**: Bellcore develops S/KEY (Haller, Karn, Walden)
3. **1995**: NRL develops OPIE (improvement on S/KEY)
4. **1996**: RFC 1938 standardizes S/KEY-style OTP
5. **1998**: RFC 2289 updates OTP standard
6. **1998**: RFC 2444 integrates OTP with SASL
7. **2000s**: Hardware tokens and TOTP/HOTP (RFC 4226, 6238) emerge
8. **2010s**: Smartphone apps replace hardware tokens
9. **2020s**: FIDO2/WebAuthn move beyond passwords entirely

## Why One-Time Passwords Matter

**Security properties:**
- ✓ Immune to eavesdropping (password only good once)
- ✓ Immune to replay attacks (used password is worthless)
- ✓ Safe even if server is compromised (forward security)
- ✓ No shared secrets stored on server
- ✓ Works over insecure channels

**Limitations:**
- ✗ Vulnerable to man-in-the-middle during active session
- ✗ Requires synchronized state (which password number)
- ✗ Finite sequence (must reinitialize after N logins)
- ✗ User must compute hash or carry token

**Modern descendants:**
- **TOTP** (Time-based OTP, RFC 6238): Google Authenticator, Authy
- **HOTP** (HMAC-based OTP, RFC 4226): Hardware tokens
- **FIDO U2F/FIDO2**: Cryptographic hardware keys (YubiKey)

## The Hash Function Connection

Lamport's one-time passwords rely on:
- **One-way hash functions**: Easy to compute H(x), hard to invert
- **Hash chains**: Repeated application H^n(x)
- **Preimage resistance**: Can't find x given H(x)

This connects to:
- **Merkle trees**: Another hash-based construction (1979)
- **Bitcoin mining**: Hash chain-based proof of work
- **Blockchain**: Hash chains for immutability

**Lamport's insight**: You don't need public-key crypto for authentication over insecure channels - hash functions suffice.

## NRL's Broader Security Impact

The Naval Research Laboratory has contributed significantly to Internet security beyond OPIE:
- IPv6 security research and early implementations
- IPsec protocol development and reference implementations
- Secure routing protocol research
- Network security tool development
- Applied cryptography research for government and defense

## Sources

Papers and RFCs obtained from:
- Leslie Lamport's website: https://lamport.azurewebsites.net/
- IETF RFC Editor: https://www.rfc-editor.org/
- USENIX archives: https://www.usenix.org/legacy/
- Naval Research Laboratory publications
