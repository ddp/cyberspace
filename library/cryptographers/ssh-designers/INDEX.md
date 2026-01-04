# SSH (Secure Shell) - Protocol Specifications

**Collection Date**: 2026-01-03
**Location**: ~/cyberspace/library/cryptographers/ssh-designers/
**Total Size**: ~220 KB

## Overview

SSH (Secure Shell) is a cryptographic network protocol for operating network services securely over an unsecured network. Created by Tatu Ylönen in 1995, SSH has become the standard for secure remote login, replacing insecure protocols like telnet, rlogin, and rsh. This collection contains the official IETF protocol specifications (RFCs 4251-4254).

## RFCs Collected

**rfc4251-ssh-architecture.txt** (70 KB)
- **RFC**: 4251
- **Title**: "The Secure Shell (SSH) Protocol Architecture"
- **Authors**: T. Ylonen, C. Lonvick (Ed.)
- **Date**: January 2006
- **Status**: Proposed Standard
- **Description**: Describes SSH architecture, notation, and terminology
- **Source**: https://www.ietf.org/rfc/rfc4251.txt

**rfc4252-ssh-authentication.txt** (33 KB)
- **RFC**: 4252
- **Title**: "The Secure Shell (SSH) Authentication Protocol"
- **Authors**: T. Ylonen, C. Lonvick (Ed.)
- **Date**: January 2006
- **Status**: Proposed Standard
- **Description**: SSH authentication framework and methods (public key, password, host-based)
- **Source**: https://www.rfc-editor.org/rfc/rfc4252.txt

**rfc4253-ssh-transport.txt** (67 KB)
- **RFC**: 4253
- **Title**: "The Secure Shell (SSH) Transport Layer Protocol"
- **Authors**: T. Ylonen, C. Lonvick (Ed.)
- **Date**: January 2006
- **Status**: Proposed Standard
- **Description**: SSH transport layer (runs over TCP/IP), key exchange, encryption, MAC
- **Source**: https://www.rfc-editor.org/rfc/rfc4253.txt

**rfc4254-ssh-connection.txt** (49 KB)
- **RFC**: 4254
- **Title**: "The Secure Shell (SSH) Connection Protocol"
- **Authors**: T. Ylonen, C. Lonvick (Ed.)
- **Date**: January 2006
- **Status**: Proposed Standard
- **Description**: Interactive sessions, remote command execution, TCP/IP forwarding, X11 forwarding
- **Source**: https://www.rfc-editor.org/rfc/rfc4254.txt

## SSH Protocol Architecture

### Protocol Layers

1. **Transport Layer (RFC 4253)**:
   - Server authentication
   - Confidentiality (encryption)
   - Integrity (MAC)
   - Key exchange
   - Compression (optional)

2. **Authentication Protocol (RFC 4252)**:
   - Client authentication
   - Multiple authentication methods
   - Extensible framework

3. **Connection Protocol (RFC 4254)**:
   - Multiple channels over single connection
   - Interactive login sessions
   - Remote command execution
   - Port forwarding (local and remote)
   - X11 forwarding

## History and Development

### Original Development (1995-1996)

**Creator**: Tatu Ylönen (Helsinki University of Technology, Finland)
**Motivation**: Password sniffing attack at his university network
**Initial Release**: July 1995 (SSH-1)
**Philosophy**: "Freely available for non-commercial use"

**Original Paper**:
- "SSH - Secure Login Connections over the Internet"
- 6th USENIX Security Symposium, 1996
- Pages 37-42 in Proceedings

### SSH Protocol Versions

**SSH-1** (1995):
- Original protocol
- Security vulnerabilities discovered
- Now deprecated

**SSH-2** (2006):
- Complete redesign
- Incompatible with SSH-1
- RFCs 4251-4254 (these documents)
- Current standard

**SSH-3**: Not a real version (common misconception)

### Standardization

**IETF Working Group**: Secsh (Secure Shell)
**Lead Authors**:
- Tatu Ylönen (SSH Communications Security)
- Chris Lonvick (Cisco Systems)
- Tero Kivinen, Timo Rinne, Sami Lehtinen (SSH Communications Security)

**Related RFCs**:
- Many additional RFCs for extensions and algorithms
- Key exchange methods, authentication methods
- File transfer (SFTP), subsystems

## Key Features

### Security Properties

**Confidentiality**:
- Symmetric encryption (AES, ChaCha20, 3DES)
- Session key derived from key exchange
- Perfect forward secrecy (with ephemeral key exchange)

**Integrity**:
- MAC (Message Authentication Code)
- HMAC-SHA1, HMAC-SHA2, Poly1305
- Prevents tampering

**Authentication**:
- Server: Host keys (public key cryptography)
- Client: Multiple methods supported
  - Public key authentication (most secure)
  - Password authentication
  - Host-based authentication

### Cryptographic Algorithms

**Key Exchange**:
- Diffie-Hellman (original)
- Elliptic Curve Diffie-Hellman (modern)
- Curve25519 (recommended)

**Public Key**:
- RSA
- DSA
- ECDSA
- Ed25519 (modern recommendation)

**Symmetric Ciphers**:
- AES (AES-128-CTR, AES-256-GCM)
- ChaCha20-Poly1305 (modern)
- 3DES-CBC (legacy)

**MAC Algorithms**:
- HMAC-SHA1
- HMAC-SHA2-256, HMAC-SHA2-512
- Poly1305 (with ChaCha20)

## Use Cases

### Remote Login
- Secure terminal access
- Replacement for telnet, rlogin
- Shell access to remote systems

### File Transfer
- SFTP (SSH File Transfer Protocol)
- SCP (Secure Copy)
- Replacement for FTP, rcp

### Port Forwarding
- Local port forwarding
- Remote port forwarding
- Dynamic forwarding (SOCKS proxy)
- VPN-like functionality

### Tunneling
- X11 forwarding (remote GUI)
- TCP/IP tunneling
- Secure channels for other protocols

## Implementations

### Open Source
- **OpenSSH**: Most widely used (OpenBSD project)
- **Dropbear**: Lightweight implementation
- **libssh**: Library for embedding SSH
- **PuTTY**: Windows SSH client

### Commercial
- **SSH Communications Security**: Original company
- **Tectia SSH**: Enterprise solution
- **Bitvise SSH**: Windows implementation

### Embedded
- Cisco, Juniper, Arista network equipment
- Git (git://, ssh:// protocols)
- rsync over SSH

## Modern Extensions

**Certificate Authentication** (RFC 6187):
- X.509 certificates for SSH
- PKI integration

**Authenticated Encryption** (RFC 5647):
- AES-GCM
- Combined encryption and MAC

**ChaCha20-Poly1305** (RFC 8308):
- Modern cipher suite
- High performance on platforms without AES hardware

**Curve25519 and Ed25519** (RFC 8709):
- Modern elliptic curves
- djb's high-security, high-performance algorithms

## Security Considerations

### Best Practices

**Key Management**:
- Use Ed25519 keys for new deployments
- Regular key rotation
- Strong passphrases for private keys
- SSH-agent for key management

**Configuration**:
- Disable password authentication (use keys)
- Disable SSH-1 protocol
- Restrict allowed algorithms to strong ones
- Use fail2ban or similar for brute-force protection

**Host Key Verification**:
- Verify host keys on first connection
- TOFU (Trust On First Use) model
- DNS-based key distribution (SSHFP records)

### Known Vulnerabilities

**Timing Attacks**: Side-channel attacks on SSH
**Terrapin Attack** (2023): Prefix truncation in SSH protocol
**Mitigations**: Keep implementations updated, use modern algorithms

## Tatu Ylönen

**Background**:
- Ph.D. from Helsinki University of Technology
- Founded SSH Communications Security (1995)
- Multiple contributions to IETF standards

**Additional Work**:
- SPKI/SDSI certificate theory (RFC 2693)
- SSH key management research
- Database concurrency control
- Natural language processing (Wiktextract)

**Resources**:
- Homepage: https://ylonen.org/
- SSH Bibliography: https://ylonen.org/ssh/bibliography.html
- Google Scholar: Extensive publications

## Impact and Adoption

### Ubiquity
- Pre-installed on nearly all Unix-like systems
- Default remote access method
- Millions of servers worldwide
- Critical infrastructure component

### GitHub and Git
- Primary authentication method
- SSH keys for commit signing
- Secure repository access

### DevOps and Cloud
- Ansible, Terraform, Puppet
- AWS, Azure, GCP instance access
- Container orchestration (Kubernetes)

### IoT and Embedded
- Router and switch management
- IoT device management
- Embedded Linux systems

## Related Papers in This Collection

- **diffie-hellman/**: Key exchange protocol used in SSH
- **djb/curve25519-2006.pdf**: Modern SSH key exchange
- **djb/ed25519-2011.pdf**: Modern SSH host keys and user authentication
- **dssa-ncsc-papers/**: Alternative approaches to distributed authentication

## Additional Resources

### Official Sites
- **OpenSSH**: https://www.openssh.com/
- **IETF Secsh WG**: https://datatracker.ietf.org/wg/secsh/
- **SSH.com**: https://www.ssh.com/ (commercial)

### Documentation
- OpenSSH Manual Pages
- RFC Index: https://www.ietf.org/rfc/ (search "SSH")
- SSH Academy: https://www.ssh.com/academy/ssh

### Security
- **CVE Database**: Search "SSH" for vulnerabilities
- **Security Advisories**: OpenSSH announcements
- **Best Practices**: NIST SP 800-77 (Guide to IPsec VPNs includes SSH)

## Citation Example

When citing the SSH protocol:

Ylonen, T., & Lonvick, C. (Eds.). (2006). The Secure Shell (SSH) Protocol Architecture (RFC 4251). RFC Editor.

Ylonen, T., & Lonvick, C. (Eds.). (2006). The Secure Shell (SSH) Transport Layer Protocol (RFC 4253). RFC Editor.

## Quotes

From Tatu Ylönen on creating SSH:
> "I wanted to protect the passwords on the network. My idea was to create a new secure remote login protocol that would not send passwords in the clear."

> "I started working on the implementation in the Spring of 1995. I developed the first version over the course of the next few months."

---

**Collection Notes**: SSH revolutionized remote system administration and secure communications. What started as a university student's response to a password-sniffing attack became one of the most important security protocols in computing. Every developer, system administrator, and security professional uses SSH daily, often without realizing the elegant cryptographic engineering underlying it.

**Curator**: Collected 2026-01-03 for cyberspace library on distributed systems security and cryptographic protocols.
