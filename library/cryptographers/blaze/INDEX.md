# Matt Blaze - Cryptography, Key Escrow, and Security Analysis

**Collection Date**: 2026-01-03
**Location**: ~/cyberspace/library/cryptographers/blaze/
**Total Size**: ~5.1 MB

## Overview

Matt Blaze is a cryptographer and security researcher best known for discovering the fundamental flaw in the Clipper chip's key escrow system in 1994, and for creating the Cryptographic File System (CFS) for Unix. His work spans cryptographic protocol analysis, wiretapping technology, physical security, and voting system security. Currently the McDevitt Chair of Computer Science and Law at Georgetown University, he serves on the board of directors of the Tor Project and is a prominent voice in debates over encryption policy and surveillance.

## Papers Collected

### Key Escrow and Clipper Chip

**clipper-protocol-failure-1994.pdf** (159 KB)
- **Title**: "Protocol Failure in the Escrowed Encryption Standard"
- **Published**: May 1994
- **Significance**: Discovered fundamental flaw in Clipper chip's key escrow mechanism
- **Impact**: Helped kill the Clipper chip program and key escrow proposals
- **Vulnerability**: Demonstrated attacker could replace LEAF (Law Enforcement Access Field) with bogus value
- **Result**: Clipper could be used for encryption while defeating law enforcement access
- **Source**: https://www.mattblaze.org/papers/eesproto.pdf

**Historical Context**: In the 1990s "Crypto Wars," the U.S. government proposed the Clipper chip—a tamper-resistant cryptographic device with built-in government backdoor. Blaze's discovery that the backdoor could be disabled was a major blow to key escrow policy.

**key-escrow-retrospective-2011.pdf** (2.1 MB)
- **Title**: "Key Escrow from a Safe Distance: Looking Back at the Clipper Chip"
- **Published**: 2011, ACSAC (Annual Computer Security Applications Conference)
- **Significance**: Retrospective analysis of 1990s crypto wars and key escrow debates
- **Topics**: Technical, policy, and social aspects of key escrow controversy
- **Relevance**: Lessons applicable to modern encryption backdoor debates
- **Source**: https://www.mattblaze.org/papers/escrow-acsac11.pdf

**Quote from paper**:
> "The 1990s were interesting times for cryptography... the civilian academic and commercial worlds were becoming seriously interested in cryptography, bolstered by new cryptologic advances."

### Cryptographic File Systems

**cfs-cryptographic-file-system-1993.pdf** (82 KB)
- **Title**: "A Cryptographic File System for Unix"
- **Published**: Proceedings of 1st ACM Conference on Computer and Communications Security, November 1993
- **Significance**: First practical cryptographic file system for Unix
- **Innovation**: Transparent encryption using NFS as transport mechanism
- **Design**: Users encrypt selected directories, mount them after providing key
- **Encryption**: DES for file data encryption
- **Source**: https://www.mattblaze.org/papers/cfs.pdf

**cfs-key-management-1994.pdf** (42 KB)
- **Title**: "Key Management in an Encrypting File System"
- **Published**: USENIX Summer 1994 Technical Conference
- **Significance**: Addressed practical key management challenges in CFS
- **Topics**: Key storage, password-based key derivation, key lifecycle
- **Impact**: Influenced design of modern encrypted file systems
- **Source**: https://www.mattblaze.org/papers/cfskey.pdf

**CFS Legacy**: Matt Blaze's CFS was groundbreaking work that demonstrated cryptographic file systems were practical. While CFS itself used DES and is now obsolete, the design principles influenced:
- Linux encrypted file systems (eCryptfs, dm-crypt)
- macOS FileVault
- Windows BitLocker
- Modern container encryption

### Physical Security

**safecracking-2004.pdf** (2.7 MB)
- **Title**: "Safecracking for the Computer Scientist"
- **Published**: December 2004 (Revised)
- **Significance**: Applied computer security analysis to physical safe security
- **Topics**: Mechanical combination locks, attack methodologies, security metrics
- **Innovation**: Bridged computer and physical security communities
- **Controversy**: "Completely pissed off the locksmithing community"
- **Defense**: Bruce Schneier supported it as valuable cross-domain learning
- **Source**: https://www.mattblaze.org/papers/safelocks.pdf

**Paper Contents**:
- Taxonomy of safe opening methods (forced, covert, surreptitious)
- Analysis of combination lock security
- Vulnerability assessment methodology
- Comparison with computer security metrics
- Practical attack techniques and countermeasures

**NSA Connection**: After publishing, Blaze discovered NSA had conducted similar classified research published in *Cryptologic Quarterly*, showing both communities recognized cryptologic aspects of physical security.

## Key Contributions

### Cryptographic Protocol Analysis
- **Clipper Chip**: Found critical flaw in government key escrow proposal
- **Protocol Verification**: Demonstrated importance of rigorous security analysis
- **Academic Impact**: Showed value of independent security research
- **Policy Impact**: Influenced encryption policy debates for decades

### Cryptographic File Systems
- **CFS (1992)**: First practical Unix encrypted file system
- **Key Management**: Practical approaches to user-key management
- **Transparent Encryption**: User-friendly encryption without application modification
- **Open Source**: Published source code, enabling further research

### Security Methodology
- **Cross-Domain Analysis**: Applied computer security thinking to physical security
- **Adversarial Thinking**: Systematic threat modeling and attack analysis
- **Practical Security**: Focus on real-world deployments and usability
- **Independent Research**: Academic freedom in security analysis

## Research Areas

### Cryptography
- Public-key infrastructure
- Cryptographic protocol design and analysis
- Trust management systems
- Secure communications

### Secure Systems
- Operating system security
- File system encryption
- Network security
- Secure software design

### Physical Security
- Lock security analysis
- Safe and vault technology
- Security metrics and evaluation
- Adversarial modeling

### Policy and Law
- Encryption policy
- Surveillance and wiretapping
- Electronic voting security
- Security and civil liberties

## Professional Background

### Academic Positions
- **Georgetown University** (2018-present): McDevitt Chair of Computer Science and Law
- **University of Pennsylvania** (2004-2018): Associate Professor of Computer and Information Science
- **AT&T Bell Laboratories** (early career): Research scientist

### Service
- **Tor Project**: Board of Directors
- **IACR** (International Association for Cryptologic Research): Member
- **Expert Witness**: Cryptography and security in legal cases
- **Policy Advisor**: Congressional testimony on encryption and surveillance

## Crypto Wars Participation

### First Crypto War (1990s)

**Cypherpunks Mailing List**: Active participant in cryptographic activism
**Clipper Chip Opposition**: Technical analysis undermined government backdoor proposal
**Export Control Reform**: Contributed to relaxation of crypto export restrictions
**Public Advocacy**: Made cryptographic security issues accessible to public

### Second Crypto War (2010s-present)

**iPhone Encryption**: Expert on Apple vs. FBI encryption controversy
**Going Dark Debate**: Technical voice against government backdoor proposals
**Congressional Testimony**: Explained why secure encryption cannot have backdoors
**Public Education**: Media appearances explaining encryption to general public

## Notable Quotes

On the Clipper Chip:
> "The Clipper chip's key escrow mechanism can be defeated using only simple modifications to the protocol."

On security research:
> "Security systems need to be analyzed by people who think like attackers, not just by people who think like designers."

On encryption policy:
> "There's no such thing as a backdoor that only the good guys can use."

## Additional Research

### Wiretapping Technology
- Analysis of law enforcement surveillance systems
- CALEA (Communications Assistance for Law Enforcement Act) technical review
- VoIP wiretapping challenges
- Secure communications in adversarial environments

### Electronic Voting
- Security analysis of voting systems
- Source code review of voting machines
- Election integrity and verification
- Transparency in electoral systems

### Trust Management
- Keynote trust management system
- Distributed authorization
- Policy specification languages
- Decentralized trust systems

## Recognition and Awards

- Numerous best paper awards at security conferences
- NSF CAREER Award
- EFF Pioneer Award (various cypherpunks)
- Influential researcher in cryptography and security policy

## Professional Activities

### Conference Participation
- Program committees for major security conferences
- Invited speaker at academic and policy venues
- Expert panels on encryption and surveillance
- Security workshop organizer

### Public Engagement
- Twitter/X presence (@mattblaze): Security commentary and photography
- Media expert on encryption and privacy issues
- Congressional testimony on surveillance and security
- Public education on cryptographic policy

## Impact on Modern Debates

### Encryption Backdoors
Blaze's Clipper chip work remains relevant in modern encryption debates:
- **Apple vs. FBI** (2016): Same arguments about backdoor feasibility
- **EARN IT Act**: Legislative attempts to weaken encryption
- **Going Dark**: Law enforcement claims about "going dark"
- **Technical Reality**: Blaze showed backdoors compromise security for everyone

### File System Security
CFS principles influence modern systems:
- Full-disk encryption standard on modern laptops
- Cloud storage encryption (Dropbox, Google Drive, etc.)
- Mobile device encryption (iOS, Android)
- Container-based security (Docker secrets, etc.)

## Related Work in This Collection

### Key Escrow Debate
- **bellovin/**: Steve Bellovin also opposed Clipper from protocol perspective
- **zimmermann/**: Phil Zimmermann's PGP represented civilian strong crypto
- Both Blaze and Bellovin participated in 1990s crypto policy debates

### Cryptographic Systems
- **djb/**: Modern cryptographic implementations (NaCl, Curve25519)
- **schneier/**: Algorithm design (Blowfish, Twofish used in encryption systems)
- **ssh-designers/**: Secure protocols for remote access

### Trust and Authentication
- **diffie-hellman/**: Public-key cryptography foundation
- **dssa-ncsc-papers/**: Distributed authentication without central authority
- **spki/**: Blaze co-authored SPKI (Simple Public Key Infrastructure) work

## Software and Tools

### CFS (Cryptographic File System)
- **Status**: Historical, proof-of-concept (uses DES)
- **Availability**: Source code available on mattblaze.org
- **Impact**: Demonstrated feasibility of transparent encryption
- **Successors**: Modern encrypted file systems based on similar principles

### Keynote
- Trust management system
- Policy specification and verification
- Distributed authorization
- Research tool for trust systems

## Photography

Note: Matt Blaze is also an accomplished photographer, with work exhibited in galleries and published in photographic journals. His security photography documents surveillance infrastructure, locks, and security technology—bridging his technical and artistic interests.

## Additional Resources

### Official Website
- **Homepage**: https://www.mattblaze.org/
- **Papers**: https://www.mattblaze.org/papers/
- **Research Summary**: https://www.mattblaze.org/research.html
- **Blog**: https://www.mattblaze.org/blog/

### Academic Profiles
- **Georgetown Law**: Faculty page
- **DBLP**: Computer science bibliography
- **Google Scholar**: Citation metrics
- **IACR**: Cryptography publications

### Social Media
- **Twitter/X**: @mattblaze (security commentary, photography)
- **Mastodon**: Active in security community
- Public intellectual on security and privacy issues

## Citation Examples

When citing Blaze's work:

**Clipper Chip Paper**:
Blaze, M. (1994). Protocol failure in the escrowed encryption standard. In Proceedings of the 2nd ACM Conference on Computer and Communications Security (pp. 59-67).

**CFS Paper**:
Blaze, M. (1993). A cryptographic file system for Unix. In Proceedings of the 1st ACM Conference on Computer and Communications Security (pp. 9-16).

**Safecracking Paper**:
Blaze, M. (2004). Safecracking for the computer scientist. University of Pennsylvania Department of Computer and Information Science Technical Report.

**Key Escrow Retrospective**:
Blaze, M. (2011). Key escrow from a safe distance: Looking back at the Clipper chip. In Proceedings of the Annual Computer Security Applications Conference (ACSAC).

## Legacy

Matt Blaze's discovery of the Clipper chip flaw was a pivotal moment in cryptography history. By demonstrating that the government's key escrow system could be defeated, he:

1. **Helped End Key Escrow**: Contributed to the failure of Clipper and similar proposals
2. **Strengthened Crypto Rights**: Bolstered arguments for strong civilian encryption
3. **Established Precedent**: Showed independent security research can influence policy
4. **Educated Public**: Made encryption debates accessible to non-experts
5. **Informed Current Debates**: Clipper arguments resurface in modern backdoor proposals

His work on cryptographic file systems demonstrated that strong encryption could be practical and user-friendly, influencing modern full-disk encryption systems used by billions of people today.

---

**Collection Notes**: Matt Blaze exemplifies the scholar-activist in computer security—combining rigorous academic research with public policy engagement. His work shows that independent security research is essential for evaluating government proposals and that cryptographic systems must be analyzed by adversarial thinkers, not just designers.

**Curator**: Collected 2026-01-03 for cyberspace library on distributed systems security and cryptographic protocols.
