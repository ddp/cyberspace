# Digital Distributed System Security Architecture & NCSC Conference Proceedings

**Collection Date**: 2025-12-31
**Location**: ~/cyberspace/dssa-ncsc-papers/
**Total Size**: 133 MB

## Overview

This collection contains Digital Equipment Corporation's (DEC) seminal Distributed System Security Architecture (DSSA) paper and proceedings from the National Computer Security Conference (NCSC), co-sponsored by NIST and NSA from 1987-1992. These documents represent foundational work in distributed systems security, authentication, and cryptographic protocols.

## The Digital Distributed System Security Architecture (DSSA)

### Core Paper

**1989-DSSA-Gasser-Goldstein-Lampson.pdf** (149 KB)
- **Title**: "The Digital Distributed System Security Architecture"
- **Authors**: Morrie Gasser, Andy Goldstein, Charlie Kaufman, Butler Lampson (Digital Equipment Corporation)
- **Presented**: 12th National Computer Security Conference, October 10-13, 1989, Baltimore, MD
- **Significance**: Comprehensive distributed security specification for heterogeneous systems

**Abstract**:
The DSSA is a comprehensive specification for security in a distributed system that employs state-of-the-art concepts to address the needs of both commercial and government environments. The architecture covers:
- User and system authentication
- Mandatory and discretionary security
- Secure initialization and loading
- Delegation in general-purpose computing environments

**Key Architectural Principles**:
- No central authorities
- No global trust assumptions
- No central controls
- Heterogeneous system support
- Public key cryptography foundation
- Certificate-based authentication
- Delegation and privilege management

**Source**: http://bwlampson.site/41-DigitalDSSA/41-DigitalDSSA.pdf

### Related Specifications

**RFC-1507-DASS-Kaufman.txt** (281 KB)
- **Title**: "DASS - Distributed Authentication Security Service"
- **Author**: Charlie Kaufman (Digital Equipment Corporation)
- **Published**: RFC 1507, September 1993
- **Status**: Experimental Protocol
- **Significance**: Public key-based authentication protocol with delegation

**Technical Features**:
- Timestamp-based authentication scheme
- Certificate distribution mechanisms
- Delegation capabilities
- X.500 hierarchy-based certification stations
- DSSA/SPX authentication protocol

**Goal**: Provide authentication services in a distributed environment that are both more secure and easier to use than existing mechanisms.

**Source**: https://www.rfc-editor.org/rfc/rfc1507.txt

**RFC-2407-IPsec-ISAKMP-Piper.txt** (67 KB)
- **Title**: "The Internet IP Security Domain of Interpretation for ISAKMP"
- **Author**: Derrell Piper
- **Published**: RFC 2407, November 1998
- **Citations**: 66 subsequent RFCs
- **Significance**: IPsec security protocols and key exchange mechanisms

**Source**: https://www.rfc-editor.org/rfc/rfc2407.txt

## NCSC Conference Proceedings

### About the Conferences

The **National Computer Security Conference** was an annual event co-sponsored by:
- National Institute of Standards and Technology (NIST) - Computer Systems Laboratory (NCSL)
- National Security Agency (NSA) - National Computer Security Center (NCSC)

**Attendance**: Over 2,000 participants from government, industry, and academia
**Focus**: Information systems security research, development, and practice
**Time Period**: 1978-2000 (this collection: 1987-1992)

### Conference Proceedings Collected

**NCSC-10th-1987-Proceedings.pdf** (148 KB)
- **Conference**: 10th National Computer Security Conference
- **Date**: September 21-24, 1987
- **Theme**: "Computer Security--From Principles to Practices"
- **Location**: Baltimore, Maryland
- **Source**: https://archive.org/details/DTIC_ADA219100

**NCSC-11th-1988-Proceedings.pdf** (29 MB)
- **Conference**: 11th National Computer Security Conference
- **Date**: October 17-20, 1988
- **Location**: Baltimore, Maryland
- **Source**: https://csrc.nist.gov/CSRC/media/Publications/conference-paper/1988/10/17/proceedings-11th-national-computer-security-conference-1988/documents/1988-11th-NCSC-proceedings.pdf

**NCSC-12th-1989-Proceedings.pdf** (38 MB) ⭐
- **Conference**: 12th National Computer Security Conference
- **Date**: October 10-13, 1989
- **Theme**: "Information Systems Security: Solutions for Today—Concepts for Tomorrow"
- **Location**: Baltimore, Maryland
- **Significance**: Contains the original DSSA paper presentation
- **Major Areas**:
  - Advanced research developments and emerging technologies
  - Network security architectures
  - Risk management
  - Management and administration issues
  - Education and ethics
- **Source**: https://csrc.nist.gov/files/pubs/conference/1989/10/10/proceedings-12th-national-computer-security-confer/final/docs/1989-12th-ncsc-proceedings.pdf

**NCSC-14th-1991-Proceedings-Vol1.pdf** (25 MB)
- **Conference**: 14th National Computer Security Conference
- **Date**: October 1-4, 1991
- **Theme**: "Information Systems Security: Requirements & Practices"
- **Location**: Washington, D.C. (Omni Shoreham Hotel)
- **Volume**: 1 of 2
- **Source**: https://csrc.nist.gov/files/pubs/conference/1991/10/01/proceedings-14th-national-computer-security-confer/final/docs/1991-14th-ncsc-proceedings-vol-1.pdf

**NCSC-14th-1991-Proceedings-Vol2.pdf** (40 MB)
- **Conference**: 14th National Computer Security Conference
- **Date**: October 1-4, 1991
- **Volume**: 2 of 2
- **Source**: https://csrc.nist.gov/CSRC/media/Publications/conference-paper/1991/10/01/proceedings-14th-national-computer-security-conference-1991/documents/1991-14th-NCSC-proceedings-vol-2.pdf

**NCSC-15th-1992-Proceedings-Vol2.pdf** (1.2 KB - incomplete download)
- **Conference**: 15th National Computer Security Conference
- **Date**: October 13-16, 1992
- **Theme**: "Information Systems Security: Building Blocks to the Future"
- **Location**: Baltimore, Maryland
- **Note**: Download incomplete, needs retry
- **Source**: https://archive.org/details/DTIC_ADA497296

## Historical Context

### DEC's Integrated Security Programme

DSSA was part of DEC's broader Integrated Security initiative, designed to provide:
- Security services for Ultrix v4.0 and VMS v5.4
- Framework for current and future applications
- Support for OSI and TCP/IP environments
- Cryptographic architecture (released September 1989)

### Technical Innovation

The DSSA architecture represented state-of-the-art distributed security:
- **No Kerberos-style central authority**: Unlike contemporary systems
- **Public key infrastructure**: Certificate-based rather than shared secrets
- **Delegation support**: Explicit privilege delegation mechanisms
- **Heterogeneous systems**: Designed for mixed OS environments
- **Mandatory and discretionary controls**: Both government and commercial security models

### Authors & Contributors

**Butler Lampson** (DSSA co-author)
- Also present in Lamport papers collection
- 2013 ACM Turing Award winner (same year as Leslie Lamport)
- Pioneered distributed systems security and capability-based security
- Microsoft Research

**Charlie Kaufman** (DSSA co-author, DASS RFC author)
- DEC cryptography architect
- Key contributor to IPsec standards
- ISAKMP and IKE specifications

**Morrie Gasser** (DSSA lead author)
- DEC security research
- Trusted computing base expert

**Andy Goldstein** (DSSA co-author)
- VMS security architect
- ACL and security kernel design

**Derrell Piper** (IPsec RFC author)
- Network Alchemy co-founder/CTO
- IPsec/ISAKMP specifications (RFC 2407)
- Security Area Directorate reviewer (IETF)

## Connections to Other Collections

### Lamport Papers Collection
- Butler Lampson co-authored DSSA paper
- Both Lampson and Lamport won Turing Awards (2013)
- Distributed systems security builds on Lamport's causality and consensus work
- Byzantine fault tolerance relevant to DSSA's trust model

### Network Alchemy Patents
- Derrell Piper (RFC 2407 author) co-founded Network Alchemy
- Certificate enrollment and cryptographic authentication
- Connection between DSSA concepts and commercial clustering products
- IPsec/ISAKMP used in secure cluster communications

### DEC VAXcluster Papers
- DSSA designed for VMS v5.4 (VAXcluster OS)
- Distributed lock manager security
- Cluster-wide authentication and access control
- SCS/SCA security architecture integration

### Distributed Agent Architecture
- DSSA's "no central authority" model aligns with distributed agents
- Certificate-based authentication for agent identity
- Delegation mechanisms for agent capability tokens
- Public key cryptography for agent-to-agent trust

## Key Topics Covered

### Authentication & Identity
- Public key cryptography
- Certificate distribution
- Delegation and proxy credentials
- Timestamp-based authentication
- X.500 directory integration

### Access Control
- Mandatory access control (MAC)
- Discretionary access control (DAC)
- Capability-based security
- ACL mechanisms
- Privilege management

### Distributed Systems Security
- Heterogeneous system trust
- No central authority requirements
- Secure initialization and boot
- Network security architectures
- Risk management in distributed environments

### Cryptographic Protocols
- IPsec/ISAKMP key exchange
- DASS authentication protocol
- Certificate chain validation
- Secure channel establishment

## Additional NCSC Conferences Not Yet Collected

Available from NIST CSRC or DTIC:
- 1st-9th NCSC (1978-1986)
- 13th NCSC (1990)
- 16th-23rd NCSC (1993-2000)

## Research Applications

This collection is valuable for:
- **Historical security architecture research**: Understanding evolution of distributed security
- **Cryptographic protocol design**: Certificate-based authentication foundations
- **Distributed systems**: No-central-authority architectures
- **IPsec/IKE history**: Early specifications and design rationale
- **Commercial vs government security**: Dual-use security models
- **VMS/Ultrix security**: DEC operating system security implementations

## Related Resources

### NIST CSRC Archives
- **Conference Proceedings**: https://csrc.nist.rip/publications/history/nissc/index.html
- **12th NCSC Report**: https://csrc.nist.gov/pubs/journal/1990/03/conference-report-12th-ncsc-1989/final

### Internet Archive (DTIC)
- **Defense Technical Information Center**: https://archive.org/details/DTIC_ADA497296
- **Multiple conference proceedings**: Search "National Computer Security Conference"

### Butler Lampson's Website
- **DSSA Paper**: http://bwlampson.site/41-DigitalDSSA/
- **Other distributed security papers**: http://bwlampson.site/

### IETF RFCs
- **RFC 1507 (DASS)**: https://datatracker.ietf.org/doc/html/rfc1507
- **RFC 2407 (IPsec)**: https://datatracker.ietf.org/doc/html/rfc2407
- **Derrell Piper Profile**: https://datatracker.ietf.org/person/ddp@electric-loft.org

## Citation

When citing these materials:

**DSSA Paper**:
Gasser, M., Goldstein, A., Kaufman, C., & Lampson, B. (1989). The Digital Distributed System Security Architecture. In Proceedings of the 12th National Computer Security Conference (pp. 305-319). Baltimore, MD.

**DASS RFC**:
Kaufman, C. (1993). DASS - Distributed Authentication Security Service. RFC 1507, IETF.

**IPsec RFC**:
Piper, D. (1998). The Internet IP Security Domain of Interpretation for ISAKMP. RFC 2407, IETF.

---

**Collection Notes**: This archive preserves seminal work in distributed systems security from the late 1980s and early 1990s, when foundational concepts like public key infrastructure, certificate-based authentication, and IPsec were being developed. The DSSA architecture influenced modern distributed security designs including capability-based systems, federated identity, and zero-trust architectures.

**Curator**: Collected 2025-12-31 to support research into cryptographically-secured distributed agent systems with certificate-based authentication and no central authority assumptions.
