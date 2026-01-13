# Library of Cyberspace - RFCs

*The Soup. The Realm. The Seal.*

*Sovereign islands in a wilderness of mirrors. Objects referencing objects, hashes pointing to hashes. Navigate by capability chain or be lost. Your realm is your place in cyberspace - a sealed closure, accumulating history, carrying your intent through the soup.*

---

Request for Comments documents for the Library of Cyberspace preservation architecture.

## Active RFCs

| RFC | Title | Status | Date |
|-----|-------|--------|------|
| [rfc-000](rfc-000-declaration.md) | The Declaration | Informational | 2026-01-06 |
| [rfc-001](rfc-001-replication-layer.md) | Replication Layer | Implemented | 2026-01-05 |
| [rfc-002](rfc-002-architecture.md) | Cyberspace Architecture | Informational | 2026-01-06 |
| [rfc-003](rfc-003-audit-trail.md) | Cryptographic Audit Trail | Implemented | 2026-01-06 |
| [rfc-004](rfc-004-spki-authorization.md) | SPKI Authorization | Implemented | 2026-01-06 |
| [rfc-005](rfc-005-metadata-levels.md) | Progressive Metadata Levels | Implemented | 2026-01-06 |
| [rfc-006](rfc-006-vault-architecture.md) | Vault System Architecture | Implemented | 2026-01-06 |
| [rfc-007](rfc-007-threshold-governance.md) | Threshold Signature Governance | Implemented | 2026-01-06 |
| [rfc-008](rfc-008-shamir-sharing.md) | Shamir Secret Sharing | Implemented | 2026-01-06 |
| [rfc-009](rfc-009-library-directory.md) | Library Directory System | Implemented | 2026-01-06 |
| [rfc-010](rfc-010-federation.md) | Federation Protocol | Proposed | 2026-01-06 |
| [rfc-011](rfc-011-byzantine-consensus.md) | Byzantine Consensus | Proposed | 2026-01-06 |
| [rfc-012](rfc-012-lamport-clocks.md) | Lamport Logical Clocks | Proposed | 2026-01-06 |
| [rfc-013](rfc-013-tla-specification.md) | TLA+ Formal Specification | Proposed | 2026-01-06 |
| [rfc-014](rfc-014-coq-extraction.md) | Coq Extraction for TCB | Proposed | 2026-01-06 |
| [rfc-015](rfc-015-versioning-rollback.md) | Versioning and Rollback | Proposed | 2026-01-06 |
| [rfc-016](rfc-016-lazy-clustering.md) | Lazy Clustering | Proposed | 2026-01-06 |
| [rfc-017](rfc-017-opera.md) | The Burning of Alexandria (Opera) | Cultural | 2026-01-06 |
| [rfc-018](rfc-018-sealed-archive.md) | Sealed Archive Format | Implemented | 2026-01-06 |
| [rfc-019](rfc-019-documentation-pipeline.md) | Documentation Pipeline | Implemented | 2026-01-06 |
| [rfc-020](rfc-020-content-addressed-storage.md) | Content-Addressed Storage | Draft | 2026-01-07 |
| [rfc-037](rfc-037-node-roles.md) | Node Roles and Capabilities | Draft | 2026-01-07 |
| [rfc-039](rfc-039-ipv6-scaling.md) | Scaling Architecture for IPv6 | Draft | 2026-01-07 |
| [rfc-040](rfc-040-security-architecture.md) | Cyberspace Security Architecture | Draft | 2026-01-08 |
| [rfc-041](rfc-041-keystore-and-attestation.md) | Keystore and Attestation | Draft | 2026-01-08 |
| [rfc-042](rfc-042-quantum-resistant-merkle.md) | Quantum-Resistant Merkle Trees | Draft | 2026-01-08 |
| [rfc-043](rfc-043-post-quantum-signatures.md) | Post-Quantum Signatures | Draft | 2026-01-08 |
| [rfc-044](rfc-044-cryptographic-entropy.md) | Cryptographic Entropy Sources | Draft | 2026-01-08 |

## RFC Purpose

These documents serve as:

1. **Design Records** - Why decisions were made
2. **Implementation Specifications** - How features work
3. **Security Analysis** - Threat models and mitigations
4. **Future Reference** - Understanding the system later

## RFC Format

Each RFC should include:

- **Abstract** - One paragraph summary
- **Motivation** - Why this is needed
- **Specification** - How it works
- **Security Considerations** - Threat analysis
- **Implementation Notes** - Practical details
- **References** - Related work

## Build & Publish

Generate all RFC formats and publish to the web:

```bash
cd spki/scheme/docs/rfc
./generate-rfcs.sh
```

This script:
1. Converts markdown to HTML, PostScript, and plain text
2. Generates the KWIC (Key Word In Context) permuted index
3. Publishes to `www.yoyodyne.com:~/cyberspace/spki/scheme/docs/rfc/`

**Manual publish only:**
```bash
rsync -av --delete *.html *.ps *.txt ddp@www.yoyodyne.com:~/cyberspace/spki/scheme/docs/rfc/
```

**Requirements:**
- `pandoc` - markdown conversion
- `latex` + `dvips` - PostScript generation
- SSH key in `~/.ssh` for yoyodyne access

## Document Formats

RFCs are published in the following canonical formats:

| Format | Extension | Purpose |
|--------|-----------|---------|
| Markdown | `.md` | Source, editing, version control |
| HTML | `.html` | Web viewing, rich rendering |
| PDF | `.pdf` | Archival, printing, distribution |
| Plain Text | `.txt` | Universal compatibility, IETF tradition |

All formats are considered canonical and are preserved in the Vault.

## Lineage

Cyberspace doesn't emerge from nothing. It stands on giants:

| System | Era | What We Learned |
|--------|-----|-----------------|
| **VMS Clusters** | 1983 | SET HOST - be there, on that node. Distributed presence. |
| **Newton** | 1993 | The soup - objects as medium, queries as navigation. Local-first. |
| **General Magic** | 1994 | Telescript, Magic Cap - agents that travel, carry intent, return with results. |
| **SPKI/SDSI** | 1996 | Capabilities, not identities. Authorization without central authority. |
| **AS/400** | 1988 | Capability-based addressing. Objects know their own type. |
| **Cambridge CAP** | 1970s | Hardware capabilities. The original capability machine. |

**What they lacked, we add:**

- VMS had clustering but ambient authority
- Newton was local-first but couldn't federate
- General Magic trusted the network too much
- SPKI never got adopted (until now)

Cyberspace is their synthesis: local-first realms, federated via capabilities, with agents swimming in the soup.

---

## Glossary

| Term | Definition |
|------|------------|
| **Realm** | A node's place in cyberspace - its vault, principal, capabilities, and objects. Local-first, sovereign. A sealed closure. |
| **Vault** | The local content-addressed object store (`.vault/`). The realm's storage. |
| **Principal** | A node's cryptographic identity (Ed25519 public key). Coordinates in cyberspace - a place you can teleport to. |
| **Soup** | The queryable object space (Newton-inspired). A wilderness of mirrors - objects referencing objects, hashes pointing to hashes. The medium in which realms exist as islands and agents swim. |
| **Seal** | Cryptographic binding - signing, archiving, committing. The primary verb. |
| **Keystore** | The inner vault where cryptographic identity lives. Encrypted at rest. |
| **Anchor** | Hardware root of trust (silicon). Provides unforgeable attestations. |
| **Attestation** | Signed proof about the realm - hardware state, software measurements, identity claims. |
| **Sigil** | A mark or attestation. Runes are measurements from the anchor. |
| **Agent** | A delegated emissary - a sealed closure spawned from a realm, carrying attenuated authority. Magic Cap reborn in Newton's soup. |
| **SET HOST** | Go yourself - direct presence in another realm (synchronous). |
| **Delegate** | Send an agent - autonomous action on your behalf (asynchronous). |
| **Merkle Tree** | Quantum-resistant hash tree. Each object a tree, each node SHAKE256 or BLAKE3. The forest that survives the quantum winter. |
| **Wilderness of Mirrors** | The soup. Objects referencing objects, hashes pointing to hashes. Navigate by capability chain or be lost. (Angleton) |
| **@principal:/path** | Object coordinates. "At this realm, this object." Teleport destination + what you seek. |
| **@principal+role:/path** | Object coordinates with role context. "At this realm, acting as this role, this object." |
| **@principal+{caps}:/path** | Object coordinates with explicit capabilities. `+{read,write}` specifies exact caps. Roles are shorthand; capabilities are truth. |
| **Weave** | The gossip fabric connecting realms in federation. Lambdas in the weave - the constellation of enrolled peers, mirrors reflecting mirrors. |
| **Wormhole** | A capability-gated tunnel between realms. With the right delegation, step through and you're there. The architecture that would have been. |
| **Enrollment** | The act of joining a federation. Enrollment IS trust - no ACLs on friendship. You're in or you're out. |

## Upcoming RFCs

- rfc-021: Capability Delegation Patterns
- rfc-022: Key Ceremony Protocol
- rfc-023: Agent Spawning and Sandboxing
- rfc-024: Network Protocol
- rfc-045: Agent Protocol (Magic Cap in the Soup)
- rfc-046: Realm Migration and Portability
