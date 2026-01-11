# RFC-002: Cyberspace Architecture

**Status:** Informational
**Date:** January 2026
**Author:** Derrell Piper <ddp@eludom.net>

---

## Abstract

Cyberspace is a distributed systems architecture built on S-expressions and Scheme, designed for cryptographic security without complexity. This RFC describes the overall system design, philosophy, and components.

---

## E Pluribus Unum

*Out of many, one.*

```
         ╭─────────────────────────────────────╮
         │                                     │
         │   Rough consensus, cryptography,    │
         │   trusted systems, running code.    │
         │                                     │
         ╰─────────────────────────────────────╯
```

---

## 1. Motivation

Modern distributed systems are drowning in complexity. X.509 certificates require decoder rings. Container orchestration demands armies of SREs. Security policies hide in YAML nested seventeen levels deep.

**The Manifesto:**

> Authorized capability set with auditing. No central authority.

These three principles - SPKI authorization, cryptographic audit trails, and optional centralization - are not new. They were proven in VAXcluster security (1984-1994), proposed in SDSI at IETF 29 Seattle (1994), and implemented partially in products that didn't survive their parent companies. Cyberspace completes what was started.

**Design Lineage:**

| Era | System | Contribution |
|-----|--------|--------------|
| 1984 | VAXcluster | "Behave as one" - N nodes, one security domain |
| 1985 | VMS C2 | Audit trails, access control, security primitives |
| 1993 | VMS 6.0 | Cluster-wide intrusion detection, TLV object store |
| 1994 | SDSI | Self-certifying keys, local names (Rivest, IETF 29) |
| 1999 | SPKI | Authorization certificates, capability delegation |
| 2026 | Cyberspace | Synthesis: SPKI + audit + IPv6 mesh + no central authority |

DECnet Phase IV had 24-bit addressing - fatal for internet scale. Cyberspace is designed for IPv6: 128-bit addresses, global mesh, same security principles.

Cyberspace returns to first principles:

- **S-expressions** for everything: readable, parseable, auditable
- **Minimal TCB**: prove the crypto, evolve the rest
- **No central authority**: SPKI/SDSI namespaces over PKI hierarchies
- **Running code**: every feature traces to research, runs, and is tested

---

## 2. The Prime Directive

> **If it's in the TCB, it's in OCaml. Otherwise it's in Chicken Scheme.**

```
┌─────────────────────────────────────────────────────────────┐
│                                                             │
│   TRUSTED COMPUTING BASE (OCaml, ~1000 lines)              │
│                                                             │
│   ┌─────────────┐  ┌─────────────┐  ┌─────────────┐        │
│   │   Ed25519   │  │   SHA-512   │  │   Verify    │        │
│   │   Sign      │  │   Hash      │  │   Chain     │        │
│   └─────────────┘  └─────────────┘  └─────────────┘        │
│                                                             │
│   That's it. Everything else is policy.                    │
│                                                             │
└─────────────────────────────────────────────────────────────┘
                           │
                           │ FFI (tiny surface)
                           ▼
┌─────────────────────────────────────────────────────────────┐
│                                                             │
│   EVERYTHING ELSE (Chicken Scheme, unlimited)              │
│                                                             │
│   Vault · Audit · Replication · Names · Discovery          │
│   CLI Tools · API Server · Library · Scripts               │
│                                                             │
│   Change it anytime. It's just policy.                     │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

**Rationale:**

- **OCaml**: Strong types, formal verification with Coq, compile-time safety
- **Chicken Scheme**: Interactive development, S-expressions everywhere, rapid evolution
- **The boundary**: Tiny, frozen, proven. The TCB does crypto and *nothing else*.

A smaller TCB means fewer bugs that can break security. We prove the crypto in Coq. Everything else can evolve freely.

### 2.1 Interface Philosophy

> **English on top, Scheme for everything else.**

```
┌─────────────────────────────────────────────────────────────┐
│  > status                    Command mode: English verbs    │
│  > commit "message"          No parens needed              │
│  > soup                      Explore, inspect, act          │
├─────────────────────────────────────────────────────────────┤
│  > (define x (keys))         Scheme mode: Full power       │
│  > (map publish (releases))  Compose, transform, compute   │
│  > (filter signed? certs)    Lambda is home                │
└─────────────────────────────────────────────────────────────┘
```

The command layer is syntactic sugar. The Scheme layer is substrate. Users start with English, graduate to Scheme when they need composition. No mode switching—parens are the only delimiter.

### 2.2 The Data Flow

> **Eggs into soup.**

```
forge → eggs → soup → vault
```

| Stage | What | How |
|-------|------|-----|
| **forge** | Compilation | Source newer than `.so`? Rebuild. Arch changed? Rebuild. |
| **eggs** | Modules | Chicken Scheme's dynamically compiled units |
| **soup** | Cache | Newton-style queryable view of vault (in memory) |
| **vault** | Storage | Content-addressed persistence (on disk) |

The system is lazy. Modules compile on demand. The soup is the vault cache—query the soup, persist to the vault. The whole thing simmers together.

---

## 3. Core Components

### 3.1 The Vault

**The vault is the disk.**

In VAXcluster, multiple subsystems coordinated distributed storage: MSCP served disks across nodes, the DLM managed locks, SCS handled communication, and the quorum disk arbitrated partitions. Five subsystems, complex interactions, decades of refinement.

Cyberspace has one abstraction: the vault.

```
VAXcluster          Cyberspace
──────────          ──────────
Shared disk    →    Vault
MSCP           →    Gossip replication
DLM            →    Quorum consensus
SCS            →    CCP (secure channels)
Quorum disk    →    Vault
LAVC           →    Enrollment
```

The vault is content-addressed storage, replicated across nodes via gossip, with quorum state for partition handling:

```scheme
(cluster-quorum
  (epoch 42)
  (expected-votes 5)
  (quorum 3)
  (members
    (alice (votes 1) (role master))
    (bob   (votes 1) (role full))
    (carol (votes 1) (role full))
    (dave  (votes 1) (role witness))
    (eve   (votes 1) (role archive))))
```

Boot sequence mirrors VAXcluster:
1. Node reads local vault → knows expected membership
2. Contacts other expected members
3. Counts responding votes
4. If ≥ quorum → cluster forms, proceed
5. If < quorum → hang, wait, retry

Partition with quorum continues. Partition without hangs. No split-brain writes. When healed, minority syncs from majority. Epoch increments on membership change.

```bash
$ cyberspace vault init
$ cyberspace vault commit -m "Deploy new API"
$ cyberspace vault verify
✓ All signatures valid
```

Every commit is cryptographically sealed. No GPG. No separate signing step.

### 3.2 The Audit Trail

Tamper-evident logging with hash chains.

```scheme
(audit-entry
  (sequence 1042)
  (timestamp "2026-01-06T15:30:00Z")
  (action (commit "Deploy v2.1"))
  (actor (public-key |...|))
  (previous-hash |...|)
  (signature |...|))
```

Append-only. Hash-chained. Signed. Export as text.

### 3.3 SPKI Certificates

Authorization without identity.

```scheme
(cert
  (issuer (public-key ed25519 |base64....|))
  (subject (name alice "deploy-server"))
  (grant (tag (http-api (method POST) (path "/deploy/*"))))
  (valid (not-after "2026-12-31")))
```

Human-readable security policy. No ASN.1. No X.509.

### 3.4 Threshold Governance

Democracy in code.

```bash
$ cyberspace policy set deploy/prod --threshold 3 --signers alice,bob,carol,dave,eve
$ cyberspace execute proposal-42
✓ 3/5 signatures verified
```

No single point of failure. No rogue admin.

### 3.5 Secret Sharing

Survive key loss with Shamir splitting.

```scheme
(define shares (shamir-split master-key 5 3))
;; Distribute 5 shares. Recover with any 3.
```

### 3.6 Replication Layer

Federated distribution without central registry. See RFC-001.

```scheme
(seal-publish "1.0.0" remote: "/shared/releases")
(seal-subscribe "/shared/releases" verify-key: alice-pub)
(seal-synchronize peer-remote direction: 'both)
```

### 3.7 The Library Directory

421 research papers, searchable.

```
📖 > papers by Lamport
📚 Found 15 documents
📖 > about SPKI
📖 > from 1979
```

---

## 4. Architecture

### 4.1 Layer Diagram

```
┌──────────────────────────────────────────────────────────────────┐
│                        CYBERSPACE                                │
├──────────────────────────────────────────────────────────────────┤
│  ┌────────────┐  ┌────────────┐  ┌────────────┐  ┌────────────┐ │
│  │   Vault    │  │   Audit    │  │   SPKI     │  │  Library   │ │
│  └─────┬──────┘  └─────┬──────┘  └─────┬──────┘  └─────┬──────┘ │
│        └───────────────┴───────┬───────┴───────────────┘        │
│                    ┌───────────▼───────────┐                    │
│                    │    Chicken Scheme     │                    │
│                    │    (Policy Layer)     │                    │
│                    └───────────┬───────────┘                    │
│                    ┌───────────▼───────────┐                    │
│                    │    OCaml TCB          │                    │
│                    │    (Crypto Only)      │                    │
│                    └───────────┬───────────┘                    │
│                    ┌───────────▼───────────┐                    │
│                    │    libsodium          │                    │
│                    └───────────────────────┘                    │
└──────────────────────────────────────────────────────────────────┘
```

### 4.2 No Central Authority

```
     Alice                    Bob                     Carol
       │                       │                        │
       │    ┌─────────────┐    │    ┌─────────────┐    │
       └───►│ Alice's     │◄───┴───►│ Bob's       │◄───┘
            │ Namespace   │         │ Namespace   │
            │             │         │             │
            │ bob → key   │         │ alice → key │
            │ carol → key │         │ carol → key │
            └─────────────┘         └─────────────┘

         No DNS. No CA. No single point of failure.
         Just keys and local names.
```

SPKI/SDSI gives you:
- **Local namespaces**: "bob" means what *you* say it means
- **Authorization without identity**: Grant permissions to keys, not people
- **Delegation chains**: Alice → Bob → Carol, each step verified

---

## 5. Research Foundations

Every feature traces to a foundational paper:

| Feature | Paper | Author | Year |
|---------|-------|--------|------|
| Vault signatures | "New Directions in Cryptography" | Diffie & Hellman | 1976 |
| Audit trails | "How to Time-Stamp a Digital Document" | Haber & Stornetta | 1991 |
| Merkle proofs | "A Digital Signature Based on a Conventional Encryption Function" | Merkle | 1987 |
| Threshold sigs | "How to Share a Secret" | Shamir | 1979 |
| Logical clocks | "Time, Clocks, and the Ordering of Events" | Lamport | 1978 |
| Capabilities | "Protection" | Lampson | 1971 |
| SPKI certs | "SPKI Certificate Theory" | Ellison et al. | 1999 |

**421 papers** in the library. Not just referenced—*studied, implemented, running*.

---

## 6. Implementation Status

```
✓ Lamport OTP       ✓ Merkle Trees      ✓ Capabilities
✓ ChaCha20          ✓ Poly1305          ✓ Lamport Signatures
✓ SPKI Certs        ✓ Vault             ✓ Audit Trails
✓ Replication       ✓ Threshold Sigs    ✓ Shamir Sharing
✓ Library Directory
```

Each traces to original research. Each runs. Each is tested.

---

## 7. Security Considerations

### 7.1 TCB Minimization

The attack surface is limited to ~1000 lines of OCaml calling libsodium. This code is:

- Formally specified
- Proven in Coq
- Frozen (rarely changes)

### 7.2 No Single Point of Failure

- **No CA**: SPKI namespaces are local
- **No central server**: Federation, not empire
- **No single key**: Threshold signatures, Shamir sharing

### 7.3 Auditability

- All security policy is human-readable S-expressions
- All history is hash-chained and signed
- All audit trails are exportable text

---

## 8. Getting Started

```bash
git clone git@github.com:ddp/cyberspace.git
cd cyberspace/spki/scheme
./spki-keygen alice
./seal init --key alice.private
./seal commit -m "Hello, Cyberspace"
```

---

## 9. Future Work

- **ChaCha20-Poly1305 AEAD** - Authenticated encryption
- **Lamport Logical Clocks** - Distributed ordering
- **TLA+ Specifications** - Model-checked protocols
- **Coq Extraction** - Verified OCaml from proofs
- **Federation Protocol** - Cross-instance sync
- **Byzantine Paxos** - Fault-tolerant consensus

---

## 10. References

1. Diffie, W., & Hellman, M. (1976). New directions in cryptography.
2. Haber, S., & Stornetta, W. S. (1991). How to time-stamp a digital document.
3. Merkle, R. C. (1987). A digital signature based on a conventional encryption function.
4. Shamir, A. (1979). How to share a secret.
5. Lamport, L. (1978). Time, clocks, and the ordering of events in a distributed system.
6. Lampson, B. W. (1971). Protection.
7. Ellison, C., et al. (1999). SPKI certificate theory. RFC 2693.

---

## Changelog

- **2026-01-06** - Initial specification

---

```
                    ╭────────────────────────────────╮
                    │                                │
                    │      "E Pluribus Unum"         │
                    │                                │
                    │   github.com/ddp/cyberspace    │
                    │                                │
                    ╰────────────────────────────────╯
```

*Built on 50 years of cryptographic research. Standing on the shoulders of giants.*
