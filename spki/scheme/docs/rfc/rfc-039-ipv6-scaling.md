# RFC-039: Scaling Architecture for IPv6

**Status:** Draft
**Date:** January 2026
**Author:** Derrell Piper <ddp@eludom.net>
**Requires:** RFC-010 (Federation), RFC-016 (Lazy Clustering), RFC-037 (Node Roles)

---

## Abstract

This RFC defines the architectural changes required to scale Cyberspace from a git-backed prototype to a native distributed system capable of operating at IPv6 scale (billions of realms, exabytes of content). Git becomes an export format; the vault becomes the source of truth.

---

## Terminology

**Realm**: A node's place in cyberspace - its vault, principal, capabilities, and objects. Each realm is sovereign: local-first, controlled by its operator. Realms federate by choice, sharing objects according to trust relationships.

**Vault**: The local content-addressed object store (`.vault/`). The vault IS the realm's storage - all objects, indexes, audit trails, and configuration live here.

**Principal**: A node's cryptographic identity (Ed25519 public key). The principal identifies the realm to peers and signs its objects.

At IPv6 scale, cyberspace consists of billions of realms, each occupying its own address space, each sovereign, each choosing what to share and with whom.

---

## Motivation

Git served as an excellent prototype substrate:
- Content-addressed objects (proof of concept)
- Merkle tree integrity (validates the model)
- Ubiquitous tooling (bootstrap adoption)

Git cannot scale to IPv6:
- Full history on every clone
- Repository as replication unit (too coarse)
- SHA-1 (cryptographically broken)
- No native federation or discovery
- Merge semantics are wrong model

The internet has 2^128 addresses. Cyberspace should use them.

---

## Design Principles

```
1. Objects, not repositories
2. Pull, not push
3. Lazy, not eager
4. Local-first, federate-second
5. Trust math, not infrastructure
```

---

## Content-Addressed Object Store

### Storage Model

```
.vault/
  objects/
    sha512-a1b2c3.../    # First 8 chars as directory
      a1b2c3d4e5f6...    # Full hash as filename
  index/
    catalog.db           # SQLite: hash → metadata
    bloom.bin            # Bloom filter for existence
  chunks/
    sha512-xxxx/         # Chunked large objects
  audit/
    chain.db             # Indexed audit trail
```

### Object Format

```scheme
(cyberspace-object
  (version 1)
  (type blob|tree|manifest|cert|audit)
  (size 1048576)
  (compression zstd|none)
  (hash "sha512:a1b2c3...")
  (chunks ("sha512:..." "sha512:..." ...))  ; If chunked
  (signature "ed25519:...")
  (timestamp 1736300000))
```

### Chunking Strategy

Large objects split at content-defined boundaries (Rabin fingerprinting):

```
Target chunk: 64 KB (Starlink-optimized)
Min chunk:    16 KB
Max chunk:   256 KB

Benefits:
  - Deduplication across objects
  - Partial sync (fetch only missing chunks)
  - Resumable transfers
  - Efficient diff
```

### Hash Function

```
SHA-512 everywhere.

Not SHA-256: We have the bits, use them.
Not SHA-1: Broken.
Not BLAKE3: Less analyzed, marginal speed gain irrelevant at network latency.

SHA-512 is:
  - FIPS certified (GovCloud path)
  - 50 years of cryptanalysis
  - Hardware accelerated
  - Already in use (audit trail, signatures)
```

---

## Index and Query

### Catalog Index (SQLite)

```sql
CREATE TABLE objects (
    hash        TEXT PRIMARY KEY,
    type        TEXT NOT NULL,
    size        INTEGER,
    timestamp   INTEGER,
    signer      TEXT,
    parent      TEXT,              -- For trees/manifests
    compressed  INTEGER DEFAULT 0
);

CREATE INDEX idx_type ON objects(type);
CREATE INDEX idx_signer ON objects(signer);
CREATE INDEX idx_timestamp ON objects(timestamp);

CREATE TABLE chunks (
    object_hash TEXT,
    chunk_hash  TEXT,
    sequence    INTEGER,
    PRIMARY KEY (object_hash, sequence)
);

CREATE TABLE tags (
    hash    TEXT,
    tag     TEXT,
    PRIMARY KEY (hash, tag)
);
CREATE INDEX idx_tag ON tags(tag);
```

### Bloom Filter

Fast existence check before network round-trip:

```scheme
(define *bloom-filter*
  (make-bloom-filter
    capacity: 10000000      ; 10M objects
    false-positive: 0.001)) ; 0.1% FP rate

(bloom-add! *bloom-filter* hash)
(bloom-contains? *bloom-filter* hash)  ; Maybe or definitely-not
```

### Audit Trail Index

```sql
CREATE TABLE audit (
    id          TEXT PRIMARY KEY,
    sequence    INTEGER UNIQUE,
    timestamp   INTEGER,
    actor       TEXT,
    action      TEXT,
    parent_id   TEXT,
    hash        TEXT
);

CREATE INDEX idx_audit_actor ON audit(actor);
CREATE INDEX idx_audit_action ON audit(action);
CREATE INDEX idx_audit_time ON audit(timestamp);
```

---

## Discovery and Routing

### Realm Identity

Each realm has a principal (Ed25519 public key). This IS its identity:

```scheme
(realm-identity
  (principal "ed25519:a1b2c3...")
  (addresses                          ; Where to reach this realm
    (ipv6 "2001:db8::1" port: 7777)
    (ipv4 "192.0.2.1" port: 7777)     ; Legacy
    (onion "xxxx.onion" port: 7777))  ; Tor
  (role witness)
  (capabilities (storage-gb 1000) (bandwidth-mbps 100))
  (signature "ed25519:..."))
```

### Peer Discovery

**Bootstrap:**
```scheme
(bootstrap-peers
  ("ed25519:official1..." "bootstrap.cyberspace.org")
  ("ed25519:official2..." "bootstrap2.cyberspace.org"))
```

**Gossip Protocol:**
```
1. Realm joins, contacts bootstrap peer
2. Receives partial peer list (random subset)
3. Contacts those peers, exchanges lists
4. Epidemic spread: O(log n) rounds to reach all realms
5. Periodic refresh (every 5 min on Starlink-friendly schedule)
```

**Distributed Hash Table (Future):**
```
Kademlia-style routing:
  - XOR distance metric on principal hashes
  - O(log n) lookups
  - Realms responsible for nearby hash ranges
  - Natural load balancing
```

### Content Discovery

```scheme
;; "Who has this hash?"
(content-locate "sha512:a1b2c3...")

;; Returns list of peers claiming to have it:
(("ed25519:peer1..." (latency-ms 50) (role full))
 ("ed25519:peer2..." (latency-ms 200) (role witness))
 ("ed25519:peer3..." (latency-ms 600) (role archiver)))

;; Fetch from best candidate
(content-fetch "sha512:a1b2c3..." from: "ed25519:peer1...")
```

---

## Transport Protocol

### Wire Format

```scheme
(cyberspace-message
  (version 1)
  (type request|response|announce|gossip)
  (from "ed25519:sender...")
  (to "ed25519:recipient...")        ; Or broadcast
  (nonce 12345678)                   ; Replay protection
  (timestamp 1736300000)
  (payload ...)
  (signature "ed25519:..."))
```

### Request Types

```scheme
;; Existence check
(have? ("sha512:..." "sha512:..." ...))
;; Response: (have ("sha512:..." "sha512:...") missing ("sha512:..."))

;; Fetch object
(fetch "sha512:...")
;; Response: (object ...)

;; Fetch chunk range
(fetch-chunks "sha512:..." start: 5 count: 10)
;; Response: (chunks ...)

;; Peer list exchange
(peers? limit: 50)
;; Response: (peers ...)

;; Announce new content
(announce ("sha512:..." "sha512:..."))
;; Response: (ack)
```

### Transport Bindings

```
Native:     UDP/IPv6, port 7777 (primary)
Fallback:   TCP/IPv6, port 7777 (firewalls)
Legacy:     TCP/IPv4, port 7777 (transition)
Stealth:    Tor onion service (censorship resistance)
Offline:    USB drive, file copy (sneakernet)
Export:     Git bundle (GitHub compatibility)
```

### Starlink Optimization

```scheme
(transport-config
  (mode satellite)
  (batch-window-ms 500)        ; Aggregate small messages
  (chunk-size-kb 64)           ; Match MTU
  (retry-strategy exponential)
  (max-in-flight 10)           ; Parallelism
  (keepalive-sec 300))         ; 5 min, not 30 sec
```

---

## Synchronization Protocol

### Lazy Sync (Default)

```
Node A                              Node B
   |                                   |
   |----(have? [h1, h2, h3])---------->|
   |<---(have [h1, h3] missing [h2])---|
   |----(fetch h2)-------------------->|
   |<---(object h2 ...)----------------|
   |                                   |

No coordination. No locks. No leader.
```

### Crdt-Style Convergence

Objects are immutable and content-addressed. No conflicts possible at object level.

Manifests (collections of objects) use:
- Lamport timestamps for ordering
- Last-writer-wins with principal tiebreaker
- Or: union (add-only sets)

```scheme
(manifest
  (name "library")
  (version (lamport 42) (principal "ed25519:..."))
  (entries
    ("rfc-001" "sha512:...")
    ("rfc-002" "sha512:...")
    ...))
```

### Merkle Sync

Efficient diff for large manifests:

```
         root
        /    \
      h1      h2
     /  \    /  \
    a    b  c    d

Exchange root hash.
If different, recurse on children.
O(log n) round trips to find diff.
```

---

## Federation at Scale

### Cluster Topology

```
                    ┌─────────────────────────────────────┐
                    │         COORDINATOR CLUSTER         │
                    │  (3-7 nodes, Byzantine consensus)   │
                    └────────────────┬────────────────────┘
                                     │
          ┌──────────────────────────┼──────────────────────────┐
          │                          │                          │
    ┌─────▼─────┐             ┌──────▼─────┐             ┌──────▼─────┐
    │   FULL    │             │   FULL     │             │    FULL    │
    │  NODES    │             │   NODES    │             │   NODES    │
    └─────┬─────┘             └─────┬──────┘             └─────┬──────┘
          │                         │                          │
    ┌─────▼─────┐             ┌─────▼──────┐             ┌─────▼──────┐
    │ WITNESSES │             │ WITNESSES  │             │ WITNESSES  │
    │ ARCHIVERS │             │ ARCHIVERS  │             │ ARCHIVERS  │
    │   EDGES   │             │   EDGES    │             │   EDGES    │
    └───────────┘             └────────────┘             └────────────┘

Coordinators: Rare, high-capability realms, run consensus
Full: Common realms, replicate everything, serve content
Witnesses: Abundant realms, verify and store, passive sync
Archivers: Cold storage realms, batch sync
Edges: Read-only realms, intermittent, mobile
```

### Partition Tolerance

```
Network splits → clusters diverge → clusters converge on reconnect

No data loss (content-addressed)
No conflicts (immutable objects)
Audit trails merge (union of entries, Lamport ordering)
Manifests resolve (LWW or union based on type)
```

---

## Git as Export Format

### The Transition

```
Phase 1 (Now):      Git is source of truth, vault is cache
Phase 2 (Next):     Vault is source of truth, git is export
Phase 3 (Future):   Git optional, purely for GitHub presence
```

### Export Process

```scheme
(git-export
  from: ".vault"
  to: "/tmp/cyberspace-export"
  format: 'git-repo)

;; Creates standard git repo from vault contents
;; For publishing to GitHub, GitLab, etc.
```

### Import Process

```scheme
(git-import
  from: "https://github.com/ddp/cyberspace.git"
  to: ".vault")

;; Extracts objects from git, stores in vault
;; Discards git history, keeps content
```

---

## Security at Scale

### Sybil Resistance

Problem: Attacker creates many fake nodes to dominate network.

Mitigations:
1. **Stake-weighted voting** (not proof-of-work, just reputation)
2. **Web of trust** - new nodes introduced by existing trusted nodes
3. **Rate limiting** - bound resources per principal
4. **Coordinator consensus** - Byzantine-resistant core

### Eclipse Attack Resistance

Problem: Attacker isolates a node by controlling all its peers.

Mitigations:
1. **Diverse bootstrap** - multiple independent entry points
2. **Random peer selection** - can't predict who you'll connect to
3. **Peer rotation** - periodically reconnect to new peers
4. **Out-of-band verification** - publish peer lists via DNS, blockchain, etc.

### Denial of Service

Problem: Attacker floods network with junk.

Mitigations:
1. **Proof of work on announcements** (small, CPU cost)
2. **Rate limiting per principal**
3. **Reputation scoring** - misbehaving peers deprioritized
4. **Content validation** - reject malformed objects immediately

---

## Implementation Phases

### Phase 1: Native Object Store
- Implement `.vault/objects/` storage
- SQLite catalog index
- Keep git for development workflow

### Phase 2: Local-First Sync
- Direct node-to-node protocol
- `have?`/`fetch` message types
- UDP transport with TCP fallback

### Phase 3: Discovery
- Gossip peer exchange
- Bootstrap nodes
- Bloom filters for content location

### Phase 4: Scale Testing
- 100 nodes
- 1000 nodes
- 10000 nodes
- Measure: latency, convergence time, bandwidth

### Phase 5: Git Deprecation
- Vault as source of truth
- Git export for compatibility
- Remove git dependency from core operations

---

## Metrics and Monitoring

```scheme
(node-metrics)
;; Returns:
((objects-stored 150000)
 (objects-size-gb 50)
 (peers-known 500)
 (peers-connected 20)
 (sync-lag-seconds 30)
 (bandwidth-in-mbps 10)
 (bandwidth-out-mbps 5)
 (requests-per-second 100)
 (errors-per-second 0.1))
```

---

## References

1. RFC-010: Federation Protocol
2. RFC-016: Lazy Clustering
3. RFC-037: Node Roles and Capabilities
4. Maymounkov, P. (2002). Kademlia: A Peer-to-peer Information System
5. Rabin, M. (1981). Fingerprinting by Random Polynomials
6. IPFS Whitepaper (2014)
7. Shapiro, M. (2011). Conflict-Free Replicated Data Types

---

## Changelog

- 2026-01-07 - Initial draft
