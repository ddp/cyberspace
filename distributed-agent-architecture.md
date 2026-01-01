# Distributed Agent Cluster Architecture
**Cryptographically-Secured, Eventually-Consistent Agent System**

## Vision: Cyberspace
Loosely coupled cluster of Claude agents with:
- SPKI/SDSI authorization (no hierarchical CAs)
- Threshold cryptography (Shamir secret sharing)
- Actor model semantics
- Byzantine fault tolerance capability
- Eventual ACID consistency

## Core Requirements

### Cryptographic Foundation: SPKI/SDSI + Shamir

**Identity Model** (SPKI/SDSI):
- **Keys are principals** — agent identity IS the public key
- **No global namespace** — local names only (`ddp's-cluster/coordinator`)
- **Authorization certificates** — not "who you are" but "what you can do"
- **No hierarchical CAs** — direct trust delegation
- **Certificate chains** — transitive authorization without central authority

**Threshold Control** (Shamir):
- **Bootstrap**: Cluster master key split into k-of-n shares
- **Agent spawning**: Threshold reconstruction required (k shares collaborate)
- **Key derivation**: New agent keypairs derived from reconstructed master
- **No single point of control**: No agent holds complete cluster secret
- **Privacy**: Encrypted state requires threshold decryption

**Authentication**:
- Message-level signatures (Ed25519)
- SPKI signature chains prove authorization
- Attestation via Merkle trees + vector clocks + crypto proofs

### Distributed Coordination
- **Consistency Model**: CRDTs for conflict-free convergence
- **Membership**: Gossip protocol for cluster awareness
- **Location**: Distributed hash table for agent registry
- **Authorization**: SPKI authorization certificates (not capability tokens)
- **Quorum Operations**: Threshold signatures for cluster-wide decisions

### Storage Layer
**Event-Oriented Persistence** (no SQL):
- Distributed append-only log (Kafka / NATS JetStream)
- Content-addressed storage for agent state (IPFS-like)
- Merkle DAG for causal history tracking
- Immutable event sourcing for state reconstruction

**Candidates:**
- **Event Store**: Kafka, EventStoreDB
- **KV/Snapshot**: Redis (pub/sub), etcd (registry), Riak (AP-mode)
- **Document**: CouchDB (replication), MongoDB (if needed)
- **Actor-Native**: Datomic (time-travel), FoundationDB (ACID)

## Claude Agent SDK Mapping

### Agent Primitives → Distributed System
```
Claude Agent          →  Cluster Node (actor with mailbox)
Subagent             →  Supervised worker pool
Session State        →  Cryptographically-signed event log
Tool Calls           →  Capability-based operations
Session Resume       →  State reconstruction from event log
```

### Supervision Hierarchy
- Main agents manage subagent lifecycle (Erlang-style supervision)
- Let-it-crash semantics with cryptographic checkpointing
- State recovery via event replay + Shamir key reconstruction

### Agent Coordination Pattern
```python
# Pseudo-architecture
session_id = spawn_agent(capabilities, crypto_context)
→ Store session_id in DHT with crypto signature
→ Agents communicate via signed messages
→ State changes append to distributed log
→ CRDT merge on reads for eventual consistency
→ Threshold signatures for cluster-wide decisions
```

## Architecture Layers

### Layer 1: Cryptographic Substrate
- Shamir secret sharing for cluster unlock
- Key derivation hierarchy for agent identities
- Message authentication codes (HMAC)
- Merkle proofs for state verification

### Layer 2: Consensus & Coordination
- Gossip protocol (membership, failure detection)
- Vector clocks / hybrid logical clocks
- CRDT merge semantics
- Byzantine agreement (if untrusted nodes)

### Layer 3: Storage & Persistence
- Distributed event log (immutable, append-only)
- Content-addressed state snapshots
- Causal ordering via Merkle DAG
- Encrypted blobs with threshold decryption

### Layer 4: Agent Runtime
- Claude Agent SDK integration
- Session state persistence/recovery
- Tool invocation with capabilities
- Subagent spawning and supervision

### Layer 5: Application Logic
- Multi-tenant agent isolation
- Cross-agent collaboration protocols
- Query routing and load balancing
- Audit trails and forensics

## Open Questions

1. **Threat Model**: Byzantine nodes? Honest-but-curious? Fully trusted?
2. **Application Domain**: Code generation? Distributed analysis? Multi-tenant SaaS?
3. **Latency vs. Consistency**: How eventual is "eventual"?
4. **Agent Mobility**: Can agents migrate between nodes?
5. **Upgrade Strategy**: How to evolve crypto/consensus without downtime?

## Technology Stack Candidates

**Message Transport**:
- NATS (lightweight, crypto-friendly)
- Kafka (durable log, proven at scale)
- ZeroMQ (actor-oriented messaging)

**Coordination**:
- etcd (configuration, service discovery)
- Consul (service mesh, gossip)
- Raft consensus library

**Storage**:
- Riak KV (AP, eventual consistency, CRDTs)
- FoundationDB (ACID, ordered key-value)
- EventStoreDB (native event sourcing)

**Crypto**:
- libsodium (modern crypto primitives)
- OpenSSL/BoringSSL (TLS, certificates)
- IPFS libraries (content addressing, Merkle DAGs)

## References
- Shamir Secret Sharing (1979)
- CRDTs: Shapiro et al., "Conflict-free Replicated Data Types" (2011)
- Actor Model: Hewitt, Agha
- Byzantine Generals Problem: Lamport et al.
- Vector Clocks: Fidge, Mattern
- Capability-Based Security: Dennis & Van Horn (1966)

## Next Steps
1. Define concrete use case / application domain
2. Specify threat model and trust assumptions
3. Select storage backend based on consistency requirements
4. Prototype Shamir scheme integration with Claude Agent SDK
5. Design message format with crypto primitives
6. Implement gossip protocol for cluster membership
7. Build CRDT layer for agent state convergence

---

**Created**: 2025-12-31
**Context**: Exploring distributed agent architecture with cryptographic guarantees
