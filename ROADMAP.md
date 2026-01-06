# Cyberspace - 6 Month Roadmap

**Timeline:** January 2026 - June 2026

**Philosophy:** "Rough consensus, cryptography, trusted systems and running code."

**Prime Directive:** TCB=OCaml, Everything else=Chicken Scheme

---

## Current State (January 2026)

### ✅ Complete
- **Library:** 421 papers across 16 categories
- **Implementations (Scheme):**
  - Lamport OTP (hash-chain authentication)
  - Merkle Trees (authenticated data structures)
  - Capabilities (unforgeable tokens, delegation)
  - ChaCha20 (ARX stream cipher)
  - Poly1305 (polynomial MAC, educational)
  - Lamport Signatures (code done, README pending)
- **SPKI TCB (OCaml):** ✨ NEW - Minimal crypto core
  - Ed25519 signatures via libsodium FFI
  - SHA-512 hashing
  - ~200 lines of verified crypto
  - All tests passing
- **SPKI Scheme FFI:** ✨ NEW - Chicken Scheme crypto bindings
  - Direct libsodium FFI working
  - All crypto tests passing
- **Coq Verification:** ✨ NEW - Formal proofs started
  - Signature.v: Ed25519 security properties
  - 6 axioms, 6 theorems (1 admitted)
  - Build system configured
- **SPKI (OCaml):** S-expression certs, chain verification, CLI tools
- **API Server:** Framework, library search working
- **Librarian:** Index builder (33 INDEX.md files parsed)
- **CONTEXT.md:** Prime Directive documented

### 🚧 In Progress
- SPKI Scheme implementation (s-expressions, certs, CLI)
- API crypto endpoints (scaffolded, needs integration)
- Lamport Signatures README

### 📋 Not Started
- Librarian semantic search
- Distributed agent architecture
- TLA+ protocol specification
- Coq byte-level model & extraction
- ChaCha20-Poly1305 AEAD
- Lamport Logical Clocks
- Federation protocols

---

## Month 1: Foundation & TCB Architecture (January 2026)

**Goal:** Establish clean TCB boundary, complete existing work

### Week 1-2: SPKI TCB Extraction
```
spki/
├── tcb/                    # OCaml - Crypto ONLY
│   ├── signature.ml        # Ed25519 via libsodium
│   ├── chain.ml            # Chain validation math
│   ├── cert.ml             # Certificate parsing/validation
│   └── export.ml           # C API for Scheme FFI
│
├── scheme/                 # Chicken Scheme - Everything else
│   ├── tcb-ffi.scm         # FFI to OCaml TCB
│   ├── policy.scm          # Policy evaluation
│   ├── sdsi.scm            # Name resolution
│   ├── discovery.scm       # Certificate discovery
│   └── tools/              # CLI rewritten in Scheme
│       ├── spki-keygen.scm
│       ├── spki-cert.scm
│       ├── spki-verify.scm
│       └── spki-show.scm
```

**Deliverables:**
- [ ] OCaml TCB (~1000 lines, libsodium bindings)
- [ ] C API exported from OCaml
- [ ] Scheme FFI to TCB
- [ ] SPKI CLI tools rewritten in Scheme
- [ ] Policy layer in pure s-expressions
- [ ] Tests: Scheme calls OCaml, crypto works

### Week 3: Complete Lamport Signatures
- [ ] Write comprehensive README
- [ ] Explain post-quantum properties
- [ ] Update INDEX.md
- [ ] Commit and push

### Week 4: API Integration
- [ ] Wire crypto routes to actual implementations
- [ ] `/crypto/lamport/sign` → call implementations/lamport-signatures/
- [ ] `/crypto/chacha20/encrypt` → call implementations/chacha20/
- [ ] `/crypto/merkle/build` → call implementations/merkle-tree/
- [ ] `/crypto/spki/verify` → call scheme/tcb-ffi.scm
- [ ] Integration tests

**Milestone:** Clean TCB boundary, SPKI policy in Scheme, API functional

---

## Month 2: Implementations & Crypto (February 2026)

**Goal:** Complete core cryptographic suite

### Week 1-2: ChaCha20-Poly1305 AEAD
```
implementations/chacha20-poly1305/
├── aead.scm                # Combine ChaCha20 + Poly1305
├── nonce-manager.scm       # Prevent nonce reuse
├── test-vectors.scm        # RFC 7539 test vectors
└── README.md               # AEAD construction explained
```

**Deliverables:**
- [ ] Authenticated encryption with associated data
- [ ] Passes RFC 7539 AEAD test vectors
- [ ] Demonstrates encrypt-then-MAC
- [ ] Integration with API `/crypto/aead/encrypt`

### Week 3-4: Lamport Logical Clocks
```
implementations/lamport-clocks/
├── logical-clock.scm       # Happened-before relation
├── vector-clock.scm        # Concurrent events
├── demo-distributed.scm    # Multi-process demo
└── README.md               # Distributed systems time
```

**Deliverables:**
- [ ] Logical timestamps
- [ ] Vector clocks for causality
- [ ] Demo: 3+ processes with message passing
- [ ] Explains happened-before (→) relation

**Milestone:** Core crypto complete, distributed systems foundations

---

## Month 3: Librarian & Discovery (March 2026)

**Goal:** AI-powered semantic search for Library

### Week 1-2: Semantic Search
```
librarian/
├── embedder.scm            # Generate embeddings (Ollama/Claude API)
├── vector-store.scm        # SQLite with vector search
├── search.scm              # Semantic query engine
└── repl.scm                # Interactive search REPL
```

**Architecture:**
```scheme
(search "Papers about hash-based crypto before 1985")
→ Finds: Lamport 1979, Merkle 1979, Rabin 1978
→ Context: Pre-RSA, foundation for post-quantum
→ Connections: → SPHINCS+ (2015), → XMSS (2018)
```

**Options:**
- **Local:** Ollama (nomic-embed-text)
- **Cloud:** Claude API prompt-based search
- **Storage:** SQLite with vector similarity

**Deliverables:**
- [ ] Embedding generation working
- [ ] Vector similarity search
- [ ] Natural language queries
- [ ] Citation with paper locations
- [ ] REPL: `(search "quantum-resistant signatures")`

### Week 3-4: API Search Endpoint
- [ ] `/library/search?q=semantic+query`
- [ ] Returns papers with relevance scores
- [ ] Temporal reasoning (before/after dates)
- [ ] Cross-domain connections

**Milestone:** AI-powered library discovery, semantic understanding

---

## Month 4: Verification Foundations (April 2026)

**Goal:** Begin formal verification of TCB

### Week 1-2: TLA+ Protocol Model
```
protocol/
├── spki-chains.tla         # Certificate chain protocol
├── delegation.tla          # Delegation semantics
├── sdsi-names.tla          # Name resolution
└── properties.tla          # Safety & liveness
```

**Properties to prove:**
- **Safety:** No forgery (can't create cert without key)
- **Safety:** Chain integrity (valid links)
- **Safety:** Propagation respect (non-propagate honored)
- **Liveness:** Valid chains eventually verify
- **Liveness:** Verification terminates

**Deliverables:**
- [ ] TLA+ specification of SPKI protocol
- [ ] Model checking with TLC
- [ ] Invariants proven
- [ ] Document findings

### Week 3-4: Coq Groundwork
```
tcb-proof/
├── signature.v             # Signature correctness
├── chain.v                 # Chain validation
└── properties.v            # TCB guarantees
```

**Initial theorems:**
```coq
Theorem signature_correct : forall pk sk msg,
  valid_keypair pk sk ->
  verify(pk, msg, sign(sk, msg)) = true.

Theorem no_forgery : forall pk msg sig,
  verify(pk, msg, sig) = true ->
  exists sk, sign(sk, msg) = sig.
```

**Deliverables:**
- [ ] Coq development environment
- [ ] Model of signature primitives
- [ ] Initial proofs (signature correctness)
- [ ] Extraction setup (Coq → OCaml)

**Milestone:** Formal specs complete, proof infrastructure ready

---

## Month 5: Distributed Architecture (May 2026)

**Goal:** Multi-agent system with SPKI authorization

### Week 1-2: Agent Framework
```
agents/
├── agent.scm               # Base agent (REPL + message passing)
├── spawn.scm               # Agent spawning with capabilities
├── registry.scm            # Agent discovery
└── protocol.scm            # Inter-agent protocol
```

**Architecture:**
```scheme
;; Spawn agent with capability
(define alice-agent
  (spawn-agent 'librarian
    (capability (read (path /library/*))
                (search library))))

;; Send message with authorization
(send alice-agent
  `(search "Lamport signatures")
  my-capability)
```

**Deliverables:**
- [ ] Agent spawning with SPKI authorization
- [ ] Message passing between agents
- [ ] Capability propagation
- [ ] Agent discovery (local registry)

### Week 3-4: Distributed Gossip
```
network/
├── gossip.scm              # Certificate distribution
├── sync.scm                # SPKI cert synchronization
└── peer.scm                # Peer discovery
```

**Protocol:**
- Gossip SPKI certificates across nodes
- Sync delegation chains
- Peer discovery (local network)
- Content-addressable cert storage (Merkle-based)

**Deliverables:**
- [ ] Gossip protocol for cert distribution
- [ ] Multi-node testing (3+ machines)
- [ ] Eventual consistency
- [ ] Integration with SPKI TCB

**Milestone:** Distributed multi-agent system operational

---

## Month 6: Polish & Documentation (June 2026)

**Goal:** Production-ready, documented, verified

### Week 1: Security Audit
- [ ] Review all crypto code
- [ ] Check for timing attacks
- [ ] Validate HMAC/signature implementations
- [ ] Test certificate chain edge cases
- [ ] Fuzz testing (QuickCheck-style)

### Week 2: Documentation Sprint
- [ ] Update all READMEs
- [ ] Architecture diagrams
- [ ] Tutorial: "Build a distributed app with Cyberspace"
- [ ] API reference documentation
- [ ] Video walkthrough (optional)

### Week 3: Advanced Features
**Pick 2-3:**
- [ ] Certificate revocation
- [ ] Threshold signatures (Shamir secret sharing)
- [ ] Byzantine consensus (simplified Paxos)
- [ ] Zero-knowledge proofs (educational)
- [ ] Cryptographic file system (CFS)

### Week 4: Release Preparation
- [ ] Version 1.0.0 tag
- [ ] Release notes
- [ ] Public announcement (blog post?)
- [ ] Demo deployment
- [ ] Docker containers (optional)

**Milestone:** Cyberspace 1.0 - production ready

---

## Success Criteria

By end of 6 months:

### Technical
- ✅ OCaml TCB (~1-2K lines) with libsodium
- ✅ 8+ working implementations in Scheme
- ✅ SPKI with policy in Scheme, crypto in OCaml
- ✅ API server with crypto endpoints
- ✅ Librarian with semantic search
- ✅ Distributed agent framework
- ✅ TLA+ protocol specification
- ✅ Initial Coq proofs

### Research → Practice
- ✅ Every implementation links to papers
- ✅ Clear lineage from research to code
- ✅ Educational value (understand papers by building)
- ✅ Running code demonstrates concepts

### Documentation
- ✅ CONTEXT.md (philosophy, Prime Directive)
- ✅ ROADMAP.md (this document)
- ✅ Per-implementation READMEs
- ✅ API documentation
- ✅ Architecture diagrams

### Verification
- ✅ TLA+ model checked
- ✅ Coq proofs for TCB critical paths
- ✅ Property testing (QuickCheck style)
- ✅ Security audit complete

---

## Dependencies & Risks

### Technical Dependencies
- **libsodium:** For OCaml TCB crypto primitives
- **Ollama/Claude API:** For Librarian semantic search
- **SQLite:** For vector storage
- **Coq:** For formal verification

### Risks & Mitigations

**Risk:** Coq verification too ambitious for 6 months
**Mitigation:** Start with TLA+ (faster), Coq proofs incremental

**Risk:** FFI between OCaml/Scheme complex
**Mitigation:** Start simple (signature verify only), expand gradually

**Risk:** Distributed system debugging difficult
**Mitigation:** Local-only first, then multi-machine

**Risk:** Scope creep (too many implementations)
**Mitigation:** Focus on quality over quantity (8 implementations is plenty)

---

## Stretch Goals (if ahead of schedule)

- Formal verification of full TCB (complete Coq proofs)
- Byzantine fault tolerance (simplified Paxos/Raft)
- Zero-knowledge authentication (Schnorr, Fiat-Shamir)
- Homomorphic encryption (educational)
- Secure multi-party computation
- Integration with existing systems (SSH, HTTP)

---

## Philosophy Throughout

Every month should demonstrate:
- **Research → Practice:** Papers become code
- **TCB discipline:** OCaml for crypto, Scheme for everything else
- **Human-readable:** S-expressions, auditable policies
- **Formal methods:** TLA+/Coq where it matters
- **Running code:** Everything works, not just designs

---

## Metrics of Success

Not traditional software metrics, but:
- **Papers implemented:** How many research ideas became code?
- **Lineage traced:** Can we show Lamport 1979 → SPHINCS+ 2015?
- **Verification coverage:** What % of TCB is proven correct?
- **Educational value:** Can someone learn distributed systems by reading this?

---

## Monthly Check-ins

End of each month:
1. **Demo:** Show working code
2. **Commits:** Review git history
3. **Documentation:** Update READMEs
4. **Adjust:** Revise roadmap based on progress

---

**"Six months to build a library that demonstrates foundational computer science research through running, verified code."**

---

## Quick Reference

**Month 1:** TCB architecture (SPKI OCaml/Scheme split)
**Month 2:** Crypto implementations (AEAD, Lamport Clocks)
**Month 3:** Librarian semantic search (AI-powered discovery)
**Month 4:** Verification (TLA+, Coq foundations)
**Month 5:** Distributed system (agents, gossip)
**Month 6:** Polish, audit, document, release

**End state:** Production-ready Cyberspace with verified TCB, rich implementations, AI-powered discovery, and distributed architecture.
