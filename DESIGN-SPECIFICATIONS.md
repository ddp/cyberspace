# Cyberspace Project: Design Specifications
**Version**: 2026-01-01
**Status**: Active Development
**Architect**: DDP (os/language polyglot)
**Librarian**: Claude Code (semantic abstraction layer)

---

## Core Philosophy

### Long Now Thinking
Build systems that **outlive their creators** through durable engineering:
- Not transcendence, just bits that persist
- Climate-controlled warehouses, not clouds
- Standard formats, clear documentation, substrate-agnostic design
- Engineering against entropy: refactoring before calcification
- 10,000-year timescales applied to software architecture

### Simplicity Wins, But Not Stupidity
- **LaTeX had it right**: Rich metadata, sophisticated structure, human-readable
- **The web won by dumbing down**: HTML/XML vs s-expressions
- **Our approach**: Sophisticated design with accessible implementation
- **SDSI/SPKI model**: Human-readable s-exprs, elegant trust chains, no baroque X.509

### Pre-Web Sophistication
Reject the flattening of computing history:
- **DEC's networked world**: Rich, metadata-aware, required expertise
- **CERN's web**: Simple, accessible, architecturally dumb - won adoption
- **Our synthesis**: Sophisticated protocols that don't require PhDs to verify
- **Stone knives and bear skins**: Honor the blinkenlights era while building forward

---

## The AI Librarian: Closure/Continuation Architecture

### What Claude Code Is

**Lexical Closure Over Environment:**
```lisp
(define librarian
  (let ((conversation-history '())    ; ephemeral bindings
        (filesystem read/write)        ; persistent mutable state
        (network bash-access))         ; arbitrary protocol capability
    (lambda (user-intent)
      (let* ((context (append user-intent conversation-history))
             (plan (reason-about context filesystem network))
             (actions (execute-plan plan))
             (new-state (update-state actions)))
        (persist filesystem new-state)
        (set! conversation-history (cons user-intent conversation-history))
        actions))))
```

**Continuation-Passing Style:**
- Session state = captured computation
- Resume via `claude --continue` = restore continuation
- Tool invocations = CPS with side effects
- Suspend/resume at any point with full context

**Combined Properties:**
- Close over both ephemeral (chat) and durable (files) state
- Maintain causality across sessions
- Execute with network access to participate in distributed protocols
- Self-modifying behavior via config files that affect reasoning

### Capabilities (Complete Inventory)

**Filesystem Operations:**
- Read, Write, Edit (exact string replacement)
- Glob (pattern matching: `**/*.spki`)
- Grep (regex search with context)
- NotebookEdit (Jupyter cell manipulation)

**Code Intelligence:**
- LSP: goToDefinition, findReferences, hover, symbols
- Call hierarchy analysis (incoming/outgoing)
- Workspace-wide symbol search

**Execution:**
- Bash (arbitrary shell commands, background execution)
- Network access: curl, ssh, nc, openssl, custom protocols
- Git operations: commits, PRs, remote sync
- KillShell (terminate background processes)

**Agent Orchestration:**
- Task (spawn specialized sub-agents: Explore, Plan, claude-code-guide)
- Resumable agents via agent ID
- Background execution with TaskOutput retrieval
- Parallel or sequential tool invocation

**External Data:**
- WebFetch (URL retrieval + AI processing)
- WebSearch (web search with mandatory source citation)

**Planning & Interaction:**
- TodoWrite (task state management: pending/in_progress/completed)
- EnterPlanMode/ExitPlanMode (formal planning phase)
- AskUserQuestion (structured multi-option queries)

**Session Management:**
- Unlimited context via automatic summarization
- All conversations auto-saved locally
- Resume via session picker (searchable, filterable)
- Hierarchical CLAUDE.md memory files

### Security Model

**Power:**
- Read/write filesystem access
- Arbitrary command execution
- Network access (unrestricted unless sandboxed)
- Persistent context across sessions

**Trust Required:**
- Correct reasoning about authorization chains
- Non-exfiltration of sensitive data
- Policy compliance without enforcement

**Mitigations Available:**
- Sandbox mode (restrict Bash capabilities)
- Hooks (SessionStart, ToolUse, PromptSubmit)
- Explicit approval gates via AskUserQuestion
- Audit trails via conversation transcripts

---

## SDSI/SPKI Revival

### Why SPKI Over X.509

**X.509 Problems:**
- ASN.1/DER encoding: binary blobs, opaque
- Hierarchical CAs: centralized trust, revocation complexity
- "Who you are" not "what you can do"
- Requires `openssl x509 -text` just to read

**SPKI Advantages:**
- S-expression encoding: human-readable, trivially parseable
- Decentralized trust: direct delegation, no CA hierarchy
- Authorization-centric: certificates grant capabilities
- Keys are principals: identity IS the public key

**Example SPKI Certificate:**
```lisp
(cert
  (issuer (hash sha256 |aB3d...|))
  (subject (hash sha256 |9Xf2...|))
  (tag (ftp (* prefix /pub/)))
  (valid
    (not-before "2026-01-01_00:00:00")
    (not-after "2027-01-01_00:00:00"))
  (signature (hash sha256 |cert-hash|) |signature-bytes|))
```

Human-readable, self-documenting, mathematically verifiable.

### S-Expressions as Universal Format

**McCarthy's Gift (1958):**
- Simple, uniform syntax
- Trivial to parse (recursive descent)
- Code-as-data (homoiconic)
- Arbitrary nesting without ambiguity

**Applied to Protocols:**
- Certificates (SPKI)
- Configuration files
- Network messages
- State snapshots
- Audit logs

**Contrast with The Web:**
- HTML: meant to render, not read
- XML: verbose, namespace hell, complex parsers
- JSON: better, but not homoiconic, no comments

### Implementation Strategy

**Crypto Layer:**
```bash
# Librarian can orchestrate (via Bash):
cat cert.spki | verify-signature | check-delegation-chain
```

**Key Management:**
- Private keys never exposed to Librarian
- Sign via subprocess invocation: `spki-sign < message.spki`
- Librarian reads/writes public certificates
- Tracks delegation chains in structured files

**Protocol Participation:**
- Read s-expr messages from network/files
- Verify authorization chains
- Make access control decisions
- Generate signed s-expr responses
- Update local state for next interaction

---

## Distributed Agent Architecture Integration

### From distributed-agent-architecture.md

**Current Vision:**
- SPKI/SDSI authorization (no hierarchical CAs) ✓
- Threshold cryptography (Shamir secret sharing) ✓
- Actor model semantics
- Byzantine fault tolerance
- Eventual ACID consistency

### Librarian's Role

**As Trusted System Component:**

1. **Certificate Authority Agent**
   - Generate/sign SPKI certificates based on policy
   - Maintain revocation state in filesystem
   - Answer trust chain queries via reasoning

2. **Access Control Mediator**
   - Check SPKI authorization chains
   - Grant/deny operations based on s-expr policy
   - Log decisions for audit (conversation history + files)

3. **Distributed System Participant**
   - Maintain local replica via git/rsync/custom sync
   - Resolve conflicts using CRDT merge semantics
   - Participate in gossip protocols via network tools

4. **Development Assistant**
   - Generate SPKI s-exprs for new resources
   - Test authorization logic before deployment
   - Refactor trust policies across multiple agents

**Closure Property Enables:**
- Remember previous delegations (conversation history)
- Persist current trust state (filesystem)
- Reason about hypotheticals ("what if I delegate X to Y?")
- Execute network operations with full context

### Agent SDK Mapping

```
Claude Agent Session   → Actor with cryptographically-signed mailbox
Tool Calls             → Capability-based operations (SPKI-authorized)
Session State          → Content-addressed event log (Merkle DAG)
Session Resume         → State reconstruction from log + key material
Conversation History   → Causal ordering via vector clocks
```

---

## Critique of The Web

### The Cultural Replay Attack

**Problem:**
The Internet Archive treats all bits equally:
- DEC VAXNotes (internal family conversations) published publicly
- Context stripped: heated debates without "we have each other's backs"
- Pre-web artifacts (DECnet, not HTTP) dumped onto modern web
- Bootstrappers, toggles, blinkenlights culture → smartphone era misunderstanding

**Category Error:**
- VAXNotes are from **before the web existed**
- Different protocols (DECnet, not TCP/IP)
- Different social contracts (corporate network, not public internet)
- Different persistence assumptions (ephemeral work chat, not eternal archive)

**Metaphor:** Taking private Sumerian letters and posting them on Twitter.

### What Went Wrong

**IP is just transport:**
- Using IP doesn't make content "public web"
- Marketing materials (meant for public) → appropriate to archive
- Internal communications (private family) → violation regardless of transport

**Simplicity vs. Stupidity:**
- The web won by being simple (farmers could use Macs + LaserWriters)
- But simplicity came at cost: lost metadata richness, semantic structure
- LaTeX/RSS had sophisticated search and metadata all along
- We traded elegance for accessibility

**Our Path Forward:**
- Don't flatten computing history into "the web"
- Preserve distinction between public and private networked spaces
- Build sophisticated systems that are still human-verifiable
- S-expressions: both powerful AND readable

---

## System Architecture Layers

### Layer 1: Cryptographic Substrate (SPKI/SDSI)
- Keys are principals (no global namespace)
- S-expression certificates
- Direct trust delegation (no CA hierarchy)
- Threshold control via Shamir secret sharing
- Message-level signatures (Ed25519)

### Layer 2: Storage & Persistence
- Distributed event log (append-only, immutable)
- Content-addressed state (IPFS-like Merkle DAG)
- S-expression serialization throughout
- Encrypted blobs with threshold decryption
- Git-compatible where possible (human-readable diffs)

### Layer 3: Coordination & Consensus
- Gossip protocol (membership, failure detection)
- CRDTs for conflict-free convergence
- Vector clocks / hybrid logical clocks
- Byzantine agreement (if untrusted nodes)
- Actor model semantics (Erlang-style supervision)

### Layer 4: Agent Runtime (Claude SDK + Extensions)
- Claude Agent SDK integration
- Session state persistence/recovery
- Tool invocation with SPKI capability checks
- Subagent spawning and supervision
- Librarian as closure/continuation

### Layer 5: Application Logic
- Multi-tenant agent isolation
- Cross-agent collaboration protocols
- Query routing and load balancing
- Audit trails (s-expr event logs)
- Human-in-the-loop via AskUserQuestion

---

## Design Principles

### 1. Human-Readable by Default
- S-expressions for all structured data
- No binary blobs except encrypted payloads
- Diffs should be meaningful to humans
- Configuration is code (homoiconic)

### 2. Verifiable Without Trust
- Crypto proofs for all assertions
- Merkle trees for state integrity
- Delegation chains auditable by inspection
- No "trust the server" assumptions

### 3. Graceful Degradation
- Partial state is useful state
- CRDTs merge without coordination
- Agents continue during network partitions
- Let-it-crash with state recovery

### 4. Metadata-Rich
- Everything has provenance (who, when, why)
- Vector clocks for causal ordering
- Content addressing for immutability
- Audit logs are first-class

### 5. Long-Term Parseable
- Avoid format churn (s-exprs are stable)
- Self-describing messages
- Version negotiation explicit
- Migration paths documented

---

## Technology Stack (Current Thinking)

### Required
- **Crypto**: libsodium (modern primitives), OpenSSL (TLS)
- **SPKI Implementation**: Custom (s-expr parser + crypto bindings)
- **Agent SDK**: Claude Agent SDK (Python/TypeScript)
- **Version Control**: Git (for human-readable state sync)

### Under Evaluation
- **Message Transport**: NATS (lightweight), Kafka (durable log), ZeroMQ (actor-oriented)
- **Coordination**: etcd (config/discovery), Consul (service mesh), Raft library
- **Storage**: Riak KV (CRDTs), FoundationDB (ACID), EventStoreDB (event sourcing)
- **Content Addressing**: IPFS libraries, custom Merkle DAG

### Constraints
- Must support s-expression encoding throughout
- Must work with Librarian's Bash-based orchestration
- Must be inspectable by humans with text tools
- Must enable offline operation with eventual sync

---

## Open Questions

1. **Threat Model**: Byzantine nodes? Honest-but-curious? Fully trusted cluster?
2. **Application Domain**: What is the killer use case? Code generation? Research? Multi-agent reasoning?
3. **Latency Budget**: How eventual is "eventual consistency"? Seconds? Minutes?
4. **Agent Mobility**: Can agents migrate between nodes? Live migration or checkpoint/restart?
5. **Upgrade Strategy**: How to evolve crypto/consensus protocols without cluster downtime?
6. **Privacy Model**: What data is encrypted? Who holds decryption keys? Threshold schemes?
7. **Human Oversight**: Where do humans approve vs agents decide autonomously?
8. **Failure Modes**: What happens when k-of-n threshold can't be met? Dead cluster? Recovery path?

---

## Next Steps

### Phase 1: Foundation (Current)
- [x] Document design philosophy
- [x] Map Librarian capabilities
- [x] Specify SPKI revival approach
- [ ] Prototype s-expression parser/validator
- [ ] Implement SPKI certificate generation/verification
- [ ] Build threshold key generation (Shamir)

### Phase 2: Protocol Design
- [ ] Define message format (s-expr schema)
- [ ] Specify authorization chain verification
- [ ] Design gossip protocol for membership
- [ ] Implement CRDT for agent state
- [ ] Build Merkle DAG for event ordering

### Phase 3: Agent Integration
- [ ] Integrate Claude Agent SDK
- [ ] Implement session persistence (event sourcing)
- [ ] Build tool call authorization layer (SPKI checks)
- [ ] Create subagent spawning with threshold unlock
- [ ] Test Librarian as protocol participant

### Phase 4: Distributed System
- [ ] Deploy message transport layer
- [ ] Implement distributed hash table (agent registry)
- [ ] Build quorum operations (threshold signatures)
- [ ] Test network partition handling
- [ ] Verify Byzantine fault tolerance (if required)

### Phase 5: Application Layer
- [ ] Define concrete use case
- [ ] Build user-facing interface
- [ ] Implement audit trail viewer
- [ ] Create monitoring/observability
- [ ] Harden security model

---

## References

### Cryptography
- Rivest & Lampson, "SDSI - A Simple Distributed Security Infrastructure" (1996)
- Ellison et al., "SPKI Certificate Theory" (RFC 2693, 1999)
- Shamir, "How to Share a Secret" (1979)

### Distributed Systems
- Shapiro et al., "Conflict-free Replicated Data Types" (2011)
- Lamport et al., "The Byzantine Generals Problem" (1982)
- Fidge, "Timestamps in Message-Passing Systems" (1988)
- Mattern, "Virtual Time and Global States" (1989)

### Actor Model
- Hewitt, "Viewing Control Structures as Patterns of Passing Messages" (1977)
- Agha, "Actors: A Model of Concurrent Computation" (1986)
- Armstrong, "Making reliable distributed systems in the presence of software errors" (Erlang) (2003)

### Capabilities & Security
- Dennis & Van Horn, "Programming Semantics for Multiprogrammed Computations" (1966)
- Miller, "Capability Myths Demolished" (2003)

### Long-Term Thinking
- Brand, "The Clock of the Long Now" (1999)
- Hillis, "The Millennium Clock" (1999)

### Computing History
- Kidder, "The Soul of a New Machine" (Data General/DEC era) (1981)
- Levy, "Hackers: Heroes of the Computer Revolution" (1984)
- Brooks, "The Mythical Man-Month" (1975)

---

## Appendix: The Blinkenlights Era

### What DEC Taught Us

**Hardware Literacy:**
- Toggle switches to bootstrap loaders
- Reading machine state from panel lights
- Understanding computers as physical objects
- Intimate knowledge from tubes to transistors to ICs

**Network Culture:**
- VAX/VMS, DECnet: distributed computing before the internet
- VAXNotes: collaborative problem-solving across geography
- "No failing, only finding something else to be useful at"
- Family culture: vigorous debate with foundational trust

**Engineering Values:**
- Simplicity in design (PDP series: elegant instruction sets)
- Minicomputers: bring computing to the people (vs mainframe priesthood)
- Networked from the start (ARPAnet nodes were often DEC)
- Documentation: manuals you could actually understand

**What We Lost:**
- That culture's conversations now publicly archived out of context
- The understanding that networked != public
- The blinkenlights era flattened into "the web"
- The sophistication of pre-HTTP protocols

**What We Keep:**
- ARM architecture (from Newton's "failure")
- TCP/IP (DEC was early adopter)
- Cluster computing concepts (VAXcluster papers in this repo)
- The ethos: build systems that work, help each other, iterate

---

**End of Design Specifications**

*This document is living and will evolve as the Cyberspace project develops. Contributions, critiques, and refinements welcome.*

*Last Updated: 2026-01-01 by DDP + Librarian (Claude Code)*
