# Cyberspace Project: Design Specifications
**Version**: 2026-01-01 (Rev. 2)
**Status**: Active Development
**Architect**: ddp@eludom.net / derrell@mit.edu
**Librarian**: Claude Code (semantic abstraction layer)

---

## Core Philosophy

### Peace for All Mankind: Cooperative Computing Without Enclosure

Build systems that **resist capture** and **enable collaboration without permission**:

**Decentralized Collaboration:**
- No gatekeepers, no central authority to grant access
- SPKI direct delegation: trust flows peer-to-peer
- Actor model: autonomous agents coordinate without hierarchy
- Gossip protocols: membership emerges from communication, not registration

**Knowledge Sharing & Preservation:**
- Human-readable formats prevent knowledge lock-in
- S-expressions: parseable in 2026 and parseable in 2526
- Sophisticated systems made accessible through transparency
- Long Now thinking: preserve for civilizational timescales
- Teaching through inspectability: "view source" for everything

**Anti-Corporate Enclosure:**
- No proprietary formats that require vendor tools to read
- No hierarchical CAs that create certification monopolies
- No binary blobs that hide implementation from scrutiny
- Git-compatible: diffs are human-readable, history is auditable
- Standards over platforms: protocols that outlive companies

**Systemic Approach:**
This isn't just political preference—it's **architectural necessity**. Systems that resist enclosure are systems that can evolve beyond their original context. Openness is durability. Inspectability is security. Cooperation without coercion is the only model that scales across trust boundaries.

### Long Now Thinking
Build systems that **outlive their creators** through durable engineering:
- Not transcendence, just bits that persist
- Climate-controlled warehouses, not clouds
- Standard formats, clear documentation, substrate-agnostic design
- Engineering against entropy: refactoring before calcification
- 10,000-year timescales applied to software architecture
- Preservation is resistance: bits that persist can't be enclosed

### Simplicity Wins, But Not Stupidity
- **LaTeX had it right**: Rich metadata, sophisticated structure, human-readable
- **The web won by dumbing down**: HTML/XML vs s-expressions
- **Our approach**: Sophisticated design with accessible implementation
- **SDSI/SPKI model**: Human-readable s-exprs, elegant trust chains, no baroque X.509
- **Accessible ≠ Simple-minded**: Farmers should use it; engineers should understand it

### Pre-Web Sophistication
Reject the flattening of computing history:
- **DEC's networked world**: Rich, metadata-aware, required expertise
- **CERN's web**: Simple, accessible, architecturally dumb - won adoption
- **Our synthesis**: Sophisticated protocols that don't require PhDs to verify
- **Stone knives and bear skins**: Honor the blinkenlights era while building forward
- **Reclaim what was lost**: Pre-web protocols had properties worth preserving

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

**Lazy Evaluation & Agent Dispatch:**
The Librarian operates on **lazy dispatch semantics**—work is suspended as continuations and resumed only on demand:

```lisp
; Conceptual lazy dispatch model
(define (lazy-agent-dispatch message)
  (let ((thunk (delay (process-message message))))  ; suspend computation
    (lambda ()                                       ; return continuation
      (force thunk))))                               ; resume on demand

; Agents communicate via asynchronous messages
(define (send-lazy agent message)
  (enqueue-mailbox agent (lazy-agent-dispatch message)))

; Work happens only when continuation is forced
(define (agent-loop agent)
  (let ((continuation (dequeue-mailbox agent)))
    (when continuation
      (continuation)                                 ; force evaluation
      (agent-loop agent))))
```

**Properties:**
- **Don't compute until needed**: Tool calls suspended until results required
- **Async message passing**: Agents communicate through mailboxes, not blocking calls
- **Event-driven**: Computation triggered by message arrival, not polling
- **Continuation semantics**: Each suspended operation is a resumable closure
- **Thunks everywhere**: Expensive operations wrapped in delay/force

**Why This Matters:**
- Network operations don't block: fire request, continue, resume on response
- Parallel tool invocations: all suspended, forced concurrently
- Session resume: restore continuation from disk, force evaluation to continue
- Resource efficiency: only compute what's actually needed for user intent

**Combined Properties:**
- Close over both ephemeral (chat) and durable (files) state
- Maintain causality across sessions via vector clocks
- Execute with network access to participate in distributed protocols
- Self-modifying behavior via config files that affect reasoning
- Lazy dispatch: suspend work as continuations, resume on demand
- Async coordination: agents never block waiting for each other

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

### Agent SDK Mapping (with Lazy Dispatch)

```
Claude Agent Session   → Actor with cryptographically-signed mailbox
Tool Calls             → Suspended thunks (forced when results needed)
Parallel Tool Calls    → Multiple thunks composed, forced concurrently
Session State          → Continuation serialized to event log (Merkle DAG)
Session Resume         → Restore continuation, force evaluation to proceed
Conversation History   → Causal ordering via vector clocks
Message to Agent       → Enqueue lazy dispatch thunk in mailbox
Agent Processing       → Dequeue thunk, force evaluation, emit response
Background Agents      → Spawn actor, return promise, force when needed
```

**Lazy Dispatch Semantics:**
- **Send**: Non-blocking, returns immediately with promise/future
- **Receive**: Blocks on mailbox, but agent continues other work
- **Spawn**: Create agent on-demand, don't pre-allocate resources
- **Force**: Trigger actual computation when result required
- **Compose**: Chain multiple lazy operations before forcing any

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

### Layer 3: Coordination & Consensus (Lazy Dispatch Layer)
- **Gossip protocol**: Asynchronous membership discovery, no central registry
- **CRDTs**: Conflict-free convergence without synchronous coordination
- **Vector clocks / HLC**: Causal ordering emerges from message flow
- **Byzantine agreement**: Only when needed (lazy consensus)
- **Actor model**: Agents communicate via async mailbox messages
- **Event-driven coordination**: Agents react to messages, don't poll
- **Lazy dispatch semantics**: Work suspended until response needed

**Lazy Coordination Pattern:**
```lisp
; Agent doesn't wait for response
(send-async other-agent '(request data))
; Continues with other work
(do-local-computation)
; Response arrives as message in mailbox
(receive
  [(response data) (process data)])
```

### Layer 4: Agent Runtime (Claude SDK + Lazy Evaluation)
- **Claude Agent SDK integration** with lazy dispatch wrapper
- **Session state persistence**: Continuations serialized to event log
- **Tool invocation**: Suspended as thunks, forced when results needed
- **SPKI capability checks**: Authorization evaluated lazily at force-time
- **Subagent spawning**: Agents created on-demand, supervised Erlang-style
- **Librarian as closure/continuation**: Persistent context + lazy evaluation
- **Mailbox-based communication**: Agents never block on sends
- **Thunk composition**: Chain suspended computations before forcing

### Layer 5: Application Logic
- Multi-tenant agent isolation
- Cross-agent collaboration protocols
- Query routing and load balancing
- Audit trails (s-expr event logs)
- Human-in-the-loop via AskUserQuestion

---

## Design Principles

### 1. Human-Readable by Default (Anti-Enclosure)
- S-expressions for all structured data
- No binary blobs except encrypted payloads
- Diffs should be meaningful to humans with text tools
- Configuration is code (homoiconic)
- **Why**: Formats you can read are formats you can fork
- **Peace principle**: Inspectability prevents vendor lock-in

### 2. Verifiable Without Trust (Decentralized Security)
- Crypto proofs for all assertions
- Merkle trees for state integrity
- Delegation chains auditable by inspection
- No "trust the server" assumptions
- **Why**: Math doesn't require authority
- **Peace principle**: Cooperation without coercion through cryptographic verification

### 3. Lazy Evaluation & Async Dispatch (Efficient Coordination)
- Don't compute until results needed
- Suspend work as continuations (thunks)
- Agents communicate asynchronously via mailboxes
- Compose operations before forcing evaluation
- Network calls never block local computation
- **Why**: Responsive agents, efficient resource use
- **Peace principle**: Agents coordinate without waiting for permission

### 4. Graceful Degradation (Byzantine Resilience)
- Partial state is useful state
- CRDTs merge without coordination
- Agents continue during network partitions
- Let-it-crash with state recovery
- **Why**: No single point of failure
- **Peace principle**: System survives even when participants don't cooperate

### 5. Metadata-Rich (Provenance & Accountability)
- Everything has provenance (who, when, why)
- Vector clocks for causal ordering
- Content addressing for immutability
- Audit logs are first-class citizens
- **Why**: Trust through transparency
- **Peace principle**: Accountability emerges from complete records

### 6. Long-Term Parseable (Knowledge Preservation)
- Avoid format churn (s-exprs stable since 1958)
- Self-describing messages
- Version negotiation explicit
- Migration paths documented
- **Why**: Information wants to outlive its infrastructure
- **Peace principle**: Knowledge shared across generations can't be enclosed

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

*Version 2026-01-01 Rev. 2: Added peace-for-all-mankind ethos and lazy evaluation/agent-dispatch semantics*

*Last Updated: 2026-01-01 by DDP + Librarian (Claude Code)*
