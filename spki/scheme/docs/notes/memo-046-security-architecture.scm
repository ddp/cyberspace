;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 46)
  (title "Cyberspace Security Architecture")
  (section
    "Abstract"
    (p "This document defines how cyberspace protects itself. The model is simple: capabilities all the way down. Objects are content. Authorization flows through signed certificates. No labels, no ACLs, no ambient authority. You hold a capability or you don't.")
    (p "We use the rigor of TCSEC B2 as a lens - particularly for covert channel analysis - but cyberspace is its own thing. This is our security architecture, in our language."))
  (section
    "The Manifesto"
    (blockquote "Authorized capability set with auditing. No central authority.")
    (p "You can have a central authority if you want one. That's up to you. But you don't need one. The architecture doesn't require it. Trust flows from keys you choose to trust, not from a hierarchy imposed upon you.")
    (p "These principles were proven in VAXcluster security (1984-1994), proposed in SDSI at IETF 29 Seattle (1994), and implemented partially in products that didn't survive their parent companies. Cyberspace completes what was started.")
    (subsection
      "Design Lineage"
      (table
        (header "Era " "System " "Contribution ")
        (row "1984 " "VAXcluster " "\"Behave as one\" - N nodes, one security domain ")
        (row "1985 " "VMS C2 " "Audit trails, access control, TCSEC security primitives ")
        (row "1993 " "VMS 6.0 " "Cluster-wide intrusion detection, TLV object store ")
        (row "1994 " "SDSI " "Self-certifying keys, local names (Rivest, IETF 29) ")
        (row "1999 " "SPKI " "Authorization certificates, capability delegation ")
        (row "2026 " "Cyberspace " "Synthesis: SPKI + audit + IPv6 mesh + no central authority "))
      (p "DECnet Phase IV had 24-bit addressing—fatal for internet scale. Cyberspace is designed for IPv6: 128-bit addresses, global mesh, same security principles.")))
  (section
    "Security Object Types"
    (p "Every first-class object in cyberspace. Names as defined.")
    (p "Table 0: Security Object Registry")
    (table
      (header "Object " "Defining RFC " "Description ")
      (row "Identity ")
      (row "principal " "Memo-004 " "Cryptographic identity (ed25519 key or hash) ")
      (row "key " "Memo-022 " "Keypair with ceremony provenance ")
      (row "attestation " "Memo-041 " "Signed claim about identity or state ")
      (row "Authorization ")
      (row "certificate " "Memo-004 " "SPKI capability grant ")
      (row "tag " "Memo-004 " "Authorization scope (read, write, etc.) ")
      (row "signature " "Memo-004 " "Ed25519 attestation ")
      (row "share " "Memo-008 " "Shamir secret fragment ")
      (row "quorum " "Memo-036 " "Voting threshold specification ")
      (row "Storage ")
      (row "vault " "Memo-006 " "Sovereign storage realm ")
      (row "object " "Memo-020 " "Content-addressed immutable data ")
      (row "archive " "Memo-018 " "Sealed, encrypted content package ")
      (row "schema " "Memo-033 " "Structure definition ")
      (row "Boundaries ")
      (row "realm " "Memo-040 " "Trust and sovereignty boundary ")
      (row "wormhole " "Memo-041 " "FUSE mount portal to filesystem ")
      (row "federation " "Memo-010 " "Peer network of realms ")
      (row "node " "Memo-037 " "Network participant with role ")
      (row "Execution ")
      (row "agent " "Memo-023 " "Sandboxed daemon ")
      (row "topic " "Memo-035 " "Pub/sub channel ")
      (row "tunnel " "Memo-035 " "Agent communication path ")
      (row "lock " "Memo-035 " "Distributed mutex ")
      (row "Observability ")
      (row "audit-entry " "Memo-003 " "Immutable log record ")
      (row "lamport-clock " "Memo-012 " "Causal ordering timestamp ")
      (row "query " "Memo-025 " "Search expression ")
      (row "Documentation ")
      (row "memo " "Memo-043 " "Scoped documentation unit ")
      (row "soup " "Memo-040 " "The auditable collection of all things "))
    (subsection
      "Object Properties"
      (p "All security objects share:")
      (code "1. Content-addressed identity (SHA-512 hash)\n2. Cryptographic signature (Ed25519)\n3. Audit trail integration (Memo-003)\n4. Capability-gated access (Memo-004)\n5. State: chaotic | quiescent"))
    (subsection
      "Object State"
      (p "All things in cyberspace exist in two states:")
      (table
        (header "State " "Meaning " "Properties ")
        (row "chaotic " "In flux, being modified " "Mutable, uncommitted, local ")
        (row "quiescent " "At rest, stable " "Immutable, signed, replicable "))
      (p "Transitions:")
      (code "chaotic ──commit──▶ quiescent\n    ▲                   │\n    │                   │\n    └───── fork ────────┘")
      (p "Only quiescent objects: - Have stable content hashes - Can be signed - Can be replicated - Can be delegated")
      (p "Chaotic things: - Exist only in the realm's store - Have provisional identity - Cannot be shared - Must settle before federation - Cannot be cached"))
    (subsection
      "Caching Implications"
      (p "State controls caching:")
      (table
        (header "State " "Cacheable " "Reason ")
        (row "quiescent " "Forever " "Hash is identity; immutable ")
        (row "chaotic " "Never " "Content may change; no stable hash "))
      (p "Quiescent things cache by content hash. Cache hit = identical content, guaranteed. Chaotic things bypass cache entirely. Every access reads current state."))
    (subsection
      "Persistence"
      (p "Persistence is the guarantee of migration to the vault.")
      (table
        (header "Durability " "Meaning ")
        (row "persistent " "Guaranteed to migrate to vault ")
        (row "ephemeral " "May vanish; no durability promise "))
      (p "State and durability are orthogonal:")
      (table
        (header "Ephemeral " "Persistent ")
        (row "Chaotic " "Scratch work " "Draft being saved ")
        (row "Quiescent " "Cached result " "Archived thing "))
      (p "Persistent things survive restart. Ephemeral things don't.")
      (p "Vault takes cataloging and effort. Not all things need persistence. Ephemeral is not failure—it's deliberate economy. Cache results, scratch work, intermediate computations: let them vanish.")
      (p "Marking a thing persistent schedules vault migration.")
      (code scheme "(persist thing)    ; guarantee vault migration\n(ephemeral thing)  ; no durability promise"))
    (subsection
      "Object Relationships"
      (code "principal ──creates──▶ certificate ──grants──▶ tag\n    │                      │\n    │                      ▼\n    │                   object ◀──stores── vault\n    │                      │\n    ▼                      ▼\n  agent ──operates──▶ wormhole ──bridges──▶ realm\n    │                                         │\n    │                                         ▼\n    └──────────────────────────────────▶ federation")))
  (section
    "The Axioms"
    (code "A1. No Ambient Authority\n    You have nothing until someone gives you something.\n    Every access requires presenting a capability.\n\nA2. Capabilities Are Unforgeable\n    Ed25519 signatures. No exceptions.\n    Create by origin or delegation. No other path.\n\nA3. Capabilities Only Attenuate\n    Delegation can reduce rights, never amplify.\n    What you give cannot exceed what you hold.\n\nA4. Objects Are Immutable Content\n    SHA-512 hash IS identity.\n    No metadata. No labels. No ACLs.\n    Objects don't know who can access them."))
  (section
    "The Realm"
    (p "A realm is your place in cyberspace. It is sovereign.")
    (code "┌─────────────────────────────────────────────────────────────┐\n│                        YOUR REALM                            │\n│                                                              │\n│   Principal: ed25519:a1b2c3...  (this is you)               │\n│                                                              │\n│   ┌──────────────────────────────────────────────────────┐  │\n│   │                      VAULT                            │  │\n│   │  Objects:     content-addressed, signed               │  │\n│   │  Capabilities: certificates you hold                  │  │\n│   │  Audit:       what happened here                      │  │\n│   └──────────────────────────────────────────────────────┘  │\n│                                                              │\n│   Trust boundary: your signing key                          │\n│   You decide: what to store, who to trust, what to share    │\n└─────────────────────────────────────────────────────────────┘")
    (p "Your realm is local-first. Federation is optional. When you federate, realms overlap - objects flow according to capability chains. But your realm remains yours."))
  (section
    "Capabilities"
    (subsection
      "The Certificate"
      (code scheme "(spki-cert\n  (issuer \"ed25519:alice...\")        ; Who grants\n  (subject \"ed25519:bob...\")         ; Who receives\n  (tag (read \"sha512:doc...\"))       ; What: read this object\n  (valid (not-after 1736400000))     ; When: expires in 24h\n  (propagate #f)                     ; Bob cannot delegate\n  (signature \"ed25519:...\"))         ; Alice's signature"))
    (subsection
      "Access Check"
      (code "Can Bob read sha512:doc?\n\n1. Does Bob hold a cert granting (read \"sha512:doc\")?\n2. Is the signature valid?\n3. Is it expired?\n4. Is it revoked?\n5. Does the chain trace to someone who could grant it?\n\nAll yes? Access granted.\nAny no?  Access denied."))
    (subsection
      "Delegation"
      (p "Alice can give Bob read access:")
      (code scheme "(spki-cert\n  (issuer \"ed25519:alice...\")\n  (subject \"ed25519:bob...\")\n  (tag (read \"sha512:doc...\"))\n  (propagate #t))                    ; Bob CAN delegate")
      (p "Bob can give Carol read access (because Alice allowed propagation):")
      (code scheme "(spki-cert\n  (issuer \"ed25519:bob...\")\n  (subject \"ed25519:carol...\")\n  (tag (read \"sha512:doc...\"))\n  (propagate #f))                    ; Carol cannot delegate further")
      (p "Carol cannot give anyone else access. The chain stops.")))
  (section
    "Classification Without Labels"
    (p "Traditional MAC puts labels on objects: UNCLASSIFIED, SECRET, TOP SECRET.")
    (p "In cyberspace, classification is a capability you hold:")
    (code scheme ";; Security officer grants SECRET clearance\n(spki-cert\n  (issuer \"ed25519:security-officer...\")\n  (subject \"ed25519:analyst...\")\n  (tag (clearance secret))\n  (valid (not-after 1767225600)))    ; Annual renewal\n\n;; Program manager grants compartment access\n(spki-cert\n  (issuer \"ed25519:program-manager...\")\n  (subject \"ed25519:engineer...\")\n  (tag (compartment \"project-atlas\")))")
    (p "Access to a classified object requires: 1. Capability to read the object itself 2. Appropriate clearance capability 3. All required compartment capabilities")
    (p "The object has no labels. The policy lives in the certificates."))
  (section
    "Information Flow"
    (p "The mathematics of multilevel security, expressed in capabilities.")
    (subsection
      "The Properties"
      (p "Traditional formulations speak of \"read up\" and \"write down\" with respect to classification labels. We preserve the mathematics but speak differently:")
      (table
        (header "Traditional " "Cyberspace " "Formal Statement ")
        (row "\"No read up\" " "Read requires capability " "∀ read(P,O): P ∈ holders(cap_read(O)) ")
        (row "\"No write down\" " "Write requires capability " "∀ write(P,O): P ∈ holders(cap_write(O)) ")
        (row "\"No read down\" " "Integrity via provenance " "∀ accept(P,O): verify(signature(O)) ")
        (row "\"No write up\" " "Attenuation only " "∀ delegate(P₁,P₂,C): C ⊆ capabilities(P₁) "))
      (p "The capability graph IS the lattice. Delegation flows down. Authority cannot flow up."))
    (subsection
      "Confidentiality"
      (p "Information flows only through capabilities:")
      (code "∀ read(P,O): P ∈ holders(capread(O))\n∀ write(P,O): P ∈ holders(capwrite(O))\n∀ delegate(P₁,P₂,C): C ⊆ capabilities(P₁)")
      (p "A principal without read capability cannot observe content. A principal without write capability cannot exfiltrate via storage. Delegation cannot grant what you don't hold."))
    (subsection
      "Integrity"
      (p "Modification flows only through capabilities:")
      (code "∀ modify(P,O): P ∈ holders(capwrite(O))\n∀ delegate(P₁,P₂,C'): integrity(C') ≤ integrity(C)\n∀ capability C: provenance(C) ⊆ audittrail")
      (p "Objects cannot be corrupted without write capability. Delegated capabilities cannot exceed held capabilities. All grants are traceable."))
    (subsection
      "Confinement"
      (p "The capability discipline eliminates ambient authority:")
      (code "∀ access(P,O): ∃ C ∈ capabilities(P): authorizes(C,O)\n∀ C: unforgeable(C)\n∀ acquire(P,C): ∃ P': delegate(P',P,C) ∨ create(P,O)")
      (p "No access without explicit capability. Capabilities cannot be manufactured. The only paths: receive via delegation, or create the object."))
    (subsection
      "Wormhole Enforcement"
      (p "Wormholes (Memo-041) are channel boundaries. Information flow is enforced at every crossing:")
      (code scheme "(wormhole-flow-guard wormhole operation object)\n  ;; Checks:\n  ;; 1. wormhole has capabilities (no ambient authority)\n  ;; 2. operation permitted by held capabilities\n  ;; 3. audit entry created")
      (table
        (header "Operation " "Required Capability " "Violation Type ")
        (row "read, stat, readdir " "read " "confidentiality ")
        (row "write, create, chmod " "write " "integrity ")
        (row "delete, unlink " "delete " "integrity ")
        (row "delegate " "delegate " "amplification "))
      (p "Denied operations raise typed errors: - no-ambient-authority — wormhole has no capabilities - read-denied — missing read capability - write-denied — missing write capability - capability-amplification — delegation exceeds held"))
    (subsection
      "The Lattice"
      (p "Capabilities form a partial order. The lattice:")
      (code "        full\n          │\n    ┌─────┼─────┐\n    │     │     │\n  admin synch read-write\n    │     │     │\n    └─────┼─────┘\n          │\n      read-only\n          │\n        none")
      (p "Delegation can only move DOWN the lattice. This is attenuation. You cannot delegate admin if you hold read-only. You cannot grant write if you hold read.")
      (p "The math is sound. We just speak it in capabilities.")))
  (section
    "Secure Erasure"
    (p "When sensitive data must be destroyed, it must be destroyed completely.")
    (subsection
      "Erasure Requirements"
      (table
        (header "What " "How " "Verification ")
        (row "Object content " "Overwrite with random, then zeros " "Read-back verify ")
        (row "Memory buffers " "Secure memset, compiler barrier " "Not optimized away ")
        (row "Key material " "Zeroize immediately after use " "Audit trail entry ")
        (row "Audit entries " "Preserve hash chain, redact content " "Chain integrity ")
        (row "Capability certs " "Revoke, then destroy " "Revocation published ")))
    (subsection
      "Erasure Guarantees"
      (code "E1. Zeroization is atomic\n    erase(o) → ¬recoverable(o)\n\nE2. Memory clearing defeats inspection\n    clear(buffer) → ∀ address ∈ buffer: read(address) = 0\n\nE3. Key destruction is immediate\n    destroy(key) → ¬usable(key) ∧ audit(destroyed, key)\n\nE4. Revocation propagates\n    revoke(cert) → ∀ delegate(cert, c'): revoke(c')"))
    (subsection
      "Implementation"
      (code scheme ";; Secure memory clearing (defeats compiler optimization)\n(define (secure-clear! buffer)\n  \"Overwrite buffer with zeros, verify\"\n  (let ((len (blob-size buffer)))\n    ;; Write zeros\n    (do ((i 0 (+ i 1)))\n        ((>= i len))\n      (blob-set! buffer i 0))\n    ;; Memory barrier (implementation-specific)\n    ;; Verify\n    (do ((i 0 (+ i 1)))\n        ((>= i len) #t)\n      (unless (zero? (blob-ref buffer i))\n        (error 'secure-clear-failed)))))\n\n;; Key zeroization\n(define (key-destroy! key)\n  \"Zeroize key material, audit\"\n  (let ((material (key-material key)))\n    (secure-clear! material)\n    (audit-append actor: (current-principal)\n                  action: 'key-destroyed\n                  target: (key-id key))\n    'destroyed))\n\n;; Object secure deletion\n(define (object-erase! hash)\n  \"Securely erase object content\"\n  (let ((path (vault-object-path hash)))\n    ;; Overwrite with random\n    (call-with-output-file path\n      (lambda (port)\n        (write-blob port (random-bytes (file-size path)))))\n    ;; Overwrite with zeros\n    (call-with-output-file path\n      (lambda (port)\n        (write-blob port (make-blob (file-size path) 0))))\n    ;; Delete\n    (delete-file path)\n    ;; Audit\n    (audit-append actor: (current-principal)\n                  action: 'object-erased\n                  target: hash)\n    'erased))"))
    (subsection
      "What Cannot Be Erased"
      (p "Some things must persist:")
      (table
        (header "Thing " "Why ")
        (row "Audit chain structure " "Hash links must verify ")
        (row "Revocation records " "Must prove capability invalid ")
        (row "Content hashes " "May exist in other chains "))
      (p "Redaction, not deletion: the fact that something existed remains, but the content is gone."))
    (subsection
      "SSD/Flash Considerations"
      (p "Modern storage complicates secure erasure:")
      (list
        (item "Wear leveling moves data without notification")
        (item "Trim/discard doesn't guarantee overwrite")
        (item "Encryption is the only reliable approach"))
      (p "Our answer: Encrypt at rest (Memo-030). Erasing the key erases the data.")
      (code scheme ";; With encryption at rest, key destruction = data destruction\n(define (secure-erase-encrypted hash)\n  \"For encrypted objects: destroy decryption key\"\n  (let ((dek (object-data-encryption-key hash)))\n    (key-destroy! dek)\n    ;; The ciphertext remains but is now meaningless\n    'erased-via-key-destruction))")))
  (section
    "The Trusted Core"
    (p "What must work correctly for security to hold:")
    (table
      (header "Component " "What It Does " "What We Trust ")
      (row "Ed25519 " "Signatures " "libsodium, math ")
      (row "SHA-512 " "Object identity " "libsodium, math ")
      (row "Capability verifier " "Chain validation " "Our code ")
      (row "Vault storage " "Object integrity " "Local filesystem ")
      (row "Audit chain " "What happened " "Hash chain, signatures ")
      (row "Soup " "Object enumeration " "Vault, audit "))
    (p "The core is small. Objects are dumb content. Policy lives in certificates. Verification is stateless computation.")
    (subsection
      "Authoritative Counts"
      (p "Object counts MUST come from the TCB. The soup is the authoritative source for object enumeration - it walks the vault and audit trail. Counts displayed outside the TCB (prompts, status displays, dashboards) are advisory only and could be stale or spoofed.")
      (p "If you need to know how many objects exist, ask the soup. Don't cache counts outside the TCB.")))
  (section
    "Covert Channels"
    (p "This is where we get serious.")
    (p "A covert channel is information flow that violates policy - a way to leak data that bypasses the capability model. They exist in every system. We analyze ours.")
    (subsection
      "Storage Channels"
      (table
        (header "Channel " "How It Works " "Bandwidth " "Mitigation ")
        (row "Object existence " "Create/don't create object as 1/0 " "~1 bit/op " "Bloom filter noise ")
        (row "Object size " "Encode in padding " "~10 bits/obj " "Size quantization ")
        (row "Object count " "Number of objects in namespace " "~4 bits/ns " "Rate limiting ")))
    (subsection
      "Timing Channels"
      (table
        (header "Channel " "How It Works " "Bandwidth " "Mitigation ")
        (row "Verification time " "Slow/fast response as 1/0 " "~1 bit/100ms " "Constant-time ops ")
        (row "Network latency " "Delay patterns " "~10 bits/sec " "Batching, Tor ")
        (row "Audit write time " "When entries appear " "~1 bit/sec " "Async, batched ")))
    (subsection
      "Federation Channels"
      (table
        (header "Channel " "How It Works " "Bandwidth " "Mitigation ")
        (row "Sync timing " "When objects replicate " "~1 bit/sync " "Random delays ")
        (row "Peer selection " "Which realms to contact " "~4 bits/conn " "Randomized peers ")
        (row "Gossip patterns " "Propagation paths " "~2 bits/round " "Epidemic flooding ")))
    (subsection
      "Analysis"
      (p "Scenario: Alice has SECRET access. Bob has UNCLASSIFIED. Alice wants to leak to Bob.")
      (p "Via storage: Alice creates/deletes objects Bob can see. Each operation signals one bit. Rate: maybe 1 bit/second with careful timing.")
      (p "Via timing: Alice influences verification time of requests Bob makes. Bob measures. Rate: maybe 0.1 bit/second, noisy.")
      (p "Via federation: Alice causes sync events Bob can observe. Rate: depends on federation config, maybe 0.01 bit/second.")
      (p "Assessment: Total covert bandwidth: ~1-2 bits/second under ideal conditions. Not enough for bulk data. Enough for short signals. Acceptable residual risk for our threat model."))
    (subsection
      "Mitigation Principles"
      (code "1. Add noise where practical (bloom filters, random delays)\n2. Quantize where observable (object sizes, batch windows)\n3. Rate limit where controllable (operations per time)\n4. Accept what remains (document it, move on)")))
  (section
    "Audit"
    (p "Everything important gets logged.")
    (code scheme "(audit-entry\n  (sequence 12345)\n  (timestamp 1736300000)\n  (lamport 67890)\n  (type capability-exercise)\n  (actor \"ed25519:subject...\")\n  (action (read \"sha512:object...\"))\n  (capability \"sha512:cert...\")\n  (previous \"sha512:prev-entry...\")\n  (signature \"ed25519:auditor...\"))")
    (p "Properties: - Hash-chained: tamper-evident - Signed: non-repudiable - Monotonic: gaps detected - Distributed: witnesses replicate")
    (p "What gets logged: - Capability creation - Capability exercise (access) - Capability revocation - Access denials - Object creation - Realm events (role changes, federation)"))
  (section
    "Session Observability"
    (p "The portal module manages session lifecycle: crossing into and out of cyberspace. Every session provides observability through the banner, session statistics, and the goodbye summary.")
    (subsection
      "The Banner"
      (p "At session start, the banner attests system state. Every line is meaningful:")
      (code "Cyberspace Scheme v0.9.17 (2026-01-11)\n  Om · Darwin-arm64 · 16 cores, 128GB, Apple M4\n  IPv4: 192.168.0.105\n  IPv6: fd0f:a8ba:61a3:42ce:1856:f4d9:e25:998e\n  37K loc, 21 modules, 0 rfcs, 1K tcb (1:32)\n  vault: .vault (1 releases, 23 audits)\n  realm: om (ecefca39...)\n  entropy: /dev/urandom (sysrandom)\n  FIPS: passed")
      (table
        (header "Line " "Security Purpose ")
        (row "Version, date " "Identifies build, detects stale installations ")
        (row "Hostname, arch " "Confirms you're on the expected machine ")
        (row "IPv4/IPv6 " "Network identity for federation, peer verification ")
        (row "loc, modules, tcb " "Codebase size, attack surface visibility ")
        (row "vault " "Confirms vault exists, shows releases and audit count ")
        (row "realm " "Your cryptographic identity (abbreviated principal) ")
        (row "entropy " "Entropy source attestation for key generation ")
        (row "FIPS " "Cryptographic self-test status (must pass) "))
      (p "The FIPS line is critical. Before trusting any cryptographic operation, the system runs Known-Answer Tests (KATs) against SHA-256, SHA-512, Ed25519, and the RNG. If any test fails, the system displays FAILED and should not be trusted for security operations."))
    (subsection
      "Realm Naming"
      (p "Realms can have human-readable names, analogous to hostnames for IP addresses:")
      (code scheme "(set-realm-name! \"om\")     ; Name this realm\n(realm-name)               ; => \"om\"")
      (p "The name appears in the banner: `realm: om (ecefca39...)` The abbreviated principal (first 8 hex chars) provides cryptographic identity while the name provides human recognition. Names are stored in `.vault/realm-name`."))
    (subsection
      "Session Statistics"
      (p "Every operation is counted. Statistics track session activity for monitoring and forensics:")
      (table
        (header "Category " "Stats " "Purpose ")
        (row "Vault I/O " "unlocks, reads, writes, deletes, queries " "Storage activity profile ")
        (row "Crypto ops " "hashes, signs, verifies, encrypts, decrypts " "Cryptographic workload ")
        (row "Seal ops " "commits, seals, syncs " "Version control activity ")
        (row "Federation " "peers-discovered, gossip-exchanges, votes " "Network participation ")
        (row "Network I/O " "bytes-in, bytes-out, packets-ipv4/ipv6 " "Traffic volume ")
        (row "Errors " "verify-fails, auth-fails, timeouts " "Security-relevant failures "))
      (p "Statistics are initialized at session start and accumulated during operation. The primitives live in the `os` module (level 0) so all modules can instrument themselves without circular dependencies.")
      (code scheme "(session-stat! 'unlocks)           ; Increment unlock counter\n(session-stat! 'bytes-in 1024)     ; Add 1024 to bytes-in\n(session-stat 'reads)              ; Get current read count"))
    (subsection
      "The Portal"
      (p "Entry and exit are symmetric. The goodbye message mirrors the banner's attestation style:")
      (code "Cyberspace frozen at 2026-01-11 20:32 on om.\n  Session: 0s · 5000 weave · 1 unlock · 3 reads · 2 queries")
      (p "The session summary shows:")
      (list
        (item "Duration (human-readable: 0s, 5m, 2h 30m, 1d 4h)")
        (item "Weave - crypto benchmark from boot")
        (item "Notable operations (non-zero counts)")
        (item "Errors if any occurred (verify-fails, auth-fails, timeouts)"))
      (p "The hostname in the goodbye message confirms which realm you're leaving - important when operating multiple realms via SSH."))
    (subsection
      "Monitoring Philosophy"
      (p "\"You can always assert() it away.\" Statistics are conditional instrumentation:")
      (list
        (item "Always present in source - documents what's measurable")
        (item "Minimal overhead - hash table increment")
        (item "No persistence - session-scoped, vanishes on exit")
        (item "Extensible - add new stats by instrumenting operations"))
      (p "The pattern comes from IKE clustering code: conditional asserts for QA builds, compiled out for production. Here we keep the counters but the cost is negligible.")))
  (section
    "Kernel Assertions"
    (p "The kernel enforces security through typed assertions. Every assertion is cataloged automatically by `extract-assertions.sh` as part of the RFC generation pipeline. The catalog is regenerated on every build - if you add an assertion, it appears in the documentation.")
    (subsection
      "Assertion Categories"
      (table
        (header "Category " "Purpose " "Example ")
        (row "instrumentation " "Session statistics " "(session-stat! 'unlocks) ")
        (row "security-error " "Access control failures " "(error 'capability-amplification) ")
        (row "precondition " "State guards " "(unless (attested?) ...) "))
      (p "The catalog provides traceability: every security-relevant check in the codebase is enumerated with file and line number."))
    (subsection
      "Security Errors"
      (p "Typed error symbols for access control failures:")
      (table
        (header "Error " "Meaning ")
        (row "capability-amplification " "Attempted to delegate more rights than held ")
        (row "confidentiality-violation " "Read without read capability ")
        (row "integrity-violation " "Write without write capability ")
        (row "no-ambient-authority " "Wormhole has no capabilities ")
        (row "read-denied " "Principal lacks read capability ")
        (row "write-denied " "Principal lacks write capability ")
        (row "delete-denied " "Principal lacks delete capability ")
        (row "delegate-denied " "Principal lacks delegate capability ")
        (row "secure-clear-failed " "Zeroization verification failed "))
      (p "These errors are not generic - each has specific semantics for audit and forensics."))
    (subsection
      "Precondition Guards"
      (p "State assertions that must hold before operations proceed:")
      (code scheme "(unless (attested?)\n  (error \"Must attest before signing\"))\n\n(unless (keystore-exists?)\n  (error \"No keystore found. Use keystore-create first.\"))\n\n(unless (quiescent? memo)\n  (error \"Chaotic memos cannot be published\"))")
      (p "Guards enforce the state machine: chaotic vs quiescent, attested vs unattested, locked vs unlocked."))
    (subsection
      "The Scheme Way"
      (p "Conditional assertions via macros with compile-time flags:")
      (code scheme ";; Config constant\n(define-constant +instrumented+ #t)  ; #f for production\n\n;; Zero-cost when disabled\n(define-syntax stat!\n  (syntax-rules ()\n    ((_ key)\n     (when +instrumented+ (session-stat! key)))))")
      (p "With `+instrumented+` false, CHICKEN's optimizer eliminates the dead branch entirely. This is the Scheme equivalent of BLISS `%IF DEBUG %THEN %assert(...) %FI`."))
    (subsection
      "Catalog Generation"
      (p "The assertion catalog is generated automatically:")
      (code "$ ./docs/notes/extract-assertions.sh\n  -> docs/notes/assertion-catalog.scm\n     18 instrumentation, 10 security errors, 12 guards (40 total)")
      (p "The catalog is a first-class S-expression that can be loaded and queried:")
      (code scheme "(load \"assertion-catalog.scm\")\n(assertion-summary)\n;; => ((instrumentation-points . 18)\n;;     (security-errors . 10)\n;;     (precondition-guards . 12)\n;;     (total . 40))")
      (p "Adding assertions to code automatically updates the documentation on next regeneration.")))
  (section
    "Trusted Path"
    (p "When it matters, talk directly to the core.")
    (code "┌──────────────────────────────────────┐\n│           HUMAN OPERATOR              │\n└─────────────────┬────────────────────┘\n                  │ Local terminal, no network\n┌─────────────────▼────────────────────┐\n│          CYBERSPACE REPL              │\n│    ╔═════════════════════════════╗   │\n│    ║  TRUSTED PATH ACTIVE        ║   │\n│    ╚═════════════════════════════╝   │\n└─────────────────┬────────────────────┘\n                  │\n┌─────────────────▼────────────────────┐\n│           TRUSTED CORE                │\n└──────────────────────────────────────┘")
    (p "Operations requiring trusted path: - (ed25519-keypair) - key generation - (node-role 'coordinator) - role assignment - (seal-release \"1.0.0\") - signing releases - Key ceremony (Memo-022)"))
  (section
    "Threats"
    (subsection
      "What We Handle"
      (table
        (header "Threat " "Defense ")
        (row "Unauthorized access " "No capability = no access ")
        (row "Capability forgery " "Ed25519 signatures ")
        (row "Replay attacks " "Timestamps, nonces, Lamport clocks ")
        (row "Stale capabilities " "Expiration, revocation ")
        (row "Delegation abuse " "Attenuation, propagation flags ")
        (row "Content tampering " "SHA-512 content addressing ")
        (row "Origin spoofing " "Object signatures ")
        (row "Audit tampering " "Hash chain, distribution ")))
    (subsection
      "What We Don't Handle"
      (table
        (header "Threat " "Why ")
        (row "Compromised signing key " "Fundamental limit. Mitigate: threshold, rotation. ")
        (row "Endpoint compromise " "Your realm, your problem. ")
        (row "Physical access " "Out of scope for software. ")
        (row "Covert channels > 1 bit/sec " "Residual risk, documented above. ")
        (row "Availability attacks " "Focus on integrity/confidentiality. ")
        (row "Quantum computing " "Ed25519 vulnerable. Migration path planned. ")
        (row "Coercion " "Math doesn't help if you're forced to sign. "))))
  (section
    "The Invariants"
    (p "These must always hold:")
    (code "I1. No access without valid capability\n    access(s,o,r) → ∃c: valid_chain(s,o,r,c)\n\nI2. Delegation cannot amplify\n    delegated(c₂,c₁) → rights(c₂) ⊆ rights(c₁)\n\nI3. Object identity is content hash\n    id(o) = sha512(content(o))\n\nI4. Audit is ordered\n    sequence(e₁) < sequence(e₂) → time(e₁) ≤ time(e₂)\n\nI5. Revocation is permanent\n    revoked(c,t) → ∀t' > t: ¬valid(c,t')\n\nI6. No ambient authority\n    ¬∃c: grants(c,,)"))
  (section
    "References"
    (p "1. Ellison, C. et al., SPKI Certificate Theory, RFC 2693, 1999 2. Dennis, J. & Van Horn, E., Programming Semantics for Multiprogrammed Computations, 1966 3. Miller, M., Robust Composition, 2006 4. Lampson, B., A Note on the Confinement Problem, 1973 5. DoD 5200.28-STD (Orange Book), 1985 - for the covert channel lens 6. Bell, D.E. & LaPadula, L.J., Secure Computer Systems: Mathematical Foundations, 1973 - confidentiality model 7. Biba, K.J., Integrity Considerations for Secure Computer Systems, 1977 - integrity model"))
  (section
    "Changelog"
    (list
      (item "2026-01-08")
      (item "Initial draft"))))

