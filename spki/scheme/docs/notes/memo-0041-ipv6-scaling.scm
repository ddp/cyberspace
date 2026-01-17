;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 41)
  (title "Scaling Architecture for IPv6")
  (section
    "Abstract"
    (p "This Memo defines the architectural changes required to scale Cyberspace from a git-backed prototype to a native distributed system capable of operating at IPv6 scale (billions of realms, exabytes of content). Git becomes an export format; the vault becomes the source of truth."))
  (section
    "Terminology"
    (p "Realm: A node's place in cyberspace - its vault, principal, capabilities, and objects. Each realm is sovereign: local-first, controlled by its operator. Realms federate by choice, sharing objects according to trust relationships.")
    (p "Vault: The local content-addressed object store (.vault/). The vault IS the realm's storage - all objects, catalogs, audit trails, and configuration live here.")
    (p "Principal: A node's cryptographic identity (Ed25519 public key). The principal identifies the realm to peers and signs its objects.")
    (p "At IPv6 scale, cyberspace consists of billions of realms, each occupying its own address space, each sovereign, each choosing what to share and with whom."))
  (section
    "Motivation"
    (p "Git served as an excellent prototype substrate: - Content-addressed objects (proof of concept) - Merkle tree integrity (validates the model) - Ubiquitous tooling (bootstrap adoption)")
    (p "Git cannot scale to IPv6: - Full history on every clone - Repository as replication unit (too coarse) - SHA-1 (cryptographically broken) - No native federation or discovery - Merge semantics are wrong model")
    (p "The internet has 2^128 addresses. Cyberspace should use them."))
  (section
    "Design Principles"
    (code "1. Objects, not repositories\n2. Pull, not push\n3. Lazy, not eager\n4. Local-first, federate-second\n5. Trust math, not infrastructure"))
  (section
    "Content-Addressed Object Store"
    (subsection
      "Storage Model"
      (code ".vault/\n  objects/\n    sha512-a1b2c3.../    # First 8 chars as directory\n      a1b2c3d4e5f6...    # Full hash as filename (S-expression)\n  catalog/\n    manifest.sexp        # Vault catalog object\n    bloom.sexp           # Bloom filter object\n    indices/             # Secondary index objects\n      by-signer.sexp\n      by-type.sexp\n  chunks/\n    sha512-xxxx/         # Chunked large objects\n  audit/\n    head.sexp            # Current audit chain head\n    chain/               # Audit entries (hash-addressed)"))
    (subsection
      "Object Format"
      (code scheme "(cyberspace-object\n  (version 1)\n  (type blob|tree|manifest|cert|audit)\n  (size 1048576)\n  (compression zstd|none)\n  (hash \"sha512:a1b2c3...\")\n  (chunks (\"sha512:...\" \"sha512:...\" ...))  ; If chunked\n  (signature \"ed25519:...\")\n  (timestamp 1736300000))"))
    (subsection
      "Chunking Strategy"
      (p "Large objects split at content-defined boundaries (Rabin fingerprinting):")
      (code "Target chunk: 64 KB (Starlink-optimized)\nMin chunk:    16 KB\nMax chunk:   256 KB\n\nBenefits:\n  - Deduplication across objects\n  - Partial sync (fetch only missing chunks)\n  - Resumable transfers\n  - Efficient diff"))
    (subsection
      "Hash Function"
      (code "SHA-512 everywhere.\n\nNot SHA-256: We have the bits, use them.\nNot SHA-1: Broken.\nNot BLAKE3: Less analyzed, marginal speed gain irrelevant at network latency.\n\nSHA-512 is:\n  - FIPS certified (GovCloud path)\n  - 50 years of cryptanalysis\n  - Hardware accelerated\n  - Already in use (audit trail, signatures)")))
  (section
    "Catalog and Query"
    (p "The soup IS the catalog. No SQL. Objects are S-expressions, queries are pattern matching.")
    (subsection
      "The Soup Query Model"
      (code scheme ";; Find objects by pattern\n(soup-query\n  '(cyberspace-object\n    (type blob)\n    (signer \"ed25519:alice...\")\n    ?rest))                        ; Match any object signed by Alice\n\n;; Find by hash (direct lookup)\n(soup-fetch \"sha512:a1b2c3...\")    ; O(1) content-addressed\n\n;; Find by type\n(soup-query '(cyberspace-object (type cert) ?rest))\n\n;; Find by time range\n(soup-query-range\n  type: 'audit\n  from: 1736000000\n  to:   1736100000)\n\n;; Cursor-based iteration for large result sets\n(soup-cursor\n  '(cyberspace-object (type ?) ?rest)\n  batch: 100)"))
    (subsection
      "Object Catalog"
      (p "The catalog is itself an object in the soup - a manifest of what the vault contains:")
      (code scheme "(vault-catalog\n  (version 1)\n  (realm \"ed25519:principal...\")\n  (object-count 150000)\n  (types\n    (blob 100000)\n    (tree 30000)\n    (cert 15000)\n    (audit 5000))\n  (bloom-filter #${...})           ; Fast existence check\n  (updated 1736400000))"))
    (subsection
      "Bloom Filter"
      (p "Fast existence check before network round-trip:")
      (code scheme "(define (soup-maybe-contains? hash)\n  \"Check bloom filter - false means definitely not, true means maybe\"\n  (let ((catalog (soup-fetch-catalog)))\n    (bloom-test (catalog-bloom catalog) hash)))\n\n;; Bloom parameters\n(bloom-filter\n  (capacity 10000000)              ; 10M objects\n  (false-positive 0.001)           ; 0.1% FP rate\n  (bits #${...}))"))
    (subsection
      "Audit Trail"
      (p "The audit trail is a hash-chain of objects in the soup:")
      (code scheme "(audit-entry\n  (sequence 12345)\n  (timestamp 1736300000)\n  (lamport 67890)\n  (actor \"ed25519:subject...\")\n  (action (read \"sha512:object...\"))\n  (previous \"sha512:prev-entry...\")  ; Chain link\n  (signature \"ed25519:auditor...\"))\n\n;; Query audit by walking the chain\n(define (audit-query actor from-seq)\n  \"Walk audit chain, filter by actor\"\n  (soup-chain-walk\n    start: (audit-head)\n    filter: (lambda (entry)\n              (equal? (entry-actor entry) actor))\n    from: from-seq))"))
    (subsection
      "Secondary Indices"
      (p "For queries that can't use content-addressing, the soup maintains lightweight indices as objects:")
      (code scheme "(soup-index\n  (name \"by-signer\")\n  (key-type principal)\n  (entries\n    ((\"ed25519:alice...\" (\"sha512:obj1\" \"sha512:obj2\" ...))\n     (\"ed25519:bob...\" (\"sha512:obj3\" \"sha512:obj4\" ...)))))\n\n(soup-index\n  (name \"by-type\")\n  (key-type symbol)\n  (entries\n    ((blob (\"sha512:...\" \"sha512:...\" ...))\n     (cert (\"sha512:...\" \"sha512:...\" ...))\n     (audit (\"sha512:...\" \"sha512:...\" ...)))))")
      (p "Indices are rebuilt on demand, not authoritative - the soup is truth.")))
  (section
    "Discovery and Routing"
    (subsection
      "Realm Identity"
      (p "Each realm has a principal (Ed25519 public key). This IS its identity:")
      (code scheme "(realm-identity\n  (principal \"ed25519:a1b2c3...\")\n  (addresses                          ; Where to reach this realm\n    (ipv6 \"2001:db8::1\" port: 7777)\n    (ipv4 \"192.0.2.1\" port: 7777)     ; Legacy\n    (onion \"xxxx.onion\" port: 7777))  ; Tor\n  (role witness)\n  (capabilities (storage-gb 1000) (bandwidth-mbps 100))\n  (signature \"ed25519:...\"))"))
    (subsection
      "Peer Discovery"
      (p "Bootstrap:")
      (code scheme "(bootstrap-peers\n  (\"ed25519:official1...\" \"bootstrap.cyberspace.org\")\n  (\"ed25519:official2...\" \"bootstrap2.cyberspace.org\"))")
      (p "Gossip Protocol:")
      (code "1. Realm joins, contacts bootstrap peer\n2. Receives partial peer list (random subset)\n3. Contacts those peers, exchanges lists\n4. Epidemic spread: O(log n) rounds to reach all realms\n5. Periodic refresh (every 5 min on Starlink-friendly schedule)")
      (p "Distributed Hash Table (Future):")
      (code "Kademlia-style routing:\n  - XOR distance metric on principal hashes\n  - O(log n) lookups\n  - Realms responsible for nearby hash ranges\n  - Natural load balancing"))
    (subsection
      "Content Discovery"
      (code scheme ";; \"Who has this hash?\"\n(content-locate \"sha512:a1b2c3...\")\n\n;; Returns list of peers claiming to have it:\n((\"ed25519:peer1...\" (latency-ms 50) (role full))\n (\"ed25519:peer2...\" (latency-ms 200) (role witness))\n (\"ed25519:peer3...\" (latency-ms 600) (role archiver)))\n\n;; Fetch from best candidate\n(content-fetch \"sha512:a1b2c3...\" from: \"ed25519:peer1...\")")))
  (section
    "Transport Protocol"
    (subsection
      "End-to-End Encryption"
      (p "All network traffic is encrypted. The OS and network are not trusted.")
      (code scheme "(cyberspace-message\n  (version 1)\n  (from \"ed25519:sender...\")\n  (to \"ed25519:recipient...\")        ; Or broadcast key\n  (ephemeral \"x25519:...\")           ; One-time key (PFS)\n  (nonce #${24-bytes})               ; Random nonce\n  (ciphertext #${...})               ; NaCl box: X25519 + XSalsa20-Poly1305\n  (signature \"ed25519:...\"))         ; Sign the ciphertext")
      (p "Encryption scheme: NaCl crypto_box (libsodium) - Key agreement: X25519 (Curve25519 ECDH) - Cipher: XSalsa20-Poly1305 - Perfect forward secrecy: ephemeral keys per message")
      (p "Decrypted payload:")
      (code scheme "(plaintext-payload\n  (type request|response|announce|gossip)\n  (nonce 12345678)                   ; Replay protection\n  (timestamp 1736300000)\n  (body ...))")
      (p "Broadcast messages use a shared group key or are signed-only (announcements of public objects)."))
    (subsection
      "Wire Format (Encrypted)"
      (code scheme ";; Sender encrypts\n(define (seal-message payload recipient-pubkey sender-keypair)\n  (let ((ephemeral (x25519-keypair))\n         (shared (x25519-shared (ephemeral-secret ephemeral) recipient-pubkey))\n         (nonce (random-bytes 24))\n         (ciphertext (crypto-box payload nonce shared)))\n    `(cyberspace-message\n      (version 1)\n      (from ,(keypair-public sender-keypair))\n      (to ,recipient-pubkey)\n      (ephemeral ,(ephemeral-public ephemeral))\n      (nonce ,nonce)\n      (ciphertext ,ciphertext)\n      (signature ,(sign-message ciphertext sender-keypair)))))\n\n;; Recipient decrypts\n(define (open-message msg recipient-keypair)\n  (let ((shared (x25519-shared (keypair-secret recipient-keypair)\n                                (message-ephemeral msg)))\n         (plaintext (crypto-box-open (message-ciphertext msg)\n                                     (message-nonce msg)\n                                     shared)))\n    (and (verify-signature msg (message-from msg))\n         plaintext)))"))
    (subsection
      "Request Types"
      (code scheme ";; Existence check\n(have? (\"sha512:...\" \"sha512:...\" ...))\n;; Response: (have (\"sha512:...\" \"sha512:...\") missing (\"sha512:...\"))\n\n;; Fetch object\n(fetch \"sha512:...\")\n;; Response: (object ...)\n\n;; Fetch chunk range\n(fetch-chunks \"sha512:...\" start: 5 count: 10)\n;; Response: (chunks ...)\n\n;; Peer list exchange\n(peers? limit: 50)\n;; Response: (peers ...)\n\n;; Announce new content\n(announce (\"sha512:...\" \"sha512:...\"))\n;; Response: (ack)"))
    (subsection
      "Transport Bindings"
      (code "Native:     UDP/IPv6, port 7777 (primary)\nFallback:   TCP/IPv6, port 7777 (firewalls)\nLegacy:     TCP/IPv4, port 7777 (transition)\nStealth:    Tor onion service (censorship resistance)\nOffline:    USB drive, file copy (sneakernet)\nExport:     Git bundle (GitHub compatibility)"))
    (subsection
      "Starlink Optimization"
      (code scheme "(transport-config\n  (mode satellite)\n  (batch-window-ms 500)        ; Aggregate small messages\n  (chunk-size-kb 64)           ; Match MTU\n  (retry-strategy exponential)\n  (max-in-flight 10)           ; Parallelism\n  (keepalive-sec 300))         ; 5 min, not 30 sec")))
  (section
    "Synchronization Protocol"
    (subsection
      "Lazy Sync (Default)"
      (code "Node A                              Node B\n   |                                   |\n   |----(have? [h1, h2, h3])---------->|\n   |<---(have [h1, h3] missing [h2])---|\n   |----(fetch h2)-------------------->|\n   |<---(object h2 ...)----------------|\n   |                                   |\n\nNo coordination. No locks. No leader."))
    (subsection
      "Crdt-Style Convergence"
      (p "Objects are immutable and content-addressed. No conflicts possible at object level.")
      (p "Manifests (collections of objects) use: - Lamport timestamps for ordering - Last-writer-wins with principal tiebreaker - Or: union (add-only sets)")
      (code scheme "(manifest\n  (name \"library\")\n  (version (lamport 42) (principal \"ed25519:...\"))\n  (entries\n    (\"memo-001\" \"sha512:...\")\n    (\"memo-002\" \"sha512:...\")\n    ...))"))
    (subsection
      "Merkle Sync"
      (p "Efficient diff for large manifests:")
      (code "         root\n        /    \\\n      h1      h2\n     /  \\    /  \\\n    a    b  c    d\n\nExchange root hash.\nIf different, recurse on children.\nO(log n) round trips to find diff.")))
  (section
    "Federation at Scale"
    (subsection
      "Cluster Topology"
      (code "                    ┌─────────────────────────────────────┐\n                    │         COORDINATOR CLUSTER         │\n                    │  (3-7 nodes, Byzantine consensus)   │\n                    └────────────────┬────────────────────┘\n                                     │\n          ┌──────────────────────────┼──────────────────────────┐\n          │                          │                          │\n    ┌─────▼─────┐             ┌──────▼─────┐             ┌──────▼─────┐\n    │   FULL    │             │   FULL     │             │    FULL    │\n    │  NODES    │             │   NODES    │             │   NODES    │\n    └─────┬─────┘             └─────┬──────┘             └─────┬──────┘\n          │                         │                          │\n    ┌─────▼─────┐             ┌─────▼──────┐             ┌─────▼──────┐\n    │ WITNESSES │             │ WITNESSES  │             │ WITNESSES  │\n    │ ARCHIVERS │             │ ARCHIVERS  │             │ ARCHIVERS  │\n    │   EDGES   │             │   EDGES    │             │   EDGES    │\n    └───────────┘             └────────────┘             └────────────┘\n\nCoordinators: Rare, high-capability realms, run consensus\nFull: Common realms, replicate everything, serve content\nWitnesses: Abundant realms, verify and store, passive sync\nArchivers: Cold storage realms, batch sync\nEdges: Read-only realms, intermittent, mobile"))
    (subsection
      "Partition Tolerance"
      (code "Network splits → clusters diverge → clusters converge on reconnect\n\nNo data loss (content-addressed)\nNo conflicts (immutable objects)\nAudit trails merge (union of entries, Lamport ordering)\nManifests resolve (LWW or union based on type)")))
  (section
    "Git as Export Format"
    (subsection
      "The Transition"
      (code "Phase 1 (Now):      Git is source of truth, vault is cache\nPhase 2 (Next):     Vault is source of truth, git is export\nPhase 3 (Future):   Git optional, purely for GitHub presence"))
    (subsection
      "Export Process"
      (code scheme "(git-export\n  from: \".vault\"\n  to: \"/tmp/cyberspace-export\"\n  format: 'git-repo)\n\n;; Creates standard git repo from vault contents\n;; For publishing to GitHub, GitLab, etc."))
    (subsection
      "Import Process"
      (code scheme "(git-import\n  from: \"https://github.com/ddp/cyberspace.git\"\n  to: \".vault\")\n\n;; Extracts objects from git, stores in vault\n;; Discards git history, keeps content")))
  (section
    "Security at Scale"
    (subsection
      "Sybil Resistance"
      (p "Problem: Attacker creates many fake nodes to dominate network.")
      (p "Mitigations:")
      (list
        (item "Stake-weighted voting (not proof-of-work, just reputation)")
        (item "Web of trust - new nodes introduced by existing trusted nodes")
        (item "Rate limiting - bound resources per principal")
        (item "Coordinator consensus - Byzantine-resistant core")))
    (subsection
      "Eclipse Attack Resistance"
      (p "Problem: Attacker isolates a node by controlling all its peers.")
      (p "Mitigations:")
      (list
        (item "Diverse bootstrap - multiple independent entry points")
        (item "Random peer selection - can't predict who you'll connect to")
        (item "Peer rotation - periodically reconnect to new peers")
        (item "Out-of-band verification - publish peer lists via DNS, blockchain, etc.")))
    (subsection
      "Denial of Service"
      (p "Problem: Attacker floods network with junk.")
      (p "Mitigations:")
      (list
        (item "Proof of work on announcements (small, CPU cost)")
        (item "Rate limiting per principal")
        (item "Reputation scoring - misbehaving peers deprioritized")
        (item "Content validation - reject malformed objects immediately"))))
  (section
    "Implementation Phases"
    (subsection
      "Phase 1: Native Object Store"
      (list
        (item "Implement .vault/objects/ storage")
        (item "Soup catalog and query")
        (item "Keep git for development workflow")))
    (subsection
      "Phase 2: Local-First Sync"
      (list
        (item "Direct node-to-node protocol - have?/fetch message types")
        (item "UDP transport with TCP fallback")))
    (subsection
      "Phase 3: Discovery"
      (list
        (item "Gossip peer exchange")
        (item "Bootstrap nodes")
        (item "Bloom filters for content location")))
    (subsection
      "Phase 4: Scale Testing"
      (list
        (item "100 nodes - 1000 nodes - 10000 nodes")
        (item "Measure: latency, convergence time, bandwidth"))
      (p "Implementation proceeds from working local storage to network protocols to discovery to scale testing. Each phase validates assumptions before the next builds on them. Git deprecation comes last—the proven system remains as fallback until the native system earns trust."))
    (subsection
      "Phase 5: Git Deprecation"
      (list
        (item "Vault as source of truth")
        (item "Git export for compatibility")
        (item "Remove git dependency from core operations"))))
  (section
    "Metrics and Monitoring"
    (code scheme "(node-metrics)\n;; Returns:\n((objects-stored 150000)\n (objects-size-gb 50)\n (peers-known 500)\n (peers-connected 20)\n (sync-lag-seconds 30)\n (bandwidth-in-mbps 10)\n (bandwidth-out-mbps 5)\n (requests-per-second 100)\n (errors-per-second 0.1))"))
  (section
    "References"
    (list
      (item "Memo-010: Federation Protocol")
      (item "Memo-016: Lazy Clustering")
      (item "Memo-037: Node Roles and Capabilities")
      (item "Maymounkov, P. (2002). Kademlia: A Peer-to-peer Information System")
      (item "Rabin, M. (1981). Fingerprinting by Random Polynomials")
      (item "IPFS Whitepaper (2014)")
      (item "Shapiro, M. (2011). Conflict-Free Replicated Data Types")))
  (section
    "Changelog"
    (list
      (item "2026-01-07")
      (item "Initial draft"))))

