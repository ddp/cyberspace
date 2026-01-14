;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 10)
  (title "Federation Protocol")
  (section
    "Abstract"
    (p "This RFC specifies the Federation Protocol for the Library of Cyberspace: a peer-to-peer synchronization system enabling loose confederacies of friends to share and preserve cryptographically sealed artifacts without central authority."))
  (section
    "E Pluribus Unum"
    (p "Out of many, one.")
    (code "    ┌─────────┐         ┌─────────┐         ┌─────────┐\n    │  Alice  │◄───────►│   Bob   │◄───────►│  Carol  │\n    │  Vault  │         │  Vault  │         │  Vault  │\n    └────┬────┘         └────┬────┘         └────┬────┘\n         │                   │                   │\n         │    ┌──────────────┴──────────────┐    │\n         │    │                             │    │\n         └────►    No Central Authority    ◄────┘\n              │                             │\n              │   Just keys, seals, trust   │\n              │                             │\n              └─────────────────────────────┘"))
  (section
    "Motivation"
    (p "Centralized systems fail:")
    (list
      (item "Single point of failure: Server goes down, everyone stops")
      (item "Censorship: Authority can deny access")
      (item "Trust concentration: Must trust operator")
      (item "Survival: Company folds, data lost"))
    (p "Federation provides:")
    (p "1. Decentralized - No master server 2. Resilient - Survives node failures 3. Autonomous - Each peer controls own data 4. Cryptographic - Trust through math, not authority 5. Eventual consistency - Convergence without coordination"))
  (section
    "Federation Model"
    (subsection
      "Peer Relationships"
      (code "Peer: A vault instance with identity (SPKI principal)\n\nRelationships:\n  - Publisher:  I push releases to you\n  - Subscriber: I pull releases from you\n  - Peer:       Bidirectional sync"))
    (subsection
      "Trust Model"
      (code scheme "(federation-trust\n  (peer alice-pubkey\n    (role publisher)\n    (trust-level verified)     ; Signature verified\n    (sync-policy automatic))\n\n  (peer bob-pubkey\n    (role subscriber)\n    (trust-level known)        ; Key known, not verified\n    (sync-policy manual)))")
      (p "Trust levels: - unknown: Never seen, reject - known: Key registered, manual approval - verified: Signature chain verified via SPKI - trusted: Full automatic sync")))
  (section
    "Protocol Operations"
    (subsection
      "Peer Discovery"
      (code scheme "(federation-discover)\n;; Returns: List of known peers and their status")
      (p "Discovery mechanisms: 1. Explicit configuration: Known peer list 2. Git remotes: Extract from repository 3. Directory service: Optional, not required 4. mDNS/Bonjour: Local network discovery via cyberspace.tcp"))
    (subsection
      "mDNS Service Discovery"
      (p "Cyberspace nodes announce themselves via mDNS using the cyberspace.tcp service type:")
      (code scheme ";; Announce this node\n(announce-presence 'starlight)\n;; Registers: starlight.cyberspace.tcp.local. port 7654\n\n;; Discover peers\n(discover-peers)\n;; Scans for cyberspace.tcp services on local network")
      (p "Platform support: - macOS: dns-sd -R for registration, dns-sd -B for browsing - Linux: avahi-publish for registration, avahi-browse for browsing"))
    (subsection
      "Peer Registration"
      (code scheme "(federation-register peer-uri\n  #!key public-key trust-level)")
      (p "Registers a new peer with: - URI (git remote, HTTP endpoint, filesystem path) - Public key for verification - Initial trust level"))
    (subsection
      "Release Announcement"
      (code scheme "(federation-announce version\n  #!key peers message)")
      (p "Pushes release notification to peers: 1. Create signed announcement 2. Send to specified peers (or all) 3. Peers verify signature 4. Peers decide whether to pull"))
    (subsection
      "Release Request"
      (code scheme "(federation-request version peer\n  #!key verify-key)")
      (p "Pulls specific release from peer: 1. Request release metadata 2. Verify signature 3. Download archive 4. Verify integrity 5. Record in audit trail"))
    (subsection
      "Synchronization"
      (code scheme "(federation-sync peer\n  #!key direction verify-key)")
      (p "Bidirectional sync (from RFC-001): 1. Exchange release lists 2. Identify missing releases 3. Push/pull as configured 4. Verify all signatures 5. Update audit trails")))
  (section
    "Message Format"
    (subsection
      "Announcement Message"
      (code scheme "(federation-message\n  (type announcement)\n  (from #${alice-pubkey})\n  (timestamp 1767685100)\n  (payload\n    (release \"2.0.0\")\n    (hash \"sha512:...\")\n    (archive-size 1048576)\n    (notes \"Major release\"))\n  (signature #${ed25519-sig}))"))
    (subsection
      "Request Message"
      (code scheme "(federation-message\n  (type request)\n  (from #${bob-pubkey})\n  (timestamp 1767685200)\n  (payload\n    (release \"2.0.0\")\n    (format cryptographic))\n  (signature #${ed25519-sig}))"))
    (subsection
      "Response Message"
      (code scheme "(federation-message\n  (type response)\n  (from #${alice-pubkey})\n  (in-reply-to \"sha512:request-hash\")\n  (timestamp 1767685300)\n  (payload\n    (release \"2.0.0\")\n    (archive-uri \"/releases/vault-2.0.0.archive\")\n    (hash \"sha512:...\")\n    (signature \"ed25519:...\"))\n  (signature #${ed25519-sig}))")))
  (section
    "Transport Bindings"
    (subsection
      "Git Transport"
      (code "Origin: git@github.com:alice/vault.git\nMechanism: Tags + release assets\n\nAnnounce: git push origin v2.0.0\nRequest:  git fetch origin --tags\nSync:     git fetch origin && git push origin"))
    (subsection
      "HTTP Transport"
      (code "Endpoint: https://alice.example.com/federation\n\nAnnounce: POST /federation/announce\nRequest:  GET /federation/releases/2.0.0\nSync:     POST /federation/sync"))
    (subsection
      "Filesystem Transport"
      (code "Path: /shared/federation/alice\n\nAnnounce: Copy to /shared/federation/alice/announce/\nRequest:  Read from /shared/federation/alice/releases/\nSync:     rsync --update")))
  (section
    "Conflict Resolution"
    (subsection
      "Version Conflicts"
      (p "Same version, different content:")
      (code scheme "(federation-conflict\n  (version \"2.0.0\")\n  (local-hash \"sha512:abc...\")\n  (remote-hash \"sha512:def...\")\n  (resolution reject))  ; Or: prefer-local, prefer-remote, rename")
      (p "Default: Reject conflicts, require human decision."))
    (subsection
      "Resolution Strategies"
      (p "1. Reject: Stop sync, alert human 2. Prefer-local: Keep local version 3. Prefer-remote: Take remote version 4. Rename: Keep both as 2.0.0-local, 2.0.0-remote 5. Merge: If content mergeable (future)")))
  (section
    "Consistency Model"
    (subsection
      "Eventual Consistency"
      (list
        (item "No global ordering required")
        (item "Each peer has local view")
        (item "Convergence through sync")
        (item "Conflicts resolved locally")))
    (subsection
      "Causal Ordering"
      (p "Within a peer's releases: - Version numbers are monotonic - Audit trail provides causality - Hash chains prevent reordering"))
    (subsection
      "No Coordination"
      (list
        (item "No consensus protocol required")
        (item "No distributed lock")
        (item "No leader election")
        (item "Each peer autonomous"))))
  (section
    "Security Considerations"
    (subsection
      "Threat Model"
      (p "Protected: - Unauthenticated release injection (signature verification) - Content tampering (hash verification) - Impersonation (SPKI principal binding) - Replay attacks (timestamps, sequence numbers)")
      (p "Not protected: - Denial of service (rate limiting helps) - Privacy of release metadata (encrypted transport helps) - Sybil attacks (trust management helps)"))
    (subsection
      "Trust Verification"
      (code scheme "(define (verify-peer-message msg peer-key)\n  (and (verify-signature msg peer-key)\n       (verify-timestamp msg (current-seconds))\n       (verify-not-replayed msg)))"))
    (subsection
      "Rate Limiting"
      (code scheme "(federation-config\n  (rate-limit\n    (announcements-per-hour 10)\n    (requests-per-minute 60)\n    (sync-interval-minimum 300)))")))
  (section
    "Gossip Protocol (Future)"
    (p "For larger networks:")
    (code "Alice announces to Bob and Carol\nBob announces to Dave and Eve\nEve announces to Frank\n\nResult: Epidemic spread without central broadcast")
    (p "Properties: - Logarithmic propagation time - Resilient to node failures - No single bottleneck"))
  (section
    "Bootstrap Procedure"
    (subsection
      "New Peer Joining"
      (p "1. Generate keypair 2. Register with known peer 3. Exchange public keys (out-of-band verification) 4. Initial sync to get current releases 5. Begin participating in federation"))
    (subsection
      "Network Partitions"
      (list
        (item "Partitions heal automatically on reconnection")
        (item "Conflicting releases detected and flagged")
        (item "Audit trails show partition history"))))
  (section
    "Configuration"
    (code scheme "(federation-config\n  ;; Identity\n  (identity my-private-key)\n\n  ;; Peers\n  (peers\n    (peer \"alice\" uri: \"git@github.com:alice/vault.git\"\n                  key: alice-pubkey\n                  trust: verified)\n    (peer \"bob\"   uri: \"/shared/bob-vault\"\n                  key: bob-pubkey\n                  trust: known))\n\n  ;; Policies\n  (auto-sync #t)\n  (sync-interval 3600)  ; seconds\n  (verify-before-accept #t)\n\n  ;; Security\n  (require-signature #t)\n  (trust-on-first-use #f))"))
  (section
    "Implementation Status"
    (subsection
      "Implemented (RFC-001)"
      (list
        (item "seal-publish: Push to single remote - seal-subscribe: Pull from single remote - seal-synchronize: Bidirectional with single peer")
        (item "Transport: git, HTTP, filesystem")))
    (subsection
      "Proposed (This RFC)"
      (list
        (item "Multi-peer management")
        (item "Trust levels and policies")
        (item "Announcement protocol")
        (item "Gossip propagation")
        (item "Conflict resolution UI"))))
  (section
    "References"
    (p "1. Birman, K. (2007). The Promise, and Limitations, of Gossip Protocols. 2. Demers, A., et al. (1987). Epidemic Algorithms for Replicated Database Maintenance. 3. Shapiro, M., et al. (2011). Conflict-Free Replicated Data Types. 4. RFC-001: Replication Layer 5. RFC-004: SPKI Authorization"))
  (section
    "Changelog"
    (list
      (item "2026-01-06")
      (item "Initial specification"))))

