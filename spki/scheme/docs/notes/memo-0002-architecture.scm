(memo
  (number 2)
  (title "Architecture")
  (section
    "Abstract"
    (p "Cyberspace is a distributed systems architecture built on S-expressions and Scheme, designed for cryptographic security without complexity. This Memo describes the overall system design, philosophy, and components."))
  (section
    "E Pluribus Unum"
    (p "Out of many, one. The VAXcluster motto: N nodes behave as one system. Cyberspace inherits this principle - distributed nodes, unified security domain, no central authority. The many remain autonomous; the one emerges from consensus.")
    (code "         ┌─────────────────────────────────────┐\n         │                                     │\n         │   Rough consensus, cryptography,    │\n         │   trusted systems, running code.    │\n         │                                     │\n         └─────────────────────────────────────┘"))
  (section
    "1. Motivation"
    (blockquote "A distributed system is one in which the failure of a computer you did not even know existed can render your own computer unusable. — Leslie Lamport")
    (blockquote "Let's face it: software is crap. Feature-laden and bloated, written under tremendous time-pressure, often by incapable coders, using dangerous languages and inadequate tools, trying to connect to heaps of broken or obsolete protocols, implemented equally insufficiently, running on unpredictable hardware – we are all more than used to brokenness. — Felix Winkelmann, author of Chicken Scheme")
    (p "Modern distributed systems are drowning in complexity. X.509 certificates require decoder rings. Container orchestration demands armies of SREs. Security policies hide in YAML nested seventeen levels deep.")
    (p "The Manifesto:")
    (blockquote "Authorized capability set with auditing. No central authority.")
    (p "These three principles - SPKI authorization, cryptographic audit trails, and optional centralization - are not new. They were proven in VAXcluster security (1984-1994), proposed in SDSI at IETF 29 Seattle (1994), and implemented partially in products that didn't survive their parent companies. Cyberspace completes what was started.")
    (p "Design Lineage:")
    (table
      (header "Era " "System " "Contribution ")
      (row "1984 " "VAXcluster " "\"Behave as one\" - N nodes, one security domain ")
      (row "1985 " "VMS C2 " "Audit trails, access control, security primitives ")
      (row "1993 " "VMS 6.0 " "Cluster-wide intrusion detection, TLV object store ")
      (row "1994 " "SDSI " "Self-certifying keys, local names (Rivest, IETF 29) ")
      (row "1999 " "SPKI " "Authorization certificates, capability delegation ")
      (row "2026 " "Cyberspace " "Synthesis: SPKI + audit + IPv6 mesh + no central authority "))
    (p "DECnet Phase IV had 24-bit addressing - fatal for internet scale. Cyberspace is designed for IPv6: 128-bit addresses, global mesh, same security principles.")
    (p "Cyberspace returns to first principles:")
    (list
      (item "S-expressions for everything: readable, parseable, auditable")
      (item "Minimal TCB: prove the crypto, evolve the rest")
      (item "No central authority: SPKI/SDSI namespaces over PKI hierarchies")
      (item "Running code: every feature traces to research, runs, and is tested"))
    (p "These principles prioritize auditability and evolution over optimization, recognizing that security systems fail when they become too complex to understand or too rigid to adapt.")
    (subsection
      "1.1 Design Methodology"
      (code "research → library → design specs → interface specs ⇄ implementation\n                                            ↓\n                                    [beta] verification/regression\n                                            ↓\n                                       release/publish")
      (p "Specs and implementation exist in dialogue. The bidirectional arrow captures the feedback loop: specifications inform code, code reveals specification defects. Tests gate the release, they don't drive the design.")))
  (section
    "2. The Prime Directive"
    (blockquote "If it's in the TCB, it's in OCaml. Otherwise it's in Chicken Scheme.")
    (code "┌─────────────────────────────────────────────────────────────┐\n│                                                             │\n│   TRUSTED COMPUTING BASE (OCaml, ~3000 lines)               │\n│                                                             │\n│   ┌─────────────┐  ┌─────────────┐  ┌─────────────┐         │\n│   │   Ed25519   │  │   SHA-512   │  │   Verify    │         │\n│   │   Sign      │  │   Hash      │  │   Chain     │         │\n│   └─────────────┘  └─────────────┘  └─────────────┘         │\n│                                                             │\n│   That's it. Everything else is policy.                     │\n│                                                             │\n└─────────────────────────────────────────────────────────────┘\n\n                        FFI (tiny surface)\n\n┌─────────────────────────────────────────────────────────────┐\n│                                                             │\n│   EVERYTHING ELSE (Chicken Scheme, unlimited)               │\n│                                                             │\n│   Vault - Audit - Replication - Names - Discovery           │\n│   CLI Tools - API Server - Library - Scripts                │\n│                                                             │\n│   Change it anytime. It's just policy.                      │\n│                                                             │\n└─────────────────────────────────────────────────────────────┘")
    (p "Rationale:")
    (list
      (item "OCaml: Strong types, formal verification with Rocq, compile-time safety")
      (item "Chicken Scheme: Interactive development, S-expressions everywhere, rapid evolution")
      (item "The boundary: Tiny, frozen, proven. The TCB does crypto and nothing else."))
    (p "A smaller TCB means fewer bugs that can break security. We prove the crypto in Rocq. Everything else can evolve freely.")
    (subsection
      "2.1 Interface Philosophy"
      (blockquote "English on top, Scheme for everything else.")
      (code "┌─────────────────────────────────────────────────────────────┐\n│  > status                    Command mode: English verbs    │\n│  > commit \"message\"          No parens needed              │\n│  > soup                      Explore, inspect, act          │\n├─────────────────────────────────────────────────────────────┤\n│  > (define x (keys))         Scheme mode: Full power       │\n│  > (map publish (releases))  Compose, transform, compute   │\n│  > (filter signed? certs)    Lambda is home                │\n└─────────────────────────────────────────────────────────────┘")
      (p "The command layer is syntactic sugar. The Scheme layer is substrate. Users start with English, graduate to Scheme when they need composition. No mode switching—parens are the only delimiter."))
    (subsection
      "2.2 The Data Flow"
      (blockquote "Eggs into soup.")
      (code "forge -> eggs -> soup -> vault")
      (code "       forge\n         ↓\n       eggs\n         ↓\n       soup ──┬──→ vault (persist)\n              │\n              └──→ ∅ (evaporate)")
      (table
        (header "Stage " "What " "How ")
        (row "forge " "Compilation " "Source newer than .so? Rebuild. Arch changed? Rebuild. ")
        (row "eggs " "Modules " "Chicken Scheme's dynamically compiled units ")
        (row "soup " "Workspace " "Newton-style queryable objects (in memory, transient) ")
        (row "vault " "Storage " "Content-addressed persistence (on disk, permanent) "))
      (p "The soup is the workspace. Commit it or lose it. Modules compile on demand. Objects simmer in memory until you seal them to the vault—or they evaporate when you quit.")))
  (section
    "3. Core Components"
    (blockquote "The unavoidable price of reliability is simplicity. — C.A.R. Hoare")
    (subsection
      "3.1 The Vault"
      (p "The vault is the disk.")
      (p "In VAXcluster, multiple subsystems coordinated distributed storage: MSCP served disks across nodes, the DLM managed locks, SCS handled communication, and the quorum disk arbitrated partitions. Five subsystems, complex interactions, decades of refinement.")
      (p "Cyberspace has one abstraction: the vault.")
      (code "VAXcluster          Cyberspace\n──────────          ──────────\nShared disk    →    Vault\nMSCP           →    Gossip replication\nDLM            →    Quorum consensus\nSCS            →    CIP (secure channels)\nQuorum disk    →    Vault\nLAVC           →    Enrollment")
      (p "The vault is content-addressed storage, replicated across nodes via gossip, with quorum state for partition handling:")
      (code scheme "(cluster-quorum\n  (epoch 42)\n  (expected-votes 5)\n  (quorum 3)\n  (members\n    (alice (votes 1) (role master))\n    (bob   (votes 1) (role full))\n    (carol (votes 1) (role full))\n    (dave  (votes 1) (role witness))\n    (eve   (votes 1) (role archive))))")
      (p "Boot sequence mirrors VAXcluster:")
      (list
        (item "Node reads local vault - knows expected membership")
        (item "Contacts other expected members")
        (item "Counts responding votes")
        (item "If >= quorum - cluster forms, proceed")
        (item "If < quorum - hang, wait, retry"))
      (p "Partition with quorum continues. Partition without hangs. No split-brain writes. When healed, minority syncs from majority. Epoch increments on membership change.")
      (code bash "$ cyberspace vault init\n$ cyberspace vault commit -m \"Deploy new API\"\n$ cyberspace vault verify\n✓ All signatures valid")
      (p "Every commit is cryptographically sealed. No GPG. No separate signing step."))
    (subsection
      "3.2 The Audit Trail"
      (p "Tamper-evident logging with hash chains.")
      (code scheme "(audit-entry\n  (sequence 1042)\n  (timestamp \"2026-01-06T15:30:00Z\")\n  (action (commit \"Deploy v2.1\"))\n  (actor (public-key |...|))\n  (previous-hash |...|)\n  (signature |...|))")
      (p "Append-only. Hash-chained. Signed. Export as text."))
    (subsection
      "3.3 SPKI Certificates"
      (p "Authorization without identity.")
      (code scheme "(cert\n  (issuer (public-key ed25519 |base64....|))\n  (subject (name alice \"deploy-server\"))\n  (grant (tag (http-api (method POST) (path \"/deploy/*\"))))\n  (valid (not-after \"2026-12-31\")))")
      (p "Human-readable security policy. No ASN.1. No X.509."))
    (subsection
      "3.4 Threshold Governance"
      (p "Democracy in code.")
      (code bash "$ cyberspace policy set deploy/prod --threshold 3 --signers alice,bob,carol,dave,eve\n$ cyberspace execute proposal-42\n✓ 3/5 signatures verified")
      (p "No single point of failure. No rogue admin."))
    (subsection
      "3.5 Secret Sharing"
      (p "Survive key loss with Shamir splitting.")
      (code scheme "(define shares (shamir-split master-key 5 3))\n;; Distribute 5 shares. Recover with any 3."))
    (subsection
      "3.6 Replication Layer"
      (p "Federated distribution without central registry. See Memo-007.")
      (code scheme "(seal-publish \"1.0.0\" remote: \"/shared/releases\")\n(seal-subscribe \"/shared/releases\" verify-key: alice-pub)\n(seal-synchronize peer-remote direction: 'both)"))
    (subsection
      "3.7 The Library Directory"
      (p "421 research papers, searchable.")
      (code "📖 > papers by Lamport\n📚 Found 15 documents\n📖 > about SPKI\n📖 > from 1979")))
  (section
    "4. Architecture"
    (blockquote "Complexity is the enemy of security. — Bruce Schneier")
    (subsection
      "4.1 Layer Diagram"
      (code "┌──────────────────────────────────────────────────────────────────┐\n│                        CYBERSPACE                                │\n├──────────────────────────────────────────────────────────────────┤\n│  ┌────────────┐  ┌────────────┐  ┌────────────┐  ┌────────────┐ │\n│  │   Vault    │  │   Audit    │  │   SPKI     │  │  Library   │ │\n│  └─────┬──────┘  └─────┬──────┘  └─────┬──────┘  └─────┬──────┘ │\n│        └───────────────┴───────┬───────┴───────────────┘        │\n│                    ┌───────────▼───────────┐                    │\n│                    │    Chicken Scheme     │                    │\n│                    │    (Policy Layer)     │                    │\n│                    └───────────┬───────────┘                    │\n│                    ┌───────────▼───────────┐                    │\n│                    │    OCaml TCB          │                    │\n│                    │    (Crypto Only)      │                    │\n│                    └───────────┬───────────┘                    │\n│                    ┌───────────▼───────────┐                    │\n│                    │    libsodium          │                    │\n│                    └───────────────────────┘                    │\n└──────────────────────────────────────────────────────────────────┘"))
    (subsection
      "4.2 No Central Authority"
      (code "     Alice                    Bob                     Carol\n       │                       │                        │\n       │    ┌─────────────┐    │    ┌─────────────┐    │\n       └───►│ Alice's     │◄───┴───►│ Bob's       │◄───┘\n            │ Namespace   │         │ Namespace   │\n            │             │         │             │\n            │ bob → key   │         │ alice → key │\n            │ carol → key │         │ carol → key │\n            └─────────────┘         └─────────────┘\n\n         No DNS. No CA. No single point of failure.\n         Just keys and local names.")
      (p "SPKI/SDSI gives you: - Local namespaces: \"bob\" means what you say it means - Authorization without identity: Grant permissions to keys, not people - Delegation chains: Alice → Bob → Carol, each step verified")))
  (section
    "5. Research Foundations"
    (blockquote "If I have seen further it is by standing on the shoulders of Giants. — Isaac Newton")
    (p "Every feature traces to a foundational paper:")
    (table
      (header "Feature " "Paper " "Author " "Year ")
      (row "Vault signatures " "\"New Directions in Cryptography\" " "Diffie & Hellman " "1976 ")
      (row "Audit trails " "\"How to Time-Stamp a Digital Document\" " "Haber & Stornetta " "1991 ")
      (row "Merkle proofs " "\"A Digital Signature Based on a Conventional Encryption Function\" " "Merkle " "1987 ")
      (row "Threshold sigs " "\"How to Share a Secret\" " "Shamir " "1979 ")
      (row "Logical clocks " "\"Time, Clocks, and the Ordering of Events\" " "Lamport " "1978 ")
      (row "Capabilities " "\"Protection\" " "Lampson " "1971 ")
      (row "SPKI certs " "\"SPKI Certificate Theory\" " "Ellison et al. " "1999 "))
    (p "421 papers in the library. Not just referenced—studied, implemented, running."))
  (section
    "6. Implementation Status"
    (blockquote "We reject kings, presidents and voting. We believe in rough consensus and running code. — Dave Clark, IETF")
    (code "✓ Lamport OTP       ✓ Merkle Trees      ✓ Capabilities\n✓ ChaCha20          ✓ Poly1305          ✓ Lamport Signatures\n✓ SPKI Certs        ✓ Vault             ✓ Audit Trails\n✓ Replication       ✓ Threshold Sigs    ✓ Shamir Sharing\n✓ Library Directory ✓ Federation        ✓ Lamport Clocks\n✓ TLA+ Specs        ◐ Rocq Proofs        ✓ AEAD Encryption\n✓ QR Merkle Trees   ✓ FUSE Wormholes    ✓ PQ Signatures")
    (p "Each traces to original research. Each runs. Each is tested."))
  (section
    "7. Security Considerations"
    (blockquote "You can't trust code that you did not totally create yourself. — Ken Thompson, Reflections on Trusting Trust")
    (subsection
      "7.1 TCB Minimization"
      (p "The attack surface is limited to ~3000 lines of OCaml calling libsodium and liboqs. This code is:")
      (list
        (item "Formally specified")
        (item "Proven in Rocq")
        (item "Frozen (rarely changes)"))
      (p "Minimizing the TCB reduces the attack surface to code that can be exhaustively verified, leaving everything else free to evolve without security implications."))
    (subsection
      "7.2 No Single Point of Failure"
      (list
        (item "No CA: SPKI namespaces are local")
        (item "No central server: Federation, not empire")
        (item "No single key: Threshold signatures, Shamir sharing"))
      (p "Eliminating single points of failure means the system degrades gracefully and cannot be compromised by attacking any one component, authority, or key holder."))
    (subsection
      "7.3 Auditability"
      (list
        (item "All security policy is human-readable S-expressions")
        (item "All history is hash-chained and signed")
        (item "All audit trails are exportable text"))
      (p "Auditability ensures that security failures can be diagnosed and that the system's behavior can be verified by inspection rather than faith.")))
  (section
    "8. Getting Started"
    (blockquote "The best way to predict the future is to invent it. — Alan Kay")
    (code bash "git clone git@github.com:ddp/cyberspace.git\ncd cyberspace/spki/scheme\n./spki-keygen alice\n./seal init --key alice.private\n./seal commit -m \"Hello, Cyberspace\""))
  (section
    "9. Future Work"
    (blockquote "A journey of a thousand miles begins with a single step. — Lao Tzu")
    (p "Most planned features are now implemented. Remaining work:")
    (list
      (item "Mobile agents (Memo-037)")))
  (section
    "10. References"
    (list
      (item "Diffie, W., & Hellman, M. (1976). New directions in cryptography.")
      (item "Haber, S., & Stornetta, W. S. (1991). How to time-stamp a digital document.")
      (item "Merkle, R. C. (1987). A digital signature based on a conventional encryption function.")
      (item "Shamir, A. (1979). How to share a secret.")
      (item "Lamport, L. (1978). Time, clocks, and the ordering of events in a distributed system.")
      (item "Lampson, B. W. (1971). Protection.")
      (item "Ellison, C., et al. (1999). SPKI certificate theory. RFC 2693.")))
  (section
    "Changelog"
    (list
      (item "2026-01-29")
      (item "Add Design Methodology diagram (section 1.1)")
      (item "2026-01-24 (2)")
      (item "Add PQ Signatures to implementation status (pq-crypto.scm complete)")
      (item "Update future work: only mobile agents remain")
      (item "2026-01-24")
      (item "Update implementation status: add Federation, Lamport Clocks, TLA+, Rocq, AEAD")
      (item "Update future work: remove implemented items, add post-quantum and mobile agents")
      (item "Fix TCB description: OCaml → Scheme")
      (item "2026-01-06")
      (item "Initial specification"))))

