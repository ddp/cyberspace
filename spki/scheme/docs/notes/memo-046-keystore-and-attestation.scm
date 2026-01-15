;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 46)
  (title "Realm Keystore and Attestation")
  (section
    "Abstract"
    (p "A realm without identity is not sovereign. This Memo defines two protected stores within the vault:")
    (p "1. Keystore - where cryptographic identity lives (Ed25519 signing keys) 2. Attestation Store - where proofs about the realm live (hardware, software, identity claims)")
    (p "Together they form the inner vault - the protected core of a realm. Keys prove who you are. Attestations prove what you are."))
  (section
    "Motivation"
    (p "Memo-040 established that capabilities flow from Ed25519 signatures. Every certificate, every sealed release, every audit entry requires a signature. But where does the signing key live?")
    (p "Currently: ephemeral, generated per session. This is fine for testing but broken for production. A realm needs:")
    (list
      (item "Persistent identity - the same principal across sessions")
      (item "Protected storage - keys encrypted at rest")
      (item "Recovery path - don't lose your realm to a forgotten passphrase")
      (item "Rotation support - keys age, compromise happens"))
    (p "The keystore solves this."))
  (section
    "Realm Continuity"
    (p "A realm is not a snapshot. It accumulates.")
    (p "Identity continuity - Your principal persists across sessions, machines, years. Key rotation creates a signed chain: each new key vouched for by the old. The chain IS your history.")
    (p "Context accumulation - Every capability granted, every object stored, every federation established - these form the realm's memory. The audit chain records what happened. The attestation store proves what you were at each moment.")
    (p "History matters - A realm that has existed for ten years, rotated keys three times, accumulated thousands of attestations, federated with hundreds of peers - this realm has weight. Trust accrues. Reputation emerges from the chain.")
    (code "┌─────────────────────────────────────────────────────────────────┐\n│                        REALM TIMELINE                            │\n├─────────────────────────────────────────────────────────────────┤\n│                                                                  │\n│  Genesis ──► Key₁ ──► Key₂ ──► Key₃ ──► ... ──► Current        │\n│     │          │        │        │                   │          │\n│     ▼          ▼        ▼        ▼                   ▼          │\n│  [att₀]    [att₁₋₁₀] [att₁₁₋₅₀] [att₅₁₋₁₀₀]    [att_n]        │\n│                                                                  │\n│  Context grows. History deepens. Trust accumulates.             │\n└─────────────────────────────────────────────────────────────────┘")
    (p "The inner vault preserves this continuity: - Keystore - the chain of identity - Attestations - the record of what you were - Audit - the log of what you did")
    (p "A realm without history is newborn. A realm with history has standing.")
    (subsection
      "The Sealed Closure"
      (p "A realm is a sealed closure - it closes over its environment and that closure is cryptographically bound.")
      (code scheme ";; The realm as closure\n(lambda (request)\n  ;; Closed over:\n  ;;   - genesis: the first key, the origin moment\n  ;;   - keychain: every rotation, signed by predecessor\n  ;;   - attestations: every proof of what we were\n  ;;   - audit: every action taken\n  ;;   - capabilities: every right we hold\n  ;;   - objects: every thing we store\n  ;;\n  ;; The closure is sealed:\n  ;;   - Hash-chained: tamper-evident\n  ;;   - Signed: non-repudiable\n  ;;   - Content-addressed: self-verifying\n  ;;\n  (verify-and-respond request))")
      (p "You cannot forge a realm. You cannot inject false history. You cannot claim attestations you don't have. The closure is sealed at every point - verify any moment, the chain holds or it doesn't.")
      (p "Import a realm? You import the entire closure - genesis to present.")
      (p "Fork a realm? You create a new closure that references the old. The fork point is signed.")
      (p "Merge realms? The histories must be compatible. Conflicts are visible.")
      (p "The sealed closure is the unit of trust in cyberspace."))
    (subsection
      "Living in the Soup"
      (p "The sealed closure doesn't exist in a vacuum - it lives in the soup.")
      (p "The soup is the medium. Objects float in it - content-addressed, immutable, queryable. The realm swims through the soup, accumulating objects, granting capabilities, leaving audit trails. Everything the realm touches becomes part of its context.")
      (code "┌─────────────────────────────────────────────────────────────────┐\n│                          THE SOUP                                │\n│                                                                  │\n│     ○ obj    ○ obj       ┌─────────────────┐      ○ obj         │\n│          ○ obj           │░░░░░░░░░░░░░░░░░│           ○ obj    │\n│    ○ obj          ○ obj  │░░░  REALM  ░░░░░│    ○ obj           │\n│         ○ obj            │░░░ (island) ░░░░│         ○ obj      │\n│   ○ obj       ○ obj      │░░░░░░░░░░░░░░░░░│  ○ obj             │\n│        ○ obj             └─────────────────┘       ○ obj        │\n│   ○ obj    ○ obj     ○ obj           ○ obj    ○ obj             │\n│                                                                  │\n│   Objects float. The realm is sovereign territory.              │\n└─────────────────────────────────────────────────────────────────┘")
      (p "The realm is an island in the soup - an enclave of sovereignty, an instance you can address. Objects float past, currents of content flow through cyberspace, but the island is bounded. Its shores are defined by capabilities: what it can see, what it can grant, what attests to it.")
      (p "Every realm has coordinates: its principal. ed25519:7f3a2b4c... isn't just an identifier - it's a place you can teleport to. Present the right capability, and you're there. The soup connects all islands; the principal is your destination.")
      (p "Or send an agent.")
      (p "You needn't go yourself. Delegate a capability to an agent - a subprocess, a daemon, a trusted emissary - and it travels on your behalf. The agent carries your authority (attenuated, scoped, time-limited) and acts in the soup. It visits realms, fetches objects, negotiates federation. When it returns, its audit trail merges with yours.")
      (code scheme "(delegate-agent\n  (parent \"ed25519:your-realm...\")\n  (agent \"ed25519:agent-key...\")\n  (capabilities\n    (read \"sha512:*\")              ; Can read any object\n    (federate \"ed25519:peer...\"))  ; Can negotiate with this peer\n  (valid (not-after 1736500000))   ; Expires in 24h\n  (sandbox                          ; Constraints\n    (no-propagate)                  ; Cannot delegate further\n    (audit-required)))              ; Must return audit chain")
      (p "The agent is a sealed closure too - spawned from yours, carrying delegated authority, accumulating its own history. When the mission ends, the histories merge or the agent is revoked.")
      (p "Lineage:")
      (p "Go yourself - like telnet or VMS SET HOST. You're there, synchronous, your session on that node. Direct presence in another realm.")
      (p "Send an agent - like General Magic's Magic Cap and Telescript. Autonomous travelers carrying your intent, visiting places, doing work, returning with results. But recast in the spirit of Newton - agents swim in the soup, query objects, accumulate context. The soup is their medium, capabilities their passport.")
      (p "The soup is a wilderness of mirrors. Objects reference objects. Hashes point to hashes. Capabilities chain through delegation. Attestations vouch for attestations. An agent navigating the soup sees reflections within reflections - content-addressed identity means every object is its own mirror. The agent must hold the thread of its capability chain or be lost in infinite regress.")
      (p "This is not a safe place. It's cyberspace.")
      (code "┌────────────────┐                    ┌────────────────┐\n│   YOUR REALM   │                    │   PEER REALM   │\n│                │                    │                │\n│  ┌──────────┐  │    SET HOST /      │  ┌──────────┐  │\n│  │   you    │━━━━━━━━━━━━━━━━━━━━━━━━▶│   you    │  │\n│  └──────────┘  │    telnet           │  └──────────┘  │\n│                │                    │                │\n│  ┌──────────┐  │    delegate        │  ┌──────────┐  │\n│  │  agent   │━━━━━━━━━━━━━━━━━━━━━━━━▶│  agent   │  │\n│  └──────────┘  │    (Magic Cap)      │  └──────────┘  │\n│                │                    │                │\n└────────────────┘                    └────────────────┘\n                         ↑\n                    THE SOUP\n                 (Newton's medium)")
      (p "Objects have no access control - they're just content, identified by hash. The realm closure holds the capabilities that give meaning: \"I can read this,\" \"I granted that,\" \"This attests to me.\"")
      (p "The soup is shared. Islands may be near or far. Federation is building bridges between islands - agreeing to share objects, honor capabilities, witness each other's audit chains."))
    (subsection
      "Addressing Objects"
      (p "Objects in cyberspace have coordinates:")
      (code scheme ";; Local (this realm)\n\"releases/1.0.3\"                    ; By path\n\"sha512:abc123...\"                  ; By hash\n\n;; Remote (another realm) - @ syntax\n\"@ed25519:7f3a2b.../releases/1.0.3\"     ; Named object at realm\n\"@ed25519:7f3a2b.../sha512:abc123...\"   ; Hash-addressed at realm\n\n;; With role context - @principal+role:/path\n\"@ed25519:7f3a2b...+curator:/collections/rare-books\"\n\"@ed25519:7f3a2b...+guardian:/vault/keys\"\n\"@ed25519:7f3a2b...+witness:/audit/signatures\"\n\n;; With explicit capabilities - @principal+{caps}:/path\n\"@ed25519:7f3a2b...+{read}:/objects/sha512:abc...\"\n\"@ed25519:7f3a2b...+{read,write}:/collections/working\"\n\"@ed25519:7f3a2b...+{read,delegate(read)}:/shared/docs\"\n\n;; Role with capability refinement\n\"@ed25519:7f3a2b...+curator{read}:/collections/rare-books\"  ; curator, read only\n\n;; Inspect remote sealed object\n(soup-inspect \"@ed25519:7f3a2b.../releases/1.0.3\")\n\n;; Fetch requires capability\n(soup-fetch \"@ed25519:7f3a2b.../sha512:abc123...\"\n  capability: my-read-cert)\n\n;; Fetch with role context\n(soup-fetch \"@ed25519:7f3a2b...+curator:/collections/rare-books\"\n  capability: my-curator-cert)")
      (p "The @principal:/path syntax reads: \"at this realm, this object.\" The principal is your teleport destination. The path or hash is what you're looking for.")
      (p "The @principal+role:/path syntax adds role context: \"at this realm, acting as this role, this object.\"")
      (p "The @principal+{caps}:/path syntax specifies explicit capabilities: \"at this realm, with these specific capabilities, this object.\" Roles are shorthand for capability bundles; the +{caps} form is the truth underneath.")
      (p "+role{caps} combines both: use this role, but only these capabilities from it. Principle of least authority - request only what you need.")
      (p "Without a capability granting access, you can see the object exists (if the realm publishes its bloom filter) but cannot fetch its contents. The wilderness of mirrors shows reflections - but you need the right key to step through.")))
  (section
    "Architecture"
    (subsection
      "The Inner Vault"
      (code ".vault/\n├── keystore/                    # Identity store\n│   ├── realm.key               # Encrypted private key\n│   ├── realm.pub               # Public key (this is your principal)\n│   ├── keystore.meta           # Metadata, parameters\n│   └── recovery/               # Optional threshold shares\n│       ├── share.1.key\n│       └── share.2.key\n├── attestations/                # Proof store\n│   ├── hardware/               # Hardware attestations\n│   │   ├── anchor-quote.att       # Anchor measurement\n│   │   └── secure-enclave.att  # Apple SE attestation\n│   ├── software/               # Software attestations\n│   │   ├── boot-hash.att       # Measured boot\n│   │   └── runtime-hash.att    # Runtime measurements\n│   ├── identity/               # Third-party vouches\n│   │   └── ca-cert.att         # External CA attestation\n│   └── attestations.meta       # Attestation catalog\n├── releases/\n├── objects/\n├── capabilities/\n├── audit/\n└── node-hardware"))
    (subsection
      "Key Files"
      (p "realm.pub - Your public identity, shareable:")
      (code scheme "(realm-public-key\n  (version 1)\n  (created 1736400000)\n  (algorithm \"ed25519\")\n  (public-key #${7f3a2b4c...}))")
      (p "realm.key - Your private key, encrypted:")
      (code scheme "(realm-private-key\n  (version 1)\n  (algorithm \"ed25519\")\n  (protection \"passphrase\")      ; or \"hardware\", \"threshold\"\n  (kdf \"argon2id\")\n  (kdf-params\n    (ops-limit 3)                ; cryptopwhashOPSLIMIT_MODERATE\n    (mem-limit 268435456)        ; 256 MB\n    (salt #${random-32-bytes}))\n  (cipher \"xchacha20-poly1305\")\n  (nonce #${random-24-bytes})\n  (ciphertext #${encrypted-private-key}))")
      (p "keystore.meta - Configuration:")
      (code scheme "(keystore-meta\n  (version 1)\n  (created 1736400000)\n  (last-accessed 1736450000)\n  (protection \"passphrase\")\n  (backup-reminder 7776000)      ; 90 days\n  (rotation-reminder 31536000))  ; 1 year")))
  (section
    "Cryptographic Operations"
    (subsection
      "Key Derivation"
      (p "Passphrase → encryption key via Argon2id:")
      (code scheme "(define (derive-key passphrase salt)\n  \"Derive encryption key from passphrase using Argon2id\"\n  (let ((key (make-blob 32)))\n    (sodium-pwhash!\n      key\n      passphrase\n      salt\n      3                          ; ops-limit (moderate)\n      268435456                  ; mem-limit (256 MB)\n      'argon2id)\n    key))")
      (p "Why Argon2id: - Memory-hard: resists GPU/ASIC attacks - Time-hard: configurable iterations - Side-channel resistant: hybrid of Argon2i and Argon2d - Winner of Password Hashing Competition - Already in libsodium"))
    (subsection
      "Encryption"
      (p "Private key encrypted via XChaCha20-Poly1305:")
      (code scheme "(define (encrypt-private-key private-key encryption-key)\n  \"Encrypt private key for storage\"\n  (let ((nonce (random-bytes 24)))\n    (values\n      nonce\n      (sodium-secretbox private-key nonce encryption-key))))\n\n(define (decrypt-private-key ciphertext nonce encryption-key)\n  \"Decrypt private key from storage\"\n  (sodium-secretbox-open ciphertext nonce encryption-key))")
      (p "Why XChaCha20-Poly1305: - 256-bit key, 192-bit nonce - Extended nonce allows random generation (no counter needed) - Authenticated: tampering detected - Fast in software - Already in libsodium (crypto_secretbox)")))
  (section
    "Bootstrap Flow"
    (subsection
      "New Realm"
      (code "$ ./cyberspace-repl\n\n╔═══════════════════════════════════════════════════════════╗\n║                    REALM BOOTSTRAP                         ║\n╚═══════════════════════════════════════════════════════════╝\n\nNo realm identity found in .vault/keystore/\n\nCreate new realm? [y/n] y\n\nChoose protection method:\n  1. Passphrase (recommended)\n  2. Hardware token (requires YubiKey)\n  3. Threshold (k-of-n shares)\n\nSelection: 1\n\nEnter passphrase: \nConfirm passphrase: \n\nGenerating Ed25519 keypair...\nEncrypting with Argon2id (this takes a moment)...\n\n╔═══════════════════════════════════════════════════════════╗\n║  REALM CREATED                                             ║\n║                                                            ║\n║  Principal: ed25519:7f3a2b4c5d6e7f8a9b0c1d2e3f4a5b6c7d8e  ║\n║  Created:   2026-01-08 14:30:00 UTC                        ║\n║                                                            ║\n║  IMPORTANT: Your passphrase cannot be recovered.           ║\n║  Consider creating recovery shares with (keystore-backup)  ║\n╚═══════════════════════════════════════════════════════════╝\n\ncyberspace>"))
    (subsection
      "Existing Realm"
      (code "$ ./cyberspace-repl\n\nRealm: ed25519:7f3a2b4c...\nPassphrase: \n\nUnlocking keystore...\n\ncyberspace> ; Ready, identity loaded"))
    (subsection
      "Failed Unlock"
      (code "Passphrase: \n\nERROR: Decryption failed (wrong passphrase?)\nAttempts remaining: 2\n\nPassphrase: \n\nERROR: Decryption failed\nAttempts remaining: 1\n\nWARNING: One attempt remaining. Consider:\n  - Recovery shares if configured\n  - The passphrase is case-sensitive\n  - Check caps lock")))
  (section
    "Recovery"
    (subsection
      "Threshold Shares"
      (p "For high-value realms, split the key into k-of-n shares (Memo-007):")
      (code scheme "(keystore-backup\n  threshold: 2                   ; k - shares needed\n  shares: 3)                     ; n - shares created\n\n;; Output:\n;; Share 1 of 3 (requires 2 to recover):\n;; CYBER-SHARE-1-7f3a2b4c5d6e7f8a9b0c1d2e3f4a5b6c7d8e9f0a1b2c3d4e5f6a7b8c9d0e1f2\n;;\n;; Share 2 of 3 (requires 2 to recover):\n;; CYBER-SHARE-2-8a9b0c1d2e3f4a5b6c7d8e9f0a1b2c3d4e5f6a7b8c9d0e1f2a3b4c5d6e7f8\n;;\n;; Share 3 of 3 (requires 2 to recover):\n;; CYBER-SHARE-3-9b0c1d2e3f4a5b6c7d8e9f0a1b2c3d4e5f6a7b8c9d0e1f2a3b4c5d6e7f8a9\n;;\n;; STORE THESE SEPARATELY. Any 2 can recover your realm.")
      (p "Recovery:")
      (code scheme "(keystore-recover\n  \"CYBER-SHARE-1-7f3a2b4c...\"\n  \"CYBER-SHARE-3-9b0c1d2e...\")\n\n;; Realm recovered. Set new passphrase:\n;; New passphrase: \n;; Confirm: \n;; Keystore restored."))
    (subsection
      "Paper Backup"
      (p "For the paranoid (wisely so):")
      (code scheme "(keystore-paper-backup)\n\n;; Generates QR code + text backup for offline storage\n;; Encrypted with passphrase, prints to terminal/file")))
  (section
    "Key Rotation"
    (p "Keys should rotate periodically. Old key signs new key, creating continuity:")
    (code scheme "(keystore-rotate)\n\n;; Current principal: ed25519:7f3a2b4c...\n;;\n;; This will:\n;;   1. Generate new Ed25519 keypair\n;;   2. Sign rotation certificate with old key\n;;   3. Store rotation chain in keystore\n;;   4. New principal becomes active\n;;\n;; Proceed? [y/n] y\n;;\n;; Enter current passphrase: \n;; Enter new passphrase (or same): \n;;\n;; Generating new keypair...\n;; Signing rotation certificate...\n;;\n;; ROTATION COMPLETE\n;; Old principal: ed25519:7f3a2b4c...\n;; New principal: ed25519:2c3d4e5f...\n;; Rotation cert: sha512:rotation-cert-hash...\n;;\n;; Old capabilities referencing ed25519:7f3a2b4c will need reissuance.")
    (p "Rotation certificate:")
    (code scheme "(rotation-cert\n  (old-principal \"ed25519:7f3a2b4c...\")\n  (new-principal \"ed25519:2c3d4e5f...\")\n  (timestamp 1736500000)\n  (reason \"scheduled-rotation\")\n  (signature \"ed25519:old-key-signature...\"))"))
  (section
    "Attestation Store"
    (p "Attestations are signed claims about the realm. They answer: \"What can you prove about yourself?\"")
    (subsection
      "Attestation Types"
      (p "Hardware Attestations - proofs from silicon:")
      (code scheme "(hardware-attestation\n  (type \"anchor-quote\")\n  (timestamp 1736400000)\n  (platform \"Darwin-arm64\")\n  (measurements\n    (rune-boot #${boot-measurement...})\n    (rune-policy #${secureboot-policy...}))\n  (signature #${anchor-signature...})\n  (certificate #${endorsement-key-cert...}))")
      (p "Software Attestations - proofs from code:")
      (code scheme "(software-attestation\n  (type \"runtime-measurement\")\n  (timestamp 1736400000)\n  (binary-hash \"sha512:cyberspace-repl...\")\n  (library-hashes\n    (\"libsodium.dylib\" \"sha512:...\")\n    (\"libchicken.dylib\" \"sha512:...\"))\n  (signature #${realm-signature...}))")
      (p "Identity Attestations - third-party vouches:")
      (code scheme "(identity-attestation\n  (type \"ca-vouch\")\n  (timestamp 1736400000)\n  (subject \"ed25519:7f3a2b4c...\")         ; This realm\n  (issuer \"ed25519:ca-public-key...\")     ; Vouching authority\n  (claims\n    (organization \"Acme Corp\")\n    (role \"coordinator\"))\n  (valid (not-after 1767936000))\n  (signature #${ca-signature...}))")
      (p "Capability Attestations - proof of holding:")
      (code scheme "(capability-attestation\n  (type \"capability-proof\")\n  (timestamp 1736400000)\n  (capability \"sha512:cert-hash...\")\n  (holder \"ed25519:7f3a2b4c...\")\n  (challenge #${nonce...})                ; Prevents replay\n  (response #${signed-challenge...}))"))
    (subsection
      "Attestation Catalog"
      (p "The attestation store maintains a catalog for fast lookup:")
      (code scheme "(attestations-meta\n  (version 1)\n  (count 5)\n  (types\n    (hardware 2)\n    (software 1)\n    (identity 1)\n    (capability 1))\n  (latest-refresh 1736400000)\n  (entries\n    ((id \"att-001\") (type hardware) (file \"hardware/anchor-quote.att\") (expires #f))\n    ((id \"att-002\") (type hardware) (file \"hardware/secure-enclave.att\") (expires #f))\n    ((id \"att-003\") (type software) (file \"software/runtime-hash.att\") (expires #f))\n    ((id \"att-004\") (type identity) (file \"identity/ca-cert.att\") (expires 1767936000))\n    ((id \"att-005\") (type capability) (file \"capability/coord-role.att\") (expires 1736500000))))"))
    (subsection
      "Attestation Operations"
      (code scheme ";; Refresh hardware attestations (re-measure)\n(attestation-refresh-hardware)\n;; => Querying Anchor... done.\n;; => Querying Secure Enclave... done.\n;; => 2 hardware attestations updated.\n\n;; Measure current software state\n(attestation-measure-software)\n;; => Hashing cyberspace-repl... done.\n;; => Hashing loaded libraries... done.\n;; => Software attestation stored.\n\n;; Request identity attestation from CA\n(attestation-request-identity \"ed25519:ca-key...\")\n;; => Sending attestation request to CA...\n;; => (requires CA to sign and return)\n\n;; Prove capability holding (for remote verification)\n(attestation-prove-capability \"sha512:cert-hash...\" challenge)\n;; => (capability-attestation ...)\n\n;; List all attestations\n(attestation-list)\n;; => ((att-001 hardware anchor-quote valid)\n;;     (att-002 hardware secure-enclave valid)\n;;     (att-003 software runtime-hash valid)\n;;     (att-004 identity ca-cert expires:2026-12-31)\n;;     (att-005 capability coord-role expires:2026-01-10))\n\n;; Verify an attestation\n(attestation-verify \"att-001\")\n;; => (attestation att-001 (status valid) (type hardware) (verified #t))\n\n;; Export for remote verification\n(attestation-export \"att-001\")\n;; => (hardware-attestation (type \"anchor-quote\") ...)"))
    (subsection
      "Attestation Chain"
      (p "Attestations can chain - a hardware attestation vouches for software, software vouches for capabilities:")
      (code "┌───────────────────────────┐\n│    The Anchor (Silicon)   │  \"This boot sequence is measured\"\n└─────────────┬─────────────┘\n              │ vouches for\n              ▼\n┌───────────────────────────┐\n│    Software Runes         │  \"These binaries are running\"\n└─────────────┬─────────────┘\n              │ vouches for\n              ▼\n┌───────────────────────────┐\n│    Realm Identity         │  \"This is my signing key\"\n└─────────────┬─────────────┘\n              │ vouches for\n              ▼\n┌───────────────────────────┐\n│    Capabilities Held      │  \"I can do these things\"\n└───────────────────────────┘")
      (p "Remote verifier can walk the chain: \"Show me your hardware attestation, software measurement, and the capability you claim.\""))
    (subsection
      "Use Cases"
      (p "Coordinator Election (Memo-037): Candidate presents attestations proving hardware capability and identity. Voters verify before granting coordinator role.")
      (p "Federation Trust (Memo-039): Realms exchange attestations when federating. \"Before I sync objects with you, prove your software is legitimate.\"")
      (p "High-Security Operations: Some capabilities might require fresh attestation: \"This capability requires Anchor attestation less than 1 hour old.\"")))
  (section
    "Hardware Token Support"
    (p "Future: YubiKey, secure enclaves, hardware anchors.")
    (code scheme "(keystore-meta\n  (version 1)\n  (protection \"hardware\")\n  (hardware-type \"yubikey-5\")\n  (hardware-serial \"12345678\")\n  (public-key #${...}))          ; Private key never leaves device")
    (p "The private key never touches disk - it lives in the hardware token. Operations requiring signature prompt for touch."))
  (section
    "Security Considerations"
    (subsection
      "What We Protect Against"
      (table
        (header "Threat " "Mitigation ")
        (row "Disk theft " "Encrypted at rest (XChaCha20-Poly1305) ")
        (row "Weak passphrase " "Argon2id memory-hard KDF ")
        (row "Brute force " "Rate limiting, attempt counter ")
        (row "Memory dump " "Zero memory after use ")
        (row "Forgotten passphrase " "Threshold recovery shares ")
        (row "Key compromise " "Rotation support ")))
    (subsection
      "What We Don't Protect Against"
      (table
        (header "Threat " "Why ")
        (row "Compromised endpoint " "If attacker has root, game over ")
        (row "Keylogger capturing passphrase " "Endpoint security problem ")
        (row "Rubber hose cryptanalysis " "Math doesn't help ")
        (row "Quantum computers " "Ed25519 vulnerable (migration planned) ")))
    (subsection
      "Memory Handling"
      (code scheme "(define (with-sensitive-data data thunk)\n  \"Execute thunk with sensitive data, zero on exit\"\n  (dynamic-wind\n    (lambda () #f)\n    thunk\n    (lambda () (sodium-memzero! data))))")
      (p "Private keys are zeroed immediately after use. Passphrases are zeroed after key derivation.")))
  (section
    "REPL Commands"
    (code scheme ";; Check keystore status\n(keystore-status)\n;; => (keystore (status unlocked) (principal \"ed25519:7f3a...\") (protection passphrase))\n\n;; Lock keystore (zero keys from memory)\n(keystore-lock)\n;; => Keystore locked. Re-authentication required for signing.\n\n;; Unlock keystore\n(keystore-unlock)\n;; => Passphrase: \n;; => Keystore unlocked.\n\n;; Change passphrase\n(keystore-change-passphrase)\n;; => Current passphrase: \n;; => New passphrase: \n;; => Confirm: \n;; => Passphrase changed.\n\n;; Create recovery shares\n(keystore-backup threshold: 2 shares: 3)\n\n;; Recover from shares\n(keystore-recover share1 share2)\n\n;; Rotate key\n(keystore-rotate)\n\n;; Export public key (safe to share)\n(keystore-export-public)\n;; => (realm-public-key (algorithm \"ed25519\") (public-key #${7f3a...}))"))
  (section
    "Vault Protection"
    (p "The keystore protects itself. The operating system is not trusted.")
    (p "realm.key - Never stored plaintext. The ciphertext blob is meaningless without the passphrase. Even if someone copies the file, they have nothing.")
    (p "realm.pub - Public by nature. This IS your identity. Share it freely.")
    (p "attestations/ - Signed claims. Tamper-evident by construction. Copy them, share them - forgery is computationally infeasible.")
    (p "The vault doesn't rely on filesystem permissions, SELinux, or any operating system mechanism. Cyberspace assumes the OS is compromised. Protection comes from:")
    (p "1. Encryption - Private key encrypted at rest 2. Memory zeroing - Keys cleared immediately after use 3. Signatures - Everything signed, tampering detected 4. Content addressing - Hash IS identity")
    (p "If someone has root on your machine, they can install a keylogger - that's a physical security problem, not a cryptographic one. Cyberspace protects the math. Protect the machine yourself."))
  (section
    "Integration"
    (subsection
      "With seal-release (Memo-033)"
      (code scheme "(seal-release \"1.0.4\" name: \"phoenix\")\n;; Uses keystore signing key automatically\n;; Prompts for unlock if keystore locked"))
    (subsection
      "With capabilities (Memo-004)"
      (code scheme "(spki-cert-create\n  subject: \"ed25519:bob...\"\n  tag: '(read \"sha512:doc...\"))\n;; Signed with keystore key\n;; Issuer automatically set to realm principal"))
    (subsection
      "With audit (Memo-040)"
      (code scheme ";; Audit entries signed with keystore key\n;; Principal identity consistent across sessions")))
  (section
    "Invariants"
    (subsection
      "Keystore"
      (code "K1. Private key never stored plaintext\n    stored(private-key) → encrypted(private-key)\n\nK2. Decryption requires authentication\n    decrypt(keystore) → auth(passphrase) ∨ auth(hardware) ∨ auth(threshold)\n\nK3. Memory zeroed after use\n    use(sensitive-data) → zero(sensitive-data)\n\nK4. Rotation preserves identity chain\n    rotate(k₁,k₂) → signed(k₂, k₁)\n\nK5. Recovery requires threshold\n    recover(keystore) → shares ≥ k"))
    (subsection
      "Attestation"
      (code "A1. Attestations are signed\n    store(attestation) → signed(attestation, issuer)\n\nA2. Attestation chains are verifiable\n    chain(a₁→a₂→...→aₙ) → ∀i: valid_sig(aᵢ)\n\nA3. Hardware attestations originate from anchors\n    hardware-attestation(a) → anchor-signed(a)\n\nA4. Attestations are timestamped\n    attestation(a) → timestamp(a) ∧ fresh(a, policy)\n\nA5. Expired attestations are invalid\n    expired(a) → ¬valid(a)")))
  (section
    "Quantum Resistance"
    (p "SHA-512 won't survive. Grover's algorithm halves the security - 256 bits becomes 128. For the wilderness of mirrors to endure, we need quantum-resistant Merkle trees.")
    (p "The Path Forward:")
    (code "Current:     sha512(content) → object identity\nFuture:      merkle-root(shake256(chunks...)) → object identity")
    (p "Why Merkle trees: - Incremental updates without rehashing everything - Selective disclosure - prove a branch without revealing siblings - Tree structure means log(n) proof sizes - Quantum-resistant hash at each node")
    (p "Candidate hash functions:")
    (table
      (header "Function " "Output " "Notes ")
      (row "SHAKE256 " "Variable " "SHA-3 family, NIST approved, used by SPHINCS+ ")
      (row "BLAKE3 " "256-bit " "Fast, tree-based internally, modern ")
      (row "SHA-3-512 " "512-bit " "Conservative choice, different construction than SHA-2 "))
    (p "Migration:")
    (p "Objects can carry both hashes during transition:")
    (code scheme "(object\n  (content-hash \"sha512:abc123...\")           ; Legacy\n  (merkle-root \"shake256:def456...\")          ; Quantum-resistant\n  (tree-depth 4)\n  (chunk-size 4096))")
    (p "The soup becomes a forest of Merkle trees. Each object a tree, each tree quantum-hardened. The wilderness of mirrors, built to outlast the quantum winter.")
    (p "Ed25519 replacement: SPHINCS+ or CRYSTALS-Dilithium for signatures. That's a separate RFC."))
  (section
    "References"
    (p "1. libsodium documentation - Password Hashing, Secret-key Encryption 2. Argon2 specification - https://github.com/P-H-C/phc-winner-argon2 3. Shamir's Secret Sharing - Shamir, A., \"How to Share a Secret\", 1979 4. Memo-007 - Threshold Governance 5. Memo-040 - Cyberspace Security Architecture"))
  (section
    "Changelog"
    (list
      (item "2026-01-08")
      (item "Initial draft"))))

