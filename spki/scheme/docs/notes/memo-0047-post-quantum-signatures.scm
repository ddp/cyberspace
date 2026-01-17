;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 47)
  (title "Post-Quantum Signatures")
  (section
    "Abstract"
    (p "Ed25519 won't survive. Shor's algorithm breaks elliptic curve cryptography in polynomial time. When quantum computers arrive, every capability ever signed, every realm identity ever created, becomes forgeable. This Memo specifies the transition from Ed25519 to post-quantum signature schemes: SPHINCS+ and CRYSTALS-Dilithium."))
  (section
    "The Threat"
    (p "Ed25519 security relies on the hardness of the elliptic curve discrete logarithm problem. Shor's algorithm solves this in polynomial time on a quantum computer.")
    (table
      (header "Algorithm " "Classical Security " "Quantum Security ")
      (row "Ed25519 " "128 bits " "0 bits (broken) ")
      (row "RSA-2048 " "112 bits " "0 bits (broken) ")
      (row "SPHINCS+-256 " "256 bits " "128 bits ")
      (row "Dilithium3 " "192 bits " "128 bits "))
    (p "When Q-Day arrives: - Every Ed25519 signature becomes forgeable - Every SPKI certificate can be counterfeited - Every realm identity can be stolen - Every sealed release can be replaced")
    (p "The capability chain breaks. The sealed closure unseals. Cyberspace falls.")
    (p "We must migrate before Q-Day."))
  (section
    "The Candidates"
    (p "NIST Post-Quantum Cryptography standardization selected:")
    (subsection
      "SPHINCS+ (Hash-Based)"
      (code "Type:           Stateless hash-based signatures\nSecurity basis: Hash function security (SHAKE256)\nKey size:       32 bytes (private), 32 bytes (public)\nSignature size: 7,856 - 49,856 bytes (parameter dependent)\nSpeed:          Slow signing, fast verification\nMaturity:       Conservative, well-understood")
      (p "Why SPHINCS+: - Security reduces to hash function security - No number-theoretic assumptions - Stateless (no state management headaches) - Uses SHAKE256 (same as our Merkle trees)")
      (p "Tradeoff: Large signatures. A SPHINCS+-256s signature is ~8 KB."))
    (subsection
      "CRYSTALS-Dilithium (Lattice-Based)"
      (code "Type:           Lattice-based (Module-LWE)\nSecurity basis: Learning With Errors hardness\nKey size:       1,312 bytes (private), 1,952 bytes (public)\nSignature size: 2,420 - 4,595 bytes (parameter dependent)\nSpeed:          Fast signing, fast verification\nMaturity:       Newer, but extensively analyzed")
      (p "Why Dilithium: - Smaller signatures than SPHINCS+ - Faster operations - NIST primary recommendation")
      (p "Tradeoff: Relies on lattice assumptions (less conservative than hash-based).")))
  (section
    "Cyberspace Strategy: Both"
    (p "We support both. Different use cases, different tradeoffs:")
    (table
      (header "Use Case " "Recommended " "Why ")
      (row "Realm identity (keystore) " "SPHINCS+ " "Maximum conservatism for long-lived keys ")
      (row "Capability certificates " "Dilithium " "Smaller signatures, many certs ")
      (row "Sealed releases " "SPHINCS+ " "Archival, must survive ")
      (row "Agent delegation " "Dilithium " "Short-lived, performance matters ")
      (row "Audit entries " "Dilithium " "High volume "))
    (p "The keystore can hold multiple key types:")
    (code scheme "(keystore\n  (realm-keys\n    (ed25519 #${legacy-key...})           ; Legacy (sunset)\n    (sphincs+ #${pq-primary...})          ; Post-quantum primary\n    (dilithium #${pq-operational...}))    ; Post-quantum operational\n  (active-signing 'sphincs+)\n  (accept-verification '(sphincs+ dilithium ed25519)))"))
  (section
    "Certificate Format"
    (subsection
      "Current (Ed25519)"
      (code scheme "(spki-cert\n  (issuer \"ed25519:alice...\")\n  (subject \"ed25519:bob...\")\n  (tag (read \"sha512:doc...\"))\n  (signature #${64-byte-ed25519-sig}))"))
    (subsection
      "Post-Quantum (SPHINCS+)"
      (code scheme "(spki-cert\n  (issuer \"sphincs+:alice...\")\n  (subject \"sphincs+:bob...\")\n  (tag (read \"shake256:doc...\"))           ; Merkle root\n  (signature-algorithm \"sphincs+-shake-256s\")\n  (signature #${7856-byte-sphincs-sig}))"))
    (subsection
      "Post-Quantum (Dilithium)"
      (code scheme "(spki-cert\n  (issuer \"dilithium:alice...\")\n  (subject \"dilithium:bob...\")\n  (tag (read \"shake256:doc...\"))\n  (signature-algorithm \"dilithium3\")\n  (signature #${3293-byte-dilithium-sig}))"))
    (subsection
      "Hybrid (Transition)"
      (p "During transition, sign with both:")
      (code scheme "(spki-cert\n  (issuer \"hybrid:alice...\")               ; Hybrid identity\n  (subject \"hybrid:bob...\")\n  (tag (read \"shake256:doc...\"))\n  (signatures\n    (ed25519 #${64-byte-sig})              ; Legacy\n    (sphincs+ #${7856-byte-sig})))         ; Post-quantum")
      (p "Both signatures must verify. If Ed25519 is later broken, SPHINCS+ still holds.")))
  (section
    "Key Generation"
    (subsection
      "SPHINCS+-SHAKE-256s"
      (code scheme "(define (sphincs+-keygen)\n  \"Generate SPHINCS+ keypair using SHAKE256\"\n  (let* ((seed (random-bytes 96))          ; 3 × 32-byte seeds\n         (sk-seed (subbytevector seed 0 32))\n         (sk-prf (subbytevector seed 32 64))\n         (pk-seed (subbytevector seed 64 96))\n         (keypair (sphincs+-generate sk-seed sk-prf pk-seed)))\n    keypair))\n\n;; Keystore storage (encrypted)\n(realm-private-key\n  (version 1)\n  (algorithm \"sphincs+-shake-256s\")\n  (parameters\n    (n 32)                                 ; Security parameter\n    (h 64)                                 ; Tree height\n    (d 8)                                  ; Hypertree layers\n    (k 22)                                 ; FORS trees\n    (w 16))                                ; Winternitz parameter\n  (protection \"passphrase\")\n  (kdf \"argon2id\")\n  (ciphertext #${encrypted-sk}))"))
    (subsection
      "Dilithium3"
      (code scheme "(define (dilithium-keygen)\n  \"Generate Dilithium3 keypair\"\n  (let* ((seed (random-bytes 32))\n         (keypair (dilithium3-generate seed)))\n    keypair))\n\n(realm-private-key\n  (version 1)\n  (algorithm \"dilithium3\")\n  (parameters\n    (k 6)                                  ; Module dimension\n    (l 5)\n    (eta 4)\n    (beta 175)\n    (omega 55))\n  (protection \"passphrase\")\n  (kdf \"argon2id\")\n  (ciphertext #${encrypted-sk}))")))
  (section
    "Signing Operations"
    (subsection
      "SPHINCS+ Signing"
      (code scheme "(define (sphincs+-sign message private-key)\n  \"Sign message with SPHINCS+\"\n  (let* ((opt-rand (random-bytes 32))      ; Optional randomness\n         (signature (sphincs+-sign-internal message private-key opt-rand)))\n    signature))\n\n;; Signature is large: 7,856 bytes for SPHINCS+-SHAKE-256s"))
    (subsection
      "Dilithium Signing"
      (code scheme "(define (dilithium-sign message private-key)\n  \"Sign message with Dilithium3\"\n  (let* ((signature (dilithium3-sign-internal message private-key)))\n    signature))\n\n;; Signature is moderate: 3,293 bytes for Dilithium3"))
    (subsection
      "Hybrid Signing"
      (code scheme "(define (hybrid-sign message ed25519-sk sphincs+-sk)\n  \"Sign with both algorithms for transition security\"\n  (let ((ed25519-sig (ed25519-sign message ed25519-sk))\n        (sphincs+-sig (sphincs+-sign message sphincs+-sk)))\n    `(hybrid-signature\n      (ed25519 ,ed25519-sig)\n      (sphincs+ ,sphincs+-sig))))")))
  (section
    "Verification"
    (subsection
      "Multi-Algorithm Verification"
      (code scheme "(define (verify-signature message signature public-key)\n  \"Verify signature, handling multiple algorithms\"\n  (let ((algorithm (signature-algorithm signature)))\n    (case algorithm\n      ((ed25519) (ed25519-verify message (sig-bytes signature) public-key))\n      ((sphincs+) (sphincs+-verify message (sig-bytes signature) public-key))\n      ((dilithium) (dilithium-verify message (sig-bytes signature) public-key))\n      ((hybrid) (verify-hybrid message signature public-key))\n      (else (error \"Unknown signature algorithm\" algorithm)))))\n\n(define (verify-hybrid message signature public-keys)\n  \"Both signatures must verify\"\n  (and (ed25519-verify message (hybrid-ed25519 signature) (keys-ed25519 public-keys))\n       (sphincs+-verify message (hybrid-sphincs+ signature) (keys-sphincs+ public-keys))))")))
  (section
    "Realm Identity"
    (p "A realm's principal expands to include algorithm:")
    (code "Current:   ed25519:7f3a2b4c5d6e...\nFuture:    sphincs+:8a9b0c1d2e3f...\n           dilithium:4e5f6a7b8c9d...\n           hybrid:7f3a2b4c|8a9b0c1d...")
    (p "The principal is still coordinates in cyberspace - a place you can teleport to. The algorithm prefix tells you what cryptography guards the gate."))
  (section
    "Capability Chain Implications"
    (p "Capability chains must handle mixed algorithms:")
    (code scheme ";; Alice (Ed25519) delegates to Bob (Dilithium) who delegates to Carol (SPHINCS+)\n(cert-chain\n  (cert-1\n    (issuer \"ed25519:alice...\")\n    (subject \"dilithium:bob...\")\n    (signature #${ed25519-sig}))\n  (cert-2\n    (issuer \"dilithium:bob...\")\n    (subject \"sphincs+:carol...\")\n    (signature #${dilithium-sig})))")
    (p "Each link verified with its own algorithm. The chain is as strong as its weakest link - but even one post-quantum link prevents total collapse after Q-Day."))
  (section
    "Migration Timeline"
    (subsection
      "Phase 1: Preparation (Now)"
      (list
        (item "Implement SPHINCS+ and Dilithium in crypto-ffi")
        (item "Add multi-algorithm support to keystore")
        (item "Test hybrid signatures")))
    (subsection
      "Phase 2: Hybrid Default (Now + 1 year)"
      (list
        (item "New realms generate hybrid keys (Ed25519 + SPHINCS+)")
        (item "All signatures include both")
        (item "Legacy realms can upgrade")))
    (subsection
      "Phase 3: Post-Quantum Primary (Q-Day - 3 years)"
      (list
        (item "SPHINCS+/Dilithium become primary")
        (item "Ed25519 becomes secondary")
        (item "Capability chains require at least one PQ signature")))
    (subsection
      "Phase 4: Legacy Sunset (Q-Day)"
      (list
        (item "Ed25519 signatures no longer trusted")
        (item "Hybrid signatures verified by PQ component only")
        (item "Legacy-only realms frozen (read-only)")))
    (subsection
      "Phase 5: Pure Post-Quantum (Q-Day + 2 years)"
      (list
        (item "Ed25519 removed from new certificates")
        (item "Historical certificates retain for audit")
        (item "Cyberspace survives"))))
  (section
    "Storage Implications"
    (p "Post-quantum signatures are larger:")
    (table
      (header "Component " "Ed25519 " "Dilithium3 " "SPHINCS+-256s ")
      (row "Public key " "32 B " "1,952 B " "32 B ")
      (row "Private key " "64 B " "4,000 B " "128 B ")
      (row "Signature " "64 B " "3,293 B " "7,856 B ")
      (row "Cert overhead " "~200 B " "~3,500 B " "~8,100 B "))
    (p "A realm with 10,000 capabilities: - Ed25519: ~2 MB - Dilithium: ~35 MB - SPHINCS+: ~81 MB")
    (p "Storage is cheap. Quantum resistance is not."))
  (section
    "Performance"
    (table
      (header "Operation " "Ed25519 " "Dilithium3 " "SPHINCS+-256s ")
      (row "Keygen " "0.03 ms " "0.15 ms " "2 ms ")
      (row "Sign " "0.05 ms " "0.5 ms " "50 ms ")
      (row "Verify " "0.1 ms " "0.3 ms " "1 ms "))
    (p "SPHINCS+ signing is slow (50ms). Acceptable for: - Realm identity (rare) - Sealed releases (rare) - Capability grants (occasional)")
    (p "Use Dilithium for: - Agent delegation (frequent) - Audit entries (constant) - Bulk operations"))
  (section
    "Library Support"
    (subsection
      "Required Libraries"
      (table
        (header "Library " "SPHINCS+ " "Dilithium " "Notes ")
        (row "liboqs " "Yes " "Yes " "Open Quantum Safe project ")
        (row "libsodium " "No " "No " "Not yet ")
        (row "OpenSSL 3.x " "Provider " "Provider " "Via oqsprovider ")
        (row "BoringSSL " "No " "Partial " "Google internal "))
      (p "Recommended: liboqs (Open Quantum Safe) - Reference implementations - Actively maintained - C library, easy FFI")
      (code scheme ";; crypto-ffi.scm addition\n(define sphincs+-sign (foreign-lambda ...))\n(define sphincs+-verify (foreign-lambda ...))\n(define dilithium-sign (foreign-lambda ...))\n(define dilithium-verify (foreign-lambda ...))")))
  (section
    "Security Considerations"
    (subsection
      "Algorithm Agility"
      (p "Cyberspace must survive algorithm obsolescence:")
      (code scheme "(define supported-algorithms\n  '((signatures . (ed25519 sphincs+ dilithium))\n    (hashes . (sha512 shake256 blake3))\n    (encryption . (xchacha20-poly1305 aes-256-gcm))))\n\n(define (algorithm-status alg)\n  (case alg\n    ((ed25519) 'deprecated)    ; Quantum-vulnerable\n    ((sphincs+) 'recommended)  ; Post-quantum, conservative\n    ((dilithium) 'recommended) ; Post-quantum, performant\n    ((sha512) 'legacy)         ; Quantum-reduced\n    ((shake256) 'recommended)  ; Post-quantum\n    ...))"))
    (subsection
      "Side Channels"
      (p "Post-quantum implementations must be constant-time: - SPHINCS+: Hash operations are naturally constant-time - Dilithium: Requires careful NTT implementation")
      (p "Use only audited implementations (liboqs reference, or formally verified)."))
    (subsection
      "Hybrid Security"
      (p "During transition, hybrid signatures provide defense in depth: - If Ed25519 is broken → SPHINCS+ holds - If SPHINCS+ has unknown flaw → Ed25519 holds (pre-Q-Day)")
      (p "Both must be broken to forge. Belt and suspenders.")))
  (section
    "Invariants"
    (code "S1. Post-quantum signatures are unforgeable (given hash security)\n    forge(sphincs+-sig) requires break(shake256)\n\nS2. Hybrid requires both valid\n    valid(hybrid-sig) ↔ valid(ed25519-sig) ∧ valid(pq-sig)\n\nS3. Algorithm indicated in signature\n    verify(sig) uses algorithm(sig), not ambient config\n\nS4. Key algorithm matches signature algorithm\n    sign(sphincs+-key, msg) produces sphincs+-signature\n\nS5. Migration preserves capability validity\n    valid-pre-migration(cert) → valid-post-migration(cert) [during transition]"))
  (section
    "The Quantum Winter"
    (p "Q-Day is coming. We don't know when - estimates range from 2030 to 2040. But the harvest-now-decrypt-later threat is real today. Every Ed25519 signature captured now can be forged after Q-Day.")
    (p "Cyberspace is built to last. The Library of Alexandria must not burn twice.")
    (p "When the quantum winter comes: - Merkle trees (Memo-042) protect object identity - SPHINCS+/Dilithium protect signatures - The sealed closure remains sealed - The wilderness of mirrors endures")
    (p "Prepare now. Migrate early. Survive."))
  (section
    "References"
    (p "1. NIST Post-Quantum Cryptography Standardization 2. SPHINCS+ specification - https://sphincs.org/ 3. CRYSTALS-Dilithium specification - https://pq-crystals.org/dilithium/ 4. Open Quantum Safe project - https://openquantumsafe.org/ 5. Shor, P., \"Algorithms for Quantum Computation\", 1994 6. Memo-041 - Keystore and Attestation 7. Memo-042 - Quantum-Resistant Merkle Trees"))
  (section
    "Changelog"
    (list
      (item "2026-01-08")
      (item "Initial draft"))))

