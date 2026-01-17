;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 4)
  (title "Replication Layer for Library of Cyberspace")
  (section
    "Abstract"
    (p "This Memo specifies a replication layer for the Library of Cyberspace preservation architecture, enabling cryptographically sealed releases to be published, subscribed to, and synchronized across distributed locations while maintaining tamper-evident audit trails."))
  (section
    "Motivation"
    (subsection
      "Heritage: \"Behave as One\""
      (p "The VAXcluster principle (1984): N nodes must behave as one. Not eventually consistent. Not loosely coupled. Identical. One security domain, one namespace, one view of the world.")
      (p "DECnet Phase IV's 24-bit addressing was fatal for internet scale. Cyberspace applies the same principle to IPv6's 128-bit address space. Federated nodes, behaving as one."))
    (subsection
      "Requirements"
      (p "The Library of Cyberspace requires a distribution mechanism that:")
      (p "1. Preserves cryptographic authenticity - Signatures travel with artifacts 2. Enables offline verification - No centralized authority required 3. Records provenance - All publication events are audited 4. Supports multiple transports - Git, HTTP, filesystem 5. Maintains loose coupling - Works for confederations of friends")
      (p "Traditional package managers and distribution systems assume centralized registries and online verification. This replication layer is designed for decentralized, long-term preservation where trust is established through SPKI certificates and cryptographic seals.")))
  (section
    "Design Principles"
    (p "1. Sealed Releases - Only cryptographically signed releases can be published 2. Transport Agnostic - Same API works for git, HTTP, filesystem 3. Audit Everything - All replication events are recorded in tamper-evident log 4. Verify Before Trust - Subscribers must verify cryptographic seals 5. Explicit Authorization - SPKI certificates determine who can publish"))
  (section
    "Specification"
    (subsection
      "Three Core Operations"
      (p "#### 1. seal-publish")
      (p "Publish a sealed release to a remote location.")
      (code scheme "(seal-publish version\n              remote: target\n              archive-format: format\n              message: notes)")
      (p "Parameters: - version - Semantic version string (e.g., \"1.0.0\") - remote - Publication target (git remote, URL, or directory path) - archive-format - 'tarball, 'bundle, or 'cryptographic (default) - message - Release notes (optional)")
      (p "Behavior: 1. Verify release exists (creates if needed via seal-release) 2. Create cryptographic archive with:    - Tarball of repository at version tag    - SHA-512 hash of tarball    - Ed25519 signature of hash    - Manifest with version, hash, signature 3. Publish to remote based on type:    - Git remote: Push tag, optionally upload archive    - HTTP URL: POST archive to endpoint    - Filesystem: Copy archive to directory 4. Record publication in audit trail with:    - Actor (public key from signing key)    - Action (seal-publish version remote)    - Motivation (release notes)    - Cryptographic seal (signature)")
      (p "Audit Entry Format:")
      (code scheme "(audit-entry\n  (id \"sha512:...\")\n  (timestamp \"Mon Jan 5 23:38:20 2026\")\n  (sequence 1)\n  (actor\n    (principal #${public-key-blob})\n    (authorization-chain))\n  (action\n    (verb seal-publish)\n    (object \"1.0.0\")\n    (parameters \"/path/to/remote\"))\n  (context\n    (motivation \"Published to filesystem\")\n    (language \"en\"))\n  (environment\n    (platform \"unknown\")\n    (timestamp 1767685100))\n  (seal\n    (algorithm \"ed25519-sha512\")\n    (content-hash \"...\")\n    (signature \"...\")))")
      (p "#### 2. seal-subscribe")
      (p "Subscribe to sealed releases from a remote source.")
      (code scheme "(seal-subscribe remote\n                target: local-path\n                verify-key: public-key)")
      (p "Parameters: - remote - Source location (git remote, URL, or directory) - target - Local path for downloaded archives (optional) - verify-key - Public key for signature verification (optional)")
      (p "Behavior: 1. Discover available releases from remote:    - Git remote: List tags    - HTTP URL: GET /releases endpoint    - Filesystem: List .archive files 2. Download cryptographic archives 3. Verify each archive:    - Check manifest structure    - Verify SHA-512 hash of tarball    - Verify Ed25519 signature (if verify-key provided) 4. Extract verified archives to target directory 5. Record subscription in audit trail:    - Count of releases downloaded    - Source location    - Verification status")
      (p "Security Consideration: Without verify-key, subscription downloads archives but cannot verify authenticity. SPKI certificate chains should be used to establish trust.")
      (p "#### 3. seal-synchronize")
      (p "Bidirectional synchronization of sealed releases.")
      (code scheme "(seal-synchronize remote\n                  direction: 'both\n                  verify-key: public-key)")
      (p "Parameters: - remote - Sync target (git remote, URL, or directory) - direction - 'both (default), 'push-only, or 'pull-only - verify-key - Public key for signature verification (optional)")
      (p "Behavior: 1. Discover local and remote releases 2. Compare versions to determine:    - Releases to push (local but not remote)    - Releases to pull (remote but not local) 3. Execute publication for new local releases 4. Execute subscription for new remote releases 5. Record synchronization in audit trail:    - Count pushed and pulled    - Remote location    - Direction")
      (p "Use Case: Periodic sync between trusted peers in a confederation.")))
  (section
    "Archive Format"
    (subsection
      "Cryptographic Archive Structure"
      (code "vault-1.0.0.archive          # Manifest file\nvault-1.0.0.archive.tar.gz   # Actual tarball")
      (p "Manifest S-expression:")
      (code scheme "(sealed-archive\n  (version \"1.0.0\")\n  (format cryptographic)\n  (tarball \"vault-1.0.0.archive.tar.gz\")\n  (hash \"sha512:...\")\n  (signature \"ed25519:...\")\n  (timestamp 1767685100)\n  (sealer #${public-key-blob}))")
      (p "Verification Steps: 1. Read manifest 2. Hash tarball with SHA-512 3. Verify hash matches manifest 4. Verify Ed25519 signature on hash 5. Check SPKI authorization (optional)")))
  (section
    "Transport Implementations"
    (subsection
      "Git Remote"
      (list
        (item "Uses git push to share tags")
        (item "Optionally uploads archives as release assets (GitHub, GitLab)")
        (item "Fetch uses git fetch + git tag -l")))
    (subsection
      "HTTP Endpoint"
      (list
        (item "POST to /releases/<version> for publication")
        (item "GET /releases for discovery")
        (item "Content-Type: application/x-sealed-archive")))
    (subsection
      "Filesystem"
      (list
        (item "Copy archives to shared directory")
        (item "Directory structure: <remote>/<archive-name>")
        (item "No network required, works with NFS, USB drives, etc."))))
  (section
    "Audit Integration"
    (p "Every replication operation creates an audit entry with:")
    (p "1. Content-addressed ID - SHA-512 hash of entry 2. Chained structure - References parent entry 3. SPKI principal - Public key of actor 4. Dual context - Human motivation + machine environment 5. Cryptographic seal - Ed25519 signature")
    (p "This provides: - Non-repudiation - Cannot deny publication - Tamper evidence - Changes are detectable - Causality - Chain shows temporal order - Accountability - Know who published what when"))
  (section
    "Security Considerations"
    (subsection
      "Threat Model"
      (p "Trusted: - Local filesystem and vault - SPKI private keys - Cryptographic primitives (libsodium)")
      (p "Untrusted: - Remote repositories - Network transport - Downloaded archives - Remote publishers (until SPKI verified)"))
    (subsection
      "Attack Scenarios"
      (p "1. Malicious Archive Substitution    - Attacker replaces archive on remote    - Mitigation: Signature verification fails")
      (p "2. Version Rollback Attack    - Attacker removes newer releases    - Mitigation: Audit trail shows previous versions")
      (p "3. Unauthorized Publication    - Attacker publishes fake release    - Mitigation: SPKI authorization chain required")
      (p "4. Transport Tampering    - Network attacker modifies download    - Mitigation: Hash and signature verification"))
    (subsection
      "Best Practices"
      (p "1. Always verify signatures - Use verify-key parameter 2. Check SPKI certificates - Verify authorization chain 3. Maintain audit trail - Detect suspicious patterns 4. Use HTTPS for HTTP transport - Prevent network attacks 5. Backup signing keys - Use Shamir secret sharing")))
  (section
    "Implementation Notes"
    (subsection
      "Helper Functions"
      (code scheme "(tag-exists? tag-name)        ; Check if git tag exists\n(git-remote? str)             ; Detect git remote format\n(http-url? str)               ; Detect HTTP/HTTPS URL\n(publish-filesystem remote version archive)  ; Copy to directory\n(publish-http url version archive)           ; POST to endpoint"))
    (subsection
      "Dependencies"
      (list
        (item "Git")
        (item "For version control and tag management - libsodium")
        (item "Ed25519 signatures, SHA-512 hashing")
        (item "Chicken Scheme modules:   - (chicken process)")
        (item "Run git commands   - (chicken file)")
        (item "Filesystem operations   - (chicken irregex)")
        (item "URL/remote detection"))))
  (section
    "Compatibility"
    (p "This specification is compatible with:")
    (list
      (item "Git tags")
      (item "Standard git operations")
      (item "Git bundles")
      (item "Portable repository format")
      (item "Tarball archives")
      (item "Universal archive format")
      (item "S-expressions")
      (item "LISP/Scheme readable format")
      (item "SPKI/SDSI")
      (item "Authorization certificates"))
    (p "Future extensions may add: - IPFS transport - Content-addressed distribution - Tor hidden services - Anonymous publication - Encrypted archives - Confidential distribution - Multi-signature releases - Threshold authorization"))
  (section
    "Test Coverage"
    (p "See test-replication.scm:")
    (code scheme ";; Test seal-publish to filesystem\n(seal-publish \"1.0.0\"\n              remote: \"/tmp/cyberspace-publish-test\"\n              message: \"Published to filesystem\")\n\n;; Verify archive exists\n(file-exists? \"/tmp/cyberspace-publish-test/vault-1.0.0.archive\")\n\n;; Verify audit entry created\n(audit-read sequence: 1)"))
  (section
    "References"
    (p "1. SPKI/SDSI - RFC 2693, RFC 2692 2. Content-Addressed Storage - Git internals, IPFS 3. Semantic Versioning - semver.org 4. Ed25519 - Bernstein et al. 5. Audit Trails - Memo-002 (Cryptographic Audit Trail)"))
  (section
    "Changelog"
    (list
      (item "2026-01-05")
      (item "Initial implementation and specification   - seal-publish with git/HTTP/filesystem support   - seal-subscribe with signature verification   - seal-synchronize with bidirectional sync  ")
      (item "Full audit trail integration  ")
      (item "Cryptographic archive format"))))

