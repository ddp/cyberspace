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
      (list
        (item "Preserves cryptographic authenticity - Signatures travel with artifacts")
        (item "Enables offline verification - No centralized authority required")
        (item "Records provenance - All publication events are audited")
        (item "Supports multiple transports - Git, HTTP, filesystem")
        (item "Maintains loose coupling - Works for confederations of friends"))
      (p "These requirements reflect the reality of distributed archival: networks partition, authorities disappear, and trust must be verifiable without phoning home.")
      (p "Traditional package managers and distribution systems assume centralized registries and online verification. This replication layer is designed for decentralized, long-term preservation where trust is established through Simple Public Key Infrastructure (SPKI) certificates and cryptographic seals.")))
  (section
    "Design Principles"
    (list
      (item "Sealed Releases - Only cryptographically signed releases can be published")
      (item "Transport Agnostic - Same API works for git, HTTP, filesystem")
      (item "Audit Everything - All replication events are recorded in tamper-evident log")
      (item "Verify Before Trust - Subscribers must verify cryptographic seals")
      (item "Explicit Authorization - SPKI certificates determine who can publish"))
    (p "These principles ensure that trust is established cryptographically rather than administratively, and that the system works regardless of network topology or transport mechanism."))
  (section
    "Specification"
    (subsection
      "Three Core Operations"
      (p "#### 1. seal-publish")
      (p "Publish a sealed release to a remote location.")
      (code scheme "(seal-publish version\n              remote: target\n              archive-format: format\n              message: notes)")
      (p "Parameters: - version - Semantic version string (e.g., \"1.0.0\") - remote - Publication target (git remote, URL, or directory path) - archive-format - 'tarball, 'bundle, or 'cryptographic (default) - message - Release notes (optional)")
      (p "Behavior:")
      (list
        (item "Verify release exists (creates if needed via seal-release)")
        (item "Create cryptographic archive with: tarball of repository at version tag, SHA-512 hash of tarball, Ed25519 signature of hash, manifest with version, hash, signature")
        (item "Publish to remote based on type: Git remote (push tag, optionally upload archive), HTTP URL (POST archive to endpoint), Filesystem (copy archive to directory)")
        (item "Record publication in audit trail with: actor (public key from signing key), action (seal-publish version remote), motivation (release notes), cryptographic seal (signature)"))
      (p "Audit Entry Format:")
      (code scheme "(audit-entry\n  (id \"sha512:...\")\n  (timestamp \"Mon Jan 5 23:38:20 2026\")\n  (sequence 1)\n  (actor\n    (principal #${public-key-blob})\n    (authorization-chain))\n  (action\n    (verb seal-publish)\n    (object \"1.0.0\")\n    (parameters \"/path/to/remote\"))\n  (context\n    (motivation \"Published to filesystem\")\n    (language \"en\"))\n  (environment\n    (platform \"unknown\")\n    (timestamp 1767685100))\n  (seal\n    (algorithm \"ed25519-sha512\")\n    (content-hash \"...\")\n    (signature \"...\")))")
      (p "#### 2. seal-subscribe")
      (p "Subscribe to sealed releases from a remote source.")
      (code scheme "(seal-subscribe remote\n                target: local-path\n                verify-key: public-key)")
      (p "Parameters: - remote - Source location (git remote, URL, or directory) - target - Local path for downloaded archives (optional) - verify-key - Public key for signature verification (optional)")
      (p "Behavior:")
      (list
        (item "Discover available releases from remote: Git remote (list tags), HTTP URL (GET /releases endpoint), Filesystem (list .archive files)")
        (item "Download cryptographic archives")
        (item "Verify each archive: check manifest structure, verify SHA-512 hash of tarball, verify Ed25519 signature (if verify-key provided)")
        (item "Extract verified archives to target directory")
        (item "Record subscription in audit trail: count of releases downloaded, source location, verification status"))
      (p "Security Consideration: Without verify-key, subscription downloads archives but cannot verify authenticity. SPKI certificate chains should be used to establish trust.")
      (p "#### 3. seal-synchronize")
      (p "Bidirectional synchronization of sealed releases.")
      (code scheme "(seal-synchronize remote\n                  direction: 'both\n                  verify-key: public-key)")
      (p "Parameters: - remote - Sync target (git remote, URL, or directory) - direction - 'both (default), 'push-only, or 'pull-only - verify-key - Public key for signature verification (optional)")
      (p "Behavior:")
      (list
        (item "Discover local and remote releases")
        (item "Compare versions to determine: releases to push (local but not remote), releases to pull (remote but not local)")
        (item "Execute publication for new local releases")
        (item "Execute subscription for new remote releases")
        (item "Record synchronization in audit trail: count pushed and pulled, remote location, direction"))
      (p "Use Case: Periodic sync between trusted peers in a confederation.")))
  (section
    "Archive Format"
    (subsection
      "Cryptographic Archive Structure"
      (code "vault-1.0.0.archive          # Manifest file\nvault-1.0.0.archive.tar.gz   # Actual tarball")
      (p "Manifest S-expression:")
      (code scheme "(sealed-archive\n  (version \"1.0.0\")\n  (format cryptographic)\n  (tarball \"vault-1.0.0.archive.tar.gz\")\n  (hash \"sha512:...\")\n  (signature \"ed25519:...\")\n  (timestamp 1767685100)\n  (sealer #${public-key-blob}))")
      (p "Verification Steps:")
      (list
        (item "Read manifest")
        (item "Hash tarball with SHA-512")
        (item "Verify hash matches manifest")
        (item "Verify Ed25519 signature on hash")
        (item "Check SPKI authorization (optional)"))))
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
    (list
      (item "Content-addressed ID - SHA-512 hash of entry")
      (item "Chained structure - References parent entry")
      (item "SPKI principal - Public key of actor")
      (item "Dual context - Human motivation + machine environment")
      (item "Cryptographic seal - Ed25519 signature"))
    (p "This provides: - Non-repudiation - Cannot deny publication - Tamper evidence - Changes are detectable - Causality - Chain shows temporal order - Accountability - Know who published what when"))
  (section
    "Security Considerations"
    (subsection
      "Threat Model"
      (p "Trusted: - Local filesystem and vault - SPKI private keys - Cryptographic primitives (libsodium)")
      (p "Untrusted: - Remote repositories - Network transport - Downloaded archives - Remote publishers (until SPKI verified)"))
    (subsection
      "Attack Scenarios"
      (list
        (item "Malicious Archive Substitution - Attacker replaces archive on remote - Mitigation: Signature verification fails")
        (item "Version Rollback Attack - Attacker removes newer releases - Mitigation: Audit trail shows previous versions")
        (item "Unauthorized Publication - Attacker publishes fake release - Mitigation: SPKI authorization chain required")
        (item "Transport Tampering - Network attacker modifies download - Mitigation: Hash and signature verification"))
      (p "Each attack is addressed at the cryptographic layer rather than the transport layer, ensuring protection regardless of network conditions."))
    (subsection
      "Best Practices"
      (list
        (item "Always verify signatures - Use verify-key parameter")
        (item "Check SPKI certificates - Verify authorization chain")
        (item "Maintain audit trail - Detect suspicious patterns")
        (item "Use HTTPS for HTTP transport - Prevent network attacks")
        (item "Backup signing keys - Use Shamir secret sharing"))
      (p "Defense in depth: cryptographic verification is primary, but transport security and operational practices add additional layers.")))
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
      (item "SDSI/SPKI")
      (item "Authorization certificates"))
    (p "Future extensions may add: - IPFS transport - Content-addressed distribution - Tor hidden services - Anonymous publication - Encrypted archives - Confidential distribution - Multi-signature releases - Threshold authorization"))
  (section
    "Test Coverage"
    (p "See test-replication.scm:")
    (code scheme ";; Test seal-publish to filesystem\n(seal-publish \"1.0.0\"\n              remote: \"/tmp/cyberspace-publish-test\"\n              message: \"Published to filesystem\")\n\n;; Verify archive exists\n(file-exists? \"/tmp/cyberspace-publish-test/vault-1.0.0.archive\")\n\n;; Verify audit entry created\n(audit-read sequence: 1)"))
  (section
    "References"
    (list
      (item "SDSI/SPKI - RFC 2693, RFC 2692")
      (item "Content-Addressed Storage - Git internals, IPFS")
      (item "Semantic Versioning - semver.org")
      (item "Ed25519 - Bernstein et al.")
      (item "Audit Trails - Memo-002 (Cryptographic Audit Trail)")))
  (section
    "Changelog"
    (list
      (item "2026-01-05")
      (item "Initial implementation and specification   - seal-publish with git/HTTP/filesystem support   - seal-subscribe with signature verification   - seal-synchronize with bidirectional sync  ")
      (item "Full audit trail integration  ")
      (item "Cryptographic archive format"))))

