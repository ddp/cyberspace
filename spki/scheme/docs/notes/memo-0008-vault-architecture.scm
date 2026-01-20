;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 8)
  (title "Vault Architecture")
  (section
    "Abstract"
    (p "This Memo specifies the Vault system for the Library of Cyberspace: cryptographically sealed version control with Simple Public Key Infrastructure (SPKI) authorization, progressive metadata, archival support, and integrated audit trails."))
  (section
    "Motivation"
    (p "Git is powerful but lacks:")
    (list
      (item "Cryptographic sealing - GPG signing is optional and awkward")
      (item "Authorization model - Anyone with access can commit")
      (item "Archival features - No first-class backup/restore")
      (item "Audit integration - History is mutable"))
    (p "These gaps leave security as an afterthought rather than a foundation, requiring external tools and manual discipline to achieve what should be built-in.")
    (p "The Vault wraps Git with:")
    (list
      (item "seal- commands that cryptographically sign operations")
      (item "SPKI certificates for authorization")
      (item "Three archive formats for different use cases")
      (item "Integrated audit trail for non-repudiation"))
    (p "The seal- prefix makes cryptographic operations explicit; security is not hidden behind flags or configuration but part of the command vocabulary.")
    (code "                    ╭────────────────────────────────╮\n                    │         CYBERSPACE VAULT       │\n                    ├────────────────────────────────┤\n                    │  seal-commit    seal-release   │\n                    │  seal-archive   seal-publish   │\n                    │  seal-verify    seal-subscribe │\n                    ├────────────────────────────────┤\n                    │         Audit Trail            │\n                    ├────────────────────────────────┤\n                    │         SPKI Certs             │\n                    ├────────────────────────────────┤\n                    │            Git                 │\n                    ╰────────────────────────────────╯"))
  (section
    "Core Operations"
    (subsection
      "seal-commit"
      (p "Stage and commit changes in one operation.")
      (code scheme "(seal-commit message\n  #!key files catalog subjects keywords description preserve)")
      (p "Parameters: - message - Commit message (required) - files - Specific files to stage (optional) - catalog - Enable catalog metadata - subjects - Subject headings - keywords - Search keywords - description - Extended description - preserve - Enable preservation metadata")
      (p "Process:")
      (list
        (item "Stage specified files (or all modified)")
        (item "Create git commit")
        (item "Save metadata (if catalog or preserve)")
        (item "Record in audit trail (if signing key configured)"))
      (p "Example:")
      (code scheme "(seal-commit \"Add authentication module\"\n  files: '(\"auth.scm\" \"auth-test.scm\")\n  catalog: #t\n  subjects: '(\"security\" \"authentication\")\n  keywords: '(\"login\" \"oauth\"))"))
    (subsection
      "seal-update"
      (p "Pull latest changes from remote.")
      (code scheme "(seal-update #!key branch)")
      (p "Like svn update - fetches and fast-forwards."))
    (subsection
      "seal-undo"
      (p "Undo changes.")
      (code scheme "(seal-undo #!key file hard)")
      (list
        (item "file")
        (item "Restore specific file - hard")
        (item "Discard all uncommitted changes")))
    (subsection
      "seal-history"
      (p "Show commit history.")
      (code scheme "(seal-history #!key count)")
      (p "Displays decorated graph log."))
    (subsection
      "seal-branch / seal-merge"
      (p "Branch and merge operations.")
      (code scheme "(seal-branch \"feature-auth\" #!key from)\n(seal-merge \"feature-auth\" #!key strategy)")))
  (section
    "Version Management"
    (subsection
      "seal-release"
      (p "Create cryptographically sealed release.")
      (code scheme "(seal-release version #!key message migrate-from)")
      (p "Parameters: - version - Semantic version (X.Y.Z required) - message - Release notes - migrate-from - Previous version for migration tracking")
      (p "Process:")
      (list
        (item "Validate semantic version format")
        (item "Get current commit hash")
        (item "Create annotated git tag")
        (item "Sign with SPKI (if configured)")
        (item "Create migration marker (if migrate-from specified)"))
      (p "Signature Storage:")
      (code scheme ";; .vault/releases/1.0.0.sig\n(signature\n  (version \"1.0.0\")\n  (hash \"abc123...\")\n  (manifest \"(release \\\"1.0.0\\\" \\\"abc123\\\" 1767685100)\")\n  (signature #${ed25519-signature}))"))
    (subsection
      "seal-verify"
      (p "Verify release signature.")
      (code scheme "(seal-verify version #!key verify-key)")
      (p "Process:")
      (list
        (item "Load signature file")
        (item "Recompute manifest hash")
        (item "Verify Ed25519 signature"))))
  (section
    "Archival System"
    (subsection
      "seal-archive"
      (p "Create sealed archive of a version.")
      (code scheme "(seal-archive version #!key format output)")
      (p "Formats:")
      (p "#### Tarball (default)")
      (code scheme "(seal-archive \"1.0.0\" format: 'tarball)")
      (list
        (item "Standard gzipped tarball")
        (item "No history included")
        (item "Smallest size"))
      (p "#### Git Bundle")
      (code scheme "(seal-archive \"1.0.0\" format: 'bundle)")
      (list
        (item "Full git history")
        (item "Can clone directly")
        (item "Medium size"))
      (p "#### Cryptographic (legacy)")
      (code scheme "(seal-archive \"1.0.0\" format: 'cryptographic)")
      (list
        (item "Tarball + SHA-512 hash + Ed25519 signature")
        (item "Tamper-evident")
        (item "Manifest for verification"))
      (p "#### Zstd+Age (preferred)")
      (code scheme "(seal-archive \"1.0.0\" format: 'zstd-age)")
      (list
        (item "Zstd compression (faster, better ratio than gzip)")
        (item "Age encryption (X25519/Ed25519 compatible)")
        (item "SHA-512 hash + Ed25519 signature")
        (item "Encrypted at rest")))
      (p "Cryptographic Archive Structure:")
      (code "vault-1.0.0.archive        # Manifest\nvault-1.0.0.archive.tar.gz # Tarball (cryptographic)")
      (p "Zstd+Age Archive Structure:")
      (code "vault-1.0.0.archive            # Manifest\nvault-1.0.0.archive.tar.zst.age # Encrypted archive")
      (p "Manifest (cryptographic):")
      (code scheme "(sealed-archive\n  (version \"1.0.0\")\n  (format cryptographic)\n  (tarball \"vault-1.0.0.archive.tar.gz\")\n  (hash \"sha512:...\")\n  (signature \"ed25519:...\"))")
      (p "Manifest (zstd-age):")
      (code scheme "(sealed-archive\n  (version \"1.0.0\")\n  (format zstd-age)\n  (archive \"vault-1.0.0.archive.tar.zst.age\")\n  (compression zstd)\n  (encryption age)\n  (recipients (\"age1...\"))\n  (hash \"sha512:...\")\n  (signature \"ed25519:...\"))"))
    (subsection
      "seal-restore"
      (p "Restore from sealed archive.")
      (code scheme "(seal-restore archive #!key verify-key target identity)")
      (p "Parameters: - verify-key - SPKI public key for signature verification - target - Extraction directory - identity - Age identity file for decryption (zstd-age format)")
      (p "Process:")
      (list
        (item "Read manifest")
        (item "Verify hash (archive integrity)")
        (item "Verify signature (if key provided)")
        (item "Decrypt (zstd-age only, requires identity)")
        (item "Extract to target directory"))))
  (section
    "Replication Layer"
    (p "See Memo-0002 for complete specification.")
    (subsection
      "seal-publish"
      (p "Publish release to remote.")
      (code scheme "(seal-publish version #!key remote archive-format message)")
      (p "Supports: - Git remotes (push tags) - HTTP endpoints (POST) - Filesystem paths (copy)"))
    (subsection
      "seal-subscribe"
      (p "Subscribe to releases from remote.")
      (code scheme "(seal-subscribe remote #!key target verify-key)")
      (p "Downloads and optionally verifies remote releases."))
    (subsection
      "seal-synchronize"
      (p "Bidirectional sync.")
      (code scheme "(seal-synchronize remote #!key direction verify-key)")))
  (section
    "Configuration"
    (subsection
      "vault-init"
      (p "Initialize vault for repository.")
      (code scheme "(vault-init #!key signing-key)")
      (p "Sets up: - Signing key configuration - Audit trail directory - Metadata directory"))
    (subsection
      "vault-config"
      (p "Get/set configuration.")
      (code scheme "(vault-config 'signing-key)              ; Get\n(vault-config 'signing-key some-key)     ; Set")
      (p "Configuration Options:")
      (table
        (header "Key " "Type " "Description ")
        (row "signing-key " "blob " "Ed25519 private key for signing ")
        (row "verify-key " "string " "Path to verification public key ")
        (row "archive-format " "symbol " "Default: tarball, bundle, cryptographic, or zstd-age ")
        (row "age-recipients " "list " "Age public keys for encryption (zstd-age format) ")
        (row "age-identity " "string " "Path to age identity file for decryption ")
        (row "migration-dir " "string " "Directory for migration scripts ")
        (row "track-metadata " "boolean " "Auto-stage metadata files ")
        (row "publish-remote " "string " "Default publication target ")
        (row "subscribe-dir " "string " "Directory for subscriptions "))))
  (section
    "Directory Structure"
    (code "project/\n├── .vault/\n│   ├── metadata/           # Commit metadata files\n│   │   ├── abc123.sexp\n│   │   └── def456.sexp\n│   ├── releases/           # Release signatures\n│   │   ├── 1.0.0.sig\n│   │   └── 1.1.0.sig\n│   ├── audit/              # Audit trail\n│   │   ├── 1.sexp\n│   │   └── 2.sexp\n│   └── subscriptions/      # Downloaded releases\n│       └── vault-1.0.0.archive\n├── migrations/             # Version migration scripts\n│   └── 1.0.0-to-2.0.0.scm\n└── .git/                   # Git repository"))
  (section
    "Migration Support"
    (subsection
      "Creating Migrations"
      (code scheme "(seal-release \"2.0.0\" migrate-from: \"1.0.0\")")
      (p "Generates template:")
      (code scheme ";; migrations/1.0.0-to-2.0.0.scm\n;;; Migration: 1.0.0 -> 2.0.0\n;;; Generated: 1767685100\n\n(define (migrate-1.0.0-to-2.0.0)\n  ;; Define migration logic here\n  #t)\n\n(migrate-1.0.0-to-2.0.0)"))
    (subsection
      "Running Migrations"
      (code scheme "(seal-migrate \"1.0.0\" \"2.0.0\" #!key script dry-run)")))
  (section
    "Integrity Checking"
    (subsection
      "seal-check"
      (p "Verify vault integrity.")
      (code scheme "(seal-check #!key deep)")
      (p "Checks: - Git repository health (git fsck) - Release signature validity (if deep) - Audit trail chain (if deep)")))
  (section
    "Security Model"
    (subsection
      "Signing Key Handling"
      (code scheme ";; Key is 64-byte Ed25519 secret key\n;; First 32 bytes: seed\n;; Last 32 bytes: public key\n\n(define (get-vault-principal signing-key)\n  \"Extract public key from signing key\"\n  (blob-copy signing-key 32 32))"))
    (subsection
      "Authorization Flow"
      (list
        (item "Configure: (vault-init signing-key: key)")
        (item "Operate: (seal-commit ...) signs with configured key")
        (item "Audit: Entry includes actor's public key")
        (item "Verify: (seal-verify ...) checks signature")))
    (subsection
      "Threat Mitigations"
      (table
        (header "Threat " "Mitigation ")
        (row "Unauthorized commits " "SPKI certificates required ")
        (row "Release tampering " "Ed25519 signatures ")
        (row "History rewriting " "Audit trail non-repudiation ")
        (row "Archive corruption " "SHA-512 hash verification "))))
  (section
    "Integration Points"
    (subsection
      "With Audit Trail (Memo-003)"
      (p "All vault operations create audit entries:")
      (code scheme "(audit-append\n  actor: (get-vault-principal signing-key)\n  action: '(seal-commit \"hash123\")\n  motivation: message)"))
    (subsection
      "With SPKI (Memo-004)"
      (p "Signing keys are SPKI principals:")
      (code scheme "(make-key-principal (get-vault-principal signing-key))"))
    (subsection
      "With Metadata (Memo-005)"
      (p "Progressive metadata via seal-commit parameters:")
      (code scheme "(seal-commit \"msg\" preserve: #t)  ; Full preservation")))
  (section
    "Usage Examples"
    (subsection
      "Basic Workflow"
      (code scheme ";; Initialize\n(vault-init signing-key: my-key)\n\n;; Daily work\n(seal-commit \"Add feature\")\n(seal-commit \"Fix bug\")\n\n;; Release\n(seal-release \"1.0.0\" message: \"Initial release\")\n\n;; Archive\n(seal-archive \"1.0.0\" format: 'cryptographic)\n\n;; Verify\n(seal-verify \"1.0.0\" verify-key: \"my.public\")"))
    (subsection
      "Federation Workflow"
      (code scheme ";; Publisher\n(seal-release \"1.0.0\")\n(seal-publish \"1.0.0\" remote: \"/shared/releases\")\n\n;; Subscriber\n(seal-subscribe \"/shared/releases\" verify-key: publisher-pub)\n\n;; Bidirectional\n(seal-synchronize peer-remote direction: 'both)")))
  (section
    "Document Formats"
    (p "The Vault preserves documents in canonical open formats:")
    (table
      (header "Format " "Extension " "Purpose ")
      (row "Text " ".txt " "Universal compatibility, IETF tradition, immortal ")
      (row "PostScript " ".ps " "Archival, printing, open since 1984 ")
      (row "Hypertext Markup Language " ".html " "Web viewing "))
    (p "All formats are first-class citizens in the Vault. RFCs and declarations SHOULD be published in all three formats for maximum preservation and accessibility. No proprietary formats."))
  (section
    "References"
    (list
      (item "Git Internals - Plumbing and Porcelain")
      (item "Memo-0002: Replication Layer")
      (item "Memo-0003: Cryptographic Audit Trail")
      (item "Memo-0004: SPKI Authorization")
      (item "Memo-0005: Progressive Metadata Levels")
      (item "Semantic Versioning 2.0.0")))
  (section
    "Changelog"
    (list
      (item "2026-01-06")
      (item "Initial specification"))))

