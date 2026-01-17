;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 6)
  (title "Progressive Metadata Levels")
  (section
    "Abstract"
    (p "This Memo specifies progressive metadata levels for vault commits, enabling configurable richness from minimal overhead to full preservation context. Three levels serve different use cases: minimal (fast iteration), catalog (discovery), and preserve (archival)."))
  (section
    "Motivation"
    (p "Different commits deserve different metadata:")
    (list
      (item "Quick fix: Just record it happened")
      (item "Feature release: Add searchable keywords")
      (item "Archival snapshot: Capture full environment"))
    (p "Traditional VCS provides one-size-fits-all commit messages. Cyberspace provides progressive levels:")
    (p "1. Minimal - Hash, timestamp, message (default) 2. Catalog - Add subjects, keywords, descriptions (discovery) 3. Preserve - Add environment, dependencies, git state (archival)"))
  (section
    "Specification"
    (subsection
      "Level 1: Minimal (Default)"
      (p "Every commit includes:")
      (code scheme "(commit-metadata\n  (hash \"abc123...\")\n  (timestamp 1767685100)\n  (message \"Fix typo in README\"))")
      (p "Usage:")
      (code scheme "(seal-commit \"Fix typo in README\")")
      (p "This is the default. No extra flags needed. Git handles storage."))
    (subsection
      "Level 2: Catalog"
      (p "Adds discovery metadata:")
      (code scheme "(commit-metadata\n  (hash \"def456...\")\n  (timestamp 1767685200)\n  (message \"Implement user authentication\")\n  (catalog\n    (subjects \"authentication\" \"security\")\n    (keywords \"login\" \"oauth\" \"jwt\")\n    (description \"Added OAuth2 authentication flow with JWT tokens\")))")
      (p "Usage:")
      (code scheme "(seal-commit \"Implement user authentication\"\n  catalog: #t\n  subjects: '(\"authentication\" \"security\")\n  keywords: '(\"login\" \"oauth\" \"jwt\")\n  description: \"Added OAuth2 authentication flow with JWT tokens\")")
      (p "Purpose: Enable search and categorization without full environmental capture."))
    (subsection
      "Level 3: Preserve"
      (p "Adds archival metadata:")
      (code scheme "(commit-metadata\n  (hash \"789abc...\")\n  (timestamp 1767685300)\n  (message \"Release v2.0.0\")\n  (preservation\n    (environment\n      (platform \"darwin\")\n      (hostname \"dev-machine\")\n      (chicken-version \"5.x\")\n      (timestamp 1767685300))\n    (dependencies\n      (egg \"srfi-1\" \"1.0\")\n      (egg \"crypto-ffi\" \"0.1\"))\n    (git-state\n      (branch \"main\")\n      (remote \"git@github.com:ddp/cyberspace.git\"))))")
      (p "Usage:")
      (code scheme "(seal-commit \"Release v2.0.0\"\n  preserve: #t)")
      (p "Purpose: Capture everything needed to understand and reproduce the commit environment.")))
  (section
    "Metadata Fields"
    (subsection
      "Catalog Fields"
      (table
        (header "Field " "Type " "Description ")
        (row "subjects " "list " "Library of Congress style subject headings ")
        (row "keywords " "list " "Free-form search terms ")
        (row "description " "string " "Extended description (beyond commit message) ")))
    (subsection
      "Preservation Fields"
      (table
        (header "Field " "Type " "Description ")
        (row "environment.platform " "string " "OS type (darwin, linux, etc.) ")
        (row "environment.hostname " "string " "Machine name ")
        (row "environment.chicken-version " "string " "Scheme implementation version ")
        (row "environment.timestamp " "integer " "Unix epoch seconds ")
        (row "dependencies " "list " "Installed eggs/libraries ")
        (row "git-state.branch " "string " "Current branch ")
        (row "git-state.remote " "string " "Remote URL "))))
  (section
    "Storage"
    (p "Metadata stored in .vault/metadata/:")
    (code ".vault/\n  metadata/\n    abc123.sexp\n    def456.sexp\n    789abc.sexp")
    (p "Filename is commit hash. Content is S-expression metadata.")
    (subsection
      "Optional Git Tracking"
      (code scheme "(vault-config 'track-metadata #t)")
      (p "When enabled, metadata files are staged for the next commit, creating a self-documenting archive.")))
  (section
    "Implementation"
    (subsection
      "save-commit-metadata"
      (code scheme "(define (save-commit-metadata commit-hash\n          #!key message catalog subjects keywords description preserve)\n  \"Save optional metadata for a commit\"\n  (create-directory \".vault/metadata\" #t)\n\n  (let ((metadata-file (sprintf \".vault/metadata/~a.sexp\" commit-hash)))\n\n    ;; Build metadata structure\n    (let ((metadata (list 'commit-metadata\n                         (list 'hash commit-hash)\n                         (list 'timestamp (current-seconds))\n                         (list 'message message))))\n\n      ;; Add catalog if requested\n      (when (or catalog subjects keywords description)\n        (set! metadata (append metadata (list (build-catalog ...)))))\n\n      ;; Add preservation if requested\n      (when preserve\n        (set! metadata (append metadata (list (build-preservation ...)))))\n\n      ;; Write metadata file\n      (with-output-to-file metadata-file\n        (lambda ()\n          (write metadata)\n          (newline))))))"))
    (subsection
      "Environment Capture"
      (code scheme "(define (get-environment-snapshot)\n  \"Capture current build environment\"\n  ((platform ,(or (get-environment-variable \"OSTYPE\") \"unknown\"))\n    (hostname ,(or (get-environment-variable \"HOSTNAME\") \"unknown\"))\n    (chicken-version \"5.x\")\n    (timestamp ,(current-seconds))))\n\n(define (get-dependencies-snapshot)\n  \"Capture current dependencies\"\n  ;; Could scan imports, check installed eggs\n  '())\n\n(define (get-git-state-snapshot)\n  \"Capture git repository state\"\n  (let ((branch (with-input-from-pipe \"git branch --show-current\" read-line))\n        (remote (with-input-from-pipe \"git remote -v\" read-line)))\n    ((branch ,branch)\n      (remote ,remote))))")))
  (section
    "Use Cases"
    (subsection
      "Daily Development (Minimal)"
      (code scheme "(seal-commit \"WIP: refactoring auth module\")\n(seal-commit \"Fix off-by-one error\")\n(seal-commit \"Update dependencies\")")
      (p "Fast, lightweight, no overhead."))
    (subsection
      "Feature Completion (Catalog)"
      (code scheme "(seal-commit \"Add two-factor authentication\"\n  catalog: #t\n  subjects: '(\"authentication\" \"security\" \"2FA\")\n  keywords: '(\"totp\" \"authenticator\" \"login\")\n  description: \"Implements TOTP-based 2FA per RFC 6238\")")
      (p "Enables later discovery: \"find all commits about authentication\""))
    (subsection
      "Release Snapshot (Preserve)"
      (code scheme "(seal-commit \"Release v2.0.0\"\n  preserve: #t)")
      (p "Captures full environment for reproducibility and forensics.")))
  (section
    "Query Support"
    (p "Future enhancement: query interface for metadata.")
    (code scheme ";; Find by subject\n(vault-search subjects: '(\"authentication\"))\n\n;; Find by keyword\n(vault-search keywords: '(\"oauth\"))\n\n;; Find by date range\n(vault-search from: \"2026-01-01\" to: \"2026-01-31\")\n\n;; Find with preservation data\n(vault-search has-preservation: #t)"))
  (section
    "Security Considerations"
    (subsection
      "Information Leakage"
      (p "Preservation metadata captures: - Hostname (could reveal infrastructure) - Platform (could reveal vulnerabilities) - Dependencies (could reveal attack surface)")
      (p "Recommendation: Use preserve level only for internal archives. Strip when publishing externally."))
    (subsection
      "Metadata Integrity"
      (p "Metadata files are not automatically signed. For tamper-evidence: 1. Enable track-metadata to include in commits 2. Use seal-release for cryptographic sealing 3. Audit trail captures metadata operations")))
  (section
    "Design Rationale"
    (subsection
      "Why Not Always Full Metadata?"
      (p "1. Performance: Environment capture adds latency 2. Noise: Not every commit needs forensic detail 3. Privacy: Some metadata reveals sensitive info 4. Storage: Full metadata increases repository size"))
    (subsection
      "Why S-expressions?"
      (p "1. Readable: Human-inspectable without tools 2. Parseable: Machine-processable 3. Extensible: Add fields without schema changes 4. Native: Scheme can read/write directly"))
    (subsection
      "Why Separate Files?"
      (p "1. Git-friendly: Small files diff well 2. Query-friendly: Can glob/grep metadata 3. Optional: Metadata doesn't bloat git objects 4. Flexible: Can delete without rewriting history")))
  (section
    "References"
    (p "1. Dublin Core Metadata Initiative (DCMI) 2. Library of Congress Subject Headings (LCSH) 3. Software Heritage Archive Metadata 4. Reproducible Builds Project"))
  (section
    "Changelog"
    (list
      (item "2026-01-06")
      (item "Initial specification"))))

