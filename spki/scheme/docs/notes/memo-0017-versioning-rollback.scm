;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 17)
  (title "Versioning and Rollback")
  (section
    "Abstract"
    (p "This Memo specifies user-visible versioning and rollback semantics for Cyberspace vaults, providing clear mental models for version management, safe rollback operations, and recovery from mistakes."))
  (section
    "Motivation"
    (p "Users need simple answers to simple questions:")
    (list
      (item "What version am I on?")
      (item "What versions exist?")
      (item "How do I go back?")
      (item "What if I make a mistake?"))
    (p "These questions are universal but git answers them with mechanisms rather than semantics, requiring users to understand implementation details.")
    (p "Git provides mechanisms. Cyberspace provides semantics:")
    (code "seal-version         → \"2.1.0\"\nseal-versions        → [1.0.0, 1.1.0, 2.0.0, 2.1.0]\nseal-rollback 2.0.0  → Done. Now at 2.0.0.\nseal-recover         → Here's what you can recover."))
  (section
    "Specification"
    (subsection
      "Version Model"
      (code "                         HEAD\n                          ↓\n    1.0.0 ──→ 1.1.0 ──→ 2.0.0 ──→ 2.1.0\n      │                   │\n      │                   └── seal-rollback target\n      │\n      └── seal-archive snapshots")
      (p "Versions are semantic (X.Y.Z), immutable, signed.")
      (p "HEAD is current working state.")
      (p "Rollback creates forward commit that restores past state."))
    (subsection
      "Core Operations"
      (p "#### seal-version")
      (p "Report current version.")
      (code scheme "(seal-version)\n;; => \"2.1.0\" or \"2.1.0+3\" (3 commits past release)")
      (p "Output format: - X.Y.Z - Exactly at release - X.Y.Z+N - N commits past release - X.Y.Z-dev - Development branch - unversioned - No releases yet")
      (p "#### seal-versions")
      (p "List all versions.")
      (code scheme "(seal-versions)\n;; => (\"1.0.0\" \"1.1.0\" \"2.0.0\" \"2.1.0\")\n\n(seal-versions verbose: #t)\n;; =>\n;; 1.0.0  2026-01-01  \"Initial release\"\n;; 1.1.0  2026-01-05  \"Bug fixes\"\n;; 2.0.0  2026-01-10  \"New governance model\"\n;; 2.1.0  2026-01-15  \"Performance improvements\"")
      (p "#### seal-rollback")
      (p "Roll back to specific version.")
      (code scheme "(seal-rollback \"2.0.0\")")
      (p "Process:")
      (list
        (item "Verify version exists")
        (item "Check for uncommitted changes (abort or stash)")
        (item "Create rollback commit with contents of target version")
        (item "Record in audit trail")
        (item "Optionally create rollback tag"))
      (p "Rollback commit message:")
      (code "Rollback to 2.0.0\n\nRestored vault state to version 2.0.0.\nPrevious HEAD was 2.1.0+3.\n\nReason: [user-provided or \"Manual rollback\"]")
      (p "NOT a git reset. History preserved. Rollback is a forward operation.")
      (p "#### seal-diff")
      (p "Compare versions.")
      (code scheme "(seal-diff \"2.0.0\" \"2.1.0\")\n;; Shows what changed between versions\n\n(seal-diff \"2.0.0\")\n;; Shows what changed since 2.0.0")
      (p "#### seal-recover")
      (p "Recovery options for mistakes.")
      (code scheme "(seal-recover)\n;; =>\n;; Recovery options:\n;;   1. Uncommitted changes (stashed 5 minutes ago)\n;;   2. Last commit (seal-undo)\n;;   3. Version 2.1.0 (seal-rollback \"2.1.0\")\n;;   4. Archive vault-2.0.0.archive (seal-restore)")))
  (section
    "Rollback Semantics"
    (subsection
      "Forward Rollback (Default)"
      (code "Before:  1.0.0 → 1.1.0 → 2.0.0 → 2.1.0 → HEAD\n                          ↑\n                     rollback target\n\nAfter:   1.0.0 → 1.1.0 → 2.0.0 → 2.1.0 → [rollback commit]\n                          │                      │\n                          └──────────────────────┘\n                              contents match\n")
      (p "History preserved. Audit trail shows rollback."))
    (subsection
      "Hard Rollback (Dangerous)"
      (code scheme "(seal-rollback \"2.0.0\" hard: #t)")
      (p "Actually resets to version. Destroys history.")
      (p "Requires: - Explicit hard: #t flag - Confirmation prompt - Audit entry before destruction"))
    (subsection
      "Rollback with Stash"
      (code scheme "(seal-rollback \"2.0.0\" stash: #t)")
      (p "Stashes uncommitted changes before rollback. Can recover with:")
      (code scheme "(seal-stash-pop)")))
  (section
    "Version Tags"
    (subsection
      "Automatic Tagging"
      (code scheme "(seal-release \"2.1.0\")\n;; Creates:\n;;   - Git tag: 2.1.0\n;;   - Signature: .vault/releases/2.1.0.sig\n;;   - Audit entry"))
    (subsection
      "Rollback Tags"
      (code scheme "(seal-rollback \"2.0.0\" tag: \"rollback-2026-01-15\")\n;; Creates additional tag marking rollback point"))
    (subsection
      "Tag Listing"
      (code scheme "(seal-tags)\n;; =>\n;; 1.0.0              2026-01-01  release\n;; 1.1.0              2026-01-05  release\n;; 2.0.0              2026-01-10  release\n;; 2.1.0              2026-01-15  release\n;; rollback-2026-01-15 2026-01-15  rollback")))
  (section
    "Recovery Scenarios"
    (subsection
      "Scenario 1: Bad Commit"
      (code scheme ";; Oops, committed broken code\n(seal-undo)                    ; Undo last commit\n;; or\n(seal-rollback \"2.1.0\")        ; Back to last release"))
    (subsection
      "Scenario 2: Bad Release"
      (code scheme ";; Released 2.2.0 but it's broken\n(seal-rollback \"2.1.0\")        ; Back to good version\n(seal-release \"2.2.1\")         ; Patch release"))
    (subsection
      "Scenario 3: Lost Changes"
      (code scheme ";; Accidentally discarded work\n(seal-recover)                 ; See options\n(seal-stash-pop)               ; If stashed\n;; or\n(seal-reflog)                  ; Find lost commits"))
    (subsection
      "Scenario 4: Corrupted Vault"
      (code scheme ";; Something went very wrong\n(seal-restore \"vault-2.0.0.archive\" verify-key: \"alice.pub\")")))
  (section
    "Audit Integration"
    (p "Every version operation recorded:")
    (code scheme "(audit-entry\n  (action\n    (verb seal-rollback)\n    (object \"2.0.0\")\n    (parameters\n      (from \"2.1.0+3\")\n      (method forward)\n      (reason \"Production incident\")))\n  (seal ...))")
    (p "Audit trail answers: - Who rolled back? - When? - From what version? - Why? (if reason provided)"))
  (section
    "CLI Interface"
    (code bash "# Current version\n$ seal version\n2.1.0+3\n\n# List versions\n$ seal versions\n1.0.0   2026-01-01   Initial release\n1.1.0   2026-01-05   Bug fixes\n2.0.0   2026-01-10   New governance model\n2.1.0   2026-01-15   Performance improvements\n\n# Rollback\n$ seal rollback 2.0.0\nRolling back to 2.0.0...\n✓ Rollback complete. Now at 2.0.0.\n\n# Rollback with reason\n$ seal rollback 2.0.0 --reason \"Production incident #123\"\n\n# Compare versions\n$ seal diff 2.0.0 2.1.0\n M config.scm\n A new-feature.scm\n D deprecated.scm\n\n# Recovery options\n$ seal recover\nRecovery options:\n  1. seal undo          - Undo last commit\n  2. seal rollback 2.1.0 - Return to last release\n  3. seal stash pop     - Recover stashed changes"))
  (section
    "Safety Mechanisms"
    (subsection
      "Uncommitted Changes"
      (code scheme "(seal-rollback \"2.0.0\")\n;; Error: Uncommitted changes detected.\n;; Use --stash to save changes, or --force to discard."))
    (subsection
      "Protected Versions"
      (code scheme "(vault-config 'protected-versions '(\"1.0.0\" \"2.0.0\"))\n\n(seal-rollback \"0.9.0\")\n;; Warning: Rolling back past protected version 1.0.0\n;; This may break compatibility. Continue? [y/N]"))
    (subsection
      "Rollback Limits"
      (code scheme "(vault-config 'max-rollback-distance 10)\n\n(seal-rollback \"0.1.0\")\n;; Error: Rollback distance (20 versions) exceeds limit (10).\n;; Use --force to override.")))
  (section
    "Implementation"
    (subsection
      "seal-rollback Implementation"
      (code scheme "(define (seal-rollback version #!key hard stash force reason tag)\n  \"Roll back vault to specified version\"\n\n  ;; Validate version exists\n  (unless (tag-exists? version)\n    (error \"Version not found\" version))\n\n  ;; Check for uncommitted changes\n  (when (uncommitted-changes?)\n    (cond\n      (stash (seal-stash))\n      (force (void))\n      (else (error \"Uncommitted changes. Use stash: or force:\"))))\n\n  ;; Record current state\n  (let ((current (seal-version)))\n\n    ;; Perform rollback\n    (if hard\n        (hard-rollback! version)\n        (forward-rollback! version reason))\n\n    ;; Create tag if requested\n    (when tag\n      (run-command \"git\" \"tag\" tag))\n\n    ;; Audit\n    (audit-append\n      actor: (get-vault-principal (vault-config 'signing-key))\n      action: (list 'seal-rollback version)\n      motivation: (or reason (sprintf \"Rollback from ~a to ~a\" current version)))\n\n    (print \"✓ Rolled back to \" version)))\n\n(define (forward-rollback! version reason)\n  \"Create rollback commit (preserves history)\"\n  (run-command \"git\" \"checkout\" version \"--\" \".\")\n  (run-command \"git\" \"commit\" \"-m\"\n    (sprintf \"Rollback to ~a\\n\\n~a\" version (or reason \"\"))))\n\n(define (hard-rollback! version)\n  \"Reset to version (destroys history)\"\n  (print \"WARNING: Hard rollback destroys history\")\n  (run-command \"git\" \"reset\" \"--hard\" version))")))
  (section
    "Security Considerations"
    (subsection
      "Rollback Attacks"
      (p "Attacker forces rollback to vulnerable version.")
      (p "Mitigation: - Threshold signatures for rollback (Memo-008) - Protected version list - Audit trail detection"))
    (subsection
      "History Manipulation"
      (p "Hard rollback can hide evidence.")
      (p "Mitigation: - Prefer forward rollback - Audit before hard rollback - Federation replication preserves history")))
  (section
    "References"
    (list
      (item "Semantic Versioning 2.0.0 (semver.org)")
      (item "Git Reset, Checkout, and Revert (git-scm.com)")
      (item "Memo-003: Cryptographic Audit Trail")
      (item "Memo-006: Vault System Architecture")))
  (section
    "Changelog"
    (list
      (item "2026-01-06")
      (item "Initial specification"))))

