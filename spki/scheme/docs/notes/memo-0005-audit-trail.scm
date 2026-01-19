(memo
  (number 5)
  (title "Cryptographic Audit Trail")
  (section
    "Abstract"
    (p "This Memo specifies the cryptographic audit trail system for the Library of Cyberspace, providing tamper-evident, hash-chained logging with Simple Public Key Infrastructure (SPKI) principal attribution and Ed25519 signatures."))
  (section
    "Motivation"
    (blockquote "The first principle is that you must not fool yourself—and you are the easiest person to fool. — Richard Feynman")
    (p "Distributed systems require accountability. Who did what, when, and under whose authority? Without cryptographic audit trails, the answer is always \"we think so\" rather than \"we can prove it.\"")
    (p "Every security breach postmortem asks the same questions: What happened? When? Who had access? Could the logs have been tampered with? Traditional logging cannot answer these questions with certainty. Cyberspace audit trails can.")
    (subsection
      "Heritage"
      (p "Inspired by VMS cluster-wide audit (1993). See Memo-0009 section 7.7 for design heritage."))
    (subsection
      "The Problem"
      (p "Traditional logging fails on all counts:")
      (list
        (item "Tamperable: Text files can be edited after the fact")
        (item "Anonymous: No cryptographic identity binds actor to action")
        (item "Disconnected: No provable ordering between entries")
        (item "Unverifiable: No mathematical proof of integrity"))
      (p "Cyberspace audit trails provide:")
      (list
        (item "Content-addressed entries - Tamper-evident by hash")
        (item "Hash-chained structure - Append-only ordering")
        (item "SPKI attribution - Cryptographic actor identity")
        (item "Ed25519 seals - Mathematical proof of authenticity")
        (item "Dual context - Human-readable motivation + machine-parseable environment"))))
  (section
    "Specification"
    (subsection
      "Entry Structure"
      (code scheme "(audit-entry\n  (id \"sha512:b14471cd57ea557f...\")\n  (timestamp \"2026-01-05 23:38:20Z\")\n  (sequence 1)\n  (parent-id \"sha512:previous...\")\n  (actor\n    (principal #${public-key-blob})\n    (authorization-chain))\n  (action\n    (verb seal-publish)\n    (object \"1.0.0\")\n    (parameters \"/path/to/remote\"))\n  (context\n    (motivation \"Published to filesystem\")\n    (language \"en\"))\n  (environment\n    (platform \"darwin\")\n    (timestamp 1767685100))\n  (seal\n    (algorithm \"ed25519-sha512\")\n    (content-hash \"...\")\n    (signature \"...\")))"))
    (subsection
      "Core Fields"
      (table
        (header "Field " "Type " "Description ")
        (row "id " "string " "Content-addressed hash (SHA-512, first 32 hex chars) ")
        (row "timestamp " "string " "ISO 8601 UTC (YYYY-MM-DD HH:MM:SSZ) ")
        (row "sequence " "integer " "Monotonic counter within audit trail ")
        (row "parent-id " "string/nil " "ID of previous entry (hash chain) ")
        (row "actor " "record " "SPKI principal who performed action ")
        (row "action " "record " "What was done (verb, object, parameters) ")
        (row "context " "record " "Human-readable motivation ")
        (row "environment " "alist " "Machine environment snapshot ")
        (row "seal " "record " "Cryptographic signature ")))
    (subsection
      "Actor Record"
      (p "Every action has an actor. Not a username—a cryptographic identity that can be verified mathematically.")
      (code scheme "(define-record-type <audit-actor>\n  (make-audit-actor principal authorization-chain)\n  audit-actor?\n  (principal actor-principal)              ; Public key blob\n  (authorization-chain actor-authorization-chain))  ; SPKI cert chain")
      (p "The actor is identified by:")
      (list
        (item "Principal: Ed25519 public key (32 bytes) - unforgeable identity")
        (item "Authorization chain: Optional SPKI certificate chain proving delegation"))
      (p "The authorization chain answers \"under whose authority?\" - crucial for auditing delegated actions."))
    (subsection
      "Action Record"
      (p "Actions are structured as verb-object-parameters, mirroring natural language: \"Alice committed version 1.0 to the vault.\"")
      (code scheme "(define-record-type <audit-action>\n  (make-audit-action verb object parameters)\n  audit-action?\n  (verb action-verb)        ; Symbol: seal-commit, seal-publish, etc.\n  (object action-object)    ; Primary target\n  (parameters action-parameters))  ; Additional arguments")
      (p "Standard verbs:")
      (table
        (header "Verb " "Meaning ")
        (row "seal-commit " "Version control commit to local vault ")
        (row "seal-publish " "Release publication to remote ")
        (row "seal-subscribe " "Subscription to remote feed ")
        (row "seal-synchronize " "Bidirectional sync with peer ")
        (row "seal-release " "Version tagging for distribution ")))
    (subsection
      "Context Record"
      (p "Machines record what happened. Humans need to know why. The context record captures motivation in natural language—the commit message, the reason for the release, the justification for the access.")
      (code scheme "(define-record-type <audit-context>\n  (make-audit-context motivation relates-to language)\n  audit-context?\n  (motivation context-motivation)    ; Human explanation\n  (relates-to context-relates-to)    ; Related entries\n  (language context-language))       ; ISO 639-1 code")
      (p "Context provides:")
      (list
        (item "Motivation: Why the action was taken, in the actor's own words")
        (item "Relates-to: Cross-references to related audit entries")
        (item "Language: ISO 639-1 code for internationalization"))
      (p "Six months later, \"Fixed the bug\" means nothing. \"Fixed CVE-2026-1234 buffer overflow in certificate parser\" means everything."))
    (subsection
      "Seal Record"
      (code scheme "(define-record-type <audit-seal>\n  (make-audit-seal algorithm content-hash signature)\n  audit-seal?\n  (algorithm seal-algorithm)        ; \"ed25519-sha512\"\n  (content-hash seal-content-hash)  ; SHA-512 of unsealed entry\n  (signature seal-signature))       ; Ed25519 signature")))
  (section
    "Operations"
    (subsection
      "audit-init"
      (p "Initialize audit trail for a vault.")
      (code scheme "(audit-init signing-key: key audit-dir: \".vault/audit\")"))
    (subsection
      "audit-append"
      (p "Create and sign a new audit entry.")
      (code scheme "(audit-append\n  actor: public-key-blob\n  action: '(seal-commit \"hash123\")\n  motivation: \"Added new feature\"\n  signing-key: private-key-blob)")
      (p "Process:")
      (list
        (item "Increment sequence counter")
        (item "Get parent entry ID (hash chain link)")
        (item "Build unsealed entry structure")
        (item "Compute SHA-512 hash of canonical S-expression")
        (item "Sign hash with Ed25519")
        (item "Create seal record")
        (item "Save entry to disk")))
    (subsection
      "audit-verify"
      (p "Verify cryptographic seal on an entry.")
      (code scheme "(audit-verify entry public-key: key)")
      (p "Verification steps:")
      (list
        (item "Reconstruct unsealed entry")
        (item "Compute SHA-512 hash")
        (item "Compare with stored content-hash")
        (item "Verify Ed25519 signature")))
    (subsection
      "audit-chain"
      (p "Verify the entire audit chain from genesis to present. One broken link invalidates everything after it.")
      (code scheme "(audit-chain verify-key: public-key)")
      (p "Verifies:")
      (list
        (item "Each entry's signature is valid")
        (item "Parent-id references form unbroken chain")
        (item "Sequence numbers are strictly monotonic"))
      (p "A valid chain proves no entries were inserted, deleted, or modified after signing."))
    (subsection
      "audit-read"
      (p "Read specific audit entry.")
      (code scheme "(audit-read sequence: 42)\n(audit-read id: \"sha512:...\")")))
  (section
    "Storage Format"
    (p "Simplicity over cleverness. Entries are individual S-expression files, one per action, named by sequence number.")
    (code ".vault/audit/\n  1.sexp\n  2.sexp\n  3.sexp\n  ...")
    (p "This format trades storage density for operational simplicity:")
    (list
      (item "Sequential reads: cat the files in order")
      (item "Range queries: list files between N and M")
      (item "Latest entry: highest-numbered file")
      (item "Debugging: read any entry with a text editor"))
    (p "No database. No binary format. No special tools required to inspect the audit trail."))
  (section
    "Security Considerations"
    (subsection
      "Threat Model"
      (p "We trust as little as possible.")
      (p "Trusted:")
      (list
        (item "Local filesystem during operation (not after)")
        (item "Ed25519 implementation (libsodium, audited)")
        (item "Private keys (your responsibility)"))
      (p "Untrusted:")
      (list
        (item "Storage medium after entry creation")
        (item "Network transport between nodes")
        (item "Other actors, including administrators"))
      (p "This threat model assumes a hostile environment where storage can be tampered with and network traffic can be intercepted. The cryptography protects the audit trail even when everything else is compromised."))
    (subsection
      "Attack Mitigations"
      (table
        (header "Attack " "Mitigation ")
        (row "Entry modification " "SHA-512 hash detects tampering ")
        (row "Entry deletion " "Chain breaks are detectable ")
        (row "Entry insertion " "Hash chain prevents backdating ")
        (row "Actor impersonation " "Ed25519 signatures verify identity ")
        (row "Replay attacks " "Sequence numbers detect duplicates ")))
    (subsection
      "Non-Repudiation"
      (p "Once an entry is signed and published, the actor cannot credibly deny it. This is non-repudiation: mathematical proof of authorship.")
      (list
        (item "Actor cannot deny performing the action—their key signed it")
        (item "Timestamp cannot be backdated—hash chain enforces ordering")
        (item "Content cannot be altered—hash would change")
        (item "Signature mathematically proves authorship—no \"someone else used my account\""))
      (p "In court, in audits, in incident response: cryptographic proof beats testimony.")))
  (section
    "Integration Points"
    (subsection
      "Vault Operations"
      (p "All vault operations record audit entries:")
      (code scheme "(seal-commit \"message\")     → (action (verb seal-commit) ...)\n(seal-publish \"1.0.0\" ...)  → (action (verb seal-publish) ...)\n(seal-subscribe remote ...) → (action (verb seal-subscribe) ...)"))
    (subsection
      "SPKI Authorization"
      (p "Audit entries can include authorization chains:")
      (code scheme "(actor\n  (principal #${bob-public-key})\n  (authorization-chain\n    (signed-cert ...)   ; Alice delegated to Bob\n    (signed-cert ...))) ; Root delegated to Alice")
      (p "This proves not just who acted, but under whose authority.")))
  (section
    "Export Formats"
    (subsection
      "S-expression Export"
      (code scheme "(audit-export-sexp output: \"audit-export.sexp\")")
      (p "Produces:")
      (code scheme "(audit-trail\n  (audit-entry ...)\n  (audit-entry ...)\n  ...)"))
    (subsection
      "Human-readable Export"
      (code scheme "(audit-export-human output: \"audit-export.txt\")")
      (p "Produces:")
      (code "AUDIT TRAIL - Library of Cyberspace\n===================================\n\nEntry #1\n  ID: sha512:b14471cd57ea557f...\n  Time: 2026-01-05 23:38:20Z\n  Action: seal-publish\n  Why: Published release to filesystem\n\nEntry #2\n  ...")))
  (section
    "Implementation Notes"
    (subsection
      "Dependencies"
      (list
        (item "crypto-ffi: Ed25519 signatures, SHA-512 hashing")
        (item "srfi-1: List utilities")
        (item "srfi-4: u8vectors for binary data")
        (item "srfi-13: String utilities")))
    (subsection
      "Performance Considerations"
      (list
        (item "Content-addressed IDs enable O(1) lookup by hash")
        (item "Sequential file naming enables efficient range queries")
        (item "Lazy verification: verify on read, not on load"))))
  (section
    "References"
    (list
      (item "Haber, S., & Stornetta, W. S. (1991). How to time-stamp a digital document.")
      (item "Merkle, R. C. (1987). A digital signature based on a conventional encryption function.")
      (item "Bernstein, D. J. (2006). Curve25519: new Diffie-Hellman speed records.")
      (item "SDSI/SPKI - RFC 2693, RFC 2692")))
  (section
    "Changelog"
    (p "2026-01-19 - Expanded narrative and rationale")
    (p "2026-01-06 - Initial specification")))

