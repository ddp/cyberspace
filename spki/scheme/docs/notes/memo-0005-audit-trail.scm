;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 5)
  (title "Cryptographic Audit Trail")
  (section
    "Abstract"
    (p "This Memo specifies the cryptographic audit trail system for the Library of Cyberspace, providing tamper-evident, hash-chained logging with SPKI principal attribution and Ed25519 signatures."))
  (section
    "Motivation"
    (p "Distributed systems require accountability. Who did what, when, and under whose authority?")
    (subsection
      "Heritage: VMS Cluster-Wide Audit"
      (p "This audit trail descends from VMS SECURITY.AUDIT$JOURNAL and the cluster-wide security infrastructure of VMS 6.0 (1993). That system introduced:")
      (list
        (item "SECURITYPOLICY bit 7 propagation")
        (item "Intrusion detection state replicated cluster-wide")
        (item "Cluster-wide intrusion detection")
        (item "Breakin attempts detected across all nodes as one")
        (item "TLV-encoded object store")
        (item "The [000000]SECURITY.SYS file in ODS5 stored SECURITYCLASS records"))
      (p "The design principle then, as now: cluster nodes behave identically. N nodes, one security domain. Every significant action audited, every audit record signed.")
      (p "Cyberspace audit trails apply the same principle at IPv6 scale."))
    (subsection
      "The Problem"
      (p "Traditional logging fails on all counts: - Tamperable: Text files can be edited - Anonymous: No cryptographic identity - Disconnected: No provable ordering - Unverifiable: No mathematical proof of integrity")
      (p "Cyberspace audit trails provide: 1. Content-addressed entries - Tamper-evident by hash 2. Hash-chained structure - Append-only ordering 3. SPKI attribution - Cryptographic actor identity 4. Ed25519 seals - Mathematical proof of authenticity 5. Dual context - Human-readable motivation + machine-parseable environment")))
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
      (code scheme "(define-record-type <audit-actor>\n  (make-audit-actor principal authorization-chain)\n  audit-actor?\n  (principal actor-principal)              ; Public key blob\n  (authorization-chain actor-authorization-chain))  ; SPKI cert chain")
      (p "The actor is identified by: - Principal: Ed25519 public key (32 bytes) - Authorization chain: Optional SPKI certificate chain proving delegation"))
    (subsection
      "Action Record"
      (code scheme "(define-record-type <audit-action>\n  (make-audit-action verb object parameters)\n  audit-action?\n  (verb action-verb)        ; Symbol: seal-commit, seal-publish, etc.\n  (object action-object)    ; Primary target\n  (parameters action-parameters))  ; Additional arguments")
      (p "Standard verbs: - seal-commit - Version control commit - seal-publish - Release publication - seal-subscribe - Subscription to remote - seal-synchronize - Bidirectional sync - seal-release - Version tagging"))
    (subsection
      "Context Record"
      (code scheme "(define-record-type <audit-context>\n  (make-audit-context motivation relates-to language)\n  audit-context?\n  (motivation context-motivation)    ; Human explanation\n  (relates-to context-relates-to)    ; Related entries\n  (language context-language))       ; ISO 639-1 code")
      (p "Context provides: - Motivation: Why the action was taken (human-readable) - Relates-to: Cross-references to related audit entries - Language: For internationalization"))
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
      (p "Process: 1. Increment sequence counter 2. Get parent entry ID (hash chain link) 3. Build unsealed entry structure 4. Compute SHA-512 hash of canonical S-expression 5. Sign hash with Ed25519 6. Create seal record 7. Save entry to disk"))
    (subsection
      "audit-verify"
      (p "Verify cryptographic seal on an entry.")
      (code scheme "(audit-verify entry public-key: key)")
      (p "Verification steps: 1. Reconstruct unsealed entry 2. Compute SHA-512 hash 3. Compare with stored content-hash 4. Verify Ed25519 signature"))
    (subsection
      "audit-chain"
      (p "Verify entire audit chain.")
      (code scheme "(audit-chain verify-key: public-key)")
      (p "Verifies: - Each entry's signature is valid - Parent-id references form valid chain - Sequence numbers are monotonic"))
    (subsection
      "audit-read"
      (p "Read specific audit entry.")
      (code scheme "(audit-read sequence: 42)\n(audit-read id: \"sha512:...\")")))
  (section
    "Storage Format"
    (p "Entries stored as individual S-expression files:")
    (code ".vault/audit/\n  1.sexp\n  2.sexp\n  3.sexp\n  ...")
    (p "File naming by sequence number enables efficient: - Sequential reads - Range queries - Latest entry lookup"))
  (section
    "Security Considerations"
    (subsection
      "Threat Model"
      (p "Trusted: - Local filesystem (during operation) - Ed25519 implementation (libsodium) - Private keys")
      (p "Untrusted: - Storage medium (after creation) - Network transport - Other actors"))
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
      (p "Once an entry is signed and published: - Actor cannot deny performing the action - Timestamp cannot be backdated - Content cannot be altered - Signature mathematically proves authorship")))
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
        (item "crypto-ffi")
        (item "Ed25519 signatures, SHA-512 hashing - srfi-1")
        (item "List utilities - srfi-4 - u8vectors for binary data - srfi-13")
        (item "String utilities")))
    (subsection
      "Performance Considerations"
      (list
        (item "Content-addressed IDs enable O(1) lookup by hash")
        (item "Sequential file naming enables efficient range queries")
        (item "Lazy verification: verify on read, not on load"))))
  (section
    "References"
    (p "1. Haber, S., & Stornetta, W. S. (1991). How to time-stamp a digital document. 2. Merkle, R. C. (1987). A digital signature based on a conventional encryption function. 3. Bernstein, D. J. (2006). Curve25519: new Diffie-Hellman speed records. 4. SPKI/SDSI - RFC 2693, RFC 2692"))
  (section
    "Changelog"
    (list
      (item "2026-01-06")
      (item "Initial specification"))))

