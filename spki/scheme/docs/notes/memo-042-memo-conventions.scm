;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 42)
  (title "Memo Conventions")
  (section
    "Abstract"
    (p "This memo establishes naming conventions, metadata requirements, and scope rules for documentation in the Library of Cyberspace. We adopt IETF RFC format for technical compatibility while using \"memo\" as our vernacular."))
  (section
    "Status of This Memo"
    (p "This document is an Informational memo for the Library of Cyberspace community. It establishes conventions for penning memos.")
    (p "Distribution of this memo is unlimited."))
  (section
    "Motivation"
    (p "The IETF's \"Request for Comments\" name reflects a historical process we don't share.[^h1] We don't request comments—we record decisions. But the RFC format is well-understood and serves our needs.")
    (p "The compromise: RFC format externally, \"memo\" internally.")
    (code "\"I penned a memo on wormholes\"     ← what we say\n\"See Memo-041\"                       ← how we cite")
    (p "[^h1]: Historical: The first RFC (Memo-1, April 1969) was literally a request for comments on host software. The name stuck. Fifty-seven years later, nobody requests comments—they publish specifications."))
  (section
    "Terminology"
    (table
      (header "Term " "Meaning ")
      (row "memo " "Any document in the Library of Cyberspace ")
      (row "RFC " "A memo published in RFC format with canonical number ")
      (row "pen " "To author a memo ")
      (row "promote " "To elevate scope (local → federation → core) ")))
  (section
    "Memo Metadata"
    (p "Every memo begins with a standardized header:")
    (code markdown "# RFC-NNN: Title\n\nStatus: Draft | Proposed | Implemented | Historic\nCategory: Standards Track | Informational | Experimental | BCP | Historic\nScope: core | federation | local\nCreated: YYYY-MM-DD\nUpdated: YYYY-MM-DD\nAuthor: Name <email>\nOrigin: federation-name | core\nSigned: <spki-hash> (optional)\nUpdates: RFC-NNN (if applicable)\nObsoletes: RFC-NNN (if applicable)\n\n---\n\n## Abstract\n\nOne paragraph summary.")
    (subsection
      "Required Fields"
      (table
        (header "Field " "Required " "Description ")
        (row "Status " "Yes " "Document lifecycle stage ")
        (row "Category " "Yes " "Document type (per Memo-019) ")
        (row "Scope " "Yes " "Visibility and authority ")
        (row "Created " "Yes " "Initial authorship date ")
        (row "Author " "Yes " "Who penned the memo ")))
    (subsection
      "Optional Fields"
      (table
        (header "Field " "When Used ")
        (row "Updated " "After modifications ")
        (row "Origin " "For federation-scoped memos ")
        (row "Signed " "For authenticated memos ")
        (row "Updates " "When extending prior memo ")
        (row "Obsoletes " "When replacing prior memo "))))
  (section
    "Naming Scope"
    (p "Memos exist at three scopes:")
    (p "Table 1: Memo Scopes")
    (table
      (header "Scope " "Format " "Authority " "Visibility ")
      (row "core " "RFC-NNN " "Core maintainers " "Global, canonical ")
      (row "federation " "<fed>:memo-NNN " "Federation members " "Federation-wide ")
      (row "local " "local:memo-NNN " "Node author " "Single node "))
    (subsection
      "Core Scope"
      (p "Core memos use IETF-style sequential numbering:")
      (code "Memo-001, Memo-002, ... Memo-043")
      (p "These are canonical specifications for the Library of Cyberspace. Core maintainer approval required for Standards Track, BCP, and Historic. Anyone may pen Informational or Experimental memos with maintainer review."))
    (subsection
      "Federation Scope"
      (p "Federation memos are namespaced by federation identifier:")
      (code "yoyodyne:memo-001\nalexandria:memo-042")
      (p "Each federation maintains its own numbering sequence. Federation memos are visible to all federation members but not globally canonical."))
    (subsection
      "Local Scope"
      (p "Local memos exist only on the authoring node:")
      (code "local:memo-001")
      (p "Local memos are drafts, notes, or node-specific documentation. They never leave the node unless explicitly promoted.")))
  (section
    "Promotion Path"
    (p "Memos flow upward through scopes:")
    (code "local:memo  →  fed:memo  →  RFC\n    ↓            ↓           ↓\n  draft     federation    canonical\n             review       consensus")
    (subsection
      "Local to Federation"
      (p "A node author submits a local memo to their federation:")
      (code scheme "(memo-promote \"local:memo-007\" 'federation)\n;; → yoyodyne:memo-023")
      (p "Federation review and rough consensus required."))
    (subsection
      "Federation to Core"
      (p "A federation submits a memo for core adoption:")
      (code scheme "(memo-promote \"yoyodyne:memo-023\" 'core)\n;; → Memo-044 (after consensus)")
      (p "Cross-federation review and rough consensus required. Standards Track requires core maintainer approval.")))
  (section
    "Collision Avoidance"
    (subsection
      "Core Namespace"
      (p "Sequential allocation by core maintainers. No collisions possible."))
    (subsection
      "Federation Namespace"
      (p "Federation prefix provides isolation:")
      (code "yoyodyne:memo-001  ≠  alexandria:memo-001"))
    (subsection
      "Content-Addressed Fallback"
      (p "For unambiguous citation across contexts:")
      (code "memo:sha256:a7f3b2c1...")
      (p "The content hash identifies the exact memo regardless of scope or number.")))
  (section
    "Citation Format"
    (subsection
      "Within Scope"
      (code markdown "See Memo-041 for wormhole specification.\nSee memo-007 for local notes."))
    (subsection
      "Cross-Federation"
      (code markdown "See yoyodyne:memo-023 for their implementation."))
    (subsection
      "Unambiguous"
      (code markdown "See memo:sha256:a7f3b2c1... for the canonical text.")))
  (section
    "Vernacular"
    (p "We say:")
    (p "- \"Pen a memo\" — author a document - \"The memo specifies...\" — referring to content - \"Promote the memo\" — elevate scope - \"See the RFC\" — cite by number")
    (p "We don't say:")
    (p "- \"Request for comments\" — we're not requesting - \"Submit an RFC\" — we pen memos, they become RFCs"))
  (section
    "Security Considerations"
    (subsection
      "Signed Memos"
      (p "Memos MAY include SPKI signatures for authentication:")
      (code markdown "Signed: sha256:a7f3b2c1...")
      (p "The signature covers the memo content hash, binding author to text."))
    (subsection
      "Scope Escalation"
      (p "Promotion from local to federation to core requires appropriate authorization. A local memo cannot claim core status without consensus."))
    (subsection
      "Metadata Integrity"
      (p "Memo metadata is stored with content in the vault. Tampering with metadata (scope, author, date) is detectable via content addressing.")))
  (section
    "References"
    (p "1. Memo-019 — Documentation Pipeline 2. Memo-042 — IETF Normative Reference 3. Memo-004 — SPKI Authorization"))
  (section
    "Changelog"
    (p "- 2026-01-07 — Initial specification")))

