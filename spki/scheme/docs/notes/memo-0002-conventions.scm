;; Memo-0002: Conventions
;; Combined from Memo-0041 (IETF Normative Reference) and Memo-0042 (Memo Conventions)

(memo
  (number 2)
  (title "Conventions")
  (section
    "Abstract"
    (p "This memo establishes naming conventions, metadata requirements, and scope rules for documentation in the Library of Cyberspace. We adopt Internet Engineering Task Force (IETF) RFC format for technical compatibility while using \"memo\" as our vernacular. The IETF and its associated organizations serve as the normative model for our standards processes."))
  (section
    "Status of This Memo"
    (p "This document is an Informational memo for the Library of Cyberspace community. It establishes conventions for penning memos and normative references to external standards bodies.")
    (p "Distribution of this memo is unlimited."))
  (section
    "Motivation"
    (p "The IETF's \"Request for Comments\" name reflects a historical process we don't share. We don't request comments--we record decisions. But the RFC format is well-understood and serves our needs.")
    (p "The compromise: RFC format externally, \"memo\" internally.")
    (code "\"I penned a memo on wormholes\"     <- what we say\n\"See Memo-041\"                       <- how we cite")
    (p "The IETF has successfully governed Internet standards for over 35 years through open processes, rough consensus, and running code. We adopt their model not from lack of imagination but from recognition of what works."))
  (section
    "Terminology"
    (table
      (header "Term " "Meaning ")
      (row "memo " "Any document in the Library of Cyberspace ")
      (row "RFC " "A memo published in RFC format with canonical number ")
      (row "pen " "To author a memo ")
      (row "promote " "To elevate scope (local -> federation -> core) ")))
  (section
    "IETF Normative Reference"
    (p "The following IETF organizations and RFCs are normative for Library of Cyberspace processes.")
    (subsection
      "Normative Organizations"
      (p "IETF - Principal standards body for Internet protocols. Website: https://www.ietf.org/")
      (p "IAB (Internet Architecture Board) - Provides architectural oversight. Charter: RFC 2850")
      (p "IESG (Internet Engineering Steering Group) - Manages the IETF standards process. RFC 2026, Section 6")
      (p "IRTF (Internet Research Task Force) - Longer-term research. Website: https://irtf.org/")
      (p "IANA (Internet Assigned Numbers Authority) - Protocol parameters. RFC 5226")
      (p "RFC Editor - Publishes and maintains the RFC series. Website: https://www.rfc-editor.org/"))
    (subsection
      "Normative RFCs"
      (table
        (header "RFC " "Title " "Relevance ")
        (row "RFC 2026 " "The Internet Standards Process, Revision 3 " "Standards track, categories, process ")
        (row "RFC 2119 " "Key Words for Use in RFCs " "MUST, SHOULD, MAY terminology ")
        (row "RFC 3935 " "A Mission Statement for the IETF " "Rough consensus, running code ")
        (row "RFC 7322 " "RFC Style Guide " "Document formatting ")
        (row "RFC 8174 " "Ambiguity of Uppercase vs Lowercase in RFC 2119 " "Keyword clarification ")))
    (subsection
      "RFC 2119 Keywords"
      (p "The key words \"MUST\", \"MUST NOT\", \"REQUIRED\", \"SHALL\", \"SHALL NOT\", \"SHOULD\", \"SHOULD NOT\", \"RECOMMENDED\", \"MAY\", and \"OPTIONAL\" in Library of Cyberspace documents are to be interpreted as described in RFC 2119 and RFC 8174.")))
  (section
    "Adopted Practices"
    (p "What we take from IETF:")
    (list
      (item "RFC format - Document structure, numbering, required sections")
      (item "RFC 2119 keywords - MUST, SHOULD, MAY precision")
      (item "Security Considerations - Required in every specification")
      (item "Rough consensus - General agreement over voting")
      (item "Running code - Implementations validate specifications"))
    (p "These practices provide precision without bureaucracy, ensuring specifications are unambiguous while remaining accessible to implementers.")
    (p "What we skip:")
    (list
      (item "Working group charters")
      (item "Area director approval")
      (item "IESG review cycles")
      (item "Last call periods")
      (item "IANA registry formalism"))
    (p "Simple. Direct. We document, we build, we ship."))
  (section
    "Memo Metadata"
    (p "Every memo begins with a standardized header:")
    (code markdown "# RFC-NNN: Title\n\nStatus: Draft | Proposed | Implemented | Historic\nCategory: Standards Track | Informational | Experimental | BCP | Historic\nScope: core | federation | local\nCreated: YYYY-MM-DD\nUpdated: YYYY-MM-DD\nAuthor: Name <email>\nOrigin: federation-name | core\nSigned: <spki-hash> (optional)\nUpdates: RFC-NNN (if applicable)\nObsoletes: RFC-NNN (if applicable)\n\n---\n\n## Abstract\n\nOne paragraph summary.")
    (subsection
      "Required Fields"
      (table
        (header "Field " "Required " "Description ")
        (row "Status " "Yes " "Document lifecycle stage ")
        (row "Category " "Yes " "Document type ")
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
    (table
      (header "Scope " "Format " "Authority " "Visibility ")
      (row "core " "RFC-NNN " "Core maintainers " "Global, canonical ")
      (row "federation " "<fed>:memo-NNN " "Federation members " "Federation-wide ")
      (row "local " "local:memo-NNN " "Node author " "Single node "))
    (subsection
      "Core Scope"
      (p "Core memos use IETF-style sequential numbering:")
      (code "Memo-001, Memo-002, ... Memo-043")
      (p "These are canonical specifications for the Library of Cyberspace."))
    (subsection
      "Federation Scope"
      (p "Federation memos are namespaced by federation identifier:")
      (code "yoyodyne:memo-001\nalexandria:memo-042")
      (p "Each federation maintains its own numbering sequence."))
    (subsection
      "Local Scope"
      (p "Local memos exist only on the authoring node:")
      (code "local:memo-001")
      (p "Local memos are drafts, notes, or node-specific documentation.")))
  (section
    "Promotion Path"
    (p "Memos flow upward through scopes:")
    (code "local:memo  ->  fed:memo  ->  RFC\n    |            |           |\n  draft     federation    canonical\n             review       consensus")
    (subsection
      "Local to Federation"
      (p "A node author submits a local memo to their federation:")
      (code scheme "(memo-promote \"local:memo-007\" 'federation)\n;; -> yoyodyne:memo-023")
      (p "Federation review and rough consensus required."))
    (subsection
      "Federation to Core"
      (p "A federation submits a memo for core adoption:")
      (code scheme "(memo-promote \"yoyodyne:memo-023\" 'core)\n;; -> Memo-044 (after consensus)")
      (p "Cross-federation review and rough consensus required.")))
  (section
    "Collision Avoidance"
    (subsection
      "Core Namespace"
      (p "Sequential allocation by core maintainers. No collisions possible."))
    (subsection
      "Federation Namespace"
      (p "Federation prefix provides isolation:")
      (code "yoyodyne:memo-001  !=  alexandria:memo-001"))
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
    (list
      (item "\"Pen a memo\" - author a document")
      (item "\"The memo specifies...\" - referring to content")
      (item "\"Promote the memo\" - elevate scope")
      (item "\"See the RFC\" - cite by number"))
    (p "We don't say:")
    (list
      (item "\"Request for comments\" - we're not requesting")
      (item "\"Submit an RFC\" - we pen memos, they become RFCs")))
  (section
    "Security Considerations"
    (subsection
      "Signed Memos"
      (p "Memos MAY include Simple Public Key Infrastructure (SPKI) signatures for authentication:")
      (code markdown "Signed: sha256:a7f3b2c1...")
      (p "The signature covers the memo content hash, binding author to text."))
    (subsection
      "Scope Escalation"
      (p "Promotion from local to federation to core requires appropriate authorization. A local memo cannot claim core status without consensus."))
    (subsection
      "Metadata Integrity"
      (p "Memo metadata is stored with content in the vault. Tampering with metadata is detectable via content addressing.")))
  (section
    "References"
    (subsection
      "Normative References"
      (list
        (item "RFC 2026 - Bradner, S., \"The Internet Standards Process\", BCP 9, 1996")
        (item "RFC 2119 - Bradner, S., \"Key words for use in RFCs\", BCP 14, 1997")
        (item "RFC 8174 - Leiba, B., \"Ambiguity of Uppercase vs Lowercase\", BCP 14, 2017")))
    (subsection
      "Informative References"
      (list
        (item "RFC 3935 - Alvestrand, H., \"A Mission Statement for the IETF\", 2004")
        (item "RFC 7322 - Flanagan, H., Ginoza, S., \"RFC Style Guide\", 2014"))))
  (section
    "Acknowledgments"
    (p "The IETF community, whose 35+ years of open standards development provides the foundation we build upon. Rough consensus and running code."))
  (section
    "Changelog"
    (p "- 2026-01-17 - Combined from Memo-0041 and Memo-0042")
    (p "- 2026-01-07 - Original specifications")))
