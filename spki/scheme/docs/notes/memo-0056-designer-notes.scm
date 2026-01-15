;; Memo-0056: Designer Notes
;; Intellectual heritage and design philosophy (not an RFC)

(memo
  (number 56)
  (title "Designer Notes")
  (reserved)
  (status "Draft")
  (date "January 2026")
  (author "Derrell Piper" "ddp@archlinux.us")

  (section
    "Notice"
    (p "This is a living document, not a specification. It records the intellectual heritage, design philosophy, and collaborative process behind Cyberspace."))

  (section
    "1. Intellectual Heritage"

    (subsection
      "1.1 MIT Athena and DSSA"
      (p "Cyberspace traces its lineage to MIT's Athena project and the Distributed System Security Architecture (DSSA) research that produced SPKI.")
      (p "Athena introduced Kerberos, distributed authentication, and the concept of a unified computing environment across heterogeneous systems. DSSA, led by Rivest, Lampson, and Ellison, gave us SPKI - capability-based authorization through certificate chains.")
      (p "These ideas were absorbed during the same lamport epoch as R4RS Scheme (1991) and SDSI (1996), alongside the practical education of Boston traffic negotiation - both exercises in asserting authority without central coordination."))

    (subsection
      "1.2 Why Scheme"
      (p "Scheme was chosen not for nostalgia but for precision. Homoiconicity makes S-expressions natural for both code and data - certificates, audit records, and configuration are all readable by the same parser that reads the implementation.")
      (p "The language that Abelson and Sussman used to teach computational thinking at MIT is the same language used to implement the security architecture that MIT research defined. Full circle.")))

  (section
    "2. Collaborative Design"
    (p "Cyberspace was designed in collaboration with Claude (Anthropic), an AI assistant. This collaboration is documented in Memo-056.")
    (p "The interaction model: human provides vision and constraints, AI provides implementation and exploration. Neither could have built this alone."))

  (section
    "3. Naming Coherence"
    (p "Knuth's principle from TAOCP: names should be consistent across the totality of a system. When we renamed 'RFC' to 'Memo' internally, we applied s/rfc/memo/g globally - not just to files being edited, but to every reference in the codebase.")
    (p "Single source of truth extends to terminology. MEMO_NUMBER_WIDTH is defined once; the four-digit format flows from that constant through Scheme and shell. When the namespace overflows to five digits, one change propagates everywhere.")
    (p "Piecemeal renaming creates inconsistent states where variables say one thing and filenames say another. The systematic approach is the only approach."))

  (section
    "4. Target Environments"
    (p "Primary targets:")
    (list
      (item "macOS (Apple Silicon) - Cyberspace.app native shell")
      (item "Linux (x86_64) - including MIT Athena dialup")
      (item "Any POSIX system with CHICKEN Scheme 5.x"))
    (p "The system should feel native on a Mac, work cleanly on Athena, and build anywhere Scheme runs."))

  (section
    "5. The Scheme Beneath"
    (p "Scheme is the implementation language, not the user interface. The newcomer sees a shell; the schemer sees a REPL. Same system, different lenses.")
    (p "By default, Scheme internals are hidden:")
    (list
      (item "Inspector disabled - errors show simple messages, not debug> prompts")
      (item "Exception display uses plain language, not 'unbound variable'")
      (item "Help shows commands, not S-expressions")
      (item "The : prompt is a portal, not a lambda"))
    (p "Schemers opt in with (enable-inspector!) and see the machinery. The abstraction layer is permeable but not transparent.")
    (p "This is not dumbing down. It is layered revelation - the same principle that makes Cyberspace.app feel native on Mac while running pure Scheme underneath."))

  (section
    "6. The Scrutinizer"
    (p "Consistency requires tooling. The scrutinizer audits tone and terminology across library and code.")
    (p "Two failure modes:")
    (list
      (item "Overreach - poetry where precision needed, whimsy in error messages")
      (item "Underreach - dry jargon where warmth appropriate, internal vocabulary leaking through"))
    (p "Passes:")
    (list
      (item "Vocabulary audit - banned terms in user-facing strings")
      (item "Tone consistency - memos vs help vs errors")
      (item "S-expression exposure - Scheme leaking to surface"))
    (p "Interface:")
    (code scheme "(scrutinize)               ; both passes (default)
(scrutinize 'library)      ; memos only
(scrutinize 'code)         ; code only
(scrutinize #f)            ; disable

*scrutinize-realmtime*     ; parameter, default #f
(scrutinize-realmtime! #t) ; enable during dev")
    (p "Realmtime mode invokes spacetime - scrutiny flows through the realm as time passes. When enabled, violations surface as modules load. Off in production, on in beta."))

  (section
    "Changelog"
    (p "- 2026-01-15 — Initial draft, heritage notes")))
