;; Memo-0054: Designer Notes
;; Intellectual heritage and design philosophy (not an RFC)

(memo
  (number 3)
  (title "Designer Notes")
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
    (p "Scheme is the implementation language, not the user interface. The novice sees a shell; the schemer sees a REPL. Same system, different lenses.")
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
    "7. Forge and Smelter"
    (p "The forge module generates pronounceable passwords using Markov chains on digraph statistics. The lineage traces back to Multics.")

    (subsection
      "7.1 Heritage"
      (p "Original design by Morrie Gasser in PL/1 on Multics. Gasser, author of 'Building a Secure Computer System' (1988), carried the code forward to VAX/VMS where it remained in PL/1 until the Alpha transition.")
      (p "When DEC moved to Alpha architecture, PL/1 wasn't in the initial compiler release. The code had to be expunged from the TCB. Derrell Piper and Jon Callas rewrote it for VMS 6.0 (circa 1991): Piper wrote the BLISS system service for the Trusted Computing Base; Callas wrote the user-mode TPU smelter.")
      (p "US and EU DEC patents were filed on the design (now expired). The terminology - forge, smelter - comes from metallurgy: the smelter refines raw ore (word lists) into workable material (digraph statistics); the forge shapes the final product (pronounceable words).")
      (p "Callas later became a principal author of OpenPGP (RFC 4880) and co-founded PGP Corporation and Silent Circle. He remains a planned beta tester for Cyberspace.")
      (p "The chain of custody: Gasser (Multics PL/1) → Piper/Callas (VMS 6.0 BLISS/TPU) → Cyberspace (Scheme)."))

    (subsection
      "7.2 Design"
      (p "The smelter reads word lists and extracts digraph (character pair) statistics:")
      (list
        (item "Starting pair frequency - which pairs begin words")
        (item "Transition probability - given 'ab', what characters follow")
        (item "Termination markers - which pairs end words"))
      (p "The forge walks these statistics with weighted random selection, producing words that follow the phonetic patterns of the source language. Entropy is tracked in 'decibits' (tenths of bits) to quantify password strength."))

    (subsection
      "7.3 Languages"
      (p "Original VMS languages: English, Latin, Italian, Dutch, Sindarin, Webster. The VT100 diacriticals were encoded in DEC MCS (Multinational Character Set).")
      (p "Cyberspace expansion to 40+ languages follows roughly the operational map of the Office of Strategic Services - another egg for those who recognize the geography:")
      (list
        (item "Western Europe: French, German, Spanish, Portuguese")
        (item "Iberia: Catalan, Galician, Basque")
        (item "Nordic (resistance networks): Swedish, Norwegian, Danish, Finnish")
        (item "Atlantic fringe: Irish, Welsh, Scottish Gaelic, Breton")
        (item "Balkans (partisan country): Greek, Albanian, Serbian, Croatian, Slovenian, Macedonian")
        (item "Eastern front: Polish, Czech, Slovak, Hungarian, Romanian")
        (item "Baltic: Lithuanian, Latvian, Estonian")
        (item "Soviet theater: Russian, Ukrainian, Bulgarian")
        (item "Near East: Turkish, Armenian")
        (item "Mediterranean (George Cross island): Maltese")
        (item "Detachment 101: Vietnamese, Thai, Lao, Korean")
        (item "Literary: Sindarin (Tolkien's Elvish), Dante's Divina Commedia"))
      (p "Word lists sourced from Hunspell, LibreOffice, SCOWL, OpenTaal, Eldamo, and the Princeton Dante Project. All diacriticals converted to UTF-8.")
      (p "Sindarin preserves Tolkien's circumflexes: Manwë, Aulë, Andúril. Dante's medieval Italian sits alongside. The OSS framing is itself an easter egg - layers of meaning for those who dig."))

    (subsection
      "7.4 Related Standards"
      (p "Forge predates but relates to two password generation standards:")
      (list
        (item "FIPS 181 (1993) - Automated Password Generator. Uses trigraph (3-letter) statistics and hyphenation rules. More structured but less natural. Forge's digraph approach (1991) produces smoother results by learning from actual language patterns rather than syllable rules.")
        (item "OPIE/S/Key - One-time Passwords In Everything. Uses a fixed 2048-word dictionary optimized for spoken communication over phone lines. Words are short and phonetically distinct. Different goal: memorability for one-time use vs. pronounceability for permanent passwords."))
      (p "Forge's contribution was combining Markov chain language modeling with entropy tracking - knowing not just that a password sounds right, but exactly how many bits of randomness it contains."))

    (subsection
      "7.5 Interface"
      (code scheme "(forge)              ; one English word
(forge 5)            ; five English words
(forge 'sindarin)    ; one Elvish word
(forge 'latin 3)     ; three Latin words
(forge 'passphrase)  ; 4-word passphrase
(forge 'german 'passphrase 6) ; 6-word German passphrase")
      (p "Each word reports its entropy. Passphrases join words with hyphens. The forge is an easter egg - undocumented in help, discovered by schemers exploring the REPL."))

    (subsection
      "7.6 Cryptographic Entropy"
      (p "Passwords fall naturally out of pronounceable words when the entropy source is sound. Forge uses /dev/urandom for cryptographically secure randomness, not pseudo-random generators.")
      (p "Boot-time verification runs automatically on module load:")
      (list
        (item "Confirms /dev/urandom exists and is readable")
        (item "Reads 256 test bytes and checks byte distribution")
        (item "Verifies no single byte appears more than ~10% (bias detection)")
        (item "Confirms at least 100 distinct byte values (diversity check)"))
      (p "If verification fails, the module refuses to load. An easter egg with real security - someone exploring the REPL discovers (forge) and gets actual cryptographic passwords, not toys.")))

  (section
    "8. The Novice Interface"
    (p "Cyberspace must be approachable by normal people. The terminal is for operators. A friendly interface layer serves everyone else.")

    (subsection
      "8.1 The Problem"
      (p "A novice asked: \"Why would I want to use this? I have iCloud. They have recipes and cat pictures.\"")
      (p "Valid question. The answer must be compelling without mentioning Ed25519, SPKI certificates, hash chains, Merkle trees, or S-expressions."))

    (subsection
      "8.2 What Novices Want"
      (p "They don't want a distributed cryptographic vault. They want:")
      (list
        (item "My stuff is mine - Not rented from a corporation")
        (item "It survives - No company shutdown deletes my photos")
        (item "I control sharing - Family, not platforms")
        (item "Privacy - My recipes aren't AI training data")
        (item "Legacy - Grandkids can inherit the vault")
        (item "No ads - I'm not the product")))

    (subsection
      "8.3 Two Doors"
      (code "                    CYBERSPACE
                        |
           +------------+------------+
           |                         |
      +----v----+              +-----v-----+
      | Terminal |              |  Friendly  |
      |  (cs)    |              |    Door    |
      +----+----+              +-----+-----+
           |                         |
      Operators                   Novices
      Hackers                     Family
      Admins                      Everyone")
      (p "The terminal offers full power and complexity for those who want it. The friendly door offers drag-and-drop simplicity - same operations, different presentation.")
      (p "Both doors lead to the same vault. Both use the same Scheme underneath."))

    (subsection
      "8.4 Principles"
      (list
        (item "Never dumb down the core - Scheme stays Scheme")
        (item "Add layers, don't subtract - Friendly is additional, not replacement")
        (item "Same operations - Both doors do the same things")
        (item "Gradual revelation - Novices can discover the terminal if curious")
        (item "Family friendly - Grandma can use it")))

    (subsection
      "8.5 The Test"
      (p "If a novice can create a vault in 30 seconds, add a photo in 5 seconds, invite family in 1 minute, and understand what they have - we've succeeded.")))

  (section
    "Changelog"
    (p "- 2026-01-17 — Added Novice Interface section (section 8)")
    (p "- 2026-01-15 — Gasser Multics provenance added (section 7.1)")
    (p "- 2026-01-15 — OSS operational geography framing, 40+ languages (section 7.3)")
    (p "- 2026-01-15 — Added cryptographic RNG with boot-time verification (section 7.6)")
    (p "- 2026-01-15 — Added forge/smelter heritage (section 7)")
    (p "- 2026-01-15 — Initial draft, heritage notes")))
