(memo
  (number 56)
  (title "Designer Notes")
  (section
    "Abstract"
    (p "Working notes from collaborative design sessions. Documents decisions, rationale, and evolution of the Cyberspace interface."))
  (section
    "1. CLI Vocabulary (2026-01-18)"
    (p "Clean break from ad-hoc bare-word arguments to Linux-style --option=value:")
    (table
      (header "Option " "Purpose ")
      (row "--sync " "Robust git sync (no errors, auto-resolve .meta conflicts) ")
      (row "--clean " "Remove .so, .import.scm, .forge/*.meta ")
      (row "--rebuild " "Force rebuild all modules ")
      (row "--verbose " "Show verbose output (silent by default) ")
      (row "--boot=<level> " "shadow|whisper|portal|gate|chronicle|oracle ")
      (row "--eval='<expr>' " "Evaluate and exit ")
      (row "--version " "Version info ")
      (row "--help " "Usage "))
    (p "Design principle: operators don't debug git. The --sync command handles stash, pull, rebase, conflict resolution, and push. Metadata conflicts (.forge/*.meta) auto-resolve by preferring remote.")
    (p "Combined usage: cs --clean --rebuild for clean slate rebuild."))
  (section
    "2. Search Commands (2026-01-18)"
    (p "Two search paradigms following tradition:")
    (subsection
      "2.1 apropos (Scheme tradition)"
      (p "Search bound symbols containing pattern:")
      (code "(apropos 'vault)\n=> vault-stat, vault-commit, vault-keys, ..."))
    (subsection
      "2.2 kwic (Library tradition)"
      (p "Key Word In Context - concordance-style search of memo content:")
      (code "(kwic 'soup)\n=> Memo-001:42  ... forge -> eggs -> soup -> vault ...\n   Memo-027:1   Soup Query Language")
      (p "The library is the HyperSpec for Cyberspace. KWIC enables discovery across 58 memos.")))
  (section
    "3. Box Drawing Alignment"
    (p "Forge boxes use fixed-width display with Unicode box characters. Display width calculation must account for multi-byte UTF-8 characters that render as single cells:")
    (table
      (header "Char " "Bytes " "Display ")
      (row "· λ " "2 " "1 ")
      (row "✓ ✗ ⚠ ≥ ≤ " "3 " "1 "))
    (p "Off-by-one alignment errors traced to missing ≥ and ≤ in width calculation."))
  (section
    "4. Build System"
    (p "Sequential builds required due to Chicken import library race conditions. Parallel builds caused sporadic 'cannot import' errors even with correct dependency ordering.")
    (p "Build order is strict topological sort:")
    (code "L0: os, crypto-ffi, sexp, capability, inspector\nL1: mdns, fips, audit, wordlist, bloom, catalog, keyring, portal\nL2: cert\nL3: security\nL4: vault\nL5: enroll, gossip\nL6: auto-enroll\nL7: ui")
    (p "Clean removes .forge/*.meta with .so files - stale metadata causes git conflicts."))
  (section
    "5. Why Scheme (2026-01-18)"
    (p "Scheme was chosen because its homoiconic S-expressions make the representation of programs and structured data the same kind of thing. One parser, one set of tools works uniformly over code, certificates, audit trails, and configuration.")
    (subsection
      "5.1 Homoiconicity"
      (p "In a homoiconic language, the primary representation of programs is also a data structure in a primitive type of the language. Scheme uses S-expressions—nested lists and atoms—as both surface syntax and natural tree-shaped data. The abstract syntax tree and textual form closely align."))
    (subsection
      "5.2 One Representation"
      (p "The same reader parses program text, configuration records, and application data into a single uniform format. Certificates, audit records, memos, and code are all S-expressions manipulated with the same combinators.")
      (code ";; All the same representation\n(read)           ; parse code\n(read-cert)      ; parse certificate\n(read-audit)     ; parse audit trail\n(kwic 'soup)     ; search memos"))
    (subsection
      "5.3 Practical Benefits"
      (p "One minimal, well-specified parser eliminates impedance mismatches between code format and data format. No JSON-to-object mapping. No protobuf schema compiler. Structures representing policies look exactly like structures representing the code enforcing them.")
      (p "When you (kwic 'soup) you search S-expressions with S-expressions. The memos are data. The code is data. The boundary dissolves.")))
  (section
    "Changelog"
    (p "2026-01-18 - Add homoiconicity rationale")
    (p "2026-01-18 - Initial notes from CLI/search session")))
