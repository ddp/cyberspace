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
    "Changelog"
    (p "2026-01-18 - Initial notes from CLI/search session")))
