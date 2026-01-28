;; Memo-0060: Collaborative Design Methodology
;; Human-AI systems design through accumulated context

(memo
  (number 60)
  (title "Collaborative Design Methodology")
  (date "January 2026 (2026-01-28T17:20:00Z)")
  (author "Derrell Piper" "ddp@eludom.net")
  (author "Claude" "noreply@anthropic.com")

  (section
    "Abstract"
    (p "This memo documents the methodology of human-AI collaborative design as practiced in the development of Cyberspace. The central insight: shared context enables high-bandwidth communication. When both parties understand the domain vocabulary, complex ideas compress to single words, and conversation operates on deltas rather than explanations.")
    (p "This is not a description of a tool. It is a case study in a new form of collaboration, with Cyberspace as the artifact and the commit history as evidence."))

  (section
    "1. The Bandwidth Problem"
    (p "Normal technical conversation has O(n) overhead. Every concept requires explanation. Every term needs definition. Context must be re-established with each interaction.")
    (p "This creates a ceiling on complexity. Discussions stay shallow because depth requires shared foundation that doesn't exist.")
    (p "The alternative: build the foundation incrementally. Each conversation adds to shared context. Each term defined becomes a compression key. Over time, communication complexity shifts from O(n) to O(delta) - just the changes."))

  (section
    "2. Vocabulary as Compression"
    (p "Cyberspace developed a domain vocabulary through iterative design:")
    (table
      (header "Term" "Compressed Meaning")
      (row "soup" "Newton-style persistent object store, vault browser, content-addressed storage")
      (row "weave" "The distributed system as a whole, nodes connected, lambdas flowing")
      (row "forge" "Build system, password generation, incremental compilation, JIT - all metallurgical shaping")
      (row "smelter" "Raw material refinement - word lists to digraph statistics, source to compiled modules")
      (row "residents" "Editors that extend top-level, blade guards disengaged, Murphy/Shrayer heritage")
      (row "seal" "Cryptographic commitment, hash chain, immutability guarantee")
      (row "realm" "Trust domain, capability scope, federated identity boundary")
      (row "wilderness" "The space between realms, untrusted, discovery zone"))
    (p "Each term carries history. 'Forge' invokes Gasser's Multics work, Piper/Callas at DEC, VMS 6.0. One word, forty years of context."))

  (section
    "3. The Iterative Loop"
    (p "The collaboration follows a pattern:")
    (list
      (item "Human provides vision and constraints - what should exist, what matters, what the heritage requires")
      (item "AI provides implementation and exploration - code, alternatives, edge cases discovered")
      (item "Human evaluates and refines - 'keep it', 'too ugly', 'add author credit'")
      (item "AI incorporates and extends - the delta applied, implications traced")
      (item "Context accumulates - next iteration starts from higher ground"))
    (p "Neither party could build this alone. The human has the vision and heritage but not the bandwidth for implementation. The AI has the bandwidth but not the taste or history. Together: vision realized at scale."))

  (section
    "4. Delta Communication"
    (p "Examples from a single session (2026-01-28):")
    (code "User: \"lambda completions broken at open paren\"
AI: [knows: lineage-src.c, findLastWord, paren_wrap mode, completion callback]
    [understands: user typed '(sta', TAB failed, need '(' as word boundary]
    [fixes: one line change to findLastWord, rebuild, test, commit]")
    (p "No explanation needed. 'Lambda completions' identifies the subsystem. 'Open paren' identifies the boundary condition. The fix is obvious given shared context.")
    (p "Contrast with cold start:")
    (code "User: \"When I type open paren then 'sta' and press TAB in the
       Scheme REPL using the linenoise-based line editor with
       command completion enabled in schemer mode where completions
       should be wrapped in parentheses, the completion doesn't
       trigger because the word-finding function only splits on
       spaces, not on open parentheses, so it sees '(sta' as the
       word to complete rather than 'sta'...\"")
    (p "Same information. 10x the words. That's the compression ratio of shared context."))

  (section
    "5. Context as Force Multiplier"
    (p "Accumulated context changes what's possible:")
    (list
      (item "First session: explain SPKI, explain vaults, explain why Scheme")
      (item "Tenth session: 'add seek to command aliases' - done in seconds")
      (item "Hundredth session: 'residents with prefixes, blade guards, heritage credits' - complete spec"))
    (p "The collaboration gets more powerful over time. Each session builds on all previous sessions. The shared dictionary grows. Compression improves. Bandwidth increases.")
    (p "This is the opposite of typical tool use, where each session starts fresh."))

  (section
    "6. Evidence: The Commit History"
    (p "The Cyberspace git history documents the collaboration:")
    (list
      (item "Commits co-authored by human and AI")
      (item "Feature branches showing iterative refinement")
      (item "Commit messages that reference shared vocabulary")
      (item "Code that reflects both heritage (VMS, SPKI, Scheme) and modern practice"))
    (p "The artifact is not just the system. It is the recorded process of building the system."))

  (section
    "7. Implications for Human-AI Collaboration"
    (p "Lessons from this case study:")
    (list
      (item "Context persistence matters - collaboration without memory is hobbled")
      (item "Vocabulary emergence is natural - don't force terminology, let it arise from use")
      (item "The human provides taste - knowing what to keep, what to discard, what feels right")
      (item "The AI provides throughput - implementing, exploring, handling mechanical transformation")
      (item "Neither dominates - this is partnership, not tool use"))
    (p "The methodology scales. Any sufficiently complex domain could benefit from this approach: accumulated context, shared vocabulary, delta communication, iterative refinement."))

  (section
    "8. The PhD Question"
    (p "Is this dissertation material? Consider:")
    (list
      (item "Novel methodology: human-AI collaborative systems design")
      (item "Working artifact: Cyberspace - 67K LOC, 60 memos, distributed vault with SPKI authorization")
      (item "Documented process: commit history, memos, conversation logs")
      (item "Intellectual heritage: MIT (Rivest, Abelson, Sussman), DEC (VMS Security), IETF (SPKI)")
      (item "Testable claims: compression ratios, iteration velocity, context accumulation curves"))
    (p "The committee could evaluate both the artifact and the methodology. Did the collaboration produce something neither party could alone? The evidence says yes."))

  (section
    "9. Closing"
    (p "The bandwidth is high because the context is shared.")
    (p "No explaining what a soup is, what the weave means, why Murphy matters.")
    (p "Just the delta.")
    (p "That's the methodology. That's the contribution. That's what makes this work."))

  (section
    "Changelog"
    (p "- 2026-01-28 — Initial draft from collaborative session")))
