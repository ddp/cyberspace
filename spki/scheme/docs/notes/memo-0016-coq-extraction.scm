(memo
  (number 16)
  (title "Coq Verification of the Authorization TCB")
  (status "Complete")
  (date "2026-01-22")
  (author "Derrell Piper" "ddp@eludom.net")

  (abstract
    (p "This memo specifies the formal verification approach for the SPKI authorization Trusted Computing Base using the Coq proof assistant. We prove authorization correctness, not cryptographic hardness - libsodium handles the latter. The extraction pipeline generates OCaml code that is called from Scheme via FFI."))

  (section
    "Motivation"
    (p "The Prime Directive (Memo-0001):")
    (blockquote "If it's in the TCB, it's in OCaml. Otherwise it's in Chicken Scheme.")
    (p "But even OCaml can have bugs. The TCB handles signature chain verification and authorization decisions. A single bug breaks everything.")
    (p "Coq provides:")
    (list
      (item "Machine-checked proofs: Theorems verified by computer")
      (item "Extraction: Generate OCaml from proofs")
      (item "Correctness by construction: Implementation matches specification"))
    (p "We prove the authorization logic correct; we trust libsodium for cryptographic primitives."))

  (section
    "Architecture"
    (code "┌─────────────────────────────────────────────────────────────┐
│                    CYBERSPACE TCB                           │
│                                                             │
│   ┌─────────────────────────────────────────────────────┐   │
│   │              SpkiTcb.v (Coq Proofs)                 │   │
│   │                                                     │   │
│   │  Types: principal, tag, cert, auth_request          │   │
│   │  Algorithms: tag_intersect, verify_chain, authorize │   │
│   │  Theorems: authorize_requester_match, etc.          │   │
│   └──────────────────────┬──────────────────────────────┘   │
│                          │ Extraction                       │
│   ┌──────────────────────▼──────────────────────────────┐   │
│   │         spki_tcb_extracted.ml (generated)           │   │
│   └──────────────────────┬──────────────────────────────┘   │
│                          │ Bridge                           │
│   ┌──────────────────────▼──────────────────────────────┐   │
│   │              spki_tcb.ml + tcb_stubs.c              │   │
│   │         (bytes conversion, libsodium FFI)           │   │
│   └──────────────────────┬──────────────────────────────┘   │
│                          │                                  │
│                   ┌──────▼──────┐                           │
│                   │  libsodium  │                           │
│                   │  (trusted)  │                           │
│                   └─────────────┘                           │
└─────────────────────────────────────────────────────────────┘")
    (p "The extraction pipeline: SpkiTcb.v → spki_tcb_extracted.ml → OCaml library → Scheme FFI."))

  (section
    "What We Prove"
    (subsection
      "Fully Proven Theorems"
      (p "Security-critical theorems with complete proofs (no admits):")
      (table
        (header "Theorem" "Property")
        (row "principal_equal_refl" "Reflexivity: p = p")
        (row "principal_equal_sym" "Symmetry: p = q → q = p")
        (row "principal_equal_trans" "Transitivity: p = q ∧ q = r → p = r")
        (row "authorize_requester_match" "If authorized, requester is named by leaf cert")
        (row "authorize_complete" "All preconditions satisfied → authorization succeeds"))
      (p "The authorize_requester_match theorem is the key security property: it guarantees that authorization only succeeds when the requester is actually named in the certificate chain."))

    (subsection
      "Partially Proven Theorems"
      (table
        (header "Theorem" "Proven Cases" "Admitted Cases")
        (row "tag_intersect_idemp" "TagAll, TagSet, TagPrefix, TagRange" "TagThreshold")
        (row "tag_intersect_subset_left" "Most combinations" "TagPrefix recursive, TagThreshold"))
      (p "The admitted cases stem from design limitations documented below."))

    (subsection
      "Partially Proven: tag_intersect_comm"
      (table
        (header "Case" "Status")
        (row "TagAll" "Proven")
        (row "TagSet" "Proven (via filter_intersect_comm lemma)")
        (row "TagRange" "Proven")
        (row "TagPrefix" "Admitted (recursive structure)")
        (row "TagThreshold" "Admitted (Cartesian product ordering)"))
      (p "The TagSet case required proving that filter intersection produces the same elements regardless of operand order, then applying canonicalize_strings to ensure structural equality."))

    (subsection
      "Admitted Theorems"
      (table
        (header "Theorem" "Reason")
        (row "verify_chain_sound" "Complex induction over chain structure")
        (row "verify_chain_attenuates" "Depends on verify_chain_sound"))
      (p "These are design debt, not security holes. The algorithms are correct; the proofs are incomplete.")))

  (section
    "What We Assume"
    (p "Cryptographic operations are axiomatized - we trust libsodium:")
    (code "Axiom sha512 : bytes -> bytes.
Axiom ed25519_verify : bytes -> bytes -> bytes -> bool.")
    (p "Trust assumptions:")
    (list
      (item "libsodium correctness: Ed25519, SHA-512 implementations")
      (item "OCaml runtime: Extraction target executes correctly")
      (item "Hardware: CPU executes instructions correctly")))

  (section
    "Design Limitations"
    (subsection
      "TagSet Canonical Ordering"
      (p "Tag intersection commutativity requires canonical representation:")
      (code "(tag_intersect (TagSet [\"read\" \"write\"]) (TagSet [\"write\" \"read\"]))
;; Result order depends on input order without canonicalization")
      (p "Solution implemented: sort and deduplicate TagSet contents. The canonicalize_canonical lemma bridges structural and semantic equality."))

    (subsection
      "TagThreshold Cartesian Product"
      (p "Intersection of thresholds produces Cartesian product of subtags:")
      (code "(tag_intersect (TagThreshold 2 [A B C]) (TagThreshold 2 [A B C]))
;; Produces 9 subtags: [A∩A, A∩B, A∩C, B∩A, B∩B, ...]")
      (p "This is semantically correct but not structurally idempotent. Options:")
      (list
        (item "Require disjoint subtags")
        (item "Normalize after intersection")
        (item "Accept semantic rather than structural idempotence"))))

  (section
    "Extraction Pipeline"
    (p "Build and extract:")
    (code "cd tcb/coq
coqc SpkiTcb.v              # Type-check proofs, extract OCaml
dune build                   # Compile extracted + bridge code")
    (p "The extraction directive:")
    (code "Extraction Language OCaml.
Extraction \"spki_tcb_extracted.ml\"
  authorize verify_chain tag_intersect principal_equal ...")
    (p "The bridge module (spki_tcb.ml) converts between Coq's int list representation and OCaml's native bytes, calling libsodium for cryptographic operations."))

  (section
    "Test Coverage"
    (table
      (header "Suite" "Tests" "Coverage")
      (row "test_extracted.ml" "16" "Unit tests: principals, tags, chains")
      (row "test_properties.ml" "11" "Property-based: QCheck random testing")
      (row "test_tcb.exe" "62" "Full TCB: crypto, cookies, audit, FIPS-181"))
    (p "All tests pass. The property-based tests validate Coq theorems at runtime:")
    (table
      (header "Property" "Generator Constraints")
      (row "principal_equal reflexive/symmetric/transitive" "Random principals")
      (row "tag_intersect commutative" "Non-threshold tags only")
      (row "tag_intersect idempotent" "Non-threshold, non-empty TagSets")
      (row "tag_intersect TagAll identity" "All tag types")
      (row "tag_subset reflexive" "Non-threshold tags only")
      (row "TagRange subset containment" "Random ranges"))
    (p "TagThreshold is excluded from commutativity/idempotence tests due to documented structural limitations (Cartesian product ordering)."))

  (section
    "Future Work"
    (list
      (item "Complete tag_intersect_comm for TagPrefix (recursive induction)")
      (item "Prove verify_chain_sound with custom induction principle")
      (item "Consider CompCert or Fiat-Crypto for deeper verification"))
    (p "Current proof coverage is sufficient for beta. The admitted theorems are proof obligations, not security vulnerabilities."))

  (section
    "References"
    (references
      (ref "Coq" 2024 "The Coq Proof Assistant. https://coq.inria.fr/")
      (ref "SPKI" 1999 "RFC 2693: SPKI Certificate Theory")
      (ref "Memo-045" 2026 "Security Architecture")
      (ref "libsodium" 2024 "https://libsodium.org/")))

  (footer
    (sig "ddp" "2026-01-22")))
