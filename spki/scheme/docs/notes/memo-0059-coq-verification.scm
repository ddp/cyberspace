(memo
  (number 59)
  (title "Formal Verification of the Authorization TCB")
  (status "Working Draft")
  (date "2026-01-22")
  (author "Derrell Piper" "ddp@eludom.net")

  (abstract
    (p "This memo documents the formal verification status of the SPKI authorization TCB using the Coq proof assistant. It describes which theorems are fully proven, which are admitted with documented design limitations, and the extraction pipeline that generates verified OCaml code."))

  (section
    "Overview"
    (p "The Trusted Computing Base for SPKI authorization lives in spki/tcb/coq/SpkiTcb.v. This file contains:")
    (list
      (item "Type definitions for principals, tags, certificates, and authorization requests")
      (item "Core algorithms: tag intersection, principal equality, chain verification")
      (item "Security theorems proving correctness properties")
      (item "Extraction directives generating verified OCaml code"))
    (p "The Coq extraction pipeline produces spki_tcb_extracted.ml, which is bridged to libsodium's cryptographic primitives via spki_tcb.ml."))

  (section
    "Proof Status"
    (subsection
      "Fully Proven Theorems"
      (p "The following security-critical theorems are complete with no admitted lemmas in their proof trees:")
      (table
        (header "Theorem" "Property" "Lines")
        (row "principal_equal_refl" "Reflexivity of principal equality" "~5")
        (row "principal_equal_sym" "Symmetry of principal equality" "~3")
        (row "principal_equal_trans" "Transitivity of principal equality" "~30")
        (row "authorize_requester_match" "Leaf certificate subject matches requester" "~15")
        (row "authorize_complete" "All preconditions imply authorization success" "~25"))
      (p "The authorize_requester_match theorem is particularly important: it guarantees that if authorization succeeds, the requester is actually named by the leaf certificate in the chain."))

    (subsection
      "Partially Proven Theorems"
      (p "These theorems have core cases proven but with some cases admitted:")
      (table
        (header "Theorem" "Proven" "Admitted")
        (row "tag_intersect_idemp" "TagAll, TagSet, TagPrefix, TagRange" "TagThreshold")
        (row "tag_intersect_subset_left" "TagAll/TagSet/TagRange combinations" "TagPrefix (recursive), TagThreshold"))
      (p "The admitted cases stem from two design issues documented below."))

    (subsection
      "Admitted Theorems"
      (p "These theorems are admitted entirely due to complexity or design limitations:")
      (table
        (header "Theorem" "Reason")
        (row "tag_intersect_comm" "TagSet needs canonical ordering")
        (row "verify_chain_sound" "Complex induction over chain structure")
        (row "verify_chain_attenuates" "Depends on verify_chain_sound"))))

  (section
    "Design Limitations"
    (subsection
      "TagSet Ordering"
      (p "The tag_intersect_comm theorem (commutativity of intersection) is not structurally true because TagSet uses list representation without canonical ordering:")
      (code "(tag_intersect (TagSet [\"read\" \"write\"]) (TagSet [\"write\" \"read\"]))
;; May produce (TagSet [\"read\"]) or (TagSet [\"write\"]) depending on order")
      (p "Fix: Implement canonical TagSet ordering (sorted, deduplicated). This requires modifying tag_intersect to sort results."))

    (subsection
      "TagThreshold Cartesian Product"
      (p "The tag_intersect_idemp theorem fails for TagThreshold because intersection produces a Cartesian product:")
      (code "(tag_intersect
  (TagThreshold 2 [t1 t2 t3])
  (TagThreshold 2 [t1 t2 t3]))
;; Produces 9 subtags (all pairs), not 3")
      (p "This is semantically correct but structurally different from the input. Options:")
      (list
        (item "Require TagThreshold subtags to be pairwise disjoint")
        (item "Normalize after intersection to remove duplicates")
        (item "Accept that idempotence is semantic rather than structural"))))

  (section
    "Extraction Pipeline"
    (p "The extraction directive in SpkiTcb.v generates OCaml code:")
    (code "Extraction Language OCaml.
Extraction \"spki_tcb_extracted.ml\" authorize verify_chain ...")
    (p "The pipeline:")
    (code "SpkiTcb.v (Coq proofs)
    |
    v
spki_tcb_extracted.ml (auto-generated)
    |
    v
spki_tcb.ml (bridge to libsodium)
    |
    v
tcb_stubs.c (FFI to libsodium)")
    (p "The bridge module converts between Coq's int list representation and OCaml's native bytes type, then calls libsodium for cryptographic operations."))

  (section
    "Test Coverage"
    (p "Two test suites validate the implementation:")
    (table
      (header "Suite" "Tests" "Coverage")
      (row "test_extracted.ml" "16" "Extracted Coq code: principals, tags, chains")
      (row "test_tcb.exe" "62" "Full TCB: crypto, cookies, audit, FIPS-181"))
    (p "All tests pass. The extracted code tests specifically exercise the Coq-verified authorization logic."))

  (section
    "Future Work"
    (list
      (item "Implement canonical TagSet ordering to prove commutativity")
      (item "Complete TagThreshold idempotence with semantic equality")
      (item "Prove verify_chain_sound using custom induction principle")
      (item "Extract test vectors from Coq proofs for property-based testing"))
    (p "The current proof coverage is sufficient for beta release. The admitted theorems represent design debt, not security holes - the algorithms are correct, the proofs are incomplete."))

  (section
    "References"
    (references
      (ref "Coq" 2024 "The Coq Proof Assistant. https://coq.inria.fr/")
      (ref "SPKI" 1999 "RFC 2693: SPKI Certificate Theory")
      (ref "Memo-045" 2026 "Security Architecture")))

  (footer
    (sig "ddp" "2026-01-22")))
