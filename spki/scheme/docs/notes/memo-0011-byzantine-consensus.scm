;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 11)
  (title "Byzantine Consensus")
  (section
    "Abstract"
    (p "This Memo specifies Byzantine fault-tolerant consensus for Cyberspace federation, enabling agreement among distributed vaults even when some participants are faulty or malicious. N nodes tolerate up to f failures where N ≥ 3f + 1."))
  (section
    "Motivation"
    (p "Federation (Memo-010) assumes honest peers. Reality differs:")
    (list
      (item "Crash failures: Nodes go offline")
      (item "Byzantine failures: Nodes lie, equivocate, or attack")
      (item "Network partitions: Messages delayed or lost")
      (item "Sybil attacks: Fake identities flood the network"))
    (p "Byzantine consensus provides:")
    (p "1. Safety: Honest nodes agree on same value 2. Liveness: System makes progress despite failures 3. Fault tolerance: Survives f failures with 3f+1 nodes")
    (p "From Lamport, Shostak, and Pease (1982):")
    (blockquote "The Byzantine Generals Problem: reaching agreement in the presence of traitors."))
  (section
    "Specification"
    (subsection
      "System Model"
      (code "Nodes:        N = 3f + 1 (tolerates f Byzantine faults)\nNetwork:      Asynchronous with eventual delivery\nCryptography: Ed25519 signatures (authenticated channels)"))
    (subsection
      "Consensus Properties"
      (p "Agreement: If honest node i decides v, honest node j decides v.")
      (p "Validity: If all honest nodes propose v, decision is v.")
      (p "Termination: All honest nodes eventually decide."))
    (subsection
      "Protocol: Practical Byzantine Fault Tolerance (PBFT)"
      (code "Phase 1: PRE-PREPARE\n  Primary broadcasts ⟨PRE-PREPARE, v, n, sig⟩\n\nPhase 2: PREPARE\n  On valid PRE-PREPARE, broadcast ⟨PREPARE, v, n, sig⟩\n  Collect 2f PREPARE messages\n\nPhase 3: COMMIT\n  On 2f+1 PREPARE, broadcast ⟨COMMIT, v, n, sig⟩\n  Collect 2f+1 COMMIT messages\n\nDecision:\n  On 2f+1 COMMIT, decide v"))
    (subsection
      "Message Formats"
      (code scheme "(consensus-message\n  (type pre-prepare)\n  (view 0)\n  (sequence 42)\n  (value-hash \"sha512:...\")\n  (from #${primary-pubkey})\n  (signature #${ed25519-sig}))\n\n(consensus-message\n  (type prepare)\n  (view 0)\n  (sequence 42)\n  (value-hash \"sha512:...\")\n  (from #${replica-pubkey})\n  (signature #${ed25519-sig}))\n\n(consensus-message\n  (type commit)\n  (view 0)\n  (sequence 42)\n  (from #${replica-pubkey})\n  (signature #${ed25519-sig}))")))
  (section
    "View Change"
    (p "When primary fails or is Byzantine:")
    (code "1. Replica timeout on PRE-PREPARE\n2. Broadcast ⟨VIEW-CHANGE, v+1, prepared-proofs⟩\n3. New primary collects 2f+1 VIEW-CHANGE\n4. New primary broadcasts ⟨NEW-VIEW, v+1, proofs⟩\n5. Resume protocol in new view"))
  (section
    "Application to Cyberspace"
    (subsection
      "Federation Ordering"
      (code scheme "(consensus-propose\n  (action release-publish)\n  (version \"2.0.0\")\n  (proposer #${alice-key}))\n\n;; After consensus:\n(consensus-decided\n  (sequence 42)\n  (action release-publish)\n  (version \"2.0.0\")\n  (decided-by (quorum ...)))"))
    (subsection
      "Threshold Governance Integration"
      (p "Combine with Memo-008: - Consensus on what to do - Threshold signatures on authorization")
      (code scheme "(governance-decision\n  (consensus-sequence 42)\n  (action deploy-production)\n  (threshold-met 3-of-5)\n  (signers (alice carol dave)))")))
  (section
    "Optimizations"
    (subsection
      "Speculation"
      (p "Execute optimistically before commit:")
      (code "Tentative execution after 2f+1 PREPARE\nRollback if COMMIT fails"))
    (subsection
      "Batching"
      (p "Amortize consensus over multiple operations:")
      (code "(consensus-batch\n  (sequence 42)\n  (operations\n    (release-publish \"2.0.0\")\n    (release-publish \"2.0.1\")\n    (config-update ...)))"))
    (subsection
      "Fast Path"
      (p "When all replicas agree initially:")
      (code "Skip PREPARE phase\nDirect to COMMIT with 3f+1 matching responses")))
  (section
    "Security Considerations"
    (subsection
      "Threat Model"
      (p "Tolerates: - f Byzantine nodes (arbitrary behavior) - Network delays and reordering - Message loss (with retransmission)")
      (p "Requires: - N ≥ 3f + 1 total nodes - Authenticated channels (signatures) - Eventual message delivery"))
    (subsection
      "Attack Resistance"
      (table
        (header "Attack " "Mitigation ")
        (row "Equivocation " "Signatures prove inconsistency ")
        (row "Replay " "Sequence numbers, view numbers ")
        (row "Denial of service " "View change, rate limiting ")
        (row "Sybil " "SPKI admission control "))))
  (section
    "Complexity"
    (table
      (header "Metric " "Value ")
      (row "Message complexity " "O(N²) per decision ")
      (row "Communication rounds " "3 (normal case) ")
      (row "Cryptographic operations " "O(N) signatures/verifies ")))
  (section
    "Implementation Notes"
    (subsection
      "State Machine"
      (code scheme "(define-record-type <pbft-state>\n  (make-pbft-state view sequence log prepared committed)\n  pbft-state?\n  (view pbft-view)\n  (sequence pbft-sequence)\n  (log pbft-log)              ; sequence → messages\n  (prepared pbft-prepared)    ; sequence → value\n  (committed pbft-committed)) ; sequence → value"))
    (subsection
      "Dependencies"
      (list
        (item "crypto-ffi")
        (item "Ed25519 signatures - audit")
        (item "Decision logging")
        (item "Network transport (TCP, QUIC)"))))
  (section
    "References"
    (p "1. Lamport, L., Shostak, R., & Pease, M. (1982). The Byzantine Generals Problem. 2. Castro, M., & Liskov, B. (1999). Practical Byzantine Fault Tolerance. 3. Yin, M., et al. (2019). HotStuff: BFT Consensus with Linearity and Responsiveness. 4. Memo-008: Threshold Signature Governance 5. Memo-010: Federation Protocol"))
  (section
    "Changelog"
    (list
      (item "2026-01-06")
      (item "Initial specification"))))

