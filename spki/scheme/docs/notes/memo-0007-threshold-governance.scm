;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 7)
  (title "Threshold Signature Governance")
  (section
    "Abstract"
    (p "This Memo specifies the threshold signature system for Cyberspace governance, enabling K-of-N multi-party authorization for critical operations. Democracy in code: no single point of failure, no rogue administrator."))
  (section
    "Motivation"
    (p "Critical operations require collective authorization:")
    (list
      (item "Release signing: Multiple maintainers must approve")
      (item "Deployment: Operations team quorum required")
      (item "Key ceremonies: Distributed trust for root keys")
      (item "Emergency response: Prevent unilateral action"))
    (p "Traditional approaches fail: - Shared passwords: Who has it? Who used it? - Sudo access: Root is root - Approval workflows: Soft controls, bypassable")
    (p "Threshold signatures provide cryptographic enforcement:")
    (blockquote "K valid signatures required. Not K-1. Not bypass. Mathematics."))
  (section
    "Specification"
    (subsection
      "Tiered Signing Model"
      (code "┌─────────────────────────────────────────────────────────────┐\n│                    SIGNING TIERS                            │\n├─────────────────────────────────────────────────────────────┤\n│  Development     1-of-1    Single developer can iterate    │\n│  Staging         2-of-2    Peer review required             │\n│  Production      3-of-5    Governance council quorum        │\n│  Emergency       5-of-7    Full council for critical ops    │\n└─────────────────────────────────────────────────────────────┘"))
    (subsection
      "Script Signature Record"
      (code scheme "(define-record-type <script-signature>\n  (make-script-signature signer signature timestamp)\n  script-signature?\n  (signer signature-signer)        ; Ed25519 public key (32 bytes)\n  (signature signature-value)      ; Ed25519 signature (64 bytes)\n  (timestamp signature-timestamp)) ; Unix epoch seconds"))
    (subsection
      "Signing a Script"
      (code scheme "(define (sign-script script-content private-key #!optional public-key)\n  \"Sign script content with a private key\"\n  ...)")
      (p "Process: 1. Convert content to blob if string 2. Derive public key from private (if not provided) 3. Sign content with Ed25519 4. Record timestamp 5. Return script-signature record"))
    (subsection
      "Verifying Single Signature"
      (code scheme "(define (verify-script script-content signature-record)\n  \"Verify a script signature\"\n  (ed25519-verify (signature-signer signature-record)\n                  content-blob\n                  (signature-value signature-record)))"))
    (subsection
      "Threshold Verification"
      (code scheme "(define (verify-threshold-script script-content signature-records threshold)\n  \"Verify threshold signatures on a script\n   Returns: #t if at least K signatures are valid\"\n  (let* ((valid-sigs (filter (lambda (sig)\n                               (verify-script script-content sig))\n                             signature-records))\n         (valid-count (length valid-sigs)))\n    (>= valid-count threshold)))")))
  (section
    "Signature File Format"
    (code scheme ";; deploy.sig\n((signature \"hex-signature\" \"hex-pubkey\" 1767685100)\n (signature \"hex-signature\" \"hex-pubkey\" 1767685200)\n (signature \"hex-signature\" \"hex-pubkey\" 1767685300))")
    (p "Each entry contains: - Signature bytes (hex-encoded) - Signer public key (hex-encoded) - Timestamp (Unix epoch)"))
  (section
    "CLI Interface"
    (subsection
      "cyberspace verify"
      (code bash "$ cyberspace verify deploy.scm deploy.sig \\\n    --threshold 3 \\\n    --keys alice.pub bob.pub carol.pub dave.pub eve.pub\n\n=== Cyberspace Script Verification ===\n\nScript:     deploy.scm\nSignatures: deploy.sig\nThreshold:  3\nKeys:       5 provided\n\nFound 3 signature(s) in file\n  Signature 1: ✓ VALID (signer: cbc9b260da65f6a7...)\n  Signature 2: ✓ VALID (signer: a5f8c9e3d2b1f0e4...)\n  Signature 3: ✓ VALID (signer: 7d3e8b2c1a0f5e4d...)\n\n✓ SUCCESS: Script verified with 3-of-3 threshold"))
    (subsection
      "cyberspace run"
      (code bash "$ cyberspace run deploy.scm deploy.sig \\\n    --threshold 3 \\\n    --keys alice.pub bob.pub carol.pub dave.pub eve.pub\n\n=== Cyberspace Script Verification ===\n...\n✓ SUCCESS: Script verified with 3-of-5 threshold\n\n=== Executing Script ===\n(seal-release \"2.0.0\"\n  message: \"Major release with new governance model\"\n  preserve: #t)")))
  (section
    "Governance Scenarios"
    (subsection
      "Production Deployment (3-of-5)"
      (code scheme ";; Governance Council: Alice, Bob, Carol, Dave, Eve\n;; Threshold: 3 signatures required\n\n(define deployment-script\n  \"(seal-release \\\"2.0.0\\\"\n    message: \\\"Major release\\\"\n    preserve: #t)\")\n\n;; Alice signs\n(define sig-alice\n  (sign-script deployment-script alice-private alice-public))\n\n;; Carol signs\n(define sig-carol\n  (sign-script deployment-script carol-private carol-public))\n\n;; Dave signs\n(define sig-dave\n  (sign-script deployment-script dave-private dave-public))\n\n;; Verify threshold\n(verify-threshold-script deployment-script\n                        (list sig-alice sig-carol sig-dave)\n                        3)\n;; => #t"))
    (subsection
      "Insufficient Signatures"
      (code scheme ";; Only 2 signatures\n(define insufficient-sigs\n  (list sig-alice sig-carol))\n\n(verify-threshold-script deployment-script insufficient-sigs 3)\n;; => #f (rejected: need 3, got 2)"))
    (subsection
      "Tampered Script Detection"
      (code scheme ";; Attacker modifies script\n(define tampered-script\n  \"(seal-release \\\"2.0.0\\\"\n    message: \\\"HACKED - deploying malware\\\"\n    preserve: #t)\")\n\n(verify-threshold-script tampered-script sufficient-sigs 3)\n;; => #f (signatures don't match modified content)")))
  (section
    "Multi-Signature vs Shamir"
    (p "Two threshold approaches exist:")
    (subsection
      "Multi-Signature (This Memo)"
      (code "Each party: own keypair\nSigning:    each signs independently\nVerify:     count valid signatures ≥ K\nUse case:   governance, approvals")
      (p "Advantages: - Each party maintains own key - Clear audit trail (who signed) - Simple revocation (by key) - No key reconstruction"))
    (subsection
      "Shamir Splitting (Memo-008)"
      (code "Single key: split into N shares\nSigning:    K parties reconstruct, sign once\nVerify:     single signature\nUse case:   key backup, recovery")
      (p "Advantages: - Single signature output - Key never fully assembled (in advanced schemes) - Smaller signature files")
      (p "For governance, multi-signature is preferred: - Accountability (which individuals approved) - No reconstruction ceremony - Works asynchronously")))
  (section
    "Security Considerations"
    (subsection
      "Threat Model"
      (p "Protected against: - Single compromised key (need K) - Rogue administrator (need quorum) - Script tampering (signatures fail) - Replay of old scripts (timestamps, context)")
      (p "Not protected against: - K compromised keys - All parties colluding - Side-channel on signing devices"))
    (subsection
      "Key Management"
      (p "1. Generation: Secure random via libsodium 2. Storage: Hardware tokens preferred, encrypted files acceptable 3. Distribution: Out-of-band verification of public keys 4. Rotation: New ceremony, revoke old keys"))
    (subsection
      "Threshold Selection"
      (table
        (header "Scenario " "Threshold " "Rationale ")
        (row "Development " "1-of-1 " "Fast iteration ")
        (row "Staging " "2-of-2 " "Peer review ")
        (row "Production " "3-of-5 " "Majority quorum ")
        (row "Root key " "5-of-7 " "Supermajority ")
        (row "Emergency " "N-of-N " "Full consensus "))))
  (section
    "Audit Integration"
    (p "Every verified execution records:")
    (code scheme "(audit-append\n  actor: (threshold-verifier-list)\n  action: (list 'script-execute script-hash)\n  motivation: \"Production deployment authorized\"\n  context: (list 'threshold 3 'signatures 3))")
    (p "Audit trail shows: - Which signers authorized - What script was executed - When authorization occurred - Threshold requirements met"))
  (section
    "Implementation Notes"
    (subsection
      "Dependencies"
      (list
        (item "crypto-ffi")
        (item "Ed25519 operations - cert")
        (item "SPKI integration - audit")
        (item "Trail recording")))
    (subsection
      "Performance"
      (list
        (item "Signature verification: ~10μs per Ed25519 verify")
        (item "Threshold check: O(N) where N = signature count")
        (item "No network round-trips (offline verification)"))))
  (section
    "References"
    (p "1. Boneh, D., et al. (2001). Short Signatures from the Weil Pairing. 2. Gennaro, R., et al. (2016). Threshold-optimal DSA/ECDSA signatures. 3. NIST SP 800-57. Recommendation for Key Management. 4. Memo-004: SPKI Authorization Integration"))
  (section
    "Changelog"
    (list
      (item "2026-01-06")
      (item "Initial specification"))))

