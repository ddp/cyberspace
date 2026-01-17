;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 9)
  (title "Shamir Secret Sharing")
  (section
    "Abstract"
    (p "This Memo specifies Shamir's Secret Sharing implementation for the Library of Cyberspace, enabling K-of-N threshold splitting and reconstruction of cryptographic keys and other secrets."))
  (section
    "Motivation"
    (p "Private keys are single points of failure:")
    (list
      (item "Key loss: Funds locked forever")
      (item "Key theft: Complete compromise")
      (item "Key escrow: Trust a third party?"))
    (p "Shamir's Secret Sharing provides:")
    (list
      (item "Threshold recovery: Any K of N shares reconstruct")
      (item "Information-theoretic security: K-1 shares reveal nothing")
      (item "Distributed custody: No single holder")
      (item "Backup flexibility: Geographic distribution"))
    (p "From Adi Shamir's 1979 paper \"How to Share a Secret\":")
    (blockquote "Split a secret into N pieces such that any K pieces suffice to reconstruct, but K-1 pieces reveal absolutely nothing."))
  (section
    "Specification"
    (subsection
      "Share Record"
      (code scheme "(define-record-type <shamir-share>\n  (make-shamir-share id threshold x y)\n  shamir-share?\n  (id share-id)            ; Symbol: share-1, share-2, etc.\n  (threshold share-threshold)  ; K value\n  (x share-x)              ; X-coordinate (1 to N)\n  (y share-y))             ; Y-coordinate (blob, same size as secret)"))
    (subsection
      "Splitting a Secret"
      (code scheme "(shamir-split secret #!key (threshold 3) (total 5))")
      (p "Parameters: - secret - Blob to split (any size, typically 32 or 64 bytes) - threshold - Minimum shares to reconstruct (K) - total - Total shares to create (N)")
      (p "Returns: List of N shamir-share records")
      (p "Algorithm: 1. For each byte of secret:    - Generate K-1 random coefficients    - Coefficient[0] = secret byte    - Polynomial: f(x) = a₀ + a₁x + a₂x² + ... + aₖ₋₁xᵏ⁻¹ 2. Evaluate polynomial at x = 1, 2, ..., N 3. Package (x, f(x)) pairs as shares"))
    (subsection
      "Reconstructing a Secret"
      (code scheme "(shamir-reconstruct shares)")
      (p "Parameters: - shares - List of at least K shamir-share records")
      (p "Returns: Reconstructed secret blob")
      (p "Algorithm: 1. Take first K shares 2. For each byte position:    - Use Lagrange interpolation    - Compute f(0) = secret byte 3. Assemble reconstructed secret")))
  (section
    "Galois Field Arithmetic"
    (p "Operations performed in GF(2⁸) with irreducible polynomial x⁸ + x⁴ + x³ + x + 1:")
    (code scheme "(define gf256-primitive #x11b)  ; x^8 + x^4 + x^3 + x + 1\n\n(define (gf256-mul a b)\n  \"Multiply in GF(2^8)\"\n  ...)\n\n(define (gf256-inv a)\n  \"Multiplicative inverse in GF(2^8)\"\n  ...)\n\n(define (gf256-poly-eval coeffs x)\n  \"Evaluate polynomial at x using Horner's method\"\n  ...)")
    (p "GF(2⁸) ensures: - All operations stay within byte range - No overflow issues - Proper field properties (every non-zero element has inverse)"))
  (section
    "Usage Examples"
    (subsection
      "Basic Secret Splitting"
      (code scheme "(import crypto-ffi)\n\n(sodium-init)\n\n;; Create a 32-byte secret\n(define secret (make-blob 32))\n;; ... fill with secret data ...\n\n;; Split into 5 shares, threshold 3\n(define shares (shamir-split secret threshold: 3 total: 5))\n\n;; Distribute shares to custodians\n(print \"Created \" (length shares) \" shares\")\n(print \"Threshold: \" (share-threshold (car shares)))"))
    (subsection
      "Reconstruction from K Shares"
      (code scheme ";; Collect any 3 shares\n(define collected (list share-1 share-3 share-5))\n\n;; Reconstruct\n(define reconstructed (shamir-reconstruct collected))\n\n;; Verify\n(if (equal? (blob->hex secret) (blob->hex reconstructed))\n    (print \"✓ Reconstruction successful!\")\n    (print \"✗ Reconstruction failed\"))"))
    (subsection
      "Ed25519 Key Backup"
      (code scheme ";; Generate keypair\n(define keypair (ed25519-keypair))\n(define public-key (car keypair))\n(define private-key (cadr keypair))\n\n;; Split private key (5-of-7 for production)\n(define key-shares (shamir-split private-key threshold: 5 total: 7))\n\n;; Later: reconstruct and verify\n(define recovered-key (shamir-reconstruct (take key-shares 5)))\n\n;; Test: sign with recovered key\n(define message \"Test message\")\n(define signature (ed25519-sign recovered-key message))\n(define valid? (ed25519-verify public-key message signature))\n\n(if valid?\n    (print \"✓ Recovered key produces valid signatures!\")\n    (print \"✗ Key recovery failed\"))")))
  (section
    "Security Properties"
    (subsection
      "Information-Theoretic Security"
      (p "With K-1 shares: - No information about secret is revealed - Not computationally hard - literally impossible - Even infinite compute power cannot break")
      (p "This is because K-1 points determine infinitely many degree-(K-1) polynomials."))
    (subsection
      "Share Independence"
      (p "Each share is uniformly random: - Looks like random bytes - No correlation between shares - Safe to store on untrusted media"))
    (subsection
      "Threshold Guarantee"
      (p "Exactly K shares required: - K shares: reconstruction succeeds - K-1 shares: no information - K+1 shares: still works (overdetermined)")))
  (section
    "Threshold Selection Guidelines"
    (table
      (header "Use Case " "Threshold " "Total " "Rationale ")
      (row "Personal backup " "2-of-3 " "Simple recovery ")
      (row "Team key " "3-of-5 " "Majority required ")
      (row "Organization root " "5-of-7 " "Supermajority ")
      (row "Hardware ceremony " "7-of-11 " "High assurance ")
      (row "Paranoid " "11-of-15 " "Maximum distribution "))
    (subsection
      "Considerations"
      (list
        (item "Availability: Higher K = harder to recover")
        (item "Security: Lower K = easier to collude")
        (item "Geography: Consider time zones for ceremonies")
        (item "Succession: What if custodians unavailable?"))))
  (section
    "Share Distribution"
    (subsection
      "Physical Security"
      (code "Share 1: Safe deposit box (Bank A)\nShare 2: Home safe\nShare 3: Attorney's vault\nShare 4: Trusted family member\nShare 5: Offshore location"))
    (subsection
      "Digital Storage"
      (code "Share 1: Hardware security module\nShare 2: Air-gapped laptop\nShare 3: Encrypted USB (passphrase protected)\nShare 4: Paper printout (secure location)\nShare 5: Tattoo (not recommended)"))
    (subsection
      "Geographic Distribution"
      (list
        (item "Different jurisdictions")
        (item "Different failure domains")
        (item "Different time zones (for ceremonies)"))))
  (section
    "Verification Without Reconstruction"
    (p "For periodic verification that shares are intact:")
    (code scheme ";; Each custodian verifies their share\n(define (verify-share share expected-id expected-threshold)\n  (and (eq? (share-id share) expected-id)\n       (= (share-threshold share) expected-threshold)\n       (= (blob-size (share-y share)) expected-length)))")
    (p "Full reconstruction should be rare: - Key rotation ceremonies - Emergency recovery - Succession events"))
  (section
    "Integration with Threshold Signatures"
    (p "Two complementary approaches:")
    (subsection
      "Shamir for Key Backup (This Memo)"
      (code "Private key → split → N shares\nRecovery: K shares → reconstruct → use key"))
    (subsection
      "Multi-Signature for Governance (Memo-008)"
      (code "N parties → N keys → N signatures\nVerification: count valid ≥ K")
      (p "Use Shamir when: - Backing up existing keys - Emergency recovery scenarios - Single key must be reconstructable")
      (p "Use Multi-Sig when: - Ongoing governance decisions - Need audit trail of who signed - Asynchronous authorization")))
  (section
    "Security Considerations"
    (subsection
      "Threats Mitigated"
      (table
        (header "Threat " "Mitigation ")
        (row "Key loss " "Any K shares recover ")
        (row "Single compromise " "Need K colluding ")
        (row "Insider attack " "Distribute to independent parties ")
        (row "Coercion " "Geographic/jurisdictional diversity ")))
    (subsection
      "Threats Remaining"
      (table
        (header "Threat " "Notes ")
        (row "K colluding parties " "Fundamental limitation ")
        (row "Poor share storage " "Operational security ")
        (row "Side channels during reconstruction " "Use secure environments ")
        (row "Weak random generation " "Use libsodium ")))
    (subsection
      "Operational Security"
      (list
        (item "Generation: Air-gapped machine, secure random")
        (item "Distribution: Out-of-band verification")
        (item "Storage: Encrypted, physically secure")
        (item "Reconstruction: Secure room, witnesses")
        (item "Destruction: Secure wipe after use"))))
  (section
    "Implementation Notes"
    (subsection
      "Dependencies"
      (list
        (item "libsodium")
        (item "Secure random number generation - srfi-4 - u8vectors for byte manipulation")))
    (subsection
      "Performance"
      (list
        (item "Split: O(N × K × secretlength)")
        (item "Reconstruct: O(K² × secretlength)")
        (item "GF(2⁸) operations: O(1) per byte")))
    (subsection
      "Limitations"
      (list
        (item "Secret size: Arbitrary (but typically ≤ 64 bytes)")
        (item "Share count: Practical limit ~255 (byte x-coordinates)")
        (item "Threshold: 2 ≤ K ≤ N"))))
  (section
    "References"
    (list
      (item "Shamir, A. (1979). How to share a secret. Communications of the ACM.")
      (item "Blakley, G. R. (1979). Safeguarding cryptographic keys.")
      (item "Beimel, A. (2011). Secret-Sharing Schemes: A Survey.")
      (item "NIST SP 800-57. Recommendation for Key Management.")))
  (section
    "Changelog"
    (list
      (item "2026-01-06")
      (item "Initial specification"))))

