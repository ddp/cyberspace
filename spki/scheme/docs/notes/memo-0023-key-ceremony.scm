;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 23)
  (title "Key Ceremony Protocol")
  (section
    "Abstract"
    (p "This Memo specifies key ceremony protocols for the Library of Cyberspace: the ritualized generation, distribution, and activation of cryptographic keys with witnessed verification. Key ceremonies establish roots of trust through transparent, auditable, multi-party processes."))
  (section
    "Motivation"
    (p "Keys are the foundation of all cryptographic trust:")
    (list
      (item "Generate wrong")
      (item "Everything built on them fails")
      (item "Store wrong")
      (item "Compromise propagates everywhere")
      (item "Distribute wrong")
      (item "Man-in-the-middle forever")
      (item "No witnesses")
      (item "No one believes you did it right"))
    (p "Key ceremonies solve this through:")
    (list
      (item "Witnessed generation")
      (item "Multiple parties verify randomness")
      (item "Split custody")
      (item "No single point of compromise")
      (item "Documented process")
      (item "Reproducible and auditable")
      (item "Air-gapped execution")
      (item "Network isolation during critical operations"))
    (p "The Library requires key ceremonies for:")
    (list
      (item "Vault master keys")
      (item "Threshold signing keys")
      (item "Root certificates")
      (item "Recovery keys")))
  (section
    "Ceremony Types"
    (subsection
      "Type 1: Single Key Generation"
      (p "For individual vault keys:")
      (code "┌─────────────────────────────────────────┐\n│          SINGLE KEY CEREMONY            │\n├─────────────────────────────────────────┤\n│ Participants: 1 generator, 2+ witnesses │\n│ Duration: ~30 minutes                   │\n│ Output: 1 keypair                       │\n└─────────────────────────────────────────┘"))
    (subsection
      "Type 2: Threshold Key Generation"
      (p "For M-of-N shared keys (Memo-008, Memo-007):")
      (code "┌─────────────────────────────────────────┐\n│        THRESHOLD KEY CEREMONY           │\n├─────────────────────────────────────────┤\n│ Participants: N shareholders, 2+ witnesses │\n│ Duration: ~2 hours                      │\n│ Output: N shares, 1 public key          │\n└─────────────────────────────────────────┘"))
    (subsection
      "Type 3: Root Certificate Ceremony"
      (p "For establishing certificate authority:")
      (code "┌─────────────────────────────────────────┐\n│       ROOT CERTIFICATE CEREMONY         │\n├─────────────────────────────────────────┤\n│ Participants: 3-5 officers, auditor     │\n│ Duration: ~4 hours                      │\n│ Output: Root cert, subordinate certs    │\n└─────────────────────────────────────────┘"))
    (subsection
      "Type 4: Recovery Key Ceremony"
      (p "For generating disaster recovery keys:")
      (code "┌─────────────────────────────────────────┐\n│        RECOVERY KEY CEREMONY            │\n├─────────────────────────────────────────┤\n│ Participants: Board members, escrow     │\n│ Duration: ~3 hours                      │\n│ Output: Recovery shares in escrow       │\n└─────────────────────────────────────────┘")))
  (section
    "Ceremony Environment"
    (subsection
      "Physical Requirements"
      (code "SECURE ROOM CHECKLIST:\n[ ] No network connectivity\n[ ] No wireless devices\n[ ] Faraday shielding (ideal)\n[ ] Physical access control\n[ ] Video recording (optional)\n[ ] Tamper-evident bags for media\n[ ] Multiple witnesses present"))
    (subsection
      "Equipment"
      (code scheme "(ceremony-equipment\n  (primary\n    (air-gapped-computer \"dedicated ceremony machine\")\n    (hardware-rng \"dice, hardware token, or both\")\n    (secure-storage \"HSM or encrypted USB drives\")\n    (printer \"for paper backup\"))\n  (verification\n    (independent-computer \"verify signatures\")\n    (hash-calculator \"verify digests\"))\n  (documentation\n    (camera \"photograph key steps\")\n    (ceremony-log \"paper record\")\n    (witness-signatures \"attestation forms\")))"))
    (subsection
      "Software"
      (code scheme "(ceremony-software\n  (os \"minimal Linux, verified hash\")\n  (key-generator \"library keygen or gpg\")\n  (shamir-split \"ssss or library implementation\")\n  (hash-tool \"sha256sum\")\n  (encryption \"age for share protection\"))")))
  (section
    "Single Key Ceremony"
    (subsection
      "Pre-Ceremony"
      (code scheme "(define (pre-ceremony-checklist ceremony-id)\n  '((verify-room \"Secure room confirmed\")\n    (verify-equipment \"All equipment present and functional\")\n    (verify-participants \"All participants identified\")\n    (verify-software \"Software hashes match expected\")\n    (document-start \"Record ceremony start time\")\n    (collect-devices \"All phones/devices collected\")))"))
    (subsection
      "Entropy Generation"
      (code scheme "(define (generate-entropy witnesses)\n  \"Generate verifiable randomness\"\n  (let* (;; Hardware RNG contribution\n         (hw-entropy (read-hardware-rng 32))\n\n         ;; Dice rolls - each witness rolls\n         (dice-entropy\n          (apply bytes-append\n                 (map (lambda (w)\n                        (let ((rolls (witness-dice-rolls w 20)))\n                          (sha256 (rolls->bytes rolls))))\n                      witnesses)))\n\n         ;; Timestamp contribution\n         (time-entropy (sha256 (timestamp->bytes (current-time))))\n\n         ;; Combine all sources\n         (combined (bytes-append hw-entropy dice-entropy time-entropy)))\n\n    ;; Final mixing\n    (sha256 combined)))\n\n(define (witness-dice-rolls witness count)\n  \"Witness rolls dice, records each result\"\n  (let loop ((i 0) (rolls '()))\n    (if (= i count)\n        (reverse rolls)\n        (let ((roll (read-dice-roll witness)))\n          (announce (format \"Witness ~a roll ~a: ~a\" witness i roll))\n          (loop (+ i 1) (cons roll rolls))))))"))
    (subsection
      "Key Generation"
      (code scheme "(define (generate-ceremony-key entropy purpose)\n  \"Generate key from ceremony entropy\"\n  (let* (;; Derive key material\n         (key-material (hkdf entropy\n                             salt: (string->bytes purpose)\n                             info: \"ceremony-key\"\n                             length: 32))\n\n         ;; Generate Ed25519 keypair\n         (keypair (ed25519-keypair-from-seed key-material))\n         (public-key (keypair-public keypair))\n         (secret-key (keypair-secret keypair)))\n\n    ;; Announce public key\n    (announce \"Public key generated:\")\n    (announce (bytes->hex public-key))\n\n    ;; Return both (secret handled carefully)\n    keypair))"))
    (subsection
      "Verification"
      (code scheme "(define (verify-key-generation keypair witnesses)\n  \"Witnesses verify key was generated correctly\"\n\n  ;; Sign test message\n  (let* ((test-message \"ceremony verification test\")\n         (signature (ed25519-sign (keypair-secret keypair) test-message)))\n\n    ;; Each witness verifies on independent machine\n    (for-each\n      (lambda (witness)\n        (let ((verified (witness-verify witness\n                                        (keypair-public keypair)\n                                        test-message\n                                        signature)))\n          (announce (format \"Witness ~a verification: ~a\"\n                           witness\n                           (if verified \"PASS\" \"FAIL\")))\n          (unless verified\n            (error \"Verification failed - abort ceremony\"))))\n      witnesses)))"))
    (subsection
      "Key Storage"
      (code scheme "(define (store-ceremony-key keypair ceremony-id storage-method)\n  \"Securely store generated key\"\n  (case storage-method\n    ((hsm)\n     ;; Store in hardware security module\n     (hsm-store ceremony-id (keypair-secret keypair)))\n\n    ((encrypted-usb)\n     ;; Encrypt to USB drive\n     (let ((passphrase (generate-passphrase 6)))\n       (announce \"Passphrase for USB backup:\")\n       (announce passphrase)\n       (write-encrypted-usb ceremony-id\n                           (keypair-secret keypair)\n                           passphrase)))\n\n    ((paper)\n     ;; Print paper backup\n     (print-paper-backup ceremony-id\n                        (keypair-secret keypair)\n                        (keypair-public keypair)))\n\n    ((shamir)\n     ;; Split into shares (see threshold ceremony)\n     (shamir-split-key keypair ceremony-id))))"))
    (subsection
      "Ceremony Record"
      (code scheme "(define (create-ceremony-record ceremony-id keypair witnesses)\n  \"Create signed ceremony record\"\n  (let ((record\n         (key-ceremony\n           (id ,ceremony-id)\n           (type single-key)\n           (timestamp ,(current-time))\n           (public-key ,(bytes->hex (keypair-public keypair)))\n           (algorithm ed25519)\n           (witnesses\n            ,(map (lambda (w)\n                    (witness\n                      (name ,(witness-name w))\n                      (public-key ,(witness-pubkey w))\n                      (attestation \"I witnessed this key ceremony\")))\n                  witnesses))\n           (entropy-sources (hardware-rng dice timestamps))\n           (storage-method ,(storage-method)))))\n\n    ;; Sign by ceremony officer\n    (let ((signed (sign-ceremony-record record)))\n      ;; Counter-sign by witnesses\n      (for-each\n        (lambda (w)\n          (witness-countersign signed w))\n        witnesses)\n\n      ;; Store in audit trail\n      (audit-append\n        action: `(key-ceremony ,ceremony-id)\n        motivation: \"Key generation ceremony completed\")\n\n      signed)))")))
  (section
    "Threshold Key Ceremony"
    (subsection
      "Share Distribution"
      (code scheme "(define (threshold-ceremony n k ceremony-id)\n  \"Generate threshold key with N shares, K required\"\n\n  ;; Generate master entropy (same as single key)\n  (let* ((entropy (generate-entropy witnesses))\n         (keypair (generate-ceremony-key entropy ceremony-id))\n\n         ;; Split secret into shares\n         (shares (shamir-split (keypair-secret keypair) n k)))\n\n    ;; Distribute shares to shareholders\n    (for-each\n      (lambda (i share shareholder)\n        (announce (format \"Distributing share ~a to ~a\" i shareholder))\n        (distribute-share share shareholder ceremony-id))\n      (iota n)\n      shares\n      shareholders)\n\n    ;; Verify reconstruction (with K volunteers)\n    (verify-threshold-reconstruction shares k keypair)\n\n    ;; Create ceremony record\n    (create-threshold-ceremony-record ceremony-id\n                                      keypair\n                                      n k\n                                      shareholders\n                                      witnesses)))"))
    (subsection
      "Share Protection"
      (code scheme "(define (distribute-share share shareholder ceremony-id)\n  \"Encrypt share for specific shareholder\"\n  (let* (;; Encrypt share to shareholder's key\n         (encrypted (age-encrypt share (shareholder-pubkey shareholder)))\n\n         ;; Create share package\n         (package\n          `(share-package\n            (ceremony-id ,ceremony-id)\n            (shareholder ,(shareholder-id shareholder))\n            (share-number ,(share-index share))\n            (encrypted-share ,(bytes->base64 encrypted))\n            (verification-hash ,(sha256 share)))))\n\n    ;; Print or store\n    (deliver-share-package package shareholder)))"))
    (subsection
      "Reconstruction Test"
      (code scheme "(define (verify-threshold-reconstruction shares k expected-keypair)\n  \"Verify shares reconstruct correctly\"\n\n  ;; Select K volunteers\n  (let* ((volunteers (take (shuffle shareholders) k))\n         (volunteer-shares (map get-share-from-volunteer volunteers))\n\n         ;; Reconstruct secret\n         (reconstructed (shamir-reconstruct volunteer-shares))\n\n         ;; Verify matches\n         (matches (equal? reconstructed (keypair-secret expected-keypair))))\n\n    (announce (format \"Reconstruction test with ~a shareholders: ~a\"\n                     k\n                     (if matches \"PASS\" \"FAIL\")))\n\n    (unless matches\n      (error \"Reconstruction failed - shares may be corrupted\"))\n\n    ;; Securely clear reconstructed secret from memory\n    (secure-clear reconstructed)))")))
  (section
    "Root Certificate Ceremony"
    (subsection
      "Certificate Generation"
      (code scheme "(define (root-certificate-ceremony ceremony-id validity-years)\n  \"Generate root certificate authority\"\n\n  (let (;; Generate root keypair\n         (root-keypair (ceremony-generate-key \"root-ca\"))\n\n         ;; Create self-signed root certificate\n         (root-cert\n          `(spki-cert\n            (issuer ,(keypair-public root-keypair))\n            (subject ,(keypair-public root-keypair))\n            (capability (action sign-certificates))\n            (validity\n              (not-before ,(current-time))\n              (not-after ,(+ (current-time)\n                            ( validity-years 365 24 3600))))\n            (extensions\n              (basic-constraints (ca #t) (path-length 2))\n              (key-usage (cert-sign crl-sign)))))\n\n         ;; Sign root certificate\n         (signed-root (sign-cert root-keypair root-cert)))\n\n    ;; Witnesses verify root certificate\n    (verify-root-certificate signed-root witnesses)\n\n    ;; Generate subordinate CA certificates\n    (let ((subordinates (generate-subordinate-certs root-keypair)))\n\n      ;; Create ceremony record\n      (create-root-ceremony-record ceremony-id\n                                  signed-root\n                                  subordinates\n                                  witnesses))))"))
    (subsection
      "Trust Anchor Publication"
      (code scheme "(define (publish-trust-anchor root-cert ceremony-record)\n  \"Publish root certificate as trust anchor\"\n\n  ;; Multiple publication channels\n  (publish-to-vault root-cert ceremony-record)\n  (publish-to-website root-cert ceremony-record)\n  (publish-to-transparency-log root-cert ceremony-record)\n\n  ;; Generate human-readable fingerprint\n  (let ((fingerprint (cert-fingerprint root-cert)))\n    (announce \"Root certificate fingerprint:\")\n    (announce (fingerprint->words fingerprint))\n    (announce (fingerprint->hex fingerprint))))")))
  (section
    "Recovery Key Ceremony"
    (subsection
      "Escrow Protocol"
      (code scheme "(define (recovery-key-ceremony n k escrow-agents)\n  \"Generate recovery keys with escrow\"\n\n  (let* (;; Generate recovery keypair\n         (recovery-keypair (ceremony-generate-key \"recovery\"))\n\n         ;; Split into shares\n         (shares (shamir-split (keypair-secret recovery-keypair) n k))\n\n         ;; Encrypt each share to escrow agent\n         (escrowed-shares\n          (map (lambda (share agent)\n                 (escrow-share share agent))\n               shares\n               escrow-agents)))\n\n    ;; Store escrow metadata (not shares)\n    (create-escrow-record recovery-keypair escrowed-shares)\n\n    ;; Test recovery (with k agents)\n    (test-recovery-process escrowed-shares k recovery-keypair)))\n\n(define (escrow-share share agent)\n  \"Encrypt share for escrow agent\"\n  `(escrowed-share\n    (agent ,(agent-id agent))\n    (encrypted ,(age-encrypt share (agent-pubkey agent)))\n    (verification ,(sha256 share))\n    (escrow-date ,(current-time))))"))
    (subsection
      "Recovery Execution"
      (code scheme "(define (execute-recovery escrowed-shares agents)\n  \"Execute recovery using escrowed shares\"\n\n  ;; Verify quorum present\n  (unless (>= (length agents) recovery-threshold)\n    (error \"Insufficient agents for recovery\"))\n\n  ;; Each agent decrypts their share\n  (let* ((decrypted-shares\n          (map (lambda (agent escrowed)\n                 (agent-decrypt-share agent escrowed))\n               agents\n               (filter-by-agent escrowed-shares agents)))\n\n         ;; Verify share hashes\n         (_ (verify-share-hashes decrypted-shares escrowed-shares))\n\n         ;; Reconstruct\n         (recovered-secret (shamir-reconstruct decrypted-shares)))\n\n    ;; Audit recovery event\n    (audit-append\n      action: '(recovery-executed)\n      motivation: \"Disaster recovery initiated\"\n      priority: 'critical)\n\n    recovered-secret))")))
  (section
    "Ceremony Audit Trail"
    (subsection
      "Ceremony Log Format"
      (code scheme "(ceremony-log\n  (ceremony-id \"KC-2026-001\")\n  (type root-certificate)\n  (date \"2026-01-07\")\n  (location \"Secure facility, Building A, Room 101\")\n\n  (participants\n    (officer \"Alice Smith\" (role ceremony-officer))\n    (officer \"Bob Jones\" (role key-custodian))\n    (witness \"Carol White\" (role witness))\n    (witness \"David Brown\" (role witness))\n    (auditor \"Eve Green\" (role auditor)))\n\n  (timeline\n    (event \"09:00\" \"Room secured, equipment verified\")\n    (event \"09:15\" \"Participants identified, devices collected\")\n    (event \"09:30\" \"Software verification complete\")\n    (event \"09:45\" \"Entropy generation started\")\n    (event \"10:00\" \"Dice rolls complete, 100 rolls recorded\")\n    (event \"10:15\" \"Key generation complete\")\n    (event \"10:30\" \"Share distribution complete\")\n    (event \"10:45\" \"Reconstruction test PASSED\")\n    (event \"11:00\" \"Ceremony concluded\"))\n\n  (artifacts\n    (public-key \"sha256:abc123...\")\n    (ceremony-record \"sha256:def456...\")\n    (video-hash \"sha256:789xyz...\"))\n\n  (attestations\n    (signed-by \"Alice Smith\" \"sha256:sig1...\")\n    (signed-by \"Bob Jones\" \"sha256:sig2...\")\n    (signed-by \"Carol White\" \"sha256:sig3...\")\n    (signed-by \"David Brown\" \"sha256:sig4...\")\n    (signed-by \"Eve Green\" \"sha256:sig5...\")))"))
    (subsection
      "Soup Integration"
      (code scheme "(soup-object\n  (name \"ceremony/KC-2026-001\")\n  (type key-ceremony)\n  (size \"4.2KB\")\n  (crypto (ed25519 sha256 \"ceremony-hash...\"))\n  (ceremony-type root-certificate)\n  (participants 5)\n  (date \"2026-01-07\")\n  (status completed)\n  (public-key \"sha256:abc123...\"))")))
  (section
    "Security Considerations"
    (subsection
      "Entropy Quality"
      (code scheme ";; Multiple entropy sources required\n(define (verify-entropy-quality entropy-sources)\n  (unless (>= (length entropy-sources) 3)\n    (error \"Insufficient entropy sources\"))\n  (unless (member 'hardware-rng entropy-sources)\n    (warn \"No hardware RNG - ceremony quality reduced\"))\n  (unless (member 'dice entropy-sources)\n    (warn \"No dice rolls - verifiability reduced\")))"))
    (subsection
      "Side Channel Protection"
      (code scheme ";; Constant-time operations during key generation\n(define (secure-key-operations)\n  '((constant-time-comparison \"for all secret comparisons\")\n    (memory-clearing \"zero secrets after use\")\n    (no-branching-on-secrets \"avoid timing leaks\")\n    (power-analysis-resistance \"for HSM operations\")))"))
    (subsection
      "Witness Collusion"
      (code scheme ";; Mitigations for witness collusion\n(define witness-requirements\n  '((minimum-witnesses 2)\n    (independent-verification \"each witness verifies independently\")\n    (no-communication \"witnesses cannot confer during ceremony\")\n    (video-recording \"optional but recommended\")\n    (external-auditor \"for high-value ceremonies\")))"))
    (subsection
      "Ceremony Compromise Recovery"
      (code scheme "(define (ceremony-compromise-response ceremony-id)\n  \"Response if ceremony is compromised\"\n  (let ((cert (get-ceremony-certificate ceremony-id)))\n    ;; Immediate revocation\n    (emergency-revoke cert \"Ceremony compromise suspected\")\n\n    ;; Notify all relying parties\n    (broadcast-revocation cert)\n\n    ;; Schedule new ceremony\n    (schedule-replacement-ceremony ceremony-id)\n\n    ;; Forensic preservation\n    (preserve-ceremony-artifacts ceremony-id)))")))
  (section
    "Implementation"
    (subsection
      "Ceremony Script"
      (code scheme "(define (run-ceremony type)\n  \"Main ceremony execution script\"\n  (let ((ceremony-id (generate-ceremony-id)))\n    (display-banner ceremony-id type)\n\n    ;; Pre-ceremony\n    (run-checklist (pre-ceremony-checklist ceremony-id))\n\n    ;; Main ceremony\n    (case type\n      ((single-key)\n       (single-key-ceremony ceremony-id))\n      ((threshold)\n       (threshold-ceremony (prompt \"N?\") (prompt \"K?\") ceremony-id))\n      ((root-cert)\n       (root-certificate-ceremony ceremony-id (prompt \"Validity years?\")))\n      ((recovery)\n       (recovery-key-ceremony (prompt \"N?\") (prompt \"K?\")\n                              (collect-escrow-agents))))\n\n    ;; Post-ceremony\n    (run-checklist (post-ceremony-checklist ceremony-id))\n\n    (announce \"Ceremony complete.\")\n    ceremony-id))"))
    (subsection
      "Offline Tool"
      (code bash "# Ceremony tool - runs air-gapped\n$ seal-ceremony --type threshold --shares 5 --threshold 3\n\nLibrary of Cyberspace - Key Ceremony Tool\n=========================================\n\nCeremony ID: KC-2026-001\nType: Threshold (5-of-3)\n\nPre-ceremony checklist:\n[x] Network disabled\n[x] Wireless disabled\n[x] Software verified\n[x] Witnesses present (3)\n\nGenerating entropy...\n  Hardware RNG: 32 bytes collected\n  Dice rolls: Witness 1, roll 1: _")))
  (section
    "References"
    (p "1. [DNSSEC Root Key Ceremony](https://www.iana.org/dnssec/ceremonies) 2. [RFC 2693 - SPKI Certificate Theory](https://tools.ietf.org/html/rfc2693) 3. [Memo-008: Threshold Signature Governance](memo-007-threshold-governance.html) 4. [Memo-007: Shamir Secret Sharing](memo-008-shamir-sharing.html) 5. [Memo-021: Capability Delegation](memo-021-capability-delegation.html) 6. [Key Ceremony Best Practices - NIST SP 800-57](https://csrc.nist.gov/publications/detail/sp/800-57-part-1/rev-5/final)"))
  (section
    "Changelog"
    (list
      (item "2026-01-07")
      (item "Initial draft"))))

