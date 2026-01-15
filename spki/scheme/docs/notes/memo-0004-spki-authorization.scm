;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 4)
  (title "Public Key Authorization")
  (section
    "Abstract"
    (p "This Memo specifies the SPKI/SDSI certificate system for Cyberspace, providing authorization without identity. Principals are identified by cryptographic keys, not names. Authorization flows through verifiable delegation chains."))
  (section
    "Motivation"
    (subsection
      "Heritage: SDSI at IETF 29"
      (p "Ron Rivest presented SDSI (A Simple Distributed Security Infrastructure) at IETF 29 in Seattle (March 28 - April 1, 1994). The idea was elegant: self-certifying keys and local names. No global namespace. No certificate authorities. Just cryptographic principals naming what they choose to name.")
      (p "SDSI later merged with SPKI to form SPKI/SDSI, standardized in RFC 2692 and RFC 2693 (1999).")
      (p "Some in the PKI industry understood SPKI was technically superior. But they saw a monopoly to be mined—certificate authorities as toll booths on the internet. SPKI threatened that model. It was too decentralized to profit from.")
      (p "HP quietly adopted SPKI for their E-speak middleware and printer authorization. Printers. The technology worked. The politics didn't favor it.")
      (p "Cyberspace picks up where SPKI left off."))
    (subsection
      "The X.509 Problem"
      (p "X.509 certificates bind names to keys. This requires: - Certificate authorities (trust hierarchies) - Global name registries (DNS) - Identity verification (bureaucracy)")
      (p "SPKI inverts this model:")
      (blockquote "Keys are principals. Authorization is local. Delegation is explicit.")
      (p "Benefits: - No CA required - Trust flows from keys you choose - No global names - Local namespaces, local meanings - No identity - Grant permissions to keys, not people - Auditable - S-expression format is human-readable")))
  (section
    "Specification"
    (subsection
      "Principals"
      (p "A principal is an authorization endpoint. Two types:")
      (p "#### Key Principal")
      (p "Direct identification by public key:")
      (code scheme "(define-record-type <key-principal>\n  (make-key-principal public-key)\n  key-principal?\n  (public-key principal-public-key))")
      (p "S-expression: bare bytes")
      (code scheme "#${32-byte-ed25519-public-key}")
      (p "#### Key Hash Principal")
      (p "Identification by hash of public key:")
      (code scheme "(define-record-type <keyhash-principal>\n  (make-keyhash-principal hash-alg hash)\n  keyhash-principal?\n  (hash-alg principal-hash-alg)\n  (hash principal-hash))")
      (p "S-expression:")
      (code scheme "(hash sha512 #${64-byte-hash})"))
    (subsection
      "Authorization Tags"
      (p "Tags define what permissions are granted:")
      (code scheme "(define-record-type <tag>\n  (make-tag sexp)\n  tag?\n  (sexp tag-sexp))")
      (p "Example tags:")
      (code scheme ";; Read access to library\n(read (path /library/lamport-papers))\n\n;; Agent spawning limit\n(spawn-agent (max-count 5))\n\n;; HTTP API access\n(http-api (method POST) (path /deploy/))\n\n;; All permissions (wildcard)\n()"))
    (subsection
      "Validity Period"
      (p "Optional time constraints:")
      (code scheme "(define-record-type <validity>\n  (make-validity not-before not-after)\n  validity?\n  (not-before validity-not-before)   ; ISO 8601 string\n  (not-after validity-not-after))    ; ISO 8601 string"))
    (subsection
      "Certificate Structure"
      (code scheme "(define-record-type <cert>\n  (make-cert issuer subject tag validity propagate)\n  cert?\n  (issuer cert-issuer)         ; Principal granting permission\n  (subject cert-subject)       ; Principal receiving permission\n  (tag cert-tag)               ; What is being granted\n  (validity cert-validity)     ; When valid (optional)\n  (propagate cert-propagate))  ; Can subject re-delegate?")
      (p "S-expression format:")
      (code scheme "(cert\n  (issuer #${alice-public-key})\n  (subject #${bob-public-key})\n  (tag (read (path /library/*)))\n  (valid\n    (not-before \"2026-01-01\")\n    (not-after \"2026-12-31\"))\n  (propagate))"))
    (subsection
      "Signed Certificate"
      (code scheme "(define-record-type <signed-cert>\n  (make-signed-cert cert signature)\n  signed-cert?\n  (cert signed-cert-cert)\n  (signature signed-cert-signature))\n\n(define-record-type <signature>\n  (make-signature hash-alg cert-hash sig-bytes)\n  signature?\n  (hash-alg signature-hash-alg)\n  (cert-hash signature-cert-hash)\n  (sig-bytes signature-sig-bytes))")))
  (section
    "Operations"
    (subsection
      "Creating Certificates"
      (code scheme "(define cert\n  (create-cert\n    (make-key-principal alice-public)\n    (make-key-principal bob-public)\n    (make-tag '(read (path /library/*)))\n    validity: (make-validity \"2026-01-01\" \"2026-12-31\")\n    propagate: #t))"))
    (subsection
      "Signing Certificates"
      (code scheme "(define signed-cert\n  (sign-cert cert alice-private))")
      (p "Process: 1. Convert certificate to canonical S-expression 2. Hash with SHA-512 3. Sign hash with Ed25519 4. Create signature record 5. Combine into signed certificate"))
    (subsection
      "Verifying Certificates"
      (code scheme "(verify-signed-cert signed-cert alice-public)")
      (p "Verification: 1. Recompute canonical S-expression 2. Hash with SHA-512 3. Compare with stored hash 4. Verify Ed25519 signature"))
    (subsection
      "Verifying Delegation Chains"
      (code scheme "(verify-chain root-key cert-list target-tag)")
      (p "Chain verification ensures: 1. Each certificate is validly signed 2. Issuer of cert[n+1] matches subject of cert[n] 3. Tags are properly delegated (each implies the next) 4. Propagation is allowed (except final cert) 5. Final tag implies target tag")))
  (section
    "CLI Tools"
    (subsection
      "spki-keygen"
      (p "Generate Ed25519 keypair:")
      (code bash "$ ./spki-keygen alice\nGenerated keypair:\n  Public:  alice.public\n  Private: alice.private"))
    (subsection
      "spki-cert"
      (p "Create and sign certificate:")
      (code bash "$ ./spki-cert \\\n    --issuer alice.private \\\n    --subject bob.public \\\n    --tag '(read (path /library/*))' \\\n    --propagate \\\n    --not-after \"2026-12-31\" \\\n    --output alice-to-bob.cert"))
    (subsection
      "spki-verify"
      (p "Verify certificate signature:")
      (code bash "$ ./spki-verify alice.public alice-to-bob.cert\n✓ Certificate signature valid"))
    (subsection
      "spki-show"
      (p "Display certificate in human-readable form:")
      (code bash "$ ./spki-show alice-to-bob.cert\nCertificate:\n  Issuer:  ed25519:cbc9b260da65f6a7...\n  Subject: ed25519:a5f8c9e3d2b1f0e4...\n  Tag:     (read (path /library/*))\n  Valid:   until 2026-12-31\n  Propagate: yes")))
  (section
    "Tag Semantics"
    (subsection
      "Tag Implication"
      (p "Tag A implies Tag B if A grants at least all permissions of B.")
      (code scheme "(define (tag-implies tag1 tag2)\n  (cond\n    ((all-perms? tag1) #t)    ; () implies everything\n    ((all-perms? tag2) #f)    ; Only () implies (*)\n    (else (equal? tag1 tag2)))) ; Simple equality (extensible)"))
    (subsection
      "Standard Tag Vocabulary"
      (table
        (header "Tag " "Meaning ")
        (row "(*) " "All permissions ")
        (row "(read (path P)) " "Read access to path P ")
        (row "(write (path P)) " "Write access to path P ")
        (row "(spawn-agent (max-count N)) " "Spawn up to N agents ")
        (row "(http-api (method M) (path P)) " "HTTP API access ")
        (row "(seal-release) " "Permission to create releases ")
        (row "(seal-publish (remote R)) " "Permission to publish to R "))))
  (section
    "Delegation Chains"
    (subsection
      "Example: Three-Level Delegation"
      (code "Alice (root) → Bob (admin) → Carol (operator)")
      (p "Certificates:")
      (code scheme ";; Alice grants admin to Bob\n(cert\n  (issuer #${alice-key})\n  (subject #${bob-key})\n  (tag (*))\n  (propagate))\n\n;; Bob grants operator to Carol\n(cert\n  (issuer #${bob-key})\n  (subject #${carol-key})\n  (tag (seal-publish (remote origin))))")
      (p "Verification:")
      (code scheme "(verify-chain alice-public\n              (list alice-to-bob bob-to-carol)\n              (make-tag '(seal-publish (remote origin))))\n;; => #t if Carol can publish")))
  (section
    "Security Considerations"
    (subsection
      "Threat Model"
      (p "Trusted: - Local key storage - Ed25519/SHA-512 (libsodium) - Certificate chain construction")
      (p "Untrusted: - Certificate sources - Network transport - Certificate claims (until verified)"))
    (subsection
      "Attack Mitigations"
      (table
        (header "Attack " "Mitigation ")
        (row "Certificate forgery " "Ed25519 signatures ")
        (row "Unauthorized delegation " "Propagate flag ")
        (row "Expired permissions " "Validity period checks ")
        (row "Over-delegation " "Tag implication checking ")))
    (subsection
      "Key Management"
      (list
        (item "Generation: Use secure random (libsodium)")
        (item "Storage: Private keys in protected files")
        (item "Backup: Shamir secret sharing (see Memo-0007)")
        (item "Rotation: Issue new certs, revoke old"))))
  (section
    "Integration Points"
    (subsection
      "Vault Authorization"
      (code scheme "(vault-init signing-key: alice-private)\n(seal-release \"1.0.0\")  ; Requires seal-release tag"))
    (subsection
      "Audit Trail Attribution"
      (code scheme "(audit-append\n  actor: bob-public\n  action: '(seal-commit \"abc123\")\n  authorization-chain: (list alice-to-bob-cert))"))
    (subsection
      "Replication Access Control"
      (code scheme "(seal-publish \"1.0.0\"\n  remote: \"origin\"\n  authorization: bob-to-carol-cert)")))
  (section
    "SPKI vs X.509"
    (table
      (header "Aspect " "X.509 " "SPKI ")
      (row "Identity " "Names (DN) " "Keys ")
      (row "Trust " "CA hierarchy " "Local choice ")
      (row "Namespaces " "Global (DNS) " "Local ")
      (row "Revocation " "CRL/OCSP " "Validity periods ")
      (row "Format " "ASN.1/DER " "S-expressions ")
      (row "Readability " "Requires tools " "Human-readable ")
      (row "Delegation " "Implicit (CA) " "Explicit (propagate) ")))
  (section
    "References"
    (p "1. Ellison, C., et al. (1999). SPKI Certificate Theory. RFC 2693. 2. Ellison, C., et al. (1999). SPKI Requirements. RFC 2692. 3. Rivest, R., & Lampson, B. (1996). SDSI - A Simple Distributed Security Infrastructure. 4. Lampson, B. (1971). Protection."))
  (section
    "Changelog"
    (list
      (item "2026-01-06")
      (item "Initial specification"))))

