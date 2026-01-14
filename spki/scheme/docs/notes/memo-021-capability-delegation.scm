;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 21)
  (title "Capability Delegation Patterns")
  (section
    "Abstract"
    (p "This RFC specifies capability delegation patterns for the Library of Cyberspace: how principals grant, attenuate, and revoke capabilities using SPKI certificates, content-addressed objects, and the soup metadata layer. Capabilities flow through delegation chains with monotonically decreasing authority."))
  (section
    "Motivation"
    (p "Authorization in distributed systems is hard:")
    (p "- ACLs don't scale - Central lists become bottlenecks - Identity is fragile - Names change, keys rotate - Ambient authority is dangerous - \"Run as root\" is not a security model - Revocation is an afterthought - Usually bolted on badly")
    (p "SPKI (Simple Public Key Infrastructure) solved this decades ago:")
    (list
      (item "Capabilities, not identities")
      (item "What you can do, not who you are")
      (item "Local names")
      (item "No global namespace required")
      (item "Delegation chains")
      (item "Authority flows from source to delegate")
      (item "Threshold signatures")
      (item "M-of-N for critical operations"))
    (p "The Library integrates SPKI with content-addressed storage, creating capabilities that are themselves content-addressed and introspectable."))
  (section
    "Capability Model"
    (subsection
      "Principals"
      (p "A principal is anything that can hold authority:")
      (code scheme ";; Key principal - most common\n(make-principal\n  (type key)\n  (algorithm ed25519)\n  (public-key #${...32 bytes...}))\n\n;; Hash principal - content-addressed object\n(make-principal\n  (type hash)\n  (algorithm sha256)\n  (digest #${...32 bytes...}))\n\n;; Threshold principal - M-of-N group\n(make-principal\n  (type threshold)\n  (threshold 3)\n  (members (key1 key2 key3 key4 key5)))\n\n;; Name principal - local binding\n(make-principal\n  (type name)\n  (issuer parent-key)\n  (name \"alice\"))"))
    (subsection
      "Capabilities"
      (p "A capability is a transferable right to perform an action:")
      (code scheme "(capability\n  (action read)\n  (object (hash sha256 \"content-hash...\")))\n\n(capability\n  (action write)\n  (object (tree sha256 \"subtree-root...\")))\n\n(capability\n  (action sign)\n  (object (tag \"releases/*\")))\n\n(capability\n  (action delegate)\n  (object (capability ...)))  ; Meta-capability"))
    (subsection
      "Certificates"
      (p "SPKI certificates bind capabilities to principals:")
      (code scheme "(spki-cert\n  (issuer vault-master-key)\n  (subject alice-key)\n  (capability\n    (action read)\n    (object (tree sha256 \"docs-root...\")))\n  (validity\n    (not-before \"2026-01-01\")\n    (not-after \"2027-01-01\"))\n  (delegation #t))  ; Alice can re-delegate")))
  (section
    "Delegation Chains"
    (subsection
      "Chain Structure"
      (p "Authority flows through certificate chains:")
      (code "Master Key\n    │\n    ▼ (cert: full access to vault)\nAdmin Key\n    │\n    ▼ (cert: read/write to docs/, can delegate)\nDeveloper Key\n    │\n    ▼ (cert: read-only to docs/public/, cannot delegate)\nContractor Key"))
    (subsection
      "Chain Validation"
      (code scheme "(define (validate-chain chain target-capability)\n  \"Validate delegation chain grants capability\"\n  (let loop ((certs chain)\n             (current-authority 'unlimited))\n    (if (null? certs)\n        (capability-subset? target-capability current-authority)\n        (let ((cert (car certs)))\n          (and (verify-signature cert)\n               (valid-time? cert)\n               (not-revoked? cert)\n               (capability-subset? (cert-capability cert) current-authority)\n               (if (cert-delegation? cert)\n                   (loop (cdr certs) (cert-capability cert))\n                   (and (null? (cdr certs))\n                        (capability-subset? target-capability\n                                           (cert-capability cert)))))))))"))
    (subsection
      "Monotonic Attenuation"
      (p "Delegated capabilities can only decrease:")
      (code scheme ";; Alice has read/write to entire vault\n(spki-cert\n  (issuer master)\n  (subject alice)\n  (capability (action (read write)) (object vault-root))\n  (delegation #t))\n\n;; Alice delegates read-only to Bob (valid - attenuation)\n(spki-cert\n  (issuer alice)\n  (subject bob)\n  (capability (action read) (object vault-root))\n  (delegation #t))\n\n;; Bob tries to delegate write to Carol (INVALID - amplification)\n(spki-cert\n  (issuer bob)\n  (subject carol)\n  (capability (action write) (object vault-root))  ; REJECTED\n  (delegation #f))\n\n;; Bob delegates read to subtree only (valid - further attenuation)\n(spki-cert\n  (issuer bob)\n  (subject carol)\n  (capability (action read) (object docs-subtree))\n  (delegation #f))")))
  (section
    "Delegation Patterns"
    (subsection
      "Pattern 1: Direct Delegation"
      (p "Simplest form - one hop:")
      (code scheme "(define (delegate-direct issuer-key subject-key capability\n                         #!key validity can-delegate)\n  (sign-cert issuer-key\n    `(spki-cert\n      (issuer ,(key->principal issuer-key))\n      (subject ,(key->principal subject-key))\n      (capability ,capability)\n      (validity ,validity)\n      (delegation ,can-delegate))))"))
    (subsection
      "Pattern 2: Role-Based Delegation"
      (p "Delegate to roles, bind keys to roles:")
      (code scheme ";; Define role\n(spki-cert\n  (issuer vault-admin)\n  (subject (name vault-admin \"reviewer\"))\n  (capability (action read) (object (tag \"pending/*\")))\n  (delegation #f))\n\n;; Bind key to role\n(spki-cert\n  (issuer vault-admin)\n  (subject alice-key)\n  (capability (name vault-admin \"reviewer\"))\n  (validity (not-after \"2026-06-01\")))\n\n;; Alice now has reviewer capability via role binding"))
    (subsection
      "Pattern 3: Threshold Delegation"
      (p "Require multiple parties:")
      (code scheme ";; Critical operation requires 3-of-5\n(spki-cert\n  (issuer root-key)\n  (subject (threshold 3 (key1 key2 key3 key4 key5)))\n  (capability (action delete) (object vault-root))\n  (delegation #f))\n\n;; Exercise requires gathering signatures\n(define (threshold-exercise capability signers)\n  (let ((signatures (map (lambda (key) (sign key capability)) signers)))\n    (if (>= (length signatures) 3)\n        (execute-capability capability signatures)\n        (error \"Insufficient signatures\"))))"))
    (subsection
      "Pattern 4: Time-Bounded Delegation"
      (p "Temporary access:")
      (code scheme ";; Conference access - 3 days only\n(spki-cert\n  (issuer organizer-key)\n  (subject attendee-key)\n  (capability (action read) (object conference-materials))\n  (validity\n    (not-before \"2026-03-15T09:00:00Z\")\n    (not-after \"2026-03-17T18:00:00Z\"))\n  (delegation #f))"))
    (subsection
      "Pattern 5: Conditional Delegation"
      (p "Capability with restrictions:")
      (code scheme ";; Can read, but only from specific IP range\n(spki-cert\n  (issuer admin-key)\n  (subject service-key)\n  (capability (action read) (object api-data))\n  (condition\n    (source-ip \"10.0.0.0/8\"))\n  (delegation #f))\n\n;; Can write, but only objects under 1MB\n(spki-cert\n  (issuer admin-key)\n  (subject uploader-key)\n  (capability (action write) (object uploads))\n  (condition\n    (max-size 1048576))\n  (delegation #f))"))
    (subsection
      "Pattern 6: Proxy Delegation"
      (p "Delegate through intermediary:")
      (code scheme ";; Alice delegates to proxy service\n(spki-cert\n  (issuer alice-key)\n  (subject proxy-key)\n  (capability (action read) (object alice-files))\n  (delegation #t)\n  (condition (proxy-for alice-key)))\n\n;; Proxy can act on Alice's behalf\n;; but chain shows Alice as original authority")))
  (section
    "Content-Addressed Capabilities"
    (subsection
      "Hash as Capability"
      (p "Knowledge of a content hash is itself a capability (RFC-020):")
      (code scheme ";; Possessing this hash grants read access\n(define secret-doc-hash \"sha256:7f83b1657ff1fc...\")\n\n;; The hash is unguessable (256 bits of entropy)\n;; Sharing the hash = sharing the capability\n(define (share-capability recipient hash)\n  (encrypted-send recipient hash))"))
    (subsection
      "Capability Certificates for Hashes"
      (p "Formalize hash-based access:")
      (code scheme "(spki-cert\n  (issuer vault-key)\n  (subject reader-key)\n  (capability\n    (action read)\n    (object (hash sha256 \"specific-doc...\")))\n  (validity (not-after \"2027-01-01\")))"))
    (subsection
      "Tree Capabilities"
      (p "Grant access to Merkle subtree:")
      (code scheme "(spki-cert\n  (issuer vault-key)\n  (subject team-key)\n  (capability\n    (action read)\n    (object (tree sha256 \"project-root...\"))\n    (propagate #t))  ; Includes all referenced objects\n  (delegation #t))"))
    (subsection
      "Sealed Capabilities"
      (p "Encrypt capability for specific recipient:")
      (code scheme "(define (seal-capability cap recipient-pubkey)\n  \"Encrypt capability so only recipient can use it\"\n  (let ((serialized (serialize cap))\n         (encrypted (age-encrypt serialized recipient-pubkey)))\n    (cas-put encrypted)))\n\n(define (unseal-capability sealed-hash identity)\n  \"Decrypt and exercise capability\"\n  (let ((encrypted (cas-get sealed-hash))\n         (decrypted (age-decrypt encrypted identity))\n         (cap (deserialize decrypted)))\n    cap))")))
  (section
    "Revocation"
    (subsection
      "Revocation Lists"
      (code scheme "(spki-crl\n  (issuer vault-admin)\n  (revoked\n    ((cert-hash \"sha256:revoked1...\")\n     (reason key-compromise)\n     (revoked-at 1767700000))\n    ((cert-hash \"sha256:revoked2...\")\n     (reason superseded)\n     (revoked-at 1767700100))))"))
    (subsection
      "Online Revocation Check"
      (code scheme "(define (check-revocation cert)\n  \"Check if certificate is revoked\"\n  (let* ((cert-hash (sha256 (serialize cert)))\n         (issuer (cert-issuer cert))\n         (crl (fetch-crl issuer)))\n    (not (member cert-hash (crl-revoked-hashes crl)))))"))
    (subsection
      "Tombstone Revocation"
      (p "Using CAS tombstones (RFC-020):")
      (code scheme "(define (revoke-capability-tombstone cert-hash reason)\n  \"Revoke by tombstoning the certificate\"\n  (cas-tombstone cert-hash\n    reason: reason\n    actor: (current-principal)))"))
    (subsection
      "Short-Lived Certificates"
      (p "Avoid revocation by using short validity:")
      (code scheme ";; 1-hour certificate, no revocation needed\n(spki-cert\n  (issuer service-key)\n  (subject session-key)\n  (capability (action api-access))\n  (validity\n    (not-before ,(current-time))\n    (not-after ,(+ (current-time) 3600)))\n  (delegation #f))")))
  (section
    "Soup Integration"
    (subsection
      "Certificates in the Soup"
      (p "All certificates are soup objects:")
      (code scheme "(soup-object\n  (name \"cert/alice-read-docs\")\n  (type certificate)\n  (size \"412B\")\n  (crypto (ed25519 sha256 \"cert-hash...\"))\n  (issuer \"vault-admin\")\n  (subject \"alice\")\n  (capability \"read docs/*\")\n  (expires \"2027-01-01\"))"))
    (subsection
      "Querying Capabilities"
      (code scheme ";; Find all certificates for a subject\n(soup-query type: 'certificate subject: alice-key)\n\n;; Find all certificates granting write access\n(soup-query type: 'certificate capability: 'write)\n\n;; Find expiring certificates\n(soup-query type: 'certificate\n            expires-before: (+ (current-time) (* 7 24 3600)))\n\n;; Find certificates from specific issuer\n(soup-query type: 'certificate issuer: vault-admin)"))
    (subsection
      "Capability Introspection"
      (code scheme ";; What can Alice do?\n(define (principal-capabilities principal)\n  (let ((certs (soup-query type: 'certificate subject: principal)))\n    (map cert-capability certs)))\n\n;; Who can read this object?\n(define (object-readers hash)\n  (let ((certs (soup-query type: 'certificate\n                           capability: `(read ,hash))))\n    (map cert-subject certs)))\n\n;; Visualize delegation graph\n(define (delegation-graph root-principal)\n  (let ((certs (soup-query type: 'certificate issuer: root-principal)))\n    (map (lambda (cert)\n           (cons (cert-subject cert)\n                 (delegation-graph (cert-subject cert))))\n         certs)))")))
  (section
    "Authorization Decisions"
    (subsection
      "Simple Check"
      (code scheme "(define (authorized? principal action object)\n  \"Check if principal can perform action on object\"\n  (let ((chains (find-authorization-chains principal action object)))\n    (any valid-chain? chains)))"))
    (subsection
      "Chain Discovery"
      (code scheme "(define (find-authorization-chains principal action object)\n  \"Find all certificate chains granting capability\"\n  (let ((target-cap (capability action object)))\n    (let search ((current principal) (chain '()))\n      (let ((certs (soup-query type: 'certificate subject: current)))\n        (append-map\n          (lambda (cert)\n            (if (capability-grants? (cert-capability cert) target-cap)\n                (list (reverse (cons cert chain)))\n                (if (cert-delegation? cert)\n                    (search (cert-issuer cert) (cons cert chain))\n                    '())))\n          certs)))))"))
    (subsection
      "Cached Authorization"
      (code scheme "(define auth-cache (make-lru-cache 10000))\n\n(define (authorized?/cached principal action object)\n  (let ((key (list principal action object)))\n    (or (lru-get auth-cache key)\n        (let ((result (authorized? principal action object)))\n          (lru-put! auth-cache key result)\n          result))))")))
  (section
    "Delegation Ceremonies"
    (subsection
      "Key Ceremony"
      (p "For critical delegations:")
      (code scheme "(define (key-ceremony capability threshold witnesses)\n  \"Conduct witnessed delegation ceremony\"\n  (let* ((ceremony-id (generate-ceremony-id))\n         (ceremony-record\n          (ceremony\n            (id ,ceremony-id)\n            (capability ,capability)\n            (threshold ,threshold)\n            (witnesses ,witnesses)\n            (started-at ,(current-time)))))\n\n    ;; Record ceremony start\n    (audit-append action: (ceremony-start ,ceremony-id))\n\n    ;; Gather witness signatures\n    (let ((signatures (gather-witness-signatures ceremony-record witnesses)))\n      (if (>= (length signatures) threshold)\n          (let ((cert (finalize-ceremony ceremony-record signatures)))\n            (audit-append action: (ceremony-complete ,ceremony-id))\n            cert)\n          (begin\n            (audit-append action: (ceremony-failed ,ceremony-id))\n            (error \"Insufficient witnesses\"))))))"))
    (subsection
      "Emergency Revocation"
      (code scheme "(define (emergency-revoke cert-hash reason)\n  \"Emergency revocation with audit trail\"\n  (let ((revocation\n         (emergency-revocation\n           (cert ,cert-hash)\n           (reason ,reason)\n           (revoked-by ,(current-principal))\n           (revoked-at ,(current-time)))))\n\n    ;; Immediate tombstone\n    (cas-tombstone cert-hash reason: reason)\n\n    ;; Add to CRL\n    (crl-append cert-hash reason)\n\n    ;; Audit with high priority\n    (audit-append\n      action: (emergency-revoke ,cert-hash)\n      motivation: reason\n      priority: 'critical)\n\n    ;; Notify affected parties\n    (notify-revocation cert-hash)))")))
  (section
    "Security Considerations"
    (subsection
      "Capability Leakage"
      (code scheme ";; Capabilities can leak through:\n;; 1. Logging - don't log capability tokens\n;; 2. URLs - don't put capabilities in query strings\n;; 3. Errors - don't include capabilities in error messages\n\n(define (safe-log message capability)\n  (log (string-append message \" [capability:REDACTED]\")))"))
    (subsection
      "Confused Deputy"
      (code scheme ";; Always verify capability matches intended action\n(define (execute-action action object capability)\n  (unless (capability-grants? capability action object)\n    (error \"Capability does not grant this action\"))\n  (perform-action action object))"))
    (subsection
      "Time-of-Check vs Time-of-Use"
      (code scheme ";; Validate immediately before use, not before\n(define (safe-execute capability action)\n  (let ((validated (validate-capability capability)))\n    ;; No window between check and use\n    (atomically\n      (unless validated\n        (error \"Invalid capability\"))\n      (perform-action action))))"))
    (subsection
      "Delegation Depth Limits"
      (code scheme ";; Prevent infinite delegation chains\n(define max-delegation-depth 10)\n\n(define (validate-chain-depth chain)\n  (when (> (length chain) max-delegation-depth)\n    (error \"Delegation chain too deep\")))")))
  (section
    "Implementation Notes"
    (subsection
      "Certificate Storage"
      (code scheme ";; Certificates stored in CAS\n(define (store-cert cert)\n  (let ((signed (sign-cert cert)))\n    (cas-put (serialize signed))))\n\n;; Indexed by issuer and subject for fast lookup\n(define cert-by-issuer (make-hash-table))\n(define cert-by-subject (make-hash-table))"))
    (subsection
      "Performance"
      (list
        (item "Certificate validation is expensive - cache results")
        (item "Chain discovery can be slow - index by issuer/subject")
        (item "Revocation checks add latency - use short-lived certs when possible"))))
  (section
    "References"
    (p "1. SPKI/SDSI 2.0 - RFC 2693 (preserved) 2. A Logic of Authentication - Burrows, Abadi, Needham (preserved) 3. Capability Myths Demolished - Miller, Yee, Shapiro (preserved) 4. RFC-004: SPKI Authorization 5. RFC-020: Content-Addressed Storage 6. RFC-007: Threshold Signature Governance"))
  (section
    "Changelog"
    (list
      (item "2026-01-07")
      (item "Initial draft"))))

