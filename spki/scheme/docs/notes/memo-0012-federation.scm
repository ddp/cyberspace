;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 12)
  (title "Federation Protocol")
  (section
    "Abstract"
    (p "This Memo specifies the Federation Protocol for the Library of Cyberspace: a peer-to-peer synchronization system enabling loose confederacies of friends to share and preserve cryptographically sealed artifacts without central authority."))
  (section
    "E Pluribus Unum"
    (p "Out of many, one.")
    (code "    ┌─────────┐         ┌─────────┐         ┌─────────┐\n    │  Alice  │◄───────►│   Bob   │◄───────►│  Carol  │\n    │  Vault  │         │  Vault  │         │  Vault  │\n    └────┬────┘         └────┬────┘         └────┬────┘\n         │                   │                   │\n         │    ┌──────────────┴──────────────┐    │\n         │    │                             │    │\n         └────►    No Central Authority    ◄────┘\n              │                             │\n              │   Just keys, seals, trust   │\n              │                             │\n              └─────────────────────────────┘"))
  (section
    "Motivation"
    (p "Centralized systems fail:")
    (list
      (item "Single point of failure: Server goes down, everyone stops")
      (item "Censorship: Authority can deny access")
      (item "Trust concentration: Must trust operator")
      (item "Survival: Company folds, data lost"))
    (p "These failures are not bugs but features of centralized design; the only remedy is architectural, not operational.")
    (p "Federation provides:")
    (list
      (item "Decentralized - No master server")
      (item "Resilient - Survives node failures")
      (item "Autonomous - Each peer controls own data")
      (item "Cryptographic - Trust through math, not authority")
      (item "Eventual consistency - Convergence without coordination"))
    (p "Federation trades coordination complexity for availability and autonomy, accepting that nodes may temporarily disagree in exchange for never being unable to operate."))
  (section
    "Federation Model"
    (subsection
      "Peer Relationships"
      (code "Peer: A vault instance with identity (SPKI principal)\n\nRelationships:\n  - Publisher:  I push releases to you\n  - Subscriber: I pull releases from you\n  - Peer:       Bidirectional sync"))
    (subsection
      "Trust Model"
      (code scheme "(federation-trust\n  (peer alice-pubkey\n    (role publisher)\n    (trust-level verified)     ; Signature verified\n    (sync-policy automatic))\n\n  (peer bob-pubkey\n    (role subscriber)\n    (trust-level known)        ; Key known, not verified\n    (sync-policy manual)))")
      (p "Trust levels: - unknown: Never seen, reject - known: Key registered, manual approval - verified: Signature chain verified via Simple Public Key Infrastructure (SPKI) - trusted: Full automatic sync")))
  (section
    "Protocol Operations"
    (subsection
      "Peer Discovery"
      (code scheme "(federation-discover)\n;; Returns: List of known peers and their status")
      (p "Discovery mechanisms:")
      (list
        (item "Explicit configuration: Known peer list")
        (item "Git remotes: Extract from repository")
        (item "Directory service: Optional, not required")
        (item "mDNS/Bonjour: Local network discovery via cyberspace.tcp")))
    (subsection
      "mDNS Service Discovery"
      (p "Cyberspace nodes announce themselves via mDNS using the cyberspace.tcp service type:")
      (code scheme ";; Announce this node\n(announce-presence 'starlight)\n;; Registers: starlight.cyberspace.tcp.local. port 7654\n\n;; Discover peers\n(discover-peers)\n;; Scans for cyberspace.tcp services on local network")
      (p "Platform support: - macOS: dns-sd -R for registration, dns-sd -B for browsing - Linux: avahi-publish for registration, avahi-browse for browsing"))
    (subsection
      "Peer Registration"
      (code scheme "(federation-register peer-uri\n  #!key public-key trust-level)")
      (p "Registers a new peer with: - URI (git remote, HTTP endpoint, filesystem path) - Public key for verification - Initial trust level"))
    (subsection
      "Release Announcement"
      (code scheme "(federation-announce version\n  #!key peers message)")
      (p "Pushes release notification to peers:")
      (list
        (item "Create signed announcement")
        (item "Send to specified peers (or all)")
        (item "Peers verify signature")
        (item "Peers decide whether to pull")))
    (subsection
      "Release Request"
      (code scheme "(federation-request version peer\n  #!key verify-key)")
      (p "Pulls specific release from peer:")
      (list
        (item "Request release metadata")
        (item "Verify signature")
        (item "Download archive")
        (item "Verify integrity")
        (item "Record in audit trail")))
    (subsection
      "Synchronization"
      (code scheme "(federation-sync peer\n  #!key direction verify-key)")
      (p "Bidirectional sync (from Memo-0002):")
      (list
        (item "Exchange release lists")
        (item "Identify missing releases")
        (item "Push/pull as configured")
        (item "Verify all signatures")
        (item "Update audit trails"))))
  (section
    "Message Format"
    (subsection
      "Announcement Message"
      (code scheme "(federation-message\n  (type announcement)\n  (from #${alice-pubkey})\n  (timestamp 1767685100)\n  (payload\n    (release \"2.0.0\")\n    (hash \"sha512:...\")\n    (archive-size 1048576)\n    (notes \"Major release\"))\n  (signature #${ed25519-sig}))"))
    (subsection
      "Request Message"
      (code scheme "(federation-message\n  (type request)\n  (from #${bob-pubkey})\n  (timestamp 1767685200)\n  (payload\n    (release \"2.0.0\")\n    (format cryptographic))\n  (signature #${ed25519-sig}))"))
    (subsection
      "Response Message"
      (code scheme "(federation-message\n  (type response)\n  (from #${alice-pubkey})\n  (in-reply-to \"sha512:request-hash\")\n  (timestamp 1767685300)\n  (payload\n    (release \"2.0.0\")\n    (archive-uri \"/releases/vault-2.0.0.archive\")\n    (hash \"sha512:...\")\n    (signature \"ed25519:...\"))\n  (signature #${ed25519-sig}))")))
  (section
    "Transport Bindings"
    (subsection
      "Git Transport"
      (code "Origin: git@github.com:alice/vault.git\nMechanism: Tags + release assets\n\nAnnounce: git push origin v2.0.0\nRequest:  git fetch origin --tags\nSync:     git fetch origin && git push origin"))
    (subsection
      "HTTP Transport"
      (code "Endpoint: https://alice.example.com/federation\n\nAnnounce: POST /federation/announce\nRequest:  GET /federation/releases/2.0.0\nSync:     POST /federation/sync"))
    (subsection
      "Filesystem Transport"
      (code "Path: /shared/federation/alice\n\nAnnounce: Copy to /shared/federation/alice/announce/\nRequest:  Read from /shared/federation/alice/releases/\nSync:     rsync --update")))
  (section
    "Conflict Resolution"
    (subsection
      "Version Conflicts"
      (p "Same version, different content:")
      (code scheme "(federation-conflict\n  (version \"2.0.0\")\n  (local-hash \"sha512:abc...\")\n  (remote-hash \"sha512:def...\")\n  (resolution reject))  ; Or: prefer-local, prefer-remote, rename")
      (p "Default: Reject conflicts, require human decision."))
    (subsection
      "Resolution Strategies"
      (list
        (item "Reject: Stop sync, alert human")
        (item "Prefer-local: Keep local version")
        (item "Prefer-remote: Take remote version")
        (item "Rename: Keep both as 2.0.0-local, 2.0.0-remote")
        (item "Merge: If content mergeable (future)"))))
  (section
    "Consistency Model"
    (subsection
      "Eventual Consistency"
      (list
        (item "No global ordering required")
        (item "Each peer has local view")
        (item "Convergence through sync")
        (item "Conflicts resolved locally")))
    (subsection
      "Causal Ordering"
      (p "Within a peer's releases: - Version numbers are monotonic - Audit trail provides causality - Hash chains prevent reordering"))
    (subsection
      "No Coordination"
      (list
        (item "No consensus protocol required")
        (item "No distributed lock")
        (item "No leader election")
        (item "Each peer autonomous"))))
  (section
    "Security Considerations"
    (subsection
      "Threat Model"
      (p "Protected: - Unauthenticated release injection (signature verification) - Content tampering (hash verification) - Impersonation (SPKI principal binding) - Replay attacks (timestamps, sequence numbers)")
      (p "Not protected: - Denial of service (rate limiting helps) - Privacy of release metadata (encrypted transport helps) - Sybil attacks (trust management helps)"))
    (subsection
      "Trust Verification"
      (code scheme "(define (verify-peer-message msg peer-key)\n  (and (verify-signature msg peer-key)\n       (verify-timestamp msg (current-seconds))\n       (verify-not-replayed msg)))"))
    (subsection
      "Rate Limiting"
      (code scheme "(federation-config\n  (rate-limit\n    (announcements-per-hour 10)\n    (requests-per-minute 60)\n    (sync-interval-minimum 300)))")))
  (section
    "Gossip Protocol (Future)"
    (p "For larger networks:")
    (code "Alice announces to Bob and Carol\nBob announces to Dave and Eve\nEve announces to Frank\n\nResult: Epidemic spread without central broadcast")
    (p "Properties: - Logarithmic propagation time - Resilient to node failures - No single bottleneck"))
  (section
    "Bootstrap Procedure"
    (subsection
      "New Peer Joining"
      (list
        (item "Generate keypair")
        (item "Register with known peer")
        (item "Exchange public keys (out-of-band verification)")
        (item "Initial sync to get current releases")
        (item "Begin participating in federation")))
    (subsection
      "Network Partitions"
      (list
        (item "Partitions heal automatically on reconnection")
        (item "Conflicting releases detected and flagged")
        (item "Audit trails show partition history"))))
  (section
    "Configuration"
    (code scheme "(federation-config\n  ;; Identity\n  (identity my-private-key)\n\n  ;; Peers\n  (peers\n    (peer \"alice\" uri: \"git@github.com:alice/vault.git\"\n                  key: alice-pubkey\n                  trust: verified)\n    (peer \"bob\"   uri: \"/shared/bob-vault\"\n                  key: bob-pubkey\n                  trust: known))\n\n  ;; Policies\n  (auto-sync #t)\n  (sync-interval 3600)  ; seconds\n  (verify-before-accept #t)\n\n  ;; Security\n  (require-signature #t)\n  (trust-on-first-use #f))"))
  (section
    "Multi-Peer Management"
    (subsection
      "Peer Registry"
      (p "Each vault maintains a local peer registry mapping identities to connection metadata:")
      (code scheme "(define-record-type peer\n  (make-peer id pubkey uri trust-level last-seen sync-state)\n  peer?\n  (id peer-id)                    ; Human-readable name\n  (pubkey peer-pubkey)            ; SPKI principal (Ed25519 public key)\n  (uri peer-uri)                  ; Connection URI (git, http, file)\n  (trust-level peer-trust-level)  ; unknown|known|verified|trusted\n  (last-seen peer-last-seen)      ; Unix timestamp of last contact\n  (sync-state peer-sync-state))   ; idle|syncing|error")
      (p "The registry persists in `.vault/peers.scm` as a simple alist."))
    (subsection
      "Peer Lifecycle"
      (code "┌─────────┐   register   ┌─────────┐   verify   ┌──────────┐   trust   ┌─────────┐\n│ unknown │────────────►│  known  │──────────►│ verified │─────────►│ trusted │\n└─────────┘             └─────────┘           └──────────┘          └─────────┘\n     ▲                       │                      │                    │\n     │                       │ expire               │ revoke             │ revoke\n     │                       ▼                      ▼                    ▼\n     └───────────────────────┴──────────────────────┴────────────────────┘")
      (code scheme ";; Add peer (starts as 'known')\n(peer-register! \"alice\"\n  uri: \"git@github.com:alice/vault.git\"\n  pubkey: alice-ed25519-pubkey)\n\n;; Verify via SPKI cert chain\n(peer-verify! \"alice\" cert-chain)\n\n;; Promote to trusted (enables auto-sync)\n(peer-trust! \"alice\")\n\n;; Revoke (demotes to unknown, blocks sync)\n(peer-revoke! \"alice\")\n\n;; Remove entirely\n(peer-remove! \"alice\")"))
    (subsection
      "Peer Groups"
      (p "Peers can be organized into groups for bulk operations:")
      (code scheme "(peer-group-create! 'family\n  '(\"alice\" \"bob\" \"carol\"))\n\n(peer-group-create! 'work\n  '(\"dave\" \"eve\"))\n\n;; Sync to entire group\n(federation-sync-group 'family)\n\n;; Announce to multiple groups\n(federation-announce \"v2.0.0\"\n  groups: '(family work))")
      (p "Groups are purely local organizational constructs with no protocol-level significance.")))
  (section
    "Trust Levels and Policies"
    (subsection
      "Trust Hierarchy"
      (code "Level      │ Signature │ Auto-Sync │ Announce │ Description\n───────────┼───────────┼───────────┼──────────┼─────────────────────────\nunknown    │ reject    │ no        │ ignore   │ Never seen, no key on file\nknown      │ verify    │ no        │ queue    │ Key registered, manual ops\nverified   │ verify    │ manual    │ notify   │ SPKI chain verified\ntrusted    │ verify    │ automatic │ accept   │ Full bidirectional sync")
      (p "Trust is not transitive: Alice trusting Bob does not imply Alice trusts Bob's peers."))
    (subsection
      "Trust Policies"
      (code scheme "(federation-policy\n  ;; How to handle first contact\n  (first-contact\n    (action prompt)           ; prompt|reject|tofu\n    (tofu-window 300))        ; TOFU valid for 5 minutes\n\n  ;; Signature requirements\n  (signatures\n    (require-on-announce #t)\n    (require-on-sync #t)\n    (require-on-request #t))\n\n  ;; Automatic trust promotion\n  (auto-promote\n    (known->verified #f)      ; Require explicit verification\n    (verified->trusted #f))   ; Require explicit trust grant\n\n  ;; Trust decay\n  (decay\n    (trusted-idle-days 90)    ; Demote trusted->verified after 90 days idle\n    (verified-idle-days 180)  ; Demote verified->known after 180 days idle\n    (known-idle-days 365)))   ; Remove known after 1 year idle"))
    (subsection
      "SPKI Certificate Verification"
      (p "Trust verification uses SPKI certificate chains (Memo-003):")
      (code scheme "(define (peer-verify! peer-id cert-chain)\n  \"Verify peer via SPKI certificate chain\"\n  (let* ((peer (peer-lookup peer-id))\n         (pubkey (peer-pubkey peer))\n         (valid? (spki-verify-chain cert-chain pubkey (current-seconds))))\n    (when valid?\n      (peer-set-trust-level! peer-id 'verified)\n      (audit-log! 'peer-verified peer-id cert-chain))\n    valid?))")))
  (section
    "Announcement Protocol"
    (subsection
      "Message Flow"
      (code "Announcer                          Receiver\n    │                                  │\n    │  ┌─────────────────────────┐     │\n    ├──│ ANNOUNCE v2.0.0         │────►│\n    │  │ hash: sha512:abc...     │     │\n    │  │ size: 1048576           │     │\n    │  │ sig: ed25519:...        │     │\n    │  └─────────────────────────┘     │\n    │                                  │\n    │  ┌─────────────────────────┐     │\n    │◄─│ ACK                     │─────┤ (if trusted)\n    │  │ status: accepted        │     │\n    │  │ sig: ed25519:...        │     │\n    │  └─────────────────────────┘     │\n    │                                  │\n    │  ┌─────────────────────────┐     │\n    │◄─│ REQUEST v2.0.0          │─────┤ (pull follows)\n    │  └─────────────────────────┘     │")
      (p "Receivers at different trust levels handle announcements differently:")
      (list
        (item "trusted: Auto-ACK, auto-request")
        (item "verified: Notify user, queue for manual approval")
        (item "known: Queue silently, require explicit sync")
        (item "unknown: Ignore (log for audit)")))
    (subsection
      "Announcement Message"
      (code scheme "(define-record-type announcement\n  (make-announcement version hash size notes timestamp signature)\n  announcement?\n  (version announcement-version)      ; Semantic version string\n  (hash announcement-hash)            ; Content hash (sha512)\n  (size announcement-size)            ; Archive size in bytes\n  (notes announcement-notes)          ; Release notes (optional)\n  (timestamp announcement-timestamp)  ; Unix timestamp\n  (signature announcement-signature)) ; Ed25519 signature over above")
      (code scheme "(define (federation-announce version #!key peers groups notes)\n  \"Announce release to peers\"\n  (let* ((release (release-lookup version))\n         (msg (make-announcement\n                version\n                (release-hash release)\n                (release-size release)\n                (or notes \"\")\n                (current-seconds)\n                #f))  ; Signature added below\n         (signed (sign-announcement msg (vault-private-key))))\n    (for-each\n      (lambda (peer)\n        (send-announcement peer signed))\n      (resolve-recipients peers groups))))"))
    (subsection
      "Retries and Timeouts"
      (code scheme "(federation-config\n  (announce\n    (timeout-seconds 30)       ; Per-peer timeout\n    (retry-count 3)            ; Retries on failure\n    (retry-backoff-base 5)     ; 5, 10, 20 seconds\n    (parallel-sends 5)))       ; Concurrent announcements")
      (p "Failed announcements are logged and can be retried manually via `(federation-retry-failed)`.")))
  (section
    "Gossip Propagation"
    (subsection
      "Epidemic Broadcast"
      (p "For networks larger than a handful of peers, direct announcement to all peers doesn't scale. Gossip provides O(log N) propagation:")
      (code "Round 0: Alice announces to 3 random peers (fanout=3)\n         Alice ──► Bob, Carol, Dave\n\nRound 1: Bob, Carol, Dave each forward to 3 random peers\n         Bob ──► Eve, Frank, Grace\n         Carol ──► Henry, Eve, Ivan    (Eve receives duplicate)\n         Dave ──► Grace, Julia, Karl   (Grace receives duplicate)\n\nRound 2: Continue until TTL expires or all peers reached")
      (code scheme "(federation-gossip-config\n  (fanout 3)              ; Forward to N random peers\n  (ttl 5)                 ; Maximum hops\n  (dedup-window 3600))    ; Ignore duplicates within 1 hour"))
    (subsection
      "Gossip Message"
      (code scheme "(define-record-type gossip-envelope\n  (make-gossip-envelope origin hop-count ttl seen payload)\n  gossip-envelope?\n  (origin gossip-origin)        ; Original announcer pubkey\n  (hop-count gossip-hop-count)  ; Current hop count\n  (ttl gossip-ttl)              ; Time-to-live (max hops)\n  (seen gossip-seen)            ; Set of peer pubkeys who've seen this\n  (payload gossip-payload))     ; The announcement")
      (code scheme "(define (gossip-forward! envelope)\n  \"Forward gossip to random subset of peers\"\n  (when (< (gossip-hop-count envelope) (gossip-ttl envelope))\n    (let* ((candidates (filter\n                         (lambda (p)\n                           (and (>= (peer-trust-level p) 'known)\n                                (not (member (peer-pubkey p) (gossip-seen envelope)))))\n                         (peer-list)))\n           (targets (take-random candidates (gossip-fanout))))\n      (for-each\n        (lambda (peer)\n          (send-gossip peer\n            (make-gossip-envelope\n              (gossip-origin envelope)\n              (+ 1 (gossip-hop-count envelope))\n              (gossip-ttl envelope)\n              (cons (my-pubkey) (gossip-seen envelope))\n              (gossip-payload envelope))))\n        targets))))"))
    (subsection
      "Protocol Properties"
      (list
        (item "Distributed: No coordinator, any peer can initiate")
        (item "Resilient: Survives peer failures, duplicates handled")
        (item "Scalable: O(log N) rounds to reach N peers")
        (item "Tunable: Fanout and TTL control spread vs traffic")
        (item "Eventually consistent: All connected peers converge"))))
  (section
    "Conflict Resolution UI"
    (subsection
      "Conflict Types"
      (code "Type            │ Cause                           │ Default Resolution\n────────────────┼─────────────────────────────────┼───────────────────────\nversion-hash    │ Same version, different content │ Prompt user\nfork            │ Divergent version histories     │ Prompt user\nrollback        │ Remote has older than local     │ Reject\ntimestamp       │ Timestamps significantly skewed │ Warn, proceed")
      (p "All conflicts are logged to the audit trail regardless of resolution."))
    (subsection
      "Interactive Resolution"
      (code scheme ";; When conflict detected, present choices:\n(define (resolve-conflict! conflict)\n  (let* ((type (conflict-type conflict))\n         (local (conflict-local conflict))\n         (remote (conflict-remote conflict))\n         (choice (prompt-conflict type local remote)))\n    (case choice\n      ((keep-local)\n       (audit-log! 'conflict-resolved conflict 'keep-local))\n      ((take-remote)\n       (import-release! (conflict-remote-release conflict))\n       (audit-log! 'conflict-resolved conflict 'take-remote))\n      ((keep-both)\n       (rename-release! local (string-append (release-version local) \"-local\"))\n       (import-release! (conflict-remote-release conflict))\n       (audit-log! 'conflict-resolved conflict 'keep-both))\n      ((defer)\n       (queue-conflict! conflict)\n       (audit-log! 'conflict-deferred conflict)))))")
      (code "┌──────────────────────────────────────────────────────────────┐\n│                    CONFLICT DETECTED                         │\n├──────────────────────────────────────────────────────────────┤\n│  Version: 2.0.0                                              │\n│                                                              │\n│  Local:   sha512:abc123... (2026-01-15 14:30)               │\n│  Remote:  sha512:def456... (2026-01-15 14:35) from alice    │\n│                                                              │\n│  [1] Keep local version                                      │\n│  [2] Take remote version                                     │\n│  [3] Keep both (rename local to 2.0.0-local)                │\n│  [4] Defer decision                                          │\n│  [5] Show diff                                               │\n│                                                              │\n│  Choice: _                                                   │\n└──────────────────────────────────────────────────────────────┘"))
    (subsection
      "Automatic Resolution Policies"
      (code scheme "(federation-config\n  (conflict-resolution\n    ;; For trusted peers, can enable auto-resolution\n    (trusted-peer-wins #f)      ; Auto-accept from trusted\n    (newer-timestamp-wins #f)   ; Dangerous: clock skew\n    (larger-version-wins #f)    ; Only for semver conflicts\n\n    ;; Always prompt for these\n    (always-prompt-on\n      '(version-hash fork rollback))))")
      (p "Automatic resolution is discouraged for hash conflicts; cryptographic seals exist precisely to detect tampering, and automatic resolution defeats this purpose.")))
  (section
    "Implementation Status"
    (subsection
      "Implemented (Memo-007)"
      (list
        (item "seal-publish: Push to single remote")
        (item "seal-subscribe: Pull from single remote")
        (item "seal-synchronize: Bidirectional with single peer")
        (item "Transport: git, HTTP, filesystem")))
    (subsection
      "Specified (This Memo)"
      (list
        (item "Multi-peer registry and lifecycle")
        (item "Trust levels: unknown, known, verified, trusted")
        (item "Trust policies and SPKI verification")
        (item "Announcement protocol with ACK/retry")
        (item "Gossip epidemic broadcast")
        (item "Conflict detection and resolution UI")))
    (subsection
      "Future Work"
      (list
        (item "Peer reputation scoring")
        (item "Bandwidth-aware sync scheduling")
        (item "Partial sync (subset of releases)")
        (item "Encrypted peer-to-peer channels"))))
  (section
    "References"
    (list
      (item "Birman, K. (2007). The Promise, and Limitations, of Gossip Protocols.")
      (item "Demers, A., et al. (1987). Epidemic Algorithms for Replicated Database Maintenance.")
      (item "Shapiro, M., et al. (2011). Conflict-Free Replicated Data Types.")
      (item "Memo-007: Replication Layer")
      (item "Memo-003: SPKI Authorization")))
  (section
    "Changelog"
    (list
      (item "2026-01-31: Flesh out multi-peer management, trust policies, announcement protocol, gossip propagation, and conflict resolution UI")
      (item "2026-01-06: Initial specification"))))

