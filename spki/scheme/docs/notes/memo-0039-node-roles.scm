;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 39)
  (title "Realm Roles and Capabilities")
  (section
    "Abstract"
    (p "This Memo defines functional roles for nodes in a Library of Cyberspace confederation based on compute, storage, network, and security capabilities. Roles determine what operations a node can perform and how it participates in the distributed system."))
  (section
    "Terminology"
    (p "Realm: A node's place in cyberspace. A realm encompasses: - The node's vault (local content-addressed object store) - The node's principal (Ed25519 identity) - The node's capabilities (hardware, network, security) - The node's objects (what it stores and serves)")
    (p "A realm is local-first and sovereign. The node controls what to share, who to trust, what to replicate. When nodes federate, their realms overlap - objects flow between them according to trust relationships.")
    (p "The hardware manifest stored at .vault/node-hardware declares what kind of place this realm occupies in cyberspace."))
  (section
    "Motivation"
    (p "Memo-010 (Federation Protocol) defines trust relationships between peers (publisher, subscriber, peer). However, it does not address functional capabilities - what operations each node can actually perform based on its hardware and network constraints.")
    (p "A Raspberry Pi on a solar-powered satellite uplink has different capabilities than a rack-mounted server in a datacenter. The system should:")
    (list
      (item "Self-assess - Nodes should know their own capabilities")
      (item "Declare - Nodes should advertise their role to peers")
      (item "Adapt - Operations should degrade gracefully based on available roles")
      (item "Persist - Role assignments should survive restarts"))
    (p "Automatic role detection enables heterogeneous hardware to participate appropriately without manual configuration.")
    (p "Without explicit role management, the system either assumes all nodes are equal or requires manual configuration; neither scales.")))
  (section
    "Node Roles"
    (subsection
      "Role Hierarchy"
      (code "                    ┌─────────────┐\n                    │ COORDINATOR │  Byzantine consensus, threshold signing\n                    │   (rare)    │  Always-on, high compute\n                    └──────┬──────┘\n                           │\n              ┌────────────┼────────────┐\n              ▼            ▼            ▼\n       ┌───────────┐ ┌───────────┐ ┌───────────┐\n       │   FULL    │ │  WITNESS  │ │ ARCHIVER  │\n       │   NODE    │ │           │ │           │\n       └─────┬─────┘ └───────────┘ └───────────┘\n             │\n             ▼\n       ┌───────────┐\n       │   EDGE    │  Read-only, mobile, intermittent\n       └───────────┘"))
    (subsection
      "Role Definitions"
      (table
        (header "Role " "Compute " "Storage " "Network " "Operations ")
        (row "coordinator " "High " "Medium " "Always-on " "Byzantine consensus, threshold signing, key ceremony ")
        (row "full " "Medium " "High " "Reliable " "All vault operations, replication origin ")
        (row "witness " "Low " "High " "Intermittent " "Passive storage, hash verification, audit ")
        (row "archiver " "Low " "Maximum " "Batch " "Cold storage, offline preservation ")
        (row "edge " "Minimal " "Minimal " "Sporadic " "Read-only sync, mobile access ")))
    (subsection
      "Capability Requirements"
      (code scheme "(node-role-capabilities\n  (coordinator\n    (compute    (min-cores 4) (min-ram-gb 8))\n    (storage    (min-gb 100) (type ssd))\n    (network    (uptime 0.99) (latency-ms 50))\n    (security   (hsm optional) (secure-enclave optional)))\n\n  (full\n    (compute    (min-cores 2) (min-ram-gb 4))\n    (storage    (min-gb 500) (type any))\n    (network    (uptime 0.95) (latency-ms 200))\n    (security   (signing-key required)))\n\n  (witness\n    (compute    (min-cores 1) (min-ram-gb 1))\n    (storage    (min-gb 100) (type any))\n    (network    (uptime 0.50) (latency-ms 1000))\n    (security   (verify-key required)))\n\n  (archiver\n    (compute    (min-cores 1) (min-ram-gb 512mb))\n    (storage    (min-gb 1000) (type cold))\n    (network    (uptime 0.10) (batch-ok #t))\n    (security   (verify-key required) (offline-ok #t)))\n\n  (edge\n    (compute    (min-cores 1) (min-ram-gb 256mb))\n    (storage    (min-gb 1) (type any))\n    (network    (uptime 0.01) (latency-ms 5000))\n    (security   (read-only #t))))")))
  (section
    "Role Detection"
    (subsection
      "Automatic Probing"
      (code scheme "(define (node-probe-capabilities)\n  \"Probe local system capabilities\"\n  `((compute\n     (cores ,(get-cpu-cores))\n     (ram-gb ,(get-ram-gb))\n     (load-avg ,(get-load-average)))\n    (storage\n     (available-gb ,(get-available-storage))\n     (type ,(detect-storage-type)))\n    (network\n     (latency-ms ,(probe-network-latency))\n     (bandwidth-mbps ,(estimate-bandwidth))\n     (type ,(detect-network-type)))  ; ethernet, wifi, cellular, satellite\n    (security\n     (signing-key ,(has-signing-key?))\n     (verify-key ,(has-verify-key?))\n     (hsm ,(has-hsm?)))))"))
    (subsection
      "Role Assignment"
      (code scheme "(define (node-assign-role capabilities)\n  \"Assign role based on probed capabilities\"\n  (let ((compute (assq 'compute capabilities))\n        (storage (assq 'storage capabilities))\n        (network (assq 'network capabilities)))\n    (cond\n     ;; Coordinator: high everything\n     ((and (>= (get-cores compute) 4)\n           (>= (get-ram compute) 8)\n           (<= (get-latency network) 50))\n      'coordinator)\n\n     ;; Full node: medium compute, high storage\n     ((and (>= (get-cores compute) 2)\n           (>= (get-storage storage) 500))\n      'full)\n\n     ;; Archiver: low compute, massive storage, batch network\n     ((and (>= (get-storage storage) 1000)\n           (eq? (get-network-type network) 'batch))\n      'archiver)\n\n     ;; Witness: low compute, decent storage\n     ((>= (get-storage storage) 100)\n      'witness)\n\n     ;; Edge: everything else\n     (else 'edge))))")))
  (section
    "Role Declaration"
    (subsection
      "Local Configuration"
      (code scheme ";; ~/.cyberspace/node-role\n(node-config\n  (role witness)                    ; Declared role\n  (auto-detect #f)                  ; Don't override with probed\n  (capabilities                     ; Known constraints\n    (network (type satellite)\n             (latency-ms 600)\n             (bandwidth-mbps 100))))"))
    (subsection
      "Role Announcement"
      (code scheme "(define (node-announce-role)\n  \"Announce role to federation peers\"\n  (let ((role (node-current-role))\n        (caps (node-probe-capabilities))\n        (key (vault-config 'signing-key)))\n    (when key\n      (let ((announcement\n             `(node-role-announcement\n               (principal ,(get-vault-principal key))\n               (role ,role)\n               (capabilities ,caps)\n               (timestamp ,(current-seconds)))))\n        ;; Sign and broadcast\n        (federation-broadcast\n         (sign-announcement announcement key))))))")))
  (section
    "Role-Based Operation Constraints"
    (subsection
      "Operation Matrix"
      (table
        (header "Operation " "coordinator " "full " "witness " "archiver " "edge ")
        (row "seal-commit ")
        (row "seal-release ")
        (row "seal-archive ")
        (row "seal-restore ")
        (row "seal-publish ")
        (row "seal-subscribe ")
        (row "seal-synchronize ")
        (row "seal-verify ")
        (row "threshold-sign ")
        (row "byzantine-vote ")
        (row "key-ceremony ")
        (row "audit-append ")
        (row "audit-verify ")))
    (subsection
      "Graceful Degradation"
      (code scheme "(define (node-can-perform? operation)\n  \"Check if current role permits operation\"\n  (let ((role (node-current-role))\n        (required (operation-required-role operation)))\n    (role-permits? role required)))\n\n(define (role-permits? actual required)\n  \"Check role hierarchy\"\n  (let ((hierarchy '(coordinator full witness archiver edge)))\n    (<= (list-index hierarchy actual)\n        (list-index hierarchy required))))")))
  (section
    "Starlink Considerations"
    (p "Per Memo-016, the system is optimized for satellite links:")
    (code scheme "(node-config\n  (role witness)\n  (network\n    (type satellite)\n    (provider starlink)\n    (characteristics\n      (latency-ms 20-40)           ; Low-earth orbit\n      (bandwidth-mbps 100-200)     ; Bursty\n      (jitter high)                ; Variable\n      (uptime 0.95)                ; Weather dependent\n      (data-cap none))))           ; Unlimited for now\n\n;; Satellite-optimized behavior\n(define satellite-mode\n  '((batch-sync #t)                ; Aggregate operations\n    (lazy-pull #t)                 ; Don't fetch eagerly\n    (compress-always #t)           ; Minimize transfer\n    (retry-aggressive #t)          ; Handle drops\n    (heartbeat-interval 300)))     ; 5 min, not seconds")
    (subsection
      "Role Implications for Satellite Nodes"
      (p "- coordinator: Generally NOT suitable for satellite (latency too variable for consensus) - full: Marginal (can work with lazy clustering) - witness: IDEAL (passive, tolerates latency) - archiver: IDEAL (batch operations) - edge: IDEAL (intermittent by design)")))
  (section
    "Implementation"
    (subsection
      "REPL Commands"
      (code scheme ";; Probe and display capabilities\n(node-probe)\n\n;; Show current role\n(node-role)\n\n;; Set role explicitly\n(node-role 'witness)\n\n;; Check if operation permitted\n(node-can? 'threshold-sign)\n\n;; Announce role to peers\n(node-announce)"))
    (subsection
      "Persistence"
      (p "Role configuration stored in the realm:")
      (code "~/.cyberspace/node-role      ; User override (global)\n.vault/node-role             ; Realm-specific role\n.vault/node-hardware         ; Hardware manifest (auto-refreshed)")
      (p "The hardware manifest is automatically updated on REPL startup, declaring the realm's capabilities to federated peers."))
    (subsection
      "Audit Trail"
      (p "Role changes are auditable events:")
      (code scheme "(audit-entry\n  (type node-role-change)\n  (timestamp 1736280000)\n  (from edge)\n  (to witness)\n  (reason \"Storage expanded\")\n  (actor #${principal}))")))
  (section
    "Security Considerations"
    (subsection
      "Role Spoofing"
      (p "A node could claim a higher role than its capabilities warrant. Mitigations:")
      (list
        (item "Capability proofs: Require benchmark results")
        (item "Peer validation: Other nodes can challenge claims")
        (item "Reputation: Track role fulfillment history")
        (item "Threshold trust: Multiple witnesses needed"))
      (p "These mitigations layer defense in depth; no single spoofing technique defeats all of them.")))
    (subsection
      "Role Downgrade Attacks"
      (p "An attacker could force nodes to operate at lower roles:")
      (list
        (item "Signed role declarations: Can't forge")
        (item "Local override: Node controls own role")
        (item "Audit trail: Role changes are logged"))
      (p "A node's sovereignty over its own role prevents external actors from dictating its participation level."))))
  (section
    "Membership Lifecycle"
    (p "Roles define what a node can do; membership defines who belongs. This section specifies the full lifecycle: enrollment, persistence, voluntary departure, and involuntary removal.")
    (subsection
      "Join Policy"
      (p "A realm's join policy determines how new members are admitted. Four policies, from most to least permissive:")
      (table
        (header "Policy " "Description " "When ")
        (row "open " "Any node may join; master auto-approves " "Development, testing, personal realms ")
        (row "sponsored " "Existing member vouches for joiner " "Default for small realms (2-10 nodes) ")
        (row "voted " "N-of-M existing members must approve " "Production realms, high-trust environments ")
        (row "closed " "No new members accepted " "Frozen realms, archival configurations "))
      (p "The policy is a realm-level setting, stored in realm state and enforced by the join listener.")
      (code scheme "(realm-state\n  (version 1)\n  (master fluffy)\n  (join-policy sponsored)    ; open | sponsored | voted | closed\n  (vote-threshold (2 3))     ; 2-of-3 required (voted policy only)\n  ...)")
      (p "Open policy is the current default. The join listener accepts any well-formed join request and issues a certificate. This is correct for the current two-node development scenario but must evolve as realms grow."))
    (subsection
      "Sponsored Enrollment"
      (p "Under the sponsored policy, the sponsoring member's identity is recorded in the enrollment certificate:")
      (code scheme "(signed-enrollment-cert\n  (spki-cert\n    (issuer (principal ed25519:...))\n    (subject (name new-node) (principal ed25519:...))\n    (role full)\n    (sponsor fluffy)             ; who vouched\n    (validity (not-before ...) (not-after ...))))\n  (signature ...))")
      (p "The sponsor field creates an accountability chain. If a sponsored node misbehaves, the sponsor's judgment is part of the audit record."))
    (subsection
      "Voted Enrollment"
      (p "Under the voted policy, a join request enters a pending queue. Existing members vote to approve or reject.")
      (code scheme ";; Pending join request (stored in *pending-proposals*)\n(pending-join\n  (name starlight)\n  (pubkey #${...})\n  (hardware (introspection ...))\n  (proposed-by fluffy)\n  (proposed-at 1770583600)\n  (votes ((fluffy . approve)\n          (luna . approve)))\n  (threshold (2 3))              ; need 2-of-3\n  (status pending))              ; pending | approved | rejected | expired")
      (p "When the threshold is met, the proposing member (or any approver) issues the enrollment certificate. Votes are gossiped so all members converge on the same decision.")
      (p "Pending proposals expire after a configurable timeout (default: 7 days). Expired proposals are garbage-collected and the joiner must re-request."))
    (subsection
      "Enrollment Persistence"
      (p "After successful enrollment (by any policy), three artifacts are persisted to the vault:")
      (code ".vault/\n  certs/membership.sexp           ; signed enrollment certificate\n  keystore/\n    enrollment.pub                ; Ed25519 public key (plaintext)\n    enrollment.key                ; Ed25519 private key (plaintext)\n  realm-state.sexp                ; master, role, members, timestamp")
      (p "On restart, the system checks all three. If any is missing or invalid, the node falls back to fresh auto-enrollment. This three-point check prevents a node from operating with stale identity material.")
      (p "Hardware capabilities and scaling factors are NOT persisted. They are recomputed from fresh introspection on every startup, ensuring the node's declared capabilities always match reality.")))
  (section
    "Leaving a Realm"
    (p "A node may voluntarily depart a realm. Departure is clean: the node revokes its own membership, notifies peers, and returns to the Wilderness.")
    (subsection
      "Voluntary Departure"
      (code scheme "(define (leave-realm)\n  \"Voluntarily depart the realm. Clean exit.\"\n  ;; 1. Notify peers (gossip departure)\n  ;; 2. Revoke local membership cert\n  ;; 3. Delete realm-state.sexp\n  ;; 4. Delete enrollment keypair\n  ;; 5. Stop join listener\n  ;; 6. Unregister from Bonjour\n  ;; 7. Reset in-memory state\n  ;; Node returns to Wilderness\n  ...)")
      (p "Steps 1-6 are idempotent. A crashed node that restarts after partial departure will detect the missing files and fall through to fresh enrollment, achieving the same end state."))
    (subsection
      "Member List Update"
      (p "When a node departs, the remaining members must update their member lists. The departure is gossiped as a membership event:")
      (code scheme "(membership-event\n  (type departure)\n  (node starlight)\n  (timestamp 1770583600)\n  (reason voluntary)             ; voluntary | timeout | disbarred\n  (signed-by starlight))")
      (p "On receiving a departure event, each member removes the node from its local member list and recomputes scaling factors. If the departing node was master, the remaining members trigger a new election."))
    (subsection
      "Master Departure"
      (p "If the master departs, the realm needs a new one. The remaining members hold a capability-based election (same as initial enrollment). The most capable remaining node becomes master.")
      (p "If no members remain, the realm ceases to exist. Its artifacts persist in vaults but no active realm operates.")))
  (section
    "Disbarment"
    (p "Involuntary removal of a malicious or compromised node. Unlike voluntary departure, the node does not cooperate.")
    (subsection
      "Grounds for Disbarment"
      (list
        (item "Certificate compromise: Private key leaked or stolen")
        (item "Byzantine behavior: Node issues conflicting statements")
        (item "Resource abuse: Excessive storage, bandwidth, or compute consumption")
        (item "Protocol violation: Malformed messages, replay attacks"))
      (p "Disbarment is a serious action. The bar is high because false positives destroy trust in the system."))
    (subsection
      "Disbarment Protocol"
      (p "Disbarment requires a vote under the realm's join policy (even if the join policy is 'open', disbarment always requires a vote):")
      (code scheme ";; Disbarment proposal\n(pending-disbar\n  (name compromised-node)\n  (proposed-by fluffy)\n  (proposed-at 1770583600)\n  (reason \"Certificate compromise detected\")\n  (evidence (audit-ref \"hash-of-evidence\"))\n  (votes ((fluffy . disbar)\n          (luna . disbar)))\n  (threshold (2 3))\n  (status pending))")
      (p "When the threshold is met:")
      (list
        (item "The node's membership certificate is revoked (added to a revocation list)")
        (item "The node is removed from all member lists")
        (item "The revocation is gossiped to all members")
        (item "The node's Bonjour registration is ignored by members")
        (item "Scaling factors are recomputed without the disbarred node")))
    (subsection
      "Certificate Revocation"
      (p "Revoked certificates are stored in a revocation list that is gossiped alongside membership events:")
      (code scheme "(revocation-list\n  (version 1)\n  (entries\n    ((principal ed25519:abc123...)\n     (revoked-at 1770583600)\n     (reason \"Byzantine behavior\")\n     (revoked-by (fluffy luna)))))")
      (p "Any node encountering a revoked certificate rejects it, even if the certificate is otherwise valid. The revocation list is append-only and signed by the revoking quorum."))
    (subsection
      "Disbarred Node Behavior"
      (p "A disbarred node finds itself unable to participate:")
      (list
        (item "Join requests are rejected (pubkey is on revocation list)")
        (item "Gossip messages from the node are dropped")
        (item "The node can still operate locally but cannot federate"))
      (p "The node effectively returns to the Wilderness but with a tainted identity. It must generate new keys to re-enroll, and even then, the voted policy provides a gate.")))
  (section
    "Pending Joins Queue"
    (p "The pending proposals queue (*pending-proposals*) tracks join and disbarment votes in progress.")
    (subsection
      "Queue Structure"
      (code scheme "(define *pending-proposals* '())\n\n;; Each proposal:\n(proposal\n  (id \"hash-of-proposal\")\n  (type join)                    ; join | disbar\n  (subject node-name)\n  (proposed-by proposer-name)\n  (proposed-at timestamp)\n  (votes ())                     ; ((name . vote) ...)\n  (threshold (n m))              ; n-of-m required\n  (expires (+ proposed-at 604800))  ; 7 days\n  (status pending))              ; pending | approved | rejected | expired"))
    (subsection
      "Queue Operations"
      (code scheme ";; Propose a new member\n(propose-join 'new-node pubkey hardware)\n\n;; Vote on a pending proposal\n(vote-proposal proposal-id 'approve)  ; or 'reject\n\n;; List pending proposals\n(pending)\n\n;; Proposals are gossiped between members\n;; Votes are gossiped as they arrive\n;; Threshold check happens on every vote receipt"))
    (subsection
      "Consistency"
      (p "Proposals and votes are gossiped, so all members eventually see the same state. Because votes are idempotent (a member can only vote once per proposal), convergence is guaranteed regardless of message ordering.")
      (p "In the event of a network partition, each partition may independently reach a threshold if enough members are present. When the partition heals, the gossiped results converge. If conflicting decisions were made (one partition approved, another rejected), the earlier timestamp wins.")))
  (section
    "Voting Protocol"
    (p "Membership votes use the quorum protocol defined in Memo-038. The specific application to membership decisions:")
    (subsection
      "Simple Majority"
      (p "For small realms (2-5 members), a simple majority suffices. Votes are open (not encrypted) since the social cost of disagreement is low in small groups.")
      (code scheme "(vote-threshold\n  (policy majority)\n  (minimum 2))                   ; at least 2 votes regardless of realm size"))
    (subsection
      "N-of-M Threshold"
      (p "For larger realms, an explicit threshold prevents single members from controlling admission:")
      (code scheme "(vote-threshold\n  (policy threshold)\n  (n 3)\n  (m 5))                         ; 3 of 5 members must approve")
      (p "The threshold is a realm-level setting. Changing the threshold itself requires a vote at the current threshold."))
    (subsection
      "Private Ballot"
      (p "For sensitive decisions (especially disbarment), the homomorphic voting protocol from Memo-038 applies. Individual votes are encrypted; only the tally is revealed.")
      (p "Private ballot is RECOMMENDED for disbarment and OPTIONAL for join votes. The realm's join policy configuration specifies which.")))
  (section
    "References"
    (list
      (item "Memo-010: Federation Protocol")
      (item "Memo-011: Byzantine Consensus")
      (item "Memo-016: Lazy Clustering")
      (item "Memo-017: Security Considerations")
      (item "Memo-038: Quorum Protocol with Homomorphic Voting")
      (item "Memo-050: The Wilderness")))
  (section
    "Changelog"
    (list
      (item "2026-02-09: Membership lifecycle (enrollment, departure, disbarment, voting)")
      (item "2026-01-07: Initial draft (roles and capabilities)"))))

