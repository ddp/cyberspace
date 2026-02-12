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
    (p "Without explicit role management, the system either assumes all nodes are equal or requires manual configuration; neither scales."))
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
      (p "These mitigations layer defense in depth; no single spoofing technique defeats all of them."))
    (subsection
      "Role Downgrade Attacks"
      (p "An attacker could force nodes to operate at lower roles:")
      (list
        (item "Signed role declarations: Can't forge")
        (item "Local override: Node controls own role")
        (item "Audit trail: Role changes are logged"))
      (p "A node's sovereignty over its own role prevents external actors from dictating its participation level.")))
  (section
    "Membership Lifecycle"
    (p "Roles define what a node can do; membership defines who belongs. This section specifies the full lifecycle: enrollment, persistence, voluntary departure, and involuntary removal.")
    (p "Implemented in auto-enroll.sls (1280 lines, 41 tests in test-membership.sps).")
    (subsection
      "Join Policy"
      (p "A realm's join policy determines how new members are admitted. Four policies, from most to least permissive:")
      (table
        (header "Policy " "Description " "When ")
        (row "open " "Any node may join; master auto-approves " "Development, testing, personal realms ")
        (row "sponsored " "Existing member vouches for joiner " "Default for small realms (2-10 nodes) ")
        (row "voted " "N-of-M existing members must approve " "Production realms, high-trust environments ")
        (row "closed " "No new members accepted " "Frozen realms, archival configurations "))
      (p "The policy is a realm-level setting, persisted in .vault/membership-state.sexp and enforced by the join listener's handle-join-connection.")
      (code scheme ";; REPL interface\n(set-join-policy! 'voted 'threshold: '(2 3))\n(realm-join-policy)  ; => voted")
      (p "The join listener gates every request through a policy check. Revoked principals are rejected first, regardless of policy. Under closed, all requests are rejected. Under voted, requests enter the pending queue. Under sponsored, the sponsoring member's approval auto-satisfies the (1 1) threshold. Under open, the original auto-approve behavior applies.")
      (code scheme ";; Join policy enforcement (handle-join-connection)\n(cond\n  ((principal-revoked? node-name)\n   (enrollment-send out '(join-rejected ...)))\n  ((eq? *join-policy* 'closed)\n   (enrollment-send out '(join-rejected ...)))\n  ((eq? *join-policy* 'voted)\n   (propose-join node-name pubkey hardware)\n   (enrollment-send out '(join-pending ...)))\n  ((eq? *join-policy* 'sponsored)\n   (propose-join node-name pubkey hardware)\n   ;; auto-approves: threshold (1 1)\n   (enrollment-send out '(join-accepted ...)))\n  (else ;; open\n   (create-enrollment-cert ...)\n   (enrollment-send out '(join-accepted ...))))"))
    (subsection
      "Sponsored Enrollment"
      (p "Under the sponsored policy, the sponsoring member's identity is recorded in the enrollment certificate:")
      (code scheme "(signed-enrollment-cert\n  (spki-cert\n    (issuer (principal ed25519:...))\n    (subject (name new-node) (principal ed25519:...))\n    (role full)\n    (sponsor fluffy)             ; who vouched\n    (validity (not-before ...) (not-after ...))))\n  (signature ...))")
      (p "The sponsor field creates an accountability chain. If a sponsored node misbehaves, the sponsor's judgment is part of the audit record. Under the sponsored policy, propose-join creates a proposal with threshold (1 1), which auto-approves immediately since the proposer's vote satisfies the requirement."))
    (subsection
      "Voted Enrollment"
      (p "Under the voted policy, a join request enters a pending queue. Existing members vote to approve or reject. The actual proposal structure as implemented:")
      (code scheme ";; Proposal structure (as stored in *pending-proposals*)\n(proposal\n  (id \"7368620C2C79...\")       ; SHA-256 of type:subject:timestamp\n  (type join)                    ; join | disbar\n  (subject starlight)\n  (pubkey #vu8(...))\n  (hardware (introspection ...))\n  (proposed-by fluffy)\n  (proposed-at 1770583600)\n  (votes ((fluffy . approve)\n          (luna . approve)))\n  (threshold (2 3))              ; need 2-of-3\n  (expires 1771188400)           ; proposed-at + 604800 (7 days)\n  (status pending))              ; pending | approved | rejected | expired")
      (p "Proposal IDs are SHA-256 hashes of type:subject:timestamp, providing collision-free identifiers suitable for gossip convergence.")
      (p "When the threshold is met, check-threshold! calls execute-proposal!, which has the master issue the enrollment certificate. When enough rejections make approval impossible, the proposal is marked rejected.")
      (p "Pending proposals expire after a configurable timeout (default: 7 days, *proposal-ttl*). expire-proposals! garbage-collects stale entries on every queue access.")
      (code scheme ";; REPL interface\n(propose-join 'new-node pubkey hardware)\n(vote-proposal \"7368620C2C79...\" 'approve)  ; or 'reject\n(pending-proposals)  ; list all pending\n(review-proposals)   ; interactive display with voting instructions"))
    (subsection
      "Enrollment Persistence"
      (p "After successful enrollment (by any policy), four artifacts are persisted to the vault:")
      (code ".vault/\n  certs/membership.sexp           ; signed enrollment certificate\n  keystore/\n    enrollment.pub                ; Ed25519 public key (plaintext)\n    enrollment.key                ; Ed25519 private key (plaintext)\n  realm-state.sexp                ; master, role, members, timestamp\n  membership-state.sexp           ; join policy, proposals, revocations")
      (p "The membership-state.sexp file persists the join policy, vote threshold, pending proposals, and revocation list:")
      (code scheme "(membership-state\n  (version 1)\n  (join-policy voted)\n  (vote-threshold (2 3))\n  (proposals (...))\n  (revocation-list (...))\n  (timestamp 1770920000))")
      (p "On restart, restore-realm-state calls load-membership-state!, which restores the join policy, proposals, and revocation list. Stale proposals are expired immediately on load.")
      (p "The system checks three enrollment artifacts (cert, keypair, realm-state). If any is missing or invalid, the node falls back to fresh auto-enrollment. This three-point check prevents a node from operating with stale identity material.")
      (p "Hardware capabilities and scaling factors are NOT persisted. They are recomputed from fresh introspection on every startup, ensuring the node's declared capabilities always match reality."))
    (subsection
      "Startup Notification"
      (p "On restore, pending proposals are displayed to the operator:")
      (code "*** 2 pending proposals awaiting your vote ***\n  JOIN alice (by fluffy, 3h ago, 1/2 votes) [32FBFF0F75F5]\n  DISBAR eve  (by fluffy, 1d ago, 1/2 votes) [489142FCCD98]\nUse (review-proposals) to review and vote.")
      (p "This ensures that a node returning from downtime immediately sees what decisions need its attention, rather than silently ignoring pending membership actions.")))
  (section
    "Leaving a Realm"
    (p "A node may voluntarily depart a realm. Departure is clean: the node revokes its own membership, notifies peers, and returns to the Wilderness.")
    (subsection
      "Voluntary Departure"
      (p "Implemented in leave-realm. Each step is wrapped in guard for crash safety:")
      (code scheme "(define (leave-realm)\n  (unless *my-name*\n    (error 'leave-realm \"not enrolled in any realm\"))\n  (let ((name *my-name*)\n        (was-master (eq? *my-role* 'master)))\n    ;; 1. Revoke local membership cert\n    (guard (exn [#t ...]) (revoke-membership!))\n    ;; 2. Stop join listener\n    (guard (exn [#t #f]) (stop-join-listener))\n    ;; 3. Unregister from Bonjour\n    (guard (exn [#t #f]) (bonjour-unregister))\n    ;; 4. Reset in-memory state\n    (set! *realm-master* #f)\n    (set! *realm-members* '())\n    (set! *my-role* #f) ...             ; all state variables\n    `((departed . ,name)\n      (was-master . ,was-master))))")
      (p "Each step is idempotent. A crashed node that restarts after partial departure will detect the missing cert and fall through to fresh enrollment, achieving the same end state."))
    (subsection
      "Member List Update"
      (p "When a node departs, the remaining members must update their member lists. The departure is gossiped as a membership event:")
      (code scheme "(membership-event\n  (type departure)\n  (node starlight)\n  (timestamp 1770583600)\n  (reason voluntary)             ; voluntary | timeout | disbarred\n  (signed-by starlight))")
      (p "On receiving a departure event, each member removes the node from its local member list and recomputes scaling factors. If the departing node was master, the remaining members trigger a new election."))
    (subsection
      "Master Departure"
      (p "If the master departs, the realm needs a new one. The disbar-member! procedure already handles this case: when the disbarred or departed node was master, it triggers elect-master on the remaining members and assigns the winner as the new master.")
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
      (p "Disbarment always requires a vote, even under open join policy. The threshold is computed as majority of current members (minimum 2). propose-disbar creates the proposal; members vote via vote-proposal with the 'disbar vote type.")
      (code scheme ";; REPL interface\n(propose-disbar 'compromised-node \"Certificate compromise\"\n                'evidence: \"audit-hash-abc123\")\n(vote-proposal \"DA95EEFC0289...\" 'disbar)\n\n;; Disbarment proposal (as stored)\n(proposal\n  (id \"DA95EEFC028B...\")\n  (type disbar)\n  (subject compromised-node)\n  (proposed-by fluffy)\n  (proposed-at 1770583600)\n  (reason \"Certificate compromise detected\")\n  (evidence \"audit-hash-abc123\")\n  (votes ((fluffy . disbar)\n          (luna . disbar)))\n  (threshold (2 3))\n  (expires 1771188400)\n  (status pending))")
      (p "When the threshold is met, disbar-member! executes:")
      (list
        (item "The node is added to the revocation list (append-only)")
        (item "The node is removed from the member list")
        (item "Scaling factors are recomputed without the disbarred node")
        (item "If the disbarred node was master, elect-master triggers re-election")
        (item "The revocation list is persisted to .vault/membership-state.sexp")))
    (subsection
      "Certificate Revocation"
      (p "Revoked principals are stored in an in-memory list, persisted to membership-state.sexp, and checked on every join attempt:")
      (code scheme ";; Revocation list entry (as stored)\n;; (principal timestamp reason revoked-by)\n(eve 1770583600 \"Byzantine behavior\" (fluffy luna))\n\n;; Query interface\n(revocation-list)             ; => list of all entries\n(principal-revoked? 'eve)     ; => #t")
      (p "Any node encountering a revoked principal in a join request rejects it immediately, before checking join policy. The revocation list is append-only and persisted across restarts."))
    (subsection
      "Disbarred Node Behavior"
      (p "A disbarred node finds itself unable to participate:")
      (list
        (item "Join requests are rejected (principal-revoked? check in handle-join-connection)")
        (item "Gossip messages from the node are dropped")
        (item "The node can still operate locally but cannot federate"))
      (p "The node effectively returns to the Wilderness but with a tainted identity. It must generate new keys to re-enroll, and even then, the voted policy provides a gate.")))
  (section
    "Pending Proposals Queue"
    (p "The pending proposals queue (*pending-proposals*) tracks join and disbarment votes in progress. Persisted to .vault/membership-state.sexp.")
    (subsection
      "Queue State"
      (code scheme "(define *pending-proposals* '())      ; list of proposal s-expressions\n(define *join-policy* 'open)          ; open | sponsored | voted | closed\n(define *vote-threshold* '(2 3))      ; n-of-m (voted policy)\n(define *revocation-list* '())        ; ((principal timestamp reason by) ...)\n(define *proposal-ttl* 604800)        ; 7 days in seconds"))
    (subsection
      "Queue Operations"
      (code scheme ";; Propose a new member (requires sponsored or voted policy)\n(propose-join 'new-node pubkey hardware)\n\n;; Propose disbarment (always requires vote, regardless of policy)\n(propose-disbar 'bad-node \"reason\" 'evidence: \"hash\")\n\n;; Vote on a pending proposal\n(vote-proposal proposal-id 'approve)  ; or 'reject or 'disbar\n\n;; List pending proposals\n(pending-proposals)\n\n;; Interactive review with voting instructions\n(review-proposals)")
      (p "Votes are idempotent: a member can change their vote by voting again, but each member has exactly one vote per proposal. check-threshold! runs after every vote, triggering execute-proposal! when the approval threshold is met, or marking the proposal rejected when enough reject votes make approval impossible."))
    (subsection
      "Interactive Review"
      (p "review-proposals displays all pending proposals with full context and voting instructions. On startup, restore-realm-state shows a summary of pending proposals:")
      (code scheme ";; Full interactive review\n> (review-proposals)\n\n=== Pending Proposals (2) ===\nJoin policy: voted\n\n  Proposal: 7368620C2C79...\n  Type:     Join\n  Subject:  starlight\n  Proposed: fluffy (3h ago)\n  Threshold: 2 of 3\n  Expires:  6d remaining\n  Status:   pending\n  Votes:\n    fluffy: approve\n  (You have not voted)\n\nTo vote: (vote-proposal \"7368620C2C79...\" 'approve)\n     or: (vote-proposal \"7368620C2C79...\" 'reject)")
      (p "format-proposal displays a single proposal in detail. format-proposal-oneline produces the compact summary used in startup notifications."))
    (subsection
      "Consistency"
      (p "Proposals and votes are gossiped, so all members eventually see the same state. Because votes are idempotent (a member can only vote once per proposal), convergence is guaranteed regardless of message ordering.")
      (p "In the event of a network partition, each partition may independently reach a threshold if enough members are present. When the partition heals, the gossiped results converge. If conflicting decisions were made (one partition approved, another rejected), the earlier timestamp wins.")))
  (section
    "Voting Protocol"
    (p "Membership votes use threshold-based approval. The specific application to membership decisions:")
    (subsection
      "Threshold Configuration"
      (p "The vote threshold is a pair (n m) where n approvals out of m members are required. Configured via set-join-policy!:")
      (code scheme ";; Set voted policy with 2-of-3 threshold\n(set-join-policy! 'voted 'threshold: '(2 3))\n\n;; For disbarment, threshold is computed automatically:\n;; max(2, ceiling(member-count / 2)) of member-count\n;; This ensures disbarment always requires a meaningful quorum.")
      (p "The threshold is a realm-level setting, persisted in membership-state.sexp. Changing the threshold requires calling set-join-policy! again."))
    (subsection
      "Vote Processing"
      (p "check-threshold! runs after every vote and determines the outcome:")
      (list
        (item "Approved: approval count >= n (triggers execute-proposal!)")
        (item "Rejected: rejection count > (m - n) (makes approval impossible)")
        (item "Pending: neither condition met, awaiting more votes"))
      (p "For join proposals, the vote types are 'approve and 'reject. For disbarment proposals, the vote type is 'disbar (functionally equivalent to approve)."))
    (subsection
      "Private Ballot"
      (p "For sensitive decisions (especially disbarment), the homomorphic voting protocol from Memo-038 could apply. Individual votes would be encrypted; only the tally revealed.")
      (p "Private ballot is not yet implemented. The current implementation uses open voting where all members can see each other's votes. This is acceptable for small realms where social transparency is appropriate.")))
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
      (item "2026-02-09: Reflect implementation in memo (actual code, persistence, interactive review)")
      (item "2026-02-09: Membership lifecycle (enrollment, departure, disbarment, voting)")
      (item "2026-01-07: Initial draft (roles and capabilities)"))))

