;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 37)
  (title "Node Roles and Capabilities")
  (section
    "Abstract"
    (p "This RFC defines functional roles for nodes in a Library of Cyberspace confederation based on compute, storage, network, and security capabilities. Roles determine what operations a node can perform and how it participates in the distributed system."))
  (section
    "Terminology"
    (p "Realm: A node's place in cyberspace. A realm encompasses: - The node's vault (local content-addressed object store) - The node's principal (Ed25519 identity) - The node's capabilities (hardware, network, security) - The node's objects (what it stores and serves)")
    (p "A realm is local-first and sovereign. The node controls what to share, who to trust, what to replicate. When nodes federate, their realms overlap - objects flow between them according to trust relationships.")
    (p "The hardware manifest stored at .vault/node-hardware declares what kind of place this realm occupies in cyberspace."))
  (section
    "Motivation"
    (p "RFC-010 (Federation Protocol) defines trust relationships between peers (publisher, subscriber, peer). However, it does not address functional capabilities - what operations each node can actually perform based on its hardware and network constraints.")
    (p "A Raspberry Pi on a solar-powered satellite uplink has different capabilities than a rack-mounted server in a datacenter. The system should:")
    (p "1. Self-assess - Nodes should know their own capabilities 2. Declare - Nodes should advertise their role to peers 3. Adapt - Operations should degrade gracefully based on available roles 4. Persist - Role assignments should survive restarts"))
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
    (p "Per RFC-016, the system is optimized for satellite links:")
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
      (p "1. Capability proofs: Require benchmark results 2. Peer validation: Other nodes can challenge claims 3. Reputation: Track role fulfillment history 4. Threshold trust: Multiple witnesses needed"))
    (subsection
      "Role Downgrade Attacks"
      (p "An attacker could force nodes to operate at lower roles:")
      (p "1. Signed role declarations: Can't forge 2. Local override: Node controls own role 3. Audit trail: Role changes are logged")))
  (section
    "References"
    (p "1. RFC-010: Federation Protocol 2. RFC-011: Byzantine Consensus 3. RFC-016: Lazy Clustering 4. RFC-017: Security Considerations"))
  (section
    "Changelog"
    (list
      (item "2026-01-07")
      (item "Initial draft"))))

