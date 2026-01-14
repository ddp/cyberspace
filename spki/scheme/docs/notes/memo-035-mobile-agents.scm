;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 35)
  (title "Mobile Agents and Pub/Sub")
  (section
    "Abstract"
    (p "This Memo specifies the mobile agent architecture for the Library of Cyberspace: Telescript-inspired agents that migrate between realms, carry SPKI credentials, communicate via pub/sub channels, and operate under realm coordinator supervision. Agents are first-class citizens with cryptographic identity."))
  (section
    "Motivation"
    (p "Distributed computation requires mobile code:")
    (list
      (item "Latency")
      (item "Move computation to data, not data to computation")
      (item "Autonomy")
      (item "Agents act on behalf of principals when disconnected")
      (item "Coordination")
      (item "Pub/sub enables loose coupling across realms")
      (item "Accountability")
      (item "Every agent action is auditable"))
    (p "General Magic's Telescript (1994) pioneered these ideas. We preserve the good parts while integrating with SPKI capabilities and content-addressed storage."))
  (section
    "Agent Model"
    (subsection
      "What is an Agent?"
      (p "An agent is:")
      (p "1. Mobile code - Scheme closures that can serialize and migrate 2. Credentialed - Carries SPKI certificates granting capabilities 3. Accountable - Every action recorded in audit trail 4. Supervised - Realm coordinator can inspect, suspend, terminate")
      (code scheme "(define-record-type <agent>\n  (make-agent id principal code state credentials realm)\n  agent?\n  (id agent-id)                    ; Content hash of initial code+state\n  (principal agent-principal)      ; SPKI key that spawned this agent\n  (code agent-code)                ; Scheme closure (serializable)\n  (state agent-state)              ; Mutable state (content-addressed)\n  (credentials agent-credentials)  ; SPKI certificate chain\n  (realm agent-realm))             ; Current realm location"))
    (subsection
      "Agent Lifecycle"
      (code "entangle → running → [teleport] → running → ... → decohere\n             ↓                       ↓\n          suspend               superpose\n             ↓                       ↓\n          resume                  collapse"))
    (subsection
      "Telescript Parallels"
      (table
        (header "Telescript " "Cyberspace " "Description ")
        (row "go " "teleport " "Move agent to another realm ")
        (row "meet " "entangle " "Two agents become correlated ")
        (row "send " "tunnel " "Message passes through barriers ")
        (row "permits " "SPKI certificates " "Capability credentials ")
        (row "places " "Realms " "Execution environments ")
        (row "telename " "Content hash " "Globally unique identity ")))
    (subsection
      "Quantum Vocabulary"
      (p "The fabric of cyberspace uses quantum metaphors:")
      (table
        (header "Operation " "Name " "Metaphor ")
        (row "send message " "tunnel " "Quantum tunneling through barriers ")
        (row "receive message " "observe " "Collapse the wave function ")
        (row "spawn agent " "entangle " "Create correlated pair ")
        (row "migrate agent " "teleport " "Quantum teleportation ")
        (row "terminate " "decohere " "Loss of quantum coherence ")
        (row "checkpoint " "superpose " "Exist in multiple states ")
        (row "link processes " "correlate " "Spooky action at a distance "))
      (p "\"A wilderness of mirrors\" - James Angleton")
      (p "Agents live in a cryptographic wilderness where: - They cannot see plaintext (HE encryption) - They cannot trust other agents (capability-restricted) - Every interaction is mediated by certificates - Identity is what you can prove, not who you claim")))
  (section
    "Agent Operations"
    (subsection
      "entangle (spawn)"
      (p "Create a new agent in the current realm:")
      (code scheme "(entangle\n  code: (lambda (self msg) ...)\n  state: initial-state\n  credentials: cert-chain\n  #!key name timeout)\n\n;; Returns agent-id (content hash)")
      (p "The spawning principal's key signs the agent, establishing provenance. The new agent is entangled with its creator - correlated through shared lineage."))
    (subsection
      "teleport (migrate)"
      (p "Move agent to another realm:")
      (code scheme "(teleport agent-id target-realm\n  #!key superpose)  ; checkpoint before teleport")
      (p "Process: 1. Serialize agent code + state 2. Create migration certificate (signed by current realm) 3. Transmit to target realm 4. Target validates credentials against its policy 5. Resume execution")
      (p "Migration Certificate:")
      (code scheme "(spki-cert\n  (issuer source-realm-key)\n  (subject agent-id)\n  (capability (action execute) (object target-realm))\n  (validity (not-after migration-timeout)))"))
    (subsection
      "decohere (terminate)"
      (p "End agent execution:")
      (code scheme "(decohere agent-id\n  #!key reason superpose-final)")
      (p "Decoherence can be: - Self-initiated - Agent calls (decohere) - Coordinator-initiated - Kill signal from realm coordinator - Timeout - Exceeded allocated time - Revocation - Credentials revoked mid-execution"))
    (subsection
      "superpose / collapse (checkpoint / restore)"
      (p "Save and restore agent state:")
      (code scheme "(superpose agent-id)\n;; Returns content hash of serialized state\n;; Agent exists in multiple potential states\n\n(collapse checkpoint-hash realm)\n;; Resurrects agent from superposition\n;; Wave function collapses to specific state")
      (p "Checkpoints are content-addressed, enabling: - Fault recovery - Time travel debugging - Forking (spawn from checkpoint)")))
  (section
    "Quantum Messaging"
    (subsection
      "Topics (Observation Points)"
      (p "Topics are hierarchical, content-addressed channels where agents observe:")
      (code scheme "(define-record-type <topic>\n  (make-topic name realm observers)\n  topic?\n  (name topic-name)           ; Hierarchical name \"realm/category/subject\"\n  (realm topic-realm)         ; Owning realm\n  (observers topic-observers)); Set of observing agent-ids"))
    (subsection
      "observe (subscribe)"
      (code scheme "(observe topic-pattern handler\n  #!key filter replay-from)\n\n;; topic-pattern: \"realm/events/*\" (glob supported)\n;; handler: (lambda (topic message) ...)\n;; filter: Predicate for message selection\n;; replay-from: Sequence number for replay")
      (p "When you observe, you collapse potential messages into actual received values."))
    (subsection
      "tunnel (publish/send)"
      (code scheme "(tunnel topic message\n  #!key ttl priority)\n\n;; message: Any serializable Scheme value\n;; ttl: Time-to-live in seconds\n;; priority: 'normal | 'high | 'critical")
      (p "Messages tunnel through the fabric of cyberspace, passing barriers that would block classical communication."))
    (subsection
      "Message Structure"
      (code scheme "(quantum-message\n  (id \"sha256:msg-hash...\")\n  (topic \"realm/agents/status\")\n  (source agent-id)\n  (timestamp 1767700000)\n  (sequence 42)\n  (payload (status running) (progress 0.73))\n  (signature #${ed25519-sig}))")
      (p "All messages are signed by the source agent."))
    (subsection
      "Delivery Guarantees"
      (table
        (header "Mode " "Guarantee ")
        (row "at-most-once " "Fire and forget (default) ")
        (row "at-least-once " "Retry until ack ")
        (row "exactly-once " "Deduplication + ack "))))
  (section
    "Realm Coordination"
    (subsection
      "What is a Realm?"
      (p "A realm is an execution domain with:")
      (list
        (item "Coordinator")
        (item "Supervises agents, enforces policy (quiescent until message)")
        (item "Policy")
        (item "What agents can do (SPKI-based)")
        (item "Resources")
        (item "CPU, memory, network quotas")
        (item "Pub/sub broker")
        (item "Message routing"))
      (code scheme "(define-record-type <realm>\n  (make-realm id coordinator policy agents topics)\n  realm?\n  (id realm-id)\n  (coordinator realm-coordinator)  ; Coordinator agent-id\n  (policy realm-policy)            ; SPKI authorization policy\n  (agents realm-agents)            ; Hash table of active agents\n  (topics realm-topics))           ; Hash table of topics"))
    (subsection
      "Quiescent Coordinator"
      (p "Coordinators are event-driven, not polling. Zero CPU when idle:")
      (code scheme "(define (coordinator-loop realm)\n  (let loop ()\n    ;; Block until message arrives (no busy-wait)\n    (let ((msg (observe! (realm-inbox realm))))\n      (case (message-type msg)\n        ((heartbeat) (handle-heartbeat realm msg))\n        ((entangle)  (handle-spawn realm msg))\n        ((teleport)  (handle-migrate realm msg))\n        ((decohere)  (handle-terminate realm msg))\n        ((lock-req)  (handle-lock-request realm msg))\n        ((signal)    (handle-signal realm msg)))\n      (loop))))"))
    (subsection
      "Agent Heartbeat"
      (p "Agents must heartbeat to their coordinator:")
      (code scheme "(agent-heartbeat\n  (agent-id \"sha256:...\")\n  (realm \"sha256:realm...\")\n  (timestamp 1767700000)\n  (status running)\n  (resources\n    (cpu-ms 1234)\n    (memory-kb 5678)\n    (messages-sent 42)))")
      (p "Missing heartbeats trigger investigation:")
      (code "0s    - heartbeat expected\n30s   - grace period\n60s   - coordinator pings agent\n90s   - agent marked unhealthy\n120s  - agent decohered (or superposed)"))
    (subsection
      "Remote Termination (Kill Signal)"
      (p "Coordinators can terminate agents remotely:")
      (code scheme "(coordinator-kill agent-id\n  #!key reason grace-period)")
      (p "Kill Signal:")
      (code scheme "(kill-signal\n  (target agent-id)\n  (issuer coordinator-key)\n  (reason (policy-violation \"exceeded-cpu-quota\"))\n  (grace-period 5)  ; seconds to superpose\n  (signature #${ed25519-sig}))")
      (p "Agents MUST honor kill signals. Failure to terminate results in: 1. Resource revocation (network, storage access removed) 2. Forced decoherence by runtime 3. Blacklisting of spawning principal")))
  (section
    "Distributed Locking (SCS-Style)"
    (subsection
      "Lock Manager"
      (p "Each realm has a lock manager for coordination:")
      (code scheme "(define-record-type <lock-manager>\n  (make-lock-manager realm locks waiters)\n  lock-manager?\n  (realm lm-realm)\n  (locks lm-locks)      ; Hash table: resource → holder\n  (waiters lm-waiters)) ; Hash table: resource → queue"))
    (subsection
      "Lock Operations"
      (code scheme "(lock-acquire resource\n  #!key timeout mode)\n;; mode: 'exclusive | 'shared\n\n(lock-release resource)\n\n(lock-upgrade resource)  ; shared → exclusive\n\n(lock-downgrade resource)  ; exclusive → shared"))
    (subsection
      "Distributed Locks (Cross-Realm)"
      (p "For resources spanning realms:")
      (code scheme "(distributed-lock resource realms\n  #!key timeout coordinator)")
      (p "Uses two-phase locking: 1. Prepare - All realms vote to grant lock 2. Commit - Lock granted if all vote yes 3. Abort - Any no vote aborts"))
    (subsection
      "Deadlock Detection"
      (p "Lock manager maintains wait-for graph:")
      (code scheme "(define (detect-deadlock lock-manager)\n  \"Find cycles in wait-for graph\"\n  (let ((graph (build-wait-for-graph lock-manager)))\n    (find-cycles graph)))")
      (p "Resolution: Youngest agent in cycle is aborted.")))
  (section
    "Security Considerations"
    (subsection
      "TCSEC B2 Channel Security"
      (p "Agent channels must resist covert channel analysis:")
      (table
        (header "Channel Type " "Leak Vector " "Mitigation ")
        (row "Storage " "Message size, topic names " "Pad to fixed sizes ")
        (row "Timing " "Response latency " "Add jitter, batch windows ")
        (row "Signaling " "Pub/sub presence " "Dummy traffic ")))
    (subsection
      "Credential Validation"
      (p "On every operation: 1. Verify agent's SPKI certificate chain 2. Check capability grants requested action 3. Validate certificates not revoked 4. Enforce monotonic attenuation"))
    (subsection
      "Migration Security"
      (code scheme "(define (validate-migration agent target-realm)\n  (and (valid-credentials? (agent-credentials agent))\n       (realm-admits? target-realm agent)\n       (not-revoked? (agent-credentials agent))\n       (within-quota? target-realm agent)))"))
    (subsection
      "Audit Trail"
      (p "All agent actions recorded:")
      (code scheme "(audit-append\n  actor: (agent-principal agent)\n  action: `(teleport ,agent-id ,target-realm)\n  motivation: \"data locality optimization\")")))
  (section
    "Homomorphic Encryption Integration"
    (subsection
      "When to Use HE"
      (p "Use homomorphic encryption for narrow, well-defined operations:")
      (table
        (header "Use Case " "HE Appropriate? ")
        (row "Vote tallying " "Yes - sum encrypted votes ")
        (row "Aggregate metrics " "Yes - sum/average encrypted values ")
        (row "Private analytics " "Yes - fixed statistical operations ")
        (row "General computation " "No - too slow ")
        (row "Dynamic branching " "No - can't branch on encrypted values ")))
    (subsection
      "Encrypted Agent State"
      (p "Agents can carry encrypted state they cannot read:")
      (code scheme "(entangle\n  code: aggregation-circuit  ; Pre-compiled HE circuit\n  state: (encrypted-state\n           (ciphertext #${...})\n           (scheme 'bfv)\n           (operations '(add multiply)))\n  credentials: cert-chain)")
      (p "The agent computes on encrypted data, returns encrypted result. Only the principal with the decryption key can read the result.")))
  (section
    "References"
    (p "1. Telescript Language Reference - General Magic (preserved) 2. Mobile Agents - Lange & Oshima (preserved) 3. Distributed Lock Manager - VAX/VMS SCS (preserved) 4. Concurrency Oriented Programming in Termite Scheme - Germain (preserved) 5. Memo-003: Cryptographic Audit Trail 6. Memo-004: SPKI Authorization 7. Memo-010: Federation Protocol 8. Memo-021: Capability Delegation 9. Memo-023: Agent Sandboxing"))
  (section
    "Changelog"
    (list
      (item "2026-01-07")
      (item "Initial draft with quantum vocabulary"))))

