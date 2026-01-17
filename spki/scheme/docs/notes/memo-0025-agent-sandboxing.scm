;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 25)
  (title "Demonic Agents")
  (section
    "Abstract"
    (p "This Memo specifies demonic agents for the Library of Cyberspace: how autonomous agents—daemons in the BSD tradition—are spawned, constrained, monitored, and terminated. Agents are helpful spirits that operate with capability-based authority in isolated sandboxes, enabling safe delegation of tasks while maintaining security boundaries. The vault daemons watch over all."))
  (section
    "Motivation"
    (subsection
      "The BSD Daemon Tradition"
      (p "In Unix mythology, a daemon is a helpful spirit—a background process that tends to the system without being asked. The term comes from Maxwell's demon, the thought experiment about a creature that sorts molecules. BSD gave this concept a face: Beastie, the cheerful daemon with a pitchfork, watching over the system.")
      (p "The Library embraces this tradition. Our agents are daemons—helpful spirits that carry authority, travel between vaults, and do work while their principals sleep."))
    (subsection
      "The General Magic Vision"
      (p "Telescript, from 1994:")
      (blockquote "\"Programs that travel from machine to machine, carrying your authority, doing things while you sleep.\"")
      (p "That vision failed because:")
      (list
        (item "No security model")
        (item "Agents ran with ambient authority")
        (item "No isolation")
        (item "One agent could corrupt another")
        (item "No accountability")
        (item "No audit of agent actions")
        (item "No revocation")
        (item "Once launched, agents were uncontrollable")))
    (subsection
      "The Demonic Solution"
      (p "The Library realizes this vision with proper daemonology:")
      (list
        (item "Capability-based authority")
        (item "Daemons have only granted permissions")
        (item "Sandbox isolation")
        (item "Process, filesystem, network boundaries")
        (item "Full audit trail")
        (item "The Audit Daemon witnesses every action")
        (item "Remote termination")
        (item "Daemons can be banished at any time"))
      (p "Daemons don't rule—they serve. They don't watch over—they watch with.")))
  (section
    "Daemon Model"
    (subsection
      "What is a Daemon?"
      (p "A daemon is a helpful spirit—an autonomous agent that serves its principal:")
      (code scheme "(agent\n  (id \"agent-2026-001\")\n  (spawned-by user-principal)\n  (purpose \"Monitor RSS feeds and archive new papers\")\n  (capabilities\n    (read (url \"https://arxiv.org/rss/\"))\n    (write (path \"/vault/papers/\"))\n    (network (hosts (\"arxiv.org\" \"doi.org\"))))\n  (constraints\n    (max-runtime ( 24 3600))  ; 24 hours\n    (max-memory ( 512 1024 1024))  ; 512MB\n    (max-storage ( 1 1024 1024 1024)))  ; 1GB\n  (sandbox posix-sandbox)\n  (status running))"))
    (subsection
      "Agent Lifecycle"
      (code "    ┌─────────┐\n    │ DEFINED │ Agent specification created\n    └────┬────┘\n         │ spawn\n         ▼\n    ┌─────────┐\n    │ SPAWNED │ Process created, sandbox initialized\n    └────┬────┘\n         │ activate\n         ▼\n    ┌─────────┐\n    │ RUNNING │ Agent executing with capabilities\n    └────┬────┘\n         │ pause/resume/terminate\n         ▼\n    ┌─────────┐\n    │ PAUSED  │ Execution suspended, state preserved\n    └────┬────┘\n         │ terminate/timeout/error\n         ▼\n    ┌─────────┐\n    │ FINISHED│ Execution complete, cleanup pending\n    └────┬────┘\n         │ cleanup\n         ▼\n    ┌─────────┐\n    │ ARCHIVED│ Audit log preserved, resources released\n    └─────────┘")))
  (section
    "Spawning Agents"
    (subsection
      "Spawn Request"
      (code scheme "(define (spawn-agent spec)\n  \"Spawn new agent from specification\"\n  (let* ((agent-id (generate-agent-id))\n         (spawner (current-principal))\n\n         ;; Validate spawner has required capabilities\n         (_ (verify-spawn-authority spawner (spec-capabilities spec)))\n\n         ;; Create sandbox\n         (sandbox (create-sandbox (spec-sandbox-type spec)\n                                  (spec-constraints spec)))\n\n         ;; Create agent record\n         (agent (make-agent\n                 id: agent-id\n                 spawned-by: spawner\n                 spec: spec\n                 sandbox: sandbox\n                 status: 'spawned)))\n\n    ;; Audit spawn\n    (audit-append\n      action: `(agent-spawn ,agent-id)\n      motivation: (spec-purpose spec))\n\n    ;; Initialize agent process\n    (sandbox-exec sandbox (spec-code spec))\n\n    ;; Return agent handle\n    agent))"))
    (subsection
      "Capability Verification"
      (code scheme "(define (verify-spawn-authority spawner requested-caps)\n  \"Verify spawner can grant requested capabilities\"\n  (for-each\n    (lambda (cap)\n      (unless (authorized? spawner 'delegate cap)\n        (error \"Cannot delegate capability\" cap)))\n    requested-caps))"))
    (subsection
      "Agent Code Loading"
      (code scheme "(define (load-agent-code spec)\n  \"Load and verify agent code\"\n  (let* ((code-hash (spec-code-hash spec))\n         (code (cas-get code-hash)))\n\n    ;; Verify code hash\n    (unless (equal? code-hash (sha256 code))\n      (error \"Code integrity failure\"))\n\n    ;; Verify code signature (if required)\n    (when (spec-require-signed? spec)\n      (unless (verify-code-signature code (spec-signer spec))\n        (error \"Code signature invalid\")))\n\n    code))")))
  (section
    "Sandbox Types"
    (subsection
      "POSIX Sandbox"
      (p "Process isolation using OS primitives:")
      (code scheme "(define (create-posix-sandbox constraints)\n  \"Create POSIX-based sandbox\"\n  (sandbox\n    (type posix)\n\n    ;; Process isolation\n    (process\n      (uid (allocate-sandbox-uid))\n      (gid (allocate-sandbox-gid))\n      (chroot (create-sandbox-root))\n      (rlimits\n        (cpu ,(constraints-max-cpu constraints))\n        (memory ,(constraints-max-memory constraints))\n        (files ,(constraints-max-files constraints))\n        (processes 1)))  ; No forking\n\n    ;; Filesystem isolation\n    (filesystem\n      (root ,(sandbox-root))\n      (mounts\n        ((\"/lib\" read-only)\n         (\"/usr/lib\" read-only)\n         ,(sandbox-work-dir) read-write)))\n\n    ;; Network isolation\n    (network\n      (allowed-hosts ,(constraints-network-hosts constraints))\n      (allowed-ports ,(constraints-network-ports constraints)))))"))
    (subsection
      "Scheme Sandbox"
      (p "Language-level isolation for Scheme agents:")
      (code scheme "(define (create-scheme-sandbox constraints)\n  \"Create Scheme-level sandbox\"\n  (sandbox\n    (type scheme)\n\n    ;; Safe environment - no dangerous primitives\n    (environment\n      (import (scheme base)\n              (scheme write)\n              (library sandbox-io)\n              (library sandbox-net))\n      (exclude system exit eval load\n               file-delete directory-delete\n               process-fork process-exec))\n\n    ;; Resource limits via fuel\n    (fuel\n      (computation ,(constraints-max-steps constraints))\n      (allocation ,(constraints-max-memory constraints)))\n\n    ;; Capability-restricted I/O\n    (io-capabilities ,(constraints-io constraints))))"))
    (subsection
      "Container Sandbox"
      (p "OCI container isolation:")
      (code scheme "(define (create-container-sandbox constraints image)\n  \"Create container-based sandbox\"\n  (sandbox\n    (type container)\n\n    ;; Container configuration\n    (container\n      (image ,image)\n      (readonly-rootfs #t)\n      (no-new-privileges #t)\n      (cap-drop ALL)\n      (cap-add ,(minimal-caps constraints)))\n\n    ;; Resource limits\n    (resources\n      (memory ,(constraints-max-memory constraints))\n      (cpu-shares ,(constraints-cpu-shares constraints))\n      (pids-limit 10))\n\n    ;; Network policy\n    (network\n      (mode bridge)\n      (egress-policy ,(network-policy constraints)))))"))
    (subsection
      "WASM Sandbox"
      (p "WebAssembly isolation:")
      (code scheme "(define (create-wasm-sandbox constraints)\n  \"Create WebAssembly sandbox\"\n  (sandbox\n    (type wasm)\n\n    ;; WASM runtime configuration\n    (runtime\n      (memory-limit ,(constraints-max-memory constraints))\n      (table-limit 10000)\n      (fuel ,(constraints-max-steps constraints)))\n\n    ;; WASI capabilities\n    (wasi\n      (preopens ,(wasi-preopens constraints))\n      (env ,(wasi-env constraints))\n      (args ,(wasi-args constraints)))\n\n    ;; Host function imports (minimal)\n    (imports\n      (log \"library:log\")\n      (cas-get \"library:casget\")\n      (cas-put \"library:casput\"))))")))
  (section
    "Capability Enforcement"
    (subsection
      "Capability Proxy"
      (p "All agent I/O goes through capability-checking proxies:")
      (code scheme "(define (make-capability-proxy agent capabilities)\n  \"Create proxy that enforces capability checks\"\n\n  (lambda (operation . args)\n    (let ((required-cap (operation->capability operation args)))\n\n      ;; Check capability\n      (unless (capability-granted? capabilities required-cap)\n        (audit-violation agent operation required-cap)\n        (error \"Capability denied\" operation))\n\n      ;; Audit allowed operation\n      (audit-agent-action agent operation args)\n\n      ;; Execute operation\n      (apply (operation->handler operation) args))))\n\n(define (operation->capability op args)\n  \"Map operation to required capability\"\n  (case op\n    ((read-file)\n     (read (path ,(car args))))\n    ((write-file)\n     (write (path ,(car args))))\n    ((http-get)\n     (network (url ,(car args))))\n    ((cas-get)\n     (read (hash ,(car args))))\n    (else\n     (error \"Unknown operation\" op))))"))
    (subsection
      "Attenuation on Delegation"
      (code scheme "(define (agent-spawn-child parent-agent child-spec)\n  \"Agent spawning child agent with attenuated capabilities\"\n  (let* ((parent-caps (agent-capabilities parent-agent))\n         (requested-caps (spec-capabilities child-spec))\n\n         ;; Child can only have subset of parent's capabilities\n         (child-caps (capability-intersect parent-caps requested-caps)))\n\n    (unless (equal? child-caps requested-caps)\n      (warn \"Child capabilities attenuated\"))\n\n    (spawn-agent (spec-with-capabilities child-spec child-caps))))")))
  (section
    "Agent Communication"
    (subsection
      "Message Passing"
      (p "Agents communicate via typed, capability-checked messages:")
      (code scheme "(define (agent-send from-agent to-agent message)\n  \"Send message between agents\"\n\n  ;; Verify sender has send capability to receiver\n  (unless (capability-granted? (agent-capabilities from-agent)\n                               (send (agent ,(agent-id to-agent))))\n    (error \"Cannot send to agent\"))\n\n  ;; Verify message type allowed\n  (unless (message-type-allowed? from-agent to-agent (message-type message))\n    (error \"Message type not allowed\"))\n\n  ;; Queue message\n  (mailbox-enqueue (agent-mailbox to-agent)\n                   (signed-message from-agent message))\n\n  ;; Audit\n  (audit-append\n    action: (agent-message ,(agent-id from-agent) ,(agent-id to-agent))\n    motivation: (message-type message)))\n\n(define (agent-receive agent #!key timeout)\n  \"Receive message from mailbox\"\n  (let ((msg (mailbox-dequeue (agent-mailbox agent) timeout: timeout)))\n    (when msg\n      ;; Verify signature\n      (verify-message-signature msg)\n      msg)))"))
    (subsection
      "Shared State"
      (p "Agents can share state through CAS:")
      (code scheme "(define (agent-share agent hash recipients)\n  \"Share CAS object with other agents\"\n\n  ;; Verify agent can read the object\n  (unless (capability-granted? (agent-capabilities agent)\n                               (read (hash ,hash)))\n    (error \"Cannot read object to share\"))\n\n  ;; Grant read capability to recipients\n  (for-each\n    (lambda (recipient)\n      (grant-capability agent recipient (read (hash ,hash))))\n    recipients)\n\n  ;; Audit sharing\n  (audit-append\n    action: `(agent-share ,hash ,recipients)))")))
  (section
    "Monitoring and Control"
    (subsection
      "Agent Status"
      (code scheme "(define (agent-status agent)\n  \"Get current agent status\"\n  `(agent-status\n    (id ,(agent-id agent))\n    (status ,(agent-state agent))\n    (uptime ,(- (current-time) (agent-start-time agent)))\n    (resources\n      (memory ,(sandbox-memory-usage (agent-sandbox agent)))\n      (cpu ,(sandbox-cpu-usage (agent-sandbox agent)))\n      (storage ,(sandbox-storage-usage (agent-sandbox agent))))\n    (actions ,(agent-action-count agent))\n    (messages-sent ,(agent-messages-sent agent))\n    (messages-received ,(agent-messages-received agent))))"))
    (subsection
      "Agent Control"
      (code scheme "(define (agent-pause agent #!key reason)\n  \"Pause agent execution\"\n  (unless (authorized? (current-principal) 'control agent)\n    (error \"Not authorized to control agent\"))\n  (sandbox-pause (agent-sandbox agent))\n  (set-agent-state! agent 'paused)\n  (audit-append action: (agent-pause ,(agent-id agent)) motivation: reason))\n\n(define (agent-resume agent)\n  \"Resume paused agent\"\n  (unless (authorized? (current-principal) 'control agent)\n    (error \"Not authorized to control agent\"))\n  (sandbox-resume (agent-sandbox agent))\n  (set-agent-state! agent 'running)\n  (audit-append action: (agent-resume ,(agent-id agent))))\n\n(define (agent-terminate agent #!key reason)\n  \"Terminate agent immediately\"\n  (unless (authorized? (current-principal) 'control agent)\n    (error \"Not authorized to control agent\"))\n  (sandbox-kill (agent-sandbox agent))\n  (set-agent-state! agent 'terminated)\n  (audit-append\n    action: `(agent-terminate ,(agent-id agent))\n    motivation: reason\n    priority: 'high)\n  (cleanup-agent agent))"))
    (subsection
      "Watchdog Daemon"
      (p "The watchdog daemon tends the flock of agents—a daemon watching daemons:")
      (code scheme "(define (agent-watchdog)\n  \"Monitor all agents, enforce constraints\"\n  (for-each\n    (lambda (agent)\n      (when (eq? (agent-state agent) 'running)\n        ;; Check resource limits\n        (when (> (sandbox-memory-usage (agent-sandbox agent))\n                 (agent-max-memory agent))\n          (agent-terminate agent reason: \"Memory limit exceeded\"))\n\n        ;; Check runtime limit\n        (when (> (agent-uptime agent) (agent-max-runtime agent))\n          (agent-terminate agent reason: \"Runtime limit exceeded\"))\n\n        ;; Check heartbeat\n        (when (> (- (current-time) (agent-last-heartbeat agent))\n                 agent-heartbeat-timeout)\n          (agent-terminate agent reason: \"Heartbeat timeout\"))))\n    (all-agents)))")))
  (section
    "Soup Integration"
    (subsection
      "Agents in the Soup"
      (code scheme "(soup-object\n  (name \"agent/2026-001\")\n  (type agent)\n  (size \"145KB\")\n  (status running)\n  (spawned-by \"ddp@eludom.net\")\n  (purpose \"Archive arxiv papers\")\n  (runtime \"4h 23m\")\n  (resources (memory \"234MB\") (storage \"890MB\"))\n  (capabilities (read \"arxiv.org/*\") (write \"/vault/papers/\")))"))
    (subsection
      "Querying Agents"
      (code scheme ";; All running agents\n(soup-query type: 'agent status: 'running)\n\n;; Agents spawned by user\n(soup-query type: 'agent spawned-by: user-principal)\n\n;; Agents with network access\n(soup-query type: 'agent has-capability: 'network)\n\n;; Resource hogs\n(soup-query type: 'agent min-memory: (* 256 1024 1024))"))
    (subsection
      "Agent Introspection"
      (code scheme ";; Agent can query itself\n(define (agent-self-inspect)\n  `(self\n    (id ,(current-agent-id))\n    (capabilities ,(current-capabilities))\n    (resources-remaining\n      (memory ,(- max-memory (current-memory)))\n      (runtime ,(- max-runtime (current-uptime)))\n      (fuel ,(remaining-fuel)))))")))
  (section
    "Agent Patterns"
    (subsection
      "Pattern 1: Periodic Task Agent"
      (code scheme "(spawn-agent\n  (code '(lambda ()\n           (let loop ()\n             (perform-task)\n             (sleep 3600)  ; hourly\n             (loop))))\n  (capabilities\n    (read \"/vault/feeds/\")\n    (write \"/vault/archive/\")\n    (network (\"rss.example.com\")))\n  (constraints\n    (max-runtime ( 30 24 3600))  ; 30 days\n    (max-memory ( 128 1024 1024))))"))
    (subsection
      "Pattern 2: One-Shot Processing Agent"
      (code scheme "(spawn-agent\n  (code '(lambda ()\n           (let ((input (cas-get input-hash)))\n             (let ((result (process input)))\n               (cas-put result)))))\n  (capabilities\n    (read (hash input-hash))\n    (write \"/vault/results/\"))\n  (constraints\n    (max-runtime 3600)\n    (max-memory (* 1024 1024 1024))))"))
    (subsection
      "Pattern 3: Reactive Agent"
      (code scheme "(spawn-agent\n  (code '(lambda ()\n           (let loop ()\n             (let ((msg (agent-receive timeout: 60000)))\n               (when msg\n                 (handle-message msg))\n               (loop)))))\n  (capabilities\n    (receive (from supervisor-agent))\n    (send (to worker-agents))\n    (read \"/vault/tasks/\")\n    (write \"/vault/results/\"))\n  (constraints\n    (max-runtime #f)  ; runs until terminated\n    (max-memory (* 256 1024 1024))))"))
    (subsection
      "Pattern 4: Mobile Agent"
      (code scheme ";; Agent that migrates between vaults\n(spawn-agent\n  (code '(lambda ()\n           (let ((data (gather-local-data)))\n             (migrate-to remote-vault data)\n             (process-remote data)\n             (migrate-home results))))\n  (capabilities\n    (read \"/vault/local/\")\n    (migrate (vaults (vault-a vault-b vault-c))))\n  (constraints\n    (max-migrations 10)\n    (max-runtime (* 24 3600))))")))
  (section
    "Security Considerations"
    (subsection
      "Escape Prevention"
      (code scheme ";; Sandbox escape mitigations\n(define sandbox-security\n  '((seccomp \"restrict system calls\")\n    (namespaces \"process/network/mount isolation\")\n    (capabilities \"drop all Linux capabilities\")\n    (no-setuid \"prevent privilege escalation\")\n    (read-only-root \"immutable rootfs\")\n    (no-raw-sockets \"prevent network attacks\")))"))
    (subsection
      "Resource Exhaustion"
      (code scheme ";; Prevent denial of service\n(define resource-limits\n  '((memory \"hard limit, OOM killer\")\n    (cpu \"cgroups CPU quota\")\n    (disk \"quota or sparse files\")\n    (network \"bandwidth limiting\")\n    (processes \"prevent fork bombs\")\n    (file-descriptors \"prevent fd exhaustion\")))"))
    (subsection
      "Information Leakage"
      (code scheme ";; Prevent covert channels\n(define isolation-measures\n  '((timing \"fuel-based execution, no precise timers\")\n    (filesystem \"no access outside sandbox\")\n    (network \"egress filtering\")\n    (ipc \"message passing only, no shared memory\")\n    (environment \"sanitized env vars\")))"))
    (subsection
      "Malicious Agents"
      (code scheme "(define (detect-malicious-behavior agent)\n  \"Heuristics for detecting malicious agents\"\n  (or\n    ;; Excessive resource usage\n    (> (agent-resource-velocity agent) threshold)\n    ;; Unusual network patterns\n    (suspicious-network-activity? agent)\n    ;; Repeated capability violations\n    (> (agent-violation-count agent) max-violations)\n    ;; Anomalous message patterns\n    (anomalous-messaging? agent)))")))
  (section
    "Implementation Notes"
    (subsection
      "Dependencies"
      (table
        (header "Component " "Implementation ")
        (row "Process sandbox " "pledge/unveil (OpenBSD), seccomp (Linux) ")
        (row "Container sandbox " "runc, crun ")
        (row "WASM sandbox " "wasmtime, wasmer ")
        (row "Scheme sandbox " "custom safe environment ")))
    (subsection
      "Performance"
      (list
        (item "Sandbox creation: ~100ms (container), ~10ms (process), ~1ms (WASM)")
        (item "Message passing: ~10μs (local), ~1ms (cross-sandbox)")
        (item "Capability check: ~100ns (cached), ~10μs (chain validation)"))))
  (section
    "References"
    (p "1. [Telescript Technology: Mobile Agents](https://www.cs.cmu.edu/~pattis/15-1XX/common/handouts/telescript.html) 2. [Capsicum: Practical Capabilities for UNIX](https://www.cl.cam.ac.uk/research/security/capsicum/) 3. [WebAssembly System Interface (WASI)](https://wasi.dev/) 4. [Memo-021: Capability Delegation](memo-021-capability-delegation.html) 5. [Memo-003: Cryptographic Audit Trail](memo-003-audit-trail.html) 6. [E Programming Language](http://erights.org/) - Object capabilities"))
  (section
    "Changelog"
    (list
      (item "2026-01-07")
      (item "Initial draft"))))

