;; RFC-057: Federation Operational Security

(rfc
  (number 57)
  (title "Federation Operational Security")
  (section
    "Abstract"
    (p "Federation (RFC-010) enables peer-to-peer synchronization between vaults. This RFC specifies operational security considerations for federation: what information flows between peers, how to minimize information leakage, and techniques for protecting node identity and capabilities from covert channel analysis."))
  (section
    "1. The Problem Space"
    (p "When vaults federate, they exchange more than just releases. Every message, timing pattern, and capability advertisement creates an information flow. An adversary observing federation traffic—or a malicious peer—can build a profile of your node.")
    (code "          ┌─────────────────────────────────────────┐
          │           FEDERATION TRAFFIC               │
          ├─────────────────────────────────────────────┤
          │  Explicit:                                  │
          │    • Release announcements                  │
          │    • Sync requests                          │
          │    • Public keys                            │
          │                                             │
          │  Implicit (covert channels):                │
          │    • Timing patterns                        │
          │    • Response latencies                     │
          │    • Capability advertisements (weave)      │
          │    • Connection frequencies                 │
          │    • Online/offline patterns                │
          └─────────────────────────────────────────────┘"))
  (section
    "2. Threat Model"
    (subsection
      "2.1 Adversary Capabilities"
      (list
        (item "Passive observer: Can see federation traffic")
        (item "Active participant: Can be a peer in your federation")
        (item "Traffic analyst: Can correlate timing and volume")
        (item "Long-term observer: Can build profiles over time")))
    (subsection
      "2.2 Information at Risk"
      (list
        (item "Node identity: Hardware fingerprinting via benchmarks")
        (item "Location: Timezone from activity patterns")
        (item "Capabilities: Computational power from weave")
        (item "Behavior: Usage patterns from sync timing")
        (item "Network topology: Who talks to whom"))))
  (section
    "3. Weave as Covert Channel"
    (subsection
      "3.1 The Weave Metric"
      (p "Weave measures cryptographic throughput: SHA-512 operations per millisecond. This correlates directly with:")
      (list
        (item "CPU architecture (ARM vs x86, Apple Silicon vs Intel)")
        (item "Core count and frequency")
        (item "Thermal state and power constraints")
        (item "Competing workload"))
      (p "A raw weave value is a fingerprint."))
    (subsection
      "3.2 Attack Scenario"
      (code "Attacker observes: weave = 1667 (your actual value)

Known profiles:
  Apple M4 (10-core):  1600-1700
  Apple M3 (8-core):   1200-1400
  Raspberry Pi 4:       150-200
  Cloud VM (shared):    400-600

Conclusion: You're running Apple M4 Silicon on macOS.
Cross-reference with other traffic: Likely a specific model."))
    (subsection
      "3.3 Quantized Weave Strata"
      (p "Never share raw weave values in federation. Use quantized strata:")
      (code scheme "(define *weave-strata*
  '((constrained . 500)     ; IoT, embedded, RPi
    (standard    . 1000)    ; Laptops, desktops
    (capable     . 2000)    ; Workstations, servers
    (powerful    . 4000)))  ; HPC, GPU-accelerated

(define (weave-stratum weave)
  \"Which stratum of the lattice does this weave occupy?\"
  (cond
    ((< weave 500)  'constrained)
    ((< weave 1000) 'standard)
    ((< weave 2000) 'capable)
    (else           'powerful)))")
      (p "Federation messages advertise stratum, not value:")
      (code scheme "(federation-message
  (type capability)
  (from #${my-pubkey})
  (payload
    (weave-stratum capable)   ; NOT: (weave 1667)
    (storage-tier large))
  (signature #${sig}))")))
  (section
    "4. Timing Analysis"
    (subsection
      "4.1 Response Timing"
      (p "Response latency reveals:")
      (list
        (item "Storage speed (SSD vs HDD vs network)")
        (item "Vault size (query time scales with objects)")
        (item "Current load"))
      (p "Mitigation: Add random jitter to responses.")
      (code scheme "(define (jittered-response response)
  \"Add 50-500ms random delay to mask timing.\"
  (thread-sleep! (+ 0.05 (* 0.45 (random))))
  response)"))
    (subsection
      "4.2 Sync Timing"
      (p "Regular sync patterns reveal:")
      (list
        (item "Timezone (sync at 'morning' = your morning)")
        (item "Work patterns (gaps during meetings)")
        (item "Geographic region"))
      (p "Mitigation: Randomize sync intervals around configured period.")
      (code scheme "(define (next-sync-time base-interval)
  \"Randomize by +/- 20% to mask patterns.\"
  (let ((jitter (* base-interval 0.2 (- (* 2 (random)) 1))))
    (+ (current-seconds) base-interval jitter)))")))
  (section
    "5. Metadata Minimization"
    (subsection
      "5.1 Principle"
      (p "Share the minimum information needed for federation to work. Everything else is unnecessary exposure."))
    (subsection
      "5.2 Required Information"
      (list
        (item "Public key: Identity (unavoidable)")
        (item "Release hashes: Content verification")
        (item "Timestamps: Ordering (can be coarsened)")))
    (subsection
      "5.3 Unnecessary Information"
      (list
        (item "Hostname: Use pubkey hash instead")
        (item "OS/version: Protocol version suffices")
        (item "Raw benchmarks: Use capability strata")
        (item "Vault statistics: Object counts, sizes")
        (item "Uptime: Session duration")))
    (subsection
      "5.4 Minimal Federation Message"
      (code scheme "(federation-message
  (type announcement)
  (from #${pubkey-hash})        ; Not hostname
  (epoch 1767686400)            ; Coarsened to hour
  (payload
    (release \"2.0.0\")
    (hash \"sha512:...\"))
  (signature #${sig}))          ; No extras")))
  (section
    "6. Network Topology Protection"
    (subsection
      "6.1 Peer Enumeration"
      (p "A malicious peer can probe your federation graph:")
      (code "1. Register as your peer
2. Announce fake releases
3. Observe which peers request them
4. Map your federation network"))
    (subsection
      "6.2 Mitigation"
      (p "Do not automatically propagate announcements. Verify before forwarding.")
      (code scheme "(define (should-propagate? announcement)
  \"Only propagate releases we have verified.\"
  (and (release-in-vault? (announcement-release announcement))
       (signature-verified? announcement)))")))
  (section
    "7. Node Identity Separation"
    (subsection
      "7.1 Multiple Personas"
      (p "Consider separate identities for different federation contexts:")
      (list
        (item "Personal vault: Friends and family")
        (item "Professional vault: Work colleagues")
        (item "Public vault: Open source releases"))
      (p "Cross-correlation between personas weakens privacy."))
    (subsection
      "7.2 Implementation"
      (code scheme "(federation-identity
  (persona personal
    (keypair personal-keys)
    (peers alice bob carol))
  (persona professional
    (keypair work-keys)
    (peers company-vault))
  (persona public
    (keypair oss-keys)
    (peers community-mirror)))")))
  (section
    "8. Traffic Analysis Resistance"
    (subsection
      "8.1 Constant-Rate Traffic"
      (p "Advanced: Maintain constant traffic rate regardless of actual activity.")
      (code scheme "(define (constant-rate-sync interval)
  \"Send traffic at fixed intervals, real or dummy.\"
  (if (have-pending-sync?)
      (do-real-sync)
      (send-dummy-heartbeat)))"))
    (subsection
      "8.2 Transport Considerations"
      (list
        (item "TLS: Minimum for transport encryption")
        (item "Tor: For strong anonymity (adds latency)")
        (item "I2P: Alternative anonymity network")
        (item "VPN: Masks source IP (trust VPN provider)"))))
  (section
    "9. Configuration"
    (code scheme "(federation-opsec-config
  ;; Capability advertisement
  (advertise-weave-stratum #t)  ; Quantized, not raw
  (advertise-storage-tier #t)   ; large/medium/small
  (advertise-raw-metrics #f)    ; NEVER

  ;; Timing
  (response-jitter-ms 50 500)   ; Min/max jitter
  (sync-jitter-percent 20)      ; +/- randomization

  ;; Metadata
  (coarsen-timestamps 3600)     ; Round to hour
  (use-pubkey-hash #t)          ; Not hostname
  (hide-vault-stats #t)         ; No object counts

  ;; Network
  (verify-before-propagate #t)
  (constant-rate-traffic #f)    ; Advanced, optional
  (transport tls))"))
  (section
    "10. Audit Integration"
    (p "OPSEC events should be recorded locally but not shared:")
    (code scheme "(federation-opsec-audit
  (event weave-query)           ; Someone asked our weave
  (peer #${peer-pubkey})
  (response stratum:capable)    ; What we sent
  (actual 1667)                 ; What we have (local only)
  (timestamp 1767686400))")
    (p "This creates an audit trail of information disclosure without leaking it further."))
  (section
    "11. Checklist"
    (p "Federation OPSEC review:")
    (list
      (item "[ ] Weave shared as stratum, not raw value")
      (item "[ ] Response timing has jitter")
      (item "[ ] Sync intervals randomized")
      (item "[ ] Timestamps coarsened appropriately")
      (item "[ ] Hostname not in protocol messages")
      (item "[ ] Vault statistics not exposed")
      (item "[ ] Releases verified before propagation")
      (item "[ ] Transport encrypted (TLS minimum)")
      (item "[ ] Personas separated if needed")))
  (section
    "12. References"
    (p "1. RFC-010 — Federation Protocol")
    (p "2. RFC-024 — Network Protocol")
    (p "3. RFC-046 — Security Architecture")
    (p "4. Dingledine, R., et al. (2004). Tor: The Second-Generation Onion Router")
    (p "5. Danezis, G., Diaz, C. (2008). A Survey of Anonymous Communication Channels"))
  (section
    "Changelog"
    (p "- 2026-01-13 — Purge OOP: class → stratum, storage-class → storage-tier")
    (p "- 2026-01-13 — Initial specification")))
