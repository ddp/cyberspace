;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 18)
  (title "Lazy Clustering")
  (section
    "Abstract"
    (p "This Memo specifies Lazy Clustering for Cyberspace federation: a relaxed synchronization model where nodes sync when convenient, not continuously. Optimized for the \"loose confederacy of friends\" model."))
  (section
    "Motivation"
    (p "Not every deployment needs Byzantine consensus:")
    (list
      (item "Friends trust friends: No active adversary")
      (item "Bandwidth costs: Continuous sync is expensive")
      (item "Offline operation: Internet isn't always available")
      (item "Simplicity: Complex protocols have complex bugs"))
    (p "Protocol complexity should match trust assumptions; using Byzantine consensus among friends wastes resources and adds failure modes.")
    (p "Lazy Clustering provides:")
    (list
      (item "Sync when ready: Push/pull at human pace")
      (item "Offline-first: Work without network")
      (item "Conflict detection: Know when divergence happens")
      (item "Manual resolution: Humans resolve, not algorithms")
      (item "Audit everything: Full history preserved"))
    (p "These properties prioritize simplicity and autonomy over consistency, appropriate when participants have aligned interests and can tolerate temporary divergence.")
    (blockquote "The best protocol is the one you don't run."))
  (section
    "Specification"
    (subsection
      "Cluster Model"
      (code "     ┌─────────┐\n     │  Alice  │\n     │ (lazy)  │\n     └────┬────┘\n          │\n          │ sync when ready @ 10Gb/s\n          │\n     ┌────▼────┐         ┌─────────┐\n     │   Bob   │◄───────►│  Carol  │\n     │ (lazy)  │ 10Gb/s  │ (lazy)  │\n     └─────────┘         └─────────┘\n\nNo heartbeats. No leader election. No quorum.\nJust friends sharing when they're ready.\nAt line speed when they do."))
    (subsection
      "Performance Model"
      (p "Lazy semantics, line speed execution.")
      (code "Line speed (10 Gb/s):\n  Typical release: 10 MB archive\n  Transfer time:   8 ms\n  Effective rate:  ~1000 releases/second\n\nStarlink (100-200 Mb/s, 20-40ms latency):\n  Typical release: 10 MB archive\n  Transfer time:   400-800 ms\n  Effective rate:  ~1-2 releases/second\n  Optimized for:   Bursty, high-latency satellite links\n\nMinimum bandwidth:\n  Floor:           128 Kb/s (dual-ISDN)\n  Target:          1 Mb/s (T1)\n  Typical release: 10 MB archive\n  Transfer time:   ~80 sec (T1), ~10 min (dual-ISDN)\n  Strategy:        Delta sync, compressed archives")
      (p "Crypto overhead (constant):")
      (code "Signature verify: ~10 μs (Ed25519)\nHash verify:      ~1 ms (SHA-512, 10MB)\nTotal overhead:   ~1 ms (negligible vs transfer)")
      (p "\"Lazy\" means when, not how fast. When you sync, it saturates the pipe.")
      (p "Design priorities: 1. Optimized for Starlink and satellite links 2. Tolerant of high latency (no chatty protocols) 3. Graceful degradation to minimum bandwidth 4. Bursty transfer patterns (sync then idle)"))
    (subsection
      "Heartbeat and Timekeeping"
      (p "No mandatory heartbeat. That's the design.")
      (code "Traditional cluster:  ping → pong → ping → pong → ...\nLazy cluster:         ... silence ... (sync) ... silence ...")
      (p "Timekeeping: Lamport clocks (Memo-012), not wall clocks. - Causality without synchronization - No NTP dependency - No GPS required - Works across time zones, planets")
      (p "When you need consensus: Byzantine consensus (Memo-011) + Lamport clocks. - Lazy clustering for everyday sync - Byzantine consensus for critical decisions - Same Lamport clock across both modes")
      (p "Optional presence beacon:")
      (code scheme "(cluster-beacon\n  (peer \"alice\")\n  (lamport-time 4271)\n  (last-release \"2.1.0\")\n  (status available)\n  (next-expected \"when ready\"))")
      (p "Beacons are: - Pull-based (query, don't push) - Cached (no flood) - Stale-tolerant (hours/days old is fine) - Unsigned (advisory only)"))
    (subsection
      "Sync Modes"
      (p "#### Push (I have something)")
      (code scheme "(lazy-push peer)\n;; Sends my new releases to peer\n;; Non-blocking, fire-and-forget")
      (p "#### Pull (What do you have?)")
      (code scheme "(lazy-pull peer)\n;; Fetches peer's new releases\n;; Verifies signatures, stores locally")
      (p "#### Sync (Bidirectional)")
      (code scheme "(lazy-sync peer)\n;; Push then pull\n;; Returns conflict report if any"))
    (subsection
      "Lazy Semantics"
      (p "No continuous connection. Nodes are offline by default.")
      (p "No consistency guarantees. Nodes may diverge.")
      (p "No automatic resolution. Conflicts flagged for humans.")
      (p "No urgency. Sync happens when convenient.")))
  (section
    "State Tracking"
    (subsection
      "Version Vector"
      (p "Each node tracks what it knows about others:")
      (code scheme "(define-record-type <version-vector>\n  (make-version-vector entries)\n  version-vector?\n  (entries vv-entries))  ; Hash: node-id → latest-sequence\n\n;; Alice's view:\n;; { alice: 42, bob: 37, carol: 29 }"))
    (subsection
      "Sync Calculation"
      (code scheme "(define (compute-sync-set local-vv remote-vv)\n  \"What to send/receive\"\n  (let ((to-send '())\n        (to-receive '()))\n    (for-each\n      (lambda (node)\n        (let ((local-seq (vv-get local-vv node))\n              (remote-seq (vv-get remote-vv node)))\n          (cond\n            ((> local-seq remote-seq)\n             (push! to-send (releases-between node remote-seq local-seq)))\n            ((< local-seq remote-seq)\n             (push! to-receive (list node remote-seq local-seq))))))\n      (all-nodes local-vv remote-vv))\n    (values to-send to-receive)))")))
  (section
    "Conflict Detection"
    (subsection
      "Divergence"
      (p "Same version, different content:")
      (code scheme "(lazy-sync \"bob\")\n;; =>\n;; ⚠ Conflict detected:\n;;   Version 2.1.0\n;;   Local:  sha512:abc123...\n;;   Remote: sha512:def456...\n;;\n;;   Both modified since common ancestor 2.0.0"))
    (subsection
      "Conflict Record"
      (code scheme "(conflict\n  (version \"2.1.0\")\n  (local-hash \"sha512:abc123...\")\n  (remote-hash \"sha512:def456...\")\n  (common-ancestor \"2.0.0\")\n  (detected \"2026-01-06T15:30:00Z\")\n  (status pending))  ; pending, resolved-local, resolved-remote, merged"))
    (subsection
      "Resolution"
      (p "Manual resolution required:")
      (code scheme "(lazy-resolve \"2.1.0\" prefer: 'local)\n;; or\n(lazy-resolve \"2.1.0\" prefer: 'remote)\n;; or\n(lazy-resolve \"2.1.0\" merged: \"2.1.0-merged\")")))
  (section
    "Offline Operation"
    (subsection
      "Work Offline"
      (code scheme "(seal-commit \"Add feature\")\n(seal-release \"2.2.0\")\n;; All local, no network required"))
    (subsection
      "Queue for Sync"
      (code scheme "(lazy-queue)\n;; =>\n;; Pending sync:\n;;   2.1.1  (local, not pushed)\n;;   2.2.0  (local, not pushed)\n;;\n;; To sync: (lazy-push \"bob\")"))
    (subsection
      "Reconnect and Sync"
      (code scheme "(lazy-sync \"bob\")\n;; Sends 2.1.1, 2.2.0\n;; Receives bob's changes\n;; Reports any conflicts")))
  (section
    "Cluster Operations"
    (subsection
      "Join Cluster"
      (code scheme "(lazy-join \"bob\"\n  uri: \"git@github.com:bob/vault.git\"\n  key: bob-public-key)\n;; Registers peer, doesn't sync yet"))
    (subsection
      "Initial Sync"
      (code scheme "(lazy-pull \"bob\")\n;; Gets bob's full history\n;; Verifies all signatures"))
    (subsection
      "Leave Cluster"
      (code scheme "(lazy-leave \"bob\")\n;; Removes peer from sync list\n;; Keeps local copies of bob's releases"))
    (subsection
      "Cluster Status"
      (code scheme "(lazy-status)\n;; =>\n;; Cluster peers:\n;;   bob    last-sync: 2026-01-05  versions: 1.0.0-2.1.0  ✓\n;;   carol  last-sync: 2026-01-03  versions: 1.0.0-2.0.0  (2 behind)\n;;   dave   last-sync: never       versions: none         (not synced)\n;;\n;; Local: 2.2.0 (2 ahead of cluster)")))
  (section
    "Sync Strategies"
    (subsection
      "Manual (Default)"
      (code scheme "(vault-config 'sync-strategy 'manual)\n;; User explicitly calls lazy-sync"))
    (subsection
      "Periodic"
      (code scheme "(vault-config 'sync-strategy 'periodic)\n(vault-config 'sync-interval 3600)  ; hourly\n;; Background sync when network available"))
    (subsection
      "On-Commit"
      (code scheme "(vault-config 'sync-strategy 'on-commit)\n;; Push after each seal-commit\n;; Still lazy (non-blocking, best-effort)"))
    (subsection
      "On-Release"
      (code scheme "(vault-config 'sync-strategy 'on-release)\n;; Push only after seal-release\n;; Most conservative")))
  (section
    "Consistency Guarantees"
    (subsection
      "What We Guarantee"
      (list
        (item "Signature integrity: All releases verified")
        (item "Causal ordering: Within single node")
        (item "Conflict detection: Divergence detected")
        (item "Audit preservation: Full history kept")))
    (subsection
      "What We Don't Guarantee"
      (list
        (item "Global ordering: Nodes may see different orders")
        (item "Consistency: Nodes may have different content")
        (item "Availability: Offline nodes are offline")
        (item "Automatic resolution: Humans must resolve")))
    (subsection
      "CAP Theorem Position"
      (code "      Consistency\n          /\\\n         /  \\\n        /    \\\n       / Lazy \\\n      / Cluster\\\n     /    ✓     \\\n    /\\\nAvailability    Partition\n    ✓           Tolerance ✓")
      (p "We choose AP: Available and Partition-tolerant, eventually consistent.")))
  (section
    "Comparison with Other Modes"
    (table
      (header "Aspect " "Lazy Cluster " "Federation (Memo-010) " "Byzantine (Memo-011) ")
      (row "Trust " "Friends " "Verified peers " "Adversarial ")
      (row "Sync " "Manual/periodic " "Announcement-based " "Consensus ")
      (row "Conflicts " "Manual resolve " "Detect + flag " "Prevented ")
      (row "Offline " "Full support " "Partial " "Requires quorum ")
      (row "Complexity " "Minimal " "Medium " "High ")
      (row "Use case " "Small groups " "Organizations " "Critical systems ")))
  (section
    "Example Session"
    (code scheme ";; Morning: Alice works offline\n(seal-commit \"Add authentication\")\n(seal-commit \"Add authorization\")\n(seal-release \"2.3.0\")\n\n;; Lunch: Alice syncs with Bob\n(lazy-sync \"bob\")\n;; => Pushed 2.3.0 to bob\n;; => Pulled 2.2.1 from bob\n;; => No conflicts\n\n;; Evening: Alice syncs with Carol\n(lazy-sync \"carol\")\n;; => Pushed 2.2.1, 2.3.0 to carol\n;; => Pulled nothing (carol hasn't released)\n;; => ⚠ Carol has unsynced commits (not our concern)"))
  (section
    "Security Considerations"
    (subsection
      "Trust Model"
      (p "Lazy clustering assumes good-faith peers:")
      (list
        (item "Peers won't inject malicious releases")
        (item "Peers won't withhold releases maliciously")
        (item "Peers will eventually sync"))
      (p "Not suitable for: Adversarial environments, high-value targets.")
      (p "Suitable for: Research groups, open source projects, friend networks."))
    (subsection
      "Signature Verification"
      (p "All releases still verified:")
      (code scheme "(lazy-pull \"bob\")\n;; Each release:\n;;   1. Verify Ed25519 signature\n;;   2. Verify hash matches content\n;;   3. Check against known bob public key\n;;   4. Store only if valid"))
    (subsection
      "Conflict Attacks"
      (p "Malicious peer creates conflicting release.")
      (p "Mitigation: - Conflicts flagged, not auto-resolved - Full audit trail of conflict - Peer reputation tracking")))
  (section
    "Implementation Notes"
    (subsection
      "Dependencies"
      (list
        (item "crypto-ffi")
        (item "Signature verification - audit")
        (item "Sync logging")
        (item "Transport (git/HTTP/filesystem)")))
    (subsection
      "Storage"
      (code ".vault/\n  lazy/\n    peers.sexp        # Registered peers\n    vectors.sexp      # Version vectors\n    conflicts/        # Unresolved conflicts\n    queue/            # Pending pushes")))
  (section
    "References"
    (list
      (item "Saito, Y., & Shapiro, M. (2005). Optimistic Replication.")
      (item "Terry, D., et al. (1995). Managing Update Conflicts in Bayou.")
      (item "DeCandia, G., et al. (2007). Dynamo: Amazon's Key-Value Store.")
      (item "Memo-010: Federation Protocol")
      (item "Memo-012: Lamport Logical Clocks")))
  (section
    "Changelog"
    (list
      (item "2026-01-06")
      (item "Set minimum bandwidth: 128 Kb/s floor (dual-ISDN), 1 Mb/s target (T1) - 2026-01-06")
      (item "Initial specification"))))

