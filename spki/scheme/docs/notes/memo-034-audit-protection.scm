;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 34)
  (title "Audit Log Protection")
  (section
    "Abstract"
    (p "This RFC specifies protection mechanisms for the Library of Cyberspace audit log: how the system prevents resource exhaustion, log flooding, and denial of service attacks against the audit trail while maintaining its integrity as the authoritative record of all vault operations."))
  (section
    "Motivation"
    (p "The audit log is sacred:")
    (list
      (item "Evidence")
      (item "Legal and forensic record")
      (item "Accountability")
      (item "Who did what when")
      (item "Recovery")
      (item "Reconstruct state after failure")
      (item "Trust")
      (item "Foundation of the security model"))
    (p "But the audit log is also a target:")
    (list
      (item "Flooding")
      (item "Generate noise to hide malicious activity")
      (item "Exhaustion")
      (item "Fill storage to halt operations")
      (item "Evasion")
      (item "Overwhelm to prevent logging of real attacks")
      (item "Amplification")
      (item "Small action triggers large log entries"))
    (p "The audit log must protect itself while never failing to record."))
  (section
    "Threat Model"
    (subsection
      "Attack Vectors"
      (code scheme "(define audit-threats\n  '((flooding\n     (description \"Generate massive log volume\")\n     (goal \"Hide malicious activity in noise\")\n     (method \"Rapid legitimate-looking operations\"))\n\n    (exhaustion\n     (description \"Fill audit storage\")\n     (goal \"Halt vault operations\")\n     (method \"Sustained high-volume logging\"))\n\n    (amplification\n     (description \"Small input, large log output\")\n     (goal \"Asymmetric resource consumption\")\n     (method \"Operations that log disproportionately\"))\n\n    (corruption\n     (description \"Tamper with log entries\")\n     (goal \"Alter historical record\")\n     (method \"Exploit write access to log storage\"))\n\n    (truncation\n     (description \"Force log rotation/deletion\")\n     (goal \"Remove evidence\")\n     (method \"Fill logs to trigger cleanup\"))))"))
    (subsection
      "Attacker Capabilities"
      (code scheme ";; Assume attacker can:\n;; - Authenticate as a valid principal\n;; - Perform many legitimate operations\n;; - Control timing of operations\n;; - Observe system behavior\n\n;; Assume attacker cannot:\n;; - Directly write to audit storage\n;; - Forge signatures on log entries\n;; - Break cryptographic primitives")))
  (section
    "Rate Limiting"
    (subsection
      "Per-Principal Audit Limits"
      (code scheme "(define audit-rate-limits\n  `((entries-per-second . 100)\n    (bytes-per-second . 102400)      ; 100KB/s\n    (entries-per-minute . 1000)\n    (bytes-per-minute . 10485760)))  ; 10MB/min\n\n(define principal-audit-buckets (make-hash-table))\n\n(define (get-audit-bucket principal)\n  (or (hash-table-ref principal-audit-buckets principal #f)\n      (let ((bucket (make-token-bucket\n                     (assoc-ref audit-rate-limits 'entries-per-second)\n                     (assoc-ref audit-rate-limits 'entries-per-second))))\n        (hash-table-set! principal-audit-buckets principal bucket)\n        bucket)))\n\n(define (audit-rate-check principal entry-size)\n  \"Check if principal can generate audit entry\"\n  (let ((bucket (get-audit-bucket principal)))\n    (bucket 1)))  ; Consume one token"))
    (subsection
      "Audit Entry Costing"
      (code scheme ";; Different operations have different audit costs\n(define audit-costs\n  `((read . 1)\n    (write . 2)\n    (delete . 5)\n    (query . 1)\n    (admin . 10)\n    (key-operation . 50)\n    (emergency . 0)))  ; Always allowed\n\n(define (audit-cost action)\n  (or (assoc-ref audit-costs action) 1))\n\n(define (consume-audit-budget principal action)\n  \"Deduct from principal's audit budget\"\n  (let ((cost (audit-cost action))\n        (bucket (get-audit-bucket principal)))\n    (if (bucket cost)\n        #t\n        (begin\n          ;; Log the rate limit event (always succeeds)\n          (audit-append-privileged\n            action: 'audit-rate-limited\n            principal: principal\n            attempted-action: action)\n          #f))))"))
    (subsection
      "Burst Handling"
      (code scheme ";; Allow short bursts but limit sustained rate\n(define (make-audit-limiter)\n  (let ((short-term (make-token-bucket 200 100))   ; 100/s, burst 200\n        (long-term (make-sliding-window 10000 60))) ; 10k/min\n    (lambda (cost)\n      (and (short-term cost)\n           (long-term)))))")))
  (section
    "Storage Protection"
    (subsection
      "Reserved Audit Space"
      (code scheme ";; Always reserve space for audit\n(define audit-reserved-space ( 1024 1024 1024))  ; 1GB minimum\n\n(define (audit-storage-available)\n  (let ((total (storage-available))\n        (audit-used (audit-storage-used)))\n    (max 0 (- total audit-reserved-space*))))\n\n(define (check-audit-storage entry-size)\n  \"Ensure space for audit entry\"\n  (let ((available (audit-storage-available)))\n    (when (< available entry-size)\n      ;; Emergency: halt non-audit operations\n      (enter-audit-protection-mode)\n      ;; But always log\n      #t)))"))
    (subsection
      "Audit Protection Mode"
      (code scheme "(define audit-protection-mode? (make-parameter #f))\n\n(define (enter-audit-protection-mode)\n  \"Emergency mode: only allow audit writes\"\n  (audit-protection-mode? #t)\n  (audit-append-privileged\n    action: 'audit-protection-enabled\n    reason: 'storage-exhaustion)\n  ;; Reject all non-essential operations\n  (set-vault-mode! 'audit-only))\n\n(define (exit-audit-protection-mode)\n  \"Resume normal operations\"\n  (when (> (audit-storage-available) ( 2 audit-reserved-space*))\n    (audit-protection-mode? #f)\n    (set-vault-mode! 'normal)\n    (audit-append-privileged\n      action: 'audit-protection-disabled)))"))
    (subsection
      "Tiered Storage"
      (code scheme ";; Audit log tiers\n(define audit-tiers\n  '((hot . ((retention . 86400)      ; 1 day\n            (storage . ssd)\n            (compression . none)))\n    (warm . ((retention . 604800)    ; 7 days\n             (storage . hdd)\n             (compression . zstd-fast)))\n    (cold . ((retention . 31536000)  ; 1 year\n             (storage . archive)\n             (compression . zstd-max)))\n    (glacier . ((retention . #f)     ; Forever\n                (storage . offsite)\n                (compression . zstd-max)))))\n\n(define (tier-audit-entry entry age)\n  \"Move entry to appropriate storage tier\"\n  (let ((tier (find (lambda (t)\n                      (or (not (assoc-ref (cdr t) 'retention))\n                          (< age (assoc-ref (cdr t) 'retention))))\n                    audit-tiers)))\n    (migrate-to-tier entry (car tier))))")))
  (section
    "Entry Size Limits"
    (subsection
      "Maximum Entry Size"
      (code scheme "(define max-audit-entry-size 65536)  ; 64KB\n\n(define (validate-audit-entry entry)\n  \"Validate entry before logging\"\n  (let ((size (serialized-size entry)))\n    (when (> size max-audit-entry-size)\n      (error 'audit-entry-too-large\n             `((size . ,size)\n               (limit . ,max-audit-entry-size))))))"))
    (subsection
      "Entry Truncation"
      (code scheme "(define (truncate-audit-entry entry max-size)\n  \"Truncate oversized entry while preserving critical fields\"\n  (let ((critical '(action principal timestamp hash signature)))\n    (let loop ((entry entry)\n               (fields (entry-fields entry)))\n      (if (<= (serialized-size entry) max-size)\n          entry\n          (let ((removable (find (lambda (f)\n                                   (not (member f critical)))\n                                 fields)))\n            (if removable\n                (loop (assoc-remove entry removable)\n                      (delete removable fields))\n                ;; Can't truncate further, log warning\n                (begin\n                  (audit-append-privileged\n                    action: 'audit-entry-truncation-failed\n                    original-size: (serialized-size entry))\n                  entry)))))))"))
    (subsection
      "Payload Summarization"
      (code scheme "(define (summarize-large-payload payload)\n  \"Summarize large payloads for audit\"\n  (if (> (bytevector-length payload) 1024)\n      `((type . summarized)\n        (original-size . ,(bytevector-length payload))\n        (hash . ,(content-hash payload))\n        (preview . ,(subbytevector payload 0 256)))\n      payload))")))
  (section
    "Aggregation"
    (subsection
      "Event Aggregation"
      (code scheme ";; Aggregate similar events to reduce volume\n(define aggregation-window 60)  ; seconds\n(define pending-aggregations (make-hash-table))\n\n(define (aggregate-audit-event action principal details)\n  \"Aggregate similar events within window\"\n  (let* ((key (list action principal))\n         (existing (hash-table-ref pending-aggregations key #f)))\n    (if existing\n        ;; Add to existing aggregation\n        (begin\n          (set-cdr! (assoc 'count existing)\n                    (+ 1 (assoc-ref existing 'count)))\n          (set-cdr! (assoc 'last-seen existing)\n                    (current-time)))\n        ;; Start new aggregation\n        (hash-table-set! pending-aggregations key\n          `((action . ,action)\n            (principal . ,principal)\n            (count . 1)\n            (first-seen . ,(current-time))\n            (last-seen . ,(current-time))\n            (sample . ,details))))))\n\n(define (flush-aggregations)\n  \"Flush aggregated events to audit log\"\n  (hash-table-walk pending-aggregations\n    (lambda (key agg)\n      (when (> (- (current-time) (assoc-ref agg 'first-seen))\n               aggregation-window)\n        (audit-append-direct\n          action: 'aggregated-events\n          original-action: (assoc-ref agg 'action)\n          principal: (assoc-ref agg 'principal)\n          count: (assoc-ref agg 'count)\n          window-start: (assoc-ref agg 'first-seen)\n          window-end: (assoc-ref agg 'last-seen)\n          sample: (assoc-ref agg 'sample))\n        (hash-table-delete! pending-aggregations key)))))"))
    (subsection
      "Sampling"
      (code scheme ";; Sample high-volume events\n(define (should-sample? action principal)\n  (let ((rate (current-rate action principal)))\n    (cond\n      ((< rate 10) #t)              ; Always log low-rate\n      ((< rate 100) (< (random 1.0) 0.5))  ; 50% sample\n      ((< rate 1000) (< (random 1.0) 0.1)) ; 10% sample\n      (else (< (random 1.0) 0.01)))))      ; 1% sample\n\n(define (audit-with-sampling action principal details)\n  \"Log with sampling for high-volume events\"\n  (if (should-sample? action principal)\n      (audit-append action: action\n                    principal: principal\n                    details: details\n                    sampled: #t)\n      ;; Still count for rate tracking\n      (increment-audit-counter action principal)))")))
  (section
    "Anomaly Detection"
    (subsection
      "Baseline Establishment"
      (code scheme "(define (establish-audit-baseline principal duration)\n  \"Establish normal audit patterns for principal\"\n  (let ((events (soup-query type: 'audit-entry\n                            principal: principal\n                            timestamp: (> (- (current-time) duration)))))\n    `((events-per-hour . ,(/ (length events) (/ duration 3600)))\n      (common-actions . ,(top-n (map audit-action events) 10))\n      (typical-hours . ,(typical-active-hours events))\n      (established-at . ,(current-time)))))"))
    (subsection
      "Anomaly Detection"
      (code scheme "(define (detect-audit-anomaly principal current-rate baseline)\n  \"Detect anomalous audit patterns\"\n  (let ((expected (assoc-ref baseline 'events-per-hour))\n        (threshold 3.0))  ; 3x normal is anomalous\n    (when (> current-rate ( threshold expected))\n      (audit-append-privileged\n        action: 'audit-anomaly-detected\n        principal: principal\n        current-rate: current-rate\n        expected-rate: expected\n        severity: (if (> current-rate ( 10 expected))\n                      'critical\n                      'warning))\n      ;; Potentially throttle\n      (when (> current-rate (* 10 expected))\n        (throttle-principal principal)))))"))
    (subsection
      "Flood Detection"
      (code scheme "(define (detect-audit-flood)\n  \"Detect system-wide audit flooding\"\n  (let ((current-rate (global-audit-rate))\n        (threshold (* 10 (baseline-global-rate))))\n    (when (> current-rate threshold)\n      ;; Identify top contributors\n      (let ((top-principals (top-audit-principals 10)))\n        (audit-append-privileged\n          action: 'audit-flood-detected\n          global-rate: current-rate\n          threshold: threshold\n          top-principals: top-principals)\n        ;; Throttle top contributors\n        (for-each throttle-principal\n                  (map car top-principals))))))")))
  (section
    "Privileged Logging"
    (subsection
      "System Events"
      (code scheme ";; Some events bypass rate limits\n(define privileged-actions\n  '(audit-rate-limited\n    audit-protection-enabled\n    audit-protection-disabled\n    audit-anomaly-detected\n    audit-flood-detected\n    key-ceremony\n    emergency-revoke\n    security-alert))\n\n(define (audit-append-privileged . args)\n  \"Log privileged event (bypasses rate limits)\"\n  (let ((entry (apply make-audit-entry args)))\n    ;; Always log, never rate limit\n    (audit-write-direct entry)\n    ;; Alert on privileged events\n    (when (member (assoc-ref entry 'action) '(security-alert emergency-revoke))\n      (send-security-alert entry))))"))
    (subsection
      "Guaranteed Delivery"
      (code scheme "(define (audit-write-guaranteed entry)\n  \"Write audit entry with guaranteed delivery\"\n  ;; Write to multiple locations\n  (let ((locations (list (primary-audit-log)\n                         (secondary-audit-log)\n                         (remote-audit-log))))\n    (let ((successes (filter (lambda (loc)\n                               (guard (ex (else #f))\n                                 (audit-write loc entry)\n                                 #t))\n                             locations)))\n      (when (< (length successes) 2)\n        ;; Failed to write to enough locations\n        (emergency-audit-alert entry successes)))))")))
  (section
    "Integrity Protection"
    (subsection
      "Append-Only Enforcement"
      (code scheme ";; Audit log is strictly append-only\n(define (audit-write entry)\n  \"Append entry to audit log\"\n  (let ((log (current-audit-log)))\n    ;; Verify we're at the end\n    (unless (at-log-end? log)\n      (error 'audit-log-not-at-end))\n    ;; Append with sequence number\n    (let ((seq (next-sequence-number log)))\n      (write-entry log (cons `(sequence . ,seq) entry))\n      ;; Sign the entry\n      (sign-entry log entry))))"))
    (subsection
      "Chain Integrity"
      (code scheme ";; Each entry references previous (blockchain-style)\n(define (chain-entry entry previous-hash)\n  `((previous-hash . ,previous-hash)\n    (sequence . ,(+ 1 (previous-sequence)))\n    (timestamp . ,(current-time))\n    ,@entry\n    (hash . ,(compute-entry-hash entry previous-hash))))\n\n(define (verify-audit-chain log)\n  \"Verify audit log chain integrity\"\n  (let loop ((entries (audit-entries log))\n             (expected-prev #f))\n    (if (null? entries)\n        #t\n        (let ((entry (car entries)))\n          (and (or (not expected-prev)\n                   (equal? (assoc-ref entry 'previous-hash) expected-prev))\n               (loop (cdr entries)\n                     (assoc-ref entry 'hash)))))))")))
  (section
    "Recovery"
    (subsection
      "Log Reconstruction"
      (code scheme "(define (reconstruct-audit-log backups)\n  \"Reconstruct audit log from multiple backups\"\n  (let ((entries (merge-backup-entries backups)))\n    ;; Deduplicate by sequence number\n    (let ((deduped (deduplicate-by-sequence entries)))\n      ;; Verify chain\n      (unless (verify-audit-chain deduped)\n        (error 'audit-chain-broken))\n      deduped)))"))
    (subsection
      "Gap Detection"
      (code scheme "(define (detect-audit-gaps log)\n  \"Find gaps in audit sequence\"\n  (let loop ((entries (audit-entries log))\n             (expected-seq 1)\n             (gaps '()))\n    (if (null? entries)\n        gaps\n        (let ((seq (assoc-ref (car entries) 'sequence)))\n          (if (= seq expected-seq)\n              (loop (cdr entries) (+ seq 1) gaps)\n              (loop (cdr entries) (+ seq 1)\n                    (cons (list expected-seq (- seq 1)) gaps)))))))")))
  (section
    "References"
    (p "1. [NIST SP 800-92: Guide to Computer Security Log Management](https://csrc.nist.gov/publications/detail/sp/800-92/final) 2. [RFC-003: Cryptographic Audit Trail](rfc-003-audit-trail.html) 3. [RFC-032: Rate Limiting and Quotas](rfc-032-rate-limiting.html) 4. [RFC-028: Error Handling and Recovery](rfc-028-error-handling.html)"))
  (section
    "Changelog"
    (list
      (item "2026-01-07")
      (item "Initial draft"))))

