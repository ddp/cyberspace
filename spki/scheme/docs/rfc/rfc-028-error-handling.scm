;; Auto-converted from Markdown
;; Review and edit as needed

(rfc
  (number 28)
  (title "Error Handling and Recovery")
  (section
    "Abstract"
    (p "This RFC specifies error handling and recovery for the Library of Cyberspace: how vaults detect, report, and recover from failures while maintaining integrity guarantees. Errors are first-class objects in the soup, enabling systematic analysis and automated recovery."))
  (section
    "Motivation"
    (p "Distributed systems fail in creative ways:")
    (list
      (item "Network partitions")
      (item "Vaults lose contact")
      (item "Storage corruption")
      (item "Bits flip, disks fail")
      (item "Byzantine faults")
      (item "Nodes lie or misbehave")
      (item "Resource exhaustion")
      (item "Out of memory, disk, connections")
      (item "Protocol violations")
      (item "Malformed messages, invalid state"))
    (p "Recovery must be:")
    (list
      (item "Deterministic")
      (item "Same error, same recovery")
      (item "Auditable")
      (item "Every error logged with context")
      (item "Automatic")
      (item "Self-healing where possible")
      (item "Graceful")
      (item "Degrade rather than crash")))
  (section
    "Error Model"
    (subsection
      "Error Types"
      (code scheme "(define-error-type 'storage-error\n  (subtypes corruption missing full readonly))\n\n(define-error-type 'network-error\n  (subtypes timeout unreachable protocol-violation))\n\n(define-error-type 'crypto-error\n  (subtypes signature-invalid key-expired capability-denied))\n\n(define-error-type 'consistency-error\n  (subtypes hash-mismatch merkle-divergence conflict))\n\n(define-error-type 'resource-error\n  (subtypes memory-exhausted connections-exhausted rate-limited))\n\n(define-error-type 'protocol-error\n  (subtypes invalid-message invalid-state version-mismatch))"))
    (subsection
      "Error Structure"
      (code scheme "(define (make-error type message context)\n  `(error\n    (id ,(generate-error-id))\n    (type ,type)\n    (message ,message)\n    (context ,context)\n    (timestamp ,(current-time))\n    (vault ,(current-vault-id))\n    (principal ,(current-principal))\n    (stack ,(capture-stack-trace))))\n\n;; Errors are soup objects\n(define (record-error! err)\n  (let ((hash (soup-put err type: 'error)))\n    (audit-append action: 'error-recorded error-hash: hash)\n    hash))"))
    (subsection
      "Error Context"
      (code scheme ";; Capture rich context for debugging\n(define (error-context operation)\n  `((operation . ,operation)\n    (request-id . ,(current-request-id))\n    (correlation-id . ,(current-correlation-id))\n    (peer . ,(current-peer))\n    (attempt . ,(current-retry-count))\n    (duration . ,(operation-duration))\n    (inputs . ,(sanitize-inputs (operation-inputs)))))")))
  (section
    "Error Handling Patterns"
    (subsection
      "Result Type"
      (code scheme ";; Operations return (ok value) or (err error)\n(define (result-ok value) (ok ,value))\n(define (result-err error) (err ,error))\n\n(define (result-ok? r) (eq? (car r) 'ok))\n(define (result-err? r) (eq? (car r) 'err))\n(define (result-value r) (cadr r))\n(define (result-error r) (cadr r))\n\n;; Chain operations\n(define (result-bind r f)\n  (if (result-ok? r)\n      (f (result-value r))\n      r))\n\n;; Example\n(define (safe-read hash)\n  (result-bind (cas-get-safe hash)\n    (lambda (data)\n      (result-bind (verify-signature data)\n        (lambda (verified)\n          (result-ok verified))))))"))
    (subsection
      "Error Recovery"
      (code scheme "(define (with-recovery operation recovery)\n  \"Execute operation with recovery on failure\"\n  (let ((result (guard (ex (else (result-err ex)))\n                  (result-ok (operation)))))\n    (if (result-ok? result)\n        (result-value result)\n        (recovery (result-error result)))))\n\n;; Example: read with fallback to replica\n(define (read-with-fallback hash)\n  (with-recovery\n    (lambda () (cas-get hash))\n    (lambda (err)\n      (audit-append action: 'read-fallback error: err)\n      (cas-get-from-replica hash))))"))
    (subsection
      "Retry Logic"
      (code scheme "(define (with-retry operation max-retries backoff)\n  \"Retry operation with exponential backoff\"\n  (let loop ((attempt 1))\n    (let ((result (guard (ex (else (result-err ex)))\n                    (result-ok (operation)))))\n      (cond\n        ((result-ok? result)\n         (result-value result))\n        ((>= attempt max-retries)\n         (error \"Max retries exceeded\" (result-error result)))\n        (else\n         (let ((delay ( backoff (expt 2 (- attempt 1)))))\n           (audit-append action: 'retry attempt: attempt delay: delay)\n           (thread-sleep! delay)\n           (loop (+ attempt 1))))))))\n\n;; Retry configuration\n(define default-retry-config*\n  `((max-retries . 3)\n    (initial-backoff . 100)    ; ms\n    (max-backoff . 30000)      ; ms\n    (jitter . 0.1)))           ; 10% randomization"))
    (subsection
      "Circuit Breaker"
      (code scheme "(define (make-circuit-breaker threshold timeout)\n  (let ((failures 0)\n        (state 'closed)\n        (last-failure #f))\n\n    (lambda (operation)\n      (case state\n        ((open)\n         (if (> (- (current-time) last-failure) timeout)\n             (begin\n               (set! state 'half-open)\n               (try-operation operation))\n             (error \"Circuit open\")))\n        ((half-open)\n         (let ((result (try-operation operation)))\n           (if (result-ok? result)\n               (begin\n                 (set! state 'closed)\n                 (set! failures 0)\n                 (result-value result))\n               (begin\n                 (set! state 'open)\n                 (error \"Circuit reopened\")))))\n        ((closed)\n         (try-operation operation))))))\n\n(define (try-operation cb operation)\n  (guard (ex\n          (else\n           (cb-record-failure! cb)\n           (result-err ex)))\n    (result-ok (operation))))")))
  (section
    "Storage Errors"
    (subsection
      "Corruption Detection"
      (code scheme "(define (detect-corruption hash)\n  \"Verify object integrity\"\n  (let* ((data (storage-read-raw hash))\n         (computed-hash (content-hash data)))\n    (unless (equal? hash computed-hash)\n      (record-error!\n        (make-error 'corruption\n          \"Hash mismatch detected\"\n          `((expected . ,hash)\n            (computed . ,computed-hash)\n            (size . ,(bytevector-length data))))))))\n\n(define (scan-for-corruption)\n  \"Full vault integrity scan\"\n  (let ((corrupted '()))\n    (for-each (lambda (hash)\n                (unless (verify-integrity hash)\n                  (set! corrupted (cons hash corrupted))))\n              (all-object-hashes))\n    (when (not (null? corrupted))\n      (audit-append action: 'corruption-scan\n                    corrupted: (length corrupted)))\n    corrupted))"))
    (subsection
      "Corruption Recovery"
      (code scheme "(define (recover-corrupted hash)\n  \"Attempt to recover corrupted object\"\n  ;; Strategy 1: Fetch from replica\n  (let ((replicas (find-replicas hash)))\n    (for-each (lambda (replica)\n                (let ((data (fetch-from-replica replica hash)))\n                  (when (and data (verify-hash data hash))\n                    (storage-write hash data)\n                    (audit-append action: 'corruption-recovered\n                                  source: replica)\n                    (return data))))\n              replicas))\n\n  ;; Strategy 2: Reconstruct from erasure coding\n  (when (erasure-coded? hash)\n    (let ((data (reconstruct-from-shards hash)))\n      (when data\n        (storage-write hash data)\n        (audit-append action: 'erasure-recovery)\n        (return data))))\n\n  ;; Strategy 3: Mark as lost\n  (mark-object-lost hash)\n  (audit-append action: 'object-lost hash: hash)\n  #f)"))
    (subsection
      "Disk Full Handling"
      (code scheme "(define (handle-disk-full)\n  \"Emergency disk space recovery\"\n  ;; Phase 1: Emergency GC\n  (gc-emergency)\n\n  ;; Phase 2: Clear caches\n  (clear-all-caches)\n\n  ;; Phase 3: Compress compressible objects\n  (compress-uncompressed-objects)\n\n  ;; Phase 4: Alert and degrade\n  (when (< (available-space) critical-threshold)\n    (alert-disk-critical)\n    (vault-readonly!)))")))
  (section
    "Network Errors"
    (subsection
      "Timeout Handling"
      (code scheme "(define (with-timeout duration operation)\n  \"Execute operation with timeout\"\n  (let ((result (make-channel)))\n    (thread-start!\n      (make-thread\n        (lambda ()\n          (channel-put! result\n            (guard (ex (else (result-err ex)))\n              (result-ok (operation)))))))\n    (let ((r (channel-get! result duration)))\n      (if r\n          (if (result-ok? r)\n              (result-value r)\n              (error (result-error r)))\n          (error (make-error 'timeout\n                   \"Operation timed out\"\n                   `((duration . ,duration))))))))"))
    (subsection
      "Partition Detection"
      (code scheme "(define (detect-partition peers)\n  \"Detect network partition\"\n  (let* ((reachable (filter peer-reachable? peers))\n         (unreachable (filter (lambda (p) (not (peer-reachable? p))) peers)))\n    (when (> (length unreachable) 0)\n      (audit-append action: 'partition-detected\n                    reachable: (length reachable)\n                    unreachable: (length unreachable))\n      (if (> (length reachable) (/ (length peers) 2))\n          (continue-with-majority reachable)\n          (enter-read-only-mode)))))"))
    (subsection
      "Connection Pool Recovery"
      (code scheme "(define (recover-connection-pool pool)\n  \"Recover from connection pool exhaustion\"\n  ;; Close idle connections\n  (pool-close-idle! pool)\n\n  ;; Close long-running connections\n  (pool-close-stale! pool max-connection-age)\n\n  ;; If still exhausted, reject new requests\n  (when (pool-exhausted? pool)\n    (audit-append action: 'pool-exhausted)\n    (enable-request-shedding)))")))
  (section
    "Consistency Errors"
    (subsection
      "Conflict Detection"
      (code scheme "(define (detect-conflict hash versions)\n  \"Detect conflicting versions of object\"\n  (let ((unique-contents (delete-duplicates\n                          (map version-content versions))))\n    (when (> (length unique-contents) 1)\n      (record-error!\n        (make-error 'conflict\n          \"Conflicting versions detected\"\n          `((hash . ,hash)\n            (versions . ,(length unique-contents))\n            (sources . ,(map version-source versions))))))))"))
    (subsection
      "Conflict Resolution"
      (code scheme "(define (resolve-conflict hash versions strategy)\n  \"Resolve conflicting versions\"\n  (let ((resolved\n         (case strategy\n           ((latest)\n            (max-by version-timestamp versions))\n           ((merge)\n            (merge-versions versions))\n           ((manual)\n            (queue-for-manual-resolution hash versions))\n           ((tombstone)\n            (create-conflict-tombstone hash versions)))))\n    (audit-append action: 'conflict-resolved\n                  hash: hash\n                  strategy: strategy)\n    resolved))"))
    (subsection
      "Merkle Divergence"
      (code scheme "(define (handle-merkle-divergence local-root remote-root peer)\n  \"Handle diverged Merkle trees\"\n  (let ((divergence (find-divergence-point local-root remote-root)))\n    (audit-append action: 'merkle-divergence\n                  local: local-root\n                  remote: remote-root\n                  divergence: divergence)\n    ;; Sync diverged subtrees\n    (for-each (lambda (subtree)\n                (sync-subtree subtree peer))\n              (divergent-subtrees divergence))))")))
  (section
    "Recovery Procedures"
    (subsection
      "Automatic Recovery"
      (code scheme "(define recovery-handlers\n  `((corruption . ,recover-corrupted)\n    (missing . ,fetch-from-replica)\n    (timeout . ,retry-with-backoff)\n    (partition . ,wait-for-reconnection)\n    (conflict . ,resolve-with-default-strategy)))\n\n(define (auto-recover error)\n  \"Attempt automatic recovery\"\n  (let ((handler (assoc-ref recovery-handlers (error-type error))))\n    (if handler\n        (begin\n          (audit-append action: 'auto-recovery-attempt\n                        error: (error-id error))\n          (handler error))\n        (escalate-error error))))"))
    (subsection
      "Manual Recovery"
      (code scheme "(define (queue-manual-recovery error)\n  \"Queue error for manual intervention\"\n  (soup-put\n    `(recovery-ticket\n      (error ,(error-id error))\n      (status pending)\n      (created ,(current-time))\n      (assigned #f))\n    type: 'recovery-ticket))\n\n(define (process-recovery-ticket ticket-hash)\n  \"Process manual recovery ticket\"\n  (let ((ticket (soup-get ticket-hash)))\n    ;; Mark in progress\n    (soup-update ticket-hash status: 'in-progress)\n    ;; ... manual recovery steps ...\n    ;; Mark resolved\n    (soup-update ticket-hash\n                 status: 'resolved\n                 resolved-at: (current-time)\n                 resolved-by: (current-principal))))"))
    (subsection
      "Disaster Recovery"
      (code scheme "(define (disaster-recovery backup-location)\n  \"Full vault recovery from backup\"\n  (audit-append action: 'disaster-recovery-start\n                backup: backup-location)\n\n  ;; Phase 1: Verify backup integrity\n  (unless (verify-backup-integrity backup-location)\n    (error \"Backup integrity check failed\"))\n\n  ;; Phase 2: Restore CAS\n  (restore-cas-from-backup backup-location)\n\n  ;; Phase 3: Restore soup\n  (restore-soup-from-backup backup-location)\n\n  ;; Phase 4: Restore indexes\n  (rebuild-indexes)\n\n  ;; Phase 5: Verify restoration\n  (verify-restoration)\n\n  (audit-append action: 'disaster-recovery-complete))")))
  (section
    "Error Reporting"
    (subsection
      "Error Aggregation"
      (code scheme "(define (aggregate-errors window)\n  \"Aggregate errors over time window\"\n  (let ((errors (soup-query type: 'error\n                            timestamp: (> (- (current-time) window)))))\n    (group-by error-type errors)))\n\n(define (error-rate error-type window)\n  \"Calculate error rate\"\n  (let ((count (length (soup-query type: 'error\n                                   error-type: error-type\n                                   timestamp: (> (- (current-time) window))))))\n    (/ count window)))"))
    (subsection
      "Alerting"
      (code scheme "(define alert-thresholds\n  `((corruption . 1)        ; Any corruption is critical\n    (timeout . 100)         ; 100 timeouts per minute\n    (conflict . 10)         ; 10 conflicts per minute\n    (resource . 5)))        ; 5 resource errors per minute\n\n(define (check-alert-thresholds)\n  \"Check if error rates exceed thresholds\"\n  (for-each (lambda (threshold)\n              (let ((type (car threshold))\n                    (limit (cdr threshold)))\n                (when (> (error-rate type 60) limit)\n                  (send-alert type (error-rate type 60) limit))))\n            alert-thresholds))")))
  (section
    "Security Considerations"
    (subsection
      "Error Information Leakage"
      (code scheme ";; Don't expose internal details in user-facing errors\n(define (sanitize-error-for-user error)\n  `(error\n    (type ,(error-type error))\n    (message ,(user-safe-message (error-type error)))\n    (request-id ,(error-request-id error))))\n\n;; Full details only in audit log\n(define (log-full-error error)\n  (audit-append action: 'error\n                error: error))  ; Full context preserved"))
    (subsection
      "Error-Based Attacks"
      (code scheme ";; Rate limit error generation to prevent DoS\n(define error-rate-limiter\n  (make-rate-limiter 1000 60))  ; 1000 errors per minute max\n\n(define (rate-limited-record-error! err)\n  (if (rate-limiter-allow? error-rate-limiter)\n      (record-error! err)\n      (audit-append action: 'error-rate-limited)))")))
  (section
    "References"
    (p "1. [Release It!](https://pragprog.com/titles/mnee2/release-it-second-edition/) - Nygard 2. [Hystrix](https://github.com/Netflix/Hystrix) - Netflix Circuit Breaker 3. [RFC-003: Cryptographic Audit Trail](rfc-003-audit-trail.html) 4. [RFC-026: Garbage Collection](rfc-026-garbage-collection.html)"))
  (section
    "Changelog"
    (list
      (item "2026-01-07")
      (item "Initial draft"))))

