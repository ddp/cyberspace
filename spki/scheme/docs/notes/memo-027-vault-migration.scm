;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 27)
  (title "Vault Migration")
  (section
    "Abstract"
    (p "This RFC specifies vault migration for the Library of Cyberspace: how to move vaults between hosts, storage backends, and administrative domains while preserving content integrity, capability chains, and audit continuity. Migration is essential for long-term preservation."))
  (section
    "Motivation"
    (p "Vaults must outlive their infrastructure:")
    (list
      (item "Hardware failure")
      (item "Disks die, servers decommission")
      (item "Provider changes")
      (item "Cloud vendors come and go")
      (item "Jurisdiction")
      (item "Legal requirements may force relocation")
      (item "Performance")
      (item "Move closer to users")
      (item "Cost")
      (item "Cheaper storage becomes available"))
    (p "Migration must be:")
    (list
      (item "Complete")
      (item "All objects, metadata, capabilities")
      (item "Verifiable")
      (item "Cryptographic proof of integrity")
      (item "Resumable")
      (item "Handle interruptions gracefully")
      (item "Auditable")
      (item "Full trail of what moved where")))
  (section
    "Migration Types"
    (subsection
      "Full Migration"
      (p "Move entire vault to new location:")
      (code scheme "(define (full-migration source-vault target-host)\n  \"Migrate entire vault to new host\"\n  (let ((migration-id (generate-migration-id)))\n    (audit-append action: `(migration-start ,migration-id)\n                  type: 'full\n                  source: source-vault\n                  target: target-host)\n\n    ;; Phase 1: Snapshot\n    (let ((snapshot (vault-snapshot source-vault)))\n      ;; Phase 2: Transfer\n      (transfer-snapshot snapshot target-host)\n      ;; Phase 3: Verify\n      (verify-transfer snapshot target-host)\n      ;; Phase 4: Cutover\n      (cutover source-vault target-host migration-id))))"))
    (subsection
      "Partial Migration"
      (p "Move subset of objects:")
      (code scheme "(define (partial-migration source-vault target-host predicate)\n  \"Migrate objects matching predicate\"\n  (let ((objects (soup-query source-vault predicate)))\n    (for-each (lambda (obj)\n                (migrate-object obj target-host))\n              objects)))"))
    (subsection
      "Live Migration"
      (p "Migrate while vault remains active:")
      (code scheme "(define (live-migration source-vault target-host)\n  \"Migrate without downtime\"\n  ;; Phase 1: Initial sync\n  (let ((checkpoint (initial-sync source-vault target-host)))\n    ;; Phase 2: Catch up changes\n    (let loop ((last-checkpoint checkpoint))\n      (let ((changes (changes-since source-vault last-checkpoint)))\n        (if (< (length changes) catchup-threshold)\n            ;; Phase 3: Final cutover (brief pause)\n            (atomic-cutover source-vault target-host changes)\n            (loop (sync-changes changes target-host)))))))")))
  (section
    "Object Transfer"
    (subsection
      "Export Format"
      (code scheme ";; Sealed archive format (RFC-018)\n(define (export-object hash)\n  `(vault-object\n    (hash ,hash)\n    (content ,(cas-get hash))\n    (soup-entry ,(soup-get hash))\n    (references ,(object-references hash))\n    (signatures ,(object-signatures hash))))\n\n(define (export-batch hashes)\n  (let ((objects (map export-object hashes)))\n    (seal-archive objects\n      compression: 'zstd\n      encryption: target-vault-key)))"))
    (subsection
      "Transfer Protocol"
      (code scheme "(define (transfer-object obj source target)\n  \"Transfer single object with verification\"\n  (let* ((hash (object-hash obj))\n         (data (export-object hash)))\n    ;; Send to target\n    (vault-send target data)\n    ;; Get acknowledgment with hash\n    (let ((ack (vault-receive target)))\n      (unless (equal? (ack-hash ack) hash)\n        (error \"Transfer verification failed\" hash))\n      (audit-append action: `(object-transferred ,hash)\n                    source: source\n                    target: target))))"))
    (subsection
      "Streaming Transfer"
      (code scheme "(define (stream-transfer source target)\n  \"Stream objects for efficient bulk transfer\"\n  (let ((stream (open-transfer-stream source target)))\n    (for-each (lambda (hash)\n                (let ((obj (export-object hash)))\n                  (stream-write stream obj)\n                  (when (stream-buffer-full? stream)\n                    (stream-flush stream))))\n              (vault-all-hashes source))\n    (stream-close stream)))")))
  (section
    "Metadata Migration"
    (subsection
      "Soup Entries"
      (code scheme "(define (migrate-soup-entry hash source target)\n  \"Migrate soup metadata for object\"\n  (let ((entry (soup-get source hash)))\n    (when entry\n      (soup-put target hash entry)\n      ;; Verify\n      (unless (equal? (soup-get target hash) entry)\n        (error \"Soup entry migration failed\" hash)))))"))
    (subsection
      "Index Migration"
      (code scheme "(define (migrate-indexes source target)\n  \"Rebuild indexes on target\"\n  ;; Option 1: Export and import index data\n  (let ((index-data (export-indexes source)))\n    (import-indexes target index-data))\n\n  ;; Option 2: Rebuild from soup (slower but guaranteed correct)\n  (rebuild-indexes target))"))
    (subsection
      "Audit Trail"
      (code scheme "(define (migrate-audit source target)\n  \"Migrate audit trail (critical for provenance)\"\n  (let ((audit-entries (audit-export source)))\n    ;; Audit entries are append-only, transfer in order\n    (for-each (lambda (entry)\n                (audit-import target entry))\n              audit-entries)\n    ;; Add migration event to both\n    (let ((migration-entry\n           `(migration-audit\n             (source ,source)\n             (target ,target)\n             (entries ,(length audit-entries))\n             (timestamp ,(current-time)))))\n      (audit-append source migration-entry)\n      (audit-append target migration-entry))))")))
  (section
    "Capability Migration"
    (subsection
      "Certificate Transfer"
      (code scheme "(define (migrate-capabilities source target)\n  \"Migrate SPKI certificates\"\n  (let ((certs (soup-query source type: 'certificate)))\n    (for-each (lambda (cert)\n                ;; Certificates are content-addressed, transfer directly\n                (let ((hash (cert-hash cert)))\n                  (migrate-object hash source target)))\n              certs)))"))
    (subsection
      "Key Migration"
      (code scheme ";; Private keys require special handling\n(define (migrate-vault-keys source target ceremony-witnesses)\n  \"Migrate vault keys via key ceremony\"\n  ;; Never transfer private keys directly!\n  ;; Use threshold re-sharing or key ceremony\n  (let* ((old-shares (gather-key-shares source))\n         (new-key (generate-new-key target))\n         (transition-cert (create-key-transition-cert\n                           old-key: (vault-public-key source)\n                           new-key: new-key\n                           witnesses: ceremony-witnesses)))\n    ;; Sign transition with old key\n    (sign-transition old-shares transition-cert)\n    ;; Record in both vaults\n    (audit-append source action: (key-transition ,transition-cert))\n    (audit-append target action: (key-transition ,transition-cert))))"))
    (subsection
      "Delegation Chain Continuity"
      (code scheme "(define (verify-delegation-chains target)\n  \"Verify all delegation chains remain valid after migration\"\n  (let ((certs (soup-query target type: 'certificate)))\n    (for-each (lambda (cert)\n                (let ((chain (build-chain cert)))\n                  (unless (valid-chain? chain)\n                    (warn \"Broken delegation chain\" cert))))\n              certs)))")))
  (section
    "Verification"
    (subsection
      "Content Verification"
      (code scheme "(define (verify-migration source target)\n  \"Verify all content transferred correctly\"\n  (let ((source-hashes (vault-all-hashes source))\n        (target-hashes (vault-all-hashes target)))\n\n    ;; Check completeness\n    (let ((missing (set-difference source-hashes target-hashes)))\n      (unless (null? missing)\n        (error \"Missing objects after migration\" missing)))\n\n    ;; Check integrity (sample verification for large vaults)\n    (let ((sample (random-sample source-hashes 1000)))\n      (for-each (lambda (hash)\n                  (unless (equal? (cas-get source hash)\n                                  (cas-get target hash))\n                    (error \"Content mismatch\" hash)))\n                sample))\n\n    ;; Check soup metadata\n    (for-each (lambda (hash)\n                (unless (equal? (soup-get source hash)\n                                (soup-get target hash))\n                  (error \"Soup mismatch\" hash)))\n              (random-sample source-hashes 1000))))"))
    (subsection
      "Merkle Verification"
      (code scheme "(define (merkle-verify-migration source target)\n  \"Verify migration via Merkle root comparison\"\n  (let ((source-root (vault-merkle-root source))\n        (target-root (vault-merkle-root target)))\n    (unless (equal? source-root target-root)\n      ;; Find divergence\n      (let ((divergence (find-merkle-divergence source target)))\n        (error \"Merkle verification failed\" divergence)))))"))
    (subsection
      "Audit Verification"
      (code scheme "(define (verify-audit-continuity source target)\n  \"Verify audit trail continuity\"\n  (let ((source-audit (audit-export source))\n        (target-audit (audit-export target)))\n    ;; Target should have all source entries plus migration events\n    (unless (subsequence? source-audit target-audit)\n      (error \"Audit trail discontinuity\"))))")))
  (section
    "Cutover"
    (subsection
      "Atomic Cutover"
      (code scheme "(define (atomic-cutover source target migration-id)\n  \"Atomically switch from source to target\"\n  ;; Phase 1: Quiesce source\n  (vault-readonly! source)\n\n  ;; Phase 2: Final sync\n  (let ((final-changes (changes-since source (last-sync-point))))\n    (sync-changes final-changes target))\n\n  ;; Phase 3: Verify\n  (verify-migration source target)\n\n  ;; Phase 4: Update DNS/routing\n  (update-vault-routing source target)\n\n  ;; Phase 5: Activate target\n  (vault-activate! target)\n\n  ;; Phase 6: Record completion\n  (audit-append target action: `(migration-complete ,migration-id)))"))
    (subsection
      "Rollback"
      (code scheme "(define (migration-rollback migration-id)\n  \"Rollback failed migration\"\n  (let ((migration (get-migration migration-id)))\n    (case (migration-phase migration)\n      ((transfer)\n       ;; Just abandon target\n       (vault-delete! (migration-target migration)))\n      ((cutover)\n       ;; Restore routing to source\n       (update-vault-routing (migration-target migration)\n                             (migration-source migration))\n       (vault-readonly! (migration-target migration))\n       (vault-activate! (migration-source migration)))\n      ((complete)\n       (error \"Cannot rollback completed migration\")))))")))
  (section
    "Incremental Migration"
    (subsection
      "Checkpoint System"
      (code scheme "(define (migration-checkpoint migration-id progress)\n  \"Save migration progress for resumption\"\n  (let ((checkpoint\n         `(checkpoint\n           (migration-id ,migration-id)\n           (timestamp ,(current-time))\n           (transferred ,(progress-transferred progress))\n           (remaining ,(progress-remaining progress))\n           (last-hash ,(progress-last-hash progress)))))\n    (cas-put (serialize checkpoint))))\n\n(define (resume-migration migration-id)\n  \"Resume interrupted migration\"\n  (let ((checkpoint (latest-checkpoint migration-id)))\n    (if checkpoint\n        (continue-from-checkpoint checkpoint)\n        (error \"No checkpoint found\" migration-id))))"))
    (subsection
      "Change Tracking"
      (code scheme ";; Track changes during migration\n(define (changes-since vault timestamp)\n  \"Get all changes since timestamp\"\n  (soup-query vault\n              modified: (> timestamp)\n              order-by: '((modified asc))))\n\n(define (sync-changes changes target)\n  \"Apply changes to target\"\n  (for-each (lambda (change)\n              (case (change-type change)\n                ((create modify)\n                 (migrate-object (change-hash change) target))\n                ((delete)\n                 (cas-delete target (change-hash change)))))\n            changes))")))
  (section
    "Storage Backend Migration"
    (subsection
      "Backend Abstraction"
      (code scheme ";; Migrate between storage backends\n(define (backend-migration vault old-backend new-backend)\n  \"Migrate vault to different storage backend\"\n  (for-each (lambda (hash)\n              (let ((data (backend-get old-backend hash)))\n                (backend-put new-backend hash data)\n                (verify-backend-transfer hash old-backend new-backend)))\n            (backend-all-hashes old-backend)))\n\n;; Example: S3 to local filesystem\n(define (s3-to-local vault bucket path)\n  (backend-migration vault\n                     (make-s3-backend bucket)\n                     (make-fs-backend path)))"))
    (subsection
      "Format Conversion"
      (code scheme ";; Migrate between storage formats\n(define (format-migration vault old-format new-format)\n  \"Convert storage format during migration\"\n  (for-each (lambda (hash)\n              (let* ((old-data (read-format old-format hash))\n                     (new-data (convert-format old-data new-format)))\n                (write-format new-format hash new-data)))\n            (vault-all-hashes vault)))")))
  (section
    "Federation Migration"
    (subsection
      "Vault Federation Changes"
      (code scheme "(define (federation-migrate vault old-federation new-federation)\n  \"Migrate vault between federations\"\n  ;; Leave old federation\n  (federation-leave old-federation vault)\n\n  ;; Update vault metadata\n  (vault-set-federation! vault new-federation)\n\n  ;; Join new federation\n  (federation-join new-federation vault)\n\n  ;; Announce to peers\n  (federation-announce new-federation vault))"))
    (subsection
      "Cross-Federation Transfer"
      (code scheme "(define (cross-federation-transfer hash source-fed target-fed)\n  \"Transfer object between federations\"\n  (let* ((source-vault (federation-locate source-fed hash))\n         (target-vault (federation-select target-fed))\n         (obj (vault-get source-vault hash)))\n    (vault-put target-vault obj)\n    (federation-announce target-fed hash target-vault)))")))
  (section
    "Security Considerations"
    (subsection
      "Migration Authorization"
      (code scheme ";; Migration requires appropriate capability\n(spki-cert\n  (issuer vault-admin)\n  (subject migration-operator)\n  (capability\n    (action migrate)\n    (object vault-id))\n  (validity (not-after \"2026-02-01\")))\n\n(define (authorized-migration? operator source target)\n  (and (has-capability? operator 'migrate source)\n       (has-capability? operator 'write target)))"))
    (subsection
      "Encryption in Transit"
      (code scheme "(define (secure-transfer source target)\n  \"Transfer with encryption\"\n  (let ((session-key (establish-session-key source target)))\n    (for-each (lambda (hash)\n                (let* ((data (cas-get source hash))\n                       (encrypted (encrypt session-key data)))\n                  (send-encrypted target encrypted)))\n              (vault-all-hashes source))))"))
    (subsection
      "Migration Audit"
      (code scheme ";; All migrations are fully audited\n(define (audited-migration source target)\n  (let ((migration-id (generate-migration-id)))\n    (audit-append action: 'migration-authorized\n                  migration-id: migration-id\n                  operator: (current-principal)\n                  source: source\n                  target: target)\n    ;; ... perform migration ...\n    (audit-append action: 'migration-complete\n                  migration-id: migration-id\n                  objects: (count-migrated)\n                  verification: (verification-result))))")))
  (section
    "References"
    (p "1. [Live Migration of Virtual Machines](https://dl.acm.org/doi/10.1145/1095810.1095816) - Clark et al. 2. [RFC-018: Sealed Archive Format](rfc-018-sealed-archive.html) 3. [RFC-022: Key Ceremony Protocol](rfc-022-key-ceremony.html) 4. [RFC-024: Network Protocol](rfc-024-network-protocol.html)"))
  (section
    "Changelog"
    (list
      (item "2026-01-07")
      (item "Initial draft"))))

