;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 26)
  (title "Garbage Collection")
  (section
    "Abstract"
    (p "This RFC specifies garbage collection for the Library of Cyberspace: how vaults identify and reclaim storage from unreferenced objects while preserving pinned content, respecting tombstones, and maintaining audit trails. Content-addressed storage requires careful GC to avoid data loss.")
    (p "The Library of Cyberspace is an archival system. The default is preservation, not collection. Objects evaporate only with explicit consent."))
  (section
    "Philosophy: The Soup Preserves"
    (p "The soup is not a runtime heap. It is a library.")
    (p "In runtime garbage collection, the goal is to reclaim memory quickly. Young objects die young. Old objects survive. Collect aggressively.")
    (p "In archival garbage collection, the opposite holds:")
    (list
      (item "Old objects are precious")
      (item "They have survived, been referenced, replicated")
      (item "Young objects are suspect")
      (item "They may be transient, failed, or temporary")
      (item "Deletion is violence")
      (item "Once collected, an object is gone from this vault forever")
      (item "Preservation is the default")
      (item "When in doubt, keep it"))
    (p "The Library of Alexandria burned once. We will not let it burn again."))
  (section
    "Motivation"
    (p "Content-addressed storage accumulates objects forever unless actively pruned:")
    (list
      (item "Orphaned objects")
      (item "No longer referenced by any root")
      (item "Superseded versions")
      (item "Old versions after updates")
      (item "Failed uploads")
      (item "Partial or abandoned writes")
      (item "Temporary objects")
      (item "Intermediate computation results"))
    (p "But deletion is dangerous:")
    (list
      (item "Hash as capability")
      (item "Someone may hold the hash")
      (item "Lazy replication")
      (item "Remote vaults may need it later")
      (item "Audit requirements")
      (item "May need historical data")
      (item "Resurrection")
      (item "Deleted objects may be re-added"))
    (p "GC must be conservative, consensual, and auditable.")
    (p "The default is: never collect. Collection requires explicit action."))
  (section
    "Object Lifecycle"
    (subsection
      "States"
      (code "                    ┌─────────┐\n          write     │         │\n        ─────────►  │  LIVE   │\n                    │         │\n                    └────┬────┘\n                         │\n              ┌──────────┼──────────┐\n              │          │          │\n              ▼          ▼          ▼\n         ┌────────┐ ┌────────┐ ┌────────┐\n         │PINNED  │ │TOMBSTONE│ │ORPHANED│\n         └────────┘ └────────┘ └───┬────┘\n                                   │\n                                   │ GC\n                                   ▼\n                              ┌────────┐\n                              │COLLECTED│\n                              └────────┘"))
    (subsection
      "State Transitions"
      (code scheme "(define (object-state hash)\n  (cond\n    ((pinned? hash) 'pinned)\n    ((tombstoned? hash) 'tombstone)\n    ((referenced? hash) 'live)\n    (else 'orphaned)))\n\n(define (can-collect? hash)\n  (and (eq? (object-state hash) 'orphaned)\n       (not (in-grace-period? hash))\n       (not (pending-replication? hash))))")))
  (section
    "Reference Counting"
    (subsection
      "Direct References"
      (code scheme ";; Track incoming references\n(define ref-counts (make-hash-table))\n\n(define (add-reference from-hash to-hash)\n  (let ((count (hash-table-ref ref-counts to-hash 0)))\n    (hash-table-set! ref-counts to-hash (+ count 1))\n    (audit-append action: (add-ref ,from-hash ,to-hash))))\n\n(define (remove-reference from-hash to-hash)\n  (let ((count (hash-table-ref ref-counts to-hash 0)))\n    (hash-table-set! ref-counts to-hash (max 0 (- count 1)))\n    (audit-append action: (remove-ref ,from-hash ,to-hash))))\n\n(define (reference-count hash)\n  (hash-table-ref ref-counts hash 0))"))
    (subsection
      "Root References"
      (code scheme ";; GC roots - objects that are always reachable\n(define gc-roots (make-hash-set))\n\n(define (add-gc-root hash reason)\n  (hash-set-add! gc-roots hash)\n  (audit-append action: (add-root ,hash ,reason)))\n\n(define (remove-gc-root hash)\n  (hash-set-remove! gc-roots hash)\n  (audit-append action: (remove-root ,hash)))\n\n(define (gc-root? hash)\n  (hash-set-member? gc-roots hash))"))
    (subsection
      "Implicit Roots"
      (code scheme ";; Some objects are implicitly rooted\n(define (implicit-root? hash)\n  (or (pinned? hash)\n      (soup-object-type? hash 'certificate)  ; Certs are roots\n      (soup-object-type? hash 'audit-entry)  ; Audit is sacred\n      (recent-write? hash)))                 ; Grace period"))
    (subsection
      "Cycle Detection"
      (p "Reference counting alone cannot detect cycles (A→B→C→A). The soup uses mark-and-sweep as the authoritative reachability test, with reference counts as a fast path for common cases.")
      (code scheme ";; Reference counting is advisory, not authoritative\n(define (fast-unreachable? hash)\n  \"Quick check - zero refs MIGHT mean unreachable\"\n  (and (zero? (reference-count hash))\n       (not (gc-root? hash))\n       (not (implicit-root? hash))))\n\n;; Mark-and-sweep is authoritative\n(define (truly-unreachable? hash marked-set)\n  \"Authoritative check - not in marked set means unreachable\"\n  (not (hash-set-member? marked-set hash)))\n\n;; Cycle detection via mark-and-sweep\n(define (detect-cycles)\n  \"Find reference cycles (objects that reference each other but are unreachable)\"\n  (let* ((marked (mark-reachable))\n         (all-hashes (all-object-hashes))\n         (unmarked (filter (lambda (h) (not (hash-set-member? marked h))) all-hashes))\n         (with-refs (filter (lambda (h) (> (reference-count h) 0)) unmarked)))\n    ;; These have refs but are unreachable - they're in cycles\n    with-refs))")
      (p "In archival mode, cycles are preserved (they may be intentional - e.g., bidirectional links). Only explicit evaporation removes them.")))
  (section
    "Mark and Sweep"
    (subsection
      "Tricolor Abstraction"
      (p "The naive recursive mark algorithm risks stack overflow on deep object graphs. The tricolor abstraction provides:")
      (p "1. White: Unvisited, potentially garbage 2. Gray: Visited but references not yet scanned 3. Black: Visited and all references scanned")
      (code scheme ";; Tricolor sets - explicit worklist avoids stack overflow\n(define white-set (make-hash-set))  ; Candidates for collection\n(define gray-set (make-hash-set))   ; Work queue\n(define black-set (make-hash-set))  ; Proven reachable\n\n(define (tricolor-init)\n  \"Initialize: all objects are white\"\n  (hash-set-clear! white-set)\n  (hash-set-clear! gray-set)\n  (hash-set-clear! black-set)\n  (for-each (lambda (h) (hash-set-add! white-set h))\n            (all-object-hashes)))\n\n(define (shade-gray! hash)\n  \"Move object from white to gray (discovered)\"\n  (when (hash-set-member? white-set hash)\n    (hash-set-remove! white-set hash)\n    (hash-set-add! gray-set hash)))\n\n(define (shade-black! hash)\n  \"Move object from gray to black (fully scanned)\"\n  (hash-set-remove! gray-set hash)\n  (hash-set-add! black-set hash))"))
    (subsection
      "Mark Phase (Worklist Algorithm)"
      (code scheme "(define (mark-reachable)\n  \"Mark all objects reachable from roots using worklist\"\n  (tricolor-init)\n\n  ;; Shade roots gray\n  (for-each shade-gray! (hash-set->list gc-roots))\n  (for-each (lambda (hash)\n              (when (implicit-root? hash)\n                (shade-gray! hash)))\n            (all-object-hashes))\n\n  ;; Process gray objects until none remain\n  (let loop ()\n    (unless (hash-set-empty? gray-set)\n      (let ((current (hash-set-pop! gray-set)))\n        ;; Shade all white references gray\n        (for-each shade-gray! (object-references current))\n        ;; Current is now fully scanned\n        (shade-black! current)\n        (loop))))\n\n  black-set)  ; Return reachable set"))
    (subsection
      "Incremental Tricolor Marking"
      (p "For large soups, mark in batches to avoid long pauses:")
      (code scheme "(define mark-batch-size 1000)  ; Objects per batch\n\n(define (mark-incremental)\n  \"Mark in batches, yielding between batches\"\n  (let ((batch 0))\n    (let loop ()\n      (unless (or (hash-set-empty? gray-set)\n                  (>= batch mark-batch-size))\n        (let ((current (hash-set-pop! gray-set)))\n          (for-each shade-gray! (object-references current))\n          (shade-black! current)\n          (set! batch (+ batch 1))\n          (loop))))\n    ;; Return whether more work remains\n    (not (hash-set-empty? gray-set))))\n\n;; Usage: call repeatedly until returns #f\n(define (incremental-gc-step)\n  (if (mark-incremental)\n      'more-work\n      (begin\n        (sweep-white)\n        'complete)))"))
    (subsection
      "Concurrent Write Barrier"
      (p "For concurrent GC, mutations must maintain the tricolor invariant: a black object cannot point to a white object.")
      (code scheme ";; Write barrier for concurrent GC\n(define (cas-put-concurrent data)\n  \"Store with write barrier for concurrent GC\"\n  (let ((hash (cas-put data)))\n    ;; If GC is running and we create new references\n    (when gc-running?\n      ;; Shade new object gray (conservative)\n      (shade-gray! hash)\n      ;; Re-shade any black object referencing new object\n      (for-each (lambda (referencer)\n                  (when (hash-set-member? black-set referencer)\n                    ;; Demote to gray - needs re-scanning\n                    (hash-set-remove! black-set referencer)\n                    (hash-set-add! gray-set referencer)))\n                (incoming-references hash)))\n    hash))\n\n;; Snapshot-at-the-beginning (SATB) barrier\n(define (reference-update! from-hash old-ref new-ref)\n  \"SATB write barrier: preserve old reference for marking\"\n  (when (and gc-running? old-ref)\n    ;; Keep old reference alive through this GC cycle\n    (shade-gray! old-ref))\n  (update-reference! from-hash new-ref))"))
    (subsection
      "Original Mark (Preserved for Reference)"
      (code scheme ";; Simple recursive version (for small object graphs only)\n(define (mark-reachable/simple)\n  \"Mark all objects reachable from roots (recursive, can stack overflow)\"\n  (let ((marked (make-hash-set)))\n    (define (mark hash)\n      (unless (hash-set-member? marked hash)\n        (hash-set-add! marked hash)\n        (for-each mark (object-references hash))))\n\n    ;; Mark from explicit roots\n    (for-each mark (hash-set->list gc-roots))\n\n    ;; Mark from implicit roots\n    (for-each (lambda (hash)\n                (when (implicit-root? hash)\n                  (mark hash)))\n              (all-object-hashes))\n\n    marked))"))
    (subsection
      "Sweep Phase"
      (code scheme "(define (sweep marked)\n  \"Collect unmarked objects\"\n  (let ((collected '()))\n    (for-each\n      (lambda (hash)\n        (unless (hash-set-member? marked hash)\n          (when (can-collect? hash)\n            (set! collected (cons hash collected))\n            (collect-object! hash))))\n      (all-object-hashes))\n    collected))\n\n(define (collect-object! hash)\n  \"Remove object from storage\"\n  (let ((obj (cas-get hash)))\n    (audit-append\n      action: 'gc-collect\n      hash: hash\n      size: (object-size obj)\n      age: (object-age obj))\n    (cas-delete! hash)))"))
    (subsection
      "Full GC"
      (code scheme "(define (gc-full)\n  \"Perform full garbage collection\"\n  (let ((start (current-time)))\n    (audit-append action: 'gc-start type: 'full)\n\n    (let* ((marked (mark-reachable))\n           (collected (sweep marked)))\n\n      (audit-append\n        action: 'gc-complete\n        type: 'full\n        duration: (- (current-time) start)\n        marked: (hash-set-size marked)\n        collected: (length collected)\n        bytes-freed: (sum (map object-size collected)))\n\n      collected)))")))
  (section
    "Incremental GC"
    (subsection
      "Archival Generational Collection"
      (p "Traditional generational GC collects young objects first (they die young). Archival GC inverts this: old objects are precious.")
      (code scheme ";; Archival generations - age increases protection\n(define generations\n  '((ephemeral . 3600)     ; < 1 hour: temporary, collect freely\n    (young . 86400)        ; < 1 day: probably transient\n    (maturing . 604800)    ; < 1 week: gaining stability\n    (stable . 2592000)     ; < 30 days: likely permanent\n    (archival . #f)))      ; >= 30 days: NEVER collect automatically\n\n(define (object-generation hash)\n  (let ((age (object-age hash)))\n    (cond\n      ((< age 3600) 'ephemeral)\n      ((< age 86400) 'young)\n      ((< age 604800) 'maturing)\n      ((< age 2592000) 'stable)\n      (else 'archival))))\n\n;; Collection eligibility by generation\n(define (generation-collectible? gen)\n  (case gen\n    ((ephemeral) #t)       ; Freely collectible\n    ((young) #t)           ; Collectible with grace period\n    ((maturing) 'warning)  ; Requires explicit approval\n    ((stable) 'quorum)     ; Requires federation quorum\n    ((archival) #f)))      ; NEVER collect automatically\n\n(define (gc-generation gen)\n  \"Collect only specified generation (archival only via evaporation)\"\n  (when (eq? gen 'archival)\n    (error \"Archival objects require evaporation certificate\"))\n  (let ((candidates (filter (lambda (h)\n                              (eq? (object-generation h) gen))\n                            (all-object-hashes))))\n    (gc-candidates candidates)))"))
    (subsection
      "Write Barrier"
      (code scheme ";; Track modified objects for incremental GC\n(define modified-set (make-hash-set))\n\n(define (cas-put-with-barrier data)\n  (let ((hash (cas-put data)))\n    (hash-set-add! modified-set hash)\n    hash))\n\n(define (gc-incremental)\n  \"Collect recently modified objects if orphaned\"\n  (let ((candidates (hash-set->list modified-set)))\n    (hash-set-clear! modified-set)\n    (gc-candidates candidates)))"))
    (subsection
      "Concurrent GC"
      (code scheme ";; GC runs concurrently with mutations\n(define gc-lock (make-mutex))\n(define gc-running? #f)\n\n(define (gc-concurrent)\n  \"Run GC without stopping the world\"\n  (when (mutex-try-lock! gc-lock)\n    (set! gc-running? #t)\n    (let ((snapshot (snapshot-roots)))\n      ;; Mark phase uses snapshot\n      (let ((marked (mark-from-snapshot snapshot)))\n        ;; Sweep only clearly dead objects\n        (sweep-conservative marked)))\n    (set! gc-running? #f)\n    (mutex-unlock! gc-lock)))")))
  (section
    "Pinning"
    (subsection
      "Pin Management"
      (code scheme "(define pins (make-hash-table))\n\n(define (pin! hash reason #!key duration)\n  \"Protect object from GC\"\n  (hash-table-set! pins hash\n    ((reason . ,reason)\n      (pinned-at . ,(current-time))\n      (expires . ,(and duration (+ (current-time) duration)))\n      (pinned-by . ,(current-principal))))\n  (audit-append action: (pin ,hash ,reason)))\n\n(define (unpin! hash)\n  \"Allow object to be collected\"\n  (hash-table-delete! pins hash)\n  (audit-append action: `(unpin ,hash)))\n\n(define (pinned? hash)\n  (let ((pin (hash-table-ref pins hash #f)))\n    (and pin\n         (or (not (assoc-ref pin 'expires))\n             (> (assoc-ref pin 'expires) (current-time))))))"))
    (subsection
      "Transitive Pinning"
      (code scheme "(define (pin-tree! root-hash reason)\n  \"Pin object and all objects it references\"\n  (let ((visited (make-hash-set)))\n    (define (pin-recursive hash)\n      (unless (hash-set-member? visited hash)\n        (hash-set-add! visited hash)\n        (pin! hash reason)\n        (for-each pin-recursive (object-references hash))))\n    (pin-recursive root-hash)))")))
  (section
    "Tombstones"
    (subsection
      "Tombstone Handling"
      (code scheme ";; Tombstones are never collected\n(define (tombstoned? hash)\n  (let ((obj (soup-get hash)))\n    (and obj (eq? (soup-object-type obj) 'tombstone))))\n\n;; Tombstones prevent resurrection\n(define (cas-put-checked data)\n  (let ((hash (content-hash data)))\n    (when (tombstoned? hash)\n      (error \"Cannot resurrect tombstoned object\" hash))\n    (cas-put data)))"))
    (subsection
      "Tombstone Expiry"
      (code scheme ";; Optional: tombstones can expire\n(define (tombstone-expired? hash)\n  (let ((tomb (soup-get hash)))\n    (and tomb\n         (assoc-ref (soup-object-metadata tomb) 'expires)\n         (< (assoc-ref (soup-object-metadata tomb) 'expires)\n            (current-time)))))\n\n(define (gc-expired-tombstones)\n  \"Remove expired tombstones\"\n  (for-each\n    (lambda (hash)\n      (when (and (tombstoned? hash) (tombstone-expired? hash))\n        (collect-object! hash)))\n    (all-object-hashes)))")))
  (section
    "Grace Periods"
    (subsection
      "Write Grace Period"
      (code scheme ";; Recently written objects are protected\n(define write-grace-period 86400)  ; 24 hours\n\n(define (recent-write? hash)\n  (let ((obj (soup-get hash)))\n    (and obj\n         (< (- (current-time) (soup-object-created obj))\n            write-grace-period))))"))
    (subsection
      "Replication Grace Period"
      (code scheme ";; Objects pending replication are protected\n(define pending-replication (make-hash-set))\n\n(define (mark-pending-replication hash vaults)\n  (hash-set-add! pending-replication hash)\n  (audit-append action: `(pending-replication ,hash ,vaults)))\n\n(define (clear-pending-replication hash)\n  (hash-set-remove! pending-replication hash))\n\n(define (pending-replication? hash)\n  (hash-set-member? pending-replication hash))")))
  (section
    "Evaporation (Archival Collection)"
    (p "Objects don't get \"garbage collected\" in an archive. They evaporate - and only with explicit, signed, multi-party consent.")
    (subsection
      "Evaporation Certificate"
      (code scheme ";; An evaporation certificate authorizes deletion\n(define-record-type evaporation-certificate\n  (make-evaporation-cert hash reason signers timestamp)\n  evaporation-cert?\n  (hash evap-hash)           ; Object to evaporate\n  (reason evap-reason)       ; Why (legal, storage, corruption, etc.)\n  (signers evap-signers)     ; List of (principal . signature)\n  (timestamp evap-timestamp))\n\n;; Reasons for evaporation (enumerated, auditable)\n(define evaporation-reasons\n  '(legal-requirement        ; Court order, DMCA, etc.\n    storage-emergency        ; Vault at capacity\n    data-corruption          ; Object verified corrupt\n    owner-request            ; Content owner requests removal\n    federation-consensus))   ; Quorum agrees to remove\n\n(define (create-evaporation-cert hash reason)\n  \"Create unsigned evaporation certificate\"\n  (make-evaporation-cert\n    hash\n    reason\n    '()  ; No signatures yet\n    (current-time)))\n\n(define (sign-evaporation-cert cert private-key)\n  \"Add signature to evaporation certificate\"\n  (let* ((principal (key->principal private-key))\n         (sig (sign-data (evap-hash cert) private-key)))\n    (make-evaporation-cert\n      (evap-hash cert)\n      (evap-reason cert)\n      (cons (cons principal sig) (evap-signers cert))\n      (evap-timestamp cert))))"))
    (subsection
      "Quorum Requirement"
      (code scheme ";; Evaporation requires M-of-N signatures from federation\n(define evaporation-quorum\n  '((ephemeral . 1)     ; Single vault can evaporate\n    (young . 1)         ; Single vault can evaporate\n    (maturing . 2)      ; Two vaults must agree\n    (stable . 3)        ; Three vaults must agree\n    (archival . #f)))   ; Requires special process (see below)\n\n(define (evaporation-quorum-met? cert generation)\n  (let ((required (assoc-ref evaporation-quorum generation)))\n    (cond\n      ((not required) #f)  ; Archival: never automatic\n      (else (>= (length (evap-signers cert)) required)))))\n\n(define (evaporate! hash cert)\n  \"Evaporate object with valid certificate\"\n  (let ((gen (object-generation hash)))\n    (unless (evaporation-quorum-met? cert gen)\n      (error \"Evaporation quorum not met\"\n             `(generation ,gen required ,(assoc-ref evaporation-quorum gen))))\n\n    ;; Archival objects require special handling\n    (when (eq? gen 'archival)\n      (unless (archival-evaporation-authorized? cert)\n        (error \"Archival evaporation requires governance approval\")))\n\n    ;; Log everything before deletion\n    (audit-append\n      action: 'evaporate\n      hash: hash\n      generation: gen\n      certificate: cert\n      reason: (evap-reason cert)\n      signers: (map car (evap-signers cert)))\n\n    ;; Finally, delete\n    (cas-delete! hash)))"))
    (subsection
      "Archival Object Evaporation"
      (p "Archival objects (>30 days) receive maximum protection. They can only evaporate via:")
      (p "1. Legal requirement - With proof of legal order 2. Data corruption - With cryptographic proof of corruption 3. Governance vote - Per RFC-036 quorum protocol")
      (code scheme "(define (archival-evaporation-authorized? cert)\n  \"Check if archival evaporation is properly authorized\"\n  (case (evap-reason cert)\n    ((legal-requirement)\n     ;; Must include legal order reference\n     (and (evap-legal-order cert)\n          (verify-legal-order (evap-legal-order cert))))\n\n    ((data-corruption)\n     ;; Must include corruption proof\n     (and (evap-corruption-proof cert)\n          (verify-corruption (evap-hash cert) (evap-corruption-proof cert))))\n\n    ((federation-consensus)\n     ;; Must have governance quorum (RFC-036)\n     (governance-quorum-met? cert))\n\n    (else #f)))  ; No other reasons valid for archival")))
  (section
    "Distributed GC"
    (subsection
      "Coordinated Collection"
      (code scheme ";; Multi-vault GC requires coordination\n(define (distributed-gc vaults)\n  \"Coordinate GC across vault federation\"\n  ;; Phase 1: Gather root sets\n  (let ((root-sets (map vault-roots vaults)))\n    ;; Phase 2: Compute global reachability\n    (let ((global-marked (union-all root-sets)))\n      ;; Phase 3: Propose evaporation (no unilateral deletion)\n      (for-each (lambda (vault)\n                  (vault-propose-evaporation vault global-marked))\n                vaults))))"))
    (subsection
      "Remote Reference Tracking"
      (code scheme ";; Track references from remote vaults\n(define remote-refs (make-hash-table))\n\n(define (add-remote-reference vault-id hash)\n  (let ((refs (hash-table-ref remote-refs hash '())))\n    (hash-table-set! remote-refs hash (cons vault-id refs))))\n\n(define (remove-remote-reference vault-id hash)\n  (let ((refs (hash-table-ref remote-refs hash '())))\n    (hash-table-set! remote-refs hash (delete vault-id refs))))\n\n(define (has-remote-references? hash)\n  (not (null? (hash-table-ref remote-refs hash '()))))"))
    (subsection
      "Lease-Based Collection"
      (code scheme ";; Remote vaults lease objects\n(define leases (make-hash-table))\n\n(define (grant-lease hash vault-id duration)\n  (let ((expires (+ (current-time) duration)))\n    (hash-table-set! leases hash\n      (cons (cons vault-id expires)\n            (hash-table-ref leases hash '())))))\n\n(define (lease-active? hash)\n  (let ((hash-leases (hash-table-ref leases hash '())))\n    (any (lambda (lease)\n           (> (cdr lease) (current-time)))\n         hash-leases)))")))
  (section
    "GC Scheduling"
    (subsection
      "Archival Defaults"
      (p "The soup defaults to never collect. GC only runs when explicitly enabled and only considers ephemeral/young generations automatically.")
      (code scheme ";; Archival GC mode\n(define gc-mode 'archival)  ; 'archival, 'conservative, or 'aggressive\n\n(define (gc-enabled?)\n  \"Check if automatic GC is enabled\"\n  (not (eq? gc-mode 'archival)))"))
    (subsection
      "Triggers"
      (code scheme ";; GC triggered only under pressure, and only for young generations\n(define (should-gc?)\n  (and (gc-enabled?)\n       (or (> (storage-usage-percent) 95)    ; Emergency only\n           (> (ephemeral-orphan-count) 1000)))) ; Too many ephemeral orphans\n\n(define (gc-schedule)\n  \"Run appropriate GC based on conditions and mode\"\n  (case gc-mode\n    ((archival)\n     ;; Never automatic - only explicit evaporation\n     (audit-append action: 'gc-skipped reason: 'archival-mode))\n\n    ((conservative)\n     ;; Only ephemeral objects\n     (cond\n       ((> (storage-usage-percent) 99)\n        (gc-generation 'ephemeral)\n        (gc-generation 'young))  ; Emergency: young too\n       ((> (storage-usage-percent) 95)\n        (gc-generation 'ephemeral))\n       (else\n        (audit-append action: 'gc-skipped reason: 'no-pressure))))\n\n    ((aggressive)\n     ;; Traditional GC (NOT RECOMMENDED for archives)\n     (cond\n       ((> (storage-usage-percent) 95)\n        (gc-full))\n       ((> (storage-usage-percent) 80)\n        (gc-generation 'young))\n       (else\n        (gc-incremental))))))"))
    (subsection
      "Background GC"
      (code scheme "(define gc-thread #f)\n\n(define (start-gc-daemon interval)\n  \"Start background GC daemon (archival mode: monitoring only)\"\n  (set! gc-thread\n    (thread-start!\n      (make-thread\n        (lambda ()\n          (let loop ()\n            (thread-sleep! interval)\n            ;; Always report status\n            (audit-append\n              action: 'gc-status\n              mode: gc-mode\n              storage-percent: (storage-usage-percent)\n              ephemeral-orphans: (ephemeral-orphan-count)\n              should-gc: (should-gc?))\n            ;; Only act if enabled\n            (when (should-gc?)\n              (gc-schedule))\n            (loop)))))))")))
  (section
    "Safety Mechanisms"
    (subsection
      "Dry Run"
      (code scheme "(define (gc-dry-run)\n  \"Report what would be collected without collecting\"\n  (let* ((marked (mark-reachable))\n         (would-collect (filter (lambda (h)\n                                  (not (hash-set-member? marked h)))\n                                (all-object-hashes))))\n    `((would-collect . ,(length would-collect))\n      (bytes . ,(sum (map object-size would-collect)))\n      (samples . ,(take would-collect 10)))))"))
    (subsection
      "Collection Log"
      (code scheme ";; Every collection is logged with recovery info\n(define (collect-with-log! hash)\n  (let ((obj (cas-get hash)))\n    ;; Log enough to reconstruct if needed\n    (audit-append\n      action: 'gc-collect\n      hash: hash\n      size: (object-size obj)\n      type: (soup-object-type obj)\n      references: (object-references hash)\n      metadata: (soup-object-metadata obj))\n    (cas-delete! hash)))"))
    (subsection
      "Recovery"
      (code scheme ";; Recover recently collected object from audit log\n(define (gc-recover hash)\n  \"Attempt to recover collected object\"\n  (let ((entry (find (lambda (e)\n                       (and (eq? (audit-action e) 'gc-collect)\n                            (equal? (audit-hash e) hash)))\n                     (recent-audit-entries))))\n    (if entry\n        (error \"Object collected, metadata preserved in audit\"\n               (audit-metadata entry))\n        (error \"Object not found in recent collections\"))))")))
  (section
    "Metrics"
    (subsection
      "GC Statistics"
      (code scheme "(define gc-stats\n  ((collections . 0)\n    (bytes-freed . 0)\n    (objects-freed . 0)\n    (total-time . 0)\n    (last-gc . #f)))\n\n(define (update-gc-stats collected duration)\n  (set! gc-stats\n    ((collections . ,(+ 1 (assoc-ref gc-stats 'collections)))\n      (bytes-freed . ,(+ (sum (map object-size collected))\n                         (assoc-ref gc-stats 'bytes-freed)))\n      (objects-freed . ,(+ (length collected)\n                           (assoc-ref gc-stats 'objects-freed)))\n      (total-time . ,(+ duration (assoc-ref gc-stats 'total-time)))\n      (last-gc . ,(current-time)))))"))
    (subsection
      "Monitoring"
      (code scheme ";; Expose GC metrics\n(define (gc-metrics)\n  `((storage-used . ,(storage-used))\n    (storage-total . ,(storage-total))\n    (object-count . ,(object-count))\n    (orphan-estimate . ,(orphan-estimate))\n    (pinned-count . ,(hash-table-size pins))\n    (gc-stats . ,gc-stats)))")))
  (section
    "Security Considerations"
    (subsection
      "GC as Side Channel"
      (code scheme ";; GC timing can leak information about object references\n;; Use constant-time operations where possible\n(define (constant-time-mark hash)\n  (let ((refs (object-references hash)))\n    ;; Always process same number of refs\n    (for-each mark (pad-list refs max-refs))))"))
    (subsection
      "Denial of Service"
      (code scheme ";; Prevent GC starvation attacks\n(define max-pins-per-principal 10000)\n\n(define (pin-with-limit! hash reason)\n  (let ((count (principal-pin-count (current-principal))))\n    (when (> count max-pins-per-principal)\n      (error \"Pin limit exceeded\"))\n    (pin! hash reason)))")))
  (section
    "Invariants"
    (code "G1. Preservation default\n    default-mode = archival → no-automatic-collection\n\nG2. Age increases protection\n    age(obj) > age(obj') → protection(obj) ≥ protection(obj')\n\nG3. Evaporation requires consent\n    evaporate(hash) requires signed-certificate(hash)\n\nG4. Quorum scales with age\n    generation = archival → quorum = governance-level\n\nG5. Archival objects are sacred\n    age > 30-days → no-automatic-evaporation\n\nG6. Audit trail preserved\n    evaporate(hash) → audit-append(hash, certificate, reason, signers)\n\nG7. Mark-and-sweep authoritative\n    truly-unreachable(hash) ↔ ¬member(hash, mark-reachable())\n\nG8. Cycles preserved\n    cycle(A, B, C) ∧ archival-mode → preserve(A, B, C)"))
  (section
    "References"
    (p "1. The Garbage Collection Handbook - Jones, Hosking, Moss 2. On-the-Fly Garbage Collection - Dijkstra et al. 3. RFC-020: Content-Addressed Storage 4. RFC-003: Cryptographic Audit Trail 5. RFC-036: Quorum Protocol with Homomorphic Voting 6. RFC-007: Threshold Signature Governance"))
  (section
    "Changelog"
    (list
      (item "2026-01-09")
      (item "Tricolor marking with worklist (eliminates stack overflow), incremental marking, SATB write barriers, concurrent GC support - 2026-01-09")
      (item "Archival GC improvements: evaporation certificates, quorum requirements, reversed generational policy, cycle detection, preservation-first defaults - 2026-01-07")
      (item "Initial draft"))))

