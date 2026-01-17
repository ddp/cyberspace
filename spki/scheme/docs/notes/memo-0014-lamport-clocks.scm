;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 14)
  (title "Lamport Logical Clocks")
  (section
    "Abstract"
    (p "This Memo specifies Lamport logical clocks for Cyberspace distributed ordering, providing a happened-before relation across federated vaults without synchronized physical clocks."))
  (section
    "Motivation"
    (p "Physical clocks lie:")
    (p "- Clock skew: Machines disagree on time - Clock drift: Skew grows over time - NTP failures: Synchronization breaks - Relativity: No global \"now\" anyway")
    (p "Lamport clocks provide:")
    (list
      (item "Logical ordering: a -> b means a happened before b")
      (item "No synchronization: No NTP, no GPS, no trusted time")
      (item "Causality tracking: If a caused b, then C(a) < C(b)")
      (item "Consistency: All nodes agree on partial order"))
    (p "Logical clocks capture what matters in distributed systems: which events could have influenced which others, regardless of wall-clock time.")
    (p "From Lamport (1978):")
    (blockquote "Time, Clocks, and the Ordering of Events in a Distributed System"))
  (section
    "Specification"
    (subsection
      "The Happened-Before Relation"
      (p "Definition: a → b (a happened before b) if:")
      (list
        (item "a and b are in same process and a comes before b, or")
        (item "a is sending a message and b is receiving it, or")
        (item "There exists c such that a -> c and c -> b (transitivity)")))
    (subsection
      "Lamport Clock Rules"
      (p "Each process P maintains counter C(P):")
      (code "Rule 1: Before each event, increment C(P)\n         C(P) := C(P) + 1\n\nRule 2: When sending message m, attach C(P)\n         send(m, C(P))\n\nRule 3: When receiving message (m, T), update clock\n         C(P) := max(C(P), T) + 1"))
    (subsection
      "Clock Condition"
      (p "If a → b then C(a) < C(b).")
      (p "Note: Converse is not guaranteed. C(a) < C(b) does not imply a → b.")))
  (section
    "Data Structures"
    (subsection
      "Logical Timestamp"
      (code scheme "(define-record-type <lamport-clock>\n  (make-lamport-clock counter node-id)\n  lamport-clock?\n  (counter clock-counter)\n  (node-id clock-node-id))"))
    (subsection
      "Timestamped Event"
      (code scheme "(define-record-type <timestamped-event>\n  (make-timestamped-event clock event)\n  timestamped-event?\n  (clock event-clock)\n  (event event-data))")))
  (section
    "Operations"
    (subsection
      "Increment (Local Event)"
      (code scheme "(define (clock-tick! clock)\n  \"Increment clock for local event\"\n  (set! (clock-counter clock)\n        (+ 1 (clock-counter clock)))\n  clock)"))
    (subsection
      "Send (Message Departure)"
      (code scheme "(define (clock-send clock message)\n  \"Attach timestamp to outgoing message\"\n  (clock-tick! clock)\n  (make-timestamped-message\n    (clock-counter clock)\n    (clock-node-id clock)\n    message))"))
    (subsection
      "Receive (Message Arrival)"
      (code scheme "(define (clock-receive! clock timestamped-message)\n  \"Update clock on message receipt\"\n  (let ((remote-time (message-timestamp timestamped-message)))\n    (set! (clock-counter clock)\n          (+ 1 (max (clock-counter clock) remote-time)))\n    (message-payload timestamped-message)))")))
  (section
    "Total Ordering"
    (p "Lamport clocks give partial order. For total order, break ties with node ID:")
    (code scheme "(define (lamport-compare a b)\n  \"Total order: compare by timestamp, then by node-id\"\n  (let ((ta (clock-counter (event-clock a)))\n        (tb (clock-counter (event-clock b)))\n        (na (clock-node-id (event-clock a)))\n        (nb (clock-node-id (event-clock b))))\n    (cond\n      ((< ta tb) -1)\n      ((> ta tb) 1)\n      ((string<? na nb) -1)\n      ((string>? na nb) 1)\n      (else 0))))"))
  (section
    "Application to Cyberspace"
    (subsection
      "Audit Trail Ordering"
      (code scheme "(audit-entry\n  (lamport-clock 1042 \"alice-vault\")\n  (timestamp \"2026-01-06T15:30:00Z\")  ; Physical (advisory)\n  (action (seal-commit \"abc123\"))\n  ...)")
      (p "Logical clock provides causal ordering even if physical clocks differ."))
    (subsection
      "Federation Message Ordering"
      (code scheme "(federation-message\n  (logical-time 573)\n  (from \"bob-vault\")\n  (type announcement)\n  (payload ...))")
      (p "Receivers update their clocks, ensuring consistent view of causality."))
    (subsection
      "Conflict Detection"
      (p "If events are concurrent (neither a → b nor b → a):")
      (code scheme "(define (concurrent? a b)\n  \"True if neither event happened before the other\"\n  (let ((ta (clock-counter (event-clock a)))\n        (tb (clock-counter (event-clock b))))\n    ;; If timestamps equal and different nodes, concurrent\n    ;; More sophisticated: use vector clocks for accurate detection\n    (and (= ta tb)\n         (not (equal? (clock-node-id (event-clock a))\n                      (clock-node-id (event-clock b)))))))")))
  (section
    "Vector Clocks (Extension)"
    (p "For precise concurrency detection, use vector clocks:")
    (code scheme "(define-record-type <vector-clock>\n  (make-vector-clock entries)\n  vector-clock?\n  (entries vc-entries))  ; Hash: node-id → counter\n\n;; a → b iff VC(a) < VC(b) (component-wise)\n;; a || b (concurrent) iff neither VC(a) < VC(b) nor VC(b) < VC(a)")
    (p "Trade-off: O(N) space vs O(1) for Lamport clocks."))
  (section
    "Integration Points"
    (subsection
      "With Audit Trail (Memo-003)"
      (code scheme "(audit-entry\n  (sequence 42)           ; Local sequence\n  (lamport-clock 1042)    ; Logical timestamp\n  (physical-time \"...\")   ; Advisory only\n  ...)"))
    (subsection
      "With Consensus (Memo-011)"
      (code scheme "(consensus-message\n  (sequence 573)          ; Consensus sequence\n  (lamport-clock 2891)    ; Causal context\n  ...)"))
    (subsection
      "With Replication (Memo-0002)"
      (code scheme "(seal-publish \"2.0.0\"\n  (logical-time 892)\n  ...)")))
  (section
    "Security Considerations"
    (subsection
      "Clock Manipulation"
      (p "A Byzantine node could: - Report artificially high clock values - Attempt to order events incorrectly")
      (p "Mitigations: - Clock values bounded by received values + margin - Signatures prevent retroactive tampering - Audit trails detect anomalies"))
    (subsection
      "Denial of Service"
      (p "Flooding with high-timestamped messages forces clock advancement.")
      (p "Mitigation: Rate limiting, reputation systems.")))
  (section
    "Implementation Notes"
    (subsection
      "Thread Safety"
      (p "Clock updates must be atomic:")
      (code scheme "(define (atomic-tick! clock)\n  (mutex-lock! clock-mutex)\n  (clock-tick! clock)\n  (mutex-unlock! clock-mutex))"))
    (subsection
      "Persistence"
      (p "Clock state survives restarts:")
      (code scheme "(define (save-clock clock path)\n  (with-output-to-file path\n    (lambda ()\n      (write `(lamport-clock\n                (counter ,(clock-counter clock))\n                (node-id ,(clock-node-id clock)))))))")))
  (section
    "References"
    (list
      (item "Lamport, L. (1978). Time, Clocks, and the Ordering of Events in a Distributed System.")
      (item "Fidge, C. J. (1988). Timestamps in Message-Passing Systems.")
      (item "Mattern, F. (1989). Virtual Time and Global States of Distributed Systems.")
      (item "Memo-003: Cryptographic Audit Trail")
      (item "Memo-010: Federation Protocol")))
  (section
    "Changelog"
    (list
      (item "2026-01-06")
      (item "Initial specification"))))

