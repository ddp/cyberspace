;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 48)
  (title "Access Control and Audit Co-Design")
  (section
    "Abstract"
    (p "This Memo establishes the principle that access control and auditing must be designed together, not separately. Every access control decision point produces three outputs: a decision, an effect, and a record. Audit policy is per-realm, with lean defaults."))
  (section
    "Motivation"
    (p "Security systems often treat auditing as an afterthought—bolted on after access control is designed. This leads to:")
    (list
      (item "Incomplete coverage: Some decisions are never logged")
      (item "Inconsistent records: Different formats at different points")
      (item "Performance surprises: Auditing added late without cost analysis")
      (item "Policy gaps: No framework for what to log when"))
    (p "The solution: co-design access control and auditing from the start."))
  (section
    "Design Principle"
    (p "Access control and auditing are co-designed, not bolted on.")
    (p "Every access control point has three outputs:")
    (code "┌─────────────────────────────────────┐\n│         Access Control Point        │\n├─────────────────────────────────────┤\n│ Input:  principal, action, context  │\n├─────────────────────────────────────┤\n│ Output: decision (grant | refuse)   │\n│         effect   (what happens)     │\n│         record   (audit entry)      │\n│                  ↓                  │\n│         policy → lean: print        │\n│                  paranoid: append   │\n└─────────────────────────────────────┘")
    (subsection
      "The Three Outputs"
      (p "1. Decision: Grant or refuse the requested action 2. Effect: The consequence of the decision (action performed, or refusal message) 3. Record: An audit entry capturing what happened"))
    (subsection
      "Auditable vs. Audited"
      (list
        (item "Auditable: The mechanism exists to log the event")
        (item "Audited: The event is actively being logged"))
      (p "All access control decisions are auditable. Whether they are audited depends on realm policy.")))
  (section
    "Per-Realm Audit Policy"
    (p "Each realm configures its own audit policy. The default is lean.")
    (subsection
      "Policy Levels"
      (table
        (header "Level " "Description ")
        (row "lean " "Minimal auditing, low overhead (default) ")
        (row "standard " "Security-relevant events audited ")
        (row "paranoid " "All access decisions audited ")))
    (subsection
      "Event Categories"
      (table
        (header "Event " "Lean " "Standard " "Paranoid ")
        (row "Successful joins " "audit " "audit " "audit ")
        (row "Join refusals " "print " "audit " "audit ")
        (row "Delegations " "audit " "audit " "audit ")
        (row "Revocations " "audit " "audit " "audit ")
        (row "Capability grants " "audit " "audit " "audit ")
        (row "Capability refusals " "print " "audit " "audit ")
        (row "Object reads " "— " "— " "audit ")
        (row "Object writes " "print " "audit " "audit ")))
    (subsection
      "Configuration"
      (code scheme "(realm-audit-policy 'lean)      ; default\n(realm-audit-policy 'standard)\n(realm-audit-policy 'paranoid)\n\n;; Or fine-grained:\n(realm-audit-policy\n  '((joins . audit)\n    (refusals . print)\n    (delegations . audit)\n    (reads . none)))")))
  (section
    "Implementation Pattern"
    (p "When implementing an access control point:")
    (code scheme "(define (access-control-point principal action context)\n  \"Template for access control with co-designed auditing\"\n\n  ;; 1. Make the decision\n  (let ((decision (evaluate-policy principal action context)))\n\n    ;; 2. Record based on policy\n    (case (realm-audit-policy)\n      ((paranoid)\n       (audit-append\n         actor: principal\n         action: `(,action ,@context)\n         motivation: (if (eq? decision 'grant)\n                         \"Access granted\"\n                         \"Access refused\")))\n      ((standard)\n       (when (or (eq? decision 'grant)\n                 (security-relevant? action))\n         (audit-append ...)))\n      ((lean)\n       (when (eq? decision 'refuse)\n         (print (format \"~a Refused: ~a\" action (refuse-reason))))))\n\n    ;; 3. Effect\n    (if (eq? decision 'grant)\n        (perform-action action context)\n        (refuse-with-reason action context))))"))
  (section
    "Vocabulary"
    (p "Consistent terminology for access control outcomes:")
    (table
      (header "Outcome " "Verb " "Usage ")
      (row "Execution fails " "Evaporated " "\"Execution Evaporated: Signature verification failed\" ")
      (row "Join denied " "Refused " "\"Join Refused: No valid attestation\" ")
      (row "Capability denied " "Refused " "\"Capability Refused: Insufficient authority\" ")
      (row "Operation blocked " "Refused " "\"Operation Refused: Policy violation\" "))
    (p "Avoid: terminated, aborted, ended, failed (where possible)."))
  (section
    "Security Considerations"
    (subsection
      "Refusal Patterns"
      (p "A pattern of refusals may indicate: - Misconfiguration (legitimate users being blocked) - Attack probing (malicious principals testing boundaries) - Policy too restrictive (needs adjustment)")
      (p "Standard and paranoid policies audit refusals to enable pattern detection."))
    (subsection
      "Audit Cost"
      (p "Each audit entry is: - Cryptographically signed (Ed25519) - Hash-chained to previous entry - Persisted to storage")
      (p "Lean policy minimizes this overhead for high-throughput realms."))
    (subsection
      "Audit Integrity"
      (p "Audit entries themselves are tamper-evident. An attacker cannot: - Delete entries (breaks hash chain) - Modify entries (invalidates signature) - Reorder entries (violates sequence numbers)")))
  (section
    "References"
    (list
      (item "Memo-003: Cryptographic Audit Trail")
      (item "Memo-004: SPKI Authorization")
      (item "Memo-046: Security Architecture")))
  (section
    "Changelog"
    (p "- 2026-01-10: Initial draft")))

