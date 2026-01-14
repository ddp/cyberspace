;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 13)
  (title "TLA+ Formal Specification")
  (section
    "Abstract"
    (p "This RFC specifies the use of TLA+ (Temporal Logic of Actions) for formal specification and model checking of Cyberspace protocols, ensuring correctness before implementation."))
  (section
    "Motivation"
    (p "Running code is necessary but not sufficient:")
    (list
      (item "Tests check examples: Not all possible executions")
      (item "Reviews check logic: Not all interleavings")
      (item "Bugs hide in corners: Race conditions, edge cases"))
    (p "TLA+ provides:")
    (p "1. Precise specification: Mathematical description of behavior 2. Model checking: Exhaustive state space exploration 3. Proof capability: Formal verification of properties 4. Design tool: Find bugs before writing code")
    (p "From Lamport:")
    (blockquote "If you're thinking without writing, you only think you're thinking."))
  (section
    "Specification"
    (subsection
      "TLA+ Overview"
      (p "TLA+ describes systems as state machines:")
      (code tla "VARIABLES state, messages, decisions\n\nInit ==\n  /\\ state = [n \\in Nodes |-> \"idle\"]\n  /\\ messages = {}\n  /\\ decisions = {}\n\nNext ==\n  \\/ Propose(...)\n  \\/ Prepare(...)\n  \\/ Commit(...)\n  \\/ Decide(...)\n\nSpec == Init /\\ [][Next]_<<state, messages, decisions>>"))
    (subsection
      "Safety Properties"
      (p "Invariants that must always hold:")
      (code tla "TypeOK ==\n  /\\ state \\in [Nodes -> {\"idle\", \"prepared\", \"committed\"}]\n  /\\ messages \\subseteq Message\n  /\\ decisions \\subseteq Value\n\nAgreement ==\n  \\A n1, n2 \\in Nodes:\n    (decisions[n1] # {} /\\ decisions[n2] # {}) =>\n      decisions[n1] = decisions[n2]"))
    (subsection
      "Liveness Properties"
      (p "Temporal properties about progress:")
      (code tla "Termination ==\n  <>(\\A n \\in Nodes: decisions[n] # {})\n\nEventualConsistency ==\n  []<>(\\A n1, n2 \\in Nodes: state[n1] = state[n2])")))
  (section
    "Cyberspace Protocol Specifications"
    (subsection
      "Threshold Signatures (RFC-007)"
      (code tla "--------------------------- MODULE ThresholdSig ---------------------------\nEXTENDS Integers, FiniteSets\n\nCONSTANTS Signers, Threshold, Script\n\nVARIABLES signatures, verified\n\nInit ==\n  /\\ signatures = {}\n  /\\ verified = FALSE\n\nSign(s) ==\n  /\\ s \\in Signers\n  /\\ s \\notin {sig.signer : sig \\in signatures}\n  /\\ signatures' = signatures \\union\n       {[signer |-> s, script |-> Script, valid |-> TRUE]}\n  /\\ verified' = verified\n\nVerify ==\n  /\\ Cardinality({sig \\in signatures : sig.valid}) >= Threshold\n  /\\ verified' = TRUE\n  /\\ UNCHANGED signatures\n\nNext ==\n  \\/ \\E s \\in Signers: Sign(s)\n  \\/ Verify\n\n\\ Safety: Never verify with insufficient signatures\nSafety ==\n  verified => Cardinality({sig \\in signatures : sig.valid}) >= Threshold\n\n\\ Liveness: If enough sign, eventually verify\nLiveness ==\n  (Cardinality(Signers) >= Threshold) => <>(verified)\n\n============================================================================="))
    (subsection
      "Audit Trail (RFC-003)"
      (code tla "--------------------------- MODULE AuditTrail ---------------------------\nEXTENDS Integers, Sequences\n\nCONSTANTS Actors, Actions\n\nVARIABLES log, sequence\n\nInit ==\n  /\\ log = <<>>\n  /\\ sequence = 0\n\nAppend(actor, action) ==\n  /\\ actor \\in Actors\n  /\\ action \\in Actions\n  /\\ sequence' = sequence + 1\n  /\\ log' = Append(log, [\n       seq |-> sequence',\n       actor |-> actor,\n       action |-> action,\n       parent |-> IF sequence = 0 THEN \"genesis\" ELSE log[sequence].hash\n     ])\n\n\\ Invariant: Chain integrity\nChainIntegrity ==\n  \\A i \\in 1..Len(log)-1:\n    log[i+1].parent = log[i].hash\n\n\\ Invariant: Monotonic sequence\nMonotonicSequence ==\n  \\A i \\in 1..Len(log)-1:\n    log[i+1].seq = log[i].seq + 1\n\n============================================================================="))
    (subsection
      "Byzantine Consensus (RFC-011)"
      (code tla "--------------------------- MODULE PBFT ---------------------------\nEXTENDS Integers, FiniteSets\n\nCONSTANTS Nodes, f, Values\n\nASSUME Cardinality(Nodes) >= 3f + 1\n\nVARIABLES\n  view,\n  prepares,\n  commits,\n  decisions\n\nInit ==\n  /\\ view = 0\n  /\\ prepares = [n \\in Nodes |-> {}]\n  /\\ commits = [n \\in Nodes |-> {}]\n  /\\ decisions = [n \\in Nodes |-> {}]\n\nPrePrepare(primary, v) ==\n  /\\ primary = Leader(view)\n  /\\ v \\in Values\n  /\\ \\A n \\in Nodes:\n       prepares' = [prepares EXCEPT ![n] = @ \\union {[view |-> view, value |-> v]}]\n  /\\ UNCHANGED <<view, commits, decisions>>\n\nPrepare(n, v) ==\n  /\\ [view |-> view, value |-> v] \\in prepares[n]\n  /\\ Cardinality({m \\in Nodes : [view |-> view, value |-> v] \\in prepares[m]}) >= 2f + 1\n  /\\ commits' = [commits EXCEPT ![n] = @ \\union {[view |-> view, value |-> v]}]\n  /\\ UNCHANGED <<view, prepares, decisions>>\n\nCommit(n, v) ==\n  /\\ [view |-> view, value |-> v] \\in commits[n]\n  /\\ Cardinality({m \\in Nodes : [view |-> view, value |-> v] \\in commits[m]}) >= 2f + 1\n  /\\ decisions' = [decisions EXCEPT ![n] = {v}]\n  /\\ UNCHANGED <<view, prepares, commits>>\n\n\\ Safety: Agreement\nAgreement ==\n  \\A n1, n2 \\in Nodes:\n    (decisions[n1] # {} /\\ decisions[n2] # {}) =>\n      decisions[n1] = decisions[n2]\n\n=============================================================================")))
  (section
    "Model Checking Process"
    (subsection
      "1. Write Specification"
      (p "Define state machine and properties."))
    (subsection
      "2. Configure Model"
      (code tla "CONSTANTS\n  Nodes = {n1, n2, n3, n4}\n  f = 1\n  Values = {v1, v2}"))
    (subsection
      "3. Run TLC Model Checker"
      (code bash "$ tlc PBFT.tla\nTLC2 Version 2.18\n...\nModel checking completed. No errors found.\n  States explored: 847293\n  Distinct states: 12847"))
    (subsection
      "4. Analyze Counterexamples"
      (p "If property violated, TLC shows trace:")
      (code "Error: Invariant Agreement is violated.\nTrace:\n  State 1: <Initial>\n  State 2: PrePrepare(n1, v1)\n  State 3: Prepare(n2, v1)\n  ...\n  State 12: decisions = [n1 |-> {v1}, n2 |-> {v2}]  << VIOLATION")))
  (section
    "Integration with Implementation"
    (subsection
      "Specification → Implementation"
      (code "TLA+ Spec          Scheme Implementation\n-----------        ---------------------\nVARIABLES state    (define-record-type <state> ...)\nInit ==            (define (init) ...)\nAction(x) ==       (define (action x) ...)\nInvariant          (assert (invariant? state))"))
    (subsection
      "Runtime Assertions"
      (code scheme "(define (append-audit! entry)\n  ;; TLA+ invariant: MonotonicSequence\n  (assert (> (entry-sequence entry)\n             (entry-sequence (last-entry))))\n  ;; TLA+ invariant: ChainIntegrity\n  (assert (equal? (entry-parent entry)\n                  (entry-hash (last-entry))))\n  ;; Proceed with append\n  ...)")))
  (section
    "PlusCal (Algorithmic TLA+)"
    (p "Higher-level syntax that compiles to TLA+:")
    (code tla "--algorithm ThresholdSign {\n  variables signatures = {}, verified = FALSE;\n\n  process (signer \\in Signers)\n  {\n    sign:\n      signatures := signatures \\union {self};\n  }\n\n  process (verifier = \"v\")\n  {\n    verify:\n      await Cardinality(signatures) >= Threshold;\n      verified := TRUE;\n  }\n}"))
  (section
    "Benefits"
    (table
      (header "Aspect " "Without TLA+ " "With TLA+ ")
      (row "Design " "Informal, ambiguous " "Precise, mathematical ")
      (row "Bugs " "Found in testing/production " "Found before coding ")
      (row "Confidence " "\"Seems to work\" " "\"Proven correct\" ")
      (row "Documentation " "Natural language " "Executable specification ")
      (row "Maintenance " "Risky changes " "Verify changes ")))
  (section
    "Limitations"
    (list
      (item "State explosion: Large state spaces take time")
      (item "Learning curve: TLA+ is different")
      (item "Abstraction gap: Spec ≠ implementation")
      (item "Finite models: Cannot check infinite systems directly"))
    (p "Mitigations: - Symmetry reduction - Abstraction - Proof for infinite cases"))
  (section
    "References"
    (p "1. Lamport, L. (2002). Specifying Systems: The TLA+ Language. 2. Lamport, L. (2009). The PlusCal Algorithm Language. 3. Newcombe, C., et al. (2015). How Amazon Web Services Uses Formal Methods. 4. TLA+ Tools: https://lamport.azurewebsites.net/tla/tools.html"))
  (section
    "Changelog"
    (list
      (item "2026-01-06")
      (item "Initial specification"))))

