;; Library of Cyberspace - Loose Ends
;; Things to test, investigate, or resolve

(loose-ends

  (item
    (id 1)
    (added "2026-01-08")
    (status open)
    (priority high)
    (title "Multi-instance single-host clustering")
    (description "Test running multiple cyberspace nodes as separate processes
on a single machine, each with its own .vault/, to debug federation
protocol without physical hardware. Network Alchemy heritage - their
clustering code ran in user mode on a single Digital HiNote, debuggable
in Emacs.")
    (test-plan
      "1. Create four separate vault directories"
      "2. Spawn four cyberspace-repl instances"
      "3. Configure TCP clustering between them"
      "4. Verify federation, replication, consensus"
      "5. Single-step through protocol in debugger")))
