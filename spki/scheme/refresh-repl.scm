#!/usr/bin/env csi -s
;;; refresh-repl.scm - Rebuild repl binary

(import scheme
        (chicken base)
        (chicken process))

(print "=== Rebuilding repl ===\n")

(system "csc -O2 -d1 repl.scm -o repl")

(print "\nDone.")
