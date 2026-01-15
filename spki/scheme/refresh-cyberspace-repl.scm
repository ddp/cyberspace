#!/usr/bin/env csi -s
;;; refresh-cyberspace-repl.scm - Rebuild cyberspace-repl binary

(import scheme
        (chicken base)
        (chicken process))

(print "=== Rebuilding cyberspace-repl ===\n")

(system "csc -O2 -d1 cyberspace-repl.scm -o cyberspace-repl")

(print "\nDone.")
