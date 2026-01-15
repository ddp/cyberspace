#!/usr/bin/env csi -s
;;; refresh-repl.scm - Rebuild Cyberspace.app

(import scheme
        (chicken base)
        (chicken process)
        (chicken format)
        (chicken pathname)
        (chicken process-context))

(print "=== Rebuilding Cyberspace.app ===\n")

(let ((app-dir (make-pathname (current-directory) "app")))
  (system (sprintf "cd ~a && ./build.sh" app-dir)))

(print "\nDone.")
