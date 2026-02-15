#!/usr/bin/env csi -s
;;; Test audit parser reconstruction

(import audit
        crypto-ffi
        (chicken file)
        (chicken format)
        (chicken io)
        srfi-13)

(sodium-init)

(print "=== Audit Parser Test ===\n")

;; Export audit trail to human-readable format
(print "Exporting audit trail to human-readable format...")
(audit-export-human output: "audit-test-export.txt")
(print "✓ Export complete\n")

;; Read the export and check for 'unknown' action
(print "Checking exported audit trail...")
(let ((content (with-input-from-file "audit-test-export.txt" read-string)))
  (if (string-contains content "unknown")
      (begin
        (print "✗ FAILED: Found 'unknown' in export - parser not working\n")
        (print "Export preview (first 500 chars):")
        (print (substring content 0 (min 500 (string-length content))))
        (exit 1))
      (begin
        (print "✓ PASSED: No 'unknown' found - parser correctly reconstructing entries\n")
        (print "\nSample from export:")
        (print (substring content 0 (min 800 (string-length content))))
        (print "..."))))

(print "\n=== Test Complete ===")
