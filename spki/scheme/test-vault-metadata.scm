#!/usr/bin/env csi -s
;;; Test vault metadata levels

(import vault
        crypto-ffi
        (chicken file)
        (chicken format)
        (chicken blob)
        (chicken time)
        srfi-4)

(sodium-init)

(print "=== Vault Metadata Levels Test ===\n")

;; Use existing vault initialization
(print "Using existing .vault directory\n")

(define test-timestamp (current-seconds))

;; Test 1: Minimal metadata (default)
(print "Test 1: Sealed commit with minimal metadata (default)")
(with-output-to-file "metadata-test-1.txt"
  (lambda ()
    (display (sprintf "First test file for metadata testing - ~a" test-timestamp))))
(seal-commit "Test: minimal metadata" files: '("metadata-test-1.txt"))
(print "✓ Minimal metadata commit\n")

;; Test 2: Catalog metadata
(print "Test 2: Sealed commit with catalog metadata")
(with-output-to-file "metadata-test-2.txt"
  (lambda ()
    (display (sprintf "Second test file with catalog metadata - ~a" test-timestamp))))
(seal-commit "Test: catalog metadata"
             files: '("metadata-test-2.txt")
             catalog: #t
             subjects: '("testing" "metadata")
             keywords: '("vault" "catalog"))
(print "✓ Catalog metadata commit\n")

;; Test 3: Preserve metadata
(print "Test 3: Sealed commit with preserve metadata")
(with-output-to-file "metadata-test-3.txt"
  (lambda ()
    (display (sprintf "Third test file with full preservation metadata - ~a" test-timestamp))))
(seal-commit "Test: preserve metadata"
             files: '("metadata-test-3.txt")
             preserve: #t)
(print "✓ Preserve metadata commit\n")

;; Check metadata directory
(print "Checking .vault/metadata directory:")
(let ((metadata-files (directory ".vault/metadata" #t)))
  (print "Found " (length metadata-files) " metadata entries")
  (for-each (lambda (f) (print "  - " f)) metadata-files))

(print "\n=== Metadata Test Complete ===")
