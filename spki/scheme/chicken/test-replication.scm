#!/usr/bin/env csi -s
;;; Test replication layer - publish/subscribe/synchronize

(import vault
        crypto-ffi
        (chicken file)
        (chicken format)
        (chicken process-context))

(sodium-init)

(print "=== Replication Layer Test ===\n")

;; Initialize vault with signing key
(print "Initializing vault...")
(define keys (ed25519-keypair))
(define public-key (car keys))
(define private-key (cadr keys))
(vault-init signing-key: private-key)
(print "✓ Vault initialized\n")

;; Skip seal-commit test for now - focus on replication
;; Just use current git state

;; Create a sealed release
(print "Creating sealed release 1.0.0...")
(seal-release "1.0.0" message: "First sealed release for replication testing")
(print "✓ Release created\n")

;; Test filesystem publication
(print "Testing seal-publish to filesystem...")
(let ((publish-dir "/tmp/cyberspace-publish-test"))
  ;; Create publish directory (will reuse if exists)
  (create-directory publish-dir #t)

  ;; Publish to filesystem
  (seal-publish "1.0.0" remote: publish-dir message: "Published to filesystem")

  ;; Verify archive exists
  (let ((archive-path (sprintf "~a/vault-1.0.0.archive" publish-dir)))
    (if (file-exists? archive-path)
        (begin
          (print "✓ Archive published to filesystem\n")
          (print "Archive location: " archive-path))
        (begin
          (print "✗ Archive not found at expected location")
          (exit 1)))))

(print "\n=== Test Complete ===")
