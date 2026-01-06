#!/usr/bin/env csi -s
;;; test-audit.scm - Demonstrate audit trail for Library of Cyberspace

(import audit crypto-ffi)

;; Generate test keypair
(define keys (ed25519-keypair))
(define public-key (car keys))
(define private-key (cadr keys))

(print "Initializing audit trail...")
(audit-init signing-key: private-key)

(print "\nCreating audit entries...")

;; Entry 1: Initial setup
(audit-append
 actor: public-key
 action: '(audit-init ".vault/audit")
 motivation: "Establishing cryptographic audit trail for the Library of Cyberspace"
 relates-to: "preservation-architecture"
 signing-key: private-key)

;; Entry 2: Adding vault system
(audit-append
 actor: public-key
 action: '(seal-commit "vault.scm" catalog: #t)
 motivation: "Add cryptographically sealed version control with progressive metadata"
 relates-to: "vault-v1.0"
 signing-key: private-key)

;; Entry 3: Adding audit system
(audit-append
 actor: public-key
 action: '(seal-commit "audit.scm" preserve: #t)
 motivation: "Implement future-proof audit trail encoding for offline discovery"
 relates-to: "library-preservation"
 signing-key: private-key)

(print "\nVerifying audit chain...")
(audit-chain verify-key: public-key)

(print "\nExporting audit trail...")
(audit-export-human output: "audit-trail.txt")

(print "\nDone! See audit-trail.txt for human-readable format")
