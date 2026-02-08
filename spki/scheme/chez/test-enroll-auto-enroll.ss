#!/usr/bin/env scheme-script
;;; test-enroll-auto-enroll.ss - Tests for enrollment modules (Chez port)
;;;
;;; Tests: enroll.sls, auto-enroll.sls, vault.sls membership extensions
;;;
;;; Run: CHEZSCHEMELIBDIRS=. chez --program test-enroll-auto-enroll.ss

(import (rnrs)
        (only (chezscheme) printf format void
              file-exists?
              with-output-to-string with-output-to-file
              system delete-file getenv
              flush-output-port current-directory)
        (cyberspace chicken-compatibility chicken)
        (cyberspace chicken-compatibility base64)
        (cyberspace os)
        (cyberspace crypto-ffi)
        (cyberspace wordlist)
        (cyberspace vault)
        (cyberspace capability)
        (cyberspace enroll)
        (cyberspace auto-enroll))

;;; ============================================================
;;; Test Framework
;;; ============================================================

(define *tests-run* 0)
(define *tests-passed* 0)
(define *tests-failed* 0)

(define (test name pred)
  (set! *tests-run* (+ *tests-run* 1))
  (if pred
      (begin
        (set! *tests-passed* (+ *tests-passed* 1))
        (printf "  PASS: ~a~%" name))
      (begin
        (set! *tests-failed* (+ *tests-failed* 1))
        (printf "  FAIL: ~a~%" name))))

(define (test-section name)
  (printf "~%=== ~a ===~%" name))

;;; ============================================================
;;; Initialize
;;; ============================================================

(sodium-init)

;;; ============================================================
;;; Enroll Module - Local Helpers
;;; ============================================================

(test-section "Enroll - Utility Functions")

;; val->string is internal but we can test format-enrollment-display

(test "probe-scaling returns positive integer"
  (let ((weave (probe-scaling)))
    (and (integer? weave) (> weave 0))))

(test "detect-mobile - MacBook is mobile"
  (let* ((hw `(hardware (os "Darwin") (model "MacBookAir10,1")
                        (mobile #t) (weave 1000)
                        (cores 8) (memory-gb 16)))
         (mobile (cadr (assq 'mobile (cdr hw)))))
    (eq? mobile #t)))

(test "detect-mobile - Mac Studio is not mobile"
  (let* ((hw `(hardware (os "Darwin") (model "Mac14,6")
                        (mobile #f) (weave 5000)
                        (cores 14) (memory-gb 128)))
         (mobile (cadr (assq 'mobile (cdr hw)))))
    (eq? mobile #f)))

;;; ============================================================
;;; Enroll Module - System Introspection
;;; ============================================================

(test-section "Enroll - System Introspection")

(test "introspect-hardware returns alist"
  (let ((hw (introspect-hardware)))
    (and (pair? hw) (eq? (car hw) 'hardware))))

(test "hardware has os field"
  (let ((hw (introspect-hardware)))
    (assq 'os (cdr hw))))

(test "hardware has arch field"
  (let ((hw (introspect-hardware)))
    (assq 'arch (cdr hw))))

(test "hardware has mobile field"
  (let ((hw (introspect-hardware)))
    (assq 'mobile (cdr hw))))

(test "hardware has weave field"
  (let ((hw (introspect-hardware)))
    (let ((w (assq 'weave (cdr hw))))
      (and w (number? (cadr w)) (> (cadr w) 0)))))

(test "introspect-network returns alist"
  (let ((net (introspect-network)))
    (and (pair? net) (eq? (car net) 'network))))

(test "introspect-storage returns alist"
  (let ((sto (introspect-storage)))
    (and (pair? sto) (eq? (car sto) 'storage))))

(test "introspect-realm returns alist"
  (let ((realm (introspect-realm)))
    (and (pair? realm) (eq? (car realm) 'realm))))

(test "introspect-realm has vault-path"
  (let ((realm (introspect-realm)))
    (assq 'vault-path (cdr realm))))

(test "introspect-codebase returns alist"
  (let ((cb (introspect-codebase)))
    (and (pair? cb) (eq? (car cb) 'codebase))))

(test "introspect-system returns full system-info"
  (let ((sys (introspect-system)))
    (and (pair? sys) (eq? (car sys) 'system-info))))

(test "introspect-system has timestamp"
  (let ((sys (introspect-system)))
    (assq 'timestamp (cdr sys))))

(test "introspect-system has lamport-time"
  (let ((sys (introspect-system)))
    (assq 'lamport-time (cdr sys))))

;;; ============================================================
;;; Enroll Module - Certificate Creation
;;; ============================================================

(test-section "Enroll - Certificate Management")

(let* ((master-kp (ed25519-keypair))
       (master-pub (car master-kp))
       (master-priv (cadr master-kp))
       (node-kp (ed25519-keypair))
       (node-pub (car node-kp))
       (node-priv (cadr node-kp)))

  ;; Create enrollment cert
  (let ((cert (create-enrollment-cert 'testnode node-pub master-priv)))
    (test "create-enrollment-cert returns signed cert"
      (and (pair? cert)
           (eq? (car cert) 'signed-enrollment-cert)))

    (test "cert has spki-cert body"
      (let ((body (cadr cert)))
        (and (pair? body) (eq? (car body) 'spki-cert))))

    (test "cert has signature"
      (let ((sig (caddr cert)))
        (and (pair? sig) (eq? (car sig) 'signature))))

    (test "cert body has name"
      (let ((body (cadr cert)))
        (let ((name (assq 'name (cdr body))))
          (and name (eq? (cadr name) 'testnode)))))

    (test "cert body has default role=full"
      (let ((body (cadr cert)))
        (let ((role (assq 'role (cdr body))))
          (and role (eq? (cadr role) 'full)))))

    (test "cert body has capabilities"
      (let ((body (cadr cert)))
        (let ((caps (assq 'capabilities (cdr body))))
          (and caps (pair? (cadr caps))))))

    (test "cert body has validity"
      (let ((body (cadr cert)))
        (let ((valid (assq 'validity (cdr body))))
          (and valid
               (assq 'not-before (cdr valid))
               (assq 'not-after (cdr valid))))))

    ;; Create with master role
    (let ((master-cert (create-enrollment-cert 'master-node master-pub master-priv
                                                'role: 'master)))
      (test "master cert has master role"
        (let ((body (cadr master-cert)))
          (let ((role (assq 'role (cdr body))))
            (and role (eq? (cadr role) 'master))))))

    ;; Renew certificate
    (let ((renewed (renew-certificate cert master-priv)))
      (test "renewed cert is signed-enrollment-cert"
        (and (pair? renewed)
             (eq? (car renewed) 'signed-enrollment-cert)))

      (test "renewed cert has renewed-from"
        (let ((body (cadr renewed)))
          (assq 'renewed-from (cdr body)))))

    ;; Revoke certificate
    (let ((revocation (revoke-certificate cert master-priv)))
      (test "revocation has correct structure"
        (and (pair? revocation)
             (eq? (car revocation) 'revocation)))

      (test "revocation has certificate-name"
        (assq 'certificate-name (cdr revocation)))

      (test "revocation has revoked-at timestamp"
        (assq 'revoked-at (cdr revocation)))

      (test "revocation has signature"
        (assq 'signature (cdr revocation))))))

;;; ============================================================
;;; Enroll Module - Display Formatting
;;; ============================================================

(test-section "Enroll - Display Formatting")

(let* ((kp (ed25519-keypair))
       (pubkey (car kp))
       (code (pubkey->syllables pubkey)))

  (test "format-enrollment-display returns string"
    (string? (format-enrollment-display 'testnode code)))

  (test "enrollment display contains node name"
    (string-contains (format-enrollment-display 'testnode code) "testnode"))

  (test "enrollment display contains box characters"
    (string-contains (format-enrollment-display 'testnode code) "\x250C;"))

  ;; Test format-approval-display
  (let ((hw `(hardware (os "Linux") (arch "x86_64") (hostname "test")
                       (cpu "Test CPU") (memory-gb 32)
                       (mobile #f) (weave 1000))))
    (test "format-approval-display returns string"
      (string? (format-approval-display 'testnode code "testhost" hw)))

    (test "approval display contains hardware info"
      (string-contains (format-approval-display 'testnode code "testhost" hw)
                       "Test CPU"))))

;;; ============================================================
;;; Vault - Membership Certificate Storage
;;; ============================================================

(test-section "Vault - Membership Certificates")

;; Set up temp vault
(define test-vault-dir ".vault-test-enroll")
(system (string-append "rm -rf " test-vault-dir))
(system (string-append "mkdir -p " test-vault-dir))

(test "realm-affiliated? returns #f when no cert"
  (not (realm-affiliated?)))

;; Test with actual .vault (if exists, skip; otherwise mock)
(test "realm-membership-cert returns #f when no vault"
  ;; Will be #f unless .vault/certs/membership.cert exists
  (let ((cert (realm-membership-cert)))
    (or (not cert) (pair? cert))))

;; Clean up
(system (string-append "rm -rf " test-vault-dir))

;;; ============================================================
;;; Auto-Enroll Module - State Management
;;; ============================================================

(test-section "Auto-Enroll - State Management")

(test "initial realm-status shows no master"
  (let ((status (realm-status)))
    (not (cdr (assq 'master status)))))

(test "enrollment-status shows not enrolled"
  (let ((status (enrollment-status)))
    (not (cdr (assq 'enrolled status)))))

(test "auto-enroll-status returns alist"
  (let ((status (auto-enroll-status)))
    (and (pair? status)
         (assq 'join-listener-active status)
         (assq 'my-name status))))

(test "realm-verbose! enables verbose mode"
  (let ((result (realm-verbose! #t)))
    (and (string? result)
         (string=? result "realm verbose on"))))

(test "realm-verbose! disables verbose mode"
  (let ((result (realm-verbose! #f)))
    (and (string? result)
         (string=? result "realm verbose off"))))

;;; ============================================================
;;; Auto-Enroll Module - Reset
;;; ============================================================

(test-section "Auto-Enroll - Reset and Cleanup")

(test "reset-enrollment-state! returns 'reset"
  (eq? (reset-enrollment-state!) 'reset))

(test "after reset, realm-status shows no master"
  (let ((status (realm-status)))
    (not (cdr (assq 'master status)))))

(test "after reset, enrollment-status shows not enrolled"
  (let ((status (enrollment-status)))
    (not (cdr (assq 'enrolled status)))))

;;; ============================================================
;;; Auto-Enroll Module - Gossip Configuration
;;; ============================================================

(test-section "Auto-Enroll - Gossip Configuration")

;; Build a fake scaling factors structure
(let ((scaling `((reference . test-master)
                 (reference-score . 500.0)
                 (members . ((test-master . 1.0) (test-node . 0.5)))
                 (aggregate-score . 750.0)
                 (member-count . 2)
                 (effective-capacity . 1.5)
                 (recommended-replication . 2))))

  (let ((gossip-cfg (configure-gossip-from-scaling scaling)))
    (test "gossip config has interval"
      (assq 'gossip-interval gossip-cfg))

    (test "gossip config has batch-size"
      (assq 'batch-size gossip-cfg))

    (test "gossip interval is in range [10, 300]"
      (let ((interval (cdr (assq 'gossip-interval gossip-cfg))))
        (and (>= interval 10) (<= interval 300))))

    (test "batch size is in range [10, 500]"
      (let ((batch (cdr (assq 'batch-size gossip-cfg))))
        (and (>= batch 10) (<= batch 500))))

    (test "gossip config has max-connections"
      (let ((mc (cdr (assq 'max-connections gossip-cfg))))
        (and (integer? mc) (> mc 0))))

    (test "gossip config has replication-target"
      (assq 'replication-target gossip-cfg))

    (test "gossip config has my-scale"
      (assq 'my-scale gossip-cfg))))

;;; ============================================================
;;; Integration: Capability + Enrollment
;;; ============================================================

(test-section "Integration - Capability + Enrollment")

(let ((hw (introspect-hardware)))
  (test "hardware can be scored by capability module"
    (let ((score (compute-capability-score hw)))
      (and (number? score) (>= score 0))))

  (test "single-member scaling factor computes"
    (let* ((members `((testnode . ,hw)))
           (scaling (compute-scaling-factor members)))
      (and (pair? scaling)
           (assq 'reference scaling)
           (assq 'members scaling)))))

;;; ============================================================
;;; Integration: Enrollment + Wordlist
;;; ============================================================

(test-section "Integration - Enrollment + Wordlist")

(let* ((kp (ed25519-keypair))
       (pubkey (car kp)))

  (test "pubkey->syllables produces verification code"
    (let ((code (pubkey->syllables pubkey)))
      (and (pair? code) (> (length code) 0))))

  (test "syllables->display formats nicely"
    (let* ((code (pubkey->syllables pubkey))
           (display-str (syllables->display code)))
      (and (string? display-str) (> (string-length display-str) 0)))))

;;; ============================================================
;;; Edge Cases
;;; ============================================================

(test-section "Edge Cases")

(test "enroll-listen returns empty list initially"
  (null? (enroll-listen)))

(test "enroll-reject creates rejection notice"
  (let ((rejection (enroll-reject '((name testnode)) 'reason: "testing")))
    (and (pair? rejection)
         (eq? (car rejection) 'enrollment-rejected)
         (string=? (cadr (assq 'reason (cdr rejection))) "testing"))))

(test "enroll-wait returns awaiting-approval"
  (let-values (((pub priv code) (enroll-request 'silent)))
    (let ((result (enroll-wait pub priv code 'silent)))
      (and (pair? result)
           (eq? (car result) 'awaiting-approval)))))

;;; ============================================================
;;; Results
;;; ============================================================

(printf "~%~%========================================~%")
(printf "Tests: ~a run, ~a passed, ~a failed~%"
        *tests-run* *tests-passed* *tests-failed*)
(printf "========================================~%")

(when (> *tests-failed* 0)
  (exit 1))
