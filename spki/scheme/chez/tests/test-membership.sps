#!/usr/bin/env chez --script
;;; test-membership.sps - Membership lifecycle tests (Memo-039)
;;;
;;; Tests join policies, proposals, voting, departure, disbarment,
;;; and revocation list management.

(import (rnrs)
        (only (chezscheme) printf format)
        (cyberspace auto-enroll)
        (cyberspace crypto-ffi))

(define *pass* 0)
(define *fail* 0)

(define (assert-true msg expr)
  (if expr
      (begin (set! *pass* (+ *pass* 1))
             (printf "  PASS: ~a~n" msg))
      (begin (set! *fail* (+ *fail* 1))
             (printf "  FAIL: ~a~n" msg))))

(define (assert-equal msg expected actual)
  (if (equal? expected actual)
      (begin (set! *pass* (+ *pass* 1))
             (printf "  PASS: ~a~n" msg))
      (begin (set! *fail* (+ *fail* 1))
             (printf "  FAIL: ~a (expected ~s, got ~s)~n" msg expected actual))))

(define (assert-error msg thunk)
  (guard (exn [#t (set! *pass* (+ *pass* 1))
                  (printf "  PASS: ~a~n" msg)])
    (thunk)
    (set! *fail* (+ *fail* 1))
    (printf "  FAIL: ~a (no error raised)~n" msg)))

(printf "~n=== Membership Lifecycle Tests (Memo-039) ===~n~n")
(sodium-init)

;; ============================================================
;; Join Policy
;; ============================================================

(printf "--- Join Policy ---~n")

(reset-enrollment-state!)
(assert-equal "default join policy is open" 'open (realm-join-policy))

(set-join-policy! 'sponsored)
(assert-equal "set policy to sponsored" 'sponsored (realm-join-policy))

(set-join-policy! 'voted 'threshold: '(3 5))
(assert-equal "set policy to voted" 'voted (realm-join-policy))

(set-join-policy! 'closed)
(assert-equal "set policy to closed" 'closed (realm-join-policy))

(assert-error "invalid policy raises error"
  (lambda () (set-join-policy! 'invalid)))

(set-join-policy! 'open)
(assert-equal "reset to open" 'open (realm-join-policy))

;; ============================================================
;; Revocation List
;; ============================================================

(printf "--- Revocation List ---~n")

(reset-enrollment-state!)
(assert-equal "revocation list starts empty" '() (revocation-list))
(assert-true "unknown principal not revoked" (not (principal-revoked? 'bad-node)))

;; We can't call add-revocation! directly (not exported), but we can
;; test via disbar-member! indirectly through propose-disbar + voting.
;; For now, test the exported query interface.

;; ============================================================
;; Proposals - Sponsored Policy
;; ============================================================

(printf "--- Proposals (Sponsored) ---~n")

(reset-enrollment-state!)
;; Simulate being an enrolled master
;; We need to set up enough state for proposals to work
;; Start a minimal realm (no network)
(let ((kp (ed25519-keypair)))
  ;; Manually prime state for testing
  ;; Use auto-enroll-realm behavior without network
  (void))

;; Set up as master with a keypair
(reset-enrollment-state!)
(set-join-policy! 'sponsored)

;; propose-join needs *my-name* set
;; We test that proposals require sponsored or voted policy
(set-join-policy! 'open)
(assert-error "propose-join rejects under open policy"
  (lambda () (propose-join 'new-node #vu8(1 2 3) '(hardware (cores 4)))))

(set-join-policy! 'sponsored)
;; Set minimal state for proposal creation
;; (This would normally happen via start-join-listener)

;; ============================================================
;; Proposals - Voted Policy
;; ============================================================

(printf "--- Proposals (Voted) ---~n")

(reset-enrollment-state!)
(set-join-policy! 'voted 'threshold: '(2 3))

;; propose-join under voted creates a pending proposal
(let ((proposal (propose-join 'applicant #vu8(1 2 3) '(hardware (cores 4)))))
  (assert-true "proposal created" (pair? proposal))
  (assert-equal "proposal type is join"
                'join (cadr (assq 'type (cdr proposal))))
  (assert-equal "proposal subject is applicant"
                'applicant (cadr (assq 'subject (cdr proposal))))
  (assert-equal "proposal status is pending"
                'pending (cadr (assq 'status (cdr proposal))))
  (assert-equal "proposal threshold is (2 3)"
                '(2 3) (cadr (assq 'threshold (cdr proposal))))
  (assert-equal "one pending proposal" 1 (length (pending-proposals))))

;; ============================================================
;; Voting Protocol
;; ============================================================

(printf "--- Voting Protocol ---~n")

(assert-error "vote-proposal rejects invalid vote"
  (lambda () (vote-proposal "fake-id" 'maybe)))

(assert-error "vote-proposal rejects unknown proposal"
  (lambda () (vote-proposal "nonexistent" 'approve)))

;; ============================================================
;; Full Voting Flow
;; ============================================================

(printf "--- Full Voting Flow ---~n")

;; Set up a 3-member realm under voted policy
(reset-enrollment-state!)
(set-join-policy! 'voted 'threshold: '(2 3))

;; Create a proposal for a new member
(let* ((proposal (propose-join 'newcomer #vu8(10 20 30) '(hardware (cores 8))))
       (id (cadr (assq 'id (cdr proposal)))))
  ;; One vote from proposer - not enough (need 2 of 3)
  (assert-equal "proposal still pending after 1 vote"
                'pending (cadr (assq 'status (cdr (car (pending-proposals))))))
  ;; Second vote meets threshold
  ;; Simulate a second member voting (vote-proposal uses *my-name*)
  ;; The proposal has proposer's vote already; add another
  (let ((updated (vote-proposal id 'approve)))
    ;; With threshold (2 3) and 2 approve votes (proposer + current),
    ;; but they're from the same *my-name* (which is #f), so it's idempotent.
    ;; To properly test, we'd need to change *my-name* between votes.
    ;; For now, verify the vote was recorded.
    (assert-true "vote recorded in proposal"
                 (pair? (cadr (assq 'votes (cdr updated)))))))

;; ============================================================
;; Disbarment Proposals
;; ============================================================

(printf "--- Disbarment ---~n")

(reset-enrollment-state!)
;; Disbarment always requires a vote regardless of policy
(let ((proposal (propose-disbar 'bad-node "Byzantine behavior"
                                'evidence: "audit-hash-123")))
  (assert-true "disbar proposal created" (pair? proposal))
  (assert-equal "proposal type is disbar"
                'disbar (cadr (assq 'type (cdr proposal))))
  (assert-equal "reason recorded"
                "Byzantine behavior" (cadr (assq 'reason (cdr proposal))))
  (assert-true "evidence recorded"
               (assq 'evidence (cdr proposal)))
  (assert-equal "one pending proposal" 1 (length (pending-proposals))))

;; ============================================================
;; Pending Proposals
;; ============================================================

(printf "--- Pending Proposals ---~n")

(reset-enrollment-state!)
(assert-equal "no pending proposals after reset" '() (pending-proposals))

;; ============================================================
;; Leave Realm
;; ============================================================

(printf "--- Leave Realm ---~n")

(reset-enrollment-state!)
(assert-error "leave-realm errors when not enrolled"
  (lambda () (leave-realm)))

;; ============================================================
;; Status Integration
;; ============================================================

(printf "--- Status Integration ---~n")

(reset-enrollment-state!)
(let ((status (realm-status)))
  (assert-true "realm-status includes join-policy"
               (assq 'join-policy status))
  (assert-equal "join-policy in status is open"
                'open (cdr (assq 'join-policy status)))
  (assert-true "realm-status includes pending-proposals"
               (assq 'pending-proposals status))
  (assert-equal "pending-proposals count is 0"
                0 (cdr (assq 'pending-proposals status)))
  (assert-true "realm-status includes revocations"
               (assq 'revocations status))
  (assert-equal "revocations count is 0"
                0 (cdr (assq 'revocations status))))

(let ((status (auto-enroll-status)))
  (assert-true "auto-enroll-status includes join-policy"
               (assq 'join-policy status))
  (assert-true "auto-enroll-status includes pending-proposals"
               (assq 'pending-proposals status))
  (assert-true "auto-enroll-status includes revocations"
               (assq 'revocations status)))

;; ============================================================
;; Interactive Review
;; ============================================================

(printf "--- Interactive Review ---~n")

(reset-enrollment-state!)
;; review-proposals with no pending
(let ((result (review-proposals)))
  (assert-equal "review-proposals returns () when empty" '() result))

;; Create proposals and review
(set-join-policy! 'voted 'threshold: '(2 3))
(propose-join 'alice #vu8(10 20 30) '(hardware (cores 8)))
(propose-disbar 'eve "replay attack detected")

(let ((result (review-proposals)))
  (assert-equal "review-proposals returns 2 pending" 2 (length result)))

;; format-proposal returns the proposal
(let* ((proposals (pending-proposals))
       (p (car proposals)))
  (assert-true "format-proposal returns proposal"
               (pair? (format-proposal p))))

;; ============================================================
;; Reset clears everything
;; ============================================================

(printf "--- Reset ---~n")

(set-join-policy! 'voted)
(reset-enrollment-state!)
(assert-equal "reset restores open policy" 'open (realm-join-policy))
(assert-equal "reset clears revocation list" '() (revocation-list))
(assert-equal "reset clears proposals" '() (pending-proposals))

;; Summary
(printf "~n=== Membership: ~a passed, ~a failed ===~n~n" *pass* *fail*)
(when (> *fail* 0) (exit 1))
