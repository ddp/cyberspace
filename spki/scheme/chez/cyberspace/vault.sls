;;; vault.sls - Vault Core: Lamport Clock + Capability Set (Chez Port)
;;; Library of Cyberspace
;;;
;;; Extracts the subsystems needed by gossip and other federation modules:
;;;   - Lamport clock (Memo-012): happened-before ordering
;;;   - Capability set: what this node can do
;;;
;;; The full vault (soup, keystore, seal-commit, etc.) will be ported
;;; separately once additional filesystem compat layers are available.
;;;
;;; Ported from vault.scm (lines 691-815).
;;; Copyright (c) 2026 Yoyodyne. See LICENSE.

(library (cyberspace vault)
  (export
    ;; Lamport Clock (Memo-012)
    lamport-tick!
    lamport-time
    lamport-send
    lamport-receive!
    lamport-save!
    lamport-load!
    lamport-format

    ;; Capability Set
    capability-add!
    capability-remove!
    capability?
    capabilities
    capability-intersect
    capability-difference
    capability-audit-enable!

    ;; Helper
    get-vault-principal)

  (import (rnrs)
          (only (chezscheme)
                printf format void file-exists? list-sort
                with-output-to-file with-input-from-file
                directory-exists?)
          (cyberspace chicken-compatibility hashtable)
          (cyberspace chicken-compatibility blob))

  ;; ============================================================
  ;; Helper
  ;; ============================================================

  (define (get-vault-principal signing-key)
    "Extract public key from Ed25519 signing key (64 bytes)."
    (if (and (bytevector? signing-key) (= (bytevector-length signing-key) 64))
        (let ((pk (make-bytevector 32)))
          (bytevector-copy! signing-key 32 pk 0 32)
          pk)
        #f))

  ;; ============================================================
  ;; Lamport Clock (Memo-012)
  ;;
  ;; Time in the weave is measured in lambda ticks, not wall-clock time.
  ;; The clock increments monotonically on every event.
  ;; Federation sync uses happened-before, not synchronized clocks.
  ;; ============================================================

  (define *lamport-counter* 0)

  (define (lamport-clock-path) ".vault/lamport-clock")

  (define (lamport-tick!)
    "Increment clock for local event. Returns new time."
    (set! *lamport-counter* (+ 1 *lamport-counter*))
    *lamport-counter*)

  (define (lamport-time)
    "Current Lamport time."
    *lamport-counter*)

  (define (lamport-send message)
    "Attach timestamp to outgoing message. Increments clock."
    (lamport-tick!)
    `((lamport-time . ,*lamport-counter*)
      (payload . ,message)))

  (define (lamport-receive! timestamped-message)
    "Update clock on message receipt. Returns payload."
    (let ((remote-time (cdr (assq 'lamport-time timestamped-message))))
      (set! *lamport-counter*
            (+ 1 (max *lamport-counter* remote-time)))
      (cdr (assq 'payload timestamped-message))))

  (define (lamport-save!)
    "Persist clock to vault (survives restarts)."
    (guard (exn [#t (void)])
      (when (directory-exists? ".vault")
        (with-output-to-file (lamport-clock-path)
          (lambda ()
            (write `(lamport-clock (counter ,*lamport-counter*)))
            (newline))))))

  (define (lamport-load!)
    "Load clock from vault. Called at startup."
    (guard (exn [#t (void)])
      (let ((path (lamport-clock-path)))
        (when (file-exists? path)
          (let ((data (with-input-from-file path read)))
            (when (and (pair? data) (eq? (car data) 'lamport-clock))
              (let ((counter-pair (assq 'counter (cdr data))))
                (when counter-pair
                  (set! *lamport-counter* (cadr counter-pair))))))))))

  (define (lamport-format)
    "Human-readable Lamport time with SI prefix."
    (let ((t *lamport-counter*))
      (cond
        ((< t 1000) (string-append "l " (number->string t)))
        ((< t 1000000) (string-append "l " (number->string (div t 1000)) "k"))
        ((< t 1000000000) (string-append "l " (number->string (div t 1000000)) "m"))
        (else (string-append "l " (number->string (div t 1000000000)) "g")))))

  ;; ============================================================
  ;; Capability Set (Weave Self-Awareness)
  ;;
  ;; Tracks what this node can do.  Used for gossip negotiation
  ;; and auto-enrollment master election.
  ;; ============================================================

  (define *capabilities* (make-hash-table eq?))
  (define *capability-audit* #f)

  (define (capability-add! cap)
    "Register a capability this node supports."
    (hash-table-set! *capabilities* cap #t)
    cap)

  (define (capability-remove! cap)
    "Remove a capability."
    (hash-table-delete! *capabilities* cap))

  (define (capability? cap)
    "Check if this node has a capability."
    (hash-table-exists? *capabilities* cap))

  (define (capabilities)
    "List all capabilities as a sorted list."
    (list-sort (lambda (a b)
                 (string<? (symbol->string a) (symbol->string b)))
               (hash-table-keys *capabilities*)))

  (define (capability-intersect caps1 caps2)
    (filter (lambda (c) (memq c caps2)) caps1))

  (define (capability-difference caps1 caps2)
    (filter (lambda (c) (not (memq c caps2))) caps1))

  (define (capability-audit-enable! signing-key)
    "Enable signed attestations for capability changes."
    (set! *capability-audit* signing-key)
    'audit-enabled)

  ;; Register core capabilities at load time
  (capability-add! 'ed25519-sign)
  (capability-add! 'ed25519-verify)
  (capability-add! 'sha256-hash)
  (capability-add! 'argon2id-kdf)
  (capability-add! 'chacha20-poly1305)
  (capability-add! 'lamport-clock)
  (capability-add! 'spki-certs)

) ;; end library
