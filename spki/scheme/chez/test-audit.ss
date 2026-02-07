;;; Audit Trail Test Suite
;;; Library of Cyberspace - Chez Port
;;;
;;; Tests the audit trail data structures, S-expression conversion,
;;; time parsing, query engine, and cryptographic sealing/verification.

(import (rnrs)
        (only (chezscheme) printf format void
              with-output-to-string getenv
              file-exists? delete-file)
        (cyberspace chicken-compatibility chicken)
        (cyberspace chicken-compatibility blob)
        (cyberspace chicken-compatibility hashtable)
        (cyberspace crypto-ffi)
        (cyberspace audit))

;; ============================================================
;; Test harness
;; ============================================================

(define *pass* 0)
(define *fail* 0)

(define (check name ok?)
  (if ok?
      (begin
        (printf "  pass ~a\n" name)
        (set! *pass* (+ *pass* 1)))
      (begin
        (printf "  FAIL ~a\n" name)
        (set! *fail* (+ *fail* 1)))))

(printf "\n=== Audit Trail Test Suite ===\n\n")

;; Init sodium
(sodium-init)

;; ============================================================
;; Time Utilities
;; ============================================================

(printf "--- Time Parsing ---\n")

;; Relative time specs
(let ((now (current-seconds)))
  (let ((t (parse-time-spec "1h")))
    (check "parse 1h" (and (number? t) (< (abs (- t (- now 3600))) 2))))
  (let ((t (parse-time-spec "24h")))
    (check "parse 24h" (and (number? t) (< (abs (- t (- now 86400))) 2))))
  (let ((t (parse-time-spec "7d")))
    (check "parse 7d" (and (number? t) (< (abs (- t (- now 604800))) 2))))
  (let ((t (parse-time-spec "5m")))
    (check "parse 5m" (and (number? t) (< (abs (- t (- now 300))) 2)))))

;; ISO date
(let ((t (parse-time-spec "2026-01-01")))
  (check "parse ISO date" (number? t))
  (check "ISO date value" (> t 0)))

;; ISO datetime
(let ((t (parse-time-spec "2026-01-15T12:30:00")))
  (check "parse ISO datetime" (number? t))
  (check "ISO datetime > ISO date" (> t (parse-time-spec "2026-01-01"))))

;; Epoch passthrough
(check "parse epoch number" (= (parse-time-spec 12345) 12345))

;; ============================================================
;; String Utilities (new additions)
;; ============================================================

(printf "\n--- String Utilities ---\n")

(check "string-suffix? yes" (string-suffix? ".sexp" "entry.sexp"))
(check "string-suffix? no" (not (string-suffix? ".txt" "entry.sexp")))
(check "string-take-right" (string=? (string-take-right "hello" 3) "llo"))
(check "string-drop-right" (string=? (string-drop-right "hello" 2) "hel"))
(check "string-concatenate" (string=? (string-concatenate '("a" "b" "c")) "abc"))

;; ============================================================
;; Audit Config
;; ============================================================

(printf "\n--- Configuration ---\n")

;; Use temp directory for tests
(let ((test-dir "/tmp/cyberspace-audit-test"))
  (audit-config 'audit-dir test-dir)
  (check "set audit-dir" (string=? (audit-config 'audit-dir) test-dir)))

(check "default sequence" (= (audit-config 'current-sequence) 0))
(check "default signing-key" (not (audit-config 'signing-key)))

;; ============================================================
;; Entry Records
;; ============================================================

(printf "\n--- Entry Records ---\n")

;; Generate a keypair for testing
(let-values (((pk sk) (ed25519-keypair)))
  (audit-config 'signing-key sk)
  (check "signing key set" (bytevector? (audit-config 'signing-key)))

  ;; Init audit in temp dir
  (audit-init 'audit-dir: "/tmp/cyberspace-audit-test")

  ;; Create an entry
  (let ((entry (audit-append
                 'actor: pk
                 'action: '(test-action "test-object" param1 param2)
                 'motivation: "Testing the audit trail"
                 'signing-key: sk)))
    (check "entry created" (entry-id entry))
    (check "entry id prefix" (string-prefix? "sha512:" (entry-id entry)))
    (check "entry sequence" (= (entry-sequence entry) 1))
    (check "entry timestamp" (string? (entry-timestamp entry)))
    (check "entry actor" (bytevector? (actor-principal (entry-actor entry))))
    (check "action verb" (eq? (action-verb (entry-action entry)) 'test-action))
    (check "action object" (string=? (action-object (entry-action entry)) "test-object"))
    (check "context motivation"
      (string=? (context-motivation (entry-context entry)) "Testing the audit trail"))

    ;; ============================================================
    ;; S-Expression Roundtrip
    ;; ============================================================

    (printf "\n--- S-Expression Roundtrip ---\n")

    (let ((sexp (entry->sexp entry)))
      (check "entry->sexp" (pair? sexp))
      (check "sexp tag" (eq? (car sexp) 'audit-entry))
      (check "sexp has id" (assq 'id (cdr sexp)))
      (check "sexp has seal" (assq 'seal (cdr sexp))))

    ;; ============================================================
    ;; Verification
    ;; ============================================================

    (printf "\n--- Verification ---\n")

    (let ((verified (audit-verify entry 'public-key: pk)))
      (check "verify entry" verified))

    ;; Create a second entry (chained)
    (let ((entry2 (audit-append
                    'actor: pk
                    'action: '(seal-commit "vault.sls")
                    'motivation: "Sealing vault module"
                    'signing-key: sk)))
      (check "entry2 sequence" (= (entry-sequence entry2) 2))
      (check "entry2 has parent" (string? (entry-parent-id entry2)))
      (check "entry2 parent = entry1 id"
        (string=? (entry-parent-id entry2) (entry-id entry)))

      (let ((verified2 (audit-verify entry2 'public-key: pk)))
        (check "verify entry2" verified2)))

    ;; ============================================================
    ;; Persistence & Query
    ;; ============================================================

    (printf "\n--- Persistence & Query ---\n")

    ;; Read back from disk
    (let ((read-entry (audit-read 'sequence: 1)))
      (check "read entry by sequence" read-entry)
      (when read-entry
        (check "read entry id matches"
          (string=? (entry-id read-entry) (entry-id entry)))))

    ;; All entries
    (let ((all (audit-all-entries)))
      (check "all entries count" (= (length all) 2)))

    ;; Query by type
    (let ((results (audit-query (audit-all-entries) '(type test-action))))
      (check "query by type" (= (length results) 1)))

    (let ((results (audit-query (audit-all-entries) '(type seal-commit))))
      (check "query seal-commit" (= (length results) 1)))

    ;; Query by object
    (let ((results (audit-query (audit-all-entries) '(object "vault.sls"))))
      (check "query by object" (= (length results) 1)))

    ;; ============================================================
    ;; Summary
    ;; ============================================================

    (printf "\n--- Summary ---\n")

    (let ((groups (audit-group-by (audit-all-entries) 'type)))
      (check "group-by type" (= (length groups) 2)))

    ;; audit-summary just prints, check it doesn't crash
    (guard (exn [#t (check "audit-summary" #f)])
      (audit-summary (audit-all-entries))
      (check "audit-summary" #t))))

;; ============================================================
;; Cleanup
;; ============================================================

;; Remove test files
(guard (exn [#t (void)])
  (for-each
    (lambda (f)
      (guard (exn [#t (void)])
        (delete-file (string-append "/tmp/cyberspace-audit-test/" f))))
    '("1.sexp" "2.sexp")))

;; ============================================================
;; Results
;; ============================================================

(printf "\n=== Results: ~a passed, ~a failed ===\n\n" *pass* *fail*)

(if (= *fail* 0)
    (printf "Audit: GO\n\n")
    (begin
      (printf "Audit: FAIL\n\n")
      (exit 1)))
