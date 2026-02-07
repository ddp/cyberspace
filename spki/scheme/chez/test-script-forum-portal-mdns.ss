;;; Script + Forum + Portal + mDNS Test Suite
;;; Library of Cyberspace - Chez Port
;;;
;;; Run: CHEZSCHEMELIBDIRS=. chez --program test-script-forum-portal-mdns.ss

(import (rnrs)
        (only (chezscheme) printf format void
              file-exists? delete-file
              directory-list system)
        (cyberspace chicken-compatibility chicken)
        (cyberspace chicken-compatibility hashtable)
        (cyberspace crypto-ffi)
        (cyberspace cert)
        (cyberspace os)
        (cyberspace script)
        (cyberspace forum)
        (cyberspace portal)
        (cyberspace mdns))

;; ============================================================
;; Test harness
;; ============================================================

(define *pass* 0)
(define *fail* 0)

(define (check name ok?)
  (if ok?
      (begin
        (printf "  pass ~a~%" name)
        (set! *pass* (+ *pass* 1)))
      (begin
        (printf "  FAIL ~a~%" name)
        (set! *fail* (+ *fail* 1)))))

(printf "~%=== Script + Forum + Portal + mDNS Test Suite ===~%~%")

;; Init sodium
(sodium-init)

;; ============================================================
;; Script Tests
;; ============================================================

(printf "--- Script Signing ---~%")

;; Generate keypair
(let* ((keys (ed25519-keypair))
       (pub (car keys))
       (priv (cadr keys))
       (content "#!/usr/bin/env cyberspace\n(display \"hello\")\n"))

  ;; Sign script
  (let ((sig (sign-script content priv pub)))
    (check "sign-script" (script-signature? sig))
    (check "signature-signer" (bytevector? (signature-signer sig)))
    (check "signature-value" (bytevector? (signature-value sig)))
    (check "signature-timestamp" (number? (signature-timestamp sig)))

    ;; Verify
    (check "verify-script valid" (verify-script content sig))
    (check "verify-script tampered" (not (verify-script "tampered!" sig))))

  ;; Sign without explicit public key
  (let ((sig2 (sign-script content priv)))
    (check "sign without pubkey" (script-signature? sig2))
    (check "verify without pubkey" (verify-script content sig2)))

  ;; Threshold signatures
  (let* ((keys2 (ed25519-keypair))
         (pub2 (car keys2))
         (priv2 (cadr keys2))
         (keys3 (ed25519-keypair))
         (pub3 (car keys3))
         (priv3 (cadr keys3))
         (sigs (threshold-sign-script content
                 (list priv pub priv2)  ; Wrong - testing error
                 (list pub pub2 pub3))))
    ;; Note: priv is 64 bytes, pub is 32 bytes, so signing with pub will
    ;; produce garbage, but the list lengths match (3 each)
    (check "threshold-sign count" (= (length sigs) 3)))

  ;; Proper threshold test
  (let* ((keys2 (ed25519-keypair))
         (pub2 (car keys2))
         (priv2 (cadr keys2))
         (sigs (threshold-sign-script content
                 (list priv priv2)
                 (list pub pub2))))
    (check "threshold 2-of-2 valid"
      (verify-threshold-script content sigs 2))
    (check "threshold 1-of-2 valid"
      (verify-threshold-script content sigs 1))
    ;; Remove one signature
    (check "threshold 2-of-1 fails"
      (not (verify-threshold-script content (list (car sigs)) 2))))

  ;; Mismatched key lists
  (check "threshold mismatched keys"
    (guard (exn (#t #t))
      (threshold-sign-script content (list priv) (list pub pub))
      #f)))

;; ============================================================
;; Forum Tests
;; ============================================================

(printf "~%--- Forum ---~%")

;; Set up test forum directory
(define test-forum-path ".vault/forum-test")
(set! *forum-path* test-forum-path)
(system (string-append "rm -rf " test-forum-path))

;; Ensure forum creates directory
(check "forum-path set" (string=? *forum-path* test-forum-path))

;; Post a topic
(let ((num (post "Test subject" "This is the body of topic 1.")))
  (check "post returns number" (number? num))
  (check "post topic 1" (= num 1))
  (check "current-topic set" (= *current-topic* 1)))

;; Post another
(let ((num (post "Second topic" "Body of topic 2.")))
  (check "post topic 2" (= num 2)))

;; Load and verify topic structure
(let ((t (with-input-from-file (string-append test-forum-path "/1.sexp") read)))
  (check "topic structure" (eq? (car t) 'topic))
  (check "topic number" (= (cadr (assq 'number (cdr t))) 1))
  (check "topic subject" (string=? (cadr (assq 'subject (cdr t))) "Test subject"))
  (check "topic body" (string=? (cadr (assq 'body (cdr t))) "This is the body of topic 1.")))

;; Read topic
(read-topic 1)
(check "read-topic sets current" (= *current-topic* 1))

;; Read nonexistent
(read-topic 999)
(check "read nonexistent ok" #t)  ; should not error

;; Reply
(reply "This is a reply to topic 1.")
(let ((t (with-input-from-file (string-append test-forum-path "/1.sexp") read)))
  (let ((replies (cadr (assq 'replies (cdr t)))))
    (check "reply added" (= (length replies) 1))
    (check "reply body" (string=? (cadr (assq 'body (car replies)))
                                  "This is a reply to topic 1."))))

;; Reply again
(reply "Second reply.")
(let ((t (with-input-from-file (string-append test-forum-path "/1.sexp") read)))
  (let ((replies (cadr (assq 'replies (cdr t)))))
    (check "two replies" (= (length replies) 2))))

;; Topics listing (just verify it runs)
(topics 5)
(check "topics listing ok" #t)

;; Forum overview
(forum)
(check "forum overview ok" #t)

;; Note alias
(note 1)
(check "note alias" (= *current-topic* 1))

;; Clean up test forum
(system (string-append "rm -rf " test-forum-path))

;; ============================================================
;; Portal Tests
;; ============================================================

(printf "~%--- Portal ---~%")

;; Initialize session stats
(session-stat-init!)
(check "session-stat-init!" #t)

;; Verify boot-time was set
(check "boot-time set" (> (session-stat 'boot-time) 0))

;; Stats initialized to zero
(check "reads init 0" (= (session-stat 'reads) 0))
(check "writes init 0" (= (session-stat 'writes) 0))
(check "hashes init 0" (= (session-stat 'hashes) 0))
(check "commands init 0" (= (session-stat 'commands) 0))

;; Increment stats
(session-stat! 'reads)
(session-stat! 'reads)
(session-stat! 'hashes)
(check "reads incremented" (= (session-stat 'reads) 2))
(check "hashes incremented" (= (session-stat 'hashes) 1))

;; Uptime
(let ((up (session-uptime)))
  (check "session-uptime" (>= up 0)))

;; Format duration
(check "format-duration seconds" (string=? (format-duration 42) "42s"))
(check "format-duration minutes" (string=? (format-duration 125) "2m 5s"))
(check "format-duration hours" (string=? (format-duration 7380) "2h 3m"))
(check "format-duration days" (string=? (format-duration 90000) "1d 1h"))

;; Format bytes
(check "format-bytes B" (string=? (format-bytes 512) "512B"))
(check "format-bytes K" (string=? (format-bytes 2048) "2K"))

;; Session summary
(let ((summary (session-summary)))
  (check "session-summary list" (list? summary))
  (check "summary has uptime" (pair? summary)))

;; Count vault items (may or may not exist)
(check "count-vault-items" (number? (count-vault-items "objects")))

;; Audit load raw
(check "audit-load-entries-raw" (list? (audit-load-entries-raw)))

;; ============================================================
;; mDNS Tests
;; ============================================================

(printf "~%--- mDNS ---~%")

;; Constants
(check "mdns-port" (= mdns-port 5353))
(check "enrollment-port" (= enrollment-port 7654))
(check "cyberspace-service" (string=? cyberspace-service "_cyberspace._tcp"))

;; Status
(let ((status (mdns-status)))
  (check "mdns-status" (pair? status))
  (check "bonjour not registered" (not (cdr (assq 'bonjour-registered status))))
  (check "listener not active" (not (cdr (assq 'listener-active status)))))

;; Cleanup stale (should be no-op)
(cleanup-stale-bonjour)
(check "cleanup-stale ok" #t)

;; Shutdown (no-op when nothing running)
(mdns-shutdown!)
(check "mdns-shutdown! ok" #t)

;; Browse (will find nothing on this machine, but should not error)
;; Skip if dns-sd not available
(let ((has-dns-sd (file-exists? "/usr/bin/dns-sd")))
  (if has-dns-sd
      (let ((results (bonjour-browse 1)))
        (check "bonjour-browse returns list" (list? results)))
      (check "dns-sd not available (skip browse)" #t)))

;; Enrollment channel helpers (test close with #f)
(enrollment-close #f #f)
(check "enrollment-close nil ok" #t)

;; Enrollment receive from #f
(check "enrollment-receive nil" (not (enrollment-receive #f)))

;; ============================================================
;; Results
;; ============================================================

(printf "~%=== Results: ~a passed, ~a failed ===~%~%" *pass* *fail*)

(if (= *fail* 0)
    (printf "Script+Forum+Portal+mDNS: GO~%~%")
    (begin
      (printf "Script+Forum+Portal+mDNS: FAIL~%~%")
      (exit 1)))
