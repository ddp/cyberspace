;;; portal.scm - Session lifecycle: crossing into and out of Cyberspace
;;; Library of Cyberspace - Chez Port
;;;
;;; They enter through gates, some call them portals, into lambda land,
;;; where we teleport through wormholes in the fabric of the weave.
;;;
;;; Tracks session statistics, provides the goodbye message, and manages
;;; the portal between objective reality and Cyberspace.
;;;
;;; Heritage: VMS SYS$SYSTEM:LOGINOUT.EXE (with LGI$ callouts by COVERT::COVERT)
;;; Memo-054 Terminal Interface Conventions

(library (cyberspace portal)
  (export
    ;; Session statistics (primitives in os module)
    session-stat-init!
    session-uptime
    session-summary

    ;; Formatting helpers
    format-duration
    format-bytes

    ;; Exit
    goodbye

    ;; Internal (for REPL)
    count-vault-items
    audit-load-entries-raw)

  (import (rnrs)
          (only (chezscheme)
                printf format void
                file-exists? directory-list
                flush-output-port
                current-time time-second
                exit)
          (cyberspace chicken-compatibility chicken)
          (cyberspace chicken-compatibility hashtable)
          (cyberspace os))

  ;;; ============================================================
  ;;; Session Statistics
  ;;; ============================================================
  ;;
  ;; *session-stats*, session-stat!, session-stat are imported from os.
  ;; This allows cross-module instrumentation at any level.

  (define (init-stats-boot!)
    "Initialize boot-time statistics."
    (hash-table-set! *session-stats* 'boot-time (current-seconds))
    (hash-table-set! *session-stats* 'boot-audit-count (length (audit-load-entries-raw)))
    (hash-table-set! *session-stats* 'boot-weave 0)
    (hash-table-set! *session-stats* 'commands 0))

  (define (init-stats-vault!)
    "Initialize vault operation counters."
    (for-each (lambda (k) (hash-table-set! *session-stats* k 0))
              '(unlocks reads writes bytes-written deletes queries)))

  (define (init-stats-crypto!)
    "Initialize cryptographic operation counters."
    (for-each (lambda (k) (hash-table-set! *session-stats* k 0))
              '(hashes signs verifies encrypts decrypts)))

  (define (init-stats-seal!)
    "Initialize seal operation counters."
    (for-each (lambda (k) (hash-table-set! *session-stats* k 0))
              '(commits seals syncs)))

  (define (init-stats-federation!)
    "Initialize federation counters."
    (for-each (lambda (k) (hash-table-set! *session-stats* k 0))
              '(peers-discovered gossip-exchanges votes federation-changes channels handshakes)))

  (define (init-stats-network!)
    "Initialize network counters."
    (for-each (lambda (k) (hash-table-set! *session-stats* k 0))
              '(mdns-messages)))

  (define (init-stats-errors!)
    "Initialize error counters."
    (for-each (lambda (k) (hash-table-set! *session-stats* k 0))
              '(verify-fails auth-fails timeouts wormholes)))

  (define (session-stat-init!)
    "Initialize session statistics at boot."
    (init-stats-boot!)
    (init-stats-vault!)
    (init-stats-crypto!)
    (init-stats-seal!)
    (init-stats-federation!)
    (init-stats-network!)
    (init-stats-errors!))

  (define (audit-load-entries-raw)
    "Load audit entry count without parsing (for boot stats)."
    (let ((dir ".vault/audit"))
      (if (file-exists? dir)
          (filter (lambda (f) (string-suffix? ".sexp" f))
                  (directory-list dir))
          '())))

  (define (session-uptime)
    "Get session uptime in seconds."
    (- (current-seconds) (session-stat 'boot-time)))

  ;;; ============================================================
  ;;; Formatting Helpers
  ;;; ============================================================

  (define (format-duration secs)
    "Format seconds as human-readable duration."
    (cond
     ((< secs 60) (string-append (number->string secs) "s"))
     ((< secs 3600)
      (string-append (number->string (quotient secs 60)) "m "
                     (number->string (modulo secs 60)) "s"))
     ((< secs 86400)
      (string-append (number->string (quotient secs 3600)) "h "
                     (number->string (quotient (modulo secs 3600) 60)) "m"))
     (else
      (string-append (number->string (quotient secs 86400)) "d "
                     (number->string (quotient (modulo secs 86400) 3600)) "h"))))

  (define (format-bytes bytes)
    "Format bytes as human-readable with SI prefixes."
    (cond
     ((< bytes 1024)
      (string-append (number->string bytes) "B"))
     ((< bytes 1048576)
      (string-append (number->string (quotient bytes 1024)) "K"))
     ((< bytes 1073741824)
      (let* ((mb (/ bytes 1048576.0))
             (rounded (/ (round (* mb 10)) 10.0)))
        (string-append (number->string rounded) "M")))
     (else
      (let* ((gb (/ bytes 1073741824.0))
             (rounded (/ (round (* gb 100)) 100.0)))
        (string-append (number->string rounded) "G")))))

  ;;; ============================================================
  ;;; Session Summary Helpers
  ;;; ============================================================

  (define (format-stat key singular plural-suffix)
    "Format a session stat with pluralization, or #f if zero."
    (let ((n (session-stat key)))
      (if (> n 0)
          (string-append (number->string n) " " singular
                         (if (= n 1) "" plural-suffix))
          #f)))

  (define (format-stat-irregular key singular plural)
    "Format a session stat with irregular plural, or #f if zero."
    (let ((n (session-stat key)))
      (if (> n 0)
          (string-append (number->string n) " " (if (= n 1) singular plural))
          #f)))

  (define (format-stat-fixed key label)
    "Format a session stat with fixed label, or #f if zero."
    (let ((n (session-stat key)))
      (if (> n 0)
          (string-append (number->string n) " " label)
          #f)))

  ;;; ============================================================
  ;;; Session Summary
  ;;; ============================================================

  (define (session-summary)
    "Generate session statistics summary for goodbye."
    (let* ((uptime (session-uptime))
           (new-audits (- (length (audit-load-entries-raw))
                          (session-stat 'boot-audit-count)))
           (boot-weave (session-stat 'boot-weave)))
      ;; Collect all stats, filter out #f values
      (filter (lambda (x) x)
        (list
          ;; Always show uptime
          (format-duration uptime)
          ;; Vault I/O
          (format-stat 'unlocks "unlock" "s")
          (format-stat 'reads "read" "s")
          (format-stat 'writes "write" "s")
          (let ((bw (session-stat 'bytes-written)))
            (and (> bw 0) (string-append (format-bytes bw) " written")))
          (format-stat-irregular 'queries "query" "queries")
          ;; Crypto ops
          (format-stat 'hashes "hash" "es")
          (format-stat 'signs "sign" "s")
          (format-stat-irregular 'verifies "verify" "verifies")
          (format-stat 'encrypts "encrypt" "s")
          (format-stat 'decrypts "decrypt" "s")
          ;; Seal ops
          (format-stat 'commits "commit" "s")
          (format-stat 'syncs "replication" "s")
          (format-stat 'peers-discovered "peer" "s")
          (format-stat 'votes "vote" "s")
          (format-stat-fixed 'gossip-exchanges "gossip")
          (format-stat-fixed 'mdns-messages "mDNS")
          (format-stat 'seals "seal" "s")
          (format-stat 'federation-changes "fed" "s")
          (format-stat 'wormholes "wormhole" "s")
          ;; Audits
          (and (> new-audits 0)
               (string-append "+" (number->string new-audits) " audit"))
          ;; Channels & handshakes
          (format-stat 'channels "channel" "s")
          (format-stat 'handshakes "handshake" "s")
          ;; Errors
          (format-stat 'verify-fails "verify-fail" "s!")
          (format-stat 'auth-fails "auth-fail" "s!")
          (format-stat 'timeouts "timeout" "s")))))

  ;;; ============================================================
  ;;; Vault Helpers
  ;;; ============================================================

  (define (count-vault-items subdir)
    "Count items in vault subdirectory"
    (let ((path (string-append ".vault/" subdir)))
      (if (file-exists? path)
          (length (filter (lambda (f) (not (string-prefix? "." f)))
                          (directory-list path)))
          0)))

  ;;; ============================================================
  ;;; Goodbye Helpers
  ;;; ============================================================

  (define (seconds->timestamp secs)
    "Format epoch seconds to ISO-8601 timestamp (Hinnant's algorithm)."
    (let* ((z (+ (quotient secs 86400) 719468))
           (era (quotient (if (>= z 0) z (- z 146096)) 146097))
           (doe (- z (* era 146097)))
           (yoe (quotient (- doe (+ (quotient doe 1460)
                                    (- (quotient doe 36524))
                                    (quotient doe 146096)))
                          365))
           (y (+ yoe (* era 400)))
           (doy (- doe (- (+ (* 365 yoe) (quotient yoe 4))
                          (quotient yoe 100))))
           (mp (quotient (+ (* 5 doy) 2) 153))
           (d (+ (- doy (quotient (+ (* 153 mp) 2) 5)) 1))
           (m (+ mp (if (< mp 10) 3 -9)))
           (y* (+ y (if (<= m 2) 1 0)))
           (time-of-day (modulo secs 86400))
           (hh (quotient time-of-day 3600))
           (mm (quotient (modulo time-of-day 3600) 60))
           (ss (modulo time-of-day 60)))
      (string-append
        (number->string y*) "-"
        (if (< m 10) "0" "") (number->string m) "-"
        (if (< d 10) "0" "") (number->string d) " "
        (if (< hh 10) "0" "") (number->string hh) ":"
        (if (< mm 10) "0" "") (number->string mm) ":"
        (if (< ss 10) "0" "") (number->string ss) "Z")))

  (define (vault-summary)
    "Generate vault state summary."
    (let ((obj-count (count-vault-items "objects"))
          (key-count (count-vault-items "keys")))
      (filter (lambda (x) x)
        (list (and (> obj-count 0)
                   (string-append (number->string obj-count) " "
                                  (if (= obj-count 1) "object" "objects")))
              (and (> key-count 0)
                   (string-append (number->string key-count) " "
                                  (if (= key-count 1) "key" "keys")))))))

  ;;; ============================================================
  ;;; Goodbye
  ;;; ============================================================

  (define (goodbye . rest)
    "Exit Cyberspace with farewell message and session summary.
     Optional: history-save-proc, verbosity (default 1).
     Verbosity 0 (shadow) exits silently."
    (let ((history-save-proc (if (null? rest) #f (car rest)))
          (verbosity (if (or (null? rest) (null? (cdr rest))) 1 (cadr rest))))
      (when history-save-proc (history-save-proc))
      (when (> verbosity 0)
        (let* ((date-str (seconds->timestamp (current-seconds)))
               (host (hostname))
               (boot-weave (session-stat 'boot-weave))
               (weave-str (if (> boot-weave 0)
                              (string-append " (weaving at "
                                             (number->string (exact (round boot-weave)))
                                             " SHA-512/ms)")
                              ""))
               (all-parts (append (session-summary) (vault-summary))))
          (print "")
          (if (null? all-parts)
              (printf "Cyberspace frozen at ~a on ~a~a.~%" date-str host weave-str)
              (printf "Cyberspace frozen at ~a on ~a~a.~%  Session: ~a~%"
                      date-str host weave-str
                      (string-intersperse all-parts " \xb7 ")))
          (print "")))
      (run-cleanup-hooks!)
      (flush-output-port (current-output-port))
      (exit 0)))

) ;; end library
