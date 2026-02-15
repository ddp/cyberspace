;;; portal.sls - Session lifecycle: crossing into and out of Cyberspace
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
;;;
;;; Ported from Chicken's portal.scm.
;;; Changes: module -> library, (: ...) type decls stripped,
;;;          seconds->utc-time/local-time -> date(1) shell,
;;;          *session-stats* direct access -> session-stat!/session-stat,
;;;          signal handlers -> no-op (Chez lacks arbitrary signal support),
;;;          #!optional -> get-opt, sprintf -> format, quotient/modulo -> div/mod.

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

    ;; Signal handlers
    install-signal-handlers!

    ;; Internal (for REPL)
    count-vault-items
    audit-load-entries-raw)

  (import (except (rnrs) exit)
          (only (chezscheme)
                printf format void exit char-ready?)
          (cyberspace os)
          (cyberspace chicken-compatibility chicken)
          (only (cyberspace chicken-compatibility file)
                directory-exists? directory current-seconds)
          (only (cyberspace chicken-compatibility process)
                with-input-from-pipe read-line))

  ;; ============================================================
  ;; Inline Helpers
  ;; ============================================================

  (define (string-suffix? suffix str)
    (let ((slen (string-length str))
          (xlen (string-length suffix)))
      (and (>= slen xlen)
           (string=? (substring str (- slen xlen) slen) suffix))))

  (define (string-prefix? prefix str)
    (and (>= (string-length str) (string-length prefix))
         (string=? (substring str 0 (string-length prefix)) prefix)))

  ;; ============================================================
  ;; Session Statistics
  ;; ============================================================
  ;;
  ;; *session-stats* is not exported from os.sls (R6RS forbids
  ;; exporting assigned variables). Use session-stat!/session-stat.

  (define (init-stats-boot!)
    (session-stat! 'boot-time (current-seconds))
    (session-stat! 'boot-audit-count (length (audit-load-entries-raw)))
    (session-stat! 'boot-weave 0)
    (session-stat! 'commands 0))

  (define (init-stats-vault!)
    (for-each (lambda (k) (session-stat! k 0))
              '(unlocks reads writes bytes-written deletes queries)))

  (define (init-stats-crypto!)
    (for-each (lambda (k) (session-stat! k 0))
              '(hashes signs verifies encrypts decrypts)))

  (define (init-stats-seal!)
    (for-each (lambda (k) (session-stat! k 0))
              '(commits seals syncs)))

  (define (init-stats-federation!)
    (for-each (lambda (k) (session-stat! k 0))
              '(peers-discovered gossip-exchanges votes federation-changes channels handshakes)))

  (define (init-stats-network!)
    (for-each (lambda (k) (session-stat! k 0))
              '(mdns-messages)))

  (define (init-stats-errors!)
    (for-each (lambda (k) (session-stat! k 0))
              '(verify-fails auth-fails timeouts wormholes)))

  (define (session-stat-init!)
    (init-stats-boot!)
    (init-stats-vault!)
    (init-stats-crypto!)
    (init-stats-seal!)
    (init-stats-federation!)
    (init-stats-network!)
    (init-stats-errors!))

  (define (audit-load-entries-raw)
    (let ((dir ".vault/audit"))
      (if (directory-exists? dir)
          (filter (lambda (f) (string-suffix? ".sexp" f)) (directory dir))
          '())))

  (define (session-uptime)
    (- (current-seconds) (session-stat 'boot-time)))

  ;; ============================================================
  ;; Formatting Helpers
  ;; ============================================================

  (define (format-duration secs)
    (cond
     ((< secs 60) (format #f "~as" secs))
     ((< secs 3600) (format #f "~am ~as" (div secs 60) (mod secs 60)))
     ((< secs 86400) (format #f "~ah ~am" (div secs 3600) (div (mod secs 3600) 60)))
     (else (format #f "~ad ~ah" (div secs 86400) (div (mod secs 86400) 3600)))))

  (define (format-bytes bytes)
    (cond
     ((< bytes 1024) (format #f "~aB" bytes))
     ((< bytes 1048576) (format #f "~aK" (div bytes 1024)))
     ((< bytes 1073741824)
      (let* ((mb (/ bytes 1048576.0))
             (rounded (/ (round (* mb 10)) 10.0)))
        (format #f "~aM" rounded)))
     (else
      (let* ((gb (/ bytes 1073741824.0))
             (rounded (/ (round (* gb 100)) 100.0)))
        (format #f "~aG" rounded)))))

  ;; ============================================================
  ;; Session Summary Helpers
  ;; ============================================================

  (define (format-stat key singular plural-suffix)
    (let ((n (session-stat key)))
      (if (> n 0)
          (string-append (number->string n) " " singular
                         (if (= n 1) "" plural-suffix))
          #f)))

  (define (format-stat-irregular key singular plural)
    (let ((n (session-stat key)))
      (if (> n 0)
          (string-append (number->string n) " " (if (= n 1) singular plural))
          #f)))

  (define (format-stat-fixed key label)
    (let ((n (session-stat key)))
      (if (> n 0)
          (string-append (number->string n) " " label)
          #f)))

  ;; ============================================================
  ;; Session Summary
  ;; ============================================================

  (define (session-summary)
    (let* ((uptime (session-uptime))
           (new-audits (- (length (audit-load-entries-raw)) (session-stat 'boot-audit-count)))
           (boot-weave (session-stat 'boot-weave)))
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
          (and (> new-audits 0) (string-append "+" (number->string new-audits) " audit"))
          ;; Channels & handshakes
          (format-stat 'channels "channel" "s")
          (format-stat 'handshakes "handshake" "s")
          ;; Errors (hopefully zero)
          (format-stat 'verify-fails "verify-fail" "s!")
          (format-stat 'auth-fails "auth-fail" "s!")
          (format-stat 'timeouts "timeout" "s")))))

  ;; ============================================================
  ;; Vault Helpers
  ;; ============================================================

  (define (count-vault-items subdir)
    (let ((path (string-append ".vault/" subdir)))
      (if (directory-exists? path)
          (length (filter (lambda (f) (not (string-prefix? "." f)))
                          (directory path)))
          0)))

  ;; ============================================================
  ;; Time Formatting
  ;; ============================================================
  ;;
  ;; Chicken uses seconds->utc-time / seconds->local-time from
  ;; (chicken time posix). Chez has no equivalent; shell out to
  ;; date(1) instead (same pattern as forum.sls).

  (define (format-freeze-timestamp)
    (guard (exn [#t "unknown time"])
      (let* ((s (number->string (exact (truncate (current-seconds)))))
             (utc (with-input-from-pipe
                    (string-append "date -u -r " s " '+%Y-%m-%d %H:%M:%SZ'")
                    read-line))
             (local (with-input-from-pipe
                      (string-append "date -r " s " '+%H:%M:%S %Z'")
                      read-line)))
        (if (and utc (not (eof-object? utc)) (not (string=? utc ""))
                 local (not (eof-object? local)) (not (string=? local "")))
            (format #f "~a (~a)" utc local)
            "unknown time"))))

  (define (vault-summary)
    (let ((obj-count (count-vault-items "objects"))
          (key-count (count-vault-items "keys")))
      (filter (lambda (x) x)
        (list (and (> obj-count 0)
                   (format #f "~a ~a" obj-count (if (= obj-count 1) "object" "objects")))
              (and (> key-count 0)
                   (format #f "~a ~a" key-count (if (= key-count 1) "key" "keys")))))))

  (define (drain-input)
    (when (char-ready?)
      (get-char (current-input-port))
      (drain-input)))

  ;; ============================================================
  ;; Signal Handlers
  ;; ============================================================
  ;;
  ;; Chez Scheme does not support arbitrary signal handlers.
  ;; Only keyboard-interrupt-handler (SIGINT) is available.
  ;; SIGTERM/SIGHUP cleanup relies on OS defaults.
  ;; When full signal support is needed, wrap via C FFI.

  (define (install-signal-handlers!)
    (void))

  ;; ============================================================
  ;; Goodbye
  ;; ============================================================

  (define (goodbye . opts)
    (let ((history-save-proc (get-opt opts 0 #f))
          (verbosity (get-opt opts 1 1)))
      (when history-save-proc (history-save-proc))
      (when (> verbosity 0)
        (let* ((date-str (format-freeze-timestamp))
               (boot-weave (session-stat 'boot-weave))
               (weave-str (if (> boot-weave 0)
                              (format #f " (weaving at ~a SHA-512/ms)"
                                      (exact (round boot-weave)))
                              ""))
               (all-parts (append (session-summary) (vault-summary))))
          (print "")
          (if (null? all-parts)
              (printf "Cyberspace frozen at ~a on ~a~a.~%" date-str (hostname) weave-str)
              (printf "Cyberspace frozen at ~a on ~a~a.~%  Session: ~a~%"
                      date-str (hostname) weave-str (string-intersperse all-parts " \x00B7; ")))
          (print "")))
      (run-cleanup-hooks!)
      (flush-output-port (current-output-port))
      (drain-input)
      (exit 0)))

) ;; end library
