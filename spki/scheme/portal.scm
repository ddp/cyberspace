;;; portal.scm - Session lifecycle: crossing into and out of Cyberspace
;;;
;;; Tracks session statistics, provides the goodbye message, and manages
;;; the portal between objective reality and Cyberspace.
;;;
;;; Heritage: VMS SYS$SYSTEM:LOGINOUT.EXE (with LGI$ callouts by COVERT::COVERT)
;;; RFC-054 Terminal Interface Conventions
;;;
;;; Copyright (c) 2026 Derrell Piper. See LICENSE.

(module portal
  (;; Session statistics (primitives in os module)
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

  (import scheme
          (chicken base)
          (chicken format)
          (chicken file)
          (chicken string)
          (chicken time)
          (chicken time posix)
          (chicken type)  ; for type declarations
          srfi-1
          srfi-13
          srfi-69
          os)

  ;;; ============================================================
  ;;; Type Declarations
  ;;; ============================================================
  ;;
  ;; Explicit types help the scrutinizer avoid exponential inference.
  ;; Ada got this right: declare everything, infer nothing.

  (: format-duration (fixnum -> string))
  (: format-bytes (number -> string))
  (: session-summary (-> (list-of string)))
  (: session-uptime (-> fixnum))
  (: count-vault-items (string -> fixnum))
  (: audit-load-entries-raw (-> (list-of string)))
  (: goodbye (#!optional (or false procedure) fixnum -> noreturn))

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
      (if (directory-exists? dir)
          (filter (lambda (f) (string-suffix? ".sexp" f)) (directory dir))
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
     ((< secs 60) (sprintf "~as" secs))
     ((< secs 3600) (sprintf "~am ~as" (quotient secs 60) (modulo secs 60)))
     ((< secs 86400) (sprintf "~ah ~am" (quotient secs 3600) (quotient (modulo secs 3600) 60)))
     (else (sprintf "~ad ~ah" (quotient secs 86400) (quotient (modulo secs 86400) 3600)))))

  (define (format-bytes bytes)
    "Format bytes as human-readable with SI prefixes."
    (cond
     ((< bytes 1024) (sprintf "~aB" bytes))
     ((< bytes 1048576) (sprintf "~aK" (quotient bytes 1024)))
     ((< bytes 1073741824)
      ;; Manual 1 decimal place: multiply by 10, round, divide by 10
      (let* ((mb (/ bytes 1048576.0))
             (rounded (/ (round (* mb 10)) 10.0)))
        (sprintf "~aM" rounded)))
     (else
      ;; Manual 2 decimal places
      (let* ((gb (/ bytes 1073741824.0))
             (rounded (/ (round (* gb 100)) 100.0)))
        (sprintf "~aG" rounded)))))

  ;;; ============================================================
  ;;; Session Summary Helpers
  ;;; ============================================================
  ;;
  ;; Small typed helpers avoid exponential type inference.
  ;; Each returns string or #f, composed via filter.

  (: format-stat (symbol string string -> (or string false)))
  (define (format-stat key singular plural-suffix)
    "Format a session stat with pluralization, or #f if zero."
    (let ((n (session-stat key)))
      (if (> n 0)
          (string-append (number->string n) " " singular
                         (if (= n 1) "" plural-suffix))
          #f)))

  (: format-stat-irregular (symbol string string -> (or string false)))
  (define (format-stat-irregular key singular plural)
    "Format a session stat with irregular plural, or #f if zero."
    (let ((n (session-stat key)))
      (if (> n 0)
          (string-append (number->string n) " " (if (= n 1) singular plural))
          #f)))

  (: format-stat-fixed (symbol string -> (or string false)))
  (define (format-stat-fixed key label)
    "Format a session stat with fixed label (no pluralization), or #f if zero."
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
           (new-audits (- (length (audit-load-entries-raw)) (session-stat 'boot-audit-count)))
           (boot-weave (session-stat 'boot-weave)))
      ;; Collect all stats, filter out #f values
      (filter identity
        (list
          ;; Always show uptime
          (format-duration uptime)
          ;; Weave score
          (and (> boot-weave 0)
               (string-append (number->string (inexact->exact (round boot-weave))) " weave"))
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

  ;;; ============================================================
  ;;; Vault Helpers
  ;;; ============================================================

  (define (count-vault-items subdir)
    "Count items in vault subdirectory"
    (let ((path (string-append ".vault/" subdir)))
      (if (directory-exists? path)
          (length (filter (lambda (f) (not (string-prefix? "." f)))
                          (directory path)))
          0)))

  ;;; ============================================================
  ;;; Goodbye Helpers
  ;;; ============================================================

  (: pad2 (fixnum -> string))
  (define (pad2 n)
    "Pad number to 2 digits."
    (string-pad-left (number->string n) 2 #\0))

  (: format-utc-timestamp (vector -> string))
  (define (format-utc-timestamp utc)
    "Format UTC time vector as ISO timestamp."
    (sprintf "~a-~a-~a ~a:~a:~aZ"
             (+ 1900 (vector-ref utc 5))
             (pad2 (+ 1 (vector-ref utc 4)))
             (pad2 (vector-ref utc 3))
             (pad2 (vector-ref utc 2))
             (pad2 (vector-ref utc 1))
             (pad2 (vector-ref utc 0))))

  (: format-local-timestamp (vector -> string))
  (define (format-local-timestamp local)
    "Format local time vector as HH:MM:SS TZ."
    (sprintf "~a:~a:~a ~a"
             (pad2 (vector-ref local 2))
             (pad2 (vector-ref local 1))
             (pad2 (vector-ref local 0))
             (time->string local "%Z")))

  (: format-freeze-timestamp (-> string))
  (define (format-freeze-timestamp)
    "Format current time as 'UTC (local)' for goodbye."
    (let* ((secs (current-seconds))
           (utc (seconds->utc-time secs))
           (local (seconds->local-time secs)))
      (sprintf "~a (~a)" (format-utc-timestamp utc) (format-local-timestamp local))))

  (: vault-summary (-> (list-of string)))
  (define (vault-summary)
    "Generate vault state summary."
    (let ((obj-count (count-vault-items "objects"))
          (key-count (count-vault-items "keys")))
      (filter identity
        (list (and (> obj-count 0) (sprintf "~a objects" obj-count))
              (and (> key-count 0) (sprintf "~a keys" key-count))))))

  (: drain-input (-> undefined))
  (define (drain-input)
    "Drain pending input to avoid escape codes leaking to shell."
    (when (char-ready?) (read-char) (drain-input)))

  ;;; ============================================================
  ;;; Goodbye
  ;;; ============================================================

  (define (goodbye #!optional (history-save-proc #f) (verbosity 1))
    "Exit Cyberspace with farewell message and session summary.
     Verbosity 0 (shadow) exits silently; higher levels show the banner."
    (when history-save-proc (history-save-proc))
    (when (> verbosity 0)  ; shadow mode: silent exit
      (let* ((date-str (format-freeze-timestamp))
             (all-parts (append (session-summary) (vault-summary))))
        (print "")
        (if (null? all-parts)
            (printf "Cyberspace frozen at ~a on ~a.~n" date-str (hostname))
            (printf "Cyberspace frozen at ~a on ~a.~n  Session: ~a~n"
                    date-str (hostname) (string-intersperse all-parts " · ")))
        (print "")))
    (flush-output)
    (drain-input)
    (exit 0))

) ;; end module portal
