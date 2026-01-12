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
  (: goodbye (#!optional (or false procedure) -> noreturn))

  ;;; ============================================================
  ;;; Session Statistics
  ;;; ============================================================
  ;;
  ;; *session-stats*, session-stat!, session-stat are imported from os.
  ;; This allows cross-module instrumentation at any level.

  (define (session-stat-init!)
    "Initialize session statistics at boot."
    (hash-table-set! *session-stats* 'boot-time (current-seconds))
    (hash-table-set! *session-stats* 'boot-audit-count (length (audit-load-entries-raw)))
    (hash-table-set! *session-stats* 'boot-weave 0)
    ;; Commands
    (hash-table-set! *session-stats* 'commands 0)
    ;; Vault operations
    (hash-table-set! *session-stats* 'unlocks 0)
    (hash-table-set! *session-stats* 'reads 0)
    (hash-table-set! *session-stats* 'writes 0)
    (hash-table-set! *session-stats* 'bytes-written 0)
    (hash-table-set! *session-stats* 'deletes 0)
    (hash-table-set! *session-stats* 'queries 0)
    ;; Crypto operations
    (hash-table-set! *session-stats* 'hashes 0)
    (hash-table-set! *session-stats* 'signs 0)
    (hash-table-set! *session-stats* 'verifies 0)
    (hash-table-set! *session-stats* 'encrypts 0)
    (hash-table-set! *session-stats* 'decrypts 0)
    ;; Seal operations
    (hash-table-set! *session-stats* 'commits 0)
    (hash-table-set! *session-stats* 'seals 0)
    (hash-table-set! *session-stats* 'syncs 0)
    ;; Federation
    (hash-table-set! *session-stats* 'peers-discovered 0)
    (hash-table-set! *session-stats* 'gossip-exchanges 0)
    (hash-table-set! *session-stats* 'votes 0)
    (hash-table-set! *session-stats* 'federation-changes 0)
    (hash-table-set! *session-stats* 'channels 0)
    (hash-table-set! *session-stats* 'handshakes 0)
    ;; Network I/O
    (hash-table-set! *session-stats* 'bytes-in 0)
    (hash-table-set! *session-stats* 'bytes-out 0)
    (hash-table-set! *session-stats* 'packets-ipv4 0)
    (hash-table-set! *session-stats* 'packets-ipv6 0)
    (hash-table-set! *session-stats* 'mdns-messages 0)
    ;; Errors (hopefully zero)
    (hash-table-set! *session-stats* 'verify-fails 0)
    (hash-table-set! *session-stats* 'auth-fails 0)
    (hash-table-set! *session-stats* 'timeouts 0)
    ;; Navigation
    (hash-table-set! *session-stats* 'wormholes 0))

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
           (boot-weave (session-stat 'boot-weave))
           (bytes-in (session-stat 'bytes-in))
           (bytes-out (session-stat 'bytes-out))
           (ipv4 (session-stat 'packets-ipv4))
           (ipv6 (session-stat 'packets-ipv6)))
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
          ;; Network I/O
          (and (or (> bytes-in 0) (> bytes-out 0))
               (string-append "↓" (format-bytes bytes-in) " ↑" (format-bytes bytes-out)))
          ;; Packet counts
          (and (> ipv4 0) (string-append (number->string ipv4) " v4"))
          (and (> ipv6 0) (string-append (number->string ipv6) " v6"))
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
  ;;; Goodbye
  ;;; ============================================================

  (define (goodbye #!optional (history-save-proc #f))
    "Exit Cyberspace with farewell message and session summary."
    ;; Save history if callback provided
    (when history-save-proc (history-save-proc))
    (let* ((secs (current-seconds))
           (utc (seconds->utc-time secs))
           (local (seconds->local-time secs))
           (utc-str (sprintf "~a-~a-~a ~a:~a:~aZ"
                            (+ 1900 (vector-ref utc 5))
                            (string-pad-left (number->string (+ 1 (vector-ref utc 4))) 2 #\0)
                            (string-pad-left (number->string (vector-ref utc 3)) 2 #\0)
                            (string-pad-left (number->string (vector-ref utc 2)) 2 #\0)
                            (string-pad-left (number->string (vector-ref utc 1)) 2 #\0)
                            (string-pad-left (number->string (vector-ref utc 0)) 2 #\0)))
           (local-str (sprintf "~a:~a:~a ~a"
                              (string-pad-left (number->string (vector-ref local 2)) 2 #\0)
                              (string-pad-left (number->string (vector-ref local 1)) 2 #\0)
                              (string-pad-left (number->string (vector-ref local 0)) 2 #\0)
                              (time->string local "%Z")))
           (date-str (sprintf "~a (~a)" utc-str local-str))
           ;; Session statistics
           (session-parts (session-summary))
           ;; Vault state
           (obj-count (count-vault-items "objects"))
           (key-count (count-vault-items "keys"))
           (vault-parts (filter identity
                          (list
                            (and (> obj-count 0) (sprintf "~a objects" obj-count))
                            (and (> key-count 0) (sprintf "~a keys" key-count)))))
           ;; Combine session stats and vault state
           (all-parts (append session-parts vault-parts)))
      (print "")
      (if (null? all-parts)
          (printf "Cyberspace frozen at ~a on ~a.~n" date-str (hostname))
          (printf "Cyberspace frozen at ~a on ~a.~n  Session: ~a~n"
                  date-str
                  (hostname)
                  (string-intersperse all-parts " · ")))
      (print "")
      (flush-output)
      ;; Drain any pending input to avoid escape codes leaking to shell
      (let drain () (when (char-ready?) (read-char) (drain)))
      (exit 0)))

) ;; end module portal
