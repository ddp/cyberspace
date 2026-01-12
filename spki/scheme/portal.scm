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
  (;; Session statistics
   *session-stats*
   session-stat-init!
   session-stat!
   session-stat
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
          srfi-1
          srfi-13
          srfi-69)

  ;;; ============================================================
  ;;; Session Statistics
  ;;; ============================================================

  (define *session-stats*
    (make-hash-table))

  (define (session-stat-init!)
    "Initialize session statistics at boot."
    (hash-table-set! *session-stats* 'boot-time (current-seconds))
    (hash-table-set! *session-stats* 'boot-audit-count (length (audit-load-entries-raw)))
    (hash-table-set! *session-stats* 'commands 0)
    (hash-table-set! *session-stats* 'syncs 0)
    (hash-table-set! *session-stats* 'commits 0)
    (hash-table-set! *session-stats* 'signs 0)
    (hash-table-set! *session-stats* 'verifies 0)
    (hash-table-set! *session-stats* 'queries 0)
    (hash-table-set! *session-stats* 'peers-discovered 0)
    (hash-table-set! *session-stats* 'gossip-exchanges 0)
    (hash-table-set! *session-stats* 'votes 0)
    (hash-table-set! *session-stats* 'seals 0)
    (hash-table-set! *session-stats* 'federation-changes 0)
    (hash-table-set! *session-stats* 'bytes-in 0)
    (hash-table-set! *session-stats* 'bytes-out 0)
    (hash-table-set! *session-stats* 'packets-ipv4 0)
    (hash-table-set! *session-stats* 'packets-ipv6 0)
    (hash-table-set! *session-stats* 'mdns-messages 0)
    (hash-table-set! *session-stats* 'wormholes 0)
    (hash-table-set! *session-stats* 'boot-vups 0))

  (define (audit-load-entries-raw)
    "Load audit entry count without parsing (for boot stats)."
    (let ((dir ".vault/audit"))
      (if (directory-exists? dir)
          (filter (lambda (f) (string-suffix? ".sexp" f)) (directory dir))
          '())))

  (define (session-stat! key #!optional (delta 1))
    "Increment a session statistic."
    (hash-table-set! *session-stats* key
                     (+ delta (hash-table-ref/default *session-stats* key 0))))

  (define (session-stat key)
    "Get a session statistic."
    (hash-table-ref/default *session-stats* key 0))

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
     ((< bytes 1073741824) (sprintf "~.1fM" (/ bytes 1048576.0)))
     (else (sprintf "~.2fG" (/ bytes 1073741824.0)))))

  (define (string-pad-left str len char)
    (let ((slen (string-length str)))
      (if (>= slen len)
          str
          (string-append (make-string (- len slen) char) str))))

  ;;; ============================================================
  ;;; Session Summary
  ;;; ============================================================

  (define (session-summary)
    "Generate session statistics summary for goodbye."
    (let* ((uptime (session-uptime))
           (new-audits (- (length (audit-load-entries-raw)) (session-stat 'boot-audit-count)))
           (stats '()))
      ;; Build list of notable stats - always show uptime
      (set! stats (cons (format-duration uptime) stats))
      (when (> (session-stat 'syncs) 0)
        (set! stats (cons (sprintf "~a sync~a" (session-stat 'syncs)
                                   (if (= 1 (session-stat 'syncs)) "" "s")) stats)))
      (when (> (session-stat 'commits) 0)
        (set! stats (cons (sprintf "~a commit~a" (session-stat 'commits)
                                   (if (= 1 (session-stat 'commits)) "" "s")) stats)))
      (when (> (session-stat 'signs) 0)
        (set! stats (cons (sprintf "~a sign~a" (session-stat 'signs)
                                   (if (= 1 (session-stat 'signs)) "" "s")) stats)))
      (when (> (session-stat 'verifies) 0)
        (set! stats (cons (sprintf "~a verif~a" (session-stat 'verifies)
                                   (if (= 1 (session-stat 'verifies)) "y" "ies")) stats)))
      (when (> (session-stat 'peers-discovered) 0)
        (set! stats (cons (sprintf "~a peer~a" (session-stat 'peers-discovered)
                                   (if (= 1 (session-stat 'peers-discovered)) "" "s")) stats)))
      (when (> (session-stat 'votes) 0)
        (set! stats (cons (sprintf "~a vote~a" (session-stat 'votes)
                                   (if (= 1 (session-stat 'votes)) "" "s")) stats)))
      (when (> (session-stat 'gossip-exchanges) 0)
        (set! stats (cons (sprintf "~a gossip" (session-stat 'gossip-exchanges)) stats)))
      (when (> (session-stat 'mdns-messages) 0)
        (set! stats (cons (sprintf "~a mDNS" (session-stat 'mdns-messages)) stats)))
      (when (> (session-stat 'seals) 0)
        (set! stats (cons (sprintf "~a seal~a" (session-stat 'seals)
                                   (if (= 1 (session-stat 'seals)) "" "s")) stats)))
      (when (> (session-stat 'federation-changes) 0)
        (set! stats (cons (sprintf "~a fed~a" (session-stat 'federation-changes)
                                   (if (= 1 (session-stat 'federation-changes)) "" "s")) stats)))
      (when (> (session-stat 'wormholes) 0)
        (set! stats (cons (sprintf "~a wormhole~a" (session-stat 'wormholes)
                                   (if (= 1 (session-stat 'wormholes)) "" "s")) stats)))
      ;; Network I/O - show as "↓NN ↑NN" if any traffic
      (let ((bytes-in (session-stat 'bytes-in))
            (bytes-out (session-stat 'bytes-out)))
        (when (or (> bytes-in 0) (> bytes-out 0))
          (set! stats (cons (sprintf "↓~a ↑~a" (format-bytes bytes-in) (format-bytes bytes-out)) stats))))
      ;; Packet counts by protocol
      (let ((ipv4 (session-stat 'packets-ipv4))
            (ipv6 (session-stat 'packets-ipv6)))
        (when (> ipv4 0)
          (set! stats (cons (sprintf "~a v4" ipv4) stats)))
        (when (> ipv6 0)
          (set! stats (cons (sprintf "~a v6" ipv6) stats))))
      (when (> new-audits 0)
        (set! stats (cons (sprintf "+~a audit" new-audits) stats)))
      ;; VUPS - always show boot-time benchmark
      (let ((vups (session-stat 'boot-vups)))
        (when (> vups 0)
          (set! stats (cons (sprintf "~a VUPS" vups) stats))))
      (reverse stats)))

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
    (let* ((now (seconds->local-time (current-seconds)))
           (date-str (sprintf "~a-~a-~a ~a:~a"
                             (+ 1900 (vector-ref now 5))
                             (string-pad-left (number->string (+ 1 (vector-ref now 4))) 2 #\0)
                             (string-pad-left (number->string (vector-ref now 3)) 2 #\0)
                             (string-pad-left (number->string (vector-ref now 2)) 2 #\0)
                             (string-pad-left (number->string (vector-ref now 1)) 2 #\0)))
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
          (printf "Returning to objective reality, Cyberspace frozen at ~a.~n" date-str)
          (printf "Returning to objective reality, Cyberspace frozen at ~a.~n  Session: ~a~n"
                  date-str
                  (string-intersperse all-parts " · ")))
      (print "")
      (flush-output)
      ;; Drain any pending input to avoid escape codes leaking to shell
      (let drain () (when (char-ready?) (read-char) (drain)))
      (exit 0)))

) ;; end module portal
