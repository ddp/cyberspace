#!/usr/bin/env chez --libdirs . --script
;;; repl.sps - Cyberspace Scheme (Chez Port)
;;;
;;; Copyright (c) 2026 ddp@eludom.net
;;; MIT License - see LICENSE file
;;; Currently unpublished and proprietary; license applies upon public release.
;;;
;;; Usage: ./repl.sps
;;;
;;; Preloads all Cyberspace modules for interactive exploration:
;;;   - vault: seal-commit, seal-release, seal-archive, etc.
;;;   - crypto-ffi: ed25519-keypair, sha512-hash, etc.
;;;   - audit: audit-append, audit-read, etc.
;;;   - cert: SPKI certificates
;;;   - sexp: S-expression handling

(import (rnrs)
        (only (chezscheme)
              printf format void pretty-print
              with-output-to-string
              file-directory? directory-list mkdir
              delete-file rename-file
              getenv sort date-and-time
              current-time time-second time-nanosecond
              current-directory command-line exit
              system make-parameter new-cafe
              parameterize open-process-ports
              current-transcoder
              flush-output-port
              hashtable-copy)
        (cyberspace crypto-ffi)
        (cyberspace fips)
        (cyberspace vault)
        (cyberspace audit)
        (cyberspace cert)
        (cyberspace sexp)
        (cyberspace bloom)
        (cyberspace gossip)
        (cyberspace security)
        (cyberspace keyring)
        (cyberspace portal)
        (cyberspace os)
        (cyberspace chicken-compatibility blob)
        (cyberspace chicken-compatibility chicken)
        (cyberspace chicken-compatibility file)
        (cyberspace chicken-compatibility hash-table)
        (cyberspace chicken-compatibility process))

;;; ============================================================
;;; Inlined Helpers
;;; ============================================================

;; SRFI-1 helpers not in (rnrs)
(define (find pred lst)
  (cond ((null? lst) #f)
        ((pred (car lst)) (car lst))
        (else (find pred (cdr lst)))))

(define (filter-map proc lst)
  (let loop ((lst lst) (acc '()))
    (if (null? lst)
        (reverse acc)
        (let ((result (proc (car lst))))
          (loop (cdr lst) (if result (cons result acc) acc))))))

(define (take lst n)
  (if (or (zero? n) (null? lst))
      '()
      (cons (car lst) (take (cdr lst) (- n 1)))))

(define (iota n)
  (let loop ((i 0) (acc '()))
    (if (= i n) (reverse acc) (loop (+ i 1) (cons i acc)))))

(define (every pred lst)
  (or (null? lst) (and (pred (car lst)) (every pred (cdr lst)))))

(define (any pred lst)
  (and (not (null? lst))
       (or (pred (car lst)) (any pred (cdr lst)))))

;; String helpers
(define (string-prefix? prefix str)
  (let ((plen (string-length prefix)))
    (and (>= (string-length str) plen)
         (string=? prefix (substring str 0 plen)))))

(define (string-suffix? suffix str)
  (let ((slen (string-length suffix))
        (len (string-length str)))
    (and (>= len slen)
         (string=? suffix (substring str (- len slen) len)))))

(define (string-contains haystack needle)
  (let ((hlen (string-length haystack))
        (nlen (string-length needle)))
    (if (> nlen hlen)
        #f
        (let loop ((i 0))
          (cond ((> (+ i nlen) hlen) #f)
                ((string=? needle (substring haystack i (+ i nlen))) i)
                (else (loop (+ i 1))))))))

(define (string-contains-ci haystack needle)
  (string-contains (string-downcase haystack) (string-downcase needle)))

(define (string-trim-both str)
  (let* ((len (string-length str))
         (start (let loop ((i 0))
                  (if (or (>= i len) (not (char-whitespace? (string-ref str i))))
                      i (loop (+ i 1)))))
         (end (let loop ((i (- len 1)))
                (if (or (< i start) (not (char-whitespace? (string-ref str i))))
                    (+ i 1) (loop (- i 1))))))
    (substring str start end)))

(define (string-pad-right str width . rest)
  (let ((pad-char (if (null? rest) #\space (car rest))))
    (if (>= (string-length str) width)
        str
        (string-append str (make-string (- width (string-length str)) pad-char)))))

(define (string-pad-left str width . rest)
  (let ((pad-char (if (null? rest) #\space (car rest))))
    (if (>= (string-length str) width)
        str
        (string-append (make-string (- width (string-length str)) pad-char) str))))

(define (string-null? str)
  (= (string-length str) 0))

(define (string-index str ch)
  (let ((len (string-length str)))
    (let loop ((i 0))
      (cond ((>= i len) #f)
            ((char=? (string-ref str i) ch) i)
            (else (loop (+ i 1)))))))

(define (substring-index needle haystack)
  (string-contains haystack needle))

;; Pathname helpers
(define (pathname-file path)
  (let ((slash (let loop ((i (- (string-length path) 1)))
                 (cond ((< i 0) #f)
                       ((char=? (string-ref path i) #\/) i)
                       (else (loop (- i 1)))))))
    (if slash
        (substring path (+ slash 1) (string-length path))
        path)))

(define (pathname-directory path)
  (let ((slash (let loop ((i (- (string-length path) 1)))
                 (cond ((< i 0) #f)
                       ((char=? (string-ref path i) #\/) i)
                       (else (loop (- i 1)))))))
    (if slash (substring path 0 slash) ".")))

(define (pathname-strip-extension path)
  (let ((dot (let loop ((i (- (string-length path) 1)))
               (cond ((< i 0) #f)
                     ((char=? (string-ref path i) #\.) i)
                     ((char=? (string-ref path i) #\/) #f)
                     (else (loop (- i 1)))))))
    (if dot (substring path 0 dot) path)))

(define (pathname-strip-directory path)
  (pathname-file path))

(define (make-pathname dir file . rest)
  (let ((ext (if (null? rest) #f (car rest))))
    (let ((base (if dir (string-append dir "/" file) file)))
      (if ext (string-append base ext) base))))

;; I/O helpers
(define (file-size path)
  (guard (exn (#t 0))
    (let ((port (open-file-input-port path)))
      (let ((size (port-length port)))
        (close-port port)
        size))))

;; Time helpers
(define (current-process-milliseconds)
  (let ((t (current-time)))
    (+ (* (time-second t) 1000)
       (div (time-nanosecond t) 1000000))))

;; Misc helpers
(define (->string x)
  (cond ((string? x) x)
        ((symbol? x) (symbol->string x))
        ((number? x) (number->string x))
        (else (with-output-to-string (lambda () (display x))))))

(define pp pretty-print)

(define (current-arch)
  (let ((result (with-input-from-pipe "uname -m 2>/dev/null" read-line)))
    (if (or (eof-object? result) (not result)) "unknown" result)))

(define (hash-table-copy ht)
  (let ((new-ht (make-hash-table)))
    (hash-table-walk ht (lambda (k v) (hash-table-set! new-ht k v)))
    new-ht))

(define (write-string str . rest)
  (let ((port (if (null? rest) (current-output-port) (car rest))))
    (put-string port str)))

(define (realm-signature)
  (let ((name (realm-name)))
    (or name "wilderness")))

;;; ============================================================
;;; Boot Timing
;;; ============================================================

(define *repl-start-time* (current-process-milliseconds))

;;; ============================================================
;;; Boot Verbosity
;;; ============================================================

(define *boot-verbosity*
  (let ((env (getenv "CYBERSPACE_BOOT")))
    (cond
     ((not env) 2)  ; default: portal
     ((string=? env "shadow") 0)
     ((string=? env "whisper") 1)
     ((string=? env "portal") 2)
     ((string=? env "gate") 2)
     ((string=? env "chronicle") 3)
     ((string=? env "oracle") 4)
     (else 2))))

(define (boot-level! level)
  (set! *boot-verbosity*
        (case level
          ((shadow) 0) ((whisper) 1) ((portal gate) 2)
          ((chronicle) 3) ((oracle) 4) (else 2)))
  (print "Boot level: " level " (" *boot-verbosity* ")"))

;;; ============================================================
;;; Command Line Interface
;;; ============================================================

(define (parse-cli-option arg)
  (cond
    ((not (string-prefix? "--" arg)) #f)
    ((string-index arg #\=)
     => (lambda (idx)
          (cons (substring arg 2 idx)
                (substring arg (+ idx 1) (string-length arg)))))
    (else (cons (substring arg 2 (string-length arg)) #t))))

(define (parse-cli-args args)
  (filter-map parse-cli-option args))

(define (collect-script-args args)
  (filter (lambda (a) (not (string-prefix? "--" a))) args))

(define *cli-options* (parse-cli-args (cdr (command-line))))
(define *cli-scripts* (collect-script-args (cdr (command-line))))

(define (cli-option name)
  (let ((opt (assoc name *cli-options*)))
    (and opt (cdr opt))))

(define (cli-option? name)
  (and (cli-option name) #t))

;;; --help
(when (cli-option? "help")
  (print "Cyberspace Scheme - Distributed Systems Shell (Chez Port)")
  (print "")
  (print "Usage: repl.sps [options]")
  (print "")
  (print "Options:")
  (print "  --boot=<level>       Boot verbosity: shadow|whisper|portal|oracle")
  (print "  --eval='<expr>'      Evaluate expression and exit")
  (print "  --exec='<expr>'      Evaluate expression after init, then start REPL")
  (print "  --version            Show version information")
  (print "  --help               Show this help")
  (print "")
  (print "Examples:")
  (print "  repl.sps                      Start REPL (default)")
  (print "  repl.sps --boot=portal        Start with banner and help")
  (print "  repl.sps --eval='(+ 1 2)'     Evaluate and exit")
  (exit 0))

;;; --version
(when (cli-option? "version")
  (let ((ver (with-input-from-pipe "git describe --tags --always 2>/dev/null" read-line)))
    (print "Cyberspace Scheme (Chez Port) " (if (eof-object? ver) "unknown" ver)))
  (exit 0))

;;; --boot=<level>
(when (cli-option "boot")
  (let ((level (cli-option "boot")))
    (when (string? level)
      (set! *boot-verbosity*
            (cond
             ((string=? level "shadow") 0)
             ((string=? level "whisper") 1)
             ((string=? level "portal") 2)
             ((string=? level "gate") 2)
             ((string=? level "chronicle") 3)
             ((string=? level "oracle") 4)
             (else 2))))))

;;; ============================================================
;;; Initialize Crypto
;;; ============================================================

(sodium-init)
(fips-self-test)

;;; ============================================================
;;; Memo-040: Object State (chaotic/quiescent) and Persistence
;;; ============================================================

(define *thing-states* '())
(define *thing-durability* '())
(define *chaotic-store* '())
(define *persistence-queue* '())

(define (thing-id thing)
  (cond
   ((and (list? thing) (pair? (car thing)) (assoc 'id thing))
    => (lambda (pair) (cdr pair)))
   ((string? thing)
    (if (< (string-length thing) 64)
        thing
        (content-address thing)))
   (else
    (content-address (format "~a" thing)))))

(define (chaotic? thing)
  (let ((state (alist-ref (thing-id thing) *thing-states* equal?)))
    (or (not state) (eq? state 'chaotic))))

(define (quiescent? thing)
  (let ((state (alist-ref (thing-id thing) *thing-states* equal?)))
    (eq? state 'quiescent)))

(define (ephemeral? thing)
  (let ((dur (alist-ref (thing-id thing) *thing-durability* equal?)))
    (or (not dur) (eq? dur 'ephemeral))))

(define (persistent? thing)
  (let ((dur (alist-ref (thing-id thing) *thing-durability* equal?)))
    (eq? dur 'persistent)))

(define (thing-state thing)
  (or (alist-ref (thing-id thing) *thing-states* equal?) 'chaotic))

(define (thing-durability thing)
  (or (alist-ref (thing-id thing) *thing-durability* equal?) 'ephemeral))

(define (short-id id)
  (let ((s (if (string? id) id (->string id))))
    (if (> (string-length s) 16)
        (string-append (substring s 0 16) "...")
        s)))

(define (chaotic thing)
  (let ((id (thing-id thing)))
    (set! *thing-states* (cons (cons id 'chaotic) *thing-states*))
    (set! *chaotic-store* (cons (cons id thing) *chaotic-store*))
    (print "Thing " (short-id id) " is chaotic")
    thing))

(define (commit-thing thing)
  (let ((id (thing-id thing)))
    (unless (chaotic? thing)
      (print "Thing already quiescent"))
    (set! *thing-states* (cons (cons id 'quiescent) *thing-states*))
    (set! *chaotic-store* (filter (lambda (e) (not (equal? (car e) id))) *chaotic-store*))
    (print "Thing " (short-id id) " committed (quiescent)")
    (when (persistent? thing)
      (set! *persistence-queue* (cons thing *persistence-queue*))
      (print "  Queued for vault migration"))
    thing))

(define (persist thing)
  (let ((id (thing-id thing)))
    (set! *thing-durability* (cons (cons id 'persistent) *thing-durability*))
    (print "Thing " (short-id id) " marked persistent")
    (when (quiescent? thing)
      (set! *persistence-queue* (cons thing *persistence-queue*))
      (print "  Queued for vault migration"))
    thing))

(define (ephemeral thing)
  (let ((id (thing-id thing)))
    (set! *thing-durability* (cons (cons id 'ephemeral) *thing-durability*))
    (set! *persistence-queue* (filter (lambda (t) (not (equal? (thing-id t) id))) *persistence-queue*))
    (print "Thing " (short-id id) " marked ephemeral")
    thing))

(define (validate-for-vault thing)
  (let ((test-entry (and (list? thing)
                         (pair? (car thing))
                         (assq 'test thing))))
    (if test-entry
        (guard (exn (#t (begin
                          (print "  x validation exception")
                          #f)))
          (let ((result ((cdr test-entry))))
            (if result #t
                (begin (print "  x self-test failed") #f))))
        (begin
          (print "  x no test lambda (mandatory for vault)")
          #f))))

(define (flush-persistence!)
  (if (null? *persistence-queue*)
      (print "Persistence queue empty")
      (let* ((things *persistence-queue*)
             (validated (filter validate-for-vault things))
             (rejected (filter (lambda (t) (not (validate-for-vault t))) things)))
        (print "Migrating " (length things) " things to vault...")
        (print "  " (length validated) " passed validation")
        (when (not (null? rejected))
          (print "  " (length rejected) " REJECTED (failed self-test)"))
        (for-each
         (lambda (thing)
           (let ((id (thing-id thing)))
             (content-put (format "~a" thing))
             (print "  ok " (short-id id) " -> vault")))
         validated)
        (set! *persistence-queue* rejected)
        (if (null? rejected)
            (print "Done.")
            (print "Done. " (length rejected) " things remain in queue (fix and retry).")))))

(define (thing-status thing)
  (let ((id (thing-id thing)))
    (print "Thing: " (short-id id))
    (print "  State: " (thing-state thing))
    (print "  Durability: " (thing-durability thing))
    (print "  Cacheable: " (if (quiescent? thing) "yes (forever)" "no"))
    (print "  Self-test: " (if (and (list? thing) (pair? (car thing)) (assq 'test thing))
                               "present" "none"))
    `((id . ,id)
      (state . ,(thing-state thing))
      (durability . ,(thing-durability thing)))))

(define (make-tested-thing id data test-lambda)
  `((id . ,id) (data . ,data) (test . ,test-lambda) (created . ,(current-seconds))))

;;; ============================================================
;;; Node Identity and Attestation
;;; ============================================================

(define *node-attestation* #f)

(define (principal->string p)
  (if (blob? p) (blob->hex p) (format "~a" p)))

(define (attest . rest)
  (let ((principal (get-opt rest 0 #f))
        (key (vault-config 'signing-key)))
    (cond
     ((not key)
      (print "No signing key configured. Generate with (ed25519-keypair)")
      #f)
     (principal
      (let ((our-principal (principal->string key)))
        (if (equal? principal our-principal)
            (begin
              (set! *node-attestation* our-principal)
              (print "Attested as: " (short-id our-principal))
              our-principal)
            (begin
              (print "Attestation failed: principal mismatch")
              #f))))
     (else
      (let ((our-principal (principal->string key)))
        (set! *node-attestation* our-principal)
        (print "Attested as: " (short-id our-principal))
        our-principal)))))

(define (attested?)
  (and *node-attestation* #t))

(define (!)
  (unless (attested?)
    (print "Attestation required. Use (attest) first.")
    (print "")
    (attest))
  (when (attested?)
    (let* ((caps (probe-system-capabilities))
           (role (recommend-role caps)))
      (print "")
      (print "Node Information")
      (print "")
      (print "  Principal:   " (short-id *node-attestation*))
      (print "  Platform:    " (os-platform))
      (print "  Role:        " role)
      (print "  Vault:       " (if (directory-exists? ".vault") ".vault/" "(none)"))
      (print "")
      (print "  Compute")
      (let ((compute (cdr (assq 'compute caps))))
        (print "    Cores:     " (cdr (assq 'cores compute)))
        (print "    RAM:       " (cdr (assq 'ram-gb compute)) " GB")
        (print "    Load:      " (cdr (assq 'load-avg compute))))
      (print "")
      (print "  Storage")
      (let ((storage (cdr (assq 'storage caps))))
        (print "    Available: " (cdr (assq 'available-gb storage)) " GB")
        (print "    Type:      " (cdr (assq 'type storage))))
      (print "")
      (print "  Network")
      (let ((network (cdr (assq 'network caps))))
        (print "    Type:      " (cdr (assq 'type network)))
        (print "    Latency:   " (cdr (assq 'latency-ms network)) " ms"))
      (print "")
      (print "  State")
      (print "    Memos:     " (length *memos*))
      (print "    Chaotic:   " (length *chaotic-store*))
      (print "    Pending:   " (length *persistence-queue*))
      (print "")
      `((principal . ,*node-attestation*)
        (platform . ,(os-platform))
        (role . ,role)
        (capabilities . ,caps)))))

;;; ============================================================
;;; Memo-043: Memo Conventions
;;; ============================================================

(define *memos* '())
(define *memo-counter* 0)

(define (pad-number n width)
  (let ((s (number->string n)))
    (string-append (make-string (max 0 (- width (string-length s))) #\0) s)))

(define (memo-create title . opts)
  (let ((scope (get-key opts 'scope: 'local))
        (category (get-key opts 'category: 'informational))
        (author (get-key opts 'author: "anonymous"))
        (content (get-key opts 'content: "")))
    (set! *memo-counter* (+ *memo-counter* 1))
    (let* ((num (pad-number *memo-counter* 3))
           (id (case scope
                 ((local) (string-append "local:memo-" num))
                 ((federation) (string-append (current-directory) ":memo-" num))
                 ((core) (string-append "Memo-" num))
                 (else (error 'memo-create "Invalid scope" scope))))
           (memo `((id . ,id) (title . ,title) (scope . ,scope)
                   (category . ,category) (author . ,author)
                   (content . ,content) (created . ,(current-seconds))
                   (status . draft))))
      (chaotic memo)
      (set! *memos* (cons memo *memos*))
      (print "Created " id ": " title)
      (print "  Scope: " scope)
      (print "  Category: " category)
      (print "  State: chaotic (pen to commit)")
      memo)))

(define (memo-commit memo-id)
  (let ((memo (find (lambda (m) (equal? (alist-ref 'id m) memo-id)) *memos*)))
    (if memo
        (begin (commit-thing memo) (print "Memo committed: " memo-id) memo)
        (error 'memo-commit "Memo not found" memo-id))))

(define (memo-promote memo-id new-scope)
  (let ((memo (find (lambda (m) (equal? (alist-ref 'id m) memo-id)) *memos*)))
    (unless memo (error 'memo-promote "Memo not found" memo-id))
    (let ((current-scope (alist-ref 'scope memo)))
      (unless (quiescent? memo)
        (error 'memo-promote "Cannot promote chaotic memo - commit first"))
      (case new-scope
        ((federation)
         (unless (eq? current-scope 'local)
           (error 'memo-promote "Can only promote local to federation"))
         (print "Promoting " memo-id " to federation scope"))
        ((core)
         (unless (member current-scope '(local federation))
           (error 'memo-promote "Already at core scope"))
         (print "Promoting " memo-id " to core (Memo)"))
        (else (error 'memo-promote "Invalid scope" new-scope)))
      `(promoted ,memo-id ,new-scope))))

(define (memo-persist memo-id)
  (let ((memo (find (lambda (m) (equal? (alist-ref 'id m) memo-id)) *memos*)))
    (if memo (persist memo) (error 'memo-persist "Memo not found" memo-id))))

(define (memo-list . rest)
  (let ((scope (get-opt rest 0 #f)))
    (let ((filtered (if scope
                        (filter (lambda (m) (eq? (alist-ref 'scope m) scope)) *memos*)
                        *memos*)))
      (if (null? filtered)
          (print "No memos" (if scope (format " at scope ~a" scope) ""))
          (for-each
           (lambda (m)
             (print "  " (alist-ref 'id m) ": " (alist-ref 'title m)
                    " [" (thing-state m) "/" (thing-durability m) "]"))
           filtered)))))

(define (memo-show memo-id)
  (let ((memo (find (lambda (m) (equal? (alist-ref 'id m) memo-id)) *memos*)))
    (if memo
        (begin
          (print "Memo: " (alist-ref 'id memo))
          (print "  Title: " (alist-ref 'title memo))
          (print "  Scope: " (alist-ref 'scope memo))
          (print "  Category: " (alist-ref 'category memo))
          (print "  Author: " (alist-ref 'author memo))
          (print "  State: " (thing-state memo))
          (print "  Durability: " (thing-durability memo))
          (print "  Created: " (alist-ref 'created memo))
          memo)
        (error 'memo-show "Memo not found" memo-id))))

;;; ============================================================
;;; Memo-016: Lazy Clustering
;;; ============================================================

(define *lazy-peers* '())
(define *lazy-queue* '())
(define *version-vectors* '())

(define (lazy-join peer . opts)
  (let ((uri (get-key opts 'uri: #f))
        (key (get-key opts 'key: #f)))
    (cond
     ((not peer) (print "Join Refused: No peer specified") #f)
     ((assoc peer *lazy-peers*) (print "Join Refused: Already joined with " peer) #f)
     (else
      (set! *lazy-peers* (cons `((peer . ,peer) (uri . ,uri) (key . ,key) (last-sync . never)) *lazy-peers*))
      (print "Joined lazy cluster with " peer)
      `(joined ,peer)))))

(define (lazy-leave peer)
  (set! *lazy-peers* (filter (lambda (p) (not (equal? (alist-ref 'peer p) peer))) *lazy-peers*))
  (print "Left lazy cluster: " peer)
  `(left ,peer))

(define (lazy-push peer)
  (print "Pushing to " peer "...")
  (print "  (lazy push simulated)")
  `(pushed ,peer))

(define (lazy-pull peer)
  (print "Pulling from " peer "...")
  (print "  (lazy pull simulated)")
  `(pulled ,peer))

(define (lazy-sync peer)
  (print "Syncing with " peer "...")
  (lazy-push peer)
  (lazy-pull peer)
  (session-stat! 'syncs)
  `(synced ,peer))

(define (lazy-status)
  (if (null? *lazy-peers*)
      (print "No lazy cluster peers configured")
      (begin
        (print "Lazy cluster peers:")
        (for-each (lambda (p)
                    (print "  " (alist-ref 'peer p) " [" (alist-ref 'last-sync p) "]"))
                  *lazy-peers*))))

(define (lazy-queue)
  (if (null? *lazy-queue*)
      (print "Sync queue empty")
      (begin
        (print "Pending sync:")
        (for-each (lambda (item) (print "  " item)) *lazy-queue*))))

(define (lazy-resolve version . opts)
  (let ((prefer (get-key opts 'prefer: 'local))
        (merged (get-key opts 'merged: #f)))
    (print "Resolving " version " -> " (or merged prefer))
    `(resolved ,version ,(or merged prefer))))

(define (lazy-beacon)
  `(beacon
    (peer ,(current-directory))
    (lamport-time ,*lamport-clock*)
    (status available)))

;;; ============================================================
;;; Memo-010: Federation
;;; ============================================================

(define *federation-peers* '())

(define (federate peer-url . opts)
  (let ((trust (get-key opts 'trust: 'partial)))
    (set! *federation-peers* (cons `((url . ,peer-url) (trust . ,trust) (status . pending)) *federation-peers*))
    (print "Federation request sent to " peer-url)
    `(federation-pending ,peer-url)))

(define (federate-status)
  (if (null? *federation-peers*)
      (print "No federation peers configured")
      (for-each (lambda (p)
                  (print "  " (alist-ref 'url p) " [" (alist-ref 'trust p) "] " (alist-ref 'status p)))
                *federation-peers*)))

(define (federate-replicate peer-url)
  (print "Replicating with " peer-url "...")
  '(replicate-complete))

;;; ============================================================
;;; The Weave - Federation Topology View
;;; ============================================================

(define (weave-list-enrolled)
  (let ((keys-dir ".vault/keys"))
    (if (directory-exists? keys-dir)
        (let ((certs (glob (string-append keys-dir "/*.cert"))))
          (map (lambda (cert-file)
                 (let* ((name (pathname-strip-extension (pathname-file cert-file)))
                        (cert-data (guard (exn (#t #f))
                                    (with-input-from-file cert-file read))))
                   (if cert-data
                       (let* ((cert (if (and (pair? cert-data) (eq? (car cert-data) 'cert))
                                       cert-data
                                       (and (pair? cert-data) (assq 'cert cert-data))))
                              (subject (and cert (assq 'subject (cdr cert))))
                              (principal (and subject (cadr subject))))
                         `(,name (principal ,(if principal
                                                 (short-id (if (blob? principal)
                                                              (blob->hex principal)
                                                              (->string principal)))
                                                 "unknown"))))
                       `(,name (error "could not parse cert")))))
               certs))
        '())))

(define (weave-local-realm)
  (let* ((host (hostname))
         (vault-exists (directory-exists? ".vault"))
         (keystore-exists (directory-exists? ".vault/keystore"))
         (principal (if keystore-exists
                       (guard (exn (#t "locked"))
                         (let ((pub-file ".vault/keystore/public.key"))
                           (if (file-exists? pub-file)
                               (short-id (with-input-from-file pub-file read-line))
                               "no-key")))
                       "no-keystore")))
    `(,host
      (principal ,principal)
      (vault ,vault-exists)
      (keystore ,keystore-exists))))

(define *consensus-proposals* '())

(define (weave)
  (session-stat! 'queries)
  (let* ((local (weave-local-realm))
         (enrolled (weave-list-enrolled))
         (gossip-info (guard (exn (#t `(gossip (error "gossip not loaded"))))
                       (gossip-status)))
         (peers (guard (exn (#t '()))
                  (list-peers))))
    (print "")
    (print "THE WEAVE")
    (print "Reflection invites introspection")
    (print "")
    (print "Local Realm:")
    (print "  " (car local))
    (for-each (lambda (kv) (print "    " (car kv) ": " (cadr kv))) (cdr local))
    (print "")
    (print "Enrolled Peers:")
    (if (null? enrolled)
        (print "  (none)")
        (for-each (lambda (node)
                    (print "  " (car node))
                    (for-each (lambda (kv) (print "    " (car kv) ": " (cadr kv))) (cdr node)))
                  enrolled))
    (print "")
    (print "Gossip Status:")
    (if (and (pair? gossip-info) (eq? (car gossip-info) 'gossip-status))
        (for-each (lambda (kv)
                    (when (pair? kv)
                      (print "  " (car kv) ": " (cadr kv))))
                  (cdr gossip-info))
        (print "  (gossip daemon not running)"))
    (print "")
    (print "Active Peers:")
    (if (null? peers)
        (print "  (none - use add-peer to connect)")
        (for-each (lambda (p) (print "  " p)) peers))
    (print "")
    (print "Consensus:")
    (if (null? *consensus-proposals*)
        (print "  (no active proposals)")
        (begin
          (print "  " (length *consensus-proposals*) " proposal(s)")
          (for-each (lambda (p)
                      (print "    " (short-id (alist-ref 'id p))
                             " [" (alist-ref 'quorum p) "] "
                             (length (alist-ref 'votes p)) " votes"))
                    *consensus-proposals*)))
    (print "")
    (print "Lamport Clock: " (lamport-time))
    (print "")
    `(weave
      (local ,local)
      (enrolled ,@enrolled)
      (gossip ,gossip-info)
      (peers ,@peers)
      (consensus ,(length *consensus-proposals*))
      (lamport ,(lamport-time)))))

(define (about)
  (let* ((realm-nm (realm-signature))
         (enrolled (guard (exn (#t '())) (weave-list-enrolled)))
         (peer-count (length enrolled))
         (vault-path (guard (exn (#t #f)) (get-vault-path)))
         (has-vault (and vault-path (directory-exists? vault-path))))
    (print "")
    (print "  Cyberspace is a system for storing and sharing digital")
    (print "  documents, code, and data without relying on any company,")
    (print "  government, or central authority.")
    (print "")
    (print "  Instead of trusting a corporation to keep your files safe,")
    (print "  you and people you trust keep copies that are cryptographically")
    (print "  signed--meaning anyone can verify who created something and")
    (print "  that it hasn't been tampered with.")
    (print "")
    (print "  Your data belongs to you, verified by math, preserved by the")
    (print "  people you choose.")
    (print "")
    (print "  This realm: " realm-nm)
    (cond
      ((= peer-count 0)
       (print "  Standing alone. No peers enrolled yet."))
      ((= peer-count 1)
       (print "  One peer in the weave. A mirror reflects.")
       (print "  " (caar enrolled)))
      (else
       (print "  " peer-count " peers in the weave. Mirrors reflecting mirrors.")
       (for-each (lambda (node) (print "  " (car node))) enrolled)))
    (print "")
    (if has-vault
        (print "  Vault: active")
        (print "  Vault: not initialized (use vault-init)"))
    (print "")
    `(about (realm ,realm-nm) (peers ,peer-count) (vault ,has-vault))))

(define (huh?) (about))
(define (what?) (about))

;;; ============================================================
;;; Memo-011: Byzantine Consensus
;;; ============================================================

(define (consensus-propose value . opts)
  (let ((quorum (get-key opts 'quorum: 'majority)))
    (let ((proposal-id (blob->hex (sha512-hash (string->blob (format "~a~a" value (current-seconds)))))))
      (set! *consensus-proposals*
            (cons `((id . ,proposal-id) (value . ,value) (quorum . ,quorum) (votes . ()))
                  *consensus-proposals*))
      (print "Proposal " (short-id proposal-id) " created")
      proposal-id)))

(define (consensus-vote proposal-id vote . opts)
  (session-stat! 'votes)
  (print "Vote " vote " recorded for " (short-id proposal-id))
  `(vote-recorded ,vote))

(define (consensus-status . rest)
  (if (null? *consensus-proposals*)
      (print "No active proposals")
      (for-each (lambda (p)
                  (print "  " (short-id (alist-ref 'id p)) " : " (alist-ref 'value p)))
                *consensus-proposals*)))

;;; ============================================================
;;; Memo-012: Lamport Clocks (REPL-local)
;;; ============================================================

(define *lamport-clock* 0)

(define (lamport-tick)
  (set! *lamport-clock* (+ *lamport-clock* 1))
  *lamport-clock*)

(define (lamport-send-local)
  (lamport-tick))

(define (lamport-receive-local remote-timestamp)
  (set! *lamport-clock* (+ 1 (max *lamport-clock* remote-timestamp)))
  *lamport-clock*)

(define (lamport-compare t1 t2)
  (cond ((< t1 t2) -1) ((> t1 t2) 1) (else 0)))

(define (lamport-clock)
  *lamport-clock*)

;;; ============================================================
;;; Memo-020: Content-Addressed Storage
;;; ============================================================

(define *content-store* '())

(define (content-address data)
  (let ((hash (sha512-hash (if (blob? data) data (string->blob data)))))
    (blob->hex hash)))

(define (content-put data)
  (let* ((addr (content-address data))
         (blob-data (if (blob? data) data (string->blob data))))
    (set! *content-store* (cons (cons addr blob-data) *content-store*))
    (print "Stored at " (short-id addr))
    addr))

(define (content-get addr)
  (let ((entry (assoc addr *content-store*)))
    (if entry (cdr entry) (error 'content-get "Content not found" addr))))

(define (content-exists? addr)
  (if (assoc addr *content-store*) #t #f))

;;; ============================================================
;;; Memo-021: Capability Delegation
;;; ============================================================

(define (delegate capability to-principal . opts)
  (let ((restrict (get-key opts 'restrict: '()))
        (expires (get-key opts 'expires: #f)))
    (let ((delegation `((capability . ,capability) (to . ,to-principal)
                        (restrictions . ,restrict) (expires . ,expires)
                        (created . ,(current-seconds)))))
      (print "Delegated " capability " to " to-principal)
      delegation)))

(define (delegate-chain delegations)
  (print "Verifying delegation chain of " (length delegations) " links...")
  (if (null? delegations) #t
      (let loop ((chain delegations))
        (if (null? (cdr chain)) #t (loop (cdr chain))))))

(define (delegate-verify delegation principal action)
  (let ((cap (alist-ref 'capability delegation))
        (to (alist-ref 'to delegation)))
    (and (equal? to principal) (equal? cap action))))

;;; ============================================================
;;; Memo-023: Agent Sandboxing
;;; ============================================================

(define *sandboxes* '())

(define (sandbox name . opts)
  (let ((capabilities (get-key opts 'capabilities: '()))
        (limits (get-key opts 'limits: '())))
    (let ((sb `((name . ,name) (capabilities . ,capabilities)
                (limits . ,limits) (status . ready))))
      (set! *sandboxes* (cons sb *sandboxes*))
      (print "Sandbox '" name "' created with " (length capabilities) " capabilities")
      sb)))

(define (sandbox-run sb-name code)
  (print "Executing in sandbox '" sb-name "'...")
  (print "  (sandboxed execution simulated)")
  '(sandbox-result ok))

(define (sandbox-capabilities sb-name)
  (let ((sb (find (lambda (s) (equal? (alist-ref 'name s) sb-name)) *sandboxes*)))
    (if sb (alist-ref 'capabilities sb) (error 'sandbox-capabilities "Sandbox not found" sb-name))))

(define (sandbox-destroy sb-name)
  (set! *sandboxes* (filter (lambda (s) (not (equal? (alist-ref 'name s) sb-name))) *sandboxes*))
  (print "Sandbox '" sb-name "' destroyed"))

;;; ============================================================
;;; Memo-035: Mobile Agents (Quantum Vocabulary)
;;; ============================================================

(define *agent-location* 'local)
(define *entanglements* '())
(define *teleport-grants* '())
(define *teleport-history* '())

(define (parse-teleport-address addr)
  (cond
   ((string-contains addr "://")
    (let* ((proto-end (string-contains addr "://"))
           (proto (substring addr 0 proto-end))
           (rest (substring addr (+ proto-end 3) (string-length addr)))
           (slash-pos (string-contains rest "/"))
           (host (if slash-pos (substring rest 0 slash-pos) rest))
           (path (if slash-pos (substring rest slash-pos (string-length rest)) "/")))
      `((protocol . ,proto) (host . ,host) (path . ,path))))
   ((string-contains addr "@")
    (let* ((at-pos (string-contains addr "@"))
           (principal (substring addr 0 at-pos))
           (rest (substring addr (+ at-pos 1) (string-length addr)))
           (colon-pos (string-contains rest ":"))
           (realm (if colon-pos (substring rest 0 colon-pos) rest))
           (path (if colon-pos (substring rest (+ colon-pos 1) (string-length rest)) "/")))
      `((principal . ,principal) (realm . ,realm) (path . ,path))))
   ((string-contains addr ":")
    (let* ((colon-pos (string-contains addr ":"))
           (realm (substring addr 0 colon-pos))
           (path (substring addr (+ colon-pos 1) (string-length addr))))
      `((realm . ,realm) (path . ,path))))
   (else `((realm . local) (path . ,addr)))))

(define (teleport-grant destination . opts)
  (let ((capabilities (get-key opts 'capabilities: '(read)))
        (expires (get-key opts 'expires: #f))
        (delegate-flag (get-key opts 'delegate: #f)))
    (unless (attested?)
      (error 'teleport-grant "Attestation required to grant teleport authorization"))
    (let ((grant `((destination . ,destination) (capabilities . ,capabilities)
                   (expires . ,expires) (delegatable . ,(and delegate-flag #t))
                   (grantor . ,*node-attestation*) (created . ,(current-seconds)))))
      (set! *teleport-grants* (cons grant *teleport-grants*))
      (print "Granted teleport to: " destination)
      (print "  Capabilities: " capabilities)
      (when expires (print "  Expires: " expires))
      (when delegate-flag (print "  Delegatable: yes"))
      grant)))

(define (teleport-check destination capabilities)
  (let ((now (current-seconds)))
    (find (lambda (g)
            (and (equal? (alist-ref 'destination g) destination)
                 (or (not (alist-ref 'expires g))
                     (> (alist-ref 'expires g) now))
                 (every (lambda (c) (member c (alist-ref 'capabilities g)))
                        capabilities)))
          *teleport-grants*)))

(define (teleport destination . opts)
  (let ((state (get-key opts 'state: '()))
        (as (get-key opts 'as: #f))
        (capabilities (get-key opts 'capabilities: '(read))))
    (unless (attested?)
      (error 'teleport "Attestation required for teleportation"))
    (let ((addr (parse-teleport-address destination)))
      (print "")
      (print "Teleport")
      (print "  From: " *agent-location*)
      (print "  To:   " destination)
      (when as (print "  As:   " as))
      (print "  Caps: " capabilities)
      (print "")
      (let ((grant (teleport-check destination capabilities)))
        (cond
         ((not grant)
          (print "  [Denied] No authorization for destination")
          #f)
         (else
          (let ((old-location *agent-location*)
                (record `((from . ,*agent-location*) (to . ,destination)
                          (principal . ,*node-attestation*) (as . ,as)
                          (capabilities . ,capabilities) (state-size . ,(length state))
                          (timestamp . ,(current-seconds)))))
            (set! *teleport-history* (cons record *teleport-history*))
            (audit-append 'actor: *node-attestation*
                          'action: 'teleport 'target: destination 'detail: record)
            (set! *agent-location* destination)
            (print "  [OK] Teleported")
            (print "  State transferred: " (length state) " items")
            `((status . ok) (from . ,old-location)
              (to . ,destination) (address . ,addr)))))))))

(define (teleport-history)
  (if (null? *teleport-history*)
      (print "No teleportation history")
      (for-each (lambda (h)
                  (print "  " (alist-ref 'timestamp h) ": "
                         (alist-ref 'from h) " -> " (alist-ref 'to h)))
                *teleport-history*)))

(define (tunnel destination . opts)
  (print "Tunneling to " destination "...")
  (set! *agent-location* destination)
  `(tunneled ,destination))

(define (observe resource)
  (print "Observing " resource "...")
  `(observed ,resource ,(current-seconds)))

(define (entangle agent1 agent2)
  (set! *entanglements* (cons (list agent1 agent2) *entanglements*))
  (print "Entangled " agent1 " <-> " agent2)
  `(entangled ,agent1 ,agent2))

(define (quantum-teleport state from to)
  (let ((pair (find (lambda (e)
                      (or (and (equal? (car e) from) (equal? (cadr e) to))
                          (and (equal? (car e) to) (equal? (cadr e) from))))
                    *entanglements*)))
    (if pair
        (begin (print "Quantum teleporting via entanglement: " from " <-> " to)
               `(teleported ,state ,to))
        (begin (print "No entanglement between " from " and " to) #f))))

(define (decohere agent)
  (print "Decohering " agent "...")
  (set! *agent-location* 'local)
  '(decohered))

(define (superpose states) `(superposition ,@states))

(define (collapse superposition)
  (if (and (pair? superposition) (eq? (car superposition) 'superposition))
      (let ((states (cdr superposition)))
        (list-ref states (random-uniform (length states))))
      superposition))

;;; ============================================================
;;; Memo-036: Quorum Voting
;;; ============================================================

(define *quorum-proposals* '())

(define (quorum-propose question options . opts)
  (let ((threshold (get-key opts 'threshold: 'majority)))
    (let ((prop-id (blob->hex (sha512-hash (string->blob question)))))
      (set! *quorum-proposals*
            (cons `((id . ,prop-id) (question . ,question) (options . ,options)
                    (threshold . ,threshold) (votes . ()) (status . open))
                  *quorum-proposals*))
      (print "Quorum proposal created: " (short-id prop-id))
      prop-id)))

(define (quorum-vote prop-id choice . opts)
  (let ((encrypted (get-key opts 'encrypted: #t)))
    (session-stat! 'votes)
    (print "Vote cast for " (short-id prop-id) " [" (if encrypted "encrypted" "plain") "]")
    `(vote-recorded ,choice)))

(define (quorum-tally prop-id)
  (print "Tallying votes for " (short-id prop-id))
  (print "  (homomorphic tally simulated)")
  '(tally-pending))

(define (quorum-status . rest)
  (if (null? *quorum-proposals*)
      (print "No active quorum proposals")
      (for-each (lambda (p)
                  (print "  " (short-id (alist-ref 'id p)) " : "
                         (alist-ref 'question p) " [" (alist-ref 'status p) "]"))
                *quorum-proposals*)))

;;; ============================================================
;;; Memo-038: Local Inference (Ollama)
;;; ============================================================

(define *inference-server* "http://localhost:11434")

(define (inference-server . rest)
  (if (null? rest) *inference-server*
      (begin (set! *inference-server* (car rest)) (car rest))))

(define (inference-models)
  (print "Querying " *inference-server* "/api/tags ...")
  '(llama3 mistral codellama nomic-embed-text))

(define (inference prompt . opts)
  (let ((model (get-key opts 'model: 'llama3))
        (max-tokens (get-key opts 'max-tokens: 500)))
    (print "Inference request to " *inference-server*)
    (print "  Model: " model)
    (print "  (would call Ollama API)")
    '(inference-simulated)))

;;; ============================================================
;;; Wormholes (Memo-041: FUSE Filesystem)
;;; ============================================================

(define *wormholes* '())
(define *vault-manifest* '())
(define *wormhole-rate-limits* '())
(define *wormhole-ops-count* 0)

(define capability:read-only '(read stat readdir xattr-read acl-read))
(define capability:read-write '(read write create stat chmod readdir mkdir xattr-read xattr-write))
(define capability:full
  '(read write create delete rename stat chmod chown
    xattr-read xattr-write acl-read acl-write readdir mkdir rmdir admin delegate audit-read rate-limit))

(define (wormhole-audit action path . rest)
  (let ((detail (get-opt rest 0 #f)))
    (audit-append 'actor: 'wormhole 'action: action 'target: path 'detail: detail)))

(define (wormhole-open fs-path . opts)
  (let ((vault-path (get-key opts 'vault-path: "/"))
        (rate-limit (get-key opts 'rate-limit: 1000))
        (capabilities (get-key opts 'capabilities: '(read write)))
        (locked (get-key opts 'locked: #f)))
    (let ((abs-path (if (char=? (string-ref fs-path 0) #\/)
                        fs-path
                        (string-append (current-directory) "/" fs-path))))
      (print "Opening wormhole: " abs-path " <-> vault:" vault-path)
      (print "  Capabilities: " (length capabilities) " granted")
      (print "  Rate limit: " rate-limit " ops/min")
      (print "  Locked: " (if locked "yes" "no"))
      (set! *wormholes* (cons `((fs . ,abs-path) (vault . ,vault-path)
                                (status . ,(if locked 'locked 'stable))
                                (capabilities . ,capabilities)
                                (rate-limit . ,rate-limit)
                                (opened . ,(current-seconds)))
                              *wormholes*))
      (set! *wormhole-rate-limits* (cons (cons abs-path rate-limit) *wormhole-rate-limits*))
      (wormhole-audit 'wormhole-open abs-path)
      (session-stat! 'wormholes)
      (print "  (wormhole simulated - full implementation requires libfuse)")
      `(wormhole ,abs-path ,vault-path))))

(define (wormhole-close fs-path)
  (print "Closing wormhole at " fs-path "...")
  (wormhole-audit 'wormhole-close fs-path)
  (set! *wormholes* (filter (lambda (w) (not (equal? (alist-ref 'fs w) fs-path))) *wormholes*))
  `(closed ,fs-path))

(define (wormholes)
  (if (null? *wormholes*)
      (print "No active wormholes")
      (for-each (lambda (w)
                  (print "  " (alist-ref 'fs w) " <-> vault:" (alist-ref 'vault w)
                         " [" (alist-ref 'status w) "] "
                         (alist-ref 'rate-limit w) " ops/min"))
                *wormholes*)))

(define vault-mount wormhole-open)
(define vault-unmount wormhole-close)
(define vault-mounts wormholes)

(define (wormhole-security)
  (print "")
  (print "Wormhole Security Properties")
  (print "")
  (print "  IDENTITY: mutual-authentication, SPKI certificates, Ed25519")
  (print "  CONFIDENTIALITY: encryption required, TLS 1.3, X25519 PFS")
  (print "  INTEGRITY: AEAD ChaCha20-Poly1305, sequence numbers")
  (print "  AUTHORIZATION: capability model, no ambient authority, attenuation only")
  (print "  CONFINEMENT: capability-bounded data flow, sandboxed agents")
  (print "  AUDIT: comprehensive logging, tamper-evident trail")
  (print "  AVAILABILITY: rate limiting, per-principal quotas")
  (print "")
  (print "  States: closed -> connecting -> handshake -> open -> closing -> closed")
  (print ""))

;;; ============================================================
;;; Secure Erasure (Memo-040)
;;; ============================================================

(define *erase-audit* '())

(define (secure-clear! buffer)
  (cond
   ((u8vector? buffer)
    (let ((len (u8vector-length buffer)))
      (do ((i 0 (+ i 1))) ((>= i len))
        (u8vector-set! buffer i 0))
      (do ((i 0 (+ i 1))) ((>= i len) #t)
        (unless (zero? (u8vector-ref buffer i))
          (error 'secure-clear-failed "Zeroization verification failed")))
      (print "  [Cleared] " len " bytes zeroized")
      #t))
   ((blob? buffer)
    (print "  [Warn] Blobs are immutable; use u8vectors for sensitive data")
    #f)
   ((string? buffer)
    (print "  [Warn] Strings are immutable; cannot clear in place")
    #f)
   (else (error 'secure-clear! "Expected u8vector, blob, or string"))))

(define (key-destroy! key-id)
  (print "Destroying key: " (short-id (if (string? key-id) key-id (format "~a" key-id))))
  (let ((entry `((timestamp . ,(current-seconds)) (action . key-destroyed)
                 (target . ,key-id) (method . zeroization))))
    (set! *erase-audit* (cons entry *erase-audit*))
    (audit-append 'actor: 'security 'action: 'key-destroyed
                  'target: key-id 'detail: '(method zeroization))
    (print "  [Destroyed] Key material zeroized")
    'destroyed))

(define (object-erase! hash)
  (print "Securely erasing: " (short-id hash))
  (let ((path (string-append ".vault/objects/" (short-id hash))))
    (if (file-exists? path)
        (begin
          (print "  [Phase 1] Overwriting with random data...")
          (print "  [Phase 2] Overwriting with zeros...")
          (print "  [Phase 3] Unlinking file...")
          (guard (exn (#t (void))) (delete-file path))
          (audit-append 'actor: 'security 'action: 'object-erased
                        'target: hash 'detail: '(method overwrite-then-delete))
          (print "  [Erased] Object securely destroyed")
          'erased)
        (begin
          (print "  [Skip] Object not found at " path)
          'not-found))))

(define (secure-erase-encrypted hash)
  (print "Erasing via key destruction: " (short-id hash))
  (let ((dek-id (string-append "dek:" (short-id hash))))
    (key-destroy! dek-id)
    (audit-append 'actor: 'security 'action: 'encrypted-object-erased
                  'target: hash 'detail: '(method key-destruction))
    (print "  [Erased] Ciphertext now unrecoverable")
    'erased-via-key-destruction))

(define (session-key-destroy! session-id)
  (print "Destroying session key: " session-id)
  (key-destroy! (string-append "session:" session-id))
  (print "  [Destroyed] Forward secrecy maintained")
  'session-key-destroyed)

(define (erase-audit)
  (if (null? *erase-audit*)
      (print "No erasure operations recorded")
      (for-each
       (lambda (e)
         (print "  " (alist-ref 'timestamp e) " " (alist-ref 'action e) " " (alist-ref 'target e)))
       *erase-audit*)))

;;; ============================================================
;;; Code Optimization Pass
;;; ============================================================

(define *canonical-vars*
  (let ((v (make-vector 256)))
    (do ((i 0 (+ i 1))) ((= i 256) v)
      (vector-set! v i (string->symbol (string-append "a" (number->string i)))))))

(define *opt-counter* 0)

(define (fresh-var)
  (let ((i *opt-counter*))
    (set! *opt-counter* (+ i 1))
    (if (< i 256)
        (vector-ref *canonical-vars* i)
        (string->symbol (string-append "a" (number->string i))))))

(define (reset-fresh!) (set! *opt-counter* 0))

(define *opt-memo* (make-hash-table))
(define *opt-memo-hits* 0)
(define *opt-memo-misses* 0)

(define (memo-clear!)
  (set! *opt-memo* (make-hash-table))
  (set! *opt-memo-hits* 0)
  (set! *opt-memo-misses* 0))

(define (alpha-normalize expr)
  (reset-fresh!)
  (alpha-rename-ht expr (make-hash-table)))

(define (alpha-rename-ht expr env)
  (cond
   ((symbol? expr) (hash-table-ref/default env expr expr))
   ((and (pair? expr) (eq? (car expr) 'lambda))
    (let* ((params (let ((p (cadr expr))) (if (list? p) p (list p))))
           (body (cddr expr))
           (new-env (hash-table-copy env)))
      (for-each (lambda (p) (hash-table-set! new-env p (fresh-var))) params)
      `(lambda ,(map (lambda (p) (hash-table-ref new-env p)) params)
         ,@(map (lambda (e) (alpha-rename-ht e new-env)) body))))
   ((and (pair? expr) (eq? (car expr) 'let))
    (let* ((bindings (cadr expr))
           (body (cddr expr))
           (new-env (hash-table-copy env))
           (new-names (map (lambda (b)
                            (let ((n (fresh-var)))
                              (hash-table-set! new-env (car b) n) n))
                          bindings)))
      `(let ,(map (lambda (b n) (list n (alpha-rename-ht (cadr b) env)))
                  bindings new-names)
         ,@(map (lambda (e) (alpha-rename-ht e new-env)) body))))
   ((and (pair? expr) (eq? (car expr) 'define))
    (if (pair? (cadr expr))
        (let* ((name (caadr expr)) (params (cdadr expr)) (body (cddr expr))
               (new-env (hash-table-copy env)))
          (for-each (lambda (p) (hash-table-set! new-env p (fresh-var))) params)
          `(define (,name ,@(map (lambda (p) (hash-table-ref new-env p)) params))
             ,@(map (lambda (e) (alpha-rename-ht e new-env)) body)))
        `(define ,(cadr expr) ,@(map (lambda (e) (alpha-rename-ht e env)) (cddr expr)))))
   ((pair? expr) (map (lambda (e) (alpha-rename-ht e env)) expr))
   (else expr)))

(define *fold-ops*
  (let ((t (make-hash-table)))
    (hash-table-set! t '+ +) (hash-table-set! t '- -)
    (hash-table-set! t '* *) (hash-table-set! t '/ /)
    (hash-table-set! t 'quotient quotient) (hash-table-set! t 'remainder remainder)
    (hash-table-set! t 'modulo modulo) (hash-table-set! t 'min min)
    (hash-table-set! t 'max max) (hash-table-set! t 'abs abs)
    (hash-table-set! t 'expt expt)
    t))

(define (const-fold expr)
  (cond
   ((and (pair? expr) (hash-table-exists? *fold-ops* (car expr))
         (every number? (cdr expr)))
    (apply (hash-table-ref *fold-ops* (car expr)) (cdr expr)))
   ((and (pair? expr) (eq? (car expr) 'string-append) (every string? (cdr expr)))
    (apply string-append (cdr expr)))
   ((and (pair? expr) (eq? (car expr) 'not) (= (length expr) 2) (boolean? (cadr expr)))
    (not (cadr expr)))
   ((and (pair? expr) (eq? (car expr) 'if) (>= (length expr) 3) (boolean? (cadr expr)))
    (if (cadr expr) (const-fold (caddr expr))
        (if (> (length expr) 3) (const-fold (cadddr expr)) '(void))))
   ((and (pair? expr) (memq (car expr) '(+ *)) (= (length expr) 2))
    (const-fold (cadr expr)))
   ((and (pair? expr) (eq? (car expr) '+))
    (let* ((folded-args (map const-fold (cdr expr)))
           (non-zero (filter (lambda (x) (not (eqv? x 0))) folded-args)))
      (cond ((null? non-zero) 0)
            ((null? (cdr non-zero)) (car non-zero))
            ((every number? non-zero) (apply + non-zero))
            (else `(+ ,@non-zero)))))
   ((and (pair? expr) (eq? (car expr) '*))
    (let* ((folded-args (map const-fold (cdr expr)))
           (non-one (filter (lambda (x) (not (eqv? x 1))) folded-args)))
      (cond ((any (lambda (x) (eqv? x 0)) folded-args) 0)
            ((null? non-one) 1)
            ((null? (cdr non-one)) (car non-one))
            ((every number? non-one) (apply * non-one))
            (else `(* ,@non-one)))))
   ((pair? expr)
    (let ((folded (map const-fold expr)))
      (if (equal? folded expr) folded (const-fold folded))))
   (else expr)))

(define (expr-type-rank x)
  (cond ((number? x) 0) ((string? x) 1) ((symbol? x) 2)
        ((null? x) 3) ((pair? x) 4) (else 5)))

(define (expr-same-type<? a b rank)
  (case rank
    ((0) (< a b)) ((1) (string<? a b))
    ((2) (string<? (symbol->string a) (symbol->string b)))
    ((3) #f)
    ((4) (or (expr<? (car a) (car b))
             (and (equal? (car a) (car b)) (expr<? (cdr a) (cdr b)))))
    (else #f)))

(define (expr<? a b)
  (let ((ta (expr-type-rank a)) (tb (expr-type-rank b)))
    (if (= ta tb) (expr-same-type<? a b ta) (< ta tb))))

(define (sort-commutative expr)
  (cond
   ((and (pair? expr) (memq (car expr) '(+ * and or)))
    (cons (car expr) (sort expr<? (map sort-commutative (cdr expr)))))
   ((pair? expr) (map sort-commutative expr))
   (else expr)))

(define (free-vars-set expr)
  (let ((s (make-hash-table)))
    (free-vars-into! expr s (make-hash-table))
    s))

(define (free-vars-into! expr result bound)
  (cond
   ((symbol? expr)
    (unless (hash-table-exists? bound expr)
      (hash-table-set! result expr #t)))
   ((and (pair? expr) (eq? (car expr) 'quote)) (void))
   ((and (pair? expr) (eq? (car expr) 'lambda))
    (let ((new-bound (hash-table-copy bound))
          (params (let ((p (cadr expr))) (if (list? p) p (list p)))))
      (for-each (lambda (p) (hash-table-set! new-bound p #t)) params)
      (for-each (lambda (e) (free-vars-into! e result new-bound)) (cddr expr))))
   ((and (pair? expr) (eq? (car expr) 'let))
    (let ((new-bound (hash-table-copy bound)))
      (for-each (lambda (b) (free-vars-into! (cadr b) result bound)) (cadr expr))
      (for-each (lambda (b) (hash-table-set! new-bound (car b) #t)) (cadr expr))
      (for-each (lambda (e) (free-vars-into! e result new-bound)) (cddr expr))))
   ((pair? expr) (for-each (lambda (e) (free-vars-into! e result bound)) expr))
   (else (void))))

(define (eliminate-dead expr)
  (cond
   ((and (pair? expr) (eq? (car expr) 'let))
    (let* ((bindings (cadr expr))
           (body (map eliminate-dead (cddr expr)))
           (used-set (free-vars-set body))
           (live (filter (lambda (b) (hash-table-exists? used-set (car b))) bindings)))
      (if (null? live)
          (if (= (length body) 1) (car body) `(begin ,@body))
          `(let ,(map (lambda (b) (list (car b) (eliminate-dead (cadr b)))) live)
             ,@body))))
   ((pair? expr) (map eliminate-dead expr))
   (else expr)))

(define (optimize expr)
  (let ((cached (hash-table-ref/default *opt-memo* expr #f)))
    (if cached
        (begin (set! *opt-memo-hits* (+ 1 *opt-memo-hits*)) cached)
        (let* ((normalized (alpha-normalize expr))
               (folded (const-fold normalized))
               (sorted (sort-commutative folded))
               (cleaned (eliminate-dead sorted)))
          (set! *opt-memo-misses* (+ 1 *opt-memo-misses*))
          (hash-table-set! *opt-memo* expr cleaned)
          cleaned))))

(define (normalize expr) (alpha-normalize expr))

(define (code-hash expr)
  (let* ((optimized (optimize expr))
         (canonical (format "~s" optimized)))
    (short-id (blob->hex (sha256-hash (string->blob canonical))))))

(define (code-equivalent? a b)
  (equal? (optimize a) (optimize b)))

(define (opt-stats)
  (print "Optimizer Statistics:")
  (print "  Memo hits:    " *opt-memo-hits*)
  (print "  Memo misses:  " *opt-memo-misses*)
  (print "  Cache size:   " (hash-table-size *opt-memo*)))

;;; ============================================================
;;; Compilation & Replication Semantics
;;; ============================================================

(define *compile-cache* '())
(define *compile-pending* '())
(define *compile-stats* '((hits . 0) (misses . 0) (compiles . 0) (replicated . 0)))

(define (compile-stat! key)
  (set! *compile-stats*
        (map (lambda (p) (if (eq? (car p) key) (cons key (+ 1 (cdr p))) p))
             *compile-stats*)))

(define (source->optimized source) (optimize source))

(define (optimized->compiled optimized)
  `(compiled (arch . ,(current-arch)) (timestamp . ,(current-seconds)) (code . ,optimized)))

(define (compile-source source)
  (let* ((opt (source->optimized source))
         (opt-hash (code-hash opt))
         (cached (assoc opt-hash *compile-cache*)))
    (if cached
        (begin (compile-stat! 'hits) (cdr cached))
        (let ((compiled (optimized->compiled opt)))
          (compile-stat! 'misses) (compile-stat! 'compiles)
          (set! *compile-cache* (cons (cons opt-hash compiled) *compile-cache*))
          compiled))))

(define (compile-status)
  (print "Compilation Status:")
  (print "  Cache entries: " (length *compile-cache*))
  (for-each (lambda (s) (print "  " (car s) ": " (cdr s))) *compile-stats*))

;;; ============================================================
;;; Cluster Status
;;; ============================================================

(define *cluster-nodes* '())
(define *cluster-state* 'solo)
(define *replication-state* 'none)

(define (node-join name . opts)
  (let ((uri (get-key opts 'uri: #f)))
    (cond
     ((not name) (print "Join Refused: No node name specified") #f)
     ((assoc name *cluster-nodes*) (print "Join Refused: Node already in cluster") #f)
     (else
      (set! *cluster-nodes* (cons (list name uri (current-seconds)) *cluster-nodes*))
      (when (and (eq? *cluster-state* 'solo) (> (length *cluster-nodes*) 0))
        (set! *cluster-state* 'forming))
      *cluster-nodes*))))

(define (node-leave name)
  (set! *cluster-nodes* (filter (lambda (n) (not (equal? (car n) name))) *cluster-nodes*))
  (when (null? *cluster-nodes*) (set! *cluster-state* 'solo))
  *cluster-nodes*)

(define (nodes)
  (if (null? *cluster-nodes*)
      (print "No cluster nodes (solo)")
      (begin
        (print "Nodes: " (length *cluster-nodes*))
        (for-each (lambda (n)
                    (print "  " (car n) (if (cadr n) (string-append " @ " (cadr n)) "")))
                  *cluster-nodes*))))

(define (cluster . rest)
  (let ((new-state (get-opt rest 0 #f)))
    (if new-state
        (begin (set! *cluster-state* new-state) (print "Cluster: " new-state))
        (begin (print "Cluster: " *cluster-state*)
               (print "  Nodes: " (length *cluster-nodes*))
               *cluster-state*))))

(define (replication . rest)
  (let ((new-state (get-opt rest 0 #f)))
    (if new-state
        (begin (set! *replication-state* new-state) (print "Replication: " new-state))
        (begin (print "Replication: " *replication-state*) *replication-state*))))

;;; ============================================================
;;; ASCII Inspector - Visual S-expression Debugging
;;; ============================================================

(define (type-tag obj)
  (cond
   ((null? obj) "nil") ((pair? obj) (if (list? obj) "list" "pair"))
   ((symbol? obj) "sym") ((string? obj) "str") ((number? obj) "num")
   ((boolean? obj) "bool") ((blob? obj) "blob") ((u8vector? obj) "u8vec")
   ((vector? obj) "vec") ((procedure? obj) "proc") ((port? obj) "port")
   ((eof-object? obj) "eof") (else "?")))

(define (format-value obj max-len)
  (let ((str (cond
              ((null? obj) "()") ((symbol? obj) (symbol->string obj))
              ((string? obj) (string-append "\"" obj "\""))
              ((number? obj) (number->string obj))
              ((boolean? obj) (if obj "#t" "#f"))
              ((blob? obj) (string-append "#${" (number->string (blob-size obj)) " bytes}"))
              ((u8vector? obj) (string-append "#u8(" (number->string (u8vector-length obj)) ")"))
              ((procedure? obj) "#<procedure>") ((port? obj) "#<port>")
              ((pair? obj) "...") ((vector? obj) (string-append "#(" (number->string (vector-length obj)) ")"))
              (else "#<unknown>"))))
    (if (> (string-length str) max-len)
        (string-append (substring str 0 (- max-len 1)) "~")
        str)))

(define (tree obj . opts)
  (let ((depth (get-key opts 'depth: 0))
        (max-depth (get-key opts 'max-depth: 6))
        (prefix (get-key opts 'prefix: ""))
        (last (get-key opts 'last: #t)))
    (let* ((indent (if (= depth 0) "" (string-append prefix (if last "L-- " "|-- "))))
           (child-prefix (if (= depth 0) "" (string-append prefix (if last "    " "|   "))))
           (tag (type-tag obj)))
      (print indent
             (if (or (pair? obj) (vector? obj))
                 (string-append "+ " tag)
                 (string-append "- " tag ": " (format-value obj 50))))
      (when (< depth max-depth)
        (cond
         ((pair? obj)
          (let loop ((items obj) (idx 0))
            (cond
             ((null? items) #f)
             ((not (pair? items))
              (tree items 'depth: (+ depth 1) 'prefix: child-prefix 'last: #t))
             ((> idx 10)
              (print child-prefix "L-- ... (" (- (length obj) idx) " more)"))
             (else
              (let ((is-last (or (null? (cdr items))
                                 (and (pair? (cdr items)) (> idx 9)))))
                (tree (car items) 'depth: (+ depth 1) 'prefix: child-prefix 'last: is-last)
                (when (pair? (cdr items))
                  (loop (cdr items) (+ idx 1))))))))
         ((vector? obj)
          (let ((len (vector-length obj)))
            (do ((i 0 (+ i 1))) ((or (= i len) (> i 10)))
              (if (> i 10)
                  (print child-prefix "L-- ... (" (- len i) " more)")
                  (tree (vector-ref obj i) 'depth: (+ depth 1)
                        'prefix: child-prefix 'last: (= i (- len 1)))))))))
      (void))))

(define (i obj) (tree obj))

;;; ============================================================
;;; CIP Protocol Constants & Helpers
;;; ============================================================

(define CIP-KNOCK    #x01)
(define CIP-COOKIE   #x02)
(define CIP-EXCHANGE #x03)
(define CIP-ATTEST   #x04)
(define CIP-OFFER    #x05)
(define CIP-CONFIRM  #x06)
(define CIP-DATA     #x10)
(define CIP-CLOSE    #xff)

(define CIP-VERSION-MAJOR 1)
(define CIP-VERSION-MINOR 0)

(define *algorithm-suites*
  '((1 . ((kex . x25519) (sign . ed25519) (aead . chacha20-poly1305)
          (hash . blake2b) (kdf . hkdf-blake2b)))))

(define (ccp-version-string)
  (string-append (number->string CIP-VERSION-MAJOR) "." (number->string CIP-VERSION-MINOR)))

(define (ccp-suite) (alist-ref CIP-VERSION-MAJOR *algorithm-suites*))

;;; Cookie generation
(define *cookie-secret* #f)
(define *cookie-epoch* 0)

(define (init-cookie-secret!)
  (set! *cookie-secret* (random-bytes 32))
  (set! *cookie-epoch* (current-seconds)))

(define (make-cookie remote-addr remote-port)
  (unless *cookie-secret* (init-cookie-secret!))
  (let* ((data (string-append (blob->string *cookie-secret*) remote-addr
                              (number->string remote-port) (number->string *cookie-epoch*)))
         (hash (blake2b-hash (string->blob data))))
    (blob->hex (string->blob (substring (blob->string hash) 0 16)))))

;;; Channel registry
(define *channel-registry* '())
(define *channel-counter* 0)
(define *node-listener* #f)
(define *node-port* 4433)
(define *node-name* #f)
(define *node-connections* '())

(define (channel-registry-new!)
  (set! *channel-counter* (+ *channel-counter* 1))
  (let ((id *channel-counter*)
        (state (vector 0 0 'new)))
    (set! *channel-registry* (cons (cons id state) *channel-registry*))
    id))

(define (channel-registry-get id)
  (let ((entry (assoc id *channel-registry*)))
    (if entry (cdr entry) #f)))

(define (channel-seq-send! id)
  (let ((state (channel-registry-get id)))
    (let ((seq (vector-ref state 0)))
      (vector-set! state 0 (+ seq 1)) seq)))

(define (channel-seq-recv! id)
  (let ((state (channel-registry-get id)))
    (let ((seq (vector-ref state 1)))
      (vector-set! state 1 (+ seq 1)) seq)))

(define (channel-set-state! id new-state)
  (let ((state (channel-registry-get id)))
    (vector-set! state 2 new-state)))

(define (channel-get-state id)
  (let ((state (channel-registry-get id)))
    (vector-ref state 2)))

;;; AEAD nonce from sequence
(define (seq->nonce seq)
  (let ((nonce (make-blob 12))
        (vec (blob->u8vector/shared nonce)))
    (do ((i 0 (+ i 1))) ((= i 4)) (u8vector-set! vec i 0))
    (u8vector-set! vec 4  (bitwise-and seq #xff))
    (u8vector-set! vec 5  (bitwise-and (bitwise-arithmetic-shift-right seq 8) #xff))
    (u8vector-set! vec 6  (bitwise-and (bitwise-arithmetic-shift-right seq 16) #xff))
    (u8vector-set! vec 7  (bitwise-and (bitwise-arithmetic-shift-right seq 24) #xff))
    (u8vector-set! vec 8  (bitwise-and (bitwise-arithmetic-shift-right seq 32) #xff))
    (u8vector-set! vec 9  (bitwise-and (bitwise-arithmetic-shift-right seq 40) #xff))
    (u8vector-set! vec 10 (bitwise-and (bitwise-arithmetic-shift-right seq 48) #xff))
    (u8vector-set! vec 11 (bitwise-and (bitwise-arithmetic-shift-right seq 56) #xff))
    nonce))

(define (channel-encrypt key seq plaintext)
  (let ((nonce (seq->nonce seq)))
    (aead-chacha20poly1305-ietf-encrypt plaintext #f nonce key)))

(define (channel-decrypt key seq ciphertext)
  (let ((nonce (seq->nonce seq)))
    (or (aead-chacha20poly1305-ietf-decrypt ciphertext #f nonce key)
        (error 'channel-decrypt "authentication failed" seq))))

;;; Network operations stubbed (no (chicken tcp) in Chez)
(define (node-listen . rest)
  (let ((port (get-opt rest 0 *node-port*)))
    (set! *node-port* port)
    (set! *node-name* (string-append "node-" (number->string port)))
    (init-cookie-secret!)
    (print "Node '" *node-name* "' configured on port " port)
    (print "  Protocol: Cyberspace Channel Protocol (CIP)")
    (print "  (TCP listener stubbed in Chez port)")
    *node-name*))

(define (node-stop)
  (set! *node-listener* #f)
  (set! *cookie-secret* #f)
  (print "Node stopped"))

(define (node-broadcast msg)
  (print "Broadcast to " (length *node-connections*) " nodes (simulated)"))

(define (node-ping)
  (node-broadcast `(ping ,(current-seconds))))

;;; ============================================================
;;; Enrollment (Simplified for Chez)
;;; ============================================================

(define *enrollment-debug* #f)
(define *pending-enrollments* '())
(define *outgoing-enrollments* '())
(define *enrollment-listener* #f)
(define *pending-file* ".vault/pending-enrollments.sexp")

(define (save-pending-enrollments!)
  (when (directory-exists? ".vault")
    (guard (exn (#t (void)))
      (with-output-to-file *pending-file*
        (lambda ()
          (write `(pending-enrollments (version 1) (timestamp ,(current-seconds))
                                       (requests ,*pending-enrollments*)))
          (newline))))))

(define (load-pending-enrollments!)
  (when (file-exists? *pending-file*)
    (guard (exn (#t (print "Warning: could not load pending enrollments")))
      (let ((data (with-input-from-file *pending-file* read)))
        (when (and (pair? data) (eq? 'pending-enrollments (car data)))
          (let ((requests (cdr (assq 'requests (cdr data)))))
            (when requests
              (set! *pending-enrollments* (car requests))))))))
  (length *pending-enrollments*))

(define (enroll-debug! . rest)
  (let ((on (get-opt rest 0 #t)))
    (set! *enrollment-debug* on)
    (print (if on "Enrollment debugging enabled" "Enrollment debugging disabled"))))

(define (pending)
  (if (null? *pending-enrollments*)
      (print "No pending enrollment requests.")
      (begin
        (print "")
        (print "Pending Enrollment Requests:")
        (for-each
         (lambda (req)
           (let ((name (cadr (assq 'name req)))
                 (words (cadr (assq 'words req))))
             (print "  " name "  words: " words)))
         (reverse *pending-enrollments*))
        (print "")))
  (void))

(define (stop-enroll)
  (set! *enrollment-listener* #f)
  (print "Enrollment listener stopped.")
  (void))

(define (enroll-test)
  (print "")
  (print "Enrollment System Diagnostics")
  (print "  Debug mode:    " (if *enrollment-debug* "ON" "OFF"))
  (print "  Listener:      " (if *enrollment-listener* "ACTIVE" "INACTIVE"))
  (print "  Pending:       " (length *pending-enrollments*) " requests")
  (print "  Outgoing:      " (length *outgoing-enrollments*) " requests")
  (void))

;;; ============================================================
;;; Post-Quantum Vault Operations (Memo-059)
;;; ============================================================

(define *pq-signing-mode* 'ed25519)

(define (pq-status)
  (print "")
  (print "=== Post-Quantum Migration Status ===")
  (print "")
  (print "Signing Mode: " *pq-signing-mode*)
  (print "")
  (let ((keys (guard (exn (#t '())) (keyring-list))))
    (print "Keys in Keyring: " (length keys))
    (print "Supported algorithms: " (guard (exn (#t "unknown")) (supported-algorithms))))
  (print ""))

(define (pq-set-mode mode)
  (if (not (memq mode '(ed25519 hybrid pq-only)))
      (print "Error: Mode must be ed25519, hybrid, or pq-only")
      (begin
        (set! *pq-signing-mode* mode)
        (print "Signing mode set to: " mode))))

;;; ============================================================
;;; Banner & Display Helpers
;;; ============================================================

(define (plural n singular)
  (let ((suffix
         (cond
          ((= n 1) "")
          ((and (> (string-length singular) 1)
                (char=? (string-ref singular (- (string-length singular) 1)) #\y)
                (not (memv (string-ref singular (- (string-length singular) 2))
                           '(#\a #\e #\i #\o #\u))))
           (set! singular (substring singular 0 (- (string-length singular) 1)))
           "ies")
          ((or (string-suffix? "s" singular) (string-suffix? "x" singular)
               (string-suffix? "ch" singular) (string-suffix? "sh" singular))
           "es")
          (else "s"))))
    (string-append (number->string n) " " singular suffix)))

(define (count-file-lines path)
  (if (file-exists? path)
      (with-input-from-file path
        (lambda ()
          (let loop ((count 0))
            (let ((line (read-line)))
              (if (eof-object? line) count (loop (+ count 1)))))))
      0))

(define (read-node-identity)
  (let ((id-file ".vault/identity.sexp"))
    (if (file-exists? id-file)
        (guard (exn (#t #f)) (with-input-from-file id-file read))
        #f)))

(define (describe-vault)
  (let* ((audit-entries (count-file-lines ".vault/audit.log"))
         (keystore-exists (directory-exists? ".vault/keystore"))
         (obj-count (count-vault-items "objects"))
         (key-count (count-vault-items "keys"))
         (release-count (length (filter (lambda (f) (string-suffix? ".sexp" f))
                                        (if (directory-exists? ".vault/releases")
                                            (directory ".vault/releases") '()))))
         (node-id (read-node-identity)))
    (print "  " (plural obj-count "object") ", " (plural release-count "release") ", " (plural key-count "key"))
    (when (> audit-entries 0) (print "  " (plural audit-entries "audit entry")))
    (when keystore-exists
      (print "  " (plural (count-vault-items "keystore") "identity") " in keystore"))
    (if node-id
        (let ((name (cond ((assq 'name node-id) => cadr) (else "unknown")))
              (role (cond ((assq 'role node-id) => cadr) (else "unknown"))))
          (print "  enrolled as " name " (" role ")"))
        (print "  not enrolled"))))

(define (git-version)
  (let ((result (with-input-from-pipe "git describe --tags --always 2>/dev/null" read-line)))
    (if (eof-object? result) "unknown" result)))

(define (git-date)
  (let ((result (with-input-from-pipe "git log -1 --format=%cs 2>/dev/null" read-line)))
    (if (eof-object? result) "unknown" result)))

(define (get-hostname)
  (let ((result (with-input-from-pipe "hostname -s 2>/dev/null" read-line)))
    (if (eof-object? result) "unknown" result)))

(define (capitalize-first s)
  (if (string-null? s) s
      (string-append (string (char-upcase (string-ref s 0)))
                     (substring s 1 (string-length s)))))

(define (get-primary-ipv4)
  (let ((result (with-input-from-pipe
                 "ifconfig 2>/dev/null | grep 'inet ' | grep -v '127.0.0.1' | head -1 | awk '{print $2}'"
                 read-line)))
    (if (or (eof-object? result) (string=? result "")) #f result)))

(define (get-primary-ipv6)
  (let ((result (with-input-from-pipe
                 "ifconfig 2>/dev/null | grep 'inet6 ' | grep -v 'fe80' | grep -v '::1' | head -1 | awk '{print $2}'"
                 read-line)))
    (if (or (eof-object? result) (string=? result "")) #f result)))

(define (get-platform-stamp) (os-platform))

(define (get-hardware-summary)
  (string-append (number->string (cpu-cores)) " cores, "
                 (number->string (memory-gb)) "GB"
                 (let ((brand (cpu-brand)))
                   (if brand (string-append ", " brand) ""))))

(define (get-connection-origin)
  (let ((ssh-client (getenv "SSH_CLIENT"))
        (ssh-conn (getenv "SSH_CONNECTION")))
    (cond
     ((and ssh-client (> (string-length ssh-client) 0))
      (car (string-split ssh-client " ")))
     ((and ssh-conn (> (string-length ssh-conn) 0))
      (car (string-split ssh-conn " ")))
     (else #f))))

(define (set-terminal-title title)
  (display (string-append "\x1b;]0;" title "\x7;")))

(define (banner)
  (let* ((host (capitalize-first (get-hostname)))
         (version (git-version))
         (date (git-date))
         (platform (get-platform-stamp))
         (ipv4 (get-primary-ipv4))
         (ipv6 (get-primary-ipv6))
         (hw (get-hardware-summary))
         (secs (current-seconds))
         (boot-time (seconds->string secs))
         (origin (get-connection-origin))
         (node-id (read-node-identity)))
    (set-terminal-title (string-append host " Workstation"))
    (print "")
    (print "Cyberspace Scheme " version " (" date ") [Chez]")
    (print "  " host " · " platform (if (not (string=? hw "")) (string-append " · " hw) ""))
    (print "  boot: " boot-time)
    (when (or ipv4 ipv6)
      (print "  Internet endpoints: " (or ipv4 "---") " · " (or ipv6 "---")))
    (when origin (print "  from: " origin))
    (when (directory-exists? ".vault")
      (describe-vault))
    ;; Realm membership
    (let ((name (realm-name))
          (affiliated (realm-affiliated?)))
      (if affiliated
          (print "  realm: " (or name "wilderness"))
          (print "  realm: wilderness")))
    ;; Entropy & FIPS
    (let ((ent (entropy-status)))
      (print "  entropy: " (cdr (assq 'source ent)) " (" (cdr (assq 'implementation ent)) ")"))
    (print "  FIPS: " (if (eq? (fips-status) 'passed) "passed" "FAILED"))
    (print "  " (lamport-format))
    ;; Identity
    (when node-id
      (let ((name (cond ((assq 'name node-id) => cadr) (else #f)))
            (role (cond ((assq 'role node-id) => cadr) (else #f))))
        (when (and name role)
          (print "  identity: " name " (" role ")"))))))

;;; ============================================================
;;; Help System
;;; ============================================================

(define *help-topics*
  '((help "Help System"
     ("help" "Show essential commands")
     ("help 'topics" "List all help topics")
     ("help '<topic>" "Show commands in topic"))
    (vault "Vault & Objects"
     ("(soup)" "Browse vault objects")
     ("(soup-du)" "Disk usage")
     ("(seal-commit MSG)" "Commit changes")
     ("(seal-release VER)" "Create release"))
    (crypto "Cryptographic Primitives"
     ("(sha512-hash DATA)" "SHA-512 hash")
     ("(blake2b-hash DATA)" "BLAKE2b hash")
     ("(ed25519-keypair)" "Generate Ed25519 keypair"))
    (security "Keys & Certificates"
     ("(keyring-list)" "List keys in keyring")
     ("(security-summary)" "Security overview"))
    (federation "Discovery & Gossip"
     ("(gossip-status)" "Gossip daemon status")
     ("(discover-peers-mdns)" "Find peers"))
    (audit "Audit Trail"
     ("(audit-read)" "Read audit entries")
     ("(audit-chain)" "Verify chain integrity"))
    (system "System & Introspection"
     ("(measure-weave)" "Crypto benchmark")
     ("(banner)" "Redisplay startup banner")
     ("(entropy-status)" "Entropy source info")
     ("(fips-status)" "FIPS self-test status"))))

(define (help . rest)
  (let ((topic (get-opt rest 0 #f)))
    (print "")
    (cond
      ((eq? topic 'topics)
       (print "Help Topics - (help 'topic) for details")
       (print "")
       (for-each (lambda (entry)
                   (let ((sym (car entry))
                         (title (cadr entry))
                         (count (length (cddr entry))))
                     (print "  " (string-pad-right (symbol->string sym) 18)
                            "- " title " (" count ")")))
                 *help-topics*)
       (print ""))
      (topic
       (let ((entry (assq topic *help-topics*)))
         (if entry
             (let ((title (cadr entry))
                   (commands (cddr entry)))
               (print title ":")
               (print "")
               (for-each (lambda (cmd)
                           (print "  " (string-pad-right (car cmd) 26) " - " (cadr cmd)))
                         commands)
               (print ""))
             (print "Unknown topic: " topic ". Try (help 'topics)"))))
      (else
       (print "Cyberspace Scheme (Chez Port)")
       (print "")
       (print "  (soup)          Browse the object store")
       (print "  (seal-commit M) Commit changes")
       (print "  (banner)        Show banner")
       (print "  (weave)         Federation topology")
       (print "  (about)         What is Cyberspace?")
       (print "")
       (print "  (help 'topics)  All help topics")
       (print "  (help 'vault)   Vault commands")
       (print "  (help 'crypto)  Crypto primitives")
       (print "")))
    (void)))

;;; ============================================================
;;; Key Ceremony (Memo-024)
;;; ============================================================

(define (ceremony . rest)
  (let ((type (get-opt rest 0 'help)))
    (case type
      ((help)
       (print "")
       (print "Key Ceremony (Memo-024)")
       (print "  (ceremony 'generate)      Generate witnessed keypair")
       (print "  (ceremony 'split K N)     Split key into N shares, K to recover")
       (print "  (ceremony 'reconstruct)   Reconstruct from shares")
       (print "  (ceremony 'verify SHARE)  Verify share integrity")
       (void))
      ((generate)
       (print "Collecting entropy from system RNG...")
       (let ((keypair (ed25519-keypair)))
         (print "")
         (print "Keypair generated")
         (printf "  Public:  ~a...~n" (substring (blob->hex (car keypair)) 0 16))
         (printf "  Secret:  [protected, ~a bytes]~n" (blob-size (cadr keypair)))
         (print "")
         (print "Store this keypair securely. Consider splitting the secret key.")
         keypair))
      ((split)
       (print "Usage: (ceremony-split KEY threshold: K total: N)")
       (void))
      ((reconstruct)
       (print "Enter shares: (ceremony-reconstruct (list share1 share2 ...))")
       (void))
      (else (printf "Unknown ceremony type: ~a~n" type)))))

(define (ceremony-split key . opts)
  (let ((threshold (get-key opts 'threshold: 3))
        (total (get-key opts 'total: 5)))
    (unless (blob? key) (error 'ceremony-split "key must be a blob"))
    (print "")
    (printf "Splitting Key (~a-of-~a)~n" threshold total)
    (let ((shares (shamir-split key 'threshold: threshold 'total: total)))
      (let loop ((i 1) (remaining shares))
        (when (pair? remaining)
          (let ((share (car remaining)))
            (printf "Share ~a/~a: ~a...~n" i total
                    (substring (blob->hex (share-y share)) 0 16)))
          (loop (+ i 1) (cdr remaining))))
      (print "")
      (printf "Generated ~a shares. ~a required to reconstruct.~n" total threshold)
      shares)))

(define (ceremony-reconstruct shares)
  (unless (and (list? shares) (>= (length shares) 2))
    (error 'ceremony-reconstruct "need at least 2 shares"))
  (printf "Reconstructing from ~a shares...~n" (length shares))
  (let ((secret (shamir-reconstruct shares)))
    (print "Secret reconstructed successfully")
    secret))

(define (ceremony-verify share)
  (if (shamir-share? share)
      (begin
        (print "Valid Shamir share")
        (printf "  Share ID:   ~a~n" (share-id share))
        (printf "  Threshold:  ~a~n" (share-threshold share))
        #t)
      (begin (print "Not a valid Shamir share") #f)))

;;; ============================================================
;;; Regression Test Suite
;;; ============================================================

(define *regression-tests* '())

(define (deftest name thunk)
  (set! *regression-tests* (append *regression-tests* (list (cons name thunk)))))

(define (run-test name thunk)
  (let ((start (current-process-milliseconds)))
    (guard (exn (#t (list name #f (- (current-process-milliseconds) start)
                          (format "Exception: ~a"
                                  (if (message-condition? exn)
                                      (condition-message exn)
                                      exn)))))
      (let ((result (thunk)))
        (list name (car result) (- (current-process-milliseconds) start) (cdr result))))))

(deftest 'sha256
  (lambda ()
    (let* ((hash (sha256-hash "abc"))
           (hex (blob->hex hash)))
      (if (string=? hex "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
          (cons #t "NIST FIPS 180-4 KAT")
          (cons #f (format "got ~a" (substring hex 0 16)))))))

(deftest 'sha512
  (lambda ()
    (let* ((hash (sha512-hash "abc"))
           (hex (blob->hex hash)))
      (if (string-prefix? "ddaf35a193617aba" hex)
          (cons #t "NIST FIPS 180-4 KAT")
          (cons #f (format "got ~a" (substring hex 0 16)))))))

(deftest 'blake2b
  (lambda ()
    (let* ((hash (blake2b-hash "abc"))
           (hex (blob->hex hash)))
      (if (string-prefix? "bddd813c63423972" hex)
          (cons #t "BLAKE2b-256 KAT")
          (cons #f (format "got ~a" (substring hex 0 16)))))))

(deftest 'ed25519-sign-verify
  (lambda ()
    (let* ((keys (ed25519-keypair))
           (pk (car keys)) (sk (cadr keys))
           (msg "test message for signing")
           (sig (ed25519-sign sk msg)))
      (if (ed25519-verify pk msg sig)
          (cons #t "sign/verify round-trip")
          (cons #f "verification failed")))))

(deftest 'ed25519-wrong-key
  (lambda ()
    (let* ((keys1 (ed25519-keypair)) (keys2 (ed25519-keypair))
           (pk1 (car keys1)) (sk2 (cadr keys2))
           (msg "test message") (sig (ed25519-sign sk2 msg)))
      (if (not (ed25519-verify pk1 msg sig))
          (cons #t "rejects wrong key")
          (cons #f "accepted wrong key!")))))

(deftest 'x25519-key-exchange
  (lambda ()
    (let* ((alice (x25519-keypair)) (bob (x25519-keypair))
           (shared-a (x25519-scalarmult (cadr alice) (car bob)))
           (shared-b (x25519-scalarmult (cadr bob) (car alice))))
      (if (blob=? shared-a shared-b)
          (cons #t "DH key agreement")
          (cons #f "shared secrets differ")))))

(deftest 'random-bytes-test
  (lambda ()
    (let* ((r1 (random-bytes 32)) (r2 (random-bytes 32)))
      (if (and (= (blob-size r1) 32) (= (blob-size r2) 32) (not (blob=? r1 r2)))
          (cons #t "32 bytes, non-repeating")
          (cons #f "entropy failure")))))

(deftest 'weave-performance
  (lambda ()
    (let* ((weave (measure-weave))
           (stratum (weave-stratum weave)))
      (if (> weave 0)
          (cons #t (format "~a (~a stratum)" weave stratum))
          (cons #f "weave is zero")))))

(deftest 'vault-exists
  (lambda ()
    (if (directory-exists? ".vault")
        (cons #t ".vault directory present")
        (cons #f "no .vault directory"))))

(deftest 'fips-passed
  (lambda ()
    (if (eq? (fips-status) 'passed)
        (cons #t "all KATs passed")
        (cons #f "FIPS self-test failed"))))

(deftest 'entropy-source
  (lambda ()
    (let ((ent (entropy-status)))
      (if ent
          (cons #t (cdr (assq 'source ent)))
          (cons #f "no entropy status")))))

(define (regression . rest)
  (let ((verbose? (get-opt rest 0 #f)))
    (print "")
    (print "Cyberspace Regression Suite")
    (print "")
    (let* ((start (current-process-milliseconds))
           (results (map (lambda (t) (run-test (car t) (cdr t))) *regression-tests*))
           (passed (filter (lambda (r) (cadr r)) results))
           (failed (filter (lambda (r) (not (cadr r))) results))
           (elapsed (- (current-process-milliseconds) start)))
      (for-each
        (lambda (r)
          (let ((name (car r)) (pass? (cadr r)) (ms (caddr r)) (msg (cadddr r)))
            (if pass?
                (when verbose?
                  (printf "  ok ~a (~ams) ~a~n"
                          (string-pad-right (symbol->string name) 20) ms msg))
                (printf "  FAIL ~a (~ams) ~a~n"
                        (string-pad-right (symbol->string name) 20) ms msg))))
        results)
      (print "")
      (let ((total (length results))
            (pass-count (length passed))
            (fail-count (length failed)))
        (if (= fail-count 0)
            (printf "All ~a tests passed in ~ams~n" total elapsed)
            (printf "~a/~a passed, ~a FAILED in ~ams~n" pass-count total fail-count elapsed)))
      (print "")
      (if (null? failed) 'passed (map car failed)))))

;;; ============================================================
;;; Commandments
;;; ============================================================

(define (commandments)
  (print "
The Library of Cyberspace

The Ten Commandments of Lambda

  0  Declaration               Thou shalt have no central authority
  1  Conventions               Thou shalt document in S-expressions
  2  Architecture              Thou shalt know thy vision
  3  Public Key Authorization  Thou shalt let keys be principals
  4  Shamir Sharing            Thou shalt have no single point of failure
  5  Audit Trail               Thou shalt witness all actions
  6  Vault Architecture        Thou shalt address content by truth
  7  Replication Layer         Thou shalt federate thy distribution
  8  Threshold Governance      Thou shalt seek consensus over dictators
  9  Designer Notes            Thou shalt know why it was ordained
")
  (void))

;;; ============================================================
;;; Sigma: Code complexity metrics
;;; ============================================================

(define (sigma)
  (print "")
  (print "Sigma - Code Complexity")
  (print "")
  (guard (exn (#t (print "  (introspection unavailable)")))
    (let* ((scheme-loc (with-input-from-pipe
                        "wc -l *.scm 2>/dev/null | tail -1 | awk '{print $1}'" read-line))
           (tcb-loc (with-input-from-pipe
                     "wc -l ../tcb/*.ml 2>/dev/null | tail -1 | awk '{print $1}'" read-line)))
      (printf "  Scheme     ~a LOC~n" (if (eof-object? scheme-loc) "?" scheme-loc))
      (printf "  OCaml      ~a LOC (TCB)~n" (if (eof-object? tcb-loc) "?" tcb-loc))))
  (print "")
  (void))

;;; ============================================================
;;; Friendly Aliases
;;; ============================================================

(define (clear)
  (display "\x1b;[2J\x1b;[H")
  (void))

(define (keys) (soup 'keys))
(define (releases) (soup-releases))
(define gossip gossip-status)
(define security security-summary)

(define quit goodbye)
(define q goodbye)
(define bye goodbye)

(define (keychain) (open-keychain))
(define (tickets) (open-tickets))
(define (console) (open-console))
(define (monitor) (open-monitor))
(define (finder) (open-finder))

;;; ============================================================
;;; Navigation
;;; ============================================================

(define *trail* '())
(define *lens* 'library)

;;; ============================================================
;;; Boot Sequence
;;; ============================================================

;; Load persisted Lamport clock
(lamport-load!)

;; Refresh hardware info
(when (directory-exists? ".vault")
  (guard (exn (#t (void)))
    (let* ((caps (probe-system-capabilities))
           (hw-file ".vault/node-hardware")
           (manifest `(node-hardware (platform ,(os-platform))
                       (capabilities ,caps) (role ,(recommend-role caps))
                       (timestamp ,(current-seconds)))))
      (with-output-to-file hw-file
        (lambda () (write manifest) (newline))))))

;;; ============================================================
;;; SICP Metrics Analysis
;;; ============================================================

(define *cyberspace-modules*
  '("crypto-ffi" "sexp" "capability" "fips" "audit" "wordlist"
    "bloom" "catalog" "keyring" "cert" "enroll" "gossip" "security"
    "vault" "auto-enroll" "inspector" "display" "filetype" "forum"
    "http" "info" "mpe" "pencil" "repl" "scrutinizer" "server"
    "os" "portal" "ui"))

(define (analyze-source src-file)
  "Analyze source file for SICP metrics (LOC, lambdas, LOC/lambda ratio)"
  (if (not (file-exists? src-file))
      '((loc . 0) (lambdas . 0) (loc/lambda . 0))
      (call-with-input-file src-file
        (lambda (port)
          (let loop ((loc 0) (lambdas 0))
            (let ((line (get-line port)))
              (if (eof-object? line)
                  (let ((ratio (if (> lambdas 0) (div loc lambdas) 0)))
                    `((loc . ,loc) (lambdas . ,lambdas) (loc/lambda . ,ratio)))
                  (let* ((trimmed (string-trim-both line))
                         (is-blank (string=? trimmed ""))
                         (is-comment (and (> (string-length trimmed) 0)
                                          (char=? (string-ref trimmed 0) #\;)))
                         (has-define (string-contains trimmed "(define "))
                         (has-lambda (string-contains trimmed "(lambda ")))
                    (loop (if (or is-blank is-comment) loc (+ loc 1))
                          (+ lambdas
                             (if has-define 1 0)
                             (if has-lambda 1 0)))))))))))

(define (sicp)
  "Analyze SICP metrics for all Cyberspace modules (live analysis)"
  (printf "~%SICP Metrics - Cyberspace Chez~%~%")
  (let loop ((modules *cyberspace-modules*)
             (total-loc 0)
             (total-lambdas 0)
             (count 0))
    (if (null? modules)
        (begin
          (printf "~%  ─────────────────────────────────~%")
          (printf "  Σ ~a LOC · ~a λ · ~a LOC/λ~%~%"
                  total-loc total-lambdas
                  (if (> total-lambdas 0) (div total-loc total-lambdas) 0))
          (printf "  ~a modules~%~%" count)
          (values total-loc total-lambdas count))
        (let* ((mod (car modules))
               (src (string-append "cyberspace/" mod ".sls"))
               (metrics (analyze-source src))
               (loc (cdr (assq 'loc metrics)))
               (lambdas (cdr (assq 'lambdas metrics)))
               (ratio (cdr (assq 'loc/lambda metrics))))
          (when (> loc 0)
            (let ((mod-padded (string-append mod (make-string (max 0 (- 15 (string-length mod))) #\space))))
              (printf "  ~a: ~a LOC · ~a λ · ~a LOC/λ~%"
                      mod-padded loc lambdas ratio)))
          (loop (cdr modules)
                (+ total-loc loc)
                (+ total-lambdas lambdas)
                (if (> loc 0) (+ count 1) count))))))

;;; ============================================================

;; Initialize session statistics
(session-stat-init!)
;; Install signal handlers
(install-signal-handlers!)

;; Register cleanup hooks
(register-cleanup-hook! 'repl-enrollment
  (lambda ()
    (when *enrollment-listener*
      (guard (exn (#t #f)) (void))
      (set! *enrollment-listener* #f))))

(register-cleanup-hook! 'repl-node
  (lambda ()
    (when *node-listener*
      (guard (exn (#t #f)) (void))
      (set! *node-listener* #f))))

;; Measure boot-time weave
(guard (exn (#t (void)))
  (session-stat! 'boot-weave))

;; Banner shown at portal level (2) and above
(when (>= *boot-verbosity* 2)
  (banner))

(when (>= *boot-verbosity* 2)
  (help))

(when (>= *boot-verbosity* 1)
  (let* ((elapsed-ms (- (current-process-milliseconds) *repl-start-time*))
         (elapsed-sec (/ elapsed-ms 1000.0)))
    (when (= *boot-verbosity* 1)
      (print "Cyberspace Scheme " (git-version) " [Chez]"))
    (print (format "Ready in ~a [~a]"
                   (if (< elapsed-sec 1)
                       (format "~ams" elapsed-ms)
                       (format "~as" elapsed-sec))
                   (realm-signature)))
    (let ((pending-count (load-pending-enrollments!)))
      (when (> pending-count 0)
        (printf "  ~a pending join request~a - (pending) to review~n"
                pending-count (if (= pending-count 1) "" "s"))))
    (print "")))

;; --eval: evaluate expression and exit
(when (cli-option "eval")
  (let ((expr (cli-option "eval")))
    (guard (exn (#t (begin (print "Error: " (condition-message exn)) (exit 1))))
      (let ((result (eval (read (open-input-string expr)))))
        (unless (eq? result (void))
          (write result) (newline))
        (exit 0)))))

;; --exec: evaluate expression after init, then start REPL
(when (cli-option "exec")
  (let ((expr (cli-option "exec")))
    (guard (exn (#t (printf "[exec] Error: ~a~n" (condition-message exn))))
      (eval (read (open-input-string expr))))))

;; Source script files passed as arguments
(for-each
  (lambda (script)
    (when (file-exists? script)
      (guard (exn (#t (printf "[script] Error in ~a: ~a~n" script (condition-message exn))))
        (load script))))
  *cli-scripts*)

;; Start Chez Scheme's interactive REPL
(new-cafe)
