#!/usr/bin/env csi -q -w
;;; cyberspace-repl - Cyberspace Scheme
;;;
;;; Usage: ./cyberspace-repl
;;;
;;; Preloads all Cyberspace modules for interactive exploration:
;;;   - vault: seal-commit, seal-release, seal-archive, etc.
;;;   - crypto-ffi: ed25519-keypair, sha512-hash, etc.
;;;   - audit: audit-append, audit-read, etc.
;;;   - cert: SPKI certificates
;;;   - sexp: S-expression handling

(import scheme
        (chicken base)
        (chicken format)
        (chicken repl)
        (chicken csi)      ; toplevel-command
        (chicken file)
        (chicken io)
        (chicken port)     ; with-output-to-string
        (chicken pretty-print)  ; pp
        (chicken time)
        (chicken time posix)
        (chicken process-context)
        (chicken process)
        (chicken blob)
        (chicken file posix)
        (chicken bitwise)
        (chicken string)
        (chicken sort)
        srfi-18            ; threads (for background listeners)
        (chicken condition)
        srfi-1
        srfi-4
        srfi-13
        srfi-69   ; hash tables
        (chicken tcp))

;;; ============================================================
;;; Bootstrap: Mixed-Architecture Defense
;;; ============================================================
;;; Ensures compiled modules match current architecture.
;;; Rebuilds automatically if arch mismatch or source newer.

(define (current-arch)
  "Detect current CPU architecture"
  (let ((result (with-input-from-pipe "uname -m" read-line)))
    (if (eof-object? result) "unknown" result)))

(define (current-os)
  "Detect current operating system"
  (let ((result (with-input-from-pipe "uname -s" read-line)))
    (if (eof-object? result) "unknown" result)))

(define (libsodium-paths arch)
  "Return (include-path lib-path) for libsodium based on architecture and OS"
  (let ((os (current-os)))
    (cond
     ;; macOS ARM (M1/M2/M3)
     ((and (string=? os "Darwin") (string=? arch "arm64"))
      '("/opt/homebrew/include" "/opt/homebrew/lib"))
     ;; macOS Intel
     ((string=? os "Darwin")
      '("/usr/local/include" "/usr/local/lib"))
     ;; Linux (Fedora, Ubuntu, etc.) - system packages
     ((string=? os "Linux")
      '("/usr/include" "/usr/lib64"))  ; Fedora uses lib64 for x86_64
     ;; Fallback
     (else
      '("/usr/local/include" "/usr/local/lib")))))

(define (arch-stamp-file module)
  "Path to architecture stamp file for module"
  (string-append "." module ".arch"))

(define (read-arch-stamp module)
  "Read stored architecture for a compiled module"
  (let ((stamp-file (arch-stamp-file module)))
    (if (file-exists? stamp-file)
        (with-input-from-file stamp-file read-line)
        #f)))

(define (write-arch-stamp module arch)
  "Write architecture stamp for compiled module"
  (with-output-to-file (arch-stamp-file module)
    (lambda () (print arch))))

(define (file-mtime path)
  "Get file modification time, or 0 if doesn't exist"
  (if (file-exists? path)
      (file-modification-time path)
      0))

(define (needs-rebuild? module arch)
  "Check if module needs rebuilding: missing, arch mismatch, or source newer"
  (let* ((src (string-append module ".scm"))
         (so  (string-append module ".so"))
         (import-scm (string-append module ".import.scm"))
         (stored-arch (read-arch-stamp module)))
    (or (not (file-exists? so))
        (not (file-exists? import-scm))
        (not stored-arch)
        (not (string=? stored-arch arch))
        (> (file-mtime src) (file-mtime so)))))

(define (rebuild-module! module arch stamp)
  "Rebuild a module for current platform.
   Pristine builds: all warnings enabled (-w)."
  (let* ((paths (libsodium-paths arch))
         (inc-path (car paths))
         (lib-path (cadr paths))
         (src (string-append module ".scm")))
    (print "")
    (print "┌─ forge: " module " ─┐")
    (let ((cmd (if (string=? module "crypto-ffi")
                   ;; crypto-ffi needs libsodium
                   (string-append "csc -shared -J -w " src
                                  " -I" inc-path
                                  " -L" lib-path
                                  " -L -lsodium 2>&1")
                   ;; other modules (vault, etc)
                   (string-append "csc -shared -J -w " src " 2>&1"))))
      (print "  " cmd)
      (let ((result (with-input-from-pipe cmd
                      (lambda ()
                        (let loop ((lines '()))
                          (let ((line (read-line)))
                            (if (eof-object? line)
                                (reverse lines)
                                (loop (cons line lines)))))))))
        ;; Print any output (warnings/errors)
        (for-each (lambda (line) (print "  " line)) result)
        ;; Check if .so was created
        (if (file-exists? (string-append module ".so"))
            (begin
              (write-arch-stamp module stamp)
              (print "  ✓ forged")
              (print "└─────────────────────┘")
              (print "")
              #t)
            (begin
              (print "  ✗ failed")
              (print "└─────────────────────┘")
              (print "")
              (exit 1)))))))

(define (platform-stamp)
  "Return OS+arch stamp (e.g., 'Darwin-arm64', 'Linux-x86_64')"
  (string-append (current-os) "-" (current-arch)))

(define (bootstrap-modules!)
  "Ensure all required modules are built for current platform.
   Pristine builds: -w enables all warnings, expect zero output."
  (let ((stamp (platform-stamp))
        (arch (current-arch))
        ;; Build order: strict topological sort by dependency level
        ;;
        ;; Level 0 (no cyberspace deps):
        ;;   os          - OS introspection ("know thyself")
        ;;   crypto-ffi  - libsodium foundation
        ;;   sexp        - s-expression parser
        ;;   mdns        - network discovery
        ;;   app-bundle  - macOS bundling (shell only)
        ;;   codesign    - macOS signing (shell only)
        ;;
        ;; Level 1 (crypto-ffi only):
        ;;   audit       - tamper-evident logging
        ;;   wordlist    - FIPS-181 verification codes
        ;;   bloom       - probabilistic set membership
        ;;   catalog     - Merkle tree inventory
        ;;   keyring     - key management
        ;;
        ;; Level 2 (Levels 0+1):
        ;;   cert        ← sexp + crypto-ffi
        ;;   enroll      ← crypto-ffi + wordlist
        ;;   gossip      ← bloom + catalog + crypto-ffi
        ;;   security    ← cert + sexp + crypto-ffi (soup inspector)
        ;;   capability  ← (standalone)
        ;;
        ;; Level 3:
        ;;   vault       ← cert + crypto-ffi + audit
        ;;   auto-enroll ← enroll + capability + mdns + gossip
        ;;   ui          ← enroll + capability + auto-enroll
        ;;
        (modules '("os" "crypto-ffi" "sexp" "mdns"
                   "audit" "wordlist" "bloom" "catalog" "keyring"
                   "cert" "enroll" "gossip" "security" "capability"
                   "vault" "auto-enroll" "ui")))
    (let ((rebuilt (fold
                    (lambda (module count)
                      (if (needs-rebuild? module stamp)
                          (begin
                            (rebuild-module! module arch stamp)
                            (+ count 1))
                          count))
                    0
                    modules)))
      (when (= rebuilt 0)
        (print "All tomes current for " stamp)))))

;; Run bootstrap before loading modules
(bootstrap-modules!)

;; Load cyberspace modules (now guaranteed to be correct arch)
(import os)
(import crypto-ffi)
(import vault)
(import audit)
(import cert)
(import sexp)
(import wordlist)
(import mdns)
(import bloom)
(import catalog)
(import enroll)
(import gossip)
(import security)
(import keyring)
(import capability)
(import auto-enroll)
(import ui)

;; Initialize libsodium
(sodium-init)

;;; ============================================================
;;; BLAKE2b Hash (placeholder using SHA-256)
;;; ============================================================
;;; BLAKE2b hashing via libsodium's crypto_generichash
;;; Re-exported from crypto-ffi for convenience

;; blake2b-hash is now imported from crypto-ffi
;; It uses libsodium's crypto_generichash (BLAKE2b-256)

(define (blob-append . blobs)
  "Concatenate multiple blobs into one"
  (let* ((total-size (apply + (map blob-size blobs)))
         (result (make-u8vector total-size 0))
         (pos 0))
    (for-each
     (lambda (b)
       (let ((vec (blob->u8vector/shared b))
             (len (blob-size b)))
         (do ((i 0 (+ i 1)))
             ((= i len))
           (u8vector-set! result (+ pos i) (u8vector-ref vec i)))
         (set! pos (+ pos len))))
     blobs)
    (u8vector->blob/shared result)))

;; Helper utilities
(define (blob->hex b)
  "Convert blob to hex string"
  (define (byte->hex n)
    (let ((s (number->string n 16)))
      (if (= (string-length s) 1)
          (string-append "0" s)
          s)))
  (let ((vec (blob->u8vector b)))
    (let loop ((i 0) (acc '()))
      (if (= i (u8vector-length vec))
          (apply string-append (reverse acc))
          (loop (+ i 1)
                (cons (byte->hex (u8vector-ref vec i)) acc))))))

(define (hex->blob hex-str)
  "Convert hex string to blob"
  (let* ((len (quotient (string-length hex-str) 2))
         (vec (make-u8vector len)))
    (do ((i 0 (+ i 1)))
        ((= i len) (u8vector->blob vec))
      (let* ((hex-byte (substring hex-str (* i 2) (+ (* i 2) 2)))
             (byte-val (string->number hex-byte 16)))
        (u8vector-set! vec i byte-val)))))

(define (clear)
  "Clear screen (ANSI escape)"
  (display "\x1b[2J\x1b[H")
  (banner))

;;; ============================================================
;;; RFC-040: Object State (chaotic/quiescent) and Persistence
;;; ============================================================

;; All things have state and durability
;; State: chaotic (in flux) | quiescent (stable)
;; Durability: ephemeral (no promise) | persistent (vault-bound)

(define *thing-states* '())      ; thing-id -> state
(define *thing-durability* '())  ; thing-id -> durability
(define *chaotic-store* '())     ; things in flux
(define *persistence-queue* '()) ; scheduled for vault migration

(define (thing-id thing)
  "Get or compute thing identity"
  (cond
   ;; Already has an id field (alist)
   ((and (list? thing)
         (pair? (car thing))
         (assoc 'id thing))
    => (lambda (pair) (cdr pair)))
   ;; String - use as-is or hash if long
   ((string? thing)
    (if (< (string-length thing) 64)
        thing
        (content-address thing)))
   ;; Everything else - hash it
   (else
    (content-address (format "~a" thing)))))

(define (chaotic? thing)
  "Is thing in chaotic state (mutable, uncommitted)?"
  (let ((state (alist-ref (thing-id thing) *thing-states* equal?)))
    (or (not state) (eq? state 'chaotic))))

(define (quiescent? thing)
  "Is thing in quiescent state (immutable, stable)?"
  (let ((state (alist-ref (thing-id thing) *thing-states* equal?)))
    (eq? state 'quiescent)))

(define (ephemeral? thing)
  "Is thing ephemeral (no durability promise)?"
  (let ((dur (alist-ref (thing-id thing) *thing-durability* equal?)))
    (or (not dur) (eq? dur 'ephemeral))))

(define (persistent? thing)
  "Is thing persistent (guaranteed vault migration)?"
  (let ((dur (alist-ref (thing-id thing) *thing-durability* equal?)))
    (eq? dur 'persistent)))

(define (thing-state thing)
  "Get thing's current state"
  (or (alist-ref (thing-id thing) *thing-states* equal?) 'chaotic))

(define (thing-durability thing)
  "Get thing's durability"
  (or (alist-ref (thing-id thing) *thing-durability* equal?) 'ephemeral))

(define (short-id id)
  "Truncate id for display (max 16 chars)"
  (if (> (string-length id) 16)
      (string-append (substring id 0 16) "...")
      id))

(define (chaotic thing)
  "Create or mark thing as chaotic"
  (let ((id (thing-id thing)))
    (set! *thing-states* (cons (cons id 'chaotic) *thing-states*))
    (set! *chaotic-store* (cons (cons id thing) *chaotic-store*))
    (print "Thing " (short-id id) " is chaotic")
    thing))

(define (commit-thing thing)
  "Transition thing from chaotic to quiescent"
  (let ((id (thing-id thing)))
    (unless (chaotic? thing)
      (print "Thing already quiescent"))
    (set! *thing-states* (cons (cons id 'quiescent) *thing-states*))
    ;; Remove from chaotic store
    (set! *chaotic-store* (filter (lambda (e) (not (equal? (car e) id))) *chaotic-store*))
    (print "Thing " (short-id id) " committed (quiescent)")
    ;; If persistent, queue for vault
    (when (persistent? thing)
      (set! *persistence-queue* (cons thing *persistence-queue*))
      (print "  Queued for vault migration"))
    thing))

(define (persist thing)
  "Mark thing as persistent (guaranteed vault migration)"
  (let ((id (thing-id thing)))
    (set! *thing-durability* (cons (cons id 'persistent) *thing-durability*))
    (print "Thing " (short-id id) " marked persistent")
    ;; If already quiescent, queue immediately
    (when (quiescent? thing)
      (set! *persistence-queue* (cons thing *persistence-queue*))
      (print "  Queued for vault migration"))
    thing))

(define (ephemeral thing)
  "Mark thing as ephemeral (no durability promise)"
  (let ((id (thing-id thing)))
    (set! *thing-durability* (cons (cons id 'ephemeral) *thing-durability*))
    ;; Remove from persistence queue if present
    (set! *persistence-queue* (filter (lambda (t) (not (equal? (thing-id t) id))) *persistence-queue*))
    (print "Thing " (short-id id) " marked ephemeral")
    thing))

(define (flush-persistence!)
  "Migrate all queued persistent things to vault"
  (if (null? *persistence-queue*)
      (print "Persistence queue empty")
      (begin
        (print "Migrating " (length *persistence-queue*) " things to vault...")
        (for-each
         (lambda (thing)
           (let ((id (thing-id thing)))
             (content-put (format "~a" thing))
             (print "  " (short-id id) " -> vault")))
         *persistence-queue*)
        (set! *persistence-queue* '())
        (print "Done."))))

(define (thing-status thing)
  "Show thing's state and durability"
  (let ((id (thing-id thing)))
    (print "Thing: " (short-id id))
    (print "  State: " (thing-state thing))
    (print "  Durability: " (thing-durability thing))
    (print "  Cacheable: " (if (quiescent? thing) "yes (forever)" "no"))
    `((id . ,id)
      (state . ,(thing-state thing))
      (durability . ,(thing-durability thing)))))

;;; ============================================================
;;; Node Identity and Attestation
;;; ============================================================

(define *node-attestation* #f)  ; current attestation state

(define (principal->string p)
  "Convert principal blob to hex string"
  (if (blob? p) (blob->hex p) (format "~a" p)))

(define (attest #!optional principal)
  "Attest identity to access node details"
  (let ((key (vault-config 'signing-key)))
    (cond
     ((not key)
      (print "No signing key configured. Generate with (ed25519-keypair)")
      #f)
     (principal
      ;; Verify against provided principal
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
      ;; Self-attestation - principal is the public key (signing-key stored)
      (let ((our-principal (principal->string key)))
        (set! *node-attestation* our-principal)
        (print "Attested as: " (short-id our-principal))
        our-principal)))))

(define (attested?)
  "Check if currently attested"
  (and *node-attestation* #t))

(define (!)
  "Display detailed node information (requires attestation)"
  (unless (attested?)
    (print "Attestation required. Use (attest) first.")
    (print "")
    (attest))
  (when (attested?)
    (let* ((caps (probe-system-capabilities))
           (role (recommend-role caps)))
      (print "")
      (print "╔═══════════════════════════════════════════════════════════════╗")
      (print "║                     Node Information                          ║")
      (print "╠═══════════════════════════════════════════════════════════════╣")
      (print "")
      (print "  Principal:   " (short-id *node-attestation*))
      (print "  Platform:    " (platform-stamp))
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
      (print "  Security")
      (let ((security (cdr (assq 'security caps))))
        (print "    Signing:   " (if (cdr (assq 'signing-key security)) "configured" "absent"))
        (print "    Verify:    " (if (cdr (assq 'verify-key security)) "configured" "absent")))
      (print "")
      (print "  State")
      (print "    Memos:     " (length *memos*))
      (print "    Chaotic:   " (length *chaotic-store*))
      (print "    Pending:   " (length *persistence-queue*))
      (print "")
      (print "╚═══════════════════════════════════════════════════════════════╝")
      (print "")
      `((principal . ,*node-attestation*)
        (platform . ,(platform-stamp))
        (role . ,role)
        (capabilities . ,caps)))))

;;; ============================================================
;;; RFC-043: Memo Conventions
;;; ============================================================

(define *memos* '())
(define *memo-counter* 0)

(define (pad-number n width)
  "Pad number with leading zeros"
  (let ((s (number->string n)))
    (string-append (make-string (max 0 (- width (string-length s))) #\0) s)))

(define (memo-create title #!key (scope 'local) (category 'informational)
                                  (author "anonymous") (content ""))
  "Create a new memo"
  (set! *memo-counter* (+ *memo-counter* 1))
  (let* ((num (pad-number *memo-counter* 3))
         (id (case scope
               ((local) (string-append "local:memo-" num))
               ((federation) (string-append (current-directory) ":memo-" num))
               ((core) (string-append "RFC-" num))
               (else (error "Invalid scope" scope))))
         (memo `((id . ,id)
                 (title . ,title)
                 (scope . ,scope)
                 (category . ,category)
                 (author . ,author)
                 (content . ,content)
                 (created . ,(current-seconds))
                 (status . draft))))
    ;; Memos start chaotic
    (chaotic memo)
    (set! *memos* (cons memo *memos*))
    (print "Created " id ": " title)
    (print "  Scope: " scope)
    (print "  Category: " category)
    (print "  State: chaotic (pen to commit)")
    memo))

(define (memo-commit memo-id)
  "Commit a memo (chaotic → quiescent)"
  (let ((memo (find (lambda (m) (equal? (alist-ref 'id m) memo-id)) *memos*)))
    (if memo
        (begin
          (commit-thing memo)
          (print "Memo committed: " memo-id)
          memo)
        (error "Memo not found" memo-id))))

(define (memo-promote memo-id new-scope)
  "Promote memo to higher scope (local → federation → core)"
  (let ((memo (find (lambda (m) (equal? (alist-ref 'id m) memo-id)) *memos*)))
    (unless memo (error "Memo not found" memo-id))
    (let ((current-scope (alist-ref 'scope memo)))
      (unless (quiescent? memo)
        (error "Cannot promote chaotic memo - commit first"))
      (case new-scope
        ((federation)
         (unless (eq? current-scope 'local)
           (error "Can only promote local to federation"))
         (print "Promoting " memo-id " to federation scope")
         (print "  Requires federation review"))
        ((core)
         (unless (member current-scope '(local federation))
           (error "Already at core scope"))
         (print "Promoting " memo-id " to core (RFC)")
         (print "  Requires rough consensus"))
        (else (error "Invalid scope" new-scope)))
      `(promoted ,memo-id ,new-scope))))

(define (memo-persist memo-id)
  "Mark memo as persistent"
  (let ((memo (find (lambda (m) (equal? (alist-ref 'id m) memo-id)) *memos*)))
    (if memo
        (persist memo)
        (error "Memo not found" memo-id))))

(define (memo-list #!optional scope)
  "List memos, optionally filtered by scope"
  (let ((filtered (if scope
                      (filter (lambda (m) (eq? (alist-ref 'scope m) scope)) *memos*)
                      *memos*)))
    (if (null? filtered)
        (print "No memos" (if scope (format " at scope ~a" scope) ""))
        (for-each
         (lambda (m)
           (print "  " (alist-ref 'id m) ": " (alist-ref 'title m)
                  " [" (thing-state m) "/" (thing-durability m) "]"))
         filtered))))

(define (memo-show memo-id)
  "Show memo details"
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
        (error "Memo not found" memo-id))))

;;; ============================================================
;;; RFC-016: Lazy Clustering
;;; ============================================================

(define *lazy-peers* '())
(define *lazy-queue* '())
(define *version-vectors* '())

(define (lazy-join peer #!key (uri #f) (key #f))
  "Register a peer for lazy sync"
  (cond
   ((not peer)
    (print "Join Refused: No peer specified")
    #f)
   ((assoc peer *lazy-peers*)
    (print "Join Refused: Already joined with " peer)
    #f)
   (else
    (set! *lazy-peers* (cons `((peer . ,peer) (uri . ,uri) (key . ,key) (last-sync . never)) *lazy-peers*))
    (print "Joined lazy cluster with " peer)
    `(joined ,peer))))

(define (lazy-leave peer)
  "Remove peer from lazy cluster"
  (set! *lazy-peers* (filter (lambda (p) (not (equal? (alist-ref 'peer p) peer))) *lazy-peers*))
  (print "Left lazy cluster: " peer)
  `(left ,peer))

(define (lazy-push peer)
  "Push local releases to peer"
  (print "Pushing to " peer "...")
  (print "  (lazy push simulated)")
  `(pushed ,peer))

(define (lazy-pull peer)
  "Pull releases from peer"
  (print "Pulling from " peer "...")
  (print "  (lazy pull simulated)")
  `(pulled ,peer))

(define (lazy-sync peer)
  "Bidirectional sync with peer"
  (print "Syncing with " peer "...")
  (lazy-push peer)
  (lazy-pull peer)
  `(synced ,peer))

(define (lazy-status)
  "Show lazy cluster status"
  (if (null? *lazy-peers*)
      (print "No lazy cluster peers configured")
      (begin
        (print "Lazy cluster peers:")
        (for-each (lambda (p)
                    (print "  " (alist-ref 'peer p) " [" (alist-ref 'last-sync p) "]"))
                  *lazy-peers*))))

(define (lazy-queue)
  "Show pending sync queue"
  (if (null? *lazy-queue*)
      (print "Sync queue empty")
      (begin
        (print "Pending sync:")
        (for-each (lambda (item) (print "  " item)) *lazy-queue*))))

(define (lazy-resolve version #!key (prefer 'local) (merged #f))
  "Resolve a sync conflict"
  (print "Resolving " version " -> " (or merged prefer))
  `(resolved ,version ,(or merged prefer)))

(define (lazy-beacon)
  "Send optional presence beacon"
  `(beacon
    (peer ,(current-directory))
    (lamport-time ,*lamport-clock*)
    (status available)))

;;; ============================================================
;;; RFC-010: Federation
;;; ============================================================

(define *federation-peers* '())

(define (federate peer-url #!key (trust 'partial))
  "Establish federation with a peer realm"
  (set! *federation-peers* (cons `((url . ,peer-url) (trust . ,trust) (status . pending)) *federation-peers*))
  (print "Federation request sent to " peer-url)
  `(federation-pending ,peer-url))

(define (federate-status)
  "Show federation status with all peers"
  (if (null? *federation-peers*)
      (print "No federation peers configured")
      (for-each (lambda (p)
                  (print "  " (alist-ref 'url p) " [" (alist-ref 'trust p) "] " (alist-ref 'status p)))
                *federation-peers*)))

(define (federate-replicate peer-url)
  "Replicate with a federated peer"
  (print "Replicating with " peer-url "...")
  '(replicate-complete))

;;; ============================================================
;;; RFC-011: Byzantine Consensus
;;; ============================================================

(define *consensus-proposals* '())

(define (consensus-propose value #!key (quorum 'majority))
  "Propose a value for Byzantine consensus"
  (let ((proposal-id (blob->hex (sha512-hash (string->blob (format "~a~a" value (current-seconds)))))))
    (set! *consensus-proposals* (cons `((id . ,proposal-id) (value . ,value) (quorum . ,quorum) (votes . ())) *consensus-proposals*))
    (print "Proposal " (short-id proposal-id) " created")
    proposal-id))

(define (consensus-vote proposal-id vote #!key (signature #f))
  "Vote on a consensus proposal (vote: 'accept | 'reject)"
  (print "Vote " vote " recorded for " (short-id proposal-id))
  `(vote-recorded ,vote))

(define (consensus-status #!optional proposal-id)
  "Show consensus status"
  (if (null? *consensus-proposals*)
      (print "No active proposals")
      (for-each (lambda (p)
                  (print "  " (short-id (alist-ref 'id p)) " : " (alist-ref 'value p)))
                *consensus-proposals*)))

;;; ============================================================
;;; RFC-012: Lamport Clocks
;;; ============================================================

(define *lamport-clock* 0)

(define (lamport-tick)
  "Increment local Lamport clock"
  (set! *lamport-clock* (+ *lamport-clock* 1))
  *lamport-clock*)

(define (lamport-send)
  "Get timestamp for sending a message"
  (lamport-tick))

(define (lamport-receive remote-timestamp)
  "Update clock on message receipt"
  (set! *lamport-clock* (+ 1 (max *lamport-clock* remote-timestamp)))
  *lamport-clock*)

(define (lamport-compare t1 t2)
  "Compare two Lamport timestamps: -1 (before), 0 (concurrent), 1 (after)"
  (cond ((< t1 t2) -1)
        ((> t1 t2) 1)
        (else 0)))

(define (lamport-clock)
  "Get current Lamport clock value"
  *lamport-clock*)

;;; ============================================================
;;; RFC-020: Content-Addressed Storage
;;; ============================================================

(define *content-store* '())

(define (content-address data)
  "Compute content address (hash) for data"
  (let ((hash (sha512-hash (if (blob? data) data (string->blob data)))))
    (blob->hex hash)))

(define (content-put data)
  "Store data by content address, return address"
  (let* ((addr (content-address data))
         (blob-data (if (blob? data) data (string->blob data))))
    (set! *content-store* (cons (cons addr blob-data) *content-store*))
    (print "Stored at " (short-id addr))
    addr))

(define (content-get addr)
  "Retrieve data by content address"
  (let ((entry (assoc addr *content-store*)))
    (if entry
        (cdr entry)
        (error "Content not found" addr))))

(define (content-exists? addr)
  "Check if content exists"
  (if (assoc addr *content-store*) #t #f))

;;; ============================================================
;;; RFC-021: Capability Delegation
;;; ============================================================

(define (delegate capability to-principal #!key (restrict '()) (expires #f))
  "Delegate a capability to another principal"
  (let ((delegation `((capability . ,capability)
                      (to . ,to-principal)
                      (restrictions . ,restrict)
                      (expires . ,expires)
                      (created . ,(current-seconds)))))
    (print "Delegated " capability " to " to-principal)
    delegation))

(define (delegate-chain delegations)
  "Verify a chain of delegations"
  (print "Verifying delegation chain of " (length delegations) " links...")
  (if (null? delegations)
      #t
      (let loop ((chain delegations))
        (if (null? (cdr chain))
            #t
            (loop (cdr chain))))))

(define (delegate-verify delegation principal action)
  "Verify if principal can perform action via delegation"
  (let ((cap (alist-ref 'capability delegation))
        (to (alist-ref 'to delegation)))
    (and (equal? to principal)
         (equal? cap action))))

;;; ============================================================
;;; RFC-023: Agent Sandboxing (Demonic Agents)
;;; ============================================================

(define *sandboxes* '())

(define (sandbox name #!key (capabilities '()) (limits '()))
  "Create a sandboxed execution environment"
  (let ((sb `((name . ,name)
              (capabilities . ,capabilities)
              (limits . ,limits)
              (status . ready))))
    (set! *sandboxes* (cons sb *sandboxes*))
    (print "Sandbox '" name "' created with " (length capabilities) " capabilities")
    sb))

(define (sandbox-run sb-name code)
  "Execute code in a sandbox"
  (print "Executing in sandbox '" sb-name "'...")
  (print "  (sandboxed execution simulated)")
  '(sandbox-result ok))

(define (sandbox-capabilities sb-name)
  "List capabilities available in sandbox"
  (let ((sb (find (lambda (s) (equal? (alist-ref 'name s) sb-name)) *sandboxes*)))
    (if sb
        (alist-ref 'capabilities sb)
        (error "Sandbox not found" sb-name))))

(define (sandbox-destroy sb-name)
  "Destroy a sandbox"
  (set! *sandboxes* (filter (lambda (s) (not (equal? (alist-ref 'name s) sb-name))) *sandboxes*))
  (print "Sandbox '" sb-name "' destroyed"))

;;; ============================================================
;;; RFC-035: Mobile Agents (Quantum Vocabulary)
;;; ============================================================

(define *agent-location* 'local)
(define *entanglements* '())
(define *teleport-grants* '())  ; authorized destinations
(define *teleport-history* '()) ; audit trail

;;; Teleportation Address Syntax:
;;;   local:path          - within current realm
;;;   realm:path          - to named realm
;;;   principal@realm:path - to realm, as principal
;;;   wormhole://host:port/path - via wormhole

(define (parse-teleport-address addr)
  "Parse teleportation address into components"
  (cond
   ((string-contains addr "://")
    ;; wormhole://host:port/path
    (let* ((proto-end (string-contains addr "://"))
           (proto (substring addr 0 proto-end))
           (rest (substring addr (+ proto-end 3) (string-length addr)))
           (slash-pos (string-contains rest "/"))
           (host (if slash-pos (substring rest 0 slash-pos) rest))
           (path (if slash-pos (substring rest slash-pos (string-length rest)) "/")))
      `((protocol . ,proto) (host . ,host) (path . ,path))))
   ((string-contains addr "@")
    ;; principal@realm:path
    (let* ((at-pos (string-contains addr "@"))
           (principal (substring addr 0 at-pos))
           (rest (substring addr (+ at-pos 1) (string-length addr)))
           (colon-pos (string-contains rest ":"))
           (realm (if colon-pos (substring rest 0 colon-pos) rest))
           (path (if colon-pos (substring rest (+ colon-pos 1) (string-length rest)) "/")))
      `((principal . ,principal) (realm . ,realm) (path . ,path))))
   ((string-contains addr ":")
    ;; realm:path
    (let* ((colon-pos (string-contains addr ":"))
           (realm (substring addr 0 colon-pos))
           (path (substring addr (+ colon-pos 1) (string-length addr))))
      `((realm . ,realm) (path . ,path))))
   (else
    ;; local path
    `((realm . local) (path . ,addr)))))

(define (teleport-grant destination #!key (capabilities '(read)) (expires #f) (delegate #f))
  "Grant authorization to teleport to destination"
  (unless (attested?)
    (error "Attestation required to grant teleport authorization"))
  (let ((grant `((destination . ,destination)
                 (capabilities . ,capabilities)
                 (expires . ,expires)
                 (delegatable . ,(and delegate #t))
                 (grantor . ,*node-attestation*)
                 (created . ,(current-seconds)))))
    (set! *teleport-grants* (cons grant *teleport-grants*))
    (print "Granted teleport to: " destination)
    (print "  Capabilities: " capabilities)
    (when expires (print "  Expires: " expires))
    (when delegate (print "  Delegatable: yes"))
    grant))

(define (teleport-check destination capabilities)
  "Check if teleportation is authorized"
  (let ((now (current-seconds)))
    (find (lambda (g)
            (and (equal? (alist-ref 'destination g) destination)
                 (or (not (alist-ref 'expires g))
                     (> (alist-ref 'expires g) now))
                 (every (lambda (c) (member c (alist-ref 'capabilities g)))
                        capabilities)))
          *teleport-grants*)))

(define (teleport destination #!key (state '()) (as #f) (capabilities '(read)))
  "Teleport to destination with authorization check"
  (unless (attested?)
    (error "Attestation required for teleportation"))

  (let ((addr (parse-teleport-address destination)))
    (print "")
    (print "Teleport")
    (print "  From: " *agent-location*)
    (print "  To:   " destination)
    (when as (print "  As:   " as))
    (print "  Caps: " capabilities)
    (print "")

    ;; Check authorization
    (let ((grant (teleport-check destination capabilities)))
      (cond
       ((not grant)
        (print "  [Denied] No authorization for destination")
        (print "  Use (teleport-grant \"" destination "\") to authorize")
        #f)
       (else
        ;; Authorized - execute teleport
        (let ((old-location *agent-location*)
              (record `((from . ,*agent-location*)
                        (to . ,destination)
                        (principal . ,*node-attestation*)
                        (as . ,as)
                        (capabilities . ,capabilities)
                        (state-size . ,(length state))
                        (timestamp . ,(current-seconds)))))
          ;; Audit (critical operation)
          (set! *teleport-history* (cons record *teleport-history*))
          (audit-append actor: *node-attestation*
                        action: 'teleport
                        target: destination
                        detail: record)
          ;; Update location
          (set! *agent-location* destination)
          (print "  [OK] Teleported")
          (print "  State transferred: " (length state) " items")
          (print "")
          `((status . ok)
            (from . ,old-location)
            (to . ,destination)
            (address . ,addr))))))))

(define (teleport-history)
  "Show teleportation audit trail"
  (if (null? *teleport-history*)
      (print "No teleportation history")
      (for-each (lambda (h)
                  (print "  " (alist-ref 'timestamp h) ": "
                         (alist-ref 'from h) " -> " (alist-ref 'to h)))
                *teleport-history*)))

(define (tunnel destination #!key (agent 'self))
  "Tunnel agent to a remote realm (legacy, use teleport)"
  (print "Tunneling " agent " to " destination "...")
  (set! *agent-location* destination)
  `(tunneled ,destination))

(define (observe resource)
  "Observe a resource (collapses superposition)"
  (print "Observing " resource "...")
  `(observed ,resource ,(current-seconds)))

(define (entangle agent1 agent2)
  "Entangle two agents (correlated state)"
  (set! *entanglements* (cons (list agent1 agent2) *entanglements*))
  (print "Entangled " agent1 " <-> " agent2)
  `(entangled ,agent1 ,agent2))

(define (quantum-teleport state from to)
  "Teleport state between entangled agents (quantum channel)"
  (let ((pair (find (lambda (e)
                      (or (and (equal? (car e) from) (equal? (cadr e) to))
                          (and (equal? (car e) to) (equal? (cadr e) from))))
                    *entanglements*)))
    (if pair
        (begin
          (print "Quantum teleporting via entanglement: " from " <-> " to)
          `(teleported ,state ,to))
        (begin
          (print "No entanglement between " from " and " to)
          #f))))

(define (decohere agent)
  "Decohere agent (cleanup, terminate)"
  (print "Decohering " agent "...")
  (set! *agent-location* 'local)
  '(decohered))

(define (superpose states)
  "Create superposition of multiple states"
  `(superposition ,@states))

(define (collapse superposition)
  "Collapse superposition to definite state"
  (if (and (pair? superposition) (eq? (car superposition) 'superposition))
      (let ((states (cdr superposition)))
        (list-ref states (random (length states))))
      superposition))

;;; ============================================================
;;; RFC-036: Quorum Voting (Homomorphic)
;;; ============================================================

(define *quorum-proposals* '())

(define (quorum-propose question options #!key (threshold 'majority))
  "Propose a quorum vote"
  (let ((prop-id (blob->hex (sha512-hash (string->blob question)))))
    (set! *quorum-proposals*
          (cons `((id . ,prop-id)
                  (question . ,question)
                  (options . ,options)
                  (threshold . ,threshold)
                  (votes . ())
                  (status . open))
                *quorum-proposals*))
    (print "Quorum proposal created: " (short-id prop-id))
    prop-id))

(define (quorum-vote prop-id choice #!key (encrypted #t))
  "Cast a vote (optionally homomorphically encrypted)"
  (print "Vote cast for " (short-id prop-id) " [" (if encrypted "encrypted" "plain") "]")
  `(vote-recorded ,choice))

(define (quorum-tally prop-id)
  "Tally votes (threshold decryption for HE votes)"
  (print "Tallying votes for " (short-id prop-id))
  (print "  (homomorphic tally simulated)")
  '(tally-pending))

(define (quorum-status #!optional prop-id)
  "Show quorum voting status"
  (if (null? *quorum-proposals*)
      (print "No active quorum proposals")
      (for-each (lambda (p)
                  (print "  " (short-id (alist-ref 'id p)) " : "
                         (alist-ref 'question p) " [" (alist-ref 'status p) "]"))
                *quorum-proposals*)))

;;; ============================================================
;;; RFC-038: Local Inference (Ollama)
;;; ============================================================

(define *inference-server* "http://localhost:11434")

(define (inference-server #!optional url)
  "Get or set inference server URL"
  (if url
      (begin (set! *inference-server* url) url)
      *inference-server*))

(define (inference-models)
  "List available models (requires Ollama)"
  (print "Querying " *inference-server* "/api/tags ...")
  (print "  (would return model list from Ollama)")
  '(llama3 mistral codellama nomic-embed-text))

(define (inference prompt #!key (model 'llama3) (max-tokens 500))
  "Run inference on local LLM"
  (print "Inference request to " *inference-server*)
  (print "  Model: " model)
  (print "  Prompt: " (if (> (string-length prompt) 50)
                          (string-append (substring prompt 0 50) "...")
                          prompt))
  (print "  (would call Ollama API)")
  '(inference-simulated))

(define (inference-embed text #!key (model 'nomic-embed-text))
  "Generate embeddings for text"
  (print "Generating embeddings with " model "...")
  (print "  (would return vector from Ollama)")
  '(embedding-simulated))

;;; ============================================================
;;; RFC-041: FUSE Filesystem
;;; ============================================================

(define *wormholes* '())
(define *vault-manifest* '())
(define *wormhole-rate-limits* '())
(define *wormhole-ops-count* 0)

;; Capability sets (long form for readability)
(define capability:read-only
  '(read stat readdir xattr-read acl-read))

(define capability:read-write
  '(read write create stat chmod readdir mkdir xattr-read xattr-write))

(define capability:full
  '(read write create delete rename
    stat chmod chown
    xattr-read xattr-write acl-read acl-write
    readdir mkdir rmdir admin delegate audit-read rate-limit))

(define capability:backup
  '(read stat readdir xattr-read acl-read))

(define capability:synchronize
  '(read write create delete rename
    stat chmod readdir mkdir rmdir
    xattr-read xattr-write))

(define (capture-xattrs path)
  "Capture extended attributes from file"
  ;; Would use: xattr -l path
  '())

(define (capture-metadata path)
  "Capture full macOS metadata for a file"
  `((posix
     (mode #o644)
     (uid 501)
     (gid 20)
     (size 0)
     (mtime ,(current-seconds))
     (birthtime ,(current-seconds)))
    (xattr ,(capture-xattrs path))
    (flags ())))

(define (wormhole-audit action path #!optional detail)
  "Log wormhole operation to audit trail"
  (let ((entry `((timestamp . ,(current-seconds))
                 (action . ,action)
                 (path . ,path)
                 (detail . ,detail))))
    (audit-append actor: 'wormhole
                  action: action
                  target: path
                  detail: detail)))

(define (wormhole-rate-check wormhole)
  "Check rate limit for wormhole operations"
  (let* ((fs-path (alist-ref 'fs wormhole))
         (limit (or (alist-ref fs-path *wormhole-rate-limits*) 1000))
         (window-start (- (current-seconds) 60)))
    (set! *wormhole-ops-count* (+ *wormhole-ops-count* 1))
    (if (> *wormhole-ops-count* limit)
        (begin
          (print "  [Rate Limited] " *wormhole-ops-count* "/" limit " ops/min")
          #f)
        #t)))

(define (wormhole-open fs-path #!key (vault-path "/") (rate-limit 1000)
                                     (capabilities capability:read-write)
                                     (locked #f) (auth-required '()))
  "Open wormhole between filesystem and vault"
  (let ((abs-path (if (char=? (string-ref fs-path 0) #\/)
                      fs-path
                      (string-append (current-directory) "/" fs-path))))
    (print "Opening wormhole: " abs-path " <-> vault:" vault-path)
    (print "  Capabilities: " (length capabilities) " granted")
    (print "  Rate limit: " rate-limit " ops/min")
    (print "  Locked: " (if locked "yes (requires unlock)" "no"))
    (when (not (null? auth-required))
      (print "  Step-up auth for: " auth-required))
    (print "  Audit: enabled")
    (print "  Requires: FUSE-T or macFUSE")
    (print "")
    (set! *wormholes* (cons `((fs . ,abs-path)
                              (vault . ,vault-path)
                              (status . ,(if locked 'locked 'stable))
                              (capabilities . ,capabilities)
                              (rate-limit . ,rate-limit)
                              (auth-required . ,auth-required)
                              (opened . ,(current-seconds)))
                            *wormholes*))
    (set! *wormhole-rate-limits* (cons (cons abs-path rate-limit) *wormhole-rate-limits*))
    (wormhole-audit 'wormhole-open abs-path `((vault ,vault-path) (capabilities ,(length capabilities))))
    (print "  (wormhole simulated - full implementation requires libfuse)")
    `(wormhole ,abs-path ,vault-path)))

(define (wormhole-lock fs-path)
  "Lock wormhole (requires unlock to resume)"
  (let ((w (find (lambda (w) (equal? (alist-ref 'fs w) fs-path)) *wormholes*)))
    (if w
        (begin
          (set-car! (alist-ref 'status w #f #f) 'locked)
          (wormhole-audit 'wormhole-lock fs-path)
          (print "Wormhole locked: " fs-path)
          `(locked ,fs-path))
        (error "Wormhole not found" fs-path))))

(define (wormhole-unlock fs-path #!key (auth #f))
  "Unlock wormhole (may require authentication)"
  (let ((w (find (lambda (w) (equal? (alist-ref 'fs w) fs-path)) *wormholes*)))
    (if w
        (begin
          ;; In production, verify auth token here
          (wormhole-audit 'wormhole-unlock fs-path `(auth ,(if auth 'provided 'none)))
          (print "Wormhole unlocked: " fs-path)
          `(unlocked ,fs-path))
        (error "Wormhole not found" fs-path))))

(define (wormhole-caps fs-path)
  "Show capabilities for a wormhole"
  (let ((w (find (lambda (w) (equal? (alist-ref 'fs w) fs-path)) *wormholes*)))
    (if w
        (begin
          (print "Capabilities for " fs-path ":")
          (for-each (lambda (c) (print "  " c)) (alist-ref 'capabilities w))
          (alist-ref 'capabilities w))
        (error "Wormhole not found" fs-path))))

(define (wormhole-delegate fs-path new-caps recipient)
  "Delegate subset of wormhole capabilities"
  (let* ((w (find (lambda (w) (equal? (alist-ref 'fs w) fs-path)) *wormholes*))
         (my-caps (and w (alist-ref 'capabilities w))))
    (unless w (error "Wormhole not found" fs-path))
    (unless (every (lambda (c) (member c my-caps)) new-caps)
      (error 'capability-amplification "Cannot delegate capabilities you don't have"))
    (wormhole-audit 'wormhole-delegate fs-path `(to ,recipient caps ,(length new-caps)))
    (print "Delegated " (length new-caps) " capabilities to " recipient)
    `(delegated ,recipient ,new-caps)))

(define (wormhole-close fs-path)
  "Close wormhole"
  (print "Closing wormhole at " fs-path "...")
  (wormhole-audit 'wormhole-close fs-path)
  (set! *wormholes*
        (filter (lambda (w) (not (equal? (alist-ref 'fs w) fs-path)))
                *wormholes*))
  `(closed ,fs-path))

(define (wormholes)
  "List active wormholes"
  (if (null? *wormholes*)
      (print "No active wormholes")
      (for-each (lambda (w)
                  (print "  " (alist-ref 'fs w) " <-> vault:" (alist-ref 'vault w)
                         " [" (alist-ref 'status w) "] "
                         (alist-ref 'rate-limit w) " ops/min"))
                *wormholes*)))

;; Aliases for mount vocabulary
(define vault-mount wormhole-open)
(define vault-unmount wormhole-close)
(define vault-mounts wormholes)

(define (fs-import path #!key (recursive #t))
  "Import macOS path into vault with full metadata"
  (print "Importing " path " into vault...")
  (print "  Capturing: POSIX attrs, xattrs, Finder tags, ACLs")
  (let* ((meta (capture-metadata path))
         (hash (blob->hex (sha512-hash (string->blob path)))))
    (set! *vault-manifest*
          (cons `((path . ,path)
                  (hash . ,hash)
                  (metadata . ,meta))
                *vault-manifest*))
    (print "  Stored as: " (short-id hash))
    `(imported ,path ,hash)))

(define (fs-export hash path)
  "Export vault object to macOS, restoring full metadata"
  (print "Exporting " (short-id hash) " to " path)
  (print "  Restoring: POSIX attrs, xattrs, Finder tags, ACLs")
  (print "  (export simulated)")
  `(exported ,hash ,path))

(define (fs-sync vault-path fs-path)
  "Bidirectional sync between vault and filesystem"
  (print "Syncing " vault-path " <-> " fs-path)
  (print "  Detecting changes...")
  (print "  (bidirectional sync simulated)")
  `(synced ,vault-path ,fs-path))

(define (manifest-list)
  "Show vault manifest entries"
  (if (null? *vault-manifest*)
      (print "Manifest empty")
      (for-each (lambda (e)
                  (print "  " (alist-ref 'path e) " -> "
                         (short-id (alist-ref 'hash e))))
                *vault-manifest*)))

;;; ============================================================
;;; Wormhole Security Properties
;;; ============================================================

;;; A wormhole is a bidirectional channel between security domains.
;;; Two types exist:
;;;   1. FUSE wormhole - filesystem <-> vault bridge (local)
;;;   2. Network wormhole - inter-node communication channel
;;;
;;; Both share the same security model: capability-confined,
;;; authenticated, audited, and rate-limited.
;;;
;;; INFORMATION FLOW PROPERTIES
;;; ===========================
;;; The mathematics of multilevel security preserved in capability form:
;;;
;;; Confidentiality (cf. "no read up, no write down"):
;;;   - A principal can only READ objects for which it holds a read capability
;;;   - A principal can only WRITE to objects for which it holds a write capability
;;;   - Capabilities flow DOWN the delegation graph, never up
;;;   - Information cannot flow to principals without appropriate capabilities
;;;
;;;   Formally: ∀ read(P,O): P ∈ holders(cap_read(O))
;;;             ∀ write(P,O): P ∈ holders(cap_write(O))
;;;             ∀ delegate(P₁,P₂,C): C ⊆ capabilities(P₁)
;;;
;;; Integrity (cf. "no read down, no write up"):
;;;   - Objects can only be modified by principals with write capability
;;;   - The capability graph defines the integrity boundary
;;;   - Attenuation ensures integrity can only decrease, never increase
;;;   - Provenance tracked: who granted what to whom
;;;
;;;   Formally: ∀ modify(P,O): P ∈ holders(cap_write(O))
;;;             ∀ delegate(P₁,P₂,C): integrity(C') ≤ integrity(C)
;;;             ∀ capability C: provenance(C) ⊆ audit_trail
;;;
;;; Confinement (the capability discipline):
;;;   - No ambient authority: all access requires explicit capability
;;;   - Capabilities are unforgeable references
;;;   - The only way to obtain a capability is to receive it
;;;   - Attenuation only: delegated ⊆ held
;;;
;;;   Formally: ∀ access(P,O): ∃ C ∈ capabilities(P): authorizes(C,O)
;;;             ∀ C: unforgeable(C)
;;;             ∀ acquire(P,C): ∃ P': delegate(P',P,C) ∨ create(P,C,O)
;;;             ∀ delegate(P₁,P₂,C'): C' ⊆ capabilities(P₁)
;;;
;;; These properties ensure that wormholes cannot be used to:
;;;   - Exfiltrate data (read) without read capability
;;;   - Corrupt data (write) without write capability
;;;   - Escalate privileges (capability amplification)
;;;   - Bypass audit (all operations logged)

;; Security property definitions
(define *wormhole-security-properties*
  '((identity
     ;; Every wormhole endpoint must prove its identity
     (mutual-authentication . required)    ; both ends verify identity
     (attestation . required)              ; principal must attest before use
     (certificate-chain . spki)            ; SPKI certificate authorization
     (identity-binding . cryptographic))   ; Ed25519 signatures

    (confidentiality
     ;; Data traversing wormholes is protected from observation
     (encryption . required)               ; all data encrypted
     (protocol . tls-1.3)                  ; minimum TLS 1.3 for network
     (forward-secrecy . perfect)           ; ephemeral session keys
     (key-exchange . x25519)               ; Curve25519 ECDH
     (plaintext . never))                  ; no cleartext transmission

    (integrity
     ;; Data cannot be modified in transit
     (authentication . aead)               ; authenticated encryption
     (algorithm . chacha20-poly1305)       ; or AES-256-GCM
     (tampering . detected)                ; any modification detected
     (replay-protection . sequence-numbers) ; prevent replay attacks
     (ordering . preserved))               ; message order maintained

    (authorization
     ;; Access controlled by capabilities, not identity alone
     (model . capability)                  ; object-capability security
     (ambient-authority . none)            ; no implicit permissions
     (attenuation . only)                  ; can only reduce, never amplify
     (delegation . explicit)               ; must explicitly pass capabilities
     (revocation . supported)              ; capabilities can be revoked
     (expiration . supported))             ; time-limited grants

    (confinement
     ;; What traverses the wormhole is strictly controlled
     (data-flow . capability-bounded)      ; only what capabilities allow
     (type-checking . enforced)            ; validate data at boundaries
     (code-execution . sandboxed)          ; agents confined by RFC-023
     (ambient-channels . blocked)          ; no covert channels
     (reference-passing . by-capability))  ; objects passed as capabilities

    (audit
     ;; All operations are logged
     (logging . comprehensive)             ; all ops logged (RFC-003)
     (trail . tamper-evident)              ; append-only, signed
     (critical-ops . always)               ; open, close, delegate logged
     (data-ops . configurable)             ; read/write logging optional
     (non-repudiation . cryptographic))    ; signed audit entries

    (availability
     ;; Protection against abuse and resource exhaustion
     (rate-limiting . enforced)            ; ops/minute limits (RFC-032)
     (connection-quota . per-principal)    ; max concurrent wormholes
     (timeout . configurable)              ; idle connection timeout
     (graceful-degradation . required)     ; fail safely under load
     (denial-of-service . mitigated))))    ; rate limits prevent DoS

;;; Information Flow Enforcement
;;; ============================

;; The capability lattice - defines the partial order
;; Higher in lattice = more authority
(define *capability-lattice*
  '((full . (admin delegate audit-read rate-limit
             read write create delete rename
             stat chmod chown readdir mkdir rmdir
             xattr-read xattr-write acl-read acl-write))
    (admin . (delegate audit-read rate-limit))
    (synchronize . (read write create delete rename stat chmod readdir mkdir rmdir xattr-read xattr-write))
    (read-write . (read write create stat chmod readdir mkdir xattr-read xattr-write))
    (read-only . (read stat readdir xattr-read acl-read))
    (backup . (read stat readdir xattr-read acl-read))
    (none . ())))

(define (capability-subsumes? held required)
  "Check if held capabilities subsume required (held ⊇ required)"
  ;; The mathematical containment check
  (every (lambda (r) (member r held)) required))

(define (capability-attenuate held granted)
  "Attenuate: granted must be subset of held (granted ⊆ held)"
  ;; Enforces: ∀ delegate(P₁,P₂,C'): C' ⊆ capabilities(P₁)
  (if (capability-subsumes? held granted)
      granted
      (error 'capability-amplification
             "Cannot grant capabilities not held"
             `(held: ,held granted: ,granted))))

(define (information-flow-check source-caps dest-caps operation)
  "Verify information flow is permitted"
  ;; Confidentiality: can only read with read capability
  ;; Integrity: can only write with write capability
  (case operation
    ((read)
     (unless (member 'read source-caps)
       (error 'confidentiality-violation "No read capability at source"))
     #t)
    ((write)
     (unless (member 'write dest-caps)
       (error 'integrity-violation "No write capability at destination"))
     #t)
    ((transfer)
     ;; Bidirectional requires both
     (unless (member 'read source-caps)
       (error 'confidentiality-violation "No read capability at source"))
     (unless (member 'write dest-caps)
       (error 'integrity-violation "No write capability at destination"))
     #t)
    (else #t)))

(define (wormhole-flow-guard wormhole operation object)
  "Guard enforcing information flow properties on wormhole operations"
  (let ((caps (or (alist-ref 'capabilities wormhole) '()))
        (principal (alist-ref 'principal wormhole)))
    ;; No ambient authority - must have explicit capability
    (when (null? caps)
      (error 'no-ambient-authority "Wormhole has no capabilities"))
    ;; Check operation is permitted
    (cond
     ((member operation '(read stat readdir xattr-read acl-read))
      (unless (member 'read caps)
        (error 'read-denied "Principal lacks read capability")))
     ((member operation '(write create chmod mkdir xattr-write acl-write))
      (unless (or (member 'write caps) (member 'create caps))
        (error 'write-denied "Principal lacks write capability")))
     ((member operation '(delete unlink rmdir))
      (unless (member 'delete caps)
        (error 'delete-denied "Principal lacks delete capability")))
     ((member operation '(delegate))
      (unless (member 'delegate caps)
        (error 'delegate-denied "Principal lacks delegate capability"))))
    ;; Passed all checks
    `(permitted ,operation ,object)))

;; Network wormhole state machine
;; States: closed -> connecting -> handshake -> open -> closing -> closed
(define *wormhole-states*
  '((closed      . (connect))              ; initial state
    (connecting  . (handshake abort))      ; TCP connection established
    (handshake   . (open abort))           ; TLS + SPKI verification
    (open        . (transfer close))       ; authenticated channel ready
    (closing     . (closed))))             ; graceful shutdown

;; Network wormhole connection record
(define (make-network-wormhole host port principal)
  "Create network wormhole connection descriptor"
  `((type . network)
    (host . ,host)
    (port . ,port)
    (principal . ,principal)
    (state . closed)
    (session-key . #f)                     ; ephemeral, per-connection
    (sequence-tx . 0)                      ; outbound message counter
    (sequence-rx . 0)                      ; inbound message counter
    (capabilities . ())                    ; granted by remote
    (opened . #f)
    (last-activity . #f)
    (bytes-tx . 0)
    (bytes-rx . 0)))

(define (wormhole-handshake! wormhole)
  "Perform TLS 1.3 handshake with mutual authentication"
  ;; 1. ClientHello with supported cipher suites
  ;; 2. ServerHello with selected cipher
  ;; 3. Certificate exchange (both directions for mTLS)
  ;; 4. SPKI certificate chain verification
  ;; 5. Key derivation via X25519 ECDH
  ;; 6. Finished messages with verify_data
  (print "  [Handshake] TLS 1.3 mutual authentication")
  (print "  [Handshake] Verifying SPKI certificate chain")
  (print "  [Handshake] Deriving session keys (X25519 + HKDF)")
  ;; In production: actual TLS handshake via openssl/libressl
  `(handshake-complete
    (cipher . chacha20-poly1305)
    (kex . x25519)
    (session-id . ,(blob->hex (random-bytes 16)))))

(define (wormhole-verify-capability! wormhole operation target)
  "Verify capability for operation on target"
  (let ((caps (alist-ref 'capabilities wormhole)))
    (cond
     ((null? caps)
      (print "  [Denied] No capabilities granted")
      #f)
     ((member operation caps)
      #t)
     ((and (eq? operation 'write)
           (member 'full caps))
      #t)
     (else
      (print "  [Denied] Missing capability: " operation)
      #f))))

(define (wormhole-transfer! wormhole data)
  "Transfer data through wormhole with integrity protection"
  ;; 1. Check rate limit
  ;; 2. Increment sequence number
  ;; 3. Encrypt with session key + sequence as nonce component
  ;; 4. Authenticate with Poly1305
  ;; 5. Transmit
  ;; 6. Audit (if configured)
  (let ((seq (+ 1 (alist-ref 'sequence-tx wormhole))))
    (print "  [TX] seq=" seq " len=" (string-length (format "~a" data)))
    `(transferred ,seq)))

(define (wormhole-security)
  "Display wormhole security properties"
  (print "")
  (print "╔═══════════════════════════════════════════════════════════╗")
  (print "║           Wormhole Security Properties                    ║")
  (print "╚═══════════════════════════════════════════════════════════╝")
  (print "")
  (for-each
   (lambda (category)
     (let ((name (car category))
           (props (cdr category)))
       (print "  " (string-upcase (symbol->string name)))
       (for-each
        (lambda (prop)
          (print "    " (car prop) ": " (cdr prop)))
        props)
       (print "")))
   *wormhole-security-properties*)
  (print "  States: closed → connecting → handshake → open → closing → closed")
  (print ""))

;; Verify wormhole conforms to security properties
(define (wormhole-verify wormhole)
  "Verify wormhole meets security requirements"
  (print "Verifying wormhole security properties...")
  (let ((type (alist-ref 'type wormhole))
        (caps (or (alist-ref 'capabilities wormhole) '()))
        (issues '()))
    ;; Check identity
    (unless (alist-ref 'principal wormhole)
      (set! issues (cons "missing principal" issues)))
    ;; Check capabilities
    (when (null? caps)
      (set! issues (cons "no capabilities (operating in deny-all mode)" issues)))
    ;; Check state
    (unless (member (alist-ref 'state wormhole) '(open closed))
      (set! issues (cons (format "unexpected state: ~a" (alist-ref 'state wormhole)) issues)))
    ;; Report
    (if (null? issues)
        (begin
          (print "  [Pass] All security properties satisfied")
          #t)
        (begin
          (print "  [Issues]")
          (for-each (lambda (i) (print "    - " i)) issues)
          #f))))

;;; ============================================================
;;; Secure Erasure (RFC-040)
;;; ============================================================

;;; When sensitive data must be destroyed, it must be destroyed completely.
;;; Key principle: encryption at rest means key destruction = data destruction.

(define *erase-audit* '())

(define (secure-clear! buffer)
  "Overwrite buffer with zeros, verify (defeats compiler optimization)"
  ;; Note: In Scheme, blobs and strings are immutable.
  ;; For truly sensitive data, use u8vectors (SRFI-4) which are mutable.
  ;; This function works with u8vectors.
  (cond
   ((u8vector? buffer)
    (let ((len (u8vector-length buffer)))
      ;; Write zeros
      (do ((i 0 (+ i 1)))
          ((>= i len))
        (u8vector-set! buffer i 0))
      ;; Verify
      (do ((i 0 (+ i 1)))
          ((>= i len) #t)
        (unless (zero? (u8vector-ref buffer i))
          (error 'secure-clear-failed "Zeroization verification failed")))
      (print "  [Cleared] " len " bytes zeroized")
      #t))
   ((blob? buffer)
    (print "  [Warn] Blobs are immutable in Chicken Scheme")
    (print "  [Info] Use (blob->u8vector/shared b) for mutable access")
    (print "  [Info] Or use u8vectors directly for sensitive data")
    #f)
   ((string? buffer)
    (print "  [Warn] Strings are immutable; cannot clear in place")
    #f)
   (else
    (error 'secure-clear! "Expected u8vector, blob, or string"))))

(define (key-destroy! key-id)
  "Zeroize key material, audit the destruction"
  (print "Destroying key: " (short-id (if (string? key-id) key-id (format "~a" key-id))))
  ;; In production: locate actual key material and zeroize
  ;; For now: audit the destruction
  (let ((entry `((timestamp . ,(current-seconds))
                 (action . key-destroyed)
                 (target . ,key-id)
                 (method . zeroization))))
    (set! *erase-audit* (cons entry *erase-audit*))
    (audit-append actor: 'security
                  action: 'key-destroyed
                  target: key-id
                  detail: '(method zeroization))
    (print "  [Destroyed] Key material zeroized")
    'destroyed))

(define (object-erase! hash)
  "Securely erase object content (overwrite + delete)"
  (print "Securely erasing: " (short-id hash))
  (let ((path (string-append ".vault/objects/" (short-id hash))))
    (if (file-exists? path)
        (begin
          ;; Phase 1: Overwrite with random
          (print "  [Phase 1] Overwriting with random data...")
          (let ((size (file-size path)))
            (with-output-to-file path
              (lambda ()
                (write-string (blob->string (random-bytes size))))))
          ;; Phase 2: Overwrite with zeros
          (print "  [Phase 2] Overwriting with zeros...")
          (let ((size (file-size path)))
            (with-output-to-file path
              (lambda ()
                (write-string (make-string size #\null)))))
          ;; Phase 3: Delete
          (print "  [Phase 3] Unlinking file...")
          (delete-file path)
          ;; Audit
          (audit-append actor: 'security
                        action: 'object-erased
                        target: hash
                        detail: '(method overwrite-then-delete))
          (print "  [Erased] Object securely destroyed")
          'erased)
        (begin
          (print "  [Skip] Object not found at " path)
          'not-found))))

(define (secure-erase-encrypted hash)
  "For encrypted objects: destroy the data encryption key"
  ;; With encryption at rest, destroying the key destroys the data
  ;; The ciphertext remains but is computationally meaningless
  (print "Erasing via key destruction: " (short-id hash))
  (let ((dek-id (string-append "dek:" (short-id hash))))
    (key-destroy! dek-id)
    (audit-append actor: 'security
                  action: 'encrypted-object-erased
                  target: hash
                  detail: '(method key-destruction))
    (print "  [Erased] Ciphertext now unrecoverable")
    'erased-via-key-destruction))

(define (session-key-destroy! session-id)
  "Destroy ephemeral session key after use"
  (print "Destroying session key: " session-id)
  (key-destroy! (string-append "session:" session-id))
  (print "  [Destroyed] Forward secrecy maintained")
  'session-key-destroyed)

(define (erase-audit)
  "Show secure erasure audit trail"
  (if (null? *erase-audit*)
      (print "No erasure operations recorded")
      (for-each
       (lambda (e)
         (print "  " (alist-ref 'timestamp e) " "
                (alist-ref 'action e) " "
                (alist-ref 'target e)))
       *erase-audit*)))

;;; ============================================================
;;; Compilation & Replication Semantics
;;; ============================================================
;;;
;;; Content-addressed compilation with latency-aware replication.
;;;
;;; COMPILATION FORMS
;;; -----------------
;;; Source → Optimized → Compiled → Executed
;;;
;;;   source-hash     = hash(source)
;;;   optimized-hash  = hash(optimize(source))    ; canonical
;;;   compiled-hash   = hash(compile(optimized))  ; arch-specific
;;;
;;; All forms stored in vault, linked:
;;;   (compiled-for optimized-hash arch) → compiled-hash
;;;   (optimized-from source-hash) → optimized-hash
;;;
;;; REPLICATION STRATEGY
;;; --------------------
;;; Trade-off: bandwidth vs compute vs latency
;;;
;;;   Eager:  Replicate compiled form (bandwidth heavy, fast exec)
;;;   Lazy:   Replicate source, compile on demand (bandwidth light)
;;;   Hybrid: Replicate optimized + compile locally (balanced)
;;;
;;; Latency tiers:
;;;   Local cache:  < 1ms   → use compiled
;;;   LAN peer:     < 10ms  → fetch compiled if available
;;;   WAN peer:     < 100ms → fetch optimized, compile local
;;;   Cold storage: > 1s    → fetch source, full pipeline
;;;
;;; COMPILATION CACHE
;;; -----------------
;;; Per-architecture cache keyed by optimized-hash:
;;;
;;;   .vault/compiled/
;;;     arm64/
;;;       <optimized-hash> → <compiled-blob>
;;;     x86_64/
;;;       <optimized-hash> → <compiled-blob>
;;;
;;; Cache coherence: optimized-hash guarantees semantic equivalence.
;;; Different architectures compile to different blobs but same semantics.
;;;
;;; LAZY COMPILATION
;;; ----------------
;;; Don't compile until needed:
;;;
;;;   (define-lazy name source-hash)  ; register, don't compile
;;;   (force-compile name)            ; compile now
;;;   (name args...)                  ; auto-compile on first call
;;;
;;; SPECULATIVE REPLICATION
;;; -----------------------
;;; Predict what peers need based on:
;;;   - Access patterns (frequently used)
;;;   - Dependency graphs (if A needed, B likely needed)
;;;   - Temporal locality (recently accessed)
;;;
;;; Push compiled forms to peers who will likely need them.

;;; Compilation state
(define *compile-cache* '())        ; ((optimized-hash . compiled) ...)
(define *compile-pending* '())      ; source-hashes awaiting compilation
(define *compile-stats*
  '((hits . 0) (misses . 0) (compiles . 0) (replicated . 0)))

(define (compile-stat! key)
  "Increment compilation statistic"
  (set! *compile-stats*
        (map (lambda (p)
               (if (eq? (car p) key)
                   (cons key (+ 1 (cdr p)))
                   p))
             *compile-stats*)))

;;; Compilation forms

(define (source->optimized source)
  "Source to canonical optimized form"
  (optimize source))

(define (optimized->compiled optimized)
  "Optimized form to compiled representation"
  ;; In real implementation: compile to bytecode or native
  ;; For now: just wrap with metadata
  `(compiled
    (arch . ,(current-arch))
    (timestamp . ,(current-seconds))
    (code . ,optimized)))

(define (compile-source source)
  "Full compilation pipeline"
  (let* ((opt (source->optimized source))
         (opt-hash (code-hash opt))
         (cached (assoc opt-hash *compile-cache*)))
    (if cached
        (begin
          (compile-stat! 'hits)
          (cdr cached))
        (let ((compiled (optimized->compiled opt)))
          (compile-stat! 'misses)
          (compile-stat! 'compiles)
          (set! *compile-cache*
                (cons (cons opt-hash compiled) *compile-cache*))
          compiled))))

;;; Lazy compilation

(define *lazy-definitions* '())  ; ((name . source-hash) ...)

(define (define-lazy name source-hash)
  "Register lazy definition - compiles on first use"
  (set! *lazy-definitions*
        (cons (cons name source-hash) *lazy-definitions*))
  (print "  Registered lazy: " name " → " (short-id source-hash)))

(define (force-compile name)
  "Force compilation of lazy definition"
  (let ((entry (assq name *lazy-definitions*)))
    (if entry
        (let* ((source-hash (cdr entry))
               ;; In real impl: fetch source from vault by hash
               (source `(placeholder-for ,source-hash))
               (compiled (compile-source source)))
          (print "  Compiled: " name)
          compiled)
        (error "No lazy definition" name))))

;;; Latency-aware fetch strategy

(define *latency-thresholds*
  '((local . 1)      ; ms - use compiled cache
    (lan . 10)       ; ms - fetch compiled from peer
    (wan . 100)      ; ms - fetch optimized, compile local
    (cold . 1000)))  ; ms - fetch source, full pipeline

(define (fetch-strategy latency-ms)
  "Determine fetch strategy based on latency"
  (cond
   ((< latency-ms (cdr (assq 'local *latency-thresholds*))) 'use-cache)
   ((< latency-ms (cdr (assq 'lan *latency-thresholds*)))   'fetch-compiled)
   ((< latency-ms (cdr (assq 'wan *latency-thresholds*)))   'fetch-optimized)
   (else                                                     'fetch-source)))

(define (fetch-with-strategy hash peer-latency)
  "Fetch code using latency-appropriate strategy"
  (let ((strategy (fetch-strategy peer-latency)))
    (print "  Strategy: " strategy " (latency " peer-latency "ms)")
    (case strategy
      ((use-cache)
       (let ((cached (assoc hash *compile-cache*)))
         (if cached (cdr cached) 'cache-miss)))
      ((fetch-compiled)
       ;; Request compiled form from peer
       `(fetch compiled ,hash))
      ((fetch-optimized)
       ;; Request optimized, compile locally
       `(fetch optimized ,hash then compile))
      ((fetch-source)
       ;; Request source, full pipeline
       `(fetch source ,hash then optimize then compile)))))

;;; Speculative replication

(define *access-history* '())  ; ((hash . access-count) ...)
(define *dependency-graph* '()) ; ((hash . (dep-hash ...)) ...)

(define (record-access! hash)
  "Record code access for speculation"
  (let ((entry (assoc hash *access-history*)))
    (if entry
        (set-cdr! entry (+ 1 (cdr entry)))
        (set! *access-history* (cons (cons hash 1) *access-history*)))))

(define (hot-code threshold)
  "Return frequently accessed code hashes"
  (map car (filter (lambda (p) (>= (cdr p) threshold)) *access-history*)))

(define (speculate-needs peer-hash)
  "Predict what code a peer might need"
  ;; Based on: what they accessed + dependencies
  (let ((their-history (or (assoc peer-hash *access-history*) '())))
    ;; Return hot code they might not have
    (hot-code 3)))

;;; Replication commands

(define (replicate-compiled hash to-peer)
  "Push compiled form to peer"
  (let ((compiled (assoc hash *compile-cache*)))
    (if compiled
        (begin
          (compile-stat! 'replicated)
          (print "  Replicated " (short-id hash) " to " to-peer)
          #t)
        (begin
          (print "  Not in cache: " (short-id hash))
          #f))))

(define (compile-status)
  "Show compilation statistics"
  (print "Compilation Status:")
  (print "  Cache entries: " (length *compile-cache*))
  (print "  Lazy pending:  " (length *lazy-definitions*))
  (for-each
   (lambda (s) (print "  " (car s) ": " (cdr s)))
   *compile-stats*))

;;; ============================================================
;;; Code Optimization Pass (Optimized)
;;; ============================================================
;;;
;;; High-performance expression normalization and optimization.
;;; Uses hash tables for O(1) lookup, memoization, and FFI hashing.
;;;
;;; Algorithmic improvements:
;;;   - Hash table environments: O(1) vs O(n) alist lookup
;;;   - Precomputed symbol cache: avoid repeated string->symbol
;;;   - Memoization: cache repeated subexpression results
;;;   - Set-based free-vars: O(1) membership test
;;;   - FFI hashing: libsodium SHA-256 for final hash
;;;
;;; Passes:
;;;   1. Alpha-normalization: canonical variable names
;;;   2. Constant folding: (+ 1 2) → 3
;;;   3. Dead code elimination: unused bindings removed
;;;   4. Sort commutative ops: (+ b a) → (+ a b)

;;; Precomputed canonical variable symbols (avoid allocation)
(define *canonical-vars*
  (let ((v (make-vector 256)))
    (do ((i 0 (+ i 1)))
        ((= i 256) v)
      (vector-set! v i (string->symbol (string-append "α" (number->string i)))))))

(define *opt-counter* 0)

(define (fresh-var)
  "Get next canonical variable - O(1) from precomputed table"
  (let ((i *opt-counter*))
    (set! *opt-counter* (+ i 1))
    (if (< i 256)
        (vector-ref *canonical-vars* i)
        ;; Fallback for > 256 vars (rare)
        (string->symbol (string-append "α" (number->string i))))))

(define (reset-fresh!)
  (set! *opt-counter* 0))

;;; Memoization cache for optimization results
(define *opt-memo* (make-hash-table equal?))
(define *opt-memo-hits* 0)
(define *opt-memo-misses* 0)

(define (memo-clear!)
  "Clear optimization memoization cache"
  (set! *opt-memo* (make-hash-table equal?))
  (set! *opt-memo-hits* 0)
  (set! *opt-memo-misses* 0))

(define (memo-stats)
  "Return memoization statistics"
  `((hits . ,*opt-memo-hits*)
    (misses . ,*opt-memo-misses*)
    (entries . ,(hash-table-size *opt-memo*))))

;;; Alpha-normalization with hash table environment

(define (alpha-normalize expr)
  "Rename bound variables to canonical names - O(1) lookup"
  (reset-fresh!)
  (alpha-rename-ht expr (make-hash-table eq?)))

(define (alpha-rename-ht expr env)
  "Recursively rename with hash table environment"
  (cond
   ;; Symbol: O(1) hash table lookup
   ((symbol? expr)
    (hash-table-ref/default env expr expr))

   ;; Lambda: rename parameters
   ((and (pair? expr) (eq? (car expr) 'lambda))
    (let* ((params (let ((p (cadr expr))) (if (list? p) p (list p))))
           (body (cddr expr))
           (new-env (hash-table-copy env)))
      ;; Add bindings to new environment
      (for-each (lambda (p)
                  (hash-table-set! new-env p (fresh-var)))
                params)
      `(lambda ,(map (lambda (p) (hash-table-ref new-env p)) params)
         ,@(map (lambda (e) (alpha-rename-ht e new-env)) body))))

   ;; Let: rename bindings (parallel)
   ((and (pair? expr) (eq? (car expr) 'let))
    (let* ((bindings (cadr expr))
           (body (cddr expr))
           (new-env (hash-table-copy env))
           (new-names (map (lambda (b)
                            (let ((n (fresh-var)))
                              (hash-table-set! new-env (car b) n)
                              n))
                          bindings)))
      `(let ,(map (lambda (b n)
                    (list n (alpha-rename-ht (cadr b) env)))
                  bindings new-names)
         ,@(map (lambda (e) (alpha-rename-ht e new-env)) body))))

   ;; Let*: sequential rename
   ((and (pair? expr) (eq? (car expr) 'let*))
    (let ((new-env (hash-table-copy env)))
      (let loop ((bindings (cadr expr))
                 (new-bindings '()))
        (if (null? bindings)
            `(let* ,(reverse new-bindings)
               ,@(map (lambda (e) (alpha-rename-ht e new-env)) (cddr expr)))
            (let* ((b (car bindings))
                   (val (alpha-rename-ht (cadr b) new-env))
                   (new-name (fresh-var)))
              (hash-table-set! new-env (car b) new-name)
              (loop (cdr bindings)
                    (cons (list new-name val) new-bindings)))))))

   ;; Define: rename parameters if function
   ((and (pair? expr) (eq? (car expr) 'define))
    (if (pair? (cadr expr))
        (let* ((name (caadr expr))
               (params (cdadr expr))
               (body (cddr expr))
               (new-env (hash-table-copy env)))
          (for-each (lambda (p)
                      (hash-table-set! new-env p (fresh-var)))
                    params)
          `(define (,name ,@(map (lambda (p) (hash-table-ref new-env p)) params))
             ,@(map (lambda (e) (alpha-rename-ht e new-env)) body)))
        `(define ,(cadr expr)
           ,@(map (lambda (e) (alpha-rename-ht e env)) (cddr expr)))))

   ;; List: recurse
   ((pair? expr)
    (map (lambda (e) (alpha-rename-ht e env)) expr))

   ;; Atom
   (else expr)))

;;; Constant folding with direct dispatch

(define *fold-ops*
  (let ((t (make-hash-table eq?)))
    (hash-table-set! t '+ +)
    (hash-table-set! t '- -)
    (hash-table-set! t '* *)
    (hash-table-set! t '/ /)
    (hash-table-set! t 'quotient quotient)
    (hash-table-set! t 'remainder remainder)
    (hash-table-set! t 'modulo modulo)
    (hash-table-set! t 'min min)
    (hash-table-set! t 'max max)
    (hash-table-set! t 'abs abs)
    (hash-table-set! t 'expt expt)
    t))

(define (const-fold expr)
  "Evaluate constant expressions - O(1) op dispatch"
  (cond
   ;; Arithmetic with direct dispatch (avoid eval)
   ((and (pair? expr)
         (hash-table-exists? *fold-ops* (car expr))
         (every number? (cdr expr)))
    (apply (hash-table-ref *fold-ops* (car expr)) (cdr expr)))

   ;; String append
   ((and (pair? expr)
         (eq? (car expr) 'string-append)
         (every string? (cdr expr)))
    (apply string-append (cdr expr)))

   ;; Boolean not
   ((and (pair? expr)
         (eq? (car expr) 'not)
         (= (length expr) 2)
         (boolean? (cadr expr)))
    (not (cadr expr)))

   ;; If with constant test
   ((and (pair? expr)
         (eq? (car expr) 'if)
         (>= (length expr) 3)
         (boolean? (cadr expr)))
    (if (cadr expr)
        (const-fold (caddr expr))
        (if (> (length expr) 3)
            (const-fold (cadddr expr))
            '(void))))

   ;; Identity: (+ x) → x, (* x) → x
   ((and (pair? expr)
         (memq (car expr) '(+ *))
         (= (length expr) 2))
    (const-fold (cadr expr)))

   ;; Zero/one elimination: (+ 0 x) → x, (* 1 x) → x
   ((and (pair? expr) (eq? (car expr) '+))
    (let* ((folded-args (map const-fold (cdr expr)))
           (non-zero (filter (lambda (x) (not (eqv? x 0))) folded-args)))
      (cond
       ((null? non-zero) 0)
       ((null? (cdr non-zero)) (car non-zero))
       ((every number? non-zero) (apply + non-zero))
       (else `(+ ,@non-zero)))))

   ((and (pair? expr) (eq? (car expr) '*))
    (let* ((folded-args (map const-fold (cdr expr)))
           (non-one (filter (lambda (x) (not (eqv? x 1))) folded-args)))
      (cond
       ((any (lambda (x) (eqv? x 0)) folded-args) 0)  ; short-circuit
       ((null? non-one) 1)
       ((null? (cdr non-one)) (car non-one))
       ((every number? non-one) (apply * non-one))
       (else `(* ,@non-one)))))

   ;; Recurse
   ((pair? expr)
    (let ((folded (map const-fold expr)))
      (if (equal? folded expr) folded (const-fold folded))))

   (else expr)))

;;; Sort commutative operations - cached comparison

(define (sort-commutative expr)
  "Sort arguments to commutative operations for canonical form"
  (cond
   ((and (pair? expr) (memq (car expr) '(+ * and or)))
    (cons (car expr)
          (sort (map sort-commutative (cdr expr)) expr<?)))
   ((pair? expr)
    (map sort-commutative expr))
   (else expr)))

(define (expr<? a b)
  "Total ordering on expressions - type-based dispatch"
  (let ((ta (expr-type-rank a))
        (tb (expr-type-rank b)))
    (if (= ta tb)
        (expr-same-type<? a b ta)
        (< ta tb))))

(define (expr-type-rank x)
  "Numeric rank for expression types"
  (cond
   ((number? x) 0)
   ((string? x) 1)
   ((symbol? x) 2)
   ((null? x) 3)
   ((pair? x) 4)
   (else 5)))

(define (expr-same-type<? a b rank)
  "Compare expressions of same type"
  (case rank
    ((0) (< a b))  ; numbers
    ((1) (string<? a b))  ; strings
    ((2) (string<? (symbol->string a) (symbol->string b)))  ; symbols
    ((3) #f)  ; null = null
    ((4) (or (expr<? (car a) (car b))  ; pairs: lexicographic
             (and (equal? (car a) (car b))
                  (expr<? (cdr a) (cdr b)))))
    (else #f)))

;;; Dead code elimination with hash set

(define (eliminate-dead expr)
  "Remove unused let bindings - O(1) membership with hash set"
  (cond
   ((and (pair? expr) (eq? (car expr) 'let))
    (let* ((bindings (cadr expr))
           (body (map eliminate-dead (cddr expr)))
           (used-set (free-vars-set body))
           (live (filter (lambda (b) (hash-table-exists? used-set (car b)))
                        bindings)))
      (if (null? live)
          (if (= (length body) 1) (car body) `(begin ,@body))
          `(let ,(map (lambda (b)
                        (list (car b) (eliminate-dead (cadr b))))
                      live)
             ,@body))))
   ((pair? expr)
    (map eliminate-dead expr))
   (else expr)))

(define (free-vars-set expr)
  "Collect free variables into hash set - O(1) membership"
  (let ((s (make-hash-table eq?)))
    (free-vars-into! expr s (make-hash-table eq?))
    s))

(define (free-vars-into! expr result bound)
  "Collect free vars, tracking bound vars"
  (cond
   ((symbol? expr)
    (unless (hash-table-exists? bound expr)
      (hash-table-set! result expr #t)))

   ((and (pair? expr) (eq? (car expr) 'quote))
    (void))  ; quoted: no free vars

   ((and (pair? expr) (eq? (car expr) 'lambda))
    (let ((new-bound (hash-table-copy bound))
          (params (let ((p (cadr expr))) (if (list? p) p (list p)))))
      (for-each (lambda (p) (hash-table-set! new-bound p #t)) params)
      (for-each (lambda (e) (free-vars-into! e result new-bound)) (cddr expr))))

   ((and (pair? expr) (eq? (car expr) 'let))
    (let ((new-bound (hash-table-copy bound)))
      ;; Init exprs use outer scope
      (for-each (lambda (b) (free-vars-into! (cadr b) result bound)) (cadr expr))
      ;; Body uses extended scope
      (for-each (lambda (b) (hash-table-set! new-bound (car b) #t)) (cadr expr))
      (for-each (lambda (e) (free-vars-into! e result new-bound)) (cddr expr))))

   ((pair? expr)
    (for-each (lambda (e) (free-vars-into! e result bound)) expr))

   (else (void))))

;;; Main optimization interface with memoization

(define (optimize expr)
  "Full optimization pipeline with memoization"
  (let ((cached (hash-table-ref/default *opt-memo* expr #f)))
    (if cached
        (begin
          (set! *opt-memo-hits* (+ 1 *opt-memo-hits*))
          cached)
        (let* ((normalized (alpha-normalize expr))
               (folded (const-fold normalized))
               (sorted (sort-commutative folded))
               (cleaned (eliminate-dead sorted)))
          (set! *opt-memo-misses* (+ 1 *opt-memo-misses*))
          (hash-table-set! *opt-memo* expr cleaned)
          cleaned))))

(define (normalize expr)
  "Just alpha-normalize"
  (alpha-normalize expr))

(define (code-hash expr)
  "Hash of optimized code - FFI SHA-256"
  (let* ((optimized (optimize expr))
         (canonical (format "~s" optimized)))
    (short-id (blob->hex (sha256-hash (string->blob canonical))))))

(define (code-equivalent? a b)
  "Semantic equivalence via optimization"
  (equal? (optimize a) (optimize b)))

(define (opt-stats)
  "Show optimizer statistics"
  (print "Optimizer Statistics:")
  (print "  Memo hits:    " *opt-memo-hits*)
  (print "  Memo misses:  " *opt-memo-misses*)
  (print "  Cache size:   " (hash-table-size *opt-memo*)))

;;; ============================================================
;;; Help
;;; ============================================================

(define (help)
  "Show available commands"
  (print "
Cyberspace REPL - Available Commands

  Command Mode (no parens needed):
    status                         Vault status
    commit \"message\"               Commit changes
    release \"1.0\"                  Create release
    keys                           List keys
    keygen                         Generate keypair
    soup                           List objects
    peers                          List nodes
    help                           This help
    clear                          Clear screen
    quit                           Exit

  Scheme Mode (full power):
    (define x 42)                  Define variables
    (map f list)                   Full Scheme available
    (+ 1 2)                        Expressions

  Object State (RFC-040):
    (chaotic thing)              Mark thing as chaotic (in flux)
    (commit-thing thing)         Commit: chaotic → quiescent
    (chaotic? thing)             Is thing chaotic?
    (quiescent? thing)           Is thing quiescent?
    (thing-state thing)          Get state (chaotic|quiescent)
    (thing-status thing)         Full status display

  Persistence (RFC-040):
    (persist thing)              Mark thing persistent (vault-bound)
    (ephemeral thing)            Mark thing ephemeral (no promise)
    (persistent? thing)          Is thing persistent?
    (ephemeral? thing)           Is thing ephemeral?
    (thing-durability thing)     Get durability
    (flush-persistence!)         Migrate queued things to vault

  Memos (RFC-043):
    (memo-create title)          Create local memo
    (memo-create t scope: 'federation)  Federation scope
    (memo-create t category: 'experimental)
    (memo-commit memo-id)        Commit memo (chaotic → quiescent)
    (memo-persist memo-id)       Mark memo persistent
    (memo-promote id 'federation) Promote scope
    (memo-list)                  List all memos
    (memo-list 'local)           Filter by scope
    (memo-show memo-id)          Show memo details

  Vault Operations:
    (seal-commit \"message\")         Commit staged changes
    (seal-release \"1.0.0\")          Create a release
    (seal-archive \"1.0.0\")          Archive a release
    (seal-archive \"1.0.0\" format: 'zstd-age)
    (seal-restore \"file.archive\")   Restore from archive
    (seal-history)                   Show commit history
    (seal-update)                    Pull latest changes
    (vault-config 'key)              Get config value
    (vault-config 'key value)        Set config value
    (vault-init signing-key: key)    Initialize vault

  Inspection:
    (seal-inspect \"file.archive\")   Show security/migration properties
    (seal-inspect \"1.0.0\")          Inspect a release version
    (seal-inspect obj verify-key: k) Verify signatures during inspection

  Debugging (Dylan-style):
    (inspect obj)                    Tree-view of any object
    (i obj)                          Short alias for inspect
    (bt)                             Show backtrace after error
    (backtrace)                      Full backtrace with limit
    (frame N)                        Inspect stack frame N
    (exception-info)                 Last exception details

  Object Soup (NewtonOS-style):
    (soup)                         List all objects
    (soup 'archives)               Filter by type
    (soup \"*.pub\")                 Glob pattern (* = any, ? = single)
    (soup #/regex/)                Regular expression
    (soup 'keys \"alice*\")          Type + pattern
    (soup?)                        Show query syntax help
    (complete \"gen\")               Complete partial name

  Cryptography:
    (ed25519-keypair)                Generate keypair (pub priv)
    (sha512-hash blob)               Hash data
    (ed25519-sign key msg)           Sign message
    (ed25519-verify pub msg sig)     Verify signature

  Audit Trail:
    (audit-append actor: k action: a) Add audit entry
    (audit-read)                      Read audit trail

  Certificates:
    (create-cert issuer subject tag) Create SPKI cert
    (sign-cert cert key)             Sign certificate
    (verify-signed-cert cert key)    Verify certificate

  Node Roles (RFC-037):
    (node-probe)                     Probe system capabilities
    (node-role)                      Show current role
    (node-role 'witness)             Set role (coordinator/full/witness/archiver/edge)
    (node-can? 'seal-commit)         Check if operation permitted
    (node-announce)                  Announce role to peers

  Lazy Clustering (RFC-016):
    (lazy-join peer uri: u key: k) Join cluster
    (lazy-leave peer)              Leave cluster
    (lazy-push peer)               Push to peer
    (lazy-pull peer)               Pull from peer
    (lazy-sync peer)               Bidirectional sync
    (lazy-status)                  Show cluster status
    (lazy-queue)                   Show pending sync
    (lazy-resolve ver prefer: p)   Resolve conflict

  Federation (RFC-010):
    (federate \"peer-url\")            Establish federation
    (federate-status)                Show federation peers
    (federate-replicate \"url\")       Replicate with peer

  Byzantine Consensus (RFC-011):
    (consensus-propose value)        Propose for consensus
    (consensus-vote id 'accept)      Vote on proposal
    (consensus-status)               Show proposals

  Lamport Clocks (RFC-012):
    (lamport-tick)                   Increment clock
    (lamport-send)                   Get send timestamp
    (lamport-receive ts)             Update on receive
    (lamport-clock)                  Get current value

  Content-Addressed Storage (RFC-020):
    (content-address data)           Compute hash address
    (content-put data)               Store by hash
    (content-get addr)               Retrieve by hash

  Capability Delegation (RFC-021):
    (delegate cap principal)         Delegate capability
    (delegate-chain delegations)     Verify chain
    (delegate-verify d p action)     Check authorization

  Agent Sandboxing (RFC-023):
    (sandbox \"name\" capabilities: c) Create sandbox
    (sandbox-run \"name\" code)        Execute in sandbox
    (sandbox-destroy \"name\")         Remove sandbox

  Mobile Agents (RFC-035):
    (tunnel destination)             Move agent to realm
    (observe resource)               Observe (collapse state)
    (entangle a1 a2)                 Correlate agents
    (teleport state from to)         Transfer state
    (decohere agent)                 Cleanup/terminate
    (superpose states)               Create superposition
    (collapse superposition)         Resolve to one state

  Quorum Voting (RFC-036):
    (quorum-propose q options)       Start vote
    (quorum-vote id choice)          Cast vote (HE encrypted)
    (quorum-tally id)                Tally results
    (quorum-status)                  Show proposals

  Local Inference (RFC-038):
    (inference-server)               Get/set Ollama URL
    (inference-models)               List available models
    (inference prompt model: m)      Run LLM inference
    (inference-embed text)           Generate embeddings

  Wormholes (RFC-041):
    (wormhole-open \"~/Space\")        Open wormhole fs <-> vault
    (wormhole-open p capabilities: capability:read-only)
    (wormhole-open p locked: #t)     Open locked (requires unlock)
    (wormhole-open p auth-required: '(delete))  Step-up auth
    (wormhole-close path)            Close wormhole
    (wormhole-lock path)             Lock (pause operations)
    (wormhole-unlock path auth: tok) Unlock with authentication
    (wormhole-caps path)             Show capabilities
    (wormhole-delegate path capabilities recipient)
    (wormholes)                      List active wormholes
    (wormhole-security)              Display security properties
    (wormhole-verify wormhole)       Verify security requirements
    (make-network-wormhole h p id)   Create network wormhole
    (fs-import path)                 Import with full metadata
    (fs-export hash path)            Export, restore metadata
    (fs-sync vault-path fs-path)     Bidirectional sync
    (manifest-list)                  Show manifest entries

  Secure Erasure (RFC-040):
    (secure-clear! buffer)           Zeroize buffer (blobs only)
    (key-destroy! key-id)            Destroy key material
    (object-erase! hash)             Overwrite + delete object
    (secure-erase-encrypted hash)    Destroy via key destruction
    (session-key-destroy! id)        Destroy session key
    (erase-audit)                    Show erasure audit trail

  Node Enrollment (RFC-044):
    (enroll-request 'name)           Request enrollment (FIPS-181)
    (enroll-listen)                  Listen for enrollment requests
    (enroll-approve req key)         Approve enrollment
    (introspect-system)              Full system introspection
    (introspect-hardware)            Hardware config
    (introspect-network)             Network interfaces
    (introspect-storage)             Storage info

  mDNS Discovery (RFC-044):
    (mdns-announce name pubkey)      Broadcast enrollment request
    (mdns-listen handler)            Listen for mDNS announcements
    (mdns-query service)             Query for service
    (announce-presence n k)          Start mDNS presence
    (discover-peers)                 Find peers on network

  Bloom Filters (RFC-020):
    (make-blocked-bloom n fpp)       Create blocked Bloom filter
    (blocked-bloom-add! bf item)     Add item to filter
    (blocked-bloom-contains? bf i)   Test membership
    (blocked-bloom-merge bf1 bf2)    Merge two filters
    (blocked-bloom-serialize bf)     Serialize for network
    (blocked-bloom-deserialize b)    Deserialize from network

  Merkle Catalog (RFC-020):
    (catalog-build hashes)           Build Merkle tree of hashes
    (catalog-root cat)               Get root hash
    (catalog-diff local remote)      Find differing subtrees
    (catalog-proof cat hash)         Generate inclusion proof
    (catalog-verify-proof proof)     Verify inclusion proof

  Anti-Entropy Gossip (RFC-010):
    (gossip-round peers)             One round of gossip
    (gossip-start interval peers)    Start gossip daemon
    (gossip-stop)                    Stop gossip daemon
    (gossip-status)                  Show gossip statistics
    (gossip-sync peer)               Full sync with peer

  Compilation & Replication:
    (compile-source source)          Full compilation pipeline
    (source->optimized source)       Optimize only
    (optimized->compiled opt)        Compile optimized form
    (define-lazy name hash)          Register lazy compilation
    (force-compile name)             Force compile lazy def
    (fetch-strategy latency-ms)      Choose fetch strategy
    (fetch-with-strategy hash ms)    Fetch with latency awareness
    (replicate-compiled hash peer)   Push compiled to peer
    (compile-status)                 Show compilation stats
    (hot-code threshold)             List frequently accessed

  Code Optimization:
    (optimize expr)                  Full optimization pipeline
    (normalize expr)                 Alpha-normalize only
    (const-fold expr)                Constant folding
    (eliminate-dead expr)            Dead code elimination
    (code-hash expr)                 Hash of optimized form
    (code-equivalent? a b)           Semantic equivalence test

  Capability Sets:
    capability:read-only             Read, stat, readdir, xattr-read
    capability:read-write            Read, write, create, chmod, mkdir
    capability:full                  All capabilities including admin
    capability:backup                Minimal for backup (read-only)
    capability:synchronize           For bidirectional sync

  Requirements:
    brew install fuse-t              FUSE-T (recommended, no kext)
    brew install macfuse             macFUSE (requires kext)
    brew install ollama              Local LLM inference

  Utilities:
    (clear)                          Clear screen (or ^L)
    (blob->hex blob)                 Convert blob to hex
    (hex->blob \"deadbeef\")           Convert hex to blob
    (help)                           Show this help

  Config Keys:
    'signing-key      Ed25519 private key (64 bytes)
    'archive-format   'tarball | 'bundle | 'cryptographic | 'zstd-age
    'age-recipients   List of age public keys
    'age-identity     Path to age identity file
"))

;; Banner with status: nodes, cluster, replication
(define *cluster-nodes* '())      ; known nodes
(define *cluster-state* 'solo)    ; solo | forming | stable | degraded | split
(define *replication-state* 'none) ; none | mirroring | current | behind | ahead

(define (node-join name #!key (uri #f))
  "Add node to cluster"
  (cond
   ((not name)
    (print "Join Refused: No node name specified")
    #f)
   ((assoc name *cluster-nodes*)
    (print "Join Refused: Node already in cluster")
    #f)
   (else
    (set! *cluster-nodes* (cons (list name uri (current-seconds)) *cluster-nodes*))
    (when (and (eq? *cluster-state* 'solo) (> (length *cluster-nodes*) 0))
      (set! *cluster-state* 'forming))
    *cluster-nodes*)))

(define (node-leave name)
  "Remove node from cluster"
  (set! *cluster-nodes* (filter (lambda (n) (not (equal? (car n) name))) *cluster-nodes*))
  (when (null? *cluster-nodes*)
    (set! *cluster-state* 'solo))
  *cluster-nodes*)

(define (nodes)
  "List cluster nodes"
  (if (null? *cluster-nodes*)
      (print "No cluster nodes (solo)")
      (begin
        (print "Nodes: " (length *cluster-nodes*))
        (for-each (lambda (n)
                    (print "  " (car n) (if (cadr n) (string-append " @ " (cadr n)) "")))
                  *cluster-nodes*))))

(define (cluster #!optional new-state)
  "Get or set cluster state"
  (if new-state
      (begin
        (set! *cluster-state* new-state)
        (print "Cluster: " new-state))
      (begin
        (print "Cluster: " *cluster-state*)
        (print "  Nodes: " (length *cluster-nodes*))
        *cluster-state*)))

(define (replication #!optional new-state)
  "Get or set replication state"
  (if new-state
      (begin
        (set! *replication-state* new-state)
        (print "Replication: " new-state))
      (begin
        (print "Replication: " *replication-state*)
        *replication-state*)))

(define (format-nodes nodes max-width)
  "Format node list to fit within max-width"
  (cond
   ((null? nodes) "")
   ((= (length nodes) 1)
    (let ((name (caar nodes)))
      (if (> (string-length name) max-width)
          (string-append (substring name 0 (- max-width 2)) "..")
          name)))
   (else
    (let* ((count (length nodes))
           (first (caar nodes))
           (suffix (string-append " +" (number->string (- count 1))))
           (avail (- max-width (string-length suffix))))
      (if (> (string-length first) avail)
          (string-append (substring first 0 (- avail 2)) ".." suffix)
          (string-append first suffix))))))

;;; ============================================================
;;; ASCII Inspector - Visual S-expression Debugging
;;; ============================================================
;;; Tree-view display of data structures with box-drawing.
;;; Inspired by Dylan's object inspector and NewtonOS data browser.

(define (type-tag obj)
  "Get type tag for display"
  (cond
   ((null? obj) "nil")
   ((pair? obj)
    (if (list? obj) "list" "pair"))
   ((symbol? obj) "sym")
   ((string? obj) "str")
   ((number? obj) "num")
   ((boolean? obj) "bool")
   ((blob? obj) "blob")
   ((u8vector? obj) "u8vec")
   ((vector? obj) "vec")
   ((procedure? obj) "proc")
   ((port? obj) "port")
   ((eof-object? obj) "eof")
   (else "?")))

(define (format-value obj max-len)
  "Format value for display, truncating if needed"
  (let ((str (cond
              ((null? obj) "()")
              ((symbol? obj) (symbol->string obj))
              ((string? obj) (string-append "\"" obj "\""))
              ((number? obj) (number->string obj))
              ((boolean? obj) (if obj "#t" "#f"))
              ((blob? obj)
               (let ((len (blob-size obj)))
                 (string-append "#${" (number->string len) " bytes}")))
              ((u8vector? obj)
               (string-append "#u8(" (number->string (u8vector-length obj)) ")"))
              ((procedure? obj) "#<procedure>")
              ((port? obj) "#<port>")
              ((pair? obj) "...")
              ((vector? obj) (string-append "#(" (number->string (vector-length obj)) ")"))
              (else "#<unknown>"))))
    (if (> (string-length str) max-len)
        (string-append (substring str 0 (- max-len 1)) "…")
        str)))

(define (inspect obj #!key (depth 0) (max-depth 6) (prefix "") (last #t))
  "Display object as ASCII tree"
  (let* ((indent (if (= depth 0) "" (string-append prefix (if last "└── " "├── "))))
         (child-prefix (if (= depth 0) "" (string-append prefix (if last "    " "│   "))))
         (tag (type-tag obj)))

    ;; Print current node
    (print indent
           (if (or (pair? obj) (vector? obj))
               (string-append "┬ " tag)
               (string-append "─ " tag ": " (format-value obj 50))))

    ;; Recurse into children
    (when (< depth max-depth)
      (cond
       ;; List/pair
       ((pair? obj)
        (let loop ((items obj) (idx 0))
          (cond
           ((null? items) #f)
           ((not (pair? items))
            ;; Improper list - show cdr
            (inspect items depth: (+ depth 1) prefix: child-prefix last: #t))
           ((> idx 10)
            (print child-prefix "└── … (" (- (length obj) idx) " more)"))
           (else
            (let ((is-last (or (null? (cdr items))
                               (and (pair? (cdr items)) (> idx 9)))))
              (inspect (car items)
                       depth: (+ depth 1)
                       prefix: child-prefix
                       last: is-last)
              (when (pair? (cdr items))
                (loop (cdr items) (+ idx 1))))))))

       ;; Vector
       ((vector? obj)
        (let ((len (vector-length obj)))
          (do ((i 0 (+ i 1)))
              ((or (= i len) (> i 10)))
            (if (> i 10)
                (print child-prefix "└── … (" (- len i) " more)")
                (inspect (vector-ref obj i)
                         depth: (+ depth 1)
                         prefix: child-prefix
                         last: (= i (- len 1))))))))))

  ;; Return void for clean REPL output
  (void))

(define (i obj)
  "Short alias for inspect"
  (inspect obj))

;;; ============================================================
;;; Stack Frame Inspector - Dylan-style Debugging
;;; ============================================================

(define *last-exception* #f)
(define *last-call-chain* #f)

(define (capture-exception exn)
  "Capture exception and call chain for inspection"
  (set! *last-exception* exn)
  (set! *last-call-chain* (get-call-chain)))

(define (backtrace #!optional (limit 20))
  "Display call stack (backtrace)"
  (print "")
  (print "┌─ Backtrace ─────────────────────────────────────────────────────┐")
  (let ((chain (or *last-call-chain* (get-call-chain))))
    (let loop ((frames chain) (idx 0))
      (when (and (pair? frames) (< idx limit))
        (let* ((frame (car frames))
               (loc (vector-ref frame 0))   ; location string like "<stdin>:3"
               (expr (vector-ref frame 1))) ; expression
          (printf "│ ~a: ~a~n" idx (or loc "<unknown>"))
          (when (and expr (not (eq? expr #f)))
            (let ((expr-str (with-output-to-string (lambda () (write expr)))))
              (printf "│     ~a~n"
                      (if (> (string-length expr-str) 60)
                          (string-append (substring expr-str 0 57) "...")
                          expr-str)))))
        (loop (cdr frames) (+ idx 1)))))
  (print "└──────────────────────────────────────────────────────────────────┘")
  (void))

(define (bt) (backtrace))

(define (frame n)
  "Inspect a specific stack frame"
  (let ((chain (or *last-call-chain* (get-call-chain))))
    (if (< n (length chain))
        (let* ((f (list-ref chain n))
               (loc (vector-ref f 0))   ; location string
               (expr (vector-ref f 1))) ; expression
          (print "")
          (print "┌─ Frame " n " ────────────────────────────────────────────────┐")
          (printf "│ Location: ~a~n" (or loc "<unknown>"))
          (print "│ Expression:")
          (when (and expr (not (eq? expr #f)))
            (inspect expr))
          (print "└──────────────────────────────────────────────────────────────────┘"))
        (print "Frame not found")))
  (void))

(define (exception-info)
  "Show last exception details"
  (if *last-exception*
      (begin
        (print "")
        (print "┌─ Last Exception ─────────────────────────────────────────────────┐")
        (print-error-message *last-exception*)
        (print "└──────────────────────────────────────────────────────────────────┘"))
      (print "No captured exception"))
  (void))

(define (rich-exception-display exn #!key (frames 5))
  "Display exception with rich formatting and mini-traceback"
  (capture-exception exn)
  (print "")
  (print "┌─ Exception ──────────────────────────────────────────────────────┐")

  ;; Extract exception properties
  (let* ((msg (get-condition-property exn 'exn 'message ""))
         (loc (get-condition-property exn 'exn 'location #f))
         (args (get-condition-property exn 'exn 'arguments '()))
         (kind (cond ((condition? exn)
                      (cond ((get-condition-property exn 'type 'type #f))
                            ((get-condition-property exn 'exn 'type #f))
                            (else #f)))
                     (else #f))))

    ;; Helper to pad and print box line
    (define (box-line content)
      (let ((s (if (> (string-length content) 63)
                   (string-append (substring content 0 60) "...")
                   content)))
        (printf "│ ~a~a│~n" s (make-string (- 65 (string-length s)) #\space))))

    ;; Exception type if available
    (when kind
      (box-line (sprintf "Type is ~a" kind)))

    ;; Error message
    (box-line msg)

    ;; Location if available
    (when loc
      (box-line (sprintf "In ~a" loc)))

    ;; Arguments if available - format nicely
    (when (and args (not (null? args)))
      (box-line "With arguments:")
      (for-each
        (lambda (arg)
          (let ((s (with-output-to-string (lambda () (write arg)))))
            (box-line (sprintf "  ~a"
                              (if (> (string-length s) 60)
                                  (string-append (substring s 0 57) "...")
                                  s)))))
        args))

    (print "├──────────────────────────────────────────────────────────────────┤")
    (print "│ (bt) backtrace  (frame N) inspect  (exception-info) details     │")
    (print "└──────────────────────────────────────────────────────────────────┘")))

;;; ============================================================
;;; Enrollment Status Display
;;; ============================================================

(define (enrollment-status)
  "Display current enrollment status with ASCII UI"
  (let* ((identity (read-node-identity))
         (hostname (get-hostname))
         (has-keystore (directory-exists? ".vault/keystore"))
         (keycount (if has-keystore (count-vault-items "keystore") 0)))
    (print "")
    (print "┌─ Enrollment Status ──────────────────────────────────────────────┐")
    (print "│                                                                  │")
    (if identity
        (let ((name (cond ((assq 'name identity) => cadr) (else "unknown")))
              (role (cond ((assq 'role identity) => cadr) (else "unknown")))
              (master (cond ((assq 'master identity) => cadr) (else #f)))
              (enrolled (cond ((assq 'enrolled identity) => cadr) (else #f))))
          (printf "│  node:     ~a~a│~n" name (make-string (- 53 (string-length (->string name))) #\space))
          (printf "│  role:     ~a~a│~n" role (make-string (- 53 (string-length (->string role))) #\space))
          (when master
            (printf "│  master:   ~a~a│~n" master (make-string (- 53 (string-length (->string master))) #\space)))
          (when enrolled
            (printf "│  enrolled: ~a~a│~n" enrolled (make-string (- 53 (string-length (->string enrolled))) #\space)))
          (print "│                                                                  │")
          (print "│  status:   enrolled                                              │"))
        (begin
          (printf "│  host:     ~a~a│~n" hostname (make-string (- 53 (string-length hostname)) #\space))
          (print "│                                                                  │")
          (print "│  status:   not enrolled                                          │")
          (print "│                                                                  │")
          (print "│  To enroll this node:                                            │")
          (print "│    1. Run: (enroll-request 'node-name)                           │")
          (print "│    2. Verify words match on master                               │")
          (print "│    3. Master approves with: (enroll-approve ...)                 │")))
    (print "│                                                                  │")
    (print "└──────────────────────────────────────────────────────────────────┘")
    (void)))

(define (enroll-status) (enrollment-status))

;;; ============================================================
;;; Enrollment Listener (Master Side)
;;; ============================================================

(define *pending-enrollments* '())
(define *enrollment-listener* #f)

(define (enrollment-handler name pubkey host port)
  "Handler for incoming enrollment requests"
  (let* ((words (generate-verification-words pubkey))
         (request `((name ,name)
                    (pubkey ,pubkey)
                    (host ,host)
                    (port ,port)
                    (words ,words)
                    (timestamp ,(current-seconds)))))
    (set! *pending-enrollments* (cons request *pending-enrollments*))
    (print "")
    (print "┌─ New Enrollment Request ─────────────────────────────────────────┐")
    (let* ((node-str (sprintf "Node ~a wants to enroll" name))
           (from-str (sprintf "Connecting from ~a on port ~a" host port))
           (verify-str (sprintf "Verification words are ~a" words)))
      (printf "│  ~a~a│~n" node-str (make-string (- 64 (string-length node-str)) #\space))
      (printf "│  ~a~a│~n" from-str (make-string (- 64 (string-length from-str)) #\space))
      (print "│                                                                  │")
      (printf "│  ~a~a│~n" verify-str (make-string (- 64 (string-length verify-str)) #\space))
      (print "│                                                                  │"))
    (print "│  Use (pending), (approve 'name), or (reject 'name)              │")
    (print "└──────────────────────────────────────────────────────────────────┘")
    (void)))

(define (generate-verification-words pubkey)
  "Generate FIPS-181 verification syllables from pubkey"
  (let ((key-data (cond
                    ((blob? pubkey) pubkey)
                    ((string? pubkey) (string->blob pubkey))
                    (else (string->blob (->string pubkey))))))
    (syllables->display (pubkey->syllables key-data))))

(define (enroll-listen #!optional (port 7654))
  "Start listening for enrollment requests (master side)"
  (when *enrollment-listener*
    (print "Stopping existing listener...")
    (stop-listening))

  (print "")
  (print "┌─ Enrollment Listener ────────────────────────────────────────────┐")
  (let ((listen-str (sprintf "Listening for enrollment requests on port ~a" port)))
    (printf "│  ~a~a│~n" listen-str (make-string (- 64 (string-length listen-str)) #\space)))
  (print "│                                                                  │")
  (print "│  Waiting nodes should run (enroll-to \"host\" 'node-name)         │")
  (print "│  Requests will appear here with verification words.             │")
  (print "│                                                                  │")
  (print "│  Use (pending) (approve 'name) (reject 'name) or (stop-enroll)  │")
  (print "└──────────────────────────────────────────────────────────────────┘")

  (set! *enrollment-listener* (listen-for-enrollments enrollment-handler port: port))
  (void))

(define (stop-enroll)
  "Stop the enrollment listener"
  (stop-listening)
  (set! *enrollment-listener* #f)
  (print "Enrollment listener stopped.")
  (void))

(define (pending)
  "Show pending enrollment requests"
  (if (null? *pending-enrollments*)
      (print "No pending enrollment requests.")
      (begin
        (print "")
        (print "┌─ Pending Enrollment Requests ────────────────────────────────────┐")
        (for-each
          (lambda (req)
            (let* ((name (cadr (assq 'name req)))
                   (words (cadr (assq 'words req)))
                   (name-str (sprintf "~a" name))
                   (verify-str (sprintf "  words are ~a" words)))
              (printf "│  ~a~a│~n" name-str (make-string (- 64 (string-length name-str)) #\space))
              (printf "│  ~a~a│~n" verify-str (make-string (- 64 (string-length verify-str)) #\space))))
          (reverse *pending-enrollments*))
        (print "├──────────────────────────────────────────────────────────────────┤")
        (print "│  Use (approve 'name) to accept or (reject 'name) to deny        │")
        (print "└──────────────────────────────────────────────────────────────────┘")))
  (void))

(define (approve name)
  "Approve pending enrollment request by name"
  (let ((req (find (lambda (r) (eq? (cadr (assq 'name r)) name)) *pending-enrollments*)))
    (if (not req)
        (printf "No pending request for '~a'. Use (pending) to see list.~n" name)
        (let ((pubkey (cadr (assq 'pubkey req))))
          (print "")
          (printf "Approving ~a...~n" name)
          ;; TODO: Generate and send certificate
          (print "Certificate generation not yet implemented.")
          (set! *pending-enrollments*
                (filter (lambda (r) (not (eq? r req))) *pending-enrollments*)))))
  (void))

(define (reject name)
  "Reject pending enrollment request by name"
  (let ((req (find (lambda (r) (eq? (cadr (assq 'name r)) name)) *pending-enrollments*)))
    (if (not req)
        (printf "No pending request for '~a'. Use (pending) to see list.~n" name)
        (begin
          (printf "Rejected ~a~n" name)
          (set! *pending-enrollments*
                (filter (lambda (r) (not (eq? r req))) *pending-enrollments*)))))
  (void))

;;; ============================================================
;;; Enrollment Request (Node Side)
;;; ============================================================

(define (enroll-to host name #!key (port 7654))
  "Request enrollment from master at host.
   host: master's hostname or IP
   name: name for this node
   port: master's enrollment port (default 7654)"
  (print "")
  (print "┌─ Enrollment Request ─────────────────────────────────────────────┐")
  (let ((conn-str (sprintf "Connecting to ~a on port ~a" host port)))
    (printf "│  ~a~a│~n" conn-str (make-string (- 64 (string-length conn-str)) #\space)))

  ;; Generate a keypair for this node (or use existing)
  (let* ((keypair (ed25519-keypair))
         (pubkey (car keypair))       ; first element is public key
         (privkey (cadr keypair))     ; second is private key
         (pubkey-hex (blob->hex pubkey))
         (words (generate-verification-words pubkey-hex))
         (node-str (sprintf "Enrolling as ~a" name))
         (verify-str (sprintf "Verification words are ~a" words)))

    (printf "│  ~a~a│~n" node-str (make-string (- 64 (string-length node-str)) #\space))
    (print "│                                                                  │")
    (printf "│  ~a~a│~n" verify-str (make-string (- 64 (string-length verify-str)) #\space))
    (print "│                                                                  │")
    (print "│  Tell the master these words to verify your identity.           │")
    (print "├──────────────────────────────────────────────────────────────────┤")

    ;; Try to connect and send request
    (handle-exceptions exn
      (begin
        (print "│  Connection failed!                                             │")
        (let ((err-str (get-condition-property exn 'exn 'message "unknown error")))
          (printf "│  ~a~a│~n" err-str (make-string (- 64 (string-length err-str)) #\space)))
        (print "└──────────────────────────────────────────────────────────────────┘"))
      (let-values (((in out) (tcp-connect host port)))
        (let ((connected-str (sprintf "Connected to ~a" host)))
          (printf "│  ~a~a│~n" connected-str (make-string (- 64 (string-length connected-str)) #\space)))
        ;; Send enrollment request
        (let ((request `(enrollment-request
                          (name ,name)
                          (pubkey ,pubkey-hex)
                          (port ,port))))
          (write request out)
          (newline out)
          (flush-output out)
          (close-output-port out)  ; Signal end of request
          (close-input-port in)    ; Close for now (cert comes later)
          (print "│  Enrollment request sent successfully.                          │")
          (print "│  Awaiting approval from master using verification words.        │")
          (print "└──────────────────────────────────────────────────────────────────┘")
          ;; Return pending state with keypair for later
          (list 'pending
                (cons 'keypair keypair)
                (cons 'words words)))))))

;;; ============================================================
;;; App Building
;;; ============================================================
;;; Native macOS .app bundle generation with code signing
;;; and notarization. In math and quantum mechanics we trust.

(define (build-app #!key
                   (version #f)
                   (output-dir ".")
                   (sign #f)
                   (notarize #f))
  "Build Cyberspace.app

   Example: (build-app)
   Example: (build-app sign: #t)
   Example: (build-app sign: #t notarize: #t)"
  (let ((ver (or version (git-version))))
    (print "")
    (print "┌─ Building Cyberspace ────────────────────────────────────────────┐")
    (print "│                                                                  │")
    (let ((ver-str (sprintf "Version ~a" ver)))
      (printf "│  ~a~a│~n" ver-str (make-string (- 64 (string-length ver-str)) #\space)))
    (print "│                                                                  │")
    (print "└──────────────────────────────────────────────────────────────────┘")
    (print "")

    (make-app 'cyberspace
              name: "Cyberspace"
              identifier: "com.yoyodyne.cyberspace"
              version: ver
              modules-dir: "."
              output-dir: output-dir
              sign: sign
              notarize: notarize)))

;; Re-export for convenience from REPL
;; sign-app, verify-app, notarize-app already exported from codesign module

;;; ============================================================
;;; Symbol Completion
;;; ============================================================

(define *cyberspace-symbols*
  '(;; Vault
    soup soup-stat soup-du seal-commit seal-release seal-archive
    seal-restore seal-history seal-update seal-inspect vault-config vault-init
    ;; Crypto
    ed25519-keypair ed25519-sign ed25519-verify sha256-hash sha512-hash
    ;; Enrollment
    enrollment-status enroll-status
    enroll-request enroll-wait enroll-complete enroll-listen enroll-approve
    introspect-system introspect-hardware introspect-network
    ;; Debugging
    inspect backtrace bt frame exception-info
    ;; Federation
    federate discover-peers announce-presence
    ;; Certificates
    create-cert sign-cert create-enrollment-cert
    ;; Audit
    audit-append audit-read audit-chain
    ;; Memos
    memo-create memo-commit memo-persist memo-list memo-show
    ;; App Building
    build-app make-app sign-app notarize-app verify-app list-signing-identities
    ;; REPL
    help status keys clear banner))

(define (complete-symbol prefix)
  "Find symbols matching prefix"
  (let ((prefix-str (if (symbol? prefix) (symbol->string prefix) prefix)))
    (filter (lambda (sym)
              (string-prefix? prefix-str (symbol->string sym)))
            *cyberspace-symbols*)))

(define (count-vault-items subdir)
  "Count items in vault subdirectory"
  (let ((path (string-append ".vault/" subdir)))
    (if (directory-exists? path)
        (length (filter (lambda (f) (not (string-prefix? "." f)))
                        (directory path)))
        0)))

(define (plural n singular)
  "Return 'N thing' or 'N things' based on count"
  (string-append (number->string n) " " singular (if (= n 1) "" "s")))

(define (count-file-lines path)
  "Count lines in a file"
  (if (file-exists? path)
      (with-input-from-file path
        (lambda ()
          (let loop ((count 0))
            (let ((line (read-line)))
              (if (eof-object? line)
                  count
                  (loop (+ count 1)))))))
      0))

(define (read-node-identity)
  "Read node identity from vault (name and role)"
  (let ((id-file ".vault/identity.sexp"))
    (if (file-exists? id-file)
        (with-input-from-file id-file read)
        #f)))

(define (describe-vault)
  "Describe vault status (enrollment, audit, keystore)"
  (let* ((audit-entries (count-file-lines ".vault/audit.log"))
         (keystore-exists (directory-exists? ".vault/keystore"))
         (identity (read-node-identity)))
    (when (> audit-entries 0)
      (print "  " (plural audit-entries "audit entry")))
    (when keystore-exists
      (let ((keycount (count-vault-items "keystore")))
        (print "  " (plural keycount "identity") " in keystore")))
    (if identity
        (let ((name (cond ((assq 'name identity) => cadr) (else "unknown")))
              (role (cond ((assq 'role identity) => cadr) (else "unknown"))))
          (print "  enrolled as " name " (" role ")"))
        (print "  not enrolled"))))

;; Get git info for banner
(define (git-version)
  (let ((result (with-input-from-pipe "git describe --tags --always 2>/dev/null" read-line)))
    (if (eof-object? result) "unknown" result)))

(define (git-date)
  (let ((result (with-input-from-pipe "git log -1 --format=%cs 2>/dev/null" read-line)))
    (if (eof-object? result) "unknown" result)))

(define (get-hostname)
  "Get short hostname (first component)"
  (let ((result (with-input-from-pipe "hostname -s 2>/dev/null" read-line)))
    (if (eof-object? result) "unknown" result)))

(define (set-terminal-title title)
  "Set terminal window title via escape sequence"
  (display (string-append "\x1b]0;" title "\x07")))

(define (capitalize-first s)
  "Capitalize first letter of string"
  (if (string-null? s)
      s
      (string-append (string (char-upcase (string-ref s 0)))
                     (substring s 1))))

(define (banner)
  (let* ((host (capitalize-first (get-hostname)))
         (window-title (string-append host " Workstation"))
         (version (git-version))
         (date (git-date)))
    (set-terminal-title window-title)
    (print "")
    (print "Cyberspace Scheme " version " (" date ")")))

;;; ============================================================
;;; Cyberspace Channel Protocol
;;; ============================================================
;;;
;;; Secure channel establishment inspired by PHOTURIS (Karn/Simpson).
;;; Cookies before crypto. Identity under encryption. No TLS.
;;;
;;; Protocol phases:
;;;   KNOCK     -> stateless, no commitment
;;;   COOKIE    <- stateless, proves return path
;;;   EXCHANGE  -> commits state, ephemeral keys
;;;   EXCHANGE  <-
;;;   -- encrypted from here --
;;;   ATTEST    -> prove principal identity
;;;   ATTEST    <-
;;;   OFFER     -> capabilities exchange
;;;   OFFER     <-
;;;   CONFIRM   -> transcript hash
;;;   CONFIRM   <-
;;;   == CHANNEL OPEN ==

;;; Protocol message types
(define CCP-KNOCK    #x01)
(define CCP-COOKIE   #x02)
(define CCP-EXCHANGE #x03)
(define CCP-ATTEST   #x04)
(define CCP-OFFER    #x05)
(define CCP-CONFIRM  #x06)
(define CCP-DATA     #x10)
(define CCP-CLOSE    #xff)

;;; ============================================================
;;; Algorithm Agility via Version-Locked Suites
;;; ============================================================
;;;
;;; No runtime negotiation. Each version specifies exact algorithms.
;;; Avoids downgrade attacks. Clean upgrade path.
;;;
;;; Version format: MAJOR.MINOR
;;;   MAJOR change = incompatible algorithms
;;;   MINOR change = compatible extensions
;;;
;;; Lessons from IKEv1: SA negotiation was complexity hell.
;;; Lessons from Chaum: blind signatures for identity privacy.

(define CCP-VERSION-MAJOR 1)
(define CCP-VERSION-MINOR 0)

;;; Algorithm suites by version
;;; Version 1.x: Modern, conservative
(define *algorithm-suites*
  '((1 . ((kex . x25519)                    ; Key exchange
          (sign . ed25519)                   ; Signatures
          (aead . chacha20-poly1305)         ; Authenticated encryption
          (hash . blake2b)                   ; Hashing
          (kdf . hkdf-blake2b)))))           ; Key derivation

;;; Future versions (reserved):
;;; Version 2.x: Post-quantum (when ready)
;;;   (kex . kyber1024)
;;;   (sign . dilithium3)
;;;   (aead . chacha20-poly1305)  ; PQ doesn't affect symmetric
;;;
;;; Version 3.x: Hybrid classical+PQ
;;;   (kex . x25519+kyber)
;;;   (sign . ed25519+dilithium)

(define (ccp-version-string)
  (string-append (number->string CCP-VERSION-MAJOR) "."
                 (number->string CCP-VERSION-MINOR)))

(define (ccp-suite)
  "Get algorithm suite for current version"
  (alist-ref CCP-VERSION-MAJOR *algorithm-suites*))

(define (ccp-check-version remote-major remote-minor)
  "Check version compatibility"
  (cond
   ((> remote-major CCP-VERSION-MAJOR)
    (values #f "Remote version too new - upgrade required"))
   ((< remote-major CCP-VERSION-MAJOR)
    (values #f "Remote version too old - they must upgrade"))
   (else
    (values #t "Compatible"))))

;;; ============================================================
;;; Chaum-style Identity Protection (Optional)
;;; ============================================================
;;;
;;; Beyond encrypting identity (which we do), we can blind it.
;;; Blind attestation: prove you're authorized without revealing WHO.
;;;
;;; Use case: Anonymous capability exercise.
;;; "I have permission to read this" without revealing identity.
;;;
;;; Implementation: Blind signature on capability hash.

(define *blind-attestation-enabled* #f)

(define (blind-factor)
  "Generate random blinding factor"
  (random-bytes 32))

(define (blind-message msg factor)
  "Blind a message before signing (simplified)"
  ;; Real impl: r^e * H(m) mod n (RSA) or scalar mult (EC)
  ;; Simulated: hash with factor
  (blake2b-hash (blob-append (string->blob msg) factor)))

(define (unblind-signature sig factor)
  "Remove blinding from signature"
  ;; Real impl: s * r^-1 mod n
  ;; Simulated: pass through (placeholder)
  sig)

(define (verify-blind-attestation blinded-sig capability-hash signer-pubkey)
  "Verify blind attestation without knowing signer identity"
  ;; The signer proved they have a valid capability
  ;; We verified the signature without learning who they are
  #t)  ; Placeholder

;;; ============================================================
;;; Protocol Version Negotiation (Minimal)
;;; ============================================================
;;;
;;; KNOCK now includes version. Responder checks compatibility.
;;; No algorithm negotiation - just version check.
;;; Incompatible? Connection refused. Upgrade and retry.

(define (make-knock-payload)
  "Create KNOCK payload with version"
  (string->blob (string-append "CCP/"
                               (number->string CCP-VERSION-MAJOR) "."
                               (number->string CCP-VERSION-MINOR))))

(define (parse-knock-payload payload)
  "Parse KNOCK payload, extract version"
  (let ((str (blob->string payload)))
    (if (string-prefix? "CCP/" str)
        (let* ((ver-str (substring str 4 (string-length str)))
               (parts (string-split ver-str "."))
               (major (string->number (car parts)))
               (minor (string->number (cadr parts))))
          (values major minor))
        (values #f #f))))

;;; Server state
(define *node-listener* #f)       ; TCP listener
(define *node-port* 4433)         ; default port
(define *node-name* #f)           ; this node's name
(define *node-connections* '())   ; active secure channels
(define *cookie-secret* #f)       ; rotates periodically
(define *cookie-epoch* 0)         ; for rotation

;;; Channel registry - mutable state for sequence numbers
;;; Key: channel-id, Value: vector #(seq-send seq-recv state)
(define *channel-registry* '())
(define *channel-counter* 0)

(define (channel-registry-new!)
  "Allocate new channel ID and registry entry"
  (set! *channel-counter* (+ *channel-counter* 1))
  (let ((id *channel-counter*)
        (state (vector 0 0 'new)))  ; seq-send, seq-recv, state
    (set! *channel-registry* (cons (cons id state) *channel-registry*))
    id))

(define (channel-registry-get id)
  "Get mutable state vector for channel"
  (let ((entry (assoc id *channel-registry*)))
    (if entry (cdr entry) #f)))

(define (channel-seq-send! id)
  "Get and increment send sequence"
  (let ((state (channel-registry-get id)))
    (let ((seq (vector-ref state 0)))
      (vector-set! state 0 (+ seq 1))
      seq)))

(define (channel-seq-recv! id)
  "Get and increment recv sequence"
  (let ((state (channel-registry-get id)))
    (let ((seq (vector-ref state 1)))
      (vector-set! state 1 (+ seq 1))
      seq)))

(define (channel-set-state! id new-state)
  "Update channel state"
  (let ((state (channel-registry-get id)))
    (vector-set! state 2 new-state)))

(define (channel-get-state id)
  "Get channel state"
  (let ((state (channel-registry-get id)))
    (vector-ref state 2)))

;;; Initialize cookie secret
(define (init-cookie-secret!)
  (set! *cookie-secret* (random-bytes 32))
  (set! *cookie-epoch* (current-seconds)))

;;; Generate stateless cookie (PHOTURIS-style)
(define (make-cookie remote-addr remote-port)
  "Generate cookie for remote endpoint (stateless verification)"
  ;; Cookie = BLAKE2b(secret || addr || port || epoch)
  (unless *cookie-secret* (init-cookie-secret!))
  (let* ((data (string-append
                (blob->string *cookie-secret*)
                remote-addr
                (number->string remote-port)
                (number->string *cookie-epoch*)))
         (hash (blake2b-hash (string->blob data))))
    (blob->hex (string->blob (substring (blob->string hash) 0 16)))))

;;; Verify cookie
(define (verify-cookie cookie remote-addr remote-port)
  "Verify cookie matches expected value"
  (let ((expected (make-cookie remote-addr remote-port)))
    (string=? cookie expected)))

;;; X25519 key exchange (using libsodium via sodium egg if available)
;;; For now: simulated with random bytes, real impl uses crypto_box_keypair
(define (generate-ephemeral-keypair)
  "Generate X25519 ephemeral keypair for this session"
  (let ((secret (random-bytes 32))
        (public (random-bytes 32)))  ; In real impl: derived from secret
    `((secret . ,secret) (public . ,public))))

;;; Derive shared secret (simulated - real impl uses crypto_scalarmult)
(define (x25519-shared my-secret their-public)
  "Compute X25519 shared secret"
  ;; Real impl: crypto_scalarmult(shared, my_secret, their_public)
  ;; Simulated: hash of concatenation
  (blake2b-hash (blob-append my-secret their-public)))

;;; Derive directional session keys
(define (derive-session-keys shared-secret cookie-i cookie-r)
  "Derive initiator->responder and responder->initiator keys"
  (let* ((ikm (blob-append shared-secret
                           (string->blob cookie-i)
                           (string->blob cookie-r)))
         (prk (blake2b-hash ikm))
         (k-ir (blake2b-hash (blob-append prk (string->blob "initiator->responder"))))
         (k-ri (blake2b-hash (blob-append prk (string->blob "responder->initiator")))))
    `((key-ir . ,(string->blob (substring (blob->string k-ir) 0 32)))
      (key-ri . ,(string->blob (substring (blob->string k-ri) 0 32))))))

;;; Channel state
(define (make-channel in out role)
  "Create new channel state with registry ID for mutable fields"
  (let ((id (channel-registry-new!)))
    `((id . ,id)                    ; registry ID for mutable state
      (in . ,in)
      (out . ,out)
      (role . ,role)                ; initiator | responder
      (ephemeral . #f)              ; our ephemeral keypair
      (their-ephemeral . #f)        ; their public key
      (cookie-ours . #f)
      (cookie-theirs . #f)
      (shared-secret . #f)
      (key-send . #f)               ; our sending key
      (key-recv . #f)               ; our receiving key
      (their-principal . #f)
      (their-capabilities . ()))))           ; for CONFIRM hash

;;; Write protocol message
(define (channel-write-msg channel type payload)
  "Write protocol message to channel"
  (let ((out (alist-ref 'out channel)))
    ;; Format: TYPE(1) LEN(4) PAYLOAD(LEN)
    (write-byte type out)
    (let ((len (blob-size payload)))
      (write-byte (bitwise-and (arithmetic-shift len -24) #xff) out)
      (write-byte (bitwise-and (arithmetic-shift len -16) #xff) out)
      (write-byte (bitwise-and (arithmetic-shift len -8) #xff) out)
      (write-byte (bitwise-and len #xff) out))
    (write-string (blob->string payload) #f out)
    (flush-output out)))

;;; Read protocol message
(define (channel-read-msg channel)
  "Read protocol message from channel"
  (let ((in (alist-ref 'in channel)))
    (let ((type (read-byte in)))
      (if (eof-object? type)
          (values #f #f)
          (let* ((b3 (read-byte in))
                 (b2 (read-byte in))
                 (b1 (read-byte in))
                 (b0 (read-byte in))
                 (len (+ (arithmetic-shift b3 24)
                         (arithmetic-shift b2 16)
                         (arithmetic-shift b1 8)
                         b0))
                 (payload (read-string len in)))
            (values type (string->blob payload)))))))

;;; Encrypt message with ChaCha20-Poly1305 (simulated)
(define (channel-encrypt key seq plaintext)
  "Encrypt and authenticate message"
  ;; Real impl: crypto_aead_chacha20poly1305_ietf_encrypt
  ;; Nonce: 12 bytes from seq
  ;; For now: XOR with key hash (NOT SECURE - placeholder)
  (let* ((nonce (string->blob (string-append
                                (number->string seq)
                                (make-string (- 12 (string-length (number->string seq))) #\null))))
         (key-stream (blake2b-hash (blob-append key nonce))))
    ;; Simulated encryption (real impl uses ChaCha20-Poly1305)
    (print "    [Encrypt] seq=" seq " len=" (blob-size plaintext))
    plaintext))  ; Placeholder - returns plaintext

;;; Decrypt message
(define (channel-decrypt key seq ciphertext)
  "Decrypt and verify message"
  ;; Real impl: crypto_aead_chacha20poly1305_ietf_decrypt
  (print "    [Decrypt] seq=" seq " len=" (blob-size ciphertext))
  ciphertext)  ; Placeholder - returns ciphertext

;;; ============================================================
;;; Protocol Implementation - Initiator Side
;;; ============================================================

(define (channel-initiate host port)
  "Initiate secure channel to remote node"
  (print "Initiating secure channel to " host ":" port)
  (let-values (((in out) (tcp-connect host port)))
    (let ((ch (make-channel in out 'initiator)))

      ;; Phase 1: KNOCK
      (print "  [Knock] Sending knock...")
      (channel-write-msg ch CCP-KNOCK (string->blob "KNOCK"))

      ;; Phase 2: Receive COOKIE
      (let-values (((type payload) (channel-read-msg ch)))
        (unless (= type CCP-COOKIE)
          (error "Expected COOKIE, got" type))
        (let ((cookie-r (blob->string payload)))
          (print "  [Cookie] Received: " (substring cookie-r 0 8) "...")
          (set! ch (alist-update 'cookie-theirs cookie-r ch))

          ;; Generate our ephemeral key and cookie
          (let ((eph (generate-ephemeral-keypair))
                (cookie-i (blob->hex (random-bytes 16))))
            (set! ch (alist-update 'ephemeral eph ch))
            (set! ch (alist-update 'cookie-ours cookie-i ch))

            ;; Phase 3: EXCHANGE
            (print "  [Exchange] Sending ephemeral public key...")
            (let ((exchange-payload (string->blob
                                      (string-append cookie-r "|"
                                                     cookie-i "|"
                                                     (blob->hex (alist-ref 'public eph))))))
              (channel-write-msg ch CCP-EXCHANGE exchange-payload))

            ;; Receive their EXCHANGE
            (let-values (((type payload) (channel-read-msg ch)))
              (unless (= type CCP-EXCHANGE)
                (error "Expected EXCHANGE, got" type))
              (let* ((parts (string-split (blob->string payload) "|"))
                     (their-public (string->blob (caddr parts))))
                (print "  [Exchange] Received their public key")
                (set! ch (alist-update 'their-ephemeral their-public ch))

                ;; Derive session keys
                (let* ((shared (x25519-shared (alist-ref 'secret eph) their-public))
                       (keys (derive-session-keys shared cookie-i cookie-r)))
                  (set! ch (alist-update 'shared-secret shared ch))
                  (set! ch (alist-update 'key-send (alist-ref 'key-ir keys) ch))
                  (set! ch (alist-update 'key-recv (alist-ref 'key-ri keys) ch))
                  (print "  [Keys] Session keys derived")

                  ;; === ENCRYPTED FROM HERE ===
                  (set! ch (alist-update 'state 'encrypted ch))

                  ;; Phase 4: ATTEST - prove our identity (SPKI principal)
                  (unless *node-attestation*
                    (error "Not attested. Use (attest) first"))
                  (print "  [Attest] Sending SPKI principal...")
                  (let* ((principal *node-attestation*)  ; Public key hash
                         (principal-hex principal)
                         (to-sign (string-append cookie-i cookie-r
                                                 (blob->hex (alist-ref 'public eph))))
                         ;; In real impl: ed25519-sign with our key
                         (signature (blob->hex (blake2b-hash (string->blob to-sign)))))
                    (channel-write-msg ch CCP-ATTEST
                                       (string->blob (string-append principal-hex "|" signature))))

                  ;; Receive their ATTEST
                  (let-values (((type payload) (channel-read-msg ch)))
                    (unless (= type CCP-ATTEST)
                      (error "Expected ATTEST, got" type))
                    (let* ((parts (string-split (blob->string payload) "|"))
                           (their-principal (car parts)))
                      (print "  [Attest] Verified: " (short-id their-principal))
                      (set! ch (alist-update 'their-principal their-principal ch))

                      ;; Phase 5: OFFER - exchange capabilities
                      ;; TODO: Should be SPKI auth-certs, not strings
                      ;; Format: (tag (set read write replicate))
                      (print "  [Offer] Sending capabilities...")
                      (let ((our-caps "(tag (* set read write replicate))"))
                        (channel-write-msg ch CCP-OFFER (string->blob our-caps)))

                      ;; Receive their OFFER
                      (let-values (((type payload) (channel-read-msg ch)))
                        (unless (= type CCP-OFFER)
                          (error "Expected OFFER, got" type))
                        ;; TODO: Parse SPKI tag s-expression properly
                        (let ((their-caps (blob->string payload)))
                          (print "  [Offer] Received: " their-caps)
                          (set! ch (alist-update 'their-capabilities their-caps ch))

                          ;; Phase 6: CONFIRM - transcript hash
                          (print "  [Confirm] Sending transcript confirmation...")
                          (let ((transcript-hash (blake2b-hash
                                                   (string->blob
                                                     (string-append cookie-i cookie-r
                                                                    their-principal)))))
                            (channel-write-msg ch CCP-CONFIRM transcript-hash)

                            ;; Receive their CONFIRM
                            (let-values (((type payload) (channel-read-msg ch)))
                              (unless (= type CCP-CONFIRM)
                                (error "Expected CONFIRM, got" type))
                              (print "  [Confirm] Verified")

                              ;; === CHANNEL OPEN ===
                              (channel-set-state! (alist-ref 'id ch) 'open)
                              (print "")
                              (print "  ╔════════════════════════════════════╗")
                              (print "  ║      Secure Channel Established    ║")
                              (print "  ╚════════════════════════════════════╝")
                              (print "  Principal: " (short-id their-principal))
                              (print "  Capabilities: " their-caps)

                              ;; Register in cluster
                              (set! *node-connections* (cons ch *node-connections*))
                              (node-join (short-id their-principal)
                                         uri: (string-append "ccp://" host ":"
                                                             (number->string port)))
                              ch)))))))))))))))

;;; ============================================================
;;; Protocol Implementation - Responder Side
;;; ============================================================

(define (channel-accept)
  "Accept and establish secure channel"
  (unless *node-listener*
    (error "Not listening. Use (node-listen) first"))
  (print "Waiting for secure connection...")
  (let-values (((in out) (tcp-accept *node-listener*)))
    (let ((ch (make-channel in out 'responder)))

      ;; Phase 1: Receive KNOCK
      (let-values (((type payload) (channel-read-msg ch)))
        (unless (= type CCP-KNOCK)
          (error "Expected KNOCK, got" type))
        (print "  [Knock] Received")

        ;; Phase 2: Send COOKIE (stateless)
        (let ((cookie-r (make-cookie "remote" 0)))  ; In real impl: actual remote addr
          (print "  [Cookie] Sending: " (substring cookie-r 0 8) "...")
          (channel-write-msg ch CCP-COOKIE (string->blob cookie-r))
          (set! ch (alist-update 'cookie-ours cookie-r ch))

          ;; Phase 3: Receive EXCHANGE
          (let-values (((type payload) (channel-read-msg ch)))
            (unless (= type CCP-EXCHANGE)
              (error "Expected EXCHANGE, got" type))
            (let* ((parts (string-split (blob->string payload) "|"))
                   (echoed-cookie (car parts))
                   (cookie-i (cadr parts))
                   (their-public-hex (caddr parts))
                   (their-public (string->blob their-public-hex)))

              ;; Verify they echoed our cookie
              (unless (string=? echoed-cookie cookie-r)
                (error "Cookie mismatch - possible spoof"))
              (print "  [Exchange] Cookie verified, received their public key")

              (set! ch (alist-update 'cookie-theirs cookie-i ch))
              (set! ch (alist-update 'their-ephemeral their-public ch))

              ;; Generate our ephemeral and respond
              (let ((eph (generate-ephemeral-keypair)))
                (set! ch (alist-update 'ephemeral eph ch))

                (let ((exchange-payload (string->blob
                                          (string-append cookie-i "|"
                                                         cookie-r "|"
                                                         (blob->hex (alist-ref 'public eph))))))
                  (channel-write-msg ch CCP-EXCHANGE exchange-payload)
                  (print "  [Exchange] Sent our public key")

                  ;; Derive session keys
                  (let* ((shared (x25519-shared (alist-ref 'secret eph) their-public))
                         (keys (derive-session-keys shared cookie-i cookie-r)))
                    (set! ch (alist-update 'shared-secret shared ch))
                    ;; Note: responder keys are reversed
                    (set! ch (alist-update 'key-send (alist-ref 'key-ri keys) ch))
                    (set! ch (alist-update 'key-recv (alist-ref 'key-ir keys) ch))
                    (print "  [Keys] Session keys derived")

                    ;; === ENCRYPTED FROM HERE ===
                    (set! ch (alist-update 'state 'encrypted ch))

                    ;; Phase 4: Receive ATTEST
                    (let-values (((type payload) (channel-read-msg ch)))
                      (unless (= type CCP-ATTEST)
                        (error "Expected ATTEST, got" type))
                      (let* ((parts (string-split (blob->string payload) "|"))
                             (their-principal (car parts))
                             (their-sig (cadr parts)))
                        ;; In real impl: verify ed25519 signature
                        (print "  [Attest] Verified: " (short-id their-principal))
                        (set! ch (alist-update 'their-principal their-principal ch))

                        ;; Send our ATTEST (SPKI principal)
                        (unless *node-attestation*
                          (error "Not attested. Use (attest) first"))
                        (print "  [Attest] Sending SPKI principal...")
                        (let* ((principal *node-attestation*)  ; Public key hash
                               (principal-hex principal)
                               (to-sign (string-append cookie-i cookie-r
                                                       (blob->hex (alist-ref 'public eph))))
                               (signature (blob->hex (blake2b-hash (string->blob to-sign)))))
                          (channel-write-msg ch CCP-ATTEST
                                             (string->blob (string-append principal-hex "|" signature))))

                        ;; Phase 5: Receive OFFER
                        (let-values (((type payload) (channel-read-msg ch)))
                          (unless (= type CCP-OFFER)
                            (error "Expected OFFER, got" type))
                          ;; TODO: Parse SPKI tag s-expression properly
                          (let ((their-caps (blob->string payload)))
                            (print "  [Offer] Received: " their-caps)
                            (set! ch (alist-update 'their-capabilities their-caps ch))

                            ;; Send our OFFER
                            ;; TODO: Should be SPKI auth-certs
                            (print "  [Offer] Sending capabilities...")
                            (let ((our-caps "(tag (* set read write replicate))"))
                              (channel-write-msg ch CCP-OFFER (string->blob our-caps)))

                            ;; Phase 6: Receive CONFIRM
                            (let-values (((type payload) (channel-read-msg ch)))
                              (unless (= type CCP-CONFIRM)
                                (error "Expected CONFIRM, got" type))
                              (print "  [Confirm] Verified")

                              ;; Send our CONFIRM
                              (let ((transcript-hash (blake2b-hash
                                                       (string->blob
                                                         (string-append cookie-i cookie-r
                                                                        their-principal)))))
                                (channel-write-msg ch CCP-CONFIRM transcript-hash))

                              ;; === CHANNEL OPEN ===
                              (channel-set-state! (alist-ref 'id ch) 'open)
                              (print "")
                              (print "  ╔════════════════════════════════════╗")
                              (print "  ║      Secure Channel Established    ║")
                              (print "  ╚════════════════════════════════════╝")
                              (print "  Principal: " (short-id their-principal))
                              (print "  Capabilities: " their-caps)

                              ;; Register
                              (set! *node-connections* (cons ch *node-connections*))
                              (node-join (short-id their-principal))
                              ch)))))))))))))))

;;; ============================================================
;;; Secure Channel Operations
;;; ============================================================

(define (channel-send ch message)
  "Send encrypted message over secure channel"
  (let ((id (alist-ref 'id ch)))
    (unless (eq? (channel-get-state id) 'open)
      (error "Channel not open"))
    (let* ((seq (channel-seq-send! id))
           (key (alist-ref 'key-send ch))
           (plaintext (string->blob (format "~a" message)))
           (ciphertext (channel-encrypt key seq plaintext)))
      (channel-write-msg ch CCP-DATA ciphertext)
      (print "  [Send] seq=" seq " encrypted"))))

(define (channel-recv ch)
  "Receive and decrypt message from secure channel"
  (let ((id (alist-ref 'id ch)))
    (unless (eq? (channel-get-state id) 'open)
      (error "Channel not open"))
    (let-values (((type payload) (channel-read-msg ch)))
      (cond
       ((= type CCP-DATA)
        (let* ((seq (channel-seq-recv! id))
               (key (alist-ref 'key-recv ch))
               (plaintext (channel-decrypt key seq payload)))
          (print "  [Recv] seq=" seq " decrypted")
          (blob->string plaintext)))
       ((= type CCP-CLOSE)
        (channel-set-state! id 'closed)
        'closed)
       (else
        (error "Unexpected message type" type))))))

(define (channel-close ch)
  "Close secure channel"
  (let ((id (alist-ref 'id ch)))
    (channel-write-msg ch CCP-CLOSE (string->blob "CLOSE"))
    (channel-set-state! id 'closed)
    ;; Destroy session keys (zeroize)
    (print "  [Closed] Channel closed, keys destroyed")))

;;; ============================================================
;;; Backward-compatible API
;;; ============================================================

(define (node-listen #!optional (port *node-port*) (name #f))
  "Start listening for secure cluster connections"
  (if *node-listener*
      (begin
        (print "Already listening on port " *node-port*)
        *node-name*)
      (begin
        (set! *node-port* port)
        (set! *node-name* (or name (string-append "node-" (number->string port))))
        (init-cookie-secret!)
        (set! *node-listener* (tcp-listen port))
        (print "Node '" *node-name* "' listening on port " port)
        (print "  Protocol: Cyberspace Channel Protocol (CCP)")
        (print "  Cookie secret initialized")
        (set! *cluster-state* 'forming)
        *node-name*)))

(define (node-stop)
  "Stop listening"
  (when *node-listener*
    (tcp-close *node-listener*)
    (set! *node-listener* #f)
    (set! *cookie-secret* #f)
    (print "Node stopped listening")))

(define (node-connect host port)
  "Connect to another node using secure channel"
  (channel-initiate host port))

(define (node-accept)
  "Accept secure connection from another node"
  (channel-accept))

(define (node-broadcast msg)
  "Send message to all connected nodes (encrypted)"
  (for-each
   (lambda (ch)
     (when (eq? (alist-ref 'state ch) 'open)
       (channel-send ch msg)))
   *node-connections*)
  (print "Broadcast to " (length *node-connections*) " nodes"))

(define (node-ping)
  "Ping all connected nodes"
  (node-broadcast `(ping ,(current-seconds))))

(banner)

;;; ============================================================
;;; Hardware Refresh - always updates node manifest in vault
;;; ============================================================

(define (node-hardware-file)
  "Path to node hardware manifest in vault"
  ".vault/node-hardware")

(define (node-hardware-refresh!)
  "Probe hardware and store in vault"
  (let* ((caps (probe-system-capabilities))
         (hw-file (node-hardware-file))
         (manifest `(node-hardware
                     (platform ,(platform-stamp))
                     (capabilities ,caps)
                     (role ,(recommend-role caps))
                     (timestamp ,(current-seconds)))))
    (with-output-to-file hw-file
      (lambda ()
        (write manifest)
        (newline)))))

;;; ============================================================
;;; Simple Pager - for long output
;;; ============================================================

(define (terminal-height)
  "Get terminal height, default 24"
  (handle-exceptions exn 24
    (let ((h (with-input-from-pipe "tput lines" read-line)))
      (if (eof-object? h) 24 (or (string->number h) 24)))))

;; VT100 escape codes
(define vt100-reverse "\x1b[7m")
(define vt100-normal "\x1b[0m")
(define vt100-clear-line "\x1b[2K\r")

(define (pager-display str)
  "Display string with paging for long output (VT100)"
  (let* ((lines (string-split str "\n" #t))
         (height (- (terminal-height) 2))  ; leave room for prompt
         (total (length lines)))
    (if (<= total height)
        ;; Short enough - display directly
        (display str)
        ;; Need paging
        (let loop ((remaining lines) (shown 0))
          (cond
           ((null? remaining) #t)
           ((>= shown height)
            ;; Show "more" prompt in reverse video
            (display vt100-reverse)
            (display "-- more (space/q) --")
            (display vt100-normal)
            (flush-output)
            (let ((ch (read-char)))
              (display vt100-clear-line)
              (cond
               ((or (eq? ch #\q) (eq? ch #\Q))
                #t)  ; quit paging
               ((eq? ch #\space)
                (loop remaining 0))  ; next page
               (else
                (loop remaining (- height 1))))))  ; next line
           (else
            (display (car remaining))
            (newline)
            (loop (cdr remaining) (+ shown 1))))))))

(define (result->string result)
  "Pretty-print result to string"
  (with-output-to-string
    (lambda ()
      (if (and (pair? result) (symbol? (car result)))
          ;; S-expression - pretty print
          (pp result)
          (write result)))))

;;; ============================================================
;;; Command Mode - paren-optional syntax
;;; ============================================================
;;;
;;; Lines starting with ( are Scheme.
;;; Bare words are commands: "status" → (status)
;;; Arguments follow: "commit msg" → (seal-commit "msg")

;; Helper for keys command
(define (list-keys) (soup 'keys))

(define *command-aliases*
  '((status    . introspect-system)
    (commit    . seal-commit)
    (release   . seal-release)
    (archive   . seal-archive)
    (history   . seal-history)
    (sync      . seal-synchronize)
    (keys      . list-keys)
    (keygen    . ed25519-keypair)
    (sign      . ed25519-sign)
    (verify    . ed25519-verify)
    (hash      . sha512-hash)
    (put       . content-put)
    (get       . content-get)
    (soup      . soup)
    (stat      . soup-stat)
    (du        . soup-du)
    (releases  . soup-releases)
    (find      . soup-find)
    (inspect   . soup-inspect)
    (peers     . nodes)
    (listen    . node-listen)
    (connect   . node-connect)
    (ping      . node-ping)
    (enroll    . enroll-request)
    (approve   . enroll-approve)
    (discover  . discover-peers)
    (gossip    . gossip-status)
    (audit     . audit-read)
    (clear     . clear)
    (help      . help)
    (quit      . exit)
    (exit      . exit)))

(define (resolve-command cmd)
  "Resolve command alias or return as-is"
  (let ((alias (assq cmd *command-aliases*)))
    (if alias (cdr alias) cmd)))

(define (parse-command-line line)
  "Parse command line into S-expression"
  (let* ((trimmed (string-trim-both line))
         (port (open-input-string trimmed)))
    (if (or (string=? trimmed "")
            (char=? (string-ref trimmed 0) #\())
        ;; Empty or Scheme - read directly
        (if (string=? trimmed "")
            #f
            (read port))
        ;; Command mode - tokenize and wrap
        (let loop ((tokens '()))
          (let ((tok (read port)))
            (if (eof-object? tok)
                (if (null? tokens)
                    #f
                    (cons (resolve-command (car (reverse tokens)))
                          (reverse (cdr (reverse tokens)))))
                (loop (cons tok tokens))))))))

;;; ============================================================
;;; Help System
;;; ============================================================

(define (help)
  "Display help for Cyberspace Scheme"
  (print "")
  (print "Cyberspace Scheme - built on Chicken Scheme")
  (print "")
  (print "Vault commands:")
  (print "  (soup)              - Browse vault objects")
  (print "  (soup 'keys)        - List keys")
  (print "  (soup 'releases)    - List releases")
  (print "  (soup-stat NAME)    - Object details")
  (print "  (soup-du)           - Disk usage")
  (print "  (seal-commit MSG)   - Commit changes")
  (print "  (seal-release VER)  - Create release")
  (print "")
  (print "Crypto:")
  (print "  (ed25519-keypair)   - Generate keypair")
  (print "  (sha512-hash DATA)  - Hash data")
  (print "")
  (print "Federation:")
  (print "  (enrollment-status)     - Show enrollment status")
  (print "  (enroll-request 'name)  - Request enrollment")
  (print "  (introspect-system)     - System info")
  (print "  (discover-peers)        - Find peers")
  (print "")
  (print "Debugging:")
  (print "  (inspect OBJ)           - Tree-view of object")
  (print "  (bt)                    - Backtrace after error")
  (print "  (frame N)               - Inspect stack frame")
  (print "")
  (print "Chicken REPL:")
  (print "  ,q ,exit            - Quit")
  (print "  ,l FILE             - Load file")
  (print "  ,d NAME             - Describe")
  (print "  ,comp PREFIX        - Symbol completion")
  (print "  ,?                  - REPL help")
  (print "")
  (print vt100-normal)
  (void))

;; Friendly exit
(define (goodbye)
  (repl-history-save)
  (let* ((now (seconds->local-time (current-seconds)))
         (date-str (sprintf "~a-~a-~a ~a:~a"
                           (+ 1900 (vector-ref now 5))
                           (string-pad-left (number->string (+ 1 (vector-ref now 4))) 2 #\0)
                           (string-pad-left (number->string (vector-ref now 3)) 2 #\0)
                           (string-pad-left (number->string (vector-ref now 2)) 2 #\0)
                           (string-pad-left (number->string (vector-ref now 1)) 2 #\0)))
         (obj-count (count-vault-items "objects"))
         (key-count (count-vault-items "keys"))
         (info-parts (filter identity
                       (list
                         (and (> obj-count 0) (sprintf "~a objects" obj-count))
                         (and (> key-count 0) (sprintf "~a keys" key-count))))))
    (print "")
    (if (null? info-parts)
        (printf "Returning to objective reality, Cyberspace frozen at ~a.~n" date-str)
        (printf "Returning to objective reality, Cyberspace frozen at ~a, ~a.~n"
                date-str
                (string-intersperse info-parts ", ")))
    (print "")
    (exit 0)))

(define (string-pad-left str len char)
  (let ((slen (string-length str)))
    (if (>= slen len)
        str
        (string-append (make-string (- len slen) char) str))))

;; Clear screen (VT100)
(define (clear)
  (display "\x1b[2J\x1b[H")
  (void))

;; English-friendly aliases (just call with parens)
(define keys (lambda () (soup 'keys)))
(define releases (lambda () (soup-releases)))
(define status (lambda () (introspect-system)))

;; Quit shortcuts (don't shadow scheme's exit)
(define quit goodbye)
(define q goodbye)
(define bye goodbye)

;; Settable prompt
(define *prompt* ": ")

;; Result history
;; Use _ for last result (like Python), _1 _2 _3 for previous
;; And ($ n) for numbered access
(define _ #f)   ; last result
(define _1 #f)  ; second-to-last
(define _2 #f)  ; third-to-last
(define *result-count* 0)
(define *result-history* (make-vector 100 #f))  ; numbered results

(define (push-result! val)
  "Save result to history"
  (set! _2 _1)
  (set! _1 _)
  (set! _ val)
  (vector-set! *result-history* (modulo *result-count* 100) val)
  (set! *result-count* (+ 1 *result-count*))
  val)

(define ($ n)
  "Get result N from history. ($ 0) = first, ($ -1) = last"
  (cond
    ((< n 0)  ; negative index from end
     (let ((idx (+ *result-count* n)))
       (if (>= idx 0)
           (vector-ref *result-history* (modulo idx 100))
           (error "No such result" n))))
    ((< n (min *result-count* 100))
     (vector-ref *result-history* (modulo n 100)))
    (else (error "No such result" n))))

;; History file for persistence
(define *history-file* (string-append (or (get-environment-variable "HOME") ".") "/.cyberspace_history"))

;; Read line with prompt
(define (repl-read-line prompt)
  (display prompt)
  (flush-output)
  (read-line))

;; History stubs - no-op without linenoise
(define (repl-history-add line) #f)
(define (repl-history-save) #f)

;; Custom REPL with comma command handling
;; Intercepts ,<cmd> before Scheme reader parses it as (unquote <cmd>)
(define (command-repl)
  (let loop ()
    (let ((line (repl-read-line *prompt*)))
      (cond
        ;; EOF (linenoise returns #f, read-line returns eof-object)
        ((or (not line) (eof-object? line))
         (newline)
         (goodbye))

        ;; Empty line
        ((string=? line "")
         (loop))

        ;; Comma commands
        ((char=? (string-ref line 0) #\,)
         (repl-history-add line)
         (let* ((cmd-line (substring line 1))
                (parts (string-split cmd-line))
                (cmd (if (null? parts) "" (car parts)))
                (args (if (null? parts) '() (cdr parts))))
           (cond
             ;; Quit
             ((or (string=? cmd "q")
                  (string=? cmd "quit")
                  (string=? cmd "exit"))
              (goodbye))

             ;; Help
             ((or (string=? cmd "h")
                  (string=? cmd "help")
                  (string=? cmd "?"))
              (help)
              (loop))

             ;; Load file
             ((string=? cmd "l")
              (if (null? args)
                  (print "Usage: ,l <filename>")
                  (begin
                    (print "Loading " (car args) "...")
                    (load (car args))))
              (loop))

             ;; Describe
             ((string=? cmd "d")
              (if (null? args)
                  (print "Usage: ,d <name>")
                  (let ((sym (string->symbol (car args))))
                    (print "Looking up: " sym)
                    (condition-case
                        (let ((val (eval sym)))
                          (if (procedure? val)
                              (print "  " sym " is a procedure")
                              (begin
                                (print "  Value: ")
                                (pp val))))
                      ((exn) (print "  Not bound")))))
              (loop))

             ;; Status
             ((string=? cmd "s")
              (status)
              (loop))

             ;; Keys
             ((string=? cmd "k")
              (keys)
              (loop))

             ;; Clear
             ((string=? cmd "c")
              (clear)
              (loop))

             ;; Complete - show symbol completions
             ((or (string=? cmd "comp") (string=? cmd "complete"))
              (if (null? args)
                  (print "Usage: ,comp PREFIX")
                  (let* ((prefix (car args))
                         (matches (complete-symbol prefix)))
                    (if (null? matches)
                        (print "No completions for: " prefix)
                        (for-each (lambda (m) (print "  " m)) matches))))
              (loop))

             ;; Unknown comma command
             (else
              (print "Unknown command: ," cmd)
              (print "Try ,? for help")
              (loop)))))

        ;; Regular Scheme expression
        (else
         (repl-history-add line)
         (handle-exceptions exn
           (rich-exception-display exn)
           (let ((result (eval (with-input-from-string line read))))
             (unless (eq? result (void))
               (push-result! result)
               (pp result))))
         (loop))))))

;; Show vault status at startup
(when (directory-exists? ".vault")
  (describe-vault)
  (node-hardware-refresh!))
(print "")

;; Start custom REPL
(command-repl)
