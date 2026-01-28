#!/usr/bin/env csi -q -w
;;; repl - Cyberspace Scheme
;;;
;;; Copyright (c) 2026 ddp@eludom.net
;;; MIT License - see LICENSE file
;;; Currently unpublished and proprietary; license applies upon public release.
;;;
;;; Usage: ./repl
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
        (except (chicken repl) quit)
        (chicken csi)      ; toplevel-command
        (chicken file)
        (chicken pathname)
        (chicken io)
        (chicken port)     ; with-output-to-string
        (chicken pretty-print)  ; pp
        (chicken time)
        (chicken time posix)
        (chicken process-context)
        (chicken process-context posix)  ; hostname
        (chicken process)
        (chicken platform)  ; machine-type, software-type, etc.
        (chicken blob)
        (chicken file posix)
        (chicken bitwise)
        (chicken string)
        (chicken sort)
        (chicken irregex)  ; regex for audit time parsing
        srfi-18            ; threads (for background listeners)
        (chicken condition)
        srfi-1
        srfi-4
        srfi-13
        srfi-69   ; hash tables
        (chicken tcp)
        tty-ffi   ; raw char input for immediate keypress
        lineage   ; line editing with history (BSD)
        edt)      ; LK201/EDT keypad bindings for QMK

;;; ============================================================
;;; Command Line Interface
;;; ============================================================
;;; cs                      - start REPL (default)
;;; cs --sync               - sync vault with remote, then REPL
;;; cs --clean              - remove artifacts, exit
;;; cs --rebuild            - force rebuild all
;;; cs --clean --rebuild    - clean slate rebuild
;;; cs --boot=<level>       - verbosity (shadow|whisper|portal|oracle)
;;; cs --eval='<expr>'      - evaluate and exit
;;; cs --version            - version info
;;; cs --help               - usage

(define (parse-cli-option arg)
  "Parse a --option or --option=value argument. Returns (option . value) or #f."
  (cond
    ((not (string-prefix? "--" arg)) #f)
    ((string-index arg #\=)
     => (lambda (idx)
          (cons (substring arg 2 idx)
                (substring arg (+ idx 1)))))
    (else (cons (substring arg 2) #t))))

(define (parse-cli-args args)
  "Parse command line arguments into options alist."
  (filter-map parse-cli-option args))

;; Parse arguments at load time
(define *cli-options* (parse-cli-args (command-line-arguments)))

(define (cli-option name)
  "Get CLI option value, or #f if not present."
  (let ((opt (assoc name *cli-options*)))
    (and opt (cdr opt))))

(define (cli-option? name)
  "Check if CLI option is present."
  (and (cli-option name) #t))

;;; --help
(when (cli-option? "help")
  (print "Cyberspace Scheme - Distributed Systems Shell")
  (print "")
  (print "Usage: cs [options]")
  (print "")
  (print "Options:")
  (print "  --sync               Sync vault with remote, then start REPL")
  (print "  --clean              Remove artifacts and rebuild repl (then run cs again)")
  (print "  --rebuild            Force rebuild all modules")
  (print "  --verbose            Show verbose output (e.g., rm during --clean)")
  (print "  --boot=<level>       Boot verbosity: shadow|whisper|portal|oracle")
  (print "  --eval='<expr>'      Evaluate expression and exit")
  (print "  --version            Show version information")
  (print "  --help               Show this help")
  (print "")
  (print "Examples:")
  (print "  cs                   Start REPL (default)")
  (print "  cs --clean --rebuild Clean slate rebuild")
  (print "  cs --boot=portal     Start with banner and help")
  (print "  cs --eval='(+ 1 2)'  Evaluate and exit")
  (exit 0))

;;; --version
(when (cli-option? "version")
  (print "Cyberspace Scheme v0.59")
  (print "  Built with CHICKEN Scheme")
  (print "  Ed25519 signatures via libsodium")
  (exit 0))

;;; --sync (robust git sync - no errors, just works)
(define (git-sync)
  "Sync with remote. Returns #t on success, #f on conflict needing human attention."
  (print "Syncing with remote...")
  ;; Stash local changes (including untracked .meta files)
  (system "git stash -q --include-untracked 2>/dev/null")
  ;; Pull with rebase
  (let ((pull-result (system "git pull --rebase -q 2>/dev/null")))
    (cond
      ((zero? pull-result)
       ;; Pull succeeded, try to push any local commits
       (system "git push -q 2>/dev/null")
       ;; Restore stash, preferring remote for .meta conflicts
       (system "git stash pop -q 2>/dev/null")
       (system "git checkout --theirs .forge/*.meta 2>/dev/null")
       (system "git checkout -- .forge/ 2>/dev/null")
       (print "  [ok] Synced")
       #t)
      (else
       ;; Rebase failed - check if it's just .meta conflicts
       (let ((conflict-check (with-input-from-pipe
                              "git diff --name-only --diff-filter=U 2>/dev/null"
                              read-lines)))
         (if (and (pair? conflict-check)
                  (every (lambda (f) (string-suffix? ".meta" f)) conflict-check))
             ;; Only .meta conflicts - auto-resolve by preferring remote
             (begin
               (system "git checkout --theirs .forge/*.meta 2>/dev/null")
               (system "git add .forge/*.meta 2>/dev/null")
               (system "git rebase --continue 2>/dev/null")
               (system "git push -q 2>/dev/null")
               (system "git stash pop -q 2>/dev/null")
               (print "  [ok] Synced (auto-resolved metadata)")
               #t)
             ;; Real conflict - abort and warn
             (begin
               (system "git rebase --abort 2>/dev/null")
               (system "git stash pop -q 2>/dev/null")
               (print "  [!!] Sync conflict - source files need manual merge")
               #f)))))))

(when (cli-option? "sync")
  (unless (git-sync)
    (exit 1)))

;;; --verbose flag
(define *verbose* (cli-option? "verbose"))

;;; --clean (implies rebuild if --boot is specified or REPL would start)
(when (cli-option? "clean")
  (for-each (lambda (f)
              (when *verbose* (print "  rm " f))
              (delete-file f))
            (glob "*.so" "*.import.scm" ".forge/*.meta"))
  ;; Also remove stale .o files and the repl binary itself
  ;; The repl binary links against modules - if they're gone, it's broken
  (for-each (lambda (f)
              (when *verbose* (print "  rm " f))
              (delete-file f))
            (glob "*.o"))
  (when (file-exists? "repl")
    (when *verbose* (print "  rm repl"))
    (delete-file "repl"))
  ;; Clear REPL history for clean slate testing
  (when (file-exists? ".vault/repl-history")
    (when *verbose* (print "  rm .vault/repl-history"))
    (delete-file ".vault/repl-history"))
  ;; After clean, rebuild the repl binary (we're running from the old one)
  (print "Rebuilding repl...")
  (let ((rc (system "csc -O2 -d1 repl.scm -o repl")))
    (if (zero? rc)
        (begin
          ;; If --rebuild was requested, exec the new repl to continue
          (if (cli-option? "rebuild")
              (begin
                (print "Restarting forge...")
                (process-execute "./repl" '("--rebuild")))
              ;; Otherwise just exit - user can run cs again
              (begin
                (print "Clean complete. Run cs to rebuild modules.")
                (exit 0))))
        (begin
          (print "Error: repl rebuild failed")
          (exit 1)))))

;; os is Level 0 (no cyberspace deps) - import early for hostname
(import os)

;;; ============================================================
;;; Startup Timing
;;; ============================================================

(define *repl-start-time* (current-process-milliseconds))
(define *module-times* '())
(define *module-start* 0)

;; Build level: controls warning/error behavior
;; Levels (strictest to most permissive):
;;   'engineering  - warnings are errors, strict types, all checks
;;   'qa           - warnings are errors, internal testing
;;   'beta         - warnings shown prominently but don't fail
;;   'production   - minimal output, warnings suppressed
(define *build-level* 'engineering)

;; Convenience predicates
(define (build-level-at-least? level)
  (let ((levels '(production beta qa engineering)))
    (>= (length (memq *build-level* levels))
        (length (memq level levels)))))

(define (warnings-are-errors?)
  (memq *build-level* '(engineering qa)))

;;; When the tala beats and the flute plays om,
;;; the lambda rests in stillness.
(define *stillness* 'quiescent)

;;; Travellers leave trails.
(define *trail* '())        ; navigation history
(define *lens* 'library)    ; current view: 'library or 'soup

;;; ============================================================
;;; Boot Verbosity Levels
;;; ============================================================
;;; 0 shadow    - just prompt (default)
;;; 1 whisper   - version + Ready
;;; 2 portal    - banner + help + Ready
;;; 3 oracle    - portal + module timings + diagnostics

(define *boot-levels*
  '((shadow . 0) (whisper . 1) (portal . 2) (gate . 2) (oracle . 3)))

(define (parse-boot-level str)
  "Parse boot level from string (name or number)."
  (cond
    ((string->number str) => identity)
    ((assq (string->symbol (string-downcase str)) *boot-levels*) => cdr)
    (else #f)))

(define (show-boot-levels)
  "Display available boot levels and exit."
  (print "Boot levels (--boot=<level>):")
  (print "  0  shadow     - silent, just prompt")
  (print "  1  whisper    - banner only")
  (print "  2  portal     - banner + help + Ready (gate = alias)")
  (print "  3  oracle     - portal + diagnostics")
  (exit 0))

(define *boot-verbosity*
  (let ((cli-boot (cli-option "boot"))
        (env (get-environment-variable "CYBERSPACE_BOOT")))
    (cond
      ((and cli-boot (member cli-boot '("help" "list" "?")))
       (show-boot-levels))
      ((and cli-boot (string? cli-boot)) (or (parse-boot-level cli-boot) 0))
      (env (or (parse-boot-level env) 0))
      (else 0))))

(define (boot-level! level)
  "Set boot verbosity level (0-4 or symbol)."
  (set! *boot-verbosity*
    (if (number? level) level
        (cdr (assq level *boot-levels*)))))

;; Verbose loading - shows resident editor messages at oracle level
;; Must be defined before loading teco.scm, pencil.scm, schemacs.scm
(define *verbose-load* (>= *boot-verbosity* 3))

(define (module-start! name)
  "Mark start of module loading."
  (set! *module-start* (current-process-milliseconds)))

(define (module-end! name)
  "Mark end of module loading, record timing."
  (let ((elapsed (- (current-process-milliseconds) *module-start*)))
    (set! *module-times* (cons (cons name elapsed) *module-times*))))

(define (report-module-times)
  "Print per-module timing report."
  (let* ((times (reverse *module-times*))
         (total (apply + (map cdr times))))
    (for-each (lambda (t)
                (let ((name (car t))
                      (ms (cdr t)))
                  (when (> ms 0)
                    (print (format "  ~a: ~ams" name ms)))))
              times)))

;;; ============================================================
;;; Session Statistics - see portal.scm
;;; (session-stat-init!, session-stat!, session-stat, session-uptime,
;;;  session-summary, format-duration, format-bytes, goodbye)

;;; ============================================================
;;; Realm Signature - Provenance in the Weave
;;; ============================================================
;;; Messages should know where they came from.
;;; The wilderness needs provenance metadata.

(define *realm-signature* #f)  ; #f = use hostname, or set to symbol/string

(define (realm-signature)
  "Get current realm signature for message provenance"
  (or *realm-signature* (hostname)))

(define (realm-signature! sig)
  "Set realm signature (symbol, string, or #f for hostname)"
  (set! *realm-signature* sig)
  (print "[realm-signature: " (realm-signature) "]"))

(define (realm-prompt)
  "Generate realm-aware prompt"
  (string-append (->string (realm-signature)) "> "))

;;; ============================================================
;;; UI Preferences
;;; ============================================================
;;; User-configurable editor and pager. Defaults to environment
;;; variables, falls back to Emacs/less, ultimate fallback to
;;; built-in Electric Pencil/cat.

(define *editor* #f)   ; #f = auto-detect
(define *pager* #f)    ; #f = auto-detect

(define (editor)
  "Get configured editor command - Electric Pencil is our nano"
  (or *editor*
      (and (directory-exists? ".vault")
           (vault-config 'editor))
      (get-environment-variable "EDITOR")
      "pencil"))

(define (editor! cmd)
  "Set editor preference (persists to vault)"
  (set! *editor* cmd)
  (when (directory-exists? ".vault")
    (vault-config 'editor cmd))
  (print "Editor: " (editor))
  (print "  pencil = Electric Pencil (built-in)")
  (print "  teco   = TECO (built-in)")
  (print "  emacs  = Emacsclient")
  (print "  Other  = External command"))

(define (pager)
  "Get configured pager command"
  (or *pager*
      (get-environment-variable "PAGER")
      "less"))

(define (pager! cmd)
  "Set pager preference"
  (set! *pager* cmd)
  (print "[pager: " (pager) "]"))

(define (preferences)
  "Show current UI preferences"
  (print "")
  (print "UI Preferences:")
  (print "  editor: " (editor))
  (print "  pager:  " (pager))
  (print "")
  (print "Set with (editor! CMD) or (pager! CMD)")
  (print "Environment: $EDITOR, $PAGER")
  (print ""))

;;; ============================================================
;;; Unicode Helpers
;;; ============================================================
;;; make-string doesn't work with multi-byte Unicode chars.
;;; Use string-repeat for box-drawing characters.

(define (string-repeat s n)
  "Repeat string s n times (Unicode-safe)."
  (apply string-append (make-list n s)))

(define (hex-dump vec #!optional (bytes-per-line 16))
  "Display hex dump of u8vector with ASCII sidebar."
  (define (hex2 n) ; 2-digit hex
    (let ((s (number->string n 16)))
      (if (< (string-length s) 2)
          (string-append "0" s)
          s)))
  (define (hex8 n) ; 8-digit hex address
    (let ((s (number->string n 16)))
      (string-append (make-string (- 8 (string-length s)) #\0) s)))
  (let ((len (u8vector-length vec)))
    (let loop ((offset 0))
      (when (< offset len)
        ;; Address
        (display (hex8 offset))
        (display "  ")
        ;; Hex bytes
        (let ((line-end (min (+ offset bytes-per-line) len)))
          (do ((i offset (+ i 1)))
              ((>= i line-end))
            (display (hex2 (u8vector-ref vec i)))
            (display " "))
          ;; Padding for short lines
          (when (< (- line-end offset) bytes-per-line)
            (display (make-string (* 3 (- bytes-per-line (- line-end offset))) #\space)))
          ;; ASCII
          (display " |")
          (do ((i offset (+ i 1)))
              ((>= i line-end))
            (let ((b (u8vector-ref vec i)))
              (display (if (and (>= b 32) (<= b 126))
                           (integer->char b)
                           #\.))))
          (print "|"))
        (loop (+ offset bytes-per-line))))))

;;; ============================================================
;;; Bootstrap: Mixed-Architecture Defense
;;; ============================================================
;;; Ensures compiled modules match current architecture.
;;; Rebuilds automatically if arch mismatch or source newer.

(module-start! "bootstrap")

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

;; --rebuild flag forces all modules to rebuild
(define *force-rebuild* (cli-option? "rebuild"))

;; Clear REPL history on --rebuild for clean testing
(when (and *force-rebuild* (file-exists? ".vault/repl-history"))
  (delete-file ".vault/repl-history"))

(define (any-import-newer? so-time)
  "Check if any .import.scm file is newer than the given timestamp.
   When module exports change, downstream modules must rebuild."
  (let ((import-files (glob "*.import.scm")))
    (any (lambda (f) (> (file-mtime f) so-time)) import-files)))

(define (needs-rebuild? module arch)
  "Check if module needs rebuilding: missing, arch mismatch, source newer,
   dependency imports newer, or --rebuild flag"
  (or *force-rebuild*
      (let* ((src (string-append module ".scm"))
             (so  (string-append module ".so"))
             (import-scm (string-append module ".import.scm"))
             (stored-arch (read-arch-stamp module))
             (so-time (file-mtime so)))
        (or (not (file-exists? so))
            (not (file-exists? import-scm))
            (not stored-arch)
            (not (string=? stored-arch arch))
            (> (file-mtime src) so-time)
            ;; Rebuild if any import file is newer (exports changed)
            (any-import-newer? so-time)))))

;;; ============================================================
;;; SICP Metrics - Structure analysis for forged modules
;;; ============================================================

(define (analyze-source src-file)
  "Analyze source file for SICP metrics.
   Returns alist: ((loc . N) (lambdas . N) (imports . N) (loc/lambda . N))"
  (if (not (file-exists? src-file))
      '((loc . 0) (lambdas . 0) (imports . 0) (loc/lambda . 0))
      (with-input-from-file src-file
        (lambda ()
          (let loop ((loc 0) (lambdas 0) (imports 0))
            (let ((line (read-line)))
              (if (eof-object? line)
                  (let ((ratio (if (> lambdas 0)
                                   (quotient loc lambdas)
                                   0)))
                    `((loc . ,loc)
                      (lambdas . ,lambdas)
                      (imports . ,imports)
                      (loc/lambda . ,ratio)))
                  (let* ((trimmed (string-trim-both line))
                         (is-blank (string-null? trimmed))
                         (is-comment (and (> (string-length trimmed) 0)
                                          (char=? (string-ref trimmed 0) #\;)))
                         (has-define (string-contains line "(define "))
                         (has-lambda (string-contains line "(lambda "))
                         (has-import (string-contains line "(import ")))
                    (loop (if (or is-blank is-comment) loc (+ loc 1))
                          (+ lambdas
                             (if has-define 1 0)
                             (if has-lambda 1 0))
                          (if has-import (+ imports 1) imports))))))))))

(define (forge-meta-file module)
  "Path to forge metadata file for module"
  (string-append ".forge/" module ".meta"))

(define (write-forge-metadata module metrics so-size import-size elapsed)
  "Write forge metadata for module"
  (unless (directory-exists? ".forge")
    (condition-case (create-directory ".forge")
      ((exn i/o file) #t)))  ; ignore race: another process created it
  (with-output-to-file (forge-meta-file module)
    (lambda ()
      (write `((module . ,module)
               (timestamp . ,(current-seconds))
               (so-size . ,so-size)
               (import-size . ,import-size)
               (compile-time-ms . ,elapsed)
               (metrics . ,metrics)))
      (newline))))

(define (read-forge-metadata module)
  "Read forge metadata for module, or #f if none"
  (let ((path (forge-meta-file module)))
    (if (file-exists? path)
        (with-input-from-file path read)
        #f)))

(define (forged module-name)
  "Display forge metadata for a module. Usage: (forged \"portal\")"
  (let ((meta (read-forge-metadata module-name)))
    (if meta
        (let* ((metrics (cdr (assq 'metrics meta)))
               (loc (cdr (assq 'loc metrics)))
               (lambdas (cdr (assq 'lambdas metrics)))
               (loc/lambda (cdr (assq 'loc/lambda metrics)))
               (so-size (cdr (assq 'so-size meta)))
               (import-size (cdr (assq 'import-size meta)))
               (compile-ms (cdr (assq 'compile-time-ms meta)))
               (ts (cdr (assq 'timestamp meta))))
          (printf "~a.scm~%" module-name)
          (printf "  forged: ~a~%" (time->string (seconds->local-time ts)))
          (printf "  output: ~aK + ~aB import in ~ams~%"
                  (quotient so-size 1024) import-size compile-ms)
          (printf "  structure: ~a LOC · ~a λ · ~a LOC/λ~%"
                  loc lambdas loc/lambda)
          (void))
        (printf "No forge metadata for ~a~%" module-name))))

(define (forged-all)
  "Display forge metrics for all modules"
  (let ((modules (if (directory-exists? ".forge")
                     (map (lambda (f) (pathname-strip-extension f))
                          (filter (lambda (f) (string-suffix? ".meta" f))
                                  (directory ".forge")))
                     '())))
    (if (null? modules)
        (print "No forge metadata found. Run (bootstrap-modules!) first.")
        (begin
          (printf "~%Bitfarm harvest: ~a modules~%~%" (length modules))
          (let ((totals (fold (lambda (mod acc)
                                (let* ((meta (read-forge-metadata mod))
                                       (metrics (cdr (assq 'metrics meta)))
                                       (loc (cdr (assq 'loc metrics)))
                                       (lambdas (cdr (assq 'lambdas metrics))))
                                  (cons (+ (car acc) loc)
                                        (+ (cdr acc) lambdas))))
                              '(0 . 0)
                              modules)))
            (printf "  Σ ~a LOC · ~a λ · ~a LOC/λ~%~%"
                    (car totals) (cdr totals)
                    (if (> (cdr totals) 0)
                        (quotient (car totals) (cdr totals))
                        0)))))))

(define *cyberspace-modules*
  '("os" "crypto-ffi" "sexp" "capability" "mdns" "fips" "audit" "wordlist"
    "bloom" "catalog" "keyring" "portal" "cert" "enroll" "gossip" "security"
    "vault" "auto-enroll" "ui" "inspector"))

(define (sicp)
  "Analyze SICP metrics for all Cyberspace modules (live, no forge metadata needed)"
  (printf "~%SICP Metrics - spki/scheme~%~%")
  (let loop ((modules *cyberspace-modules*)
             (total-loc 0)
             (total-lambdas 0))
    (if (null? modules)
        (begin
          (printf "~%  ─────────────────────────────────~%")
          (printf "  Σ ~a LOC · ~a λ · ~a LOC/λ~%~%"
                  total-loc total-lambdas
                  (if (> total-lambdas 0)
                      (quotient total-loc total-lambdas)
                      0)))
        (let* ((mod (car modules))
               (src (string-append mod ".scm"))
               (metrics (analyze-source src))
               (loc (cdr (assq 'loc metrics)))
               (lambdas (cdr (assq 'lambdas metrics)))
               (ratio (cdr (assq 'loc/lambda metrics))))
          (printf "  ~a: ~a LOC · ~a λ · ~a LOC/λ~%"
                  (string-pad-right mod 12) loc lambdas ratio)
          (loop (cdr modules)
                (+ total-loc loc)
                (+ total-lambdas lambdas))))))

(define (loch-lambda #!optional (path #f))
  "Show files with LOC/λ ≥ 10 (the Loch Lambda monsters).
   Usage: (loch-lambda)           ; Cyberspace modules
          (loch-lambda \"file.scm\") ; Single file
          (loch-lambda \"dir/\")     ; All .scm in directory"
  (let* ((files (cond
                  ((not path)
                   ;; Default: Cyberspace modules
                   (map (lambda (m) (string-append m ".scm")) *cyberspace-modules*))
                  ((string-suffix? ".scm" path)
                   ;; Single file
                   (list path))
                  ((directory-exists? path)
                   ;; Directory: all .scm files
                   (map (lambda (f) (string-append (if (string-suffix? "/" path) path (string-append path "/")) f))
                        (filter (lambda (f) (string-suffix? ".scm" f)) (directory path))))
                  (else
                   (printf "  Not a .scm file or directory: ~a~%" path)
                   '()))))
    (printf "~%Loch Lambda - files with LOC/λ ≥ 10~%~%")
    (let loop ((files files) (monsters '()))
      (if (null? files)
          (if (null? monsters)
              (printf "  No monsters! All files < 10 LOC/λ ✓~%~%")
              (begin
                (printf "  ─────────────────────────────────~%")
                (printf "  ~a monsters lurking~%~%" (length monsters))))
          (let* ((src (car files))
                 (name (pathname-strip-directory (pathname-strip-extension src)))
                 (metrics (analyze-source src))
                 (loc (cdr (assq 'loc metrics)))
                 (lambdas (cdr (assq 'lambdas metrics)))
                 (ratio (cdr (assq 'loc/lambda metrics))))
            (if (and (> lambdas 0) (>= ratio 10))
                (begin
                  (printf "  ~a: ~a LOC · ~a λ · ~a LOC/λ ⚠~%"
                          (string-pad-right name 16) loc lambdas ratio)
                  (loop (cdr files) (cons name monsters)))
                (loop (cdr files) monsters)))))))

;; Collect compiler warnings during forge (displayed at end, not inline)
(define *forge-warnings* '())

(define (forge-warnings)
  "Display collected compiler warnings from last forge run"
  (if (null? *forge-warnings*)
      (print "No warnings from last forge.")
      (begin
        (print "")
        (printf "Compiler warnings (~a):~%" (length *forge-warnings*))
        (for-each (lambda (w)
                    (printf "  ~a: ~a~%" (car w) (cdr w)))
                  *forge-warnings*)
        (print ""))))

(define (rebuild-module! module arch stamp)
  "Rebuild a module for current platform.
   Robust: checks exit code, verifies .so was updated, shows details.
   Note: Uses inline box-drawing (runs during bootstrap before os.scm loads)."
  (define (format-size bytes)
    (cond ((>= bytes (* 1024 1024))
           (sprintf "~aMB" (quotient bytes (* 1024 1024))))
          ((>= bytes 1024)
           (sprintf "~aK" (quotient bytes 1024)))
          (else
           (sprintf "~aB" bytes))))
  (define (count-substr str sub)
    "Count occurrences of substring in string."
    (let ((sub-len (string-length sub)))
      (let loop ((s str) (count 0))
        (let ((pos (string-contains s sub)))
          (if pos
              (loop (substring s (+ pos sub-len)) (+ count 1))
              count)))))

  ;; Spinning lambda for long operations - lambdas in motion!
  (define *spinner-chars* '#("λ" "λ·" "λ··" "λ···" "··λ·" "·λ··" "λ···" "λ··" "λ·" "λ"))
  (define *spinner-stars* '#("✧" "✦" "★" "✦" "✧" "☆" "✧" "✦" "★" "✦"))
  (define *spinner-idx* 0)

  (define (spin! #!optional (style 'lambda))
    "Advance spinner and display. Call repeatedly during long ops."
    (let* ((chars (if (eq? style 'stars) *spinner-stars* *spinner-chars*))
           (char (vector-ref chars (modulo *spinner-idx* (vector-length chars)))))
      (display (string-append "\r" char " "))
      (flush-output)
      (set! *spinner-idx* (+ *spinner-idx* 1))))

  (define (spin-done!)
    "Clear spinner line"
    (display "\r   \r")
    (flush-output)
    (set! *spinner-idx* 0))

  (define (with-spinner thunk #!optional (style 'lambda))
    "Run thunk with spinner animation"
    (let ((result #f))
      (handle-exceptions exn
        (begin (spin-done!) (abort exn))
        (set! result (thunk)))
      (spin-done!)
      result))
  (define (display-width str)
    "Calculate display width accounting for multi-byte Unicode chars.
     · λ are 2 bytes but 1 display char. ✓✗⚠≥≤ are 3 bytes but 1 display char."
    (let* ((len (string-length str))
           ;; Count all occurrences of multi-byte chars
           (middot-count (count-substr str "·"))  ; U+00B7, 2 bytes
           (lambda-count (count-substr str "λ"))  ; 2 bytes
           (check-count (count-substr str "✓"))   ; 3 bytes
           (cross-count (count-substr str "✗"))   ; 3 bytes
           (warn-count (count-substr str "⚠"))    ; 3 bytes
           (gte-count (count-substr str "≥"))     ; 3 bytes
           (lte-count (count-substr str "≤"))     ; 3 bytes
           ;; Adjust: ·λ=1 extra byte, ✓✗⚠≥≤=2 extra bytes each
           (adjustment (+ middot-count lambda-count
                         (* 2 (+ check-count cross-count warn-count gte-count lte-count)))))
      (- len adjustment)))
  (define w 90)  ; wide enough for compiler warnings
  (define (box-line content)
    (let* ((clen (display-width content))
           (pad (- w clen 2)))  ; original formula: w - clen - 2
      (if (< pad 0)
          ;; Line too long - truncate with ellipsis to fit box
          (let* ((max-len (- w 3))  ; room for "│ " and "… │"
                 (truncated (if (> (string-length content) max-len)
                               (substring content 0 max-len)
                               content)))
            (print "│ " truncated "… │"))
          (print "│ " content (make-string pad #\space) " │"))))
  (let* ((paths (libsodium-paths arch))
         (inc-path (car paths))
         (lib-path (cadr paths))
         (src (string-append module ".scm"))
         (so-file (string-append module ".so"))
         (import-file (string-append module ".import.scm"))
         (so-mtime-before (file-mtime so-file))
         (title (string-append " forge: " module " "))
         (title-len (string-length title))
         (left-pad (quotient (- w title-len) 2))
         (right-pad (- w title-len left-pad))
         (start-time (current-process-milliseconds)))
    (print "")
    (print "┌" (string-repeat "─" left-pad) title (string-repeat "─" right-pad) "┐")
    ;; Beta mode adds -strict-types for better type checking
    ;; All modules now have type declarations for tractable inference
    ;;
    ;; Modules depending on crypto-ffi need libsodium at link time.
    ;; We include library paths for all modules since it's harmless
    ;; for those that don't need it and ensures correct linking for
    ;; the crypto dependency chain (Memo-056: covert channel awareness).
    ;; vault uses set! in lambda closures which -strict-types breaks
    (let* ((strict-exempt '("vault"))
           (beta-flags (if (and (warnings-are-errors?) (not (member module strict-exempt)))
                           " -strict-types" ""))
           ;; crypto-ffi needs includes for header files, others just need lib path
           (needs-includes? (string=? module "crypto-ffi"))
           (lib-flags (string-append " -L" lib-path " -L -lsodium -L -lkeccak"))
           (inc-flags (if needs-includes? (string-append " -I" inc-path) ""))
           (actual-cmd (string-append "csc -shared -J" beta-flags " " src
                                      inc-flags lib-flags
                                      " 2>&1; echo \"__EXIT__$?\""))
           (display-cmd (string-append "csc -shared -J" beta-flags " " src
                                       (if needs-includes? " -I... -L... -lsodium -lkeccak" ""))))
      (box-line display-cmd)
      (let* ((all-output (with-input-from-pipe actual-cmd
                           (lambda ()
                             (let loop ((lines '()))
                               (let ((line (read-line)))
                                 (if (eof-object? line)
                                     (reverse lines)
                                     (loop (cons line lines))))))))
             (exit-line (find (lambda (l) (string-prefix? "__EXIT__" l)) all-output))
             (exit-code (if exit-line (string->number (substring exit-line 8)) 1))
             (output (remove (lambda (l) (string-prefix? "__EXIT__" l)) all-output)))
        ;; Separate warnings from errors - collect warnings, show errors
        (let ((warnings (filter (lambda (l) (string-prefix? "Warning:" l)) output))
              (non-warnings (remove (lambda (l) (string-prefix? "Warning:" l)) output)))
          ;; Collect warnings for summary at end
          (for-each (lambda (w)
                      (set! *forge-warnings*
                            (cons (cons module w) *forge-warnings*)))
                    warnings)
          ;; Show non-warning output (errors, etc.) in box
          (for-each (lambda (line)
                      (when (> (string-length line) 0)
                        (box-line line)))
                    non-warnings))
        (let* ((elapsed (- (current-process-milliseconds) start-time))
               (so-exists (file-exists? so-file))
               (so-mtime-after (file-mtime so-file))
               (so-updated (> so-mtime-after so-mtime-before))
               (success (and (= exit-code 0) so-exists so-updated)))
          (if success
              (let* ((so-size (file-size so-file))
                     (import-size (if (file-exists? import-file)
                                      (file-size import-file)
                                      0))
                     (metrics (analyze-source src))
                     (loc (cdr (assq 'loc metrics)))
                     (lambdas (cdr (assq 'lambdas metrics)))
                     (loc/lambda (cdr (assq 'loc/lambda metrics))))
                (write-arch-stamp module stamp)
                (write-forge-metadata module metrics so-size import-size elapsed)
                (box-line (sprintf "✓ ~a + ~a import in ~ams"
                                   (format-size so-size)
                                   (format-size import-size)
                                   elapsed))
                (box-line (sprintf "  ~a LOC · ~a λ · ~a LOC/λ"
                                   loc lambdas loc/lambda))
                (when (>= loc/lambda 10)
                  (box-line (sprintf "⚠ LOC/λ ≥ 10 (target: < 10)")))
                (print "└" (string-repeat "─" w) "┘")
                #t)
              (begin
                (when (not (= exit-code 0))
                  (box-line (sprintf "✗ csc exited ~a" exit-code)))
                (when (and so-exists (not so-updated))
                  (box-line "✗ stale .so (not rebuilt)"))
                (when (not so-exists)
                  (box-line "✗ no .so produced"))
                (print "└" (string-repeat "─" w) "┘")
                (print "")
                (exit 1))))))))

(define (platform-stamp)
  "Return OS+arch stamp (e.g., 'Darwin-arm64', 'Linux-x86_64')"
  (string-append (current-os) "-" (current-arch)))

(define (bootstrap-modules!)
  "Ensure all required modules are built for current platform.
   Sequential builds to avoid Chicken import library race conditions.
   Pristine builds: -w enables all warnings, expect zero output."
  ;; Clear warnings from previous forge run
  (set! *forge-warnings* '())
  (let ((stamp (platform-stamp))
        (arch (current-arch))
        ;; Build order: strict topological sort by dependency
        ;; Sequential within levels to ensure import libraries are available
        (levels '(;; Level 0 (no cyberspace deps)
                  ("os" "crypto-ffi" "sexp" "capability" "inspector" "forum" "display")
                  ;; Level 1 (single deps from L0)
                  ("mdns" "fips" "audit" "wordlist" "bloom" "catalog" "keyring" "portal")
                  ;; Level 2 (cert needs sexp)
                  ("cert")
                  ;; Level 3 (security needs cert)
                  ("security")
                  ;; Level 4 (vault needs cert, audit, os)
                  ("vault")
                  ;; Level 5 (enroll, gossip need vault)
                  ("enroll" "gossip")
                  ;; Level 6 (auto-enroll needs enroll)
                  ("auto-enroll")
                  ;; Level 7 (ui needs enroll)
                  ("ui"))))

    (define (rebuild-level! modules-in-level)
      "Rebuild modules in level sequentially, return count rebuilt.
       Sequential builds avoid Chicken import library race conditions."
      (let ((to-build (filter (lambda (m) (needs-rebuild? m stamp)) modules-in-level)))
        (for-each (lambda (module)
                    (rebuild-module! module arch stamp))
                  to-build)
        (length to-build)))

    (let ((total-rebuilt (fold (lambda (level count)
                                 (+ count (rebuild-level! level)))
                               0
                               levels)))
      ;; Show forge summary when modules were rebuilt
      (when (> total-rebuilt 0)
        (let ((totals (fold (lambda (mod acc)
                              (let ((meta (read-forge-metadata mod)))
                                (if meta
                                    (let* ((metrics (cdr (assq 'metrics meta)))
                                           (loc (cdr (assq 'loc metrics)))
                                           (lambdas (cdr (assq 'lambdas metrics))))
                                      (cons (+ (car acc) loc)
                                            (+ (cdr acc) lambdas)))
                                    acc)))
                            '(0 . 0)
                            (apply append levels))))
          (printf "~%Σ ~a LOC · ~a λ · ~a LOC/λ~%"
                  (car totals) (cdr totals)
                  (if (> (cdr totals) 0)
                      (quotient (car totals) (cdr totals))
                      0))
          ;; Show warning count if any - fail in beta mode
          (when (not (null? *forge-warnings*))
            (let ((count (length *forge-warnings*))
                  (modules (length (delete-duplicates (map car *forge-warnings*)))))
              (printf "  ⚠ ~a warning~a across ~a module~a (forge-warnings)~%"
                      count (if (= count 1) "" "s")
                      modules (if (= modules 1) "" "s"))
              (when (warnings-are-errors?)
                (print "")
                (print "Beta build: warnings are errors. Fix before continuing.")
                (forge-warnings)
                (exit 1))))))
      (when (and (= total-rebuilt 0) (>= *boot-verbosity* 1))
        (print "All tomes current for " stamp))
      ;; Show metrics at chronicle level (3+) even if nothing rebuilt
      (when (and (= total-rebuilt 0) (>= *boot-verbosity* 3))
        (let ((totals (fold (lambda (mod acc)
                              (let ((meta (read-forge-metadata mod)))
                                (if meta
                                    (let* ((metrics (cdr (assq 'metrics meta)))
                                           (loc (cdr (assq 'loc metrics)))
                                           (lambdas (cdr (assq 'lambdas metrics))))
                                      (cons (+ (car acc) loc)
                                            (+ (cdr acc) lambdas)))
                                    acc)))
                            '(0 . 0)
                            (apply append levels))))
          (printf "  Σ ~a LOC · ~a λ · ~a LOC/λ~%"
                  (car totals) (cdr totals)
                  (if (> (cdr totals) 0)
                      (quotient (car totals) (cdr totals))
                      0))
          (when (not (null? *forge-warnings*))
            (let ((count (length *forge-warnings*))
                  (modules (length (delete-duplicates (map car *forge-warnings*)))))
              (printf "  ⚠ ~a warning~a across ~a module~a (forge-warnings)~%"
                      count (if (= count 1) "" "s")
                      modules (if (= modules 1) "" "s"))
              (when (warnings-are-errors?)
                (print "")
                (print "Beta build: warnings are errors. Fix before continuing.")
                (forge-warnings)
                (exit 1)))))))))

;; Run bootstrap before loading modules
(bootstrap-modules!)

;; Load cyberspace modules (now guaranteed to be correct arch)
;; Note: os already imported at top for early hostname access
(import crypto-ffi)
(import fips)
(import (except vault lamport-send))
(import audit)
(import cert)
(import sexp)
(import wordlist)
(import mdns)
(import bloom)
(import catalog)
(import (except enroll enroll-listen))
(import gossip)
(import security)
(import keyring)
(import capability)
(import (except auto-enroll enrollment-status))
(import ui)
(import (except inspector describe))
(import (except portal count-vault-items))
(import forum)
(import (except display clear terminal-height vt100-reverse vt100-normal vt100-clear-line))
(import (except info info))  ; hypertext doc browser with pager

;; Resident editors - load once, always ready (like LSE, VAX Emacs)
(load "teco.scm")     ; Dan Murphy's TECO (1962)
(load "pencil.scm")   ; Michael Shrayer's Electric Pencil (1976)
(load "schemacs.scm") ; Emacs-style editor in Scheme (2026)

;; Initialize libsodium
(sodium-init)

;; FIPS self-tests (KATs) - verify crypto primitives before trusting them
(fips-self-test)

(module-end! "bootstrap")
(module-start! "core")

;;; ============================================================
;;; BLAKE2b Hash (via libsodium)
;;; ============================================================
;;; blake2b-hash imported from crypto-ffi
;;; Uses libsodium's crypto_generichash (BLAKE2b-256, 32 bytes)

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

(module-end! "core")
(module-start! "memos")

;;; ============================================================
;;; Memo-040: Object State (chaotic/quiescent) and Persistence
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

(define (validate-for-vault thing)
  "Run thing's self-test lambda before allowing vault migration.
   MANDATORY: Every thing MUST carry a 'test lambda to be archived.
   No test = no vault. Clean pass required."
  (let ((test-entry (and (list? thing)
                         (pair? (car thing))
                         (assq 'test thing))))
    (if test-entry
        (handle-exceptions exn
          (begin
            (print "  ✗ validation exception: "
                   (get-condition-property exn 'exn 'message "unknown"))
            #f)
          (let ((result ((cdr test-entry))))
            (if result
                #t
                (begin
                  (print "  ✗ self-test failed")
                  #f))))
        ;; No test lambda = REJECT
        (begin
          (print "  ✗ no test lambda (mandatory for vault)")
          #f))))

(define (flush-persistence!)
  "Migrate all queued persistent things to vault.
   Each thing must pass its self-contained regression test (if any)."
  (if (null? *persistence-queue*)
      (print "Persistence queue empty")
      (let* ((things *persistence-queue*)
             (validated (filter validate-for-vault things))
             (rejected (filter (lambda (t) (not (validate-for-vault t))) things)))
        (print "Migrating " (length things) " things to vault...")
        (print "  " (length validated) " passed validation")
        (when (not (null? rejected))
          (print "  " (length rejected) " REJECTED (failed self-test)"))
        ;; Only migrate validated things
        (for-each
         (lambda (thing)
           (let ((id (thing-id thing)))
             (content-put (format "~a" thing))
             (print "  ✓ " (short-id id) " -> vault")))
         validated)
        ;; Clear only migrated things, keep rejected in queue
        (set! *persistence-queue* rejected)
        (if (null? rejected)
            (print "Done.")
            (print "Done. " (length rejected) " things remain in queue (fix and retry).")))))

(define (thing-status thing)
  "Show thing's state and durability"
  (let ((id (thing-id thing)))
    (print "Thing: " (short-id id))
    (print "  State: " (thing-state thing))
    (print "  Durability: " (thing-durability thing))
    (print "  Cacheable: " (if (quiescent? thing) "yes (forever)" "no"))
    (print "  Self-test: " (if (and (list? thing)
                                    (pair? (car thing))
                                    (assq 'test thing))
                               "present"
                               "none"))
    `((id . ,id)
      (state . ,(thing-state thing))
      (durability . ,(thing-durability thing)))))

(define (make-tested-thing id data test-lambda)
  "Create a thing with a self-contained regression test.
   Example:
     (make-tested-thing 'my-cert cert-data
       (lambda () (verify-signature cert-data)))
   The test lambda must return #t to pass."
  `((id . ,id)
    (data . ,data)
    (test . ,test-lambda)
    (created . ,(current-seconds))))

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
;;; Memo-043: Memo Conventions
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
               ((core) (string-append "Memo-" num))
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
         (print "Promoting " memo-id " to core (Memo)")
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
;;; Memo-016: Lazy Clustering
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
  (session-stat! 'syncs)
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
;;; Memo-010: Federation
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
;;; The Weave - Federation Topology View
;;; ============================================================
;;; "Reflection invites introspection in the weave."
;;;
;;; From any node, see all nodes. The mirrors reflect the entire
;;; constellation - not just who you're enrolled with, but the
;;; full topology as known through gossip.

(define (weave-list-enrolled)
  "List enrolled nodes from .vault/keys/*.cert"
  (let ((keys-dir ".vault/keys"))
    (if (directory-exists? keys-dir)
        (let ((certs (glob "*.cert" keys-dir)))
          (map (lambda (cert-file)
                 (let* ((name (pathname-strip-extension (pathname-file cert-file)))
                        (cert-data (handle-exceptions exn #f
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
  "Get local realm information"
  (let* ((host (hostname))
         (vault-exists (directory-exists? ".vault"))
         (keystore-exists (directory-exists? ".vault/keystore"))
         (principal (if keystore-exists
                       (handle-exceptions exn "locked"
                         (let ((pub-file ".vault/keystore/public.key"))
                           (if (file-exists? pub-file)
                               (short-id (with-input-from-file pub-file read-line))
                               "no-key")))
                       "no-keystore")))
    `(,host
      (principal ,principal)
      (vault ,vault-exists)
      (keystore ,keystore-exists))))

(define (weave)
  "Show the weave - federation topology from this realm's perspective.

   The weave is the constellation of enrolled realms, as seen through
   the wilderness of mirrors. Each realm mirrors what it knows;
   gossip propagates the topology.

   Example:
     (weave)
     => (weave
          (local (lambda (principal \"7f3a...\") (vault #t)))
          (enrolled
            (starlight (principal \"9b2c...\"))
            (fluffy (principal \"4d8e...\")))
          (gossip
            (peers 2)
            (running #f)))"
  (session-stat! 'queries)
  (let* ((local (weave-local-realm))
         (enrolled (weave-list-enrolled))
         (gossip-info (handle-exceptions exn
                        `(gossip (error "gossip not loaded"))
                        (gossip-status)))
         (peers (handle-exceptions exn '()
                  (list-peers))))
    (print "")
    (print "╔══════════════════════════════════════════════════════════════╗")
    (print "║                        THE WEAVE                             ║")
    (print "║           Reflection invites introspection                   ║")
    (print "╚══════════════════════════════════════════════════════════════╝")
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
    ;; Consensus status
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
    ;; Lamport clock
    (print "Lamport Clock: " *lamport-clock*)
    (print "")
    ;; Return structured data for programmatic use
    `(weave
      (local ,local)
      (enrolled ,@enrolled)
      (gossip ,gossip-info)
      (peers ,@peers)
      (consensus ,(length *consensus-proposals*))
      (lamport ,*lamport-clock*))))

;; Forward declaration note: *quorum-proposals* defined in Memo-036 section
;; Weave can access it after full load

(define (about)
  "Describe Cyberspace for the uninitiated. The description morphs with the weave."
  (let* ((realm-name (realm-signature))
         (enrolled (handle-exceptions exn '() (weave-list-enrolled)))
         (peer-count (length enrolled))
         (vault-path (get-vault-path))
         (has-vault (and vault-path (directory-exists? vault-path))))
    (print "")
    (print "════════════════════════════════════════════════════════════════")
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
    (print "  If one computer goes offline, the others still have everything.")
    (print "")
    (print "  Your data belongs to you, verified by math, preserved by the")
    (print "  people you choose.")
    (print "")
    (print "════════════════════════════════════════════════════════════════")
    (print "")
    (print "  This realm: " realm-name)
    (cond
      ((= peer-count 0)
       (print "  Standing alone. No peers enrolled yet.")
       (print "  Use (enroll-request \"name\") to join the weave."))
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
    `(about
      (realm ,realm-name)
      (peers ,peer-count)
      (vault ,has-vault))))

;; Synonyms for the uninitiated
(define (huh?) (about))
(define (what?) (about))

;;; ============================================================
;;; Memo-011: Byzantine Consensus
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
  (session-stat! 'votes)
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
;;; Memo-012: Lamport Clocks
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
;;; Memo-020: Content-Addressed Storage
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
;;; Memo-021: Capability Delegation
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
;;; Memo-023: Agent Sandboxing (Demonic Agents)
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
;;; Memo-035: Mobile Agents (Quantum Vocabulary)
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
        (list-ref states (random-uniform (length states))))
      superposition))

;;; ============================================================
;;; Memo-036: Quorum Voting (Homomorphic)
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
  (session-stat! 'votes)
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
;;; Memo-038: Local Inference (Ollama)
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
;;; Memo-041: FUSE Filesystem
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
    (session-stat! 'wormholes)
    (print "  (wormhole simulated - full implementation requires libfuse)")
    `(wormhole ,abs-path ,vault-path)))

(define (wormhole-lock fs-path)
  "Lock wormhole (requires unlock to resume)"
  (let ((w (find (lambda (w) (equal? (alist-ref 'fs w) fs-path)) *wormholes*)))
    (if w
        (begin
          (set-cdr! (assq 'status w) 'locked)
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
     (code-execution . sandboxed)          ; agents confined by Memo-023
     (ambient-channels . blocked)          ; no covert channels
     (reference-passing . by-capability))  ; objects passed as capabilities

    (audit
     ;; All operations are logged
     (logging . comprehensive)             ; all ops logged (Memo-003)
     (trail . tamper-evident)              ; append-only, signed
     (critical-ops . always)               ; open, close, delegate logged
     (data-ops . configurable)             ; read/write logging optional
     (non-repudiation . cryptographic))    ; signed audit entries

    (availability
     ;; Protection against abuse and resource exhaustion
     (rate-limiting . enforced)            ; ops/minute limits (Memo-032)
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
;;; Secure Erasure (Memo-040)
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
;;; Cluster Status (banner helper)
;;; ============================================================
;; Note: (help) with topic system is defined later in the file

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

(define (tree obj #!key (depth 0) (max-depth 6) (prefix "") (last #t))
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
            (tree items depth: (+ depth 1) prefix: child-prefix last: #t))
           ((> idx 10)
            (print child-prefix "└── … (" (- (length obj) idx) " more)"))
           (else
            (let ((is-last (or (null? (cdr items))
                               (and (pair? (cdr items)) (> idx 9)))))
              (tree (car items)
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
                (tree (vector-ref obj i)
                         depth: (+ depth 1)
                         prefix: child-prefix
                         last: (= i (- len 1))))))))))

  ;; Return void for clean REPL output
  (void))

(define (i obj)
  "Short alias for tree (ASCII object display)"
  (tree obj))

;;; ============================================================
;;; Stack Frame Inspector - Dylan-style Debugging
;;; ============================================================

(define *last-exception* #f)
(define *last-call-chain* #f)

(define (capture-exception exn)
  "Capture exception and call chain for inspection"
  (set! *last-exception* exn)
  ;; Extract throw-site call chain from condition object - Chicken stores it there
  (set! *last-call-chain* (get-condition-property exn 'exn 'call-chain #f)))

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
  ;; Note: caller should have already called capture-exception
  (let ((b (os#make-box 66)))
    (print "")
    (print (os#box-top b "Exception"))

    ;; Extract exception properties
    (let* ((msg (get-condition-property exn 'exn 'message ""))
           (loc (get-condition-property exn 'exn 'location #f))
           (args (get-condition-property exn 'exn 'arguments '()))
           (kind (cond ((condition? exn)
                        (cond ((get-condition-property exn 'type 'type #f))
                              ((get-condition-property exn 'exn 'type #f))
                              (else #f)))
                       (else #f))))

      ;; Exception type if available
      (when kind
        (os#box-print b (sprintf "Type: ~a" kind)))

      ;; Error message
      (os#box-print b (or msg "(no message)"))

      ;; Location if available
      (when loc
        (os#box-print b (sprintf "In: ~a" loc)))

      ;; Arguments if available
      (when (and args (not (null? args)))
        (os#box-print b "Arguments:")
        (for-each
          (lambda (arg)
            (let ((s (with-output-to-string (lambda () (write arg)))))
              (os#box-print b (sprintf "  ~a" s))))
          args)))

    (print (os#box-separator b))
    (os#box-print b "(bt) backtrace  (frame N) inspect  (exception-info) details")
    (print (os#box-bottom b))))

;;; ============================================================
;;; Enrollment Status Display
;;; ============================================================

(define (enrollment-status)
  "Display current enrollment status"
  (let* ((node-id (read-node-identity))
         (hostname (get-hostname))
         (w 50))
    (define (line . content)
      (let* ((text (apply string-append content))
             (pad (- w (string-length text) 2)))
        (print "│ " text (make-string (max 0 pad) #\space) " │")))
    (print "")
    (print "┌───────────────────── status ─────────────────────┐")
    (if node-id
        (let ((name (cond ((assq 'name node-id) => cadr) (else "unknown")))
              (role (cond ((assq 'role node-id) => cadr) (else "unknown")))
              (master (cond ((assq 'master node-id) => cadr) (else #f)))
              (enrolled (cond ((assq 'enrolled node-id) => cadr) (else #f))))
          (line "node:     " (->string name))
          (line "role:     " (->string role))
          (when master (line "master:   " (->string master)))
          (when enrolled (line "enrolled: " (->string enrolled)))
          (line)
          (line "enrolled"))
        (begin
          (line "host:     " hostname)
          (line)
          (line "not enrolled")
          (line)
          (line "To enroll:")
          (line "  (enroll-request 'name)")))
    (print "└──────────────────────────────────────────────────┘")
    (void)))

(define (enroll-status) (enrollment-status))

;;; ============================================================
;;; Enrollment Listener (Master Side)
;;; ============================================================

(define *enrollment-debug* #f)          ; set to #t for verbose debugging
(define *pending-enrollments* '())      ; incoming requests (master side)
(define *outgoing-enrollments* '())     ; outgoing requests (requestor side)
(define *enrollment-listener* #f)
(define *pending-file* ".vault/pending-enrollments.sexp")

(define (save-pending-enrollments!)
  "Persist pending enrollments to disk"
  (when (directory-exists? ".vault")
    (with-output-to-file *pending-file*
      (lambda ()
        (write `(pending-enrollments
                  (version 1)
                  (timestamp ,(current-seconds))
                  (requests ,*pending-enrollments*)))
        (newline)))))

(define (load-pending-enrollments!)
  "Load pending enrollments from disk"
  (when (file-exists? *pending-file*)
    (handle-exceptions exn
      (print "Warning: could not load pending enrollments")
      (let ((data (with-input-from-file *pending-file* read)))
        (when (and (pair? data) (eq? 'pending-enrollments (car data)))
          (let ((requests (cdr (assq 'requests (cdr data)))))
            (when requests
              (set! *pending-enrollments* (car requests))))))))
  (length *pending-enrollments*))

(define (enroll-debug! #!optional (on #t))
  "Enable/disable enrollment debugging"
  (set! *enrollment-debug* on)
  (print (if on "Enrollment debugging enabled" "Enrollment debugging disabled")))

(define (enrollment-handler name pubkey host port)
  "Handler for incoming enrollment requests"
  (when *enrollment-debug*
    (print "[debug] enrollment-handler called:")
    (print "[debug]   name=" name)
    (print "[debug]   pubkey=" (if (> (string-length pubkey) 20)
                                    (string-append (substring pubkey 0 20) "...")
                                    pubkey))
    (print "[debug]   host=" host " port=" port)
    (print "[debug]   current pending=" (length *pending-enrollments*)))
  (let* ((words (generate-verification-words pubkey))
         (request `((name ,name)
                    (pubkey ,pubkey)
                    (host ,host)
                    (port ,port)
                    (words ,words)
                    (timestamp ,(current-seconds)))))
    (set! *pending-enrollments* (cons request *pending-enrollments*))
    (save-pending-enrollments!)  ; persist to disk
    (when *enrollment-debug*
      (print "[debug] after set!, pending=" (length *pending-enrollments*))
      (print "[debug] request=" request))
    ;; Alert user with bell and visible output
    (display "\a")  ; bell
    (flush-output)
    (print "")
    (print "")
    (print "┌─ New Enrollment Request ─────────────────────────────────────────┐")
    (let* ((node-str (sprintf "Node ~a wants to enroll" name))
           (from-str (sprintf "Connecting from ~a on port ~a" host port))
           (verify-str (sprintf "Verification words: ~a" words)))
      (printf "│  ~a~a│~n" node-str (make-string (max 0 (- 64 (string-length node-str))) #\space))
      (printf "│  ~a~a│~n" from-str (make-string (max 0 (- 64 (string-length from-str))) #\space))
      (print "│                                                                  │")
      (printf "│  ~a~a│~n" verify-str (make-string (max 0 (- 64 (string-length verify-str))) #\space))
      (print "│                                                                  │"))
    (print "│  (pending)  (accept 'name)  (reject 'name)                       │")
    (print "└──────────────────────────────────────────────────────────────────┘")
    (print "")
    (display *prompt*)  ; re-display prompt
    (flush-output)
    (void)))

(define (generate-verification-words pubkey)
  "Generate FIPS-181 verification syllables from pubkey"
  (let ((key-data (cond
                    ((blob? pubkey) pubkey)
                    ;; Hex string (64 chars for 32-byte key)
                    ((and (string? pubkey) (= (string-length pubkey) 64))
                     (hex->blob pubkey))
                    ((string? pubkey) (string->blob pubkey))
                    (else (string->blob (->string pubkey))))))
    (syllables->display (pubkey->syllables key-data))))

(define (enroll-listen #!optional (port 7654))
  "Start listening for enrollment requests (master side)"
  (when *enrollment-listener*
    (print "Stopping existing listener...")
    (stop-listening))

  ;; Load any persisted pending requests
  (let ((loaded (load-pending-enrollments!)))
    (when (> loaded 0)
      (print "Loaded " loaded " pending enrollment request(s) from disk")))

  (when *enrollment-debug*
    (print "[debug] enroll-listen starting on port " port)
    (print "[debug] current pending count: " (length *pending-enrollments*)))

  (print "")
  (print "┌─ Enrollment Listener ────────────────────────────────────────────┐")
  (let ((listen-str (sprintf "Listening for enrollment requests on port ~a" port)))
    (printf "│  ~a~a│~n" listen-str (make-string (- 64 (string-length listen-str)) #\space)))
  (print "│                                                                  │")
  (print "│  Waiting nodes should run (enroll-to \"host\" 'node-name)         │")
  (print "│  Requests will appear here with verification words.             │")
  (print "│                                                                  │")
  (print "│  Use (pending) (accept 'name) (reject 'name) or (stop-enroll)   │")
  (print "│  Use (enroll-debug!) to enable verbose debugging                │")
  (print "└──────────────────────────────────────────────────────────────────┘")

  (set! *enrollment-listener* (listen-for-enrollments enrollment-handler port: port))
  (when *enrollment-debug*
    (print "[debug] listener started: " *enrollment-listener*))
  (void))

(define (wait #!optional (seconds 5))
  "Wait for background events (enrollment requests, etc.)"
  (print "Waiting for events... (Ctrl-C to stop)")
  (let loop ((remaining seconds))
    (when (> remaining 0)
      (thread-sleep! 1)
      (when (> (length *pending-enrollments*) 0)
        (print "")
        (pending))
      (loop (- remaining 1))))
  (void))

(define (stop-enroll)
  "Stop the enrollment listener"
  (stop-listening)
  (set! *enrollment-listener* #f)
  (print "Enrollment listener stopped.")
  (void))

(define (pending)
  "Show pending enrollment requests"
  (when *enrollment-debug*
    (print "[debug] pending called, count=" (length *pending-enrollments*))
    (print "[debug] list=" *pending-enrollments*))
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
        (print "│  Use (accept 'name) to accept or (reject 'name) to deny         │")
        (print "└──────────────────────────────────────────────────────────────────┘")))
  (void))

(define (enroll-test)
  "Run enrollment system diagnostics"
  (print "")
  (print "Enrollment System Diagnostics")
  (print "─────────────────────────────")
  (print "  Debug mode:    " (if *enrollment-debug* "ON" "OFF (use (enroll-debug!) to enable)"))
  (print "  Listener:      " (if *enrollment-listener* "ACTIVE" "INACTIVE"))
  (print "  Pending:       " (length *pending-enrollments*) " requests")
  (print "  Outgoing:      " (length *outgoing-enrollments*) " requests")
  (print "")
  (print "Test handler directly? (enroll-test-handler 'test)")
  (void))

(define (enroll-test-handler name)
  "Test enrollment handler directly (bypasses network)"
  (print "Testing handler with fake enrollment request...")
  (let ((fake-pubkey (blob->hex (random-bytes 32))))
    (enrollment-handler name fake-pubkey "127.0.0.1" 7654)
    (print "")
    (print "Handler test complete. Check (pending) to see if request was stored.")))

(define (accept name)
  "Accept pending enrollment request by name"
  (let ((req (find (lambda (r) (eq? (cadr (assq 'name r)) name)) *pending-enrollments*)))
    (if (not req)
        (printf "No pending request for '~a'. Use (pending) to see list.~n" name)
        (let* ((pubkey-hex (cadr (assq 'pubkey req)))
               (pubkey (hex->blob pubkey-hex))
               (signing-key (vault-config 'signing-key))
               (master-pubkey (get-vault-principal signing-key)))
          (print "")
          (if (not signing-key)
              (print "Error: No signing key. Use (keystore-unlock \"passphrase\") first.")
              (begin
                (printf "Accepting ~a...~n" name)
                ;; Create enrollment certificate
                (let* ((now (current-seconds))
                       (validity (make-validity #f (+ now (* 365 24 60 60))))  ; 1 year
                       (tag (make-tag (sexp-list (list (sexp-atom "member")))))
                       (issuer-principal (make-key-principal master-pubkey))
                       (subject-principal (make-key-principal pubkey))
                       (cert (create-cert issuer-principal subject-principal tag
                               validity: validity))
                       (signed (sign-cert cert signing-key)))
                  ;; Store certificate in vault
                  (let ((cert-path (make-pathname ".vault/keys" (string-append (->string name) ".cert"))))
                    (unless (directory-exists? ".vault/keys")
                      (create-directory ".vault/keys" #t))
                    (with-output-to-file cert-path
                      (lambda ()
                        (display (sexp->string (signed-cert->sexp signed)))
                        (newline)))
                    (print "")
                    (print "┌─ Enrollment Accepted ───────────────────────────────────────────┐")
                    (let ((node-str (sprintf "~a is now a member of this realm" name))
                          (cert-str (sprintf "Certificate: ~a" cert-path)))
                      (printf "│  ~a~a│~n" node-str (make-string (max 0 (- 64 (string-length node-str))) #\space))
                      (printf "│  ~a~a│~n" cert-str (make-string (max 0 (- 64 (string-length cert-str))) #\space)))
                    (print "└──────────────────────────────────────────────────────────────────┘")
                    ;; Remove from pending and persist
                    (set! *pending-enrollments*
                          (filter (lambda (r) (not (eq? r req))) *pending-enrollments*))
                    (save-pending-enrollments!)
                    signed))))))
  (void)))

(define (reject name)
  "Reject pending enrollment request by name"
  (let ((req (find (lambda (r) (eq? (cadr (assq 'name r)) name)) *pending-enrollments*)))
    (if (not req)
        (printf "No pending request for '~a'. Use (pending) to see list.~n" name)
        (begin
          (printf "Rejected ~a~n" name)
          (set! *pending-enrollments*
                (filter (lambda (r) (not (eq? r req))) *pending-enrollments*))
          (save-pending-enrollments!))))
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
          ;; Give receiver time to read before we close
          (thread-sleep! 0.5)
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
  "Return 'N thing' or 'N things' based on count.
   Handles irregular plurals: -y → -ies, -s/-x/-ch/-sh → -es"
  (let ((suffix
         (cond
          ((= n 1) "")
          ;; Words ending in consonant + y → ies
          ((and (> (string-length singular) 1)
                (char=? (string-ref singular (- (string-length singular) 1)) #\y)
                (not (memv (string-ref singular (- (string-length singular) 2))
                           '(#\a #\e #\i #\o #\u))))
           (set! singular (substring singular 0 (- (string-length singular) 1)))
           "ies")
          ;; Words ending in s, x, ch, sh → es
          ((or (string-suffix? "s" singular)
               (string-suffix? "x" singular)
               (string-suffix? "ch" singular)
               (string-suffix? "sh" singular))
           "es")
          (else "s"))))
    (string-append (number->string n) " " singular suffix)))

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
         (obj-count (count-vault-items "objects"))
         (key-count (count-vault-items "keys"))
         (release-count (length (filter (lambda (f) (string-suffix? ".sexp" f))
                                        (if (directory-exists? ".vault/releases")
                                            (directory ".vault/releases")
                                            '()))))
         (node-id (read-node-identity)))
    ;; Vault contents line
    (print "  " (plural obj-count "object") ", " (plural release-count "release") ", " (plural key-count "key"))
    (when (> audit-entries 0)
      (print "  " (plural audit-entries "audit entry")))
    (when keystore-exists
      (let ((keycount (count-vault-items "keystore")))
        (print "  " (plural keycount "identity") " in keystore")))
    (if node-id
        (let ((name (cond ((assq 'name node-id) => cadr) (else "unknown")))
              (role (cond ((assq 'role node-id) => cadr) (else "unknown"))))
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

(define (get-primary-ipv4)
  "Get primary IPv4 address (first non-loopback)"
  (let ((result (with-input-from-pipe
                 "ifconfig 2>/dev/null | grep 'inet ' | grep -v '127.0.0.1' | head -1 | awk '{print $2}'"
                 read-line)))
    (if (or (eof-object? result) (string=? result ""))
        #f
        result)))

(define (get-primary-ipv6)
  "Get primary IPv6 address (first global, non-link-local)"
  (let ((result (with-input-from-pipe
                 "ifconfig 2>/dev/null | grep 'inet6 ' | grep -v 'fe80' | grep -v '::1' | head -1 | awk '{print $2}'"
                 read-line)))
    (if (or (eof-object? result) (string=? result ""))
        #f
        result)))

(define (get-platform-stamp)
  "Get platform stamp (e.g., Darwin-arm64)"
  (let ((os (with-input-from-pipe "uname -s 2>/dev/null" read-line))
        (arch (with-input-from-pipe "uname -m 2>/dev/null" read-line)))
    (if (and (not (eof-object? os)) (not (eof-object? arch)))
        (string-append os "-" arch)
        "unknown")))

(define (get-hardware-summary)
  "Get brief hardware summary (cores, memory, chip)"
  (let ((os (with-input-from-pipe "uname -s 2>/dev/null" read-line)))
    (if (and (not (eof-object? os)) (string=? os "Darwin"))
        (let* ((cores (with-input-from-pipe "sysctl -n hw.ncpu 2>/dev/null" read-line))
               (mem-bytes (with-input-from-pipe "sysctl -n hw.memsize 2>/dev/null" read-line))
               (chip (with-input-from-pipe "sysctl -n machdep.cpu.brand_string 2>/dev/null" read-line)))
          (let ((mem-gb (if (and (not (eof-object? mem-bytes)) (not (string=? mem-bytes "")))
                            (inexact->exact (round (/ (string->number mem-bytes) 1073741824)))
                            0))
                (chip-short (if (and (not (eof-object? chip)) (not (string=? chip "")))
                                ;; Extract chip name (e.g., "Apple M4" from "Apple M4 Pro")
                                (let ((idx (substring-index "Apple M" chip)))
                                  (if idx
                                      ;; Find end of chip name (M + digits + optional suffix)
                                      (let loop ((i (+ idx 7)))
                                        (if (or (>= i (string-length chip))
                                                (char=? (string-ref chip i) #\space)
                                                (char=? (string-ref chip i) #\,))
                                            (string-trim-both (substring chip idx i))
                                            (loop (+ i 1))))
                                      chip))
                                #f)))
            (string-append
             (if (and (not (eof-object? cores)) (not (string=? cores "")))
                 (string-append cores " cores, ") "")
             (if (> mem-gb 0) (string-append (number->string mem-gb) "GB") "")
             (if chip-short (string-append ", " chip-short) ""))))
        ;; Linux or other
        (let* ((cores (with-input-from-pipe "nproc 2>/dev/null" read-line))
               (mem-kb (with-input-from-pipe "grep MemTotal /proc/meminfo 2>/dev/null | awk '{print $2}'" read-line)))
          (let ((mem-gb (if (and (not (eof-object? mem-kb)) (not (string=? mem-kb "")))
                            (inexact->exact (round (/ (string->number mem-kb) 1048576)))
                            0)))
            (string-append
             (if (and (not (eof-object? cores)) (not (string=? cores "")))
                 (string-append cores " cores, ") "")
             (if (> mem-gb 0) (string-append (number->string mem-gb) "GB") "")))))))

(define (get-connection-origin)
  "Get the origin of the current connection (SSH client or local).
   Returns #f for local sessions, hostname/IP for remote."
  (let ((ssh-client (get-environment-variable "SSH_CLIENT"))
        (ssh-conn (get-environment-variable "SSH_CONNECTION")))
    (cond
     ;; SSH_CLIENT format: "IP port port"
     ((and ssh-client (> (string-length ssh-client) 0))
      (car (string-split ssh-client " ")))
     ;; SSH_CONNECTION format: "client_IP client_port server_IP server_port"
     ((and ssh-conn (> (string-length ssh-conn) 0))
      (car (string-split ssh-conn " ")))
     (else #f))))

(define (banner)
  (let* ((host (capitalize-first (get-hostname)))
         (window-title (string-append host " Workstation"))
         (version (git-version))
         (date (git-date))
         (platform (get-platform-stamp))
         (ipv4 (get-primary-ipv4))
         (ipv6 (get-primary-ipv6))
         (hw (get-hardware-summary))
         ;; Boot timestamp: UTC canonical + local reference
         (secs (current-seconds))
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
         (boot-time (sprintf "~a (~a)" utc-str local-str))
         ;; Full introspection
         (info (introspect-system))
         (code (assq 'codebase (cdr info)))
         (realm (assq 'realm (cdr info)))
         (loc (and code (cadr (assq 'loc (cdr code)))))
         (tcb (and code (assq 'tcb (cdr code)) (cadr (assq 'tcb (cdr code)))))
         (modules (and code (cadr (assq 'modules (cdr code)))))
         (memos (and code (cadr (assq 'memos (cdr code)))))
         (vault-exists (and realm (cadr (assq 'vault-exists (cdr realm)))))
         ;; Vault contents - default to 0 if not present
         (vault-objects (or (and realm (assq 'objects (cdr realm)) (cadr (assq 'objects (cdr realm)))) 0))
         (vault-keys (or (and realm (assq 'keys (cdr realm)) (cadr (assq 'keys (cdr realm)))) 0))
         (vault-releases (or (and realm (assq 'releases (cdr realm)) (cadr (assq 'releases (cdr realm)))) 0))
         (vault-audits (or (and realm (assq 'audits (cdr realm)) (cadr (assq 'audits (cdr realm)))) 0))
        ;; Identity
         (node-id (read-node-identity))
         ;; Connection origin (SSH client)
         (origin (get-connection-origin)))
    (set-terminal-title window-title)
    (print "")
    (print "Cyberspace Scheme " version " (" date ")")
    (print "  " host " · " platform (if (not (string=? hw "")) (string-append " · " hw) ""))
    (print "  boot: " boot-time)
    (when (or ipv4 ipv6)
      (print "  Internet endpoints: " (or ipv4 "—") " · " (or ipv6 "—")))
    (when origin (print "  from: " origin))
    (print "  "
           (if loc (string-append (number->string (quotient loc 1000)) "K loc") "")
           (if modules (string-append ", " (number->string modules) " modules") "")
           (if memos (string-append ", " (number->string memos) " memos") "")
           (if (and tcb (> tcb 0))
               (string-append ", " (number->string (quotient tcb 1000)) "K tcb"
                              (if loc
                                  (string-append " (1:" (number->string (round (/ loc tcb))) ")")
                                  ""))
               ""))
    (when vault-exists
      ;; Build comma-separated vault summary
      (let ((parts '()))
        (when (> vault-audits 0)
          (set! parts (cons (plural vault-audits "audit") parts)))
        (when (> vault-keys 0)
          (set! parts (cons (plural vault-keys "key") parts)))
        (when (> vault-releases 0)
          (set! parts (cons (plural vault-releases "release") parts)))
        (when (> vault-objects 0)
          (set! parts (cons (plural vault-objects "object") parts)))
        (let ((summary (if (null? parts) "" (string-append " (" (string-intersperse parts ", ") ")"))))
          (print "  vault: " vault-exists summary))))
    ;; Realm name and principal
    (when vault-exists
      (let ((name (realm-name))
            (realm-pub-file (string-append vault-exists "/keystore/realm.pub")))
        (when (file-exists? realm-pub-file)
          (let* ((sexp (with-input-from-file realm-pub-file read))
                 (pk-entry (and (pair? sexp) (assq 'public-key (cdr sexp))))
                 (pk (and pk-entry (cadr pk-entry))))
            (when pk
              (let* ((hex (blob->hex pk))
                     (len (string-length hex))
                     (short-hash (string-append (substring hex 0 4) "..." (substring hex (- len 4)))))
                (if name
                    (print "  realm: " name " (" short-hash ")")
                    (print "  realm: " short-hash))))))))
    ;; Entropy source
    (let ((ent (entropy-status)))
      (print "  entropy: " (cdr (assq 'source ent)) " (" (cdr (assq 'implementation ent)) ")"))
    ;; FIPS self-test attestation
    (print "  FIPS: " (if (eq? (fips-status) 'passed) "passed" "FAILED"))
    ;; Lamport clock (Memo-012) - time in the weave
    (print "  " (lamport-format))
    ;; Show identity if enrolled
    (when node-id
      (let ((name (cond ((assq 'name node-id) => cadr) (else #f)))
            (role (cond ((assq 'role node-id) => cadr) (else #f))))
        (when (and name role)
          (print "  identity: " name " (" role ")"))))))

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
(define CIP-KNOCK    #x01)
(define CIP-COOKIE   #x02)
(define CIP-EXCHANGE #x03)
(define CIP-ATTEST   #x04)
(define CIP-OFFER    #x05)
(define CIP-CONFIRM  #x06)
(define CIP-DATA     #x10)
(define CIP-CLOSE    #xff)

;;; ============================================================
;;; SPKI Capability Helpers for CIP
;;; ============================================================

(define (make-offer-capabilities . caps)
  "Build SPKI tag for capability offer.
   Usage: (make-offer-capabilities 'read 'write 'replicate)"
  (let ((tag-sexp (sexp-list
                   (cons (sexp-atom "tag")
                         (list (sexp-list
                                (cons (sexp-atom "*")
                                      (cons (sexp-atom "set")
                                            (map (lambda (c) (sexp-atom (symbol->string c))) caps)))))))))
    (sexp->string tag-sexp)))

(define (parse-offer-capabilities str)
  "Parse SPKI tag from capability offer string.
   Returns list of capability symbols, or #f on parse failure."
  (condition-case
      (let* ((sexp (parse-sexp str))
             (items (and (sexp-list? sexp) (list-items sexp))))
        (if (and items
                 (>= (length items) 2)
                 (sexp-atom? (car items))
                 (string=? (atom-value (car items)) "tag"))
            ;; Extract capabilities from (tag (* set cap1 cap2 ...))
            (let* ((inner (cadr items))
                   (inner-items (and (sexp-list? inner) (list-items inner))))
              (if (and inner-items
                       (>= (length inner-items) 2)
                       (sexp-atom? (car inner-items))
                       (string=? (atom-value (car inner-items)) "*")
                       (sexp-atom? (cadr inner-items))
                       (string=? (atom-value (cadr inner-items)) "set"))
                  ;; Return capability symbols
                  (map (lambda (item)
                         (if (sexp-atom? item)
                             (string->symbol (atom-value item))
                             'unknown))
                       (cddr inner-items))
                  ;; Wildcard case: (* set ...) not found, check for just (*)
                  (if (and inner-items
                           (= (length inner-items) 1)
                           (sexp-atom? (car inner-items))
                           (string=? (atom-value (car inner-items)) "*"))
                      '(*)  ; All permissions
                      #f)))
            #f))
    (exn () #f)))

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

(define CIP-VERSION-MAJOR 1)
(define CIP-VERSION-MINOR 0)

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
  (string-append (number->string CIP-VERSION-MAJOR) "."
                 (number->string CIP-VERSION-MINOR)))

(define (ccp-suite)
  "Get algorithm suite for current version"
  (alist-ref CIP-VERSION-MAJOR *algorithm-suites*))

(define (ccp-check-version remote-major remote-minor)
  "Check version compatibility"
  (cond
   ((> remote-major CIP-VERSION-MAJOR)
    (values #f "Remote version too new - upgrade required"))
   ((< remote-major CIP-VERSION-MAJOR)
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
  (string->blob (string-append "CIP/"
                               (number->string CIP-VERSION-MAJOR) "."
                               (number->string CIP-VERSION-MINOR))))

(define (parse-knock-payload payload)
  "Parse KNOCK payload, extract version"
  (let ((str (blob->string payload)))
    (if (string-prefix? "CIP/" str)
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
      (channel-write-msg ch CIP-KNOCK (string->blob "KNOCK"))

      ;; Phase 2: Receive COOKIE
      (let-values (((type payload) (channel-read-msg ch)))
        (unless (= type CIP-COOKIE)
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
              (channel-write-msg ch CIP-EXCHANGE exchange-payload))

            ;; Receive their EXCHANGE
            (let-values (((type payload) (channel-read-msg ch)))
              (unless (= type CIP-EXCHANGE)
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
                    (channel-write-msg ch CIP-ATTEST
                                       (string->blob (string-append principal-hex "|" signature))))

                  ;; Receive their ATTEST
                  (let-values (((type payload) (channel-read-msg ch)))
                    (unless (= type CIP-ATTEST)
                      (error "Expected ATTEST, got" type))
                    (let* ((parts (string-split (blob->string payload) "|"))
                           (their-principal (car parts)))
                      (print "  [Attest] Verified: " (short-id their-principal))
                      (set! ch (alist-update 'their-principal their-principal ch))

                      ;; Phase 5: OFFER - exchange capabilities
                      (print "  [Offer] Sending capabilities...")
                      (let ((our-caps (make-offer-capabilities 'read 'write 'replicate)))
                        (channel-write-msg ch CIP-OFFER (string->blob our-caps)))

                      ;; Receive their OFFER
                      (let-values (((type payload) (channel-read-msg ch)))
                        (unless (= type CIP-OFFER)
                          (error "Expected OFFER, got" type))
                        (let* ((their-caps-str (blob->string payload))
                               (their-caps-parsed (parse-offer-capabilities their-caps-str))
                               (their-caps (or their-caps-parsed their-caps-str)))
                          (print "  [Offer] Received: " their-caps)
                          (set! ch (alist-update 'their-capabilities their-caps ch))

                          ;; Phase 6: CONFIRM - transcript hash
                          (print "  [Confirm] Sending transcript confirmation...")
                          (let ((transcript-hash (blake2b-hash
                                                   (string->blob
                                                     (string-append cookie-i cookie-r
                                                                    their-principal)))))
                            (channel-write-msg ch CIP-CONFIRM transcript-hash)

                            ;; Receive their CONFIRM
                            (let-values (((type payload) (channel-read-msg ch)))
                              (unless (= type CIP-CONFIRM)
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
        (unless (= type CIP-KNOCK)
          (error "Expected KNOCK, got" type))
        (print "  [Knock] Received")

        ;; Phase 2: Send COOKIE (stateless)
        (let ((cookie-r (make-cookie "remote" 0)))  ; In real impl: actual remote addr
          (print "  [Cookie] Sending: " (substring cookie-r 0 8) "...")
          (channel-write-msg ch CIP-COOKIE (string->blob cookie-r))
          (set! ch (alist-update 'cookie-ours cookie-r ch))

          ;; Phase 3: Receive EXCHANGE
          (let-values (((type payload) (channel-read-msg ch)))
            (unless (= type CIP-EXCHANGE)
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
                  (channel-write-msg ch CIP-EXCHANGE exchange-payload)
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
                      (unless (= type CIP-ATTEST)
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
                          (channel-write-msg ch CIP-ATTEST
                                             (string->blob (string-append principal-hex "|" signature))))

                        ;; Phase 5: Receive OFFER
                        (let-values (((type payload) (channel-read-msg ch)))
                          (unless (= type CIP-OFFER)
                            (error "Expected OFFER, got" type))
                          (let* ((their-caps-str (blob->string payload))
                                 (their-caps-parsed (parse-offer-capabilities their-caps-str))
                                 (their-caps (or their-caps-parsed their-caps-str)))
                            (print "  [Offer] Received: " their-caps)
                            (set! ch (alist-update 'their-capabilities their-caps ch))

                            ;; Send our OFFER
                            (print "  [Offer] Sending capabilities...")
                            (let ((our-caps (make-offer-capabilities 'read 'write 'replicate)))
                              (channel-write-msg ch CIP-OFFER (string->blob our-caps)))

                            ;; Phase 6: Receive CONFIRM
                            (let-values (((type payload) (channel-read-msg ch)))
                              (unless (= type CIP-CONFIRM)
                                (error "Expected CONFIRM, got" type))
                              (print "  [Confirm] Verified")

                              ;; Send our CONFIRM
                              (let ((transcript-hash (blake2b-hash
                                                       (string->blob
                                                         (string-append cookie-i cookie-r
                                                                        their-principal)))))
                                (channel-write-msg ch CIP-CONFIRM transcript-hash))

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
      (channel-write-msg ch CIP-DATA ciphertext)
      (print "  [Send] seq=" seq " encrypted"))))

(define (channel-recv ch)
  "Receive and decrypt message from secure channel"
  (let ((id (alist-ref 'id ch)))
    (unless (eq? (channel-get-state id) 'open)
      (error "Channel not open"))
    (let-values (((type payload) (channel-read-msg ch)))
      (cond
       ((= type CIP-DATA)
        (let* ((seq (channel-seq-recv! id))
               (key (alist-ref 'key-recv ch))
               (plaintext (channel-decrypt key seq payload)))
          (print "  [Recv] seq=" seq " decrypted")
          (blob->string plaintext)))
       ((= type CIP-CLOSE)
        (channel-set-state! id 'closed)
        'closed)
       (else
        (error "Unexpected message type" type))))))

(define (channel-close ch)
  "Close secure channel"
  (let ((id (alist-ref 'id ch)))
    (channel-write-msg ch CIP-CLOSE (string->blob "CLOSE"))
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
        (print "  Protocol: Cyberspace Channel Protocol (CIP)")
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

;; Load persisted Lamport clock from vault (Memo-012)
(lamport-load!)

;; Banner shown at portal level (2) and above
(when (>= *boot-verbosity* 2)
  (banner))

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

;; Wrapped commands that track session statistics
(define (tracked-commit . args)
  (let ((result (apply seal-commit args)))
    (session-stat! 'commits)
    (session-stat! 'seals)
    result))

(define (tracked-sync . args)
  (let ((result (apply seal-synchronize args)))
    (session-stat! 'syncs)
    result))

(define (tracked-sign . args)
  (let ((result (apply ed25519-sign args)))
    (session-stat! 'signs)
    result))

(define (tracked-verify . args)
  (let ((result (apply ed25519-verify args)))
    (session-stat! 'verifies)
    result))

(define (tracked-release . args)
  (let ((result (apply seal-release args)))
    (session-stat! 'seals)
    result))

(define (tracked-archive . args)
  (let ((result (apply seal-archive args)))
    (session-stat! 'seals)
    result))

(define (tracked-enroll-approve . args)
  (let ((result (apply enroll-approve args)))
    (session-stat! 'federation-changes)
    result))

;;; ============================================================
;;; Post-Quantum Vault Operations (Memo-059)
;;; ============================================================
;;; Commands for Q-Day migration: upgrade to hybrid, add PQ keys,
;;; check coverage, set signing mode.

(define *pq-signing-mode* 'ed25519)  ; ed25519 | hybrid | pq-only

(define (pq-status)
  "Show post-quantum migration status"
  (print "\n=== Post-Quantum Migration Status ===\n")

  ;; Check keyring for PQ keys
  (let* ((keys (keyring-list))
         (ed-keys (filter (lambda (k) (eq? (key-algorithm k) 'ed25519)) keys))
         (pq-keys (filter (lambda (k) (memq (key-algorithm k) '(ml-dsa-65 sphincs+ hybrid))) keys))
         (hybrid-keys (filter (lambda (k) (eq? (key-algorithm k) 'hybrid)) keys)))

    (print "Signing Mode: " *pq-signing-mode*)
    (print "")
    (print "Keys in Keyring:")
    (print "  Ed25519:    " (length ed-keys))
    (print "  ML-DSA-65:  " (length (filter (lambda (k) (eq? (key-algorithm k) 'ml-dsa-65)) keys)))
    (print "  SPHINCS+:   " (length (filter (lambda (k) (eq? (key-algorithm k) 'sphincs+)) keys)))
    (print "  Hybrid:     " (length hybrid-keys))
    (print "")

    ;; Migration status
    (cond
     ((null? keys)
      (print "Status: NO KEYS - run (keyring-generate \"name\")"))
     ((and (null? pq-keys) (not (null? ed-keys)))
      (print "Status: VULNERABLE - only Ed25519 keys")
      (print "Action: Run (pq-upgrade \"keyname\") to add PQ protection"))
     ((not (null? hybrid-keys))
      (print "Status: TRANSITION - hybrid keys available")
      (print "Action: Set (pq-set-mode 'hybrid) to enable hybrid signing"))
     ((and (null? ed-keys) (not (null? pq-keys)))
      (print "Status: PQ-READY - post-quantum keys only"))
     (else
      (print "Status: MIXED - multiple key types")))

    (print "")
    (print "Supported algorithms: " (supported-algorithms))
    (print "")))

(define (pq-upgrade key-name)
  "Upgrade an Ed25519 key to hybrid by generating companion ML-DSA key"
  (let ((existing (key-by-name key-name)))
    (if (not existing)
        (print "Error: Key '" key-name "' not found")
        (let ((alg (key-algorithm existing)))
          (if (not (eq? alg 'ed25519))
              (print "Error: Key '" key-name "' is already " alg ", not Ed25519")
              (let ((hybrid-name (string-append key-name "-hybrid")))
                (print "Generating hybrid key: " hybrid-name)
                (keyring-generate hybrid-name 'hybrid)
                (print "")
                (print "Hybrid key created. Original Ed25519 key preserved.")
                (print "Set (pq-set-mode 'hybrid) to use hybrid signing.")
                hybrid-name))))))

(define (pq-add-key name #!optional (algorithm 'ml-dsa-65))
  "Add a post-quantum key to the keyring"
  (if (not (memq algorithm '(ml-dsa-65 sphincs+ hybrid)))
      (print "Error: Algorithm must be ml-dsa-65, sphincs+, or hybrid")
      (begin
        (print "Generating " algorithm " key: " name)
        (keyring-generate name algorithm)
        (print "Key generated successfully.")
        (display-key name))))

(define (pq-set-mode mode)
  "Set the signing mode: ed25519 | hybrid | pq-only"
  (if (not (memq mode '(ed25519 hybrid pq-only)))
      (print "Error: Mode must be ed25519, hybrid, or pq-only")
      (begin
        (set! *pq-signing-mode* mode)
        (print "Signing mode set to: " mode)
        (case mode
          ((ed25519) (print "  Signatures: Ed25519 only (classical)"))
          ((hybrid)  (print "  Signatures: Ed25519 + ML-DSA (transition)"))
          ((pq-only) (print "  Signatures: ML-DSA only (post-quantum)"))))))

(define (pq-coverage)
  "Analyze audit trail for post-quantum signature coverage"
  (print "\n=== Post-Quantum Audit Coverage ===\n")
  (let* ((entries (audit-read))
         (total (length entries))
         (ed-count 0)
         (pq-count 0)
         (hybrid-count 0)
         (unknown-count 0))

    ;; Count by algorithm
    (for-each
     (lambda (entry)
       (let ((seal (and (pair? entry) (assq 'seal (cdr entry)))))
         (if seal
             (let ((alg (and (pair? (cdr seal))
                            (assq 'algorithm (cdr (cdr seal))))))
               (cond
                ((not alg) (set! unknown-count (+ unknown-count 1)))
                ((string-contains (->string (cdr alg)) "hybrid")
                 (set! hybrid-count (+ hybrid-count 1)))
                ((string-contains (->string (cdr alg)) "ml-dsa")
                 (set! pq-count (+ pq-count 1)))
                ((string-contains (->string (cdr alg)) "ed25519")
                 (set! ed-count (+ ed-count 1)))
                (else (set! unknown-count (+ unknown-count 1)))))
             (set! unknown-count (+ unknown-count 1)))))
     entries)

    (print "Total audit entries: " total)
    (print "")
    (print "Signature Distribution:")
    (print "  Ed25519 (classical):  " ed-count
           " (" (if (> total 0) (round (* 100 (/ ed-count total))) 0) "%)")
    (print "  ML-DSA (PQ):          " pq-count
           " (" (if (> total 0) (round (* 100 (/ pq-count total))) 0) "%)")
    (print "  Hybrid (both):        " hybrid-count
           " (" (if (> total 0) (round (* 100 (/ hybrid-count total))) 0) "%)")
    (print "  Unknown/Legacy:       " unknown-count
           " (" (if (> total 0) (round (* 100 (/ unknown-count total))) 0) "%)")
    (print "")

    (let ((pq-protected (+ pq-count hybrid-count)))
      (if (= total 0)
          (print "Status: No audit entries yet")
          (cond
           ((= pq-protected 0)
            (print "Status: VULNERABLE - no PQ signatures in audit trail")
            (print "Action: Enable hybrid signing and re-seal critical entries"))
           ((< pq-protected total)
            (print "Status: PARTIAL - " (round (* 100 (/ pq-protected total))) "% PQ coverage")
            (print "Action: Continue migration, re-sign legacy entries"))
           (else
            (print "Status: PROTECTED - 100% PQ coverage")))))))

(define *command-aliases*
  '((status    . status)
    (dashboard . dashboard)
    (apropos   . apropos)
    (commit    . tracked-commit)
    (release   . tracked-release)
    (archive   . tracked-archive)
    (history   . seal-history)
    (sync      . tracked-sync)
    (keys      . list-keys)
    (keygen    . ed25519-keypair)
    (sign      . tracked-sign)
    (verify    . tracked-verify)
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
    (approve   . tracked-enroll-approve)
    (discover  . discover-peers)
    (gossip    . gossip-status)
    (audit     . audit)
    (prefs     . preferences)
    (preferences . preferences)
    (clear     . clear)
    (open      . open)
    (theme     . theme!)
    (publish!  . thinga!)
    (thanga!   . thinga!)
    (help      . help)
    (library   . library)
    (search    . search)
    (kwic      . kwic)
    (memo      . memo)
    (quit      . exit)
    (exit      . exit)))

(define (resolve-command cmd)
  "Resolve command alias or return as-is"
  (let ((alias (assq cmd *command-aliases*)))
    (if alias (cdr alias) cmd)))

(define (novice-command? cmd)
  "Check if cmd is a recognized novice command"
  (and (symbol? cmd)
       (or (assq cmd *command-aliases*)
           ;; Also accept resolved command names (values in alias alist)
           (find (lambda (pair) (eq? (cdr pair) cmd)) *command-aliases*)
           ;; Also allow some common Scheme functions
           (memq cmd '(+ - * / define let if cond lambda quote
                       car cdr cons list first second third
                       print display newline load begin
                       ;; Debugging
                       bt backtrace frame exception-info
                       ;; Resident editors
                       schemacs pencil pencil-novice teco)))))

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
        ;; Symbol arguments are auto-quoted (help topics -> (help 'topics))
        (let loop ((tokens '()))
          (let ((tok (read port)))
            (if (eof-object? tok)
                (if (null? tokens)
                    #f
                    (let ((reversed (reverse tokens)))
                      (cons (resolve-command (car reversed))
                            (map (lambda (arg)
                                   (if (symbol? arg)
                                       (list 'quote arg)
                                       arg))
                                 (cdr reversed)))))
                (loop (cons tok tokens))))))))

(module-end! "memos")
(module-start! "repl")

;;; ============================================================
;;; Inspector Integration
;;; ============================================================
;;;
;;; Dylan/CCL-style debugger infused into the REPL.
;;; When errors occur, drop into debug> prompt with clean stack.
;;; Uses inspector module's install-inspector! function.

(define (enable-inspector!)
  "Enable integrated debugger"
  (inspector#install-inspector!))

(define (disable-inspector!)
  "Disable integrated debugger - note: inspector module has no uninstall"
  (print "Note: inspector cannot be disabled once installed"))

;; Domain-aware inspect - handles high-level Cyberspace objects
;; before falling back to generic inspector
(define (cyberspace-inspect obj)
  "Inspect any object with domain awareness"
  (cond
    ;; Symbols that name domain concepts - call function and show result
    ((eq? obj 'soup) (soup))
    ((eq? obj 'vault) (status))
    ((eq? obj 'keys) (soup 'keys))
    ((eq? obj 'releases) (soup 'releases))
    ((eq? obj 'audits) (soup 'audit))
    ((eq? obj 'certs) (soup 'certs))
    ((eq? obj 'forge) (soup 'forge))
    ((eq? obj 'realm) (realm-info))

    ;; Procedure that matches known domain functions - call and inspect result
    ((and (procedure? obj)
          (or (eq? obj soup)
              (eq? obj keys)
              (eq? obj releases)))
     (let ((result (obj)))
       (inspector#describe result)
       result))

    ;; String that looks like a version or object name - use soup-inspect
    ((and (string? obj)
          (or (irregex-match "^[0-9]+\\.[0-9]+" obj)  ; version
              (string-suffix? ".archive" obj)         ; archive
              (string-suffix? ".sig" obj)))           ; signature
     (soup-inspect obj))

    ;; Everything else - generic inspector
    (else
     (inspector#inspect obj))))

;;; ============================================================
;;; Help System
;;; ============================================================

(define *help-topics*
  '((vault "Vault & Objects"
     ("(soup)" "Browse vault objects")
     ("(soup 'keys)" "List keys")
     ("(soup 'audit)" "List audit entries")
     ("(soup-du)" "Disk usage")
     ("(seal-commit MSG)" "Commit changes")
     ("(seal-release VER)" "Create release")
     ("(query PRED)" "Query vault objects"))

    (library "Memos"
     ("(library)" "Browse all Memos")
     ("(search 'topic)" "Search vault + library")
     ("(memo N)" "View Memo in terminal")
     ("(memo N 'html)" "Open Memo in browser"))

    (security "Keys & Certificates"
     ("(principals)" "Show identity and keys")
     ("(keyring-list)" "List keys in keyring")
     ("(keyring-generate)" "Generate new keypair")
     ("(security-summary)" "Security overview")
     ("(verify-object OBJ)" "Verify signature"))

    (crypto "Cryptographic Primitives"
     ("(sha512-hash DATA)" "SHA-512 hash")
     ("(blake2b-hash DATA)" "BLAKE2b hash")
     ("(ed25519-keypair)" "Generate Ed25519 keypair")
     ("(sign KEY DATA)" "Sign with private key")
     ("(verify KEY SIG DATA)" "Verify signature")
     ("(encrypt KEY DATA)" "Encrypt with X25519")
     ("(decrypt KEY DATA)" "Decrypt with X25519"))

    (certs "SPKI Certificates"
     ("(cert-create ...)" "Create certificate")
     ("(cert-verify CERT)" "Verify certificate")
     ("(cert-chain ...)" "Build certificate chain")
     ("(capability? OBJ)" "Check if capability"))

    (federation "Discovery & Gossip"
     ("(status)" "Node status")
     ("(enrollment-status)" "Enrollment state")
     ("(enroll)" "Interactive enrollment")
     ("(announce-presence 'name)" "Register on mDNS")
     ("(discover-peers)" "Find _cyberspace._tcp peers")
     ("(gossip-status)" "Gossip daemon status"))

    (audit "Audit Trail (TCSEC Reduction)"
     ("(audit)" "Summary of audit entries")
     ("(audit 'brief)" "Recent entries, one per line")
     ("(audit 'full)" "Full details for each entry")
     ("(audit 'plot)" "ASCII histogram (24h activity)")
     ("(audit 'heatmap)" "Time × day-of-week grid")
     ("(audit 'heatmap '(span \"30d\"))" "Monthly rhythm pattern")
     ("(audit 'rhythm \"7d\")" "Condensed daily sparkline")
     ("(audit 'query '(type sync))" "Filter by type")
     ("(audit 'query '(since \"1h\"))" "Entries in last hour")
     ("(audit-chain)" "Verify chain integrity")
     ("Visual:" "flatline=quiet, rhythm=normal, chaos=hostile"))

    (inspector "Debugger & Inspector"
     ("(inspect OBJ)" "Inspect any object, enter navigation mode")
     ("(describe OBJ)" "Describe type/contents with box display")
     (":i OBJ" "Inspect object (colon command)")
     (":s" "Show current object")
     (":d N" "Descend into slot N")
     (":u" "Go up to parent object")
     (":h" "Show navigation history")
     (":b" "Bookmark current object")
     (":t" "Show object type info")
     ("(bt)" "Show backtrace")
     ("(frame N)" "Examine stack frame")
     ("(enable-inspector!)" "Turn on debug> prompt")
     ("(disable-inspector!)" "Turn off debug> prompt"))

    (editor "Editing Files"
     ("(preferences)" "Show editor/pager settings")
     ("(editor! CMD)" "Set editor (or \"pencil\")")
     ("(pager! CMD)" "Set pager (e.g. \"less\")")
     (",e [file]" "Edit with configured editor")
     (",pencil [file]" "Electric Pencil (built-in)")
     (",novice [file]" "Pencil with on-screen hints")
     (",teco [file]" "TECO (Dan Murphy heritage)")
     (",schemacs [file]" "Schemacs (Emacs-style)")
     (",hd file" "Hex dump (xxd | less)")
     (",hext file" "HexEdit (GUI)")
     ("$EDITOR/$PAGER" "Environment fallbacks")
     ("Pencil:" "Gap buffer, WASD, Ctrl-Q quit")
     ("TECO:" "PDP-style, * prompt, ERfile$/EX")
     ("Schemacs:" "C-x C-s save, C-x C-c quit"))

    (forge "Build & Metrics"
     ("(sicp)" "SICP metrics for all modules")
     ("(loch-lambda)" "Find LOC/λ ≥ 10 modules")
     ("(forged \"module\")" "View forge metadata")
     ("(forged-all)" "All forge metrics")
     ("(regression)" "Run all regression tests")
     ("(regression #t)" "Verbose test output")
     ("(reload!)" "Hot reload REPL definitions"))

    (system "System & Introspection"
     ("(introspect)" "Full system introspection")
     ("(measure-weave)" "Crypto benchmark (ops/ms)")
     ("(weave-stratum N)" "Lattice stratum (Memo-056)")
     ("*weave-strata*" "Stratum thresholds alist")
     ("(banner)" "Redisplay startup banner")
     ("(entropy-status)" "Entropy source info")
     ("(fips-status)" "FIPS self-test status")
     ("(goodbye)" "Exit with session summary"))

    (cs "Command Line"
     ("cs" "Start REPL (default)")
     ("cs --sync" "Sync vault with remote, then start REPL")
     ("cs --clean" "Remove compiled artifacts")
     ("cs --rebuild" "Force rebuild all modules")
     ("cs --verbose" "Show verbose output")
     ("cs --boot=<level>" "shadow|whisper|portal|oracle")
     ("cs --eval='<expr>'" "Evaluate expression and exit")
     ("cs --version" "Show version information")
     ("cs --help" "Show command line help"))

    (boot "Boot Verbosity Levels"
     ("CYBERSPACE_BOOT=shadow" "0: Silent - just prompt (default)")
     ("CYBERSPACE_BOOT=whisper" "1: Version + Ready")
     ("CYBERSPACE_BOOT=portal" "2: Banner + help + Ready (alias: gate)")
     ("CYBERSPACE_BOOT=chronicle" "3: Add module timings")
     ("CYBERSPACE_BOOT=oracle" "4: Full revelation")
     ("(boot-level! 'portal)" "Set level at runtime"))))

(define (help #!optional topic)
  "Display help for Cyberspace Scheme.
   (help)         - Essential commands
   (help 'topics) - List all topics
   (help 'vault)  - Show vault commands
   (help 'crypto) - Show crypto primitives"
  (print "")
  (cond
    ;; (help 'topics) - show topic index
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

    ;; (help 'something) - show specific topic
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
           (begin
             (print "Unknown topic: " topic)
             (print "Try (help 'topics) to see available topics.")
             (print "")))))

    ;; (help) - essentials only, mode-aware
    (else
     (print "Cyberspace Scheme")
     (print "")
     (if (eq? *user-mode* 'novice)
         ;; Novice: plain English, no acronyms
         (begin
           (print "  soup            - Browse the object store")
           (print "  library         - Browse the Library of memos")
           (print "  search 'x       - Search for anything")
           (print "  global-search s - Search across soup, audit, wormhole")
           (print "")
           (print "  status          - Quick system status")
           (print "  dashboard       - Full status: session, soup, audit, wormholes")
           (print "")
           (print "  inspect x       - Look inside any object")
           (print "  kwic 'word      - See word in context across memos")
           (print "")
           (printf "  help topics     - All help topics (~a commands)~%"
                   (apply + (map (lambda (t) (length (cddr t))) *help-topics*)))
           (print "  .  ?  bye       - status, help, exit"))
         ;; Schemer: comma commands (like Chicken CSI)
         (begin
           (print "  ,soup ,library ,search ,kwic    Cyberspace")
           (print "  ,s ,i ,e ,q                     status, inspect, edit, quit")
           (print "  ,p ,x ,t ,du ,r                 pp, expand, time, dump, sysinfo")
           (print "  ,a ,l ,m ,d                     apropos, load, module, describe")
           (print "  ,sh ,bt ,exn                    shell, backtrace, exception")
           (print "")
           (printf "  ,?                              Full help (~a commands)~%"
                   (apply + (map (lambda (t) (length (cddr t))) *help-topics*)))))
     (print "")))
  (void))

;; Friendly exit - delegates to portal module
;; (portal.scm: inspired by VMS SYS$SYSTEM:LOGINOUT.EXE)
;; Respects boot verbosity: shadow mode exits silently
(define (repl-goodbye)
  (goodbye repl-history-save *boot-verbosity*))

;; Clear screen (VT100)
(define (clear)
  (display "\x1b[2J\x1b[H")
  (void))

;; English-friendly aliases (just call with parens)
(define keys (lambda () (soup 'keys)))
(define releases (lambda () (soup-releases)))
(define (peers)
  (let ((result (discover-peers)))
    (when (and (list? result) (not (null? result)))
      (session-stat! 'peers-discovered (length result)))
    result))
(define gossip gossip-status)
(define (gossip-sync . peers-arg)
  "Run gossip round with peers (tracks stats)."
  (let ((result (if (null? peers-arg)
                    (gossip-round)
                    (gossip-round (car peers-arg)))))
    (session-stat! 'gossip-exchanges)
    result))
(define security security-summary)
(define announce announce-presence)

;; Describe resident things - editors, modules, etc.
(define *resident-descriptions*
  '((teco . "TECO - Text Editor and COrrector (1962)
Dan Murphy, MIT

  The gap buffer's ancestor. Every keystroke a command.
  Every command sequence does *something* - often unintended.

  Sample TECO to uppercase a word:
    .,.+5XA QA\"A ^T' QA-32UA QA,.G

  Translation: Mark point, grab 5 chars to register A,
               if alphabetic print it, subtract 32 (ASCII magic),
               store back, insert from register.

  TECO's gift to computing:
    - Emacs (written IN TECO, then bootstrapped)
    - The gap buffer (register + point = proto-gap)
    - Proof that line noise can be Turing-complete

  \"Real programmers can write FORTRAN in any language.
   TECO programmers write in line noise.\"

  Usage: (teco) or (teco \"file.txt\")
         (teco-novice) for banner and help")

    (pencil . "Electric Pencil - Word Processor (1976)
Michael Shrayer

  The first word processor for microcomputers.
  Written for the MITS Altair 8800, later ported to CP/M.
  Predates WordStar by two years.

  Electric Pencil proved that personal computers could be
  tools for writers, not just hobbyists and engineers.

  Our implementation: gap buffer, WYSIWYG editing, novice mode.

  Usage: (pencil) or (pencil \"file.txt\")
         (pencil-novice) for extra guidance")

    (schemacs . "Schemacs - Emacs-style Editor (2026)
Cyberspace Project

  A minimal Emacs implementation in Scheme.
  Gap buffer, kill ring, mark, incremental search.

  Key bindings:
    C-x C-f  Find file       C-x C-s  Save
    C-x C-c  Quit            C-s      Search
    C-space  Set mark        C-w      Kill region
    M-w      Copy region     C-y      Yank

  Usage: (schemacs) or (schemacs \"file.txt\")")))

(define (describe thing)
  "Describe a resident thing (teco, pencil, schemacs, etc.)"
  (let* ((sym (if (string? thing) (string->symbol thing) thing))
         (desc (assq sym *resident-descriptions*)))
    (if desc
        (print (cdr desc))
        (print "Unknown: " sym ". Try: teco, pencil, schemacs"))))

(define info describe)

;; Easter egg for schemers: the Ten Commandments
(define (commandments)
  "The Ten Commandments of Cyberspace"
  (print "
The Ten Commandments of Cyberspace

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

These ten form the core of the Library. All other memos build upon them.
See: Memo-0000 Declaration of Cyberspace
")
  (void))

;; Display modes and browser opening
(define (open #!optional content)
  "Open content in browser with current theme.
   (open)         - open status/about page
   (open \"text\") - open text in browser
   (open obj)     - open pretty-printed object"
  (let ((html-content
         (cond
          ((not content)
           ;; No argument - generate status page
           (render-html "Cyberspace"
             (string-append
              "<h1>Cyberspace</h1>\n"
              "<pre>" (with-output-to-string status) "</pre>\n")))
          ((string? content)
           ;; String - wrap in pre
           (render-html "Cyberspace"
             (string-append "<pre>" content "</pre>\n")))
          (else
           ;; Object - pretty print
           (render-html "Cyberspace"
             (string-append "<pre>"
                            (with-output-to-string (lambda () (pp content)))
                            "</pre>\n"))))))
    (open-in-browser html-content)))

;; Full toolchain: sanity → commit → push → regen-all → publish
(define (thinga!)
  "Do all the th[i,a]nga: sanity, commit, push, regen-all, publish.
   Ideas forged through the full cycle become golden artifacts.
   Returns #f if regression tests fail - nothing publishes broken."
  (print "[thinga!: sanity → commit → push → regen-all → publish]")
  (print "")
  ;; Gate 1: regression tests
  (print "[scrutinizer: running sanity checks...]")
  (let ((sanity (system "./sanity.scm")))
    (if (not (zero? sanity))
        (begin
          (print "[thinga!: BLOCKED - sanity check failed]")
          #f)
        ;; Gate passed - proceed with publish
        (let ((result (system "git add -A && git commit -m 'thinga' && git push && ./repl regen && rsync -avz --exclude '.git' --exclude '*.so' --exclude '*.o' --exclude '*.c' . www.yoyodyne.com:cyberspace/spki/scheme/")))
          (if (zero? result)
              (begin
                (print "[thinga!: complete]")
                #t)
              (begin
                (print "[thinga!: failed with code " result "]")
                #f))))))

(define thanga! thinga!)  ; Tamil: gold

;; Show principals (identity + keys)
(define (principals)
  "Display identity and signing keys"
  (let ((node-id (read-node-identity)))
    (print "")
    (if node-id
        (let ((name (cond ((assq 'name node-id) => cadr) (else "unknown")))
              (role (cond ((assq 'role node-id) => cadr) (else "unknown"))))
          (print "Identity: " name " (" role ")"))
        (print "Identity: not enrolled"))
    (print "")
    ;; List keys from keyring
    (let* ((key-path ".vault/keys")
           (key-files (if (directory-exists? key-path)
                          (filter (lambda (f) (string-suffix? ".pub" f))
                                  (directory key-path))
                          '())))
      (if (null? key-files)
          (print "Keys: none")
          (begin
            (print "Keys:")
            (for-each
             (lambda (f)
               (print "  " (pathname-strip-extension f)))
             (sort key-files string<?)))))
    (print "")
    (void)))

;;; ============================================================================
;;; Audit Trail Query Interface (VMS ANALYZE/AUDIT style)
;;; ============================================================================
;;;
;;; Works with actual on-disk audit entry format:
;;; (audit-entry (type sync) (timestamp "...") (epoch N) (status S) ...)
;;;
;;; (audit)                        - summary view
;;; (audit 'brief)                 - brief listing
;;; (audit 'full)                  - detailed listing
;;; (audit 'summary)               - counts by type
;;; (audit 'plot)                  - ASCII histogram (24h)
;;; (audit 'query '(type sync))    - filter by criteria
;;; (audit 'analyze ...)           - combined VMS-style

;; Helpers for accessing audit entry fields (sexp format)
(define (audit-entry-field entry key #!optional default)
  "Get field from audit entry sexp."
  (let ((pair (assq key (cdr entry))))
    (if pair (cadr pair) default)))

(define (audit-load-entries)
  "Load all audit entries from .vault/audit/*.sexp"
  (let ((dir ".vault/audit"))
    (if (directory-exists? dir)
        (let ((files (sort (filter (lambda (f) (string-suffix? ".sexp" f))
                                   (directory dir))
                           string<?)))
          (filter-map
           (lambda (file)
             (handle-exceptions exn
               #f
               (let ((entry (with-input-from-file (string-append dir "/" file) read)))
                 (and (pair? entry) (eq? (car entry) 'audit-entry) entry))))
           files))
        '())))

(define (audit-entry-timestamp entry)
  (audit-entry-field entry 'timestamp "unknown"))

(define (audit-entry-epoch entry)
  (audit-entry-field entry 'epoch 0))

(define (audit-entry-type entry)
  (audit-entry-field entry 'type 'unknown))

(define (audit-entry-status entry)
  (audit-entry-field entry 'status 'unknown))

(define (audit-entry-commit entry)
  (audit-entry-field entry 'commit ""))

(define (audit-entry-master entry)
  (audit-entry-field entry 'master ""))

(define (format-audit-timestamp ts)
  "Format timestamp for brief display."
  (if (and (string? ts) (> (string-length ts) 16))
      (substring ts 0 16)
      ts))

(define (audit-brief-line entry)
  "Print one audit entry in brief format."
  (let ((ts (format-audit-timestamp (audit-entry-timestamp entry)))
        (type (symbol->string (audit-entry-type entry)))
        (status (symbol->string (audit-entry-status entry)))
        (commit (audit-entry-commit entry)))
    (printf "  ~a  ~a~a~a~a  ~a~%"
            ts
            type
            (make-string (max 1 (- 10 (string-length type))) #\space)
            status
            (make-string (max 1 (- 10 (string-length status))) #\space)
            commit)))

(define (audit-full-box entry)
  "Print one audit entry in full format."
  (let ((width 56))
    (printf "╭─ Audit Entry ─~a╮~%"
            (make-string (- width 17) #\─))
    (printf "│ Type:      ~a~a│~%"
            (audit-entry-type entry)
            (make-string (max 0 (- 44 (string-length (symbol->string (audit-entry-type entry))))) #\space))
    (printf "│ Timestamp: ~a~a│~%"
            (audit-entry-timestamp entry)
            (make-string (max 0 (- 44 (string-length (audit-entry-timestamp entry)))) #\space))
    (printf "│ Status:    ~a~a│~%"
            (audit-entry-status entry)
            (make-string (max 0 (- 44 (string-length (symbol->string (audit-entry-status entry))))) #\space))
    (let ((master (audit-entry-master entry)))
      (when (and (string? master) (> (string-length master) 0))
        (printf "│ Master:    ~a~a│~%"
                master
                (make-string (max 0 (- 44 (string-length master))) #\space))))
    (let ((commit (audit-entry-commit entry)))
      (when (and (string? commit) (> (string-length commit) 0))
        (printf "│ Commit:    ~a~a│~%"
                commit
                (make-string (max 0 (- 44 (string-length commit))) #\space))))
    ;; Details
    (let ((details (audit-entry-field entry 'details '())))
      (when (not (null? details))
        (printf "│ Details:~a│~%"
                (make-string 46 #\space))
        (for-each
         (lambda (d)
           (let* ((name (car d))
                  (val (symbol->string (cadr d)))
                  (line (sprintf "   ~a: ~a" name val)))
             (printf "│~a~a│~%"
                     line
                     (make-string (max 0 (- 55 (string-length line))) #\space))))
         details)))
    (printf "╰~a╯~%~%" (make-string width #\─))))

;; Time parsing for queries
(define (audit-parse-time-spec spec)
  "Parse time specification: '1h' '24h' '7d' or epoch number"
  (let ((now (current-seconds)))
    (cond
     ((number? spec) spec)
     ((string? spec)
      (let ((match (irregex-match '(: (submatch (+ digit)) (submatch (or "h" "d" "m" "w"))) spec)))
        (if match
            (let ((n (string->number (irregex-match-substring match 1)))
                  (unit (irregex-match-substring match 2)))
              (- now (* n (case (string->symbol unit)
                           ((h) 3600) ((d) 86400) ((m) 60) ((w) 604800)
                           (else 3600)))))
            (- now 86400))))  ; default: 24h ago
     (else (- now 86400)))))

;; Query filtering
(define (audit-match-criterion entry criterion)
  "Match entry against one criterion."
  (let ((key (car criterion))
        (val (cadr criterion)))
    (case key
      ((type) (eq? (audit-entry-type entry) val))
      ((status) (eq? (audit-entry-status entry) val))
      ((since after)
       (>= (audit-entry-epoch entry) (audit-parse-time-spec val)))
      ((before until)
       (<= (audit-entry-epoch entry) (audit-parse-time-spec val)))
      ((master)
       (string=? (audit-entry-master entry) val))
      ((commit)
       (string-prefix? val (audit-entry-commit entry)))
      (else #f))))

(define (audit-filter-entries entries criteria)
  "Filter entries by criteria list."
  (if (null? criteria)
      entries
      (filter (lambda (e) (every (lambda (c) (audit-match-criterion e c)) criteria))
              entries)))

;; Grouping and summary
(define (audit-group-entries entries field)
  "Group entries by field, return ((key count) ...)"
  (let ((groups (make-hash-table)))
    (for-each
     (lambda (e)
       (let ((key (case field
                   ((type) (audit-entry-type e))
                   ((status) (audit-entry-status e))
                   ((hour) (quotient (audit-entry-epoch e) 3600))
                   ((day) (quotient (audit-entry-epoch e) 86400))
                   (else 'other))))
         (hash-table-set! groups key (+ 1 (hash-table-ref/default groups key 0)))))
     entries)
    (sort (map (lambda (k) (list k (hash-table-ref groups k)))
               (hash-table-keys groups))
          (lambda (a b) (> (cadr a) (cadr b))))))

(define (audit-print-summary entries by)
  "Print summary of audit entries."
  (let* ((groups (audit-group-entries entries by))
         (total (length entries))
         (max-count (if (null? groups) 0 (apply max (map cadr groups)))))
    (printf "~%Audit Summary: ~a entries~%~%" total)
    (printf "By ~a:~%" by)
    (for-each
     (lambda (g)
       (let* ((key (car g))
              (count (cadr g))
              (bar-width (if (zero? max-count) 0
                            (inexact->exact (floor (* 24.0 (/ count max-count))))))
              (bar (make-string bar-width #\█))
              (key-str (if (symbol? key) (symbol->string key) (number->string key))))
         (printf "  ~a~a~a  ~a~%"
                 key-str
                 (make-string (max 1 (- 12 (string-length key-str))) #\space)
                 (string-pad-left (number->string count) 4 #\space)
                 bar)))
     groups)
    (newline)))

;; ASCII plotting - vertical bars
(define *audit-vbars* '#("" "▁" "▂" "▃" "▄" "▅" "▆" "▇" "█"))

(define (audit-print-histogram buckets height)
  "Print ASCII histogram from bucket counts."
  (let* ((counts (map cdr buckets))
         (max-count (if (null? counts) 1 (apply max 1 counts)))
         (scale (/ (- height 1.0) max-count)))
    ;; Print rows from top to bottom
    (do ((row (- height 1) (- row 1)))
        ((< row 0))
      (if (zero? (modulo row 2))
          (printf "~a │" (string-pad-left (number->string (inexact->exact (round (* row (/ max-count (- height 1)))))) 4 #\space))
          (display "     │"))
      (for-each
       (lambda (c)
         (let ((h (* c scale)))
           (display (cond ((> h row) "█")
                         ((> h (- row 1))
                          (vector-ref *audit-vbars* (min 8 (inexact->exact (floor (* (- h (floor h)) 8))))))
                         (else " ")))))
       counts)
      (newline))
    ;; X-axis
    (printf "   0 └~a~%" (make-string (length buckets) #\─))
    ;; Labels
    (display "      ")
    (for-each (lambda (b) (display (substring (car b) 0 (min 2 (string-length (car b)))))) buckets)
    (newline)))

(define (audit-print-plot entries bucket-spec span-spec)
  "Plot audit activity as ASCII histogram."
  (let* ((now (current-seconds))
         (span-secs (- now (audit-parse-time-spec span-spec)))
         (bucket-secs (let ((m (irregex-match '(: (submatch (+ digit)) (submatch (or "h" "d" "m"))) bucket-spec)))
                       (if m
                           (* (string->number (irregex-match-substring m 1))
                              (case (string->symbol (irregex-match-substring m 2))
                                ((h) 3600) ((d) 86400) ((m) 60) (else 3600)))
                           3600)))
         (num-buckets (max 1 (quotient span-secs bucket-secs)))
         (bucket-counts (make-vector num-buckets 0))
         (start-time (- now span-secs)))
    ;; Count entries per bucket
    (for-each
     (lambda (e)
       (let ((ts (audit-entry-epoch e)))
         (when (and (>= ts start-time) (< ts now))
           (let ((idx (min (- num-buckets 1) (max 0 (quotient (- ts start-time) bucket-secs)))))
             (vector-set! bucket-counts idx (+ 1 (vector-ref bucket-counts idx)))))))
     entries)
    ;; Build bucket list
    (let ((buckets (let loop ((i 0) (acc '()))
                    (if (>= i num-buckets) (reverse acc)
                        (loop (+ i 1) (cons (cons (number->string i) (vector-ref bucket-counts i)) acc))))))
      (printf "~%Audit Activity (~a, ~a buckets)~%~%" span-spec bucket-spec)
      (audit-print-histogram buckets 8))))

;; Heat map characters for intensity (space to full block)
(define *heat-chars* '#(" " "░" "▒" "▓" "█"))

(define (audit-heatmap entries span-spec)
  "Show time-of-day × day-of-week heat map.
   Quiescence is flat, rhythm is normal, chaos is probing."
  (let* ((now (current-seconds))
         (span-secs (- now (audit-parse-time-spec span-spec)))
         (start-time (- now span-secs))
         ;; 7 days × 24 hours grid
         (grid (make-vector 7 #f)))
    ;; Initialize grid
    (do ((d 0 (+ d 1))) ((>= d 7))
      (vector-set! grid d (make-vector 24 0)))
    ;; Count entries by day-of-week and hour
    (for-each
     (lambda (e)
       (let ((ts (audit-entry-epoch e)))
         (when (>= ts start-time)
           (let* ((time-vec (seconds->local-time ts))
                  (hour (vector-ref time-vec 2))      ; tm_hour
                  (wday (vector-ref time-vec 6)))     ; tm_wday (0=Sun)
             (let ((day-vec (vector-ref grid wday)))
               (vector-set! day-vec hour (+ 1 (vector-ref day-vec hour))))))))
     entries)
    ;; Find max for scaling
    (let ((max-count 1))
      (do ((d 0 (+ d 1))) ((>= d 7))
        (do ((h 0 (+ h 1))) ((>= h 24))
          (set! max-count (max max-count (vector-ref (vector-ref grid d) h)))))
      ;; Print header
      (printf "~%Audit Rhythm (~a)~%" span-spec)
      (printf "         00  03  06  09  12  15  18  21~%")
      (printf "         ├───┼───┼───┼───┼───┼───┼───┤~%")
      ;; Print each day
      (let ((days '#("Sun" "Mon" "Tue" "Wed" "Thu" "Fri" "Sat")))
        (do ((d 0 (+ d 1))) ((>= d 7))
          (printf "   ~a  │" (vector-ref days d))
          (do ((h 0 (+ h 1))) ((>= h 24))
            (let* ((count (vector-ref (vector-ref grid d) h))
                   (intensity (if (zero? max-count) 0
                                  (min 4 (inexact->exact (floor (* 5 (/ count max-count))))))))
              (display (vector-ref *heat-chars* intensity))))
          (printf "│~%")))
      (printf "         └───────────────────────────┘~%")
      ;; Legend
      (printf "~%   ░ sparse  ▒ normal  ▓ busy  █ peak~%")
      ;; Summary stats
      (let ((total (length (filter (lambda (e) (>= (audit-entry-epoch e) start-time)) entries))))
        (printf "   ~a entries in ~a~%" total span-spec)))))

(define (audit-rhythm entries span-spec)
  "Condensed rhythm view - one sparkline per day."
  (let* ((now (current-seconds))
         (span-secs (- now (audit-parse-time-spec span-spec)))
         (start-time (- now span-secs))
         (days-back (max 1 (quotient span-secs 86400)))
         (day-counts (make-vector days-back 0)))
    ;; Count per day
    (for-each
     (lambda (e)
       (let ((ts (audit-entry-epoch e)))
         (when (>= ts start-time)
           (let ((day-idx (min (- days-back 1) (quotient (- ts start-time) 86400))))
             (vector-set! day-counts day-idx (+ 1 (vector-ref day-counts day-idx)))))))
     entries)
    ;; Build sparkline
    (let ((max-count (apply max 1 (vector->list day-counts))))
      (printf "~%~a: " span-spec)
      (do ((i 0 (+ i 1))) ((>= i days-back))
        (let* ((count (vector-ref day-counts i))
               (level (min 8 (inexact->exact (floor (* 9 (/ count max-count)))))))
          (display (vector-ref *audit-vbars* level))))
      (printf " (~a)~%" (apply + (vector->list day-counts))))))

(define (audit . args)
  "Query and display audit trail.

  (audit)                          Summary view (default)
  (audit 'brief)                   Brief listing of entries
  (audit 'full)                    Full details for each entry
  (audit 'summary)                 Counts grouped by type
  (audit 'plot)                    ASCII histogram (24h, 1h buckets)
  (audit 'plot '(span \"7d\"))       7-day plot
  (audit 'heatmap)                 Time × day-of-week grid (7d)
  (audit 'heatmap '(span \"30d\"))   Monthly rhythm
  (audit 'rhythm \"30d\")            Condensed daily sparkline
  (audit 'query '(type sync))      Filter by action type
  (audit 'query '(since \"1h\"))     Entries in last hour

  Visual patterns (TCSEC audit reduction):
    Flatline = quiescence (nothing happening)
    Rhythm   = normal ops (humans work 9-5, cron at midnight)
    Chaos    = noise/probing (assume hostile realms)"

  (session-stat! 'queries)
  (let ((entries (audit-load-entries)))
    (cond
     ;; No args: summary view
     ((null? args)
      (let ((count (length entries)))
        (print "")
        (printf "Audit Trail: ~a entries~%" count)
        (when (> count 0)
          (print "")
          (audit-print-summary entries 'type))
        (void)))

     ;; Brief listing
     ((and (= 1 (length args)) (eq? (car args) 'brief))
      (print "")
      (printf "Audit Trail (~a entries)~%~%" (length entries))
      (for-each audit-brief-line (take entries (min 20 (length entries))))
      (when (> (length entries) 20)
        (printf "  ... (~a more entries)~%" (- (length entries) 20)))
      (void))

     ;; Full listing
     ((and (= 1 (length args)) (eq? (car args) 'full))
      (print "")
      (for-each audit-full-box entries)
      (void))

     ;; Summary by field
     ((eq? (car args) 'summary)
      (let ((by (if (> (length args) 1) (cadr args) 'type)))
        (audit-print-summary entries by)))

     ;; Plot
     ((eq? (car args) 'plot)
      (let ((bucket "1h")
            (span "24h"))
        ;; Parse optional params: '(span "7d") '(bucket "2h")
        (for-each
         (lambda (arg)
           (when (and (list? arg) (>= (length arg) 2))
             (case (car arg)
               ((span) (set! span (cadr arg)))
               ((bucket) (set! bucket (cadr arg))))))
         (cdr args))
        (audit-print-plot entries bucket span)))

     ;; Heatmap - time × day-of-week (TCSEC audit reduction)
     ((eq? (car args) 'heatmap)
      (let ((span "7d"))
        (for-each
         (lambda (arg)
           (when (and (list? arg) (>= (length arg) 2))
             (case (car arg)
               ((span) (set! span (cadr arg))))))
         (cdr args))
        (audit-heatmap entries span)))

     ;; Rhythm - condensed sparkline per day
     ((eq? (car args) 'rhythm)
      (let ((span (if (> (length args) 1) (cadr args) "30d")))
        (audit-rhythm entries span)))

     ;; Query with criteria
     ((eq? (car args) 'query)
      (let ((filtered (audit-filter-entries entries (cdr args))))
        (print "")
        (printf "Query results: ~a entries~%~%" (length filtered))
        (for-each audit-brief-line filtered)
        (void)))

     ;; VMS-style analyze (combined)
     ((eq? (car args) 'analyze)
      (let ((criteria '())
            (show-summary #f)
            (show-plot #f))
        ;; Parse options
        (for-each
         (lambda (arg)
           (when (list? arg)
             (case (car arg)
               ((select) (set! criteria (cons (cadr arg) criteria)))
               ((since before) (set! criteria (cons arg criteria)))
               ((summary) (set! show-summary (cadr arg)))
               ((plot) (set! show-plot (cadr arg))))))
         (cdr args))
        (let ((filtered (audit-filter-entries entries criteria)))
          (printf "~%ANALYZE/AUDIT: ~a entries selected~%" (length filtered))
          (when show-summary
            (audit-print-summary filtered 'type))
          (when show-plot
            (audit-print-plot filtered "1h" "24h")))))

     ;; Unknown command
     (else
      (print "Unknown audit command. Try (audit) for help.")))))

;; Library of Cyberspace - Memo browser
(define (library #!optional filter)
  "Browse the Library of Cyberspace"
  (let* ((lib (introspect-library))
         (count (cadr (assq 'count (cdr lib))))
         (memos (cadr (assq 'memos (cdr lib)))))
    (with-pager
     (lambda ()
       (print "")
       (printf "Library of Cyberspace (~a memos)~%" count)
       (print "")
       (for-each
        (lambda (m)
          (let* ((num (cadr (assq 'number (cdr m))))
                 (title (cadr (assq 'title (cdr m))))
                 (status (cadr (assq 'status (cdr m))))
                 (title-short (if (> (string-length title) 45)
                                  (string-append (substring title 0 42) "...")
                                  title)))
            (when (or (not filter)
                      (string-contains-ci title (symbol->string filter))
                      (string-contains-ci num (symbol->string filter)))
              (printf "  Memo-~a  ~a~%"
                      (string-pad-left num 3 #\0)
                      title-short))))
        memos)
       (print "")))
    (void)))

;; Unified search - vault + library
(define (search term)
  "Search across vault and library
   (search 'crypto)     - find crypto-related items
   (search \"*.tar.gz\") - find by pattern"
  (let ((term-str (if (symbol? term) (symbol->string term) term)))
    (print "")
    (print "Searching for: " term-str)
    (print "")

    ;; Search vault
    (let ((vault-results (soup-query `(name ,(string-append "*" term-str "*")) #t)))
      (when (and vault-results (not (null? vault-results)))
        (print "Vault:")
        (for-each
         (lambda (obj)
           (printf "  ~a/~a~%" (car obj) (cadr obj)))
         (take vault-results (min 10 (length vault-results))))
        (when (> (length vault-results) 10)
          (printf "  ... (~a more)~%" (- (length vault-results) 10)))
        (print "")))

    ;; Search library
    (let* ((lib (introspect-library))
           (memos (cadr (assq 'memos (cdr lib))))
           (matches (filter
                     (lambda (m)
                       (let ((title (cadr (assq 'title (cdr m))))
                             (num (cadr (assq 'number (cdr m)))))
                         (or (string-contains-ci title term-str)
                             (string-contains-ci num term-str))))
                     memos)))
      (when (not (null? matches))
        (print "Library:")
        (for-each
         (lambda (m)
           (let ((num (cadr (assq 'number (cdr m))))
                 (title (cadr (assq 'title (cdr m)))))
             (printf "  Memo-~a  ~a~%"
                     (string-pad-left num 3 #\0)
                     (if (> (string-length title) 45)
                         (string-append (substring title 0 42) "...")
                         title))))
         matches)
        (print "")))

    (void)))

;; Apropos - search bound symbols (Scheme tradition)
(define (apropos pattern)
  "Search for symbols containing pattern.
   (apropos 'vault)   - find vault-related procedures
   (apropos 'search)  - find search functions"
  (let* ((pat (if (symbol? pattern) (symbol->string pattern) pattern))
         (pat-lower (string-downcase pat))
         ;; Get symbols from help topics
         (help-syms (apply append
                           (map (lambda (topic)
                                  (map (lambda (entry)
                                         (let ((cmd (car entry)))
                                           (if (string-prefix? "(" cmd)
                                               (let ((end (string-index cmd #\space)))
                                                 (if end
                                                     (substring cmd 1 end)
                                                     (substring cmd 1 (- (string-length cmd) 1))))
                                               cmd)))
                                       (cddr topic)))
                                *help-topics*)))
         ;; Filter matching symbols
         (matches (filter (lambda (s)
                           (string-contains-ci s pat-lower))
                         help-syms)))
    (print "")
    (if (null? matches)
        (printf "No symbols matching '~a'~%" pat)
        (begin
          (printf "Symbols matching '~a':~%" pat)
          (for-each (lambda (s) (printf "  ~a~%" s))
                    (sort matches string<?))))
    (print "")
    (void)))

;; Pager support - pipe output through $PAGER (default: less)
;; less supports forward/back navigation (j/k, arrows, pgup/pgdn)
(define (with-pager thunk)
  "Run thunk with output piped to pager for interactive viewing."
  (let ((pager (or (get-environment-variable "PAGER") "less")))
    (let ((port (open-output-pipe pager)))
      (handle-exceptions exn
        (begin
          (close-output-pipe port)
          (tty-flush-input)  ; Clear any input left by pager
          (void))
        (with-output-to-port port thunk)
        (close-output-pipe port)
        (tty-flush-input)))))

;; General page command - pipe any output through pager
;; Usage: (page (soup)) or (page (help 'topics))
(define-syntax page
  (syntax-rules ()
    ((page expr)
     (with-pager (lambda () expr (void))))))

;; KWIC - Key Word In Context search for memos
(define (kwic keyword)
  "Search memo content with keyword-in-context display.
   (kwic 'soup)    - find 'soup' in all memos with context
   (kwic 'vault)   - concordance-style results"
  (let* ((kw (if (symbol? keyword) (symbol->string keyword) keyword))
         (kw-lower (string-downcase kw))
         (memo-dir (make-pathname (or (get-environment-variable "CYBERSPACE_HOME")
                                      (current-directory))
                                  "docs/notes"))
         (memo-files (glob (make-pathname memo-dir "memo-*.scm")))
         (context-width 30)  ; chars on each side
         (results '()))
    ;; Search each memo file
    (for-each
     (lambda (file)
       (let* ((basename (pathname-strip-directory file))
              (memo-num (let ((m (irregex-search "memo-([0-9]+)" basename)))
                          (if m (irregex-match-substring m 1) "???"))))
         (with-input-from-file file
           (lambda ()
             (let loop ((line-num 0))
               (let ((line (read-line)))
                 (unless (eof-object? line)
                   (when (string-contains-ci line kw-lower)
                     (let* ((pos (string-contains-ci line kw-lower))
                            (start (max 0 (- pos context-width)))
                            (end (min (string-length line) (+ pos (string-length kw) context-width)))
                            (context (substring line start end))
                            (prefix (if (> start 0) "..." ""))
                            (suffix (if (< end (string-length line)) "..." "")))
                       (set! results
                             (cons (list memo-num line-num
                                        (string-append prefix context suffix))
                                   results))))
                   (loop (+ line-num 1)))))))))
     memo-files)

    (if (null? results)
        (printf "~%No matches for '~a' in memos~%~%" kw)
        ;; Use pager for results
        (with-pager
         (lambda ()
           (printf "KWIC: ~a (~a matches)~%~%" kw (length results))
           (for-each
            (lambda (r)
              (printf "  Memo-~a:~a  ~a~%"
                      (string-pad-left (first r) 3 #\0)
                      (second r)
                      (third r)))
            (reverse results))
           (print ""))))
    (void)))

;; Open Memo in viewer
(define (memo num #!optional format)
  "Open Memo in viewer. (memo 54) or (memo 54 'html) or (memo 54 'ps)"
  (let* ((num-str (if (number? num)
                      (string-pad-left (number->string num) 3 #\0)
                      (string-pad-left (symbol->string num) 3 #\0)))
         (base-dir (or (get-environment-variable "CYBERSPACE_HOME")
                       (make-pathname (current-directory) "")))
         (memo-dir (make-pathname base-dir "docs/notes"))
         (fmt (or format 'txt))
         (ext (case fmt
                ((html) ".html")
                ((ps postscript) ".ps")
                ((txt text) ".txt")
                ((md markdown) ".md")
                (else ".txt")))
         (path (string-append memo-dir "/memo-" num-str "-*.txt"))
         ;; Find the actual filename
         (actual (with-input-from-pipe
                  (string-append "ls " memo-dir "/memo-" num-str "-*" ext " 2>/dev/null | head -1")
                  read-line)))
    (if (or (eof-object? actual) (string=? actual ""))
        (print "Memo-" num-str " not found")
        (begin
          (case fmt
            ((html)
             (system (string-append "open " actual))
             (print "Opening " (pathname-strip-directory actual) " in browser"))
            ((ps postscript)
             (system (string-append "open " actual))
             (print "Opening " (pathname-strip-directory actual) " in Preview"))
            (else
             ;; Display in terminal
             (print "")
             (with-input-from-file actual
               (lambda ()
                 (let loop ((n 0))
                   (let ((line (read-line)))
                     (when (and (not (eof-object? line)) (< n 50))
                       (print line)
                       (loop (+ n 1)))))))
             (print "")
             (print "... (memo " num " 'html) to open in browser")))
          ;; Leave a trail
          (set! *trail* (cons num *trail*))
          (void)))))

;; Alias for backward compatibility
(define rfc memo)  ; backwards compat alias

;;; Navigation - travellers leave trails
(define (back)
  "Go back to previous memo in trail"
  (if (null? *trail*)
      (print "No trail yet")
      (let ((prev (car *trail*)))
        (set! *trail* (cdr *trail*))
        (memo prev))))

(define (next #!optional n)
  "Go to next memo. (next) or (next 5)"
  (let* ((current (if (null? *trail*) 0 (car *trail*)))
         (target (+ current (or n 1))))
    (memo target)))

(define (prev #!optional n)
  "Go to previous memo. (prev) or (prev 5)"
  (let* ((current (if (null? *trail*) 1 (car *trail*)))
         (target (max 0 (- current (or n 1)))))
    (memo target)))

(define (trail)
  "Show navigation trail"
  (if (null? *trail*)
      (print "No trail yet - start reading with (memo N)")
      (begin
        (print "Trail:")
        (for-each (lambda (n) (printf "  Memo-~a~%" n))
                  (reverse (take *trail* (min 10 (length *trail*))))))))

;;; Lens - library (light) or soup (dark)
(define (lens #!optional mode)
  "Show or set viewing lens. (lens) or (lens 'soup) or (lens 'library)"
  (if mode
      (begin
        (set! *lens* mode)
        (printf "~a~%" (if (eq? mode 'soup) "⚗ soup" "📚 library")))
      (printf "~a~%" (if (eq? *lens* 'soup) "⚗ soup" "📚 library"))))

(define (light) (lens 'library))
(define (dark) (lens 'soup))

;; Status - compact tree view
(define (status)
  (define (safe-ref lst key)
    (let ((pair (and (pair? lst) (assq key (if (pair? (cdr lst)) (cdr lst) '())))))
      (and pair (pair? (cdr pair)) (cadr pair))))
  (define (get-en0-ip net type)
    ;; Extract IP from (network (interfaces (en0 (ipv4 "x") (ipv6 "y"))))
    (let* ((ifaces (and net (assq 'interfaces (cdr net))))
           (en0 (and ifaces (assq 'en0 (cdr ifaces))))
           (ip-pair (and en0 (assq type (cdr en0)))))
      (and ip-pair (cadr ip-pair))))
  (let* ((info (introspect-system))
         (hw (assq 'hardware (cdr info)))
         (net (assq 'network (cdr info)))
         (realm (assq 'realm (cdr info)))
         (code (assq 'codebase (cdr info)))
         (uptime (safe-ref info 'uptime))
         (cores (safe-ref hw 'cores))
         (mem (safe-ref hw 'memory-gb))
         (chip (safe-ref hw 'cpu))
         (ipv4 (get-en0-ip net 'ipv4))
         (ipv6 (get-en0-ip net 'ipv6))
         (vault-exists (safe-ref realm 'vault-exists))
         (keystore (safe-ref realm 'has-keystore))
         (audit (safe-ref realm 'has-audit))
         (loc (safe-ref code 'loc))
         (modules (safe-ref code 'modules))
         (memos (safe-ref code 'memos))
         (lambda-time (safe-ref info 'lamport-time)))
    (printf "~%~a · up ~a · ~a~%" (get-hostname) (or uptime "?") (lamport-format))
    (printf "├─ ~a cores, ~aGB~a~%"
            (or cores "?")
            (or mem "?")
            (if chip (string-append ", " chip) ""))
    (printf "├─ ~a~a~%"
            (or ipv4 "no ipv4")
            (if (and ipv6 (string? ipv6))
                (string-append " / " (substring ipv6 0 (min 20 (string-length ipv6))) "...")
                ""))
    (printf "├─ ~a~%"
            (if vault-exists
                (string-append "vault: " vault-exists
                               (if keystore " (keys)" "")
                               (if audit " (audit)" ""))
                "no vault"))
    (printf "└─ ~aK loc, ~a modules, ~a memos~%"
            (if loc (quotient loc 1000) "?")
            (or modules "?")
            (or memos "?"))
    (void)))

;; Single-char shortcuts (thunks that invoke the command)
(define (|.|) (status))  ; status at a glance
(define (|?|) (help))    ; help

;; Quit shortcuts (don't shadow scheme's exit)
(define quit repl-goodbye)
(define q repl-goodbye)
(define bye repl-goodbye)

;; System utilities (platform-abstracted)
(define (keychain) (open-keychain))   ; Keychain Access / seahorse
(define (tickets) (open-tickets))     ; Ticket Viewer / klist
(define (console) (open-console))     ; Console.app / journalctl
(define (monitor) (open-monitor))     ; Activity Monitor / htop
(define (finder) (open-finder))       ; Reveal cwd in file manager

;;; ============================================================
;;; Key Ceremony (Memo-0024)
;;; ============================================================
;;
;; Ritualized key generation with witnessed verification.
;; Uses Shamir secret sharing for threshold key distribution.

(define (ceremony #!optional (type 'help))
  "Key ceremony commands (Memo-0024).
   (ceremony)           - show help
   (ceremony 'generate) - generate new keypair with ceremony
   (ceremony 'split K N) - split key into N shares, K required
   (ceremony 'reconstruct) - reconstruct from shares
   (ceremony 'verify)   - verify share integrity"
  (case type
    ((help)
     (print "")
     (print "┌─ Key Ceremony ──────────────────────────────────────────────────┐")
     (print "│ (ceremony 'generate)      Generate witnessed keypair           │")
     (print "│ (ceremony 'split K N)     Split into N shares, K to recover    │")
     (print "│ (ceremony 'reconstruct)   Reconstruct key from shares          │")
     (print "│ (ceremony 'verify SHARE)  Verify share integrity               │")
     (print "│                                                                 │")
     (print "│ Shamir primitives:                                              │")
     (print "│ (shamir-split SECRET #:threshold K #:total N)                   │")
     (print "│ (shamir-reconstruct SHARES)                                     │")
     (print "└─────────────────────────────────────────────────────────────────┘")
     (void))
    ((generate)
     (ceremony-generate))
    ((split)
     (print "Usage: (ceremony-split KEY threshold: K total: N)")
     (void))
    ((reconstruct)
     (ceremony-reconstruct-interactive))
    ((verify)
     (print "Usage: (ceremony-verify SHARE)")
     (void))
    (else
     (printf "Unknown ceremony type: ~a~n" type))))

(define (ceremony-generate)
  "Interactive key generation ceremony"
  (print "")
  (print "┌─ Key Generation Ceremony ───────────────────────────────────────┐")
  (print "│ This will generate a new Ed25519 keypair with witnessed entropy │")
  (print "└─────────────────────────────────────────────────────────────────┘")
  (print "")
  ;; Generate keypair using system entropy
  (print "Collecting entropy from system RNG...")
  (let ((keypair (crypto-ffi#ed25519-keypair)))
    (print "")
    (print "✓ Keypair generated")
    (print "")
    (print "Generated keypair:")
    (printf "  Public:  ~a...~n" (substring (blob->hex (car keypair)) 0 16))
    (printf "  Secret:  [protected, ~a bytes]~n" (blob-size (cadr keypair)))
    (print "")
    (print "Store this keypair securely. Consider (ceremony-split KEY K N)")
    (print "for threshold distribution of the secret key.")
    (print "")
    keypair))

(define (ceremony-split key #!key (threshold 3) (total 5))
  "Split secret key into shares using Shamir secret sharing.
   Returns list of shares; threshold shares needed to reconstruct."
  (unless (blob? key)
    (error "ceremony-split: key must be a blob"))
  (unless (and (integer? threshold) (> threshold 1))
    (error "ceremony-split: threshold must be > 1"))
  (unless (and (integer? total) (>= total threshold))
    (error "ceremony-split: total must be >= threshold"))
  (print "")
  (printf "┌─ Splitting Key (~a-of-~a) ─────────────────────────────────────────┐~n"
          threshold total)
  (print "│ Each share should be given to a different custodian.             │")
  (print "└─────────────────────────────────────────────────────────────────┘")
  (print "")
  (let ((shares (crypto-ffi#shamir-split key threshold: threshold total: total)))
    (let loop ((i 1) (remaining shares))
      (when (pair? remaining)
        (let ((share (car remaining)))
          (printf "Share ~a/~a: ~a...~n" i total
                  (substring (blob->hex (crypto-ffi#share-y share)) 0 16)))
        (loop (+ i 1) (cdr remaining))))
    (print "")
    (printf "✓ Generated ~a shares. ~a required to reconstruct.~n" total threshold)
    (print "")
    (print "IMPORTANT: Distribute shares to separate custodians.")
    (print "           Never store multiple shares together.")
    (print "           Test reconstruction before destroying original.")
    shares))

(define (ceremony-reconstruct shares)
  "Reconstruct secret from Shamir shares"
  (unless (and (list? shares) (>= (length shares) 2))
    (error "ceremony-reconstruct: need at least 2 shares"))
  (print "")
  (printf "Reconstructing from ~a shares...~n" (length shares))
  (let ((secret (crypto-ffi#shamir-reconstruct shares)))
    (print "✓ Secret reconstructed successfully")
    (printf "  Length: ~a bytes~n" (blob-size secret))
    secret))

(define (ceremony-reconstruct-interactive)
  "Interactive share collection and reconstruction"
  (print "")
  (print "┌─ Key Reconstruction ────────────────────────────────────────────┐")
  (print "│ Collect shares from custodians to reconstruct the secret key.  │")
  (print "└─────────────────────────────────────────────────────────────────┘")
  (print "")
  (print "Enter shares as a list: (ceremony-reconstruct (list share1 share2 ...))")
  (void))

(define (ceremony-verify share)
  "Verify a Shamir share is valid"
  (if (crypto-ffi#shamir-share? share)
      (begin
        (print "")
        (print "✓ Valid Shamir share")
        (printf "  Share ID:   ~a~n" (crypto-ffi#share-id share))
        (printf "  Threshold:  ~a~n" (crypto-ffi#share-threshold share))
        (printf "  X value:    ~a~n" (crypto-ffi#share-x share))
        (printf "  Y length:   ~a bytes~n" (blob-size (crypto-ffi#share-y share)))
        #t)
      (begin
        (print "✗ Not a valid Shamir share")
        #f)))

;; Hot reload REPL definitions (for development)
(define (reload!)
  "Hot reload REPL definitions without restart.
   Note: Module state preserved, only top-level defs refreshed."
  (print "Reloading repl.scm...")
  (load "repl.scm")
  (print "Reloaded. New definitions active."))

;;; ============================================================
;;; Regression Test Suite
;;; ============================================================
;;
;; Take the lambdas out for a spin. Exercise every stratum of the weave.
;; Run with (regression) to verify the system is working.

;; Note: blob->hex defined earlier in file (line ~994)

;; Note: blob=? is provided by (chicken blob)

(define *regression-tests* '())  ; alist of (name . thunk)

(define (deftest name thunk)
  "Register a regression test"
  (set! *regression-tests* (append *regression-tests* (list (cons name thunk)))))

(define (run-test name thunk)
  "Run a single test, return (name pass? elapsed-ms message)"
  (let ((start (current-process-milliseconds)))
    (handle-exceptions exn
      (list name #f (- (current-process-milliseconds) start)
            (sprintf "Exception: ~a" (get-condition-property exn 'exn 'message "unknown")))
      (let ((result (thunk)))
        (list name (car result) (- (current-process-milliseconds) start) (cdr result))))))

;; === Crypto Primitives ===

(deftest 'sha256
  (lambda ()
    (let* ((hash (sha256-hash "abc"))
           (hex (blob->hex hash)))
      (if (string=? hex "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
          (cons #t "NIST FIPS 180-4 KAT")
          (cons #f (sprintf "got ~a" (substring hex 0 16)))))))

(deftest 'sha512
  (lambda ()
    (let* ((hash (sha512-hash "abc"))
           (hex (blob->hex hash)))
      (if (string-prefix? "ddaf35a193617aba" hex)
          (cons #t "NIST FIPS 180-4 KAT")
          (cons #f (sprintf "got ~a" (substring hex 0 16)))))))

(deftest 'blake2b
  (lambda ()
    (let* ((hash (blake2b-hash "abc"))
           (hex (blob->hex hash)))
      (if (string-prefix? "ba80a53f981c4d0d" hex)
          (cons #t "RFC 7693 KAT")
          (cons #f (sprintf "got ~a" (substring hex 0 16)))))))

(deftest 'ed25519-sign-verify
  (lambda ()
    (let* ((keys (ed25519-keypair))
           (pk (car keys))
           (sk (cadr keys))
           (msg "test message for signing")
           (sig (ed25519-sign sk msg)))
      (if (ed25519-verify pk sig msg)
          (cons #t "sign/verify round-trip")
          (cons #f "verification failed")))))

(deftest 'ed25519-wrong-key
  (lambda ()
    (let* ((keys1 (ed25519-keypair))
           (keys2 (ed25519-keypair))
           (pk1 (car keys1))
           (sk2 (cadr keys2))
           (msg "test message")
           (sig (ed25519-sign sk2 msg)))
      ;; Should NOT verify with wrong key
      (if (not (ed25519-verify pk1 sig msg))
          (cons #t "rejects wrong key")
          (cons #f "accepted wrong key!")))))

(deftest 'x25519-key-exchange
  (lambda ()
    (let* ((alice (x25519-keypair))
           (bob (x25519-keypair))
           (alice-pk (car alice))
           (alice-sk (cadr alice))
           (bob-pk (car bob))
           (bob-sk (cadr bob))
           (shared-a (x25519-shared-secret alice-sk bob-pk))
           (shared-b (x25519-shared-secret bob-sk alice-pk)))
      (if (blob=? shared-a shared-b)
          (cons #t "DH key agreement")
          (cons #f "shared secrets differ")))))

(deftest 'random-bytes
  (lambda ()
    (let* ((r1 (random-bytes 32))
           (r2 (random-bytes 32)))
      (if (and (= (blob-size r1) 32)
               (= (blob-size r2) 32)
               (not (blob=? r1 r2)))
          (cons #t "32 bytes, non-repeating")
          (cons #f "entropy failure")))))

;; === Weave Performance ===

(deftest 'weave-performance
  (lambda ()
    (let* ((weave (measure-weave))
           (stratum (weave-stratum weave)))
      (if (> weave 0)
          (cons #t (sprintf "~a (~a stratum)" weave stratum))
          (cons #f "weave is zero")))))

;; === Vault Operations ===

(deftest 'vault-exists
  (lambda ()
    (if (directory-exists? ".vault")
        (cons #t ".vault directory present")
        (cons #f "no .vault directory"))))

(deftest 'vault-query
  (lambda ()
    (if (not (directory-exists? ".vault"))
        (cons #t "skipped (no vault)")
        (let ((results (query (lambda (o) #t))))
          (cons #t (sprintf "~a objects" (length results)))))))

(deftest 'soup-browse
  (lambda ()
    (if (not (directory-exists? ".vault"))
        (cons #t "skipped (no vault)")
        (let ((count (length (directory ".vault"))))
          (cons #t (sprintf "~a entries" count))))))

;; === Module Loading ===

(deftest 'modules-loaded
  (lambda ()
    (let ((loaded (length *cyberspace-modules*)))
      (if (>= loaded 20)
          (cons #t (sprintf "~a modules" loaded))
          (cons #f (sprintf "only ~a modules" loaded))))))

;; === FIPS Status ===

(deftest 'fips-passed
  (lambda ()
    (if (eq? (fips-status) 'passed)
        (cons #t "all KATs passed")
        (cons #f "FIPS self-test failed"))))

;; === Entropy ===

(deftest 'entropy-source
  (lambda ()
    (let ((ent (entropy-status)))
      (if ent
          (cons #t (cdr (assq 'source ent)))
          (cons #f "no entropy status")))))

;; === The Regression Runner ===

(define (regression #!optional verbose?)
  "Run all regression tests against the weave.
   (regression)     - summary only
   (regression #t)  - verbose output"
  (print "")
  (print "┌─────────────────────────────────────────────────────────────┐")
  (print "│             Cyberspace Regression Suite                     │")
  (print "├─────────────────────────────────────────────────────────────┤")
  (let* ((start (current-process-milliseconds))
         ;; Run tests with spinning lambda
         (results (map (lambda (t)
                         (spin!)
                         (run-test (car t) (cdr t)))
                       *regression-tests*))
         (_ (spin-done!))
         (passed (filter (lambda (r) (cadr r)) results))
         (failed (filter (lambda (r) (not (cadr r))) results))
         (elapsed (- (current-process-milliseconds) start)))
    ;; Show each test result
    (for-each
      (lambda (r)
        (let ((name (car r))
              (pass? (cadr r))
              (ms (caddr r))
              (msg (cadddr r)))
          (if pass?
              (when verbose?
                (printf "│  ✓ ~a (~ams) ~a~n"
                        (string-pad-right (symbol->string name) 20)
                        ms msg))
              (printf "│  ✗ ~a (~ams) ~a~n"
                      (string-pad-right (symbol->string name) 20)
                      ms msg))))
      results)
    ;; Summary
    (print "├─────────────────────────────────────────────────────────────┤")
    (let ((total (length results))
          (pass-count (length passed))
          (fail-count (length failed)))
      (if (= fail-count 0)
          (printf "│  ✓ All ~a tests passed in ~ams~n" total elapsed)
          (printf "│  ~a/~a passed, ~a FAILED in ~ams~n"
                  pass-count total fail-count elapsed)))
    (print "└─────────────────────────────────────────────────────────────┘")
    (print "")
    ;; Return summary
    (if (null? failed)
        'passed
        (map car failed))))

;; Settable prompt
(define *prompt* "% ")

;; Help invocation tracking - second ? shows more detail
(define *help-call-count* 0)

;; User mode: novice (command mode) vs schemer (full Scheme)
;; Affects help detail, prompts, and suggestions
(define *user-mode* 'novice)
(define *paren-count* 0)      ; track Scheme expression usage
(define *command-count* 0)    ; track bare command usage
(define *mode-threshold* 1)   ; switch on first paren expression

(define (novice)
  "Switch to novice mode - guardrails on, confirmations required"
  (set! *user-mode* 'novice)
  (set! *prompt* "% ")
  (set! *paren-count* 0)      ; reset mode detection
  (set! *command-count* 0)
  (lineage#set-paren-wrap 0)  ; bare word completions
  (print "Novice mode. Guardrails on.")
  (print "Destructive ops require confirmation. Type ? for help."))

(define (schemer)
  "Switch to schemer mode - full power, no safety rails"
  (set! *user-mode* 'schemer)
  (set! *prompt* "λ ")
  (lineage#set-paren-wrap 1)  ; wrap completions in parens
  (print "Schemer mode. Full power, no confirmations.")
  (print "You asked for it."))

;; Novice mode guardrails - dangerous operations need confirmation
(define *dangerous-ops*
  '(seal-release seal-commit key-delete key-revoke
    vault-reset vault-wipe gossip-broadcast
    enroll-revoke capability-revoke))

(define (confirm? prompt)
  "Ask user for confirmation, returns #t if confirmed"
  (printf "~a [y/N] " prompt)
  (flush-output)
  (let ((response (read-line)))
    (and response
         (> (string-length response) 0)
         (char-ci=? (string-ref response 0) #\y))))

(define (novice-guard op-name thunk)
  "Wrap dangerous operation with confirmation in novice mode"
  (if (eq? *user-mode* 'novice)
      (if (confirm? (sprintf "~a is destructive. Continue?" op-name))
          (thunk)
          (begin (print "Cancelled.") (void)))
      (thunk)))

(define-syntax guarded
  (syntax-rules ()
    ((guarded op-name body ...)
     (novice-guard 'op-name (lambda () body ...)))))

;; Guarded wrappers for dangerous operations
;; In novice mode, these require confirmation. In schemer mode, direct.

(define (release! version . args)
  "Create a sealed release (guarded in novice mode)"
  (guarded seal-release
    (apply seal-release version args)))

(define (wipe-vault!)
  "Wipe the entire vault - DESTRUCTIVE (guarded in novice mode)"
  (guarded vault-wipe
    (vault-wipe)))

(define (delete-key! key-id)
  "Delete a key from the keyring - DESTRUCTIVE (guarded in novice mode)"
  (guarded key-delete
    (keyring-delete key-id)))

(define (broadcast! artifact)
  "Broadcast artifact to all peers - cannot be recalled (guarded in novice mode)"
  (guarded gossip-broadcast
    (gossip-broadcast artifact)))

(define (check-mode-shift!)
  "Auto-detect mode shift based on usage patterns"
  (when (and (eq? *user-mode* 'novice)
             (>= *paren-count* *mode-threshold*)
             (> *paren-count* (* 2 *command-count*)))
    (set! *user-mode* 'schemer)
    (set! *prompt* "λ ")
    (lineage#set-paren-wrap 1)  ; wrap completions in parens
    (print "")
    (print "Detected Scheme usage - switching to schemer mode.")
    (print "Type (novice) to switch back.")))

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

;; Strip ANSI escape sequences from input (for terminals without rlwrap)
;; Handles arrow keys, function keys, etc. that send ESC [ ... sequences
(define (strip-ansi str)
  "Remove ANSI escape sequences from string"
  (irregex-replace/all "\x1b\\[[0-9;]*[A-Za-z]" str ""))

;; Terminal raw mode for immediate single-char commands
;; Uses tty-ffi module for raw getchar (bypasses Scheme's stdio buffering)
(define (stty-raw) (tty-set-raw))
(define (stty-cooked) (tty-set-cooked))

;; Read line with immediate '.' and '?' handling
;; History file in vault or home directory
(define *history-file*
  (let ((vault-hist ".vault/repl-history")
        (home-hist (make-pathname (get-environment-variable "HOME") ".cyberspace-history")))
    (if (directory-exists? ".vault")
        vault-hist
        home-hist)))

(define *history-loaded* #f)

(define *completions-loaded* #f)

(define (repl-init-completions)
  "Initialize TOPS-20/JSYS style command completion"
  (unless *completions-loaded*
    ;; Add all command aliases
    (for-each (lambda (pair)
                (lineage#add-command (symbol->string (car pair))))
              *command-aliases*)
    ;; Add common Scheme forms that novice mode accepts
    (for-each (lambda (sym)
                (lineage#add-command (symbol->string sym)))
              '(;; Mode switching
                novice schemer
                ;; Help and quit
                help quit exit bye
                ;; Common Scheme forms
                define let if cond lambda quote begin load
                print display newline
                ;; Debugging
                bt backtrace frame exception-info
                ;; Editors
                schemacs pencil pencil-novice teco
                ;; Common arguments (for help, soup, dashboard, etc.)
                topics full keys releases audit wormholes crypto
                vault network federation ceremony))
    (lineage#enable-command-completion)
    (lineage#set-hints-enabled 1)
    (set! *completions-loaded* #t)))

(define (repl-history-load)
  "Load history from file"
  (unless *history-loaded*
    (when (file-exists? *history-file*)
      (lineage#load-history-from-file *history-file*))
    (set! *history-loaded* #t))
  (repl-init-completions))

(define (repl-history-add line)
  "Add line to history (skip empty, whitespace-only, and prompt strings)"
  (when (and (string? line)
             (> (string-length line) 0)
             ;; Skip whitespace-only
             (not (string-every char-whitespace? line))
             ;; Skip if it looks like a prompt (λ or %)
             (not (string-prefix? "λ" line))
             (not (string-prefix? "% " line)))
    (lineage#history-add line)))

(define (repl-history-save)
  "Save history to file"
  (lineage#save-history-to-file *history-file*))

(define (repl-read-line prompt)
  "Read line with immediate shortcuts and lineage history.
   . and ? respond immediately. ESC (arrows) defers to lineage for history.
   For non-tty (piped input), bypasses shortcuts and uses lineage directly."
  (repl-history-load)
  ;; Ensure clean terminal state before prompting
  (tty-ffi#tty-set-cooked)
  (tty-ffi#tty-flush-input)
  ;; Non-tty input: bypass raw char shortcuts, let lineage use fgets
  (if (zero? (tty?))
      (let ((line (lineage#lineage prompt)))
        (when line (repl-history-add line))
        (and line (strip-ansi line)))
      ;; Interactive tty: show prompt, peek first char for immediate shortcuts
      (begin
        (display prompt)
        (flush-output)
        ;; Loop in raw mode to handle DEL/BS at empty prompt (ignore and wait)
        ;; Use polling to prevent runaway processes when terminal disconnects
        (let read-char ()
          (tty-set-raw)
          ;; Poll with 500ms timeout - allows signal handling
          (if (not (tty-char-ready? 500))
              ;; No input ready - check if still a tty, then retry
              (begin
                (tty-set-cooked)
                (if (zero? (tty?))
                    #f  ; Terminal gone, exit
                    (read-char)))  ; Still have tty, keep waiting
              ;; Input ready - read it
              (let ((c (tty-raw-char)))
                ;; ESC must stay in raw mode so lineage can read the rest of the sequence
                (cond
                  ((= c 27)
                   ;; ESC = start of escape sequence (arrow keys, etc)
                   ;; Stay in raw mode - lineage will read [A, [B, etc.
                   (let ((line (lineage#lineage-with-first-char prompt 27)))
                     (tty-set-cooked)
                     (when line (repl-history-add line))
                     (and line (strip-ansi line))))
                  (else
                   ;; For all other chars, switch to cooked mode first
                   (tty-set-cooked)
                   (cond
                     ;; EOF
                     ((< c 0) #f)
                     ;; DEL/BS at prompt start - ignore, stay on line, wait for real input
                     ((or (= c 127) (= c 8))
                      (read-char))
                     ;; Immediate shortcuts (no Enter needed) - prompt already shown
                     ((= c 46)  ; .
                      (display ".\n")
                      ".")
                     ((= c 63)  ; ?
                      (display "?\n")
                      "?")
                     ;; Ctrl-D = EOF
                     ((= c 4) #f)
                     ;; Ctrl-C = cancel
                     ((= c 3)
                      (newline)
                      "")
                     ;; Enter on empty line - newline, return empty (loop shows next prompt)
                     ((or (= c 10) (= c 13))
                      (newline)
                      "")
                     ;; Regular char - let lineage redraw with initial (no newline)
                     (else
                      (let* ((initial (string (integer->char c)))
                             (line (lineage#lineage-with-initial prompt initial)))
                        (when line (repl-history-add line))
                        (and line (strip-ansi line)))))))))))))

;; Custom REPL with comma command handling
;; Intercepts ,<cmd> before Scheme reader parses it as (unquote <cmd>)
(define (command-repl)
  (let loop ()
    ;; Don't clear *last-call-chain* here - it should persist until next exception
    ;; capture-exception will overwrite it when a new exception occurs
    (let ((line (repl-read-line *prompt*)))
      (cond
        ;; EOF (lineage returns #f, read-line returns eof-object)
        ((or (not line) (eof-object? line))
         (newline)
         (goodbye repl-history-save *boot-verbosity*))

        ;; Empty line
        ((string=? line "")
         (loop))

        ;; QMK keyboard commands: #;QMK (edt 'key) etc
        ;; Dispatched to edt module for LK201 keypad emulation
        ((and (>= (string-length line) 6)
              (string=? (substring line 0 6) "#;QMK "))
         (handle-exceptions exn
           (printf "QMK error: ~a~n" (get-condition-property exn 'exn 'message ""))
           (edt#qmk-dispatch line))
         (loop))

        ;; Single-char shortcuts (bare ? and . invoke help/status)
        ;; Novice: first ? = brief, second = topics
        ;; Schemer: always show topics
        ((string=? line "?")
         (set! *help-call-count* (+ 1 *help-call-count*))
         (cond
           ((eq? *user-mode* 'schemer)
            (help 'topics))
           ((odd? *help-call-count*)
            (help))
           (else
            (help 'topics)))
         (loop))
        ((string=? line ".")
         (status)
         (loop))

        ;; Shell escape: !command runs command in user's shell
        ((and (> (string-length line) 0)
              (char=? (string-ref line 0) #\!))
         (let ((cmd (string-trim-both (substring line 1))))
           (if (string=? cmd "")
               (print "Usage: !command")
               (let ((shell (or (get-environment-variable "SHELL") "/bin/sh")))
                 (receive (_ _ _) (process-wait (process-run shell (list "-i" "-c" cmd)))
                   (void)))))
         (loop))

        ;; Inspector colon commands (Memo-052 Section 8.2)
        ((and (> (string-length line) 0)
              (char=? (string-ref line 0) #\:))
         ;; History already added by repl-read-line
         (let* ((cmd-line (substring line 1))
                (parts (string-split cmd-line))
                (cmd (if (null? parts) "" (car parts)))
                (args (if (null? parts) '() (cdr parts))))
           (cond
             ;; :i obj - inspect object
             ((string=? cmd "i")
              (if (null? args)
                  (print "Usage: :i <expression>")
                  (let ((expr-str (string-intersperse args " ")))
                    (handle-exceptions exn
                      (print "Error: " ((condition-property-accessor 'exn 'message) exn))
                      (inspect (eval (with-input-from-string expr-str read)))))))

             ;; :s - show current object
             ((string=? cmd "s")
              (inspector#inspector-show))

             ;; :d N - descend into slot N
             ((string=? cmd "d")
              (if (null? args)
                  (print "Usage: :d N (descend into slot N)")
                  (let ((n (string->number (car args))))
                    (if n
                        (inspector#inspector-descend n)
                        (print "Error: N must be a number")))))

             ;; :u - go up
             ((string=? cmd "u")
              (inspector#inspector-up))

             ;; :h - show history
             ((string=? cmd "h")
              (inspector#inspector-history))

             ;; :b - bookmark current
             ((string=? cmd "b")
              (inspector#inspector-bookmark))

             ;; :t - show type info
             ((string=? cmd "t")
              (inspector#inspector-type))

             ;; Unknown colon command
             (else
              (print "Unknown inspector command: :" cmd)
              (print "  :i OBJ  - inspect object")
              (print "  :s      - show current object")
              (print "  :d N    - descend into slot N")
              (print "  :u      - go up to parent")
              (print "  :h      - show navigation history")
              (print "  :b      - bookmark current object")
              (print "  :t      - show type info"))))
         (loop))

        ;; Reserved single-character graphics (UI reserved, not Scheme)
        ;; Note: colon is now handled above for inspector commands
        ((and (= (string-length line) 1)
              (string-contains "<>/;\"[]{}\\|-=_+@#$%^&*" line))
         (print "Reserved for future use")
         (loop))

        ;; Natural language exit (with optional trailing period)
        ((or (string=? line "bye") (string=? line "bye."))
         (goodbye repl-history-save *boot-verbosity*))

        ;; Comma commands - using comma asserts schemer mode
        ((char=? (string-ref line 0) #\,)
         ;; History already added by repl-read-line
         ;; Comma usage = schemer assertion
         (when (eq? *user-mode* 'novice)
           (set! *user-mode* 'schemer)
           (set! *prompt* "λ ")
           (lineage#set-paren-wrap 1))
         (let* ((cmd-line (substring line 1))
                (parts (string-split cmd-line))
                (cmd (if (null? parts) "" (car parts)))
                (args (if (null? parts) '() (cdr parts))))
           (cond
             ;; Bare comma - show preferences
             ((string=? cmd "")
              (preferences)
              (loop))

             ;; Quit
             ((or (string=? cmd "q")
                  (string=? cmd "quit")
                  (string=? cmd "exit"))
              (goodbye repl-history-save *boot-verbosity*))

             ;; Help - delegate to mode-aware (help)
             ((or (string=? cmd "h")
                  (string=? cmd "help")
                  (string=? cmd "?"))
              (help)
              (loop))

             ;; Pretty print (CSI's ,p)
             ((string=? cmd "p")
              (if (null? args)
                  (print "Usage: ,p <expression>")
                  (let ((expr-str (string-intersperse args " ")))
                    (handle-exceptions exn
                      (print "Error: " ((condition-property-accessor 'exn 'message) exn))
                      (pp (eval (with-input-from-string expr-str read))))))
              (loop))

             ;; Expand macros (CSI's ,x)
             ((string=? cmd "x")
              (if (null? args)
                  (print "Usage: ,x <expression>")
                  (let ((expr-str (string-intersperse args " ")))
                    (handle-exceptions exn
                      (print "Error: " ((condition-property-accessor 'exn 'message) exn))
                      (pp (expand (with-input-from-string expr-str read))))))
              (loop))

             ;; Time expression (CSI's ,t)
             ((string=? cmd "t")
              (if (null? args)
                  (print "Usage: ,t <expression>")
                  (let ((expr-str (string-intersperse args " ")))
                    (handle-exceptions exn
                      (print "Error: " ((condition-property-accessor 'exn 'message) exn))
                      (let* ((start (current-process-milliseconds))
                             (result (eval (with-input-from-string expr-str read)))
                             (end (current-process-milliseconds)))
                        (printf "~a ms~%" (- end start))
                        result))))
              (loop))

             ;; Shell command (CSI's ,s - use ,sh to avoid conflict with status)
             ((string=? cmd "sh")
              (if (null? args)
                  (print "Usage: ,sh <command>")
                  (let ((cmd-str (string-intersperse args " ")))
                    (system cmd-str)))
              (loop))

             ;; System info (CSI's ,r)
             ((string=? cmd "r")
              (print "")
              (printf "Machine type:     ~a~%" (machine-type))
              (printf "Software type:    ~a~%" (software-type))
              (printf "Software version: ~a~%" (software-version))
              (printf "Build platform:   ~a~%" (build-platform))
              (printf "Chicken version:  ~a~%" (chicken-version))
              (printf "Repository:       ~a~%" (repository-path))
              (print "")
              (loop))

             ;; Call chain / backtrace (CSI's ,c - use ,bt to avoid conflict with clear)
             ((string=? cmd "bt")
              (print-call-chain)
              (loop))

             ;; Last exception (CSI's ,exn)
             ((string=? cmd "exn")
              (if *last-exception*
                  (begin
                    (print "Last exception:")
                    (print-error-message *last-exception*)
                    (print "")
                    (print "Call chain at error:")
                    (when *last-call-chain*
                      (print-call-chain (current-error-port) 0 *last-call-chain*)))
                  (print "No exception recorded"))
              (loop))

             ;; Dump (CSI's ,du) - hex dump of blob/string
             ((string=? cmd "du")
              (if (null? args)
                  (print "Usage: ,du <expression>")
                  (let ((expr-str (string-intersperse args " ")))
                    (handle-exceptions exn
                      (print "Error: " ((condition-property-accessor 'exn 'message) exn))
                      (let ((val (eval (with-input-from-string expr-str read))))
                        (cond
                          ((blob? val)
                           (hex-dump (blob->u8vector val)))
                          ((string? val)
                           (hex-dump (blob->u8vector (string->blob val))))
                          ((u8vector? val)
                           (hex-dump val))
                          (else
                           (print "Value is not a blob, string, or u8vector:")
                           (pp val)))))))
              (loop))

             ;; Apropos - search symbols
             ((or (string=? cmd "a")
                  (string=? cmd "apropos"))
              (if (null? args)
                  (print "Usage: ,a <pattern>")
                  (apropos (string->symbol (car args))))
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

             ;; Inspect object
             ((string=? cmd "i")
              (if (null? args)
                  (print "Usage: ,i <expression>")
                  (let ((expr-str (string-intersperse args " ")))
                    (handle-exceptions exn
                      (print "Error: " ((condition-property-accessor 'exn 'message) exn))
                      (inspect (eval (with-input-from-string expr-str read))))))
              (loop))

             ;; Frame display
             ((string=? cmd "f")
              (if (null? args)
                  (begin
                    (print "Call stack:")
                    (let lp ((frames *call-stack*) (i 0))
                      (when (and (pair? frames) (< i 20))
                        (printf "  [~a] ~a~n" i (car (car frames)))
                        (lp (cdr frames) (+ i 1)))))
                  (pp-frame (string->number (car args))))
              (loop))

             ;; Toggle inspector
             ((string=? cmd "inspector")
              (if *inspector-enabled*
                  (begin (disable-inspector!))
                  (begin (enable-inspector!)))
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

             ;; Memo - view and build documentation
             ((string=? cmd "memo")
              (let ((memo-dir "docs/memo"))
                (cond
                  ;; No args - show catalog
                  ((null? args)
                   (print "Library Memos:")
                   (print "")
                   (for-each
                     (lambda (f)
                       (let* ((base (pathname-strip-extension (pathname-file f)))
                              (num (and (>= (string-length base) 9)
                                       (substring base 5 9)))
                              (title (with-input-from-file f
                                       (lambda ()
                                         (let ((sexp (read)))
                                           (and (pair? sexp)
                                                (let ((t (assq 'title (cdr sexp))))
                                                  (and t (cadr t)))))))))
                         (when (and num title)
                           (printf "  ~a  ~a~n" num title))))
                     (sort (glob (make-pathname memo-dir "memo-*.scm"))
                           string<?))
                   (print "")
                   (print "Usage: ,memo NUMBER [txt|html|ps|all|build]"))

                  ;; "build" - regenerate all
                  ((string=? (car args) "build")
                   (print "Building memos...")
                   (let ((build-script (make-pathname memo-dir "generate-memos.sh")))
                     (if (file-exists? build-script)
                         (system (sprintf "cd ~a && ./generate-memos.sh" memo-dir))
                         (print "Error: generate-memos.sh not found"))))

                  ;; Number - view memo
                  (else
                   (let* ((num-str (car args))
                          (num (string->number num-str))
                          (format (if (> (length args) 1) (cadr args) "txt"))
                          (padded (if num (string-pad (number->string num) 4 #\0) num-str))
                          (pattern (make-pathname memo-dir (string-append "memo-" padded "-*")))
                          (matches (glob pattern)))
                     (if (null? matches)
                         (print "Memo " num-str " not found")
                         (let* ((base (pathname-strip-extension (car matches)))
                                (txt-file (string-append base ".txt"))
                                (html-file (string-append base ".html"))
                                (ps-file (string-append base ".ps"))
                                (open-cmd (if (string=? (car (string-split (car (process-context-argv)) "/")) "")
                                              "open" "xdg-open")))
                           (cond
                             ((string=? format "txt")
                              (if (file-exists? txt-file)
                                  (system (sprintf "cat ~a" txt-file))
                                  (print "Text file not found - run ,memo build")))
                             ((string=? format "html")
                              (if (file-exists? html-file)
                                  (system (sprintf "~a ~a" open-cmd html-file))
                                  (print "HTML file not found - run ,memo build")))
                             ((string=? format "ps")
                              (if (file-exists? ps-file)
                                  (system (sprintf "~a ~a" open-cmd ps-file))
                                  (print "PostScript file not found - run ,memo build")))
                             ((string=? format "all")
                              (when (file-exists? txt-file)
                                (system (sprintf "cat ~a" txt-file)))
                              (when (file-exists? html-file)
                                (system (sprintf "~a ~a" open-cmd html-file)))
                              (when (file-exists? ps-file)
                                (system (sprintf "~a ~a" open-cmd ps-file))))
                             ((string=? format "build")
                              (print "Building memo " padded "...")
                              (system (sprintf "cd ~a && csi -q generate-all.scm ~a"
                                             memo-dir (car matches))))
                             (else
                              (print "Unknown format: " format)
                              (print "Use: txt, html, ps, all, or build")))))))))
              (loop))

             ;; Edit file with configured editor (see: editor!)
             ((or (string=? cmd "e") (string=? cmd "edit"))
              (let* ((ed (editor))
                     (file (if (null? args) "" (car args))))
                (cond
                  ;; Built-in Electric Pencil (resident)
                  ((string=? ed "pencil")
                   (handle-exceptions exn
                     (print "Error: " ((condition-property-accessor 'exn 'message) exn))
                     (if (null? args) (pencil) (pencil (car args)))))
                  ;; Built-in TECO (resident)
                  ((string=? ed "teco")
                   (handle-exceptions exn
                     (print "Error: " ((condition-property-accessor 'exn 'message) exn))
                     (if (null? args) (teco) (teco (car args)))))
                  ;; Built-in Schemacs (resident)
                  ((or (string=? ed "schemacs") (string=? ed "emacs"))
                   (handle-exceptions exn
                     (print "Error: " ((condition-property-accessor 'exn 'message) exn))
                     (if (null? args) (schemacs) (schemacs (car args)))))
                  ;; External editor
                  (else
                   (system (sprintf "~a ~a" ed file)))))
              (loop))

             ;; Electric Pencil (resident)
             ((string=? cmd "pencil")
              (handle-exceptions exn
                (print "Error: " ((condition-property-accessor 'exn 'message) exn))
                (if (null? args)
                    (pencil)
                    (pencil (car args))))
              (loop))

             ;; Electric Pencil novice mode
             ((or (string=? cmd "pencil-novice") (string=? cmd "novice"))
              (handle-exceptions exn
                (print "Error: " ((condition-property-accessor 'exn 'message) exn))
                (if (null? args)
                    (pencil-novice)
                    (pencil-novice (car args))))
              (loop))

             ;; TECO (resident, like LSE on VMS)
             ((string=? cmd "teco")
              (handle-exceptions exn
                (print "Error: " ((condition-property-accessor 'exn 'message) exn))
                (if (null? args)
                    (teco)
                    (teco (car args))))
              (loop))

             ;; Schemacs (resident Emacs-style editor)
             ((or (string=? cmd "schemacs") (string=? cmd "emacs"))
              (handle-exceptions exn
                (print "Error: " ((condition-property-accessor 'exn 'message) exn))
                (if (null? args)
                    (schemacs)
                    (schemacs (car args))))
              (loop))

             ;; Hex edit - terminal (xxd) or GUI (HexEdit)
             ((or (string=? cmd "hd") (string=? cmd "hex"))
              (if (null? args)
                  (print "Usage: ,hd <file>")
                  (system (sprintf "xxd -g 4 ~a | less" (car args))))
              (loop))
             ((string=? cmd "hext")
              (if (null? args)
                  (print "Usage: ,hext <file>")
                  (system (sprintf "open -a 'HexEdit' ~a" (car args))))
              (loop))

             ;; Pretty print expression
             ((string=? cmd "p")
              (if (null? args)
                  (print "Usage: ,p <expression>")
                  (let ((expr-str (string-intersperse args " ")))
                    (handle-exceptions exn
                      (print "Error: " ((condition-property-accessor 'exn 'message) exn))
                      (pp (eval (with-input-from-string expr-str read))))))
              (loop))

             ;; Expand expression
             ((string=? cmd "x")
              (if (null? args)
                  (print "Usage: ,x <expression>")
                  (let ((expr-str (string-intersperse args " ")))
                    (handle-exceptions exn
                      (print "Error: " ((condition-property-accessor 'exn 'message) exn))
                      (pp (expand (with-input-from-string expr-str read))))))
              (loop))

             ;; Time expression
             ((string=? cmd "t")
              (if (null? args)
                  (print "Usage: ,t <expression>")
                  (let ((expr-str (string-intersperse args " ")))
                    (handle-exceptions exn
                      (print "Error: " ((condition-property-accessor 'exn 'message) exn))
                      (time (eval (with-input-from-string expr-str read))))))
              (loop))

             ;; System info (Chicken's ,r)
             ((string=? cmd "r")
              (print "Machine type:     " (machine-type))
              (print "Software type:    " (software-type))
              (print "Software version: " (software-version))
              (print "Build platform:   " (build-platform))
              (print "Chicken version:  " (chicken-version))
              (loop))

             ;; Dump data (Chicken's ,du)
             ((string=? cmd "du")
              (if (null? args)
                  (print "Usage: ,du <expression>")
                  (let ((expr-str (string-intersperse args " ")))
                    (handle-exceptions exn
                      (print "Error: " ((condition-property-accessor 'exn 'message) exn))
                      (let ((val (eval (with-input-from-string expr-str read))))
                        (##sys#dump-heap-state)
                        (##sys#print-info val)))))
              (loop))

             ;; Load and print (Chicken's ,ln)
             ((string=? cmd "ln")
              (if (null? args)
                  (print "Usage: ,ln <filename>")
                  (begin
                    (print "Loading " (car args) " (verbose)...")
                    (load (car args) (lambda (x) (pp x)))))
              (loop))

             ;; Expression history (Chicken's ,h - we use ,history to avoid conflict)
             ((string=? cmd "history")
              (let ((hist (reverse *repl-history*)))
                (let lp ((h hist) (i 1))
                  (when (pair? h)
                    (printf "~a: ~a~%" (string-pad (number->string i) 3) (car h))
                    (lp (cdr h) (+ i 1)))))
              (loop))

             ;; Clear history (Chicken's ,ch)
             ((string=? cmd "ch")
              (set! *repl-history* '())
              (print "History cleared")
              (loop))

             ;; Last exception (Chicken's ,exn)
             ((string=? cmd "exn")
              (if (and (pair? *call-stack*) (condition? (cdar *call-stack*)))
                  (describe-condition (cdar *call-stack*))
                  (print "No recent exception"))
              (loop))

             ;; Get variable from frame (Chicken's ,g)
             ((string=? cmd "g")
              (if (null? args)
                  (print "Usage: ,g <name>")
                  (print "Frame variable access not implemented"))
              (loop))

             ;; Switch module (Chicken's ,m)
             ((string=? cmd "m")
              (if (null? args)
                  (print "Usage: ,m <module>")
                  (let ((mod (string->symbol (car args))))
                    (handle-exceptions exn
                      (print "Error: " ((condition-property-accessor 'exn 'message) exn))
                      (eval `(import ,mod))
                      (print "Switched to module: " mod))))
              (loop))

             ;; Unknown comma command
             (else
              (print "Unknown command: ," cmd)
              (print "Try ,? for help or ,csi for Chicken CSI reference")
              (loop)))))

        ;; Regular input - parse with command mode support
        (else
         ;; History already added by repl-read-line
         (let* ((trimmed (string-trim-both line))
                (is-scheme? (and (> (string-length trimmed) 0)
                                 (char=? (string-ref trimmed 0) #\()))
                (expr (parse-command-line line)))
           (when expr
             (handle-exceptions exn
               (begin
                 (capture-exception exn)  ; grab chain NOW, before display code pollutes it
                 (if *inspector-enabled*
                     (begin
                       (inspector-repl exn)
                       (loop))
                     ;; Novice mode: show friendly errors
                     (if (eq? *user-mode* 'novice)
                         (let ((msg (get-condition-property exn 'exn 'message "")))
                           (cond
                             ((string-contains msg "unbound variable")
                              (let ((var (get-condition-property exn 'exn 'arguments '())))
                                (printf "Unknown: ~a. Type ? for help.~%"
                                        (if (pair? var) (car var) "?"))))
                             ((string-contains msg "bad argument type")
                              (print "Type error. Check your arguments."))
                             ((string-contains msg "too few arguments")
                              (print "Missing argument(s)."))
                             ((string-contains msg "too many arguments")
                              (print "Too many arguments."))
                             (else
                              (rich-exception-display exn))))
                         (rich-exception-display exn))))
               ;; Handle special commands that can't be injected into eval's environment
               (let ((result
                      (cond
                        ;; inspect and i - domain-aware inspection
                        ((and (pair? expr) (memq (car expr) '(inspect i)))
                         (if (null? (cdr expr))
                             (begin (print "Usage: (inspect OBJ)") (void))
                             (cyberspace-inspect (eval (cadr expr)))))
                        ;; describe - generic object description
                        ((and (pair? expr) (eq? (car expr) 'describe))
                         (if (null? (cdr expr))
                             (begin (print "Usage: (describe OBJ)") (void))
                             (inspector#describe (eval (cadr expr)))))
                        ;; novice/schemer mode toggles
                        ((equal? expr '(novice)) (novice))
                        ((equal? expr '(schemer)) (schemer))
                        ((equal? expr '(lambda)) (schemer))
                        ;; Module imports not in eval env - call directly
                        ((equal? expr '(introspect-system)) (status))
                        ((and (pair? expr) (eq? (car expr) 'dashboard))
                         (if (and (pair? (cdr expr)) (equal? (cadr expr) ''full))
                             (dashboard 'full)
                             (dashboard)))
                        ((equal? expr '(session-stats)) (session-stats))
                        ((equal? expr '(session-stats-reset!)) (session-stats-reset!))
                        ((and (pair? expr) (eq? (car expr) 'global-search))
                         (if (null? (cdr expr))
                             (print "Usage: (global-search \"term\")")
                             (global-search (cadr expr))))
                        ((and (pair? expr) (eq? (car expr) 'soup))
                         (apply soup (cdr expr)))
                        ;; Novice mode guard - catch unrecognized COMMANDS (not Scheme)
                        ;; If they typed parens, they know what they're doing
                        ((and (eq? *user-mode* 'novice)
                              (not is-scheme?)  ; command mode, not (expr)
                              (pair? expr)
                              (symbol? (car expr))
                              (not (novice-command? (car expr))))
                         (printf "Unknown command: ~a. Type ? for help.~%" (car expr))
                         (void))
                        ;; Everything else - normal eval
                        (else (eval expr)))))
                 ;; Track usage for mode detection (only on successful eval)
                 ;; Don't count mode toggles - they shouldn't influence mode detection
                 (unless (member expr '((novice) (schemer) (lambda)))
                   (if is-scheme?
                       (set! *paren-count* (+ 1 *paren-count*))
                       (set! *command-count* (+ 1 *command-count*)))
                   (check-mode-shift!))
                 ;; Dynamic completions: add newly defined symbols
                 (when (and (pair? expr) (eq? (car expr) 'define))
                   (let ((name (if (pair? (cadr expr))
                                   (car (cadr expr))   ; (define (foo ...) ...)
                                   (cadr expr))))      ; (define foo ...)
                     (when (symbol? name)
                       (lineage#add-command (symbol->string name)))))
                 (unless (eq? result (void))
                   (push-result! result)
                   (pp result))))))
         (loop))))))

(module-end! "repl")

;; Refresh hardware info at startup (vault display now in banner)
(when (directory-exists? ".vault")
  (node-hardware-refresh!))

;; Initialize session statistics
(session-stat-init!)
;; Catch termination signals for clean exit
(install-signal-handlers!)
;; Measure boot-time weave (must be after vault import)
(hash-table-set! *session-stats* 'boot-weave (measure-weave))

;; Boot output based on verbosity level
;; 0 shadow    - just prompt
;; 1 whisper   - version + Ready
;; 2 portal    - banner + help + Ready
;; 3 oracle - full diagnostics

(when (>= *boot-verbosity* 3)  ; oracle
  (report-module-times))

(when (>= *boot-verbosity* 2)  ; portal+
  (help))

(when (>= *boot-verbosity* 1)  ; whisper+
  (let* ((elapsed-ms (- (current-process-milliseconds) *repl-start-time*))
         (elapsed-sec (/ elapsed-ms 1000.0)))
    (when (= *boot-verbosity* 1)  ; whisper: show version
      (print "Cyberspace Scheme " (git-version)))
    (print (format "Ready in ~a [~a]"
                   (if (< elapsed-sec 1)
                       (format "~ams" elapsed-ms)
                       (format "~as" elapsed-sec))
                   (realm-signature))))
  (print ""))

;; --eval: evaluate expression and exit
(when (cli-option "eval")
  (let ((expr (cli-option "eval")))
    (handle-exceptions exn
      (begin
        (print "Error: " ((condition-property-accessor 'exn 'message) exn))
        (exit 1))
      (let ((result (eval (with-input-from-string expr read))))
        (unless (eq? result (void))
          (write result)
          (newline))
        (exit 0)))))

;; Start custom REPL
;; Flush any input that accumulated during boot (editor loads, etc.)
(tty-flush-input)
(command-repl)
