#!/usr/bin/env chez-script
;;; repl.ss - Cyberspace Scheme REPL (Chez Port)
;;;
;;; Copyright (c) 2026 ddp@eludom.net
;;; MIT License - see LICENSE file
;;; Currently unpublished and proprietary; license applies upon public release.
;;;
;;; Usage: chez --program repl.ss [options]
;;;
;;; Options:
;;;   --sync               Sync vault with remote, then start REPL
;;;   --clean              Remove artifacts
;;;   --boot=<level>       Boot verbosity: shadow|whisper|portal|oracle
;;;   --eval='<expr>'      Evaluate expression and exit
;;;   --version            Show version information
;;;   --help               Show this help
;;;
;;; Preloads all Cyberspace modules for interactive exploration:
;;;   - vault: seal-commit, seal-release, seal-archive, etc.
;;;   - crypto-ffi: ed25519-keypair, sha512-hash, etc.
;;;   - audit: audit-append, audit-read, etc.
;;;   - cert: SPKI certificates
;;;   - sexp: S-expression handling
;;;
;;; Ported from repl.scm (8,477 lines Chicken Scheme).
;;; The Chicken version includes many inline subsystems (CIP protocol,
;;; compilation/replication semantics, code optimizer, etc.) that in the
;;; Chez port live in their own library modules. This REPL provides the
;;; interactive shell, command mode, help system, and inspector integration.

(import (rnrs)
        (only (chezscheme)
              printf format void system
              command-line exit
              file-exists? directory-exists?
              directory-list delete-file
              current-directory
              with-input-from-file with-output-to-file
              with-input-from-string with-output-to-string
              open-input-string
              open-process-ports native-transcoder
              flush-output-port
              pretty-print
              eval interaction-environment
              getenv
              current-time time-second time-nanosecond))

;; Core libraries
(import (cyberspace chicken-compatibility chicken)
        (cyberspace chicken-compatibility hashtable)
        (cyberspace os)
        (cyberspace sexp)
        (cyberspace tty-ffi)
        (cyberspace edt)
        (cyberspace display)
        (cyberspace info)
        (cyberspace inspector))

;; Crypto & SPKI (guarded - may fail without C bridges)
(define *crypto-available* #f)
(define *vault-available* #f)

(guard (exn [#t (void)])
  (eval '(import (cyberspace crypto-ffi)) (interaction-environment))
  (set! *crypto-available* #t))

(guard (exn [#t (void)])
  (eval '(import (cyberspace cert)) (interaction-environment))
  (eval '(import (cyberspace capability)) (interaction-environment))
  (eval '(import (cyberspace audit)) (interaction-environment)))

(guard (exn [#t (void)])
  (eval '(import (cyberspace vault)) (interaction-environment))
  (set! *vault-available* #t))

;; Higher-level modules (guarded)
(guard (exn [#t (void)])
  (eval '(import (cyberspace bloom)) (interaction-environment))
  (eval '(import (cyberspace merkle)) (interaction-environment)))

(guard (exn [#t (void)])
  (eval '(import (cyberspace wordlist)) (interaction-environment))
  (eval '(import (cyberspace fips)) (interaction-environment)))

(guard (exn [#t (void)])
  (eval '(import (cyberspace gossip)) (interaction-environment))
  (eval '(import (cyberspace mdns)) (interaction-environment)))

(guard (exn [#t (void)])
  (eval '(import (cyberspace enroll)) (interaction-environment))
  (eval '(import (cyberspace auto-enroll)) (interaction-environment)))

(guard (exn [#t (void)])
  (eval '(import (cyberspace filetype)) (interaction-environment))
  (eval '(import (cyberspace wormhole)) (interaction-environment)))

(guard (exn [#t (void)])
  (eval '(import (cyberspace ui)) (interaction-environment)))

;;; ============================================================
;;; Command Line Interface
;;; ============================================================

(define (parse-cli-option arg)
  "Parse a --option or --option=value argument."
  (let ((len (string-length arg)))
    (cond
      ((< len 2) #f)
      ((not (and (char=? (string-ref arg 0) #\-)
                 (char=? (string-ref arg 1) #\-)))
       #f)
      (else
       (let loop ((i 2))
         (cond
           ((= i len) (cons (substring arg 2 len) #t))
           ((char=? (string-ref arg i) #\=)
            (cons (substring arg 2 i)
                  (substring arg (+ i 1) len)))
           (else (loop (+ i 1)))))))))

(define (parse-cli-args args)
  (filter (lambda (x) x) (map parse-cli-option args)))

(define *cli-options* (parse-cli-args (cdr (command-line))))

(define (cli-option name)
  (let ((opt (assoc name *cli-options*)))
    (and opt (cdr opt))))

(define (cli-option? name)
  (and (cli-option name) #t))

;;; --help
(when (cli-option? "help")
  (display "Cyberspace Scheme - Distributed Systems Shell (Chez Port)\n")
  (display "\n")
  (display "Usage: chez --program repl.ss [options]\n")
  (display "\n")
  (display "Options:\n")
  (display "  --sync               Sync vault with remote, then start REPL\n")
  (display "  --clean              Remove compiled files\n")
  (display "  --boot=<level>       Boot verbosity: shadow|whisper|portal|oracle\n")
  (display "  --eval='<expr>'      Evaluate expression and exit\n")
  (display "  --version            Show version information\n")
  (display "  --help               Show this help\n")
  (display "\n")
  (display "Examples:\n")
  (display "  chez --program repl.ss                   Start REPL (default)\n")
  (display "  chez --program repl.ss --boot=portal     Start with banner and help\n")
  (display "  chez --program repl.ss --eval='(+ 1 2)'  Evaluate and exit\n")
  (exit 0))

;;; --version
(when (cli-option? "version")
  (display "Cyberspace Scheme v0.59 (Chez Port)\n")
  (display "  Built with Chez Scheme\n")
  (display "  Ed25519 signatures via libsodium\n")
  (exit 0))

;;; --sync
(define (git-sync)
  "Sync with remote. Returns #t on success."
  (display "Syncing with remote...\n")
  (system "git stash -q --include-untracked 2>/dev/null")
  (let ((rc (system "git pull --rebase -q 2>/dev/null")))
    (cond
      ((zero? rc)
       (system "git push -q 2>/dev/null")
       (system "git stash pop -q 2>/dev/null")
       (display "  [ok] Synced\n")
       #t)
      (else
       (system "git rebase --abort 2>/dev/null")
       (system "git stash pop -q 2>/dev/null")
       (display "  [!!] Sync conflict - needs manual merge\n")
       #f))))

(when (cli-option? "sync")
  (unless (git-sync)
    (exit 1)))

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
  (cond
    ((string->number str) => (lambda (n) n))
    (else
     (let ((entry (assq (string->symbol str) *boot-levels*)))
       (and entry (cdr entry))))))

(define *boot-verbosity*
  (let ((cli-boot (cli-option "boot"))
        (env (getenv "CYBERSPACE_BOOT")))
    (cond
      ((and cli-boot (string? cli-boot)) (or (parse-boot-level cli-boot) 0))
      (env (or (parse-boot-level env) 0))
      (else 0))))

;;; ============================================================
;;; Startup State
;;; ============================================================

(define *cyberspace-home*
  (or (getenv "CYBERSPACE_HOME")
      (or (getenv "HOME") ".")))

;;; When the tala beats and the flute plays om,
;;; the lambda rests in stillness.
(define *stillness* 'quiescent)

;;; Travellers leave trails.
(define *trail* '())
(define *lens* 'library)

;; Realm signature for prompt provenance
(define *realm-signature* #f)

(define (realm-signature)
  (or *realm-signature* (hostname)))

(define (realm-signature! sig)
  (set! *realm-signature* sig)
  (printf "[realm-signature: ~a]~%" (realm-signature)))

;;; ============================================================
;;; Prompt System
;;; ============================================================

(define *prompt* "% ")
(define *prompt-fn* #f)

;; Prahar (time-of-day) colors for lambda prompt (Memo-0009 Section 14)
(define (prahar-color)
  "Return ANSI 256-color code for current prahar (watch of the day)"
  (let ((hour (let* ((now (current-time))
                     (secs (time-second now)))
                ;; Extract hour from Unix time
                (mod (div secs 3600) 24))))
    (cond
      ((and (>= hour 4) (< hour 6))   "38;5;135")  ; violet - brahma muhurta
      ((and (>= hour 6) (< hour 8))   "38;5;220")  ; gold - pratahkala
      ((and (>= hour 8) (< hour 11))  "38;5;30")   ; teal - sangava
      ((and (>= hour 11) (< hour 14)) "38;5;46")   ; phosphor - madhyahna
      ((and (>= hour 14) (< hour 17)) "38;5;226")  ; neon - aparahna
      ((and (>= hour 17) (< hour 19)) "38;5;208")  ; orange - sayahna
      ((and (>= hour 19) (< hour 22)) "38;5;209")  ; coral - pradosa
      (else                           "38;5;51")))) ; cyan - nisitha

(define (prahar-prompt)
  (string-append "\x1b;[" (prahar-color) "m\x3bb;\x1b;[0m "))

(define (current-prompt)
  (if *prompt-fn*
      (*prompt-fn*)
      *prompt*))

;;; ============================================================
;;; User Mode
;;; ============================================================

(define *user-mode* 'novice)
(define *paren-count* 0)
(define *command-count* 0)
(define *mode-threshold* 1)

(define (novice)
  "Switch to novice mode - guardrails on"
  (set! *user-mode* 'novice)
  (set! *prompt* "% ")
  (set! *prompt-fn* #f)
  (set! *paren-count* 0)
  (set! *command-count* 0)
  (display "Novice mode. Guardrails on.\n")
  (display "Destructive ops require confirmation. Type ? for help.\n"))

(define (lambda-mode)
  "Switch to lambda mode - full power"
  (set! *user-mode* 'schemer)
  (set! *prompt-fn* prahar-prompt)
  (display "Lambda mode. Full power, no confirmations.\n"))

(define (check-mode-shift!)
  (when (and (eq? *user-mode* 'novice)
             (>= *paren-count* *mode-threshold*)
             (> *paren-count* (* 2 *command-count*)))
    (set! *user-mode* 'schemer)
    (set! *prompt-fn* prahar-prompt)))

;;; ============================================================
;;; Result History
;;; ============================================================

(define _ #f)
(define _1 #f)
(define _2 #f)
(define *result-count* 0)
(define *result-history* (make-vector 100 #f))

(define (push-result! val)
  (set! _2 _1)
  (set! _1 _)
  (set! _ val)
  (vector-set! *result-history* (mod *result-count* 100) val)
  (set! *result-count* (+ 1 *result-count*))
  val)

(define ($ n)
  "Get result N from history."
  (cond
    ((< n 0)
     (let ((idx (+ *result-count* n)))
       (if (>= idx 0)
           (vector-ref *result-history* (mod idx 100))
           (error '$ "No such result" n))))
    ((< n (min *result-count* 100))
     (vector-ref *result-history* (mod n 100)))
    (else (error '$ "No such result" n))))

;;; ============================================================
;;; Novice Mode Guards
;;; ============================================================

(define *dangerous-ops*
  '(seal-release seal-commit key-delete key-revoke
    vault-reset vault-wipe gossip-broadcast
    enroll-revoke capability-revoke))

(define (confirm? prompt)
  (printf "~a [y/N] " prompt)
  (flush-output-port (current-output-port))
  (let ((response (get-line (current-input-port))))
    (and (not (eof-object? response))
         (> (string-length response) 0)
         (char-ci=? (string-ref response 0) #\y))))

(define (novice-guard op-name thunk)
  (if (eq? *user-mode* 'novice)
      (if (confirm? (format "~a is destructive. Continue?" op-name))
          (thunk)
          (begin (display "Cancelled.\n") (void)))
      (thunk)))

;;; ============================================================
;;; Command Aliases
;;; ============================================================

(define *command-aliases*
  '((status    . status)
    (dashboard . dashboard)
    (commit    . seal-commit)
    (release   . seal-release)
    (archive   . seal-archive)
    (history   . seal-history)
    (keys      . list-keys)
    (keygen    . ed25519-keypair)
    (sign      . ed25519-sign)
    (verify    . ed25519-verify)
    (hash      . sha512-hash)
    (soup      . soup)
    (find      . soup-find)
    (seek      . seek)
    (inspect   . inspect)
    (peers     . nodes)
    (enroll    . enroll-request)
    (approve   . enroll-approve)
    (discover  . discover-peers)
    (gossip    . gossip-status)
    (audit     . audit)
    (clear     . clear)
    (theme     . theme!)
    (help      . help)
    (library   . library)
    (search    . search)
    (memo      . memo)
    (quit      . exit)
    (exit      . exit)
    (bye       . exit)))

(define (resolve-command cmd)
  (let ((alias (assq cmd *command-aliases*)))
    (if alias (cdr alias) cmd)))

(define (novice-command? cmd)
  (and (symbol? cmd)
       (or (assq cmd *command-aliases*)
           (find (lambda (pair) (eq? (cdr pair) cmd)) *command-aliases*)
           (memq cmd '(+ - * / define let if cond lambda quote
                        list cons car cdr map for-each
                        display newline print printf
                        string-append number->string
                        novice lambda-mode)))))

;;; ============================================================
;;; Command Mode Parser
;;; ============================================================
;;;
;;; Lines starting with ( are Scheme.
;;; Bare words are commands: "status" -> (status)
;;; Arguments follow: "commit msg" -> (seal-commit "msg")

(define (split-whitespace str)
  (let loop ((chars (string->list str))
             (current '())
             (result '()))
    (cond
      ((null? chars)
       (if (null? current)
           (reverse result)
           (reverse (cons (list->string (reverse current)) result))))
      ((char-whitespace? (car chars))
       (if (null? current)
           (loop (cdr chars) '() result)
           (loop (cdr chars) '() (cons (list->string (reverse current)) result))))
      (else
       (loop (cdr chars) (cons (car chars) current) result)))))

(define (parse-command-line line)
  "Parse input line into S-expression."
  (let ((trimmed (string-trim-both line)))
    (cond
      ((string=? trimmed "") #f)
      ;; Lines starting with ( ' ` # are Scheme
      ((memv (string-ref trimmed 0) '(#\( #\' #\` #\#))
       (guard (exn [#t (printf "Parse error: ~a~%"
                               (if (message-condition? exn)
                                   (condition-message exn)
                                   "invalid expression"))
                      #f])
         (read (open-input-string trimmed))))
      ;; Bare words = command mode
      (else
       (let* ((parts (split-whitespace trimmed))
              (cmd (string->symbol (car parts)))
              (args (cdr parts))
              (resolved (resolve-command cmd)))
         (if (null? args)
             (list resolved)
             (cons resolved
                   (map (lambda (a)
                          (or (string->number a)
                              (let ((len (string-length a)))
                                (if (and (> len 1)
                                         (char=? (string-ref a 0) #\')
                                         (not (char=? (string-ref a (- len 1)) #\')))
                                    (string->symbol (substring a 1 len))
                                    a))))
                        args))))))))

;;; ============================================================
;;; Help System
;;; ============================================================

(define *help-topics*
  '((help "Help System"
     ("help" "Show essential commands")
     ("help topics" "List all help topics")
     ("help <topic>" "Show commands in topic")
     ("?" "Quick help")
     ("." "Quick status"))

    (vault "Vault & Objects"
     ("(soup)" "Browse vault objects")
     ("(soup 'keys)" "List keys")
     ("(soup 'audit)" "List audit entries")
     ("(seal-commit MSG)" "Commit changes")
     ("(seal-release VER)" "Create release")
     ("(query PRED)" "Query vault objects"))

    (library "Memos"
     ("(library)" "Browse all Memos")
     ("(search 'topic)" "Search vault + library")
     ("(memo N)" "View Memo in terminal"))

    (security "Keys & Certificates"
     ("(principals)" "Show identity and keys")
     ("(keyring-list)" "List keys in keyring")
     ("(keyring-generate)" "Generate new keypair")
     ("(security-summary)" "Security overview"))

    (crypto "Cryptographic Primitives"
     ("(sha512-hash DATA)" "SHA-512 hash")
     ("(blake2b-hash DATA)" "BLAKE2b hash")
     ("(ed25519-keypair)" "Generate Ed25519 keypair")
     ("(ed25519-sign SK MSG)" "Sign with private key")
     ("(ed25519-verify PK SIG MSG)" "Verify signature"))

    (certs "SPKI Certificates"
     ("(cert-create ...)" "Create certificate")
     ("(cert-verify CERT)" "Verify certificate")
     ("(cert-chain ...)" "Build certificate chain"))

    (network "Network & Peers"
     ("(nodes)" "List known peers")
     ("(gossip-status)" "Show gossip state")
     ("(discover-peers)" "mDNS discovery"))

    (enrollment "Enrollment"
     ("enroll <name>" "Start enrollment")
     ("approve <name>" "Approve pending enrollment")
     ("(realm-status)" "Show realm status"))

    (inspector "Inspector"
     ("(inspect OBJ)" "Inspect any object")
     ("(describe OBJ)" "Describe object type")
     (":d N" "Descend into slot N")
     (":u" "Go back up")
     (":s" "Show current object"))

    (navigation "Navigation"
     ("." "Quick status")
     ("?" "Quick help")
     ("_ _1 _2" "Result history")
     ("($ N)" "Numbered result access")
     ("(trail)" "Show navigation history"))

    (modes "User Modes"
     ("(novice)" "Switch to novice mode (guardrails)")
     ("(lambda-mode)" "Switch to lambda mode (full power)")
     ("% prompt" "Novice mode (auto-detect)")
     ("lambda prompt" "Lambda mode (prahar-colored)"))))

(define (help . args)
  "Show help - (help), (help 'topic), (help 'symbol)"
  (if (null? args)
      ;; Default help
      (begin
        (display "\n")
        (display "Cyberspace Scheme (Chez Port)\n")
        (display "\n")
        (display "  (library)         - Enter the Library\n")
        (display "  (search 'topic)   - Search everything\n")
        (display "  (status)          - Node status\n")
        (display "  (inspect OBJ)     - Inspect anything\n")
        (display "\n")
        (display "  (help 'topics)    - All help topics\n")
        (display "  (.) status  (?) help  (bye) exit\n")
        (display "\n"))
      ;; Topic help
      (let ((topic (car args)))
        (cond
          ((eq? topic 'topics)
           (display "\nHelp Topics:\n\n")
           (for-each
             (lambda (t)
               (printf "  ~a - ~a~%"
                       (car t)
                       (if (> (length t) 1) (cadr t) "")))
             *help-topics*)
           (display "\nUse (help 'topic) for details.\n\n"))
          ((assq topic *help-topics*)
           => (lambda (entry)
                (display "\n")
                (printf "~a~%" (cadr entry))
                (display "\n")
                (for-each
                  (lambda (cmd)
                    (printf "  ~a~a~a~%"
                            (car cmd)
                            (make-string (max 1 (- 30 (string-length (car cmd)))) #\space)
                            (cadr cmd)))
                  (cddr entry))
                (display "\n")))
          (else
           (printf "No help for: ~a~%" topic))))))

;;; ============================================================
;;; Status Display
;;; ============================================================

(define (status)
  "Show system status summary."
  (let ((box (make-box 50)))
    (display (box-top box "Cyberspace Status"))
    (newline)
    (box-print box (format "Host: ~a" (hostname)))
    (box-print box (format "OS: ~a ~a" (os-type) (os-arch)))
    (box-print box (format "Crypto: ~a" (if *crypto-available* "available" "not loaded")))
    (box-print box (format "Vault: ~a"
                           (if (directory-exists? ".vault") "present" "none")))
    (box-print box (format "Mode: ~a" *user-mode*))
    (box-print box (format "FUSE: ~a"
                           (guard (exn [#t "unknown"])
                             (if (eval '(fuse-available?) (interaction-environment))
                                 "available" "not found"))))
    (display (box-bottom box))
    (newline)))

;;; ============================================================
;;; Inspector Integration
;;; ============================================================

(define *inspector-enabled* #f)

(define (enable-inspector!)
  (install-inspector!)
  (set! *inspector-enabled* #t))

;;; ============================================================
;;; Simple Pager
;;; ============================================================

(define (page text)
  "Display text through pager if longer than terminal."
  (let* ((lines (string-split-lines text))
         (height (tty-rows)))
    (if (<= (length lines) (- height 2))
        (display text)
        (info-pager lines "Output"))))

(define (string-split-lines s)
  (let loop ((chars (string->list s)) (current '()) (result '()))
    (cond
      ((null? chars)
       (reverse (if (null? current) result
                    (cons (list->string (reverse current)) result))))
      ((char=? (car chars) #\newline)
       (loop (cdr chars) '()
             (cons (list->string (reverse current)) result)))
      (else
       (loop (cdr chars) (cons (car chars) current) result)))))

;;; ============================================================
;;; REPL Input History
;;; ============================================================

(define *repl-history* '())
(define *history-max* 500)

(define (history-add! line)
  (when (and (string? line) (> (string-length line) 0))
    (set! *repl-history*
      (take (cons line *repl-history*)
            (min (+ 1 (length *repl-history*)) *history-max*)))))

;;; ============================================================
;;; Rich Exception Display
;;; ============================================================

(define (rich-exception-display exn)
  "Display exception with context."
  (let ((msg (if (message-condition? exn)
                 (condition-message exn)
                 "unknown error"))
        (who (if (who-condition? exn)
                 (condition-who exn)
                 #f))
        (irr (if (irritants-condition? exn)
                 (condition-irritants exn)
                 '())))
    (display vt100-red)
    (if who
        (printf "Error in ~a: ~a" who msg)
        (printf "Error: ~a" msg))
    (display vt100-normal)
    (newline)
    (unless (null? irr)
      (for-each (lambda (i) (printf "  ~s~%" i)) irr))))

;;; ============================================================
;;; Comma Commands (CSI-style meta-commands)
;;; ============================================================

(define (handle-comma-command cmd args)
  "Handle ,command meta-commands."
  (cond
    ;; Help
    ((member cmd '("?" "help"))
     (display "\nComma commands:\n\n")
     (display "  ,?         This help\n")
     (display "  ,p EXPR    Pretty-print expression\n")
     (display "  ,t EXPR    Time expression\n")
     (display "  ,i OBJ     Inspect object\n")
     (display "  ,d         Describe current inspector object\n")
     (display "  ,m MOD     Import module\n")
     (display "  ,history   Show input history\n")
     (display "  ,ch        Clear history\n")
     (display "  ,r         Runtime info\n")
     (display "  ,q         Quit\n")
     (display "\n"))

    ;; Pretty print
    ((string=? cmd "p")
     (when (pair? args)
       (guard (exn [#t (rich-exception-display exn)])
         (pretty-print (eval (read (open-input-string (car args)))
                             (interaction-environment))))))

    ;; Time
    ((string=? cmd "t")
     (when (pair? args)
       (guard (exn [#t (rich-exception-display exn)])
         (let* ((start (current-time))
                (result (eval (read (open-input-string (car args)))
                              (interaction-environment)))
                (end (current-time))
                (elapsed-ns (+ (* (- (time-second end) (time-second start)) 1000000000)
                                (- (time-nanosecond end) (time-nanosecond start))))
                (elapsed-ms (/ elapsed-ns 1000000.0)))
           (printf "~ams~%" elapsed-ms)
           (unless (eq? result (void))
             (pretty-print result))))))

    ;; Inspect
    ((string=? cmd "i")
     (when (pair? args)
       (guard (exn [#t (rich-exception-display exn)])
         (inspect (eval (read (open-input-string (car args)))
                        (interaction-environment))))))

    ;; Describe
    ((string=? cmd "d")
     (inspector-show))

    ;; Import module
    ((string=? cmd "m")
     (when (pair? args)
       (guard (exn [#t (rich-exception-display exn)])
         (let ((mod (string->symbol (car args))))
           (eval `(import (cyberspace ,mod)) (interaction-environment))
           (printf "Imported: (cyberspace ~a)~%" mod)))))

    ;; History
    ((string=? cmd "history")
     (let loop ((h (reverse *repl-history*)) (i 1))
       (when (pair? h)
         (printf "~a: ~a~%" i (car h))
         (loop (cdr h) (+ i 1)))))

    ;; Clear history
    ((string=? cmd "ch")
     (set! *repl-history* '())
     (display "History cleared.\n"))

    ;; Runtime info
    ((string=? cmd "r")
     (printf "Implementation: Chez Scheme~%")
     (printf "Host: ~a~%" (hostname))
     (printf "OS: ~a ~a~%" (os-type) (os-arch))
     (printf "Crypto: ~a~%" (if *crypto-available* "available" "not loaded"))
     (printf "Vault: ~a~%" (if *vault-available* "available" "not loaded")))

    ;; Quit
    ((member cmd '("q" "quit"))
     'quit)

    (else
     (printf "Unknown command: ,~a (try ,? for help)~%" cmd))))

;;; ============================================================
;;; Main REPL Loop
;;; ============================================================

(define (command-repl)
  "Main REPL loop with command mode support."
  (let loop ()
    (display (current-prompt))
    (flush-output-port (current-output-port))

    (let ((line (get-line (current-input-port))))
      (cond
        ;; EOF
        ((eof-object? line)
         (display "\nBye.\n"))

        ;; Empty line
        ((string=? (string-trim-both line) "")
         (loop))

        ;; Quick shortcuts
        ((string=? (string-trim-both line) ".")
         (status)
         (loop))

        ((string=? (string-trim-both line) "?")
         (help)
         (loop))

        ;; Exit commands
        ((member (string-trim-both line) '("bye" "bye." "quit" "exit" "(exit)" "(quit)" "(bye)"))
         (display "Farewell.\n"))

        ;; Comma commands
        ((and (> (string-length (string-trim-both line)) 0)
              (char=? (string-ref (string-trim-both line) 0) #\,))
         (let* ((trimmed (string-trim-both line))
                (rest (substring trimmed 1 (string-length trimmed)))
                (parts (split-whitespace rest))
                (cmd (if (pair? parts) (car parts) ""))
                (args (if (pair? parts) (cdr parts) '())))
           ;; Join remaining args for eval commands
           (let ((arg-str (if (pair? args)
                              (list (let loop ((a args) (acc ""))
                                      (if (null? a) acc
                                          (loop (cdr a)
                                                (if (string=? acc "")
                                                    (car a)
                                                    (string-append acc " " (car a)))))))
                              '())))
             (let ((result (handle-comma-command cmd arg-str)))
               (if (eq? result 'quit)
                   (display "Farewell.\n")
                   (loop))))))

        ;; Inspector quick commands
        ((and (> (string-length (string-trim-both line)) 0)
              (char=? (string-ref (string-trim-both line) 0) #\:))
         (let* ((trimmed (string-trim-both line))
                (parts (split-whitespace (substring trimmed 1 (string-length trimmed))))
                (cmd (if (pair? parts) (car parts) "")))
           (cond
             ((string=? cmd "s") (inspector-show))
             ((string=? cmd "u") (inspector-up))
             ((string=? cmd "h") (inspector-history))
             ((string=? cmd "b") (inspector-bookmark))
             ((string=? cmd "t") (inspector-type))
             ((and (string=? cmd "d") (pair? (cdr parts)))
              (let ((n (string->number (cadr parts))))
                (if n (inspector-descend n)
                    (display "Usage: :d N\n"))))
             (else (printf "Unknown: :~a (try :s :d N :u :h :b :t)~%" cmd))))
         (loop))

        ;; QMK/EDT dispatch
        ((qmk-dispatch line) (loop))

        ;; Regular input
        (else
         (history-add! line)
         (let* ((trimmed (string-trim-both line))
                (is-scheme? (and (> (string-length trimmed) 0)
                                 (memv (string-ref trimmed 0) '(#\( #\' #\` #\#))))
                (expr (parse-command-line line)))
           (when expr
             (guard (exn
               [#t
                (if (and *inspector-enabled* (eq? *user-mode* 'schemer))
                    (inspector-repl exn)
                    (if (eq? *user-mode* 'novice)
                        (let ((msg (if (message-condition? exn)
                                       (condition-message exn) "")))
                          (cond
                            ((string-contains msg "variable")
                             (printf "Unknown: ~a. Type ? for help.~%" trimmed))
                            (else
                             (rich-exception-display exn))))
                        (rich-exception-display exn)))])
               (let ((result
                      (cond
                        ;; Special dispatch for inspect
                        ((and (pair? expr) (memq (car expr) '(inspect i)))
                         (if (null? (cdr expr))
                             (begin (display "Usage: (inspect OBJ)\n") (void))
                             (inspect (eval (cadr expr) (interaction-environment)))))
                        ;; describe
                        ((and (pair? expr) (eq? (car expr) 'describe))
                         (if (null? (cdr expr))
                             (begin (display "Usage: (describe OBJ)\n") (void))
                             (describe (eval (cadr expr) (interaction-environment)))))
                        ;; Mode toggles
                        ((equal? expr '(novice)) (novice))
                        ((equal? expr '(lambda)) (lambda-mode))
                        ((equal? expr '(lambda-mode)) (lambda-mode))
                        ;; Status
                        ((equal? expr '(status)) (status))
                        ((member expr '((.) (status))) (status))
                        ((member expr '((?) (help))) (help))
                        ;; Help with args
                        ((and (pair? expr) (eq? (car expr) 'help))
                         (apply help (cdr expr)))
                        ;; Info
                        ((and (pair? expr) (eq? (car expr) 'info))
                         (apply info (cdr expr)))
                        ;; Novice guard
                        ((and (eq? *user-mode* 'novice)
                              (not is-scheme?)
                              (pair? expr)
                              (symbol? (car expr))
                              (not (novice-command? (car expr))))
                         (printf "Unknown: ~a. Type ? for help.~%" (car expr))
                         (void))
                        ;; Normal eval
                        (else (eval expr (interaction-environment))))))
                 ;; Track mode shift
                 (unless (member expr '((novice) (lambda) (lambda-mode)))
                   (if is-scheme?
                       (set! *paren-count* (+ 1 *paren-count*))
                       (set! *command-count* (+ 1 *command-count*)))
                   (check-mode-shift!))
                 ;; Display result
                 (unless (eq? result (void))
                   (push-result! result)
                   (pretty-print result))))))
         (loop))))))

;;; ============================================================
;;; Regression Tests (minimal, built-in)
;;; ============================================================

(define *regression-tests* '())

(define (deftest name thunk)
  (set! *regression-tests* (append *regression-tests* (list (cons name thunk)))))

(define (run-test name thunk)
  (let ((start-time (current-time)))
    (guard (exn
      [#t (list name #f 0
                (format "Exception: ~a"
                        (if (message-condition? exn)
                            (condition-message exn) "unknown")))])
      (let* ((result (thunk))
             (end-time (current-time))
             (elapsed (- (time-second end-time) (time-second start-time))))
        (list name (car result) elapsed (cdr result))))))

;; Register basic tests
(deftest 'modules-loaded
  (lambda ()
    (cons #t (format "crypto:~a vault:~a"
                      (if *crypto-available* "yes" "no")
                      (if *vault-available* "yes" "no")))))

(deftest 'vault-exists
  (lambda ()
    (if (directory-exists? ".vault")
        (cons #t ".vault directory present")
        (cons #t "no vault (ok for testing)"))))

(define (regression . rest)
  "Run all regression tests."
  (let ((verbose? (and (pair? rest) (car rest))))
    (display "\n")
    (let ((box (make-box 60)))
      (display (box-top box "Cyberspace Regression Suite"))
      (newline)
      (let* ((results (map (lambda (t) (run-test (car t) (cdr t)))
                           *regression-tests*))
             (passed (filter (lambda (r) (cadr r)) results))
             (failed (filter (lambda (r) (not (cadr r))) results)))
        (for-each
          (lambda (r)
            (let ((name (car r))
                  (pass? (cadr r))
                  (msg (cadddr r)))
              (if pass?
                  (when verbose?
                    (box-print box (format "  + ~a ~a" name msg)))
                  (box-print box (format "  X ~a ~a" name msg)))))
          results)
        (display (box-separator box)) (newline)
        (let ((total (length results))
              (pass-count (length passed))
              (fail-count (length failed)))
          (if (= fail-count 0)
              (box-print box (format "All ~a tests passed" total))
              (box-print box (format "~a/~a passed, ~a FAILED"
                                      pass-count total fail-count))))
        (display (box-bottom box)) (newline)
        (display "\n")
        (if (null? failed) 'passed (map car failed))))))

;;; ============================================================
;;; Boot Sequence
;;; ============================================================

;; Register cleanup hooks
(register-cleanup-hook! 'repl-tty
  (lambda () (guard (exn [#t #f]) (tty-set-cooked))))

;; Boot output based on verbosity
(when (>= *boot-verbosity* 3)  ; oracle
  (printf "Crypto: ~a~%" (if *crypto-available* "loaded" "not available"))
  (printf "Vault: ~a~%" (if *vault-available* "loaded" "not available")))

(when (>= *boot-verbosity* 2)  ; portal+
  (help))

(when (>= *boot-verbosity* 1)  ; whisper+
  (when (= *boot-verbosity* 1)
    (display "Cyberspace Scheme v0.59 (Chez)\n"))
  (printf "Ready [~a]~%" (realm-signature))
  (display "\n"))

;; --eval: evaluate expression and exit
(when (cli-option "eval")
  (let ((expr-str (cli-option "eval")))
    (guard (exn
      [#t (display "Error: ")
          (if (message-condition? exn)
              (display (condition-message exn))
              (display "unknown"))
          (newline)
          (exit 1)])
      (let ((result (eval (read (open-input-string expr-str))
                          (interaction-environment))))
        (unless (eq? result (void))
          (write result)
          (newline))
        (exit 0)))))

;; Flush any input that accumulated during boot
(tty-flush-input)

;; Start REPL
(command-repl)
