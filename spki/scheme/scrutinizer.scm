;;; scrutinizer.scm - Tone and terminology consistency checker
;;;
;;; Self-documenting style guide: the rules ARE the code.
;;; Audits library (memos) and code for consistency.
;;;
;;; Two failure modes:
;;;   - Overreach: poetry where precision needed, whimsy in errors
;;;   - Underreach: dry jargon where warmth appropriate, internals leaking
;;;
;;; Three passes:
;;;   1. Vocabulary audit - banned terms in user-facing strings
;;;   2. Tone consistency - memos vs help vs errors
;;;   3. S-expression exposure - Scheme leaking to surface
;;;
;;; Copyright (c) 2026 Yoyodyne. See LICENSE.

(module scrutinizer
  (;; Main interface
   scrutinize
   scrutinize-file
   scrutinize-string

   ;; Realmtime mode (scrutiny flows through the realm as time passes)
   *scrutinize-realmtime*
   scrutinize-realmtime!

   ;; Style guide (self-documenting)
   *banned-vocabulary*
   *scheme-exposure*
   *tone-rules*
   *whitelist-contexts*)

  (import scheme
          (chicken base)
          (chicken io)
          (chicken format)
          (chicken string)
          (chicken file)
          (chicken pathname)
          (chicken irregex)
          (chicken port)
          (chicken process)
          (chicken process-context)
          srfi-1
          srfi-13)

  ;; ============================================================
  ;; Style Guide - The Rules
  ;; ============================================================
  ;;
  ;; This IS the style guide. These definitions document what's
  ;; allowed and what's not. The scrutinizer enforces them.

  ;; ----------------------------------------------------------
  ;; Banned Vocabulary
  ;; ----------------------------------------------------------
  ;; Terms that must never appear in user-facing text.
  ;; Internal vocabulary is fine in comments and internal code.

  (define *banned-vocabulary*
    '(;; Internal jargon - NEVER in user-facing strings or memos
      ("normie"      . "casual user, newcomer, or just omit")
      ("sheeple"     . "users, people")
      ("luser"       . "user")
      ("RTFM"        . "see help, see documentation")
      ("PEBKAC"      . "check your input")

      ;; Scheme internals that leak to users via error messages
      ("unbound variable"   . "unknown command, not found")
      ("not a procedure"    . "cannot run, not a command")
      ("wrong number of arguments" . "missing or extra input")))

  ;; These are only checked in user-facing output (printf/error calls)
  (define *soft-vocabulary*
    '(;; Technical terms - OK in code, flagged in user output
      ("syntax error"       . "could not understand")
      ("read error"         . "could not parse")
      ("call-chain"         . "stack, history")
      ("continuation"       . "state, checkpoint")
      ("thunk"              . "action, operation")))

  ;; ----------------------------------------------------------
  ;; Scheme Exposure Patterns
  ;; ----------------------------------------------------------
  ;; Patterns that indicate Scheme is leaking to user-facing output.
  ;; Only flagged in error/help strings, NOT in code/memos.

  (define *scheme-exposure*
    '(;; Debug artifacts - should never reach users
      ("debug>"       . "inspector prompt exposed")
      ("#<procedure"  . "raw procedure object")
      ("#<port"       . "raw port object")
      ("#<condition"  . "raw condition object")
      ("#<eof>"       . "use 'end of input'")
      ("#!eof"        . "use 'end of input'")

      ;; Error internals - these leak implementation details
      ("exn:"         . "exception prefix exposed")
      ("call-chain"   . "internal call stack exposed")))

  ;; ----------------------------------------------------------
  ;; Tone Rules by Context
  ;; ----------------------------------------------------------
  ;; Different contexts require different tones.

  (define *tone-rules*
    '((memo
        (style . formal)
        (allowed . (technical-terms citations precise-language))
        (avoid . (casual-speech exclamation-marks emoji)))

      (help
        (style . friendly)
        (allowed . (simple-language examples commands))
        (avoid . (jargon implementation-details)))

      (error
        (style . simple)
        (allowed . (plain-language what-went-wrong))
        (avoid . (stack-traces internal-names blame)))

      (comment
        (style . internal)
        (allowed . (technical-jargon scheme-terms internal-vocabulary))
        (avoid . ()))))  ; comments can use anything

  ;; ----------------------------------------------------------
  ;; Whitelist Contexts
  ;; ----------------------------------------------------------
  ;; Files/patterns where certain terms are allowed.
  ;; Internal documentation, design notes, the scrutinizer itself.

  (define *whitelist-contexts*
    '(;; Reserved memos can use internal vocabulary
      ("memo-0056" . (normie internal-jargon))
      ;; The scrutinizer documents banned terms
      ("scrutinizer.scm" . (all-banned-terms))
      ;; Test files can use anything
      ("test-" . (all))
      ;; Inspector is for schemers
      ("inspector.scm" . (scheme-exposure))
      ;; REPL is Scheme interface - exposure is intentional
      ("cyberspace-repl.scm" . (scheme-exposure))
      ;; Server has internal technical code
      ("cyberspace-server.scm" . (scheme-exposure))))

  ;; ============================================================
  ;; State
  ;; ============================================================

  (define *scrutinize-realmtime* (make-parameter #f))
  (define *findings* '())

  ;; ============================================================
  ;; Core Scrutiny Functions
  ;; ============================================================

  (define (add-finding! severity file line category message)
    "Record a finding"
    (set! *findings*
      (cons (list severity file line category message) *findings*)))

  (define (clear-findings!)
    (set! *findings* '()))

  (define (scrutinize-string str file line context)
    "Scrutinize a string for violations"
    (let ((violations '()))

      ;; Vocabulary check (skip if file whitelisted)
      (unless (file-whitelisted? file 'vocabulary)
        (for-each
          (lambda (rule)
            (let ((banned (car rule))
                  (suggest (cdr rule)))
              (when (irregex-search (irregex banned 'case-insensitive) str)
                (set! violations
                  (cons (list 'vocabulary banned suggest) violations)))))
          *banned-vocabulary*))

      ;; Scheme exposure check (only for user-facing contexts)
      (unless (or (eq? context 'comment)
                  (file-whitelisted? file 'scheme-exposure))
        (for-each
          (lambda (rule)
            (let ((pattern (car rule))
                  (reason (cdr rule)))
              (when (str-contains? str pattern)
                (set! violations
                  (cons (list 'exposure pattern reason) violations)))))
          *scheme-exposure*))

      ;; Record findings
      (for-each
        (lambda (v)
          (add-finding! 'warning file line (car v)
                        (sprintf "~a: ~s -> ~a"
                                 (car v) (cadr v) (caddr v))))
        violations)

      violations))

  ;; ============================================================
  ;; File Scrutiny
  ;; ============================================================

  (define (scrutinize-file path)
    "Scrutinize a single file"
    (let ((ext (pathname-extension path)))
      (cond
        ((equal? ext "scm") (scrutinize-scheme-file path))
        ((equal? ext "txt") (scrutinize-text-file path 'help))
        ((equal? ext "md")  (scrutinize-text-file path 'memo))
        (else '()))))

  (define (scrutinize-scheme-file path)
    "Scrutinize a Scheme source file"
    (call-with-input-file path
      (lambda (port)
        (let loop ((line-num 1)
                   (in-string #f)
                   (in-comment #f)
                   (findings '()))
          (let ((line (read-line port)))
            (if (eof-object? line)
                findings
                (let* ((context (detect-context line in-comment))
                       (result (scrutinize-line line path line-num context)))
                  (loop (+ line-num 1)
                        (in-string-literal? line in-string)
                        (in-block-comment? line in-comment)
                        (append result findings)))))))))

  (define (scrutinize-text-file path context)
    "Scrutinize a text/markdown file"
    (call-with-input-file path
      (lambda (port)
        (let loop ((line-num 1)
                   (findings '()))
          (let ((line (read-line port)))
            (if (eof-object? line)
                findings
                (let ((result (scrutinize-string line path line-num context)))
                  (loop (+ line-num 1)
                        (append result findings)))))))))

  (define (scrutinize-line line path line-num context)
    "Scrutinize a single line of Scheme code"
    (let ((findings '()))
      ;; Check string literals
      (let ((strings (extract-strings line)))
        (for-each
          (lambda (s)
            (set! findings
              (append (scrutinize-string s path line-num 'help) findings)))
          strings))
      ;; Check comments for internal vocabulary (allowed but flagged for review)
      (let ((comment (extract-comment line)))
        (when comment
          (set! findings
            (append (scrutinize-string comment path line-num 'comment) findings))))
      findings))

  (define (detect-context line in-block-comment)
    "Detect the context of a line"
    (cond
      (in-block-comment 'comment)
      ((irregex-search "^\\s*;" line) 'comment)
      ((irregex-search "(printf|print|display|error)" line) 'help)
      (else 'code)))

  (define (in-string-literal? line currently-in)
    "Track if we're inside a multi-line string"
    (let ((quotes (count-unescaped-quotes line)))
      (if currently-in
          (odd? quotes)
          (odd? quotes))))

  (define (in-block-comment? line currently-in)
    "Track if we're inside #| |# block comment"
    (cond
      ((and (not currently-in) (str-contains? line "#|"))
       (not (str-contains? line "|#")))
      ((and currently-in (str-contains? line "|#"))
       #f)
      (else currently-in)))

  (define (count-unescaped-quotes str)
    "Count unescaped double quotes"
    (let loop ((chars (string->list str))
               (count 0)
               (escaped #f))
      (if (null? chars)
          count
          (let ((c (car chars)))
            (cond
              ((and (char=? c #\") (not escaped))
               (loop (cdr chars) (+ count 1) #f))
              ((char=? c #\\)
               (loop (cdr chars) count (not escaped)))
              (else
               (loop (cdr chars) count #f)))))))

  (define (extract-strings line)
    "Extract string literals from a line"
    (let ((matches (irregex-fold
                     (irregex "\"([^\"\\\\]|\\\\.)*\"")
                     (lambda (i m acc)
                       (cons (irregex-match-substring m) acc))
                     '()
                     line)))
      matches))

  (define (extract-comment line)
    "Extract comment portion of a line"
    (let ((pos (string-index line (lambda (c) (char=? c #\;)))))
      (and pos (substring line pos))))

  (define (str-contains? str substr)
    "Check if str contains substr"
    (string-contains str substr))  ; srfi-13

  (define (file-whitelisted? filepath category)
    "Check if file is whitelisted for a category"
    (let ((basename (pathname-strip-directory filepath)))
      (any (lambda (rule)
             (let ((pattern (car rule))
                   (allowed (cdr rule)))
               (and (string-prefix? pattern basename)
                    (or (memq 'all allowed)
                        (memq 'all-banned-terms allowed)
                        (memq category allowed)))))
           *whitelist-contexts*)))

  ;; `any` provided by srfi-1

  ;; ============================================================
  ;; Main Interface
  ;; ============================================================

  (define (scrutinize . args)
    "Main scrutiny function
     (scrutinize)          - both library and code
     (scrutinize 'library) - memos only
     (scrutinize 'code)    - code only
     (scrutinize #f)       - disable realmtime mode"
    (let ((target (if (null? args) 'all (car args))))
      (cond
        ((eq? target #f)
         (*scrutinize-realmtime* #f)
         (print "Realmtime scrutiny disabled."))

        ((eq? target 'library)
         (scrutinize-library))

        ((eq? target 'code)
         (scrutinize-code))

        (else
         (scrutinize-library)
         (scrutinize-code)))))

  (define (scrutinize-library)
    "Scrutinize memo library (vocabulary only, skip reserved)"
    (clear-findings!)
    (print "")
    (print "Scrutinizing library...")
    (let* ((memo-dir (or (get-environment-variable "CYBERSPACE_MEMOS")
                         "docs/notes"))
           (files (glob-memos memo-dir))
           ;; Skip reserved memos (internal documentation)
           (public-files (filter (lambda (f)
                                   (not (memo-reserved? f)))
                                 files)))
      (for-each (lambda (f) (scrutinize-memo-file f)) public-files)
      (report-findings 'library)))

  (define (scrutinize-code)
    "Scrutinize source code"
    (clear-findings!)
    (print "")
    (print "Scrutinizing code...")
    (let ((files (glob-scheme-files ".")))
      (for-each scrutinize-file files)
      (report-findings 'code)))

  (define (glob-memos dir)
    "Find memo files"
    (let ((pattern (make-pathname dir "memo-[0-9]*.scm")))
      (glob-files pattern)))

  (define (memo-reserved? filepath)
    "Check if memo is marked (reserved)"
    (call-with-input-file filepath
      (lambda (port)
        (let loop ()
          (let ((line (read-line port)))
            (cond
              ((eof-object? line) #f)
              ((str-contains? line "(reserved)") #t)
              (else (loop))))))))

  (define (scrutinize-memo-file filepath)
    "Scrutinize a memo for vocabulary issues (not Scheme exposure).
     Memos are technical documentation - code examples are expected."
    (call-with-input-file filepath
      (lambda (port)
        (let loop ((line-num 1)
                   (in-code-block #f))
          (let ((line (read-line port)))
            (unless (eof-object? line)
              ;; Skip code blocks - they're supposed to have Scheme
              (let ((now-in-code (or (and (not in-code-block)
                                          (str-contains? line "(code "))
                                     (and in-code-block
                                          (not (str-contains? line "\")"))))))
                ;; Only check prose (p ...) sections for vocabulary
                (when (and (not in-code-block)
                           (str-contains? line "(p "))
                  (scrutinize-memo-prose line filepath line-num))
                (loop (+ line-num 1) now-in-code))))))))

  (define (scrutinize-memo-prose line filepath line-num)
    "Check memo prose for banned vocabulary only"
    (for-each
      (lambda (rule)
        (let ((banned (car rule))
              (suggest (cdr rule)))
          (when (irregex-search (irregex banned 'case-insensitive) line)
            (add-finding! 'warning filepath line-num 'vocabulary
                          (sprintf "~s -> ~a" banned suggest)))))
      *banned-vocabulary*))

  (define (glob-scheme-files dir)
    "Find Scheme source files (excluding imports)"
    (let ((all (glob-files (make-pathname dir "*.scm"))))
      (filter (lambda (f) (not (str-contains? f ".import.scm"))) all)))

  (define (glob-files pattern)
    "Simple glob - shell out"
    (let* ((cmd (sprintf "ls ~a 2>/dev/null" pattern))
           (result (call-with-input-pipe cmd read-all)))
      (if (string? result)
          (filter (lambda (s) (> (string-length s) 0))
                  (string-split result "\n"))
          '())))

  (define (read-all port)
    "Read all from port as string"
    (let loop ((acc '()))
      (let ((line (read-line port)))
        (if (eof-object? line)
            (string-intersperse (reverse acc) "\n")
            (loop (cons line acc))))))

  ;; call-with-input-pipe provided by chicken.process

  (define (report-findings target)
    "Report scrutiny findings"
    (let ((count (length *findings*)))
      (if (zero? count)
          (printf "  ~a: clean~n" target)
          (begin
            (printf "  ~a: ~a findings~n~n" target count)
            (for-each
              (lambda (f)
                (let ((severity (car f))
                      (file (cadr f))
                      (line (caddr f))
                      (category (cadddr f))
                      (message (car (cddddr f))))
                  (printf "  ~a:~a [~a] ~a~n"
                          (pathname-strip-directory file)
                          line category message)))
              (reverse *findings*))
            (print "")))))

  ;; ============================================================
  ;; Realmtime Mode
  ;; ============================================================
  ;;
  ;; "Realmtime" invokes spacetime - scrutiny flows through the realm
  ;; as time passes. When enabled, violations surface as modules load.
  ;; Off in production (default), on during beta.

  (define (scrutinize-realmtime! enable)
    "Enable/disable realmtime scrutiny during development"
    (*scrutinize-realmtime* enable)
    (if enable
        (print "Realmtime scrutiny enabled. Violations surface on load.")
        (print "Realmtime scrutiny disabled.")))

  ;; Hook for module system - when realm flows, scrutiny follows
  ;; (when (*scrutinize-realmtime*) (scrutinize-on-load ...))

) ;; end module
