;;; scrutinizer.sls - Tone and terminology consistency checker
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

(library (cyberspace scrutinizer)
  (export
    ;; Main interface
    scrutinize
    scrutinize-file
    scrutinize-string

    ;; Polish mode
    scrutinize-polish
    *polish-patterns*

    ;; Realmtime mode
    scrutinize-realmtime?
    scrutinize-realmtime!

    ;; Style guide (self-documenting)
    *banned-vocabulary*
    *scheme-exposure*
    *tone-rules*
    *whitelist-contexts*)

  (import (rnrs)
          (only (chezscheme)
                printf format with-output-to-string
                file-directory? directory-list
                getenv sort make-parameter parameterize)
          (cyberspace chicken-compatibility chicken))

  ;; ============================================================
  ;; String Helpers (replacing irregex/srfi-13)
  ;; ============================================================

  (define (string-contains haystack needle)
    (let ((nlen (string-length needle))
          (hlen (string-length haystack)))
      (let loop ((i 0))
        (cond
          ((> (+ i nlen) hlen) #f)
          ((string=? needle (substring haystack i (+ i nlen))) i)
          (else (loop (+ i 1)))))))

  (define (string-contains-ci haystack needle)
    (string-contains (string-downcase haystack) (string-downcase needle)))

  (define (string-prefix? prefix str)
    (let ((plen (string-length prefix))
          (slen (string-length str)))
      (and (<= plen slen)
           (string=? prefix (substring str 0 plen)))))

  (define (string-suffix? suffix str)
    (let ((xlen (string-length suffix))
          (slen (string-length str)))
      (and (<= xlen slen)
           (string=? suffix (substring str (- slen xlen) slen)))))

  (define (string-trim-both str)
    (let* ((len (string-length str))
           (start (let loop ((i 0))
                    (if (or (>= i len) (not (char-whitespace? (string-ref str i))))
                        i
                        (loop (+ i 1)))))
           (end (let loop ((i (- len 1)))
                  (if (or (< i start) (not (char-whitespace? (string-ref str i))))
                      (+ i 1)
                      (loop (- i 1))))))
      (substring str start end)))

  (define (string-index str pred)
    (let ((len (string-length str)))
      (let loop ((i 0))
        (cond
          ((>= i len) #f)
          ((pred (string-ref str i)) i)
          (else (loop (+ i 1)))))))

  (define (pathname-strip-directory path)
    (let ((idx (let loop ((i (- (string-length path) 1)))
                 (cond ((< i 0) #f)
                       ((char=? (string-ref path i) #\/) i)
                       (else (loop (- i 1)))))))
      (if idx
          (substring path (+ idx 1) (string-length path))
          path)))

  (define (pathname-extension path)
    (let ((base (pathname-strip-directory path)))
      (let ((idx (let loop ((i (- (string-length base) 1)))
                   (cond ((< i 0) #f)
                         ((char=? (string-ref base i) #\.) i)
                         (else (loop (- i 1)))))))
        (if idx
            (substring base (+ idx 1) (string-length base))
            #f))))

  (define (read-lines port)
    (let loop ((lines '()))
      (let ((line (get-line port)))
        (if (eof-object? line)
            (reverse lines)
            (loop (cons line lines))))))

  ;; ============================================================
  ;; Style Guide - The Rules
  ;; ============================================================

  (define *banned-vocabulary*
    '(("normie"      . "newcomer, casual user, or just omit")
      ("sheeple"     . "users, people")
      ("luser"       . "user")
      ("RTFM"        . "see help, see documentation")
      ("PEBKAC"      . "check your input")
      ("unbound variable"   . "unknown command, not found")
      ("not a procedure"    . "cannot run, not a command")
      ("wrong number of arguments" . "missing or extra input")))

  (define *soft-vocabulary*
    '(("syntax error"       . "could not understand")
      ("read error"         . "could not parse")
      ("call-chain"         . "stack, history")
      ("continuation"       . "state, checkpoint")
      ("thunk"              . "action, operation")))

  (define *scheme-exposure*
    '(("debug>"       . "inspector prompt exposed")
      ("#<procedure"  . "raw procedure object")
      ("#<port"       . "raw port object")
      ("#<condition"  . "raw condition object")
      ("#<eof>"       . "use 'end of input'")
      ("#!eof"        . "use 'end of input'")
      ("exn:"         . "exception prefix exposed")
      ("call-chain"   . "internal call stack exposed")))

  (define *header-banned*
    '(("Copyright"    . "no copyright in headers")
      ("LICENSE"      . "no license refs in headers")
      ("All rights"   . "no legal boilerplate")))

  (define *polish-patterns*
    '(("Auto-converted from Markdown"  . "remove stale conversion comment")
      ("Review and edit as needed"     . "remove stale review comment")))

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
        (avoid . ()))))

  (define *whitelist-contexts*
    '(("memo-0056" . (internal-jargon))
      ("scrutinizer" . (all-banned-terms))
      ("test-" . (all))
      ("inspector" . (scheme-exposure))
      ("repl" . (scheme-exposure))
      ("server" . (scheme-exposure))))

  ;; ============================================================
  ;; State
  ;; ============================================================

  (define *scrutinize-realmtime* (make-parameter #f))
  (define *findings* '())

  (define (scrutinize-realmtime?) (*scrutinize-realmtime*))

  ;; ============================================================
  ;; Core Scrutiny Functions
  ;; ============================================================

  (define (add-finding! severity file line category message)
    (set! *findings*
      (cons (list severity file line category message) *findings*)))

  (define (clear-findings!)
    (set! *findings* '()))

  (define (scrutinize-string str file line context)
    (let ((violations '()))

      ;; Vocabulary check (skip if file whitelisted)
      (unless (file-whitelisted? file 'vocabulary)
        (for-each
          (lambda (rule)
            (let ((banned (car rule))
                  (suggest (cdr rule)))
              (when (string-contains-ci str banned)
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
              (when (string-contains str pattern)
                (set! violations
                  (cons (list 'exposure pattern reason) violations)))))
          *scheme-exposure*))

      ;; Record findings
      (for-each
        (lambda (v)
          (add-finding! 'warning file line (car v)
                        (format #f "~a: ~s -> ~a"
                                 (car v) (cadr v) (caddr v))))
        violations)

      violations))

  ;; ============================================================
  ;; File Scrutiny
  ;; ============================================================

  (define (scrutinize-file path)
    (let ((ext (pathname-extension path)))
      (cond
        ((equal? ext "scm") (scrutinize-scheme-file path))
        ((equal? ext "sls") (scrutinize-scheme-file path))
        ((equal? ext "txt") (scrutinize-text-file path 'help))
        ((equal? ext "md")  (scrutinize-text-file path 'memo))
        (else '()))))

  (define (scrutinize-scheme-file path)
    (call-with-input-file path
      (lambda (port)
        (let loop ((line-num 1)
                   (in-string #f)
                   (in-comment #f)
                   (in-header #t)
                   (findings '()))
          (let ((line (get-line port)))
            (if (eof-object? line)
                findings
                (let* ((context (detect-context line in-comment))
                       (still-header (and in-header
                                          (or (string-prefix? ";;;" line)
                                              (= 0 (string-length (string-trim-both line))))))
                       (result (scrutinize-line line path line-num context))
                       (header-result (if (and in-header (string-prefix? ";;;" line))
                                          (scrutinize-header line path line-num)
                                          '())))
                  (loop (+ line-num 1)
                        (in-string-literal? line in-string)
                        (in-block-comment? line in-comment)
                        still-header
                        (append header-result result findings)))))))))

  (define (scrutinize-header line path line-num)
    (let ((violations '()))
      (for-each
        (lambda (rule)
          (let ((banned (car rule))
                (reason (cdr rule)))
            (when (string-contains line banned)
              (add-finding! 'warning path line-num 'header
                            (format #f "~s: ~a" banned reason))
              (set! violations (cons (list 'header banned reason) violations)))))
        *header-banned*)
      violations))

  (define (scrutinize-text-file path context)
    (call-with-input-file path
      (lambda (port)
        (let loop ((line-num 1)
                   (findings '()))
          (let ((line (get-line port)))
            (if (eof-object? line)
                findings
                (let ((result (scrutinize-string line path line-num context)))
                  (loop (+ line-num 1)
                        (append result findings)))))))))

  (define (scrutinize-line line path line-num context)
    (let ((findings '()))
      ;; Check string literals
      (let ((strings (extract-strings line)))
        (for-each
          (lambda (s)
            (set! findings
              (append (scrutinize-string s path line-num 'help) findings)))
          strings))
      ;; Check comments
      (let ((comment (extract-comment line)))
        (when comment
          (set! findings
            (append (scrutinize-string comment path line-num 'comment) findings))))
      findings))

  (define (detect-context line in-block-comment)
    (cond
      (in-block-comment 'comment)
      ((and (> (string-length line) 0) (char=? (string-ref line 0) #\;)) 'comment)
      ((or (string-contains line "printf")
           (string-contains line "display")
           (string-contains line "error")) 'help)
      (else 'code)))

  (define (in-string-literal? line currently-in)
    (let ((quotes (count-unescaped-quotes line)))
      (if currently-in
          (odd? quotes)
          (odd? quotes))))

  (define (in-block-comment? line currently-in)
    (cond
      ((and (not currently-in) (string-contains line "#|"))
       (not (string-contains line "|#")))
      ((and currently-in (string-contains line "|#"))
       #f)
      (else currently-in)))

  (define (count-unescaped-quotes str)
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
    ;; Simple string literal extraction (not regex-based)
    (let ((len (string-length line)))
      (let loop ((i 0) (in-str #f) (start 0) (escaped #f) (result '()))
        (if (>= i len)
            (reverse result)
            (let ((c (string-ref line i)))
              (cond
                ((and escaped in-str)
                 (loop (+ i 1) #t start #f result))
                ((and in-str (char=? c #\\))
                 (loop (+ i 1) #t start #t result))
                ((and in-str (char=? c #\"))
                 (loop (+ i 1) #f 0 #f
                       (cons (substring line start (+ i 1)) result)))
                ((and (not in-str) (char=? c #\"))
                 (loop (+ i 1) #t i #f result))
                (else
                 (loop (+ i 1) in-str start #f result))))))))

  (define (extract-comment line)
    (let ((pos (string-index line (lambda (c) (char=? c #\;)))))
      (and pos (substring line pos (string-length line)))))

  (define (file-whitelisted? filepath category)
    (let ((basename (pathname-strip-directory filepath)))
      (exists (lambda (rule)
                (let ((pattern (car rule))
                      (allowed (cdr rule)))
                  (and (string-contains basename pattern)
                       (or (memq 'all allowed)
                           (memq 'all-banned-terms allowed)
                           (memq category allowed)))))
              *whitelist-contexts*)))

  ;; ============================================================
  ;; Main Interface
  ;; ============================================================

  (define (scrutinize . args)
    (let ((target (if (null? args) 'all (car args))))
      (cond
        ((eq? target #f)
         (*scrutinize-realmtime* #f)
         (printf "Realmtime scrutiny disabled.~%"))

        ((eq? target 'library)
         (scrutinize-library))

        ((eq? target 'code)
         (scrutinize-code))

        ((eq? target 'polish)
         (scrutinize-polish))

        (else
         (scrutinize-library)
         (scrutinize-code)))))

  (define (scrutinize-library)
    (clear-findings!)
    (printf "~%Scrutinizing library...~%")
    (let* ((memo-dir (or (getenv "CYBERSPACE_MEMOS") "docs/notes"))
           (files (glob-memos memo-dir))
           (public-files (filter (lambda (f)
                                   (not (memo-reserved? f)))
                                 files)))
      (for-each scrutinize-memo-file public-files)
      (report-findings 'library)))

  (define (scrutinize-code)
    (clear-findings!)
    (printf "~%Scrutinizing code...~%")
    (let ((files (glob-scheme-files ".")))
      (for-each scrutinize-file files)
      (report-findings 'code)))

  (define (scrutinize-polish)
    (clear-findings!)
    (printf "~%Scrutinizing for polish...~%")
    (let* ((memo-dir (or (getenv "CYBERSPACE_MEMOS") "docs/notes"))
           (files (glob-memos memo-dir)))
      (for-each scrutinize-memo-polish files)
      (report-findings 'polish)))

  (define (scrutinize-memo-polish filepath)
    (call-with-input-file filepath
      (lambda (port)
        (let ((has-blockquote #f)
              (basename (pathname-strip-directory filepath)))
          (let loop ((line-num 1))
            (let ((line (get-line port)))
              (unless (eof-object? line)
                (when (string-contains line "Auto-converted from Markdown")
                  (add-finding! 'polish filepath line-num 'stale-comment
                                "remove 'Auto-converted from Markdown' comment"))
                (when (string-contains line "Review and edit as needed")
                  (add-finding! 'polish filepath line-num 'stale-comment
                                "remove 'Review and edit as needed' comment"))
                (when (string-contains line "#### ")
                  (add-finding! 'polish filepath line-num 'markdown
                                "markdown header - use (subsection ...)"))
                (when (string-contains line "(blockquote")
                  (set! has-blockquote #t))
                (loop (+ line-num 1)))))
          (unless has-blockquote
            (add-finding! 'suggestion filepath 1 'narrative
                          "consider adding opening blockquote"))))))

  (define (glob-memos dir)
    (if (and (file-exists? dir) (file-directory? dir))
        (filter (lambda (f)
                  (and (string-prefix? "memo-" f)
                       (string-suffix? ".scm" f)))
                (map (lambda (f) (string-append dir "/" f))
                     (directory-list dir)))
        '()))

  (define (memo-reserved? filepath)
    (call-with-input-file filepath
      (lambda (port)
        (let loop ()
          (let ((line (get-line port)))
            (cond
              ((eof-object? line) #f)
              ((string-contains line "(reserved)") #t)
              (else (loop))))))))

  (define (scrutinize-memo-file filepath)
    (call-with-input-file filepath
      (lambda (port)
        (let loop ((line-num 1)
                   (in-code-block #f))
          (let ((line (get-line port)))
            (unless (eof-object? line)
              (let ((now-in-code (or (and (not in-code-block)
                                          (string-contains line "(code "))
                                     (and in-code-block
                                          (not (string-contains line "\")"))))))
                (when (and (not in-code-block)
                           (string-contains line "(p "))
                  (scrutinize-memo-prose line filepath line-num))
                (loop (+ line-num 1) now-in-code))))))))

  (define (scrutinize-memo-prose line filepath line-num)
    (for-each
      (lambda (rule)
        (let ((banned (car rule))
              (suggest (cdr rule)))
          (when (string-contains-ci line banned)
            (add-finding! 'warning filepath line-num 'vocabulary
                          (format #f "~s -> ~a" banned suggest)))))
      *banned-vocabulary*))

  (define (glob-scheme-files dir)
    (if (and (file-exists? dir) (file-directory? dir))
        (filter (lambda (f)
                  (and (string-suffix? ".scm" f)
                       (not (string-contains f ".import.scm"))))
                (map (lambda (f) (string-append dir "/" f))
                     (directory-list dir)))
        '()))

  (define (report-findings target)
    (let ((count (length *findings*)))
      (if (zero? count)
          (printf "  ~a: clean~%" target)
          (begin
            (printf "  ~a: ~a findings~%~%" target count)
            (for-each
              (lambda (f)
                (let ((severity (car f))
                      (file (cadr f))
                      (line (caddr f))
                      (category (cadddr f))
                      (message (car (cddddr f))))
                  (printf "  ~a:~a [~a] ~a~%"
                          (pathname-strip-directory file)
                          line category message)))
              (reverse *findings*))
            (printf "~%")))))

  ;; ============================================================
  ;; Realmtime Mode
  ;; ============================================================

  (define (scrutinize-realmtime! enable)
    (*scrutinize-realmtime* enable)
    (if enable
        (printf "Realmtime scrutiny enabled. Violations surface on load.~%")
        (printf "Realmtime scrutiny disabled.~%")))

) ; end library
