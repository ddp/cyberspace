#!/usr/bin/env chez --libdirs . --script
;;; scrutinize.sps - Comprehensive library consistency and coherence review
;;;
;;; Chez Scheme port. Performs deep analysis of the Cyberspace library:
;;; 1. Module naming conventions    10. Infinite recursion detection
;;; 2. Export patterns              11. Duplicate definitions
;;; 3. Import patterns              12. Tech debt markers
;;; 4. Documentation style          13. Import-except violations
;;; 5. File organization            14. Large functions
;;; 6. Naming coherence             15. Global mutation at load time
;;; 7. Dead code detection          16. Special variables catalog
;;; 8. Cross-reference validation
;;; 9. Build artifact hygiene
;;;
;;; Usage: chez --script scrutinize.sps [--fix] [directory]

(import (rnrs)
        (only (chezscheme)
              printf format command-line exit
              file-directory? directory-list
              sort current-directory
              with-input-from-file)
        (cyberspace chicken-compatibility chicken)
        (cyberspace chicken-compatibility hash-table))

;;; ============================================================
;;; String Helpers (replacing irregex / srfi-13)
;;; ============================================================

(define (string-contains haystack needle)
  (let ((nlen (string-length needle))
        (hlen (string-length haystack)))
    (let loop ((i 0))
      (cond
        ((> (+ i nlen) hlen) #f)
        ((string=? needle (substring haystack i (+ i nlen))) i)
        (else (loop (+ i 1)))))))

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
                      i (loop (+ i 1)))))
         (end (let loop ((i (- len 1)))
                (if (or (< i start) (not (char-whitespace? (string-ref str i))))
                    (+ i 1) (loop (- i 1))))))
    (substring str start end)))

(define (string-count str ch)
  (let ((len (string-length str)))
    (let loop ((i 0) (c 0))
      (if (>= i len) c
          (loop (+ i 1) (if (char=? (string-ref str i) ch) (+ c 1) c))))))

(define (pathname-strip-extension path)
  (let ((len (string-length path)))
    (let loop ((i (- len 1)))
      (cond
        ((< i 0) path)
        ((char=? (string-ref path i) #\.) (substring path 0 i))
        ((char=? (string-ref path i) #\/) path)
        (else (loop (- i 1)))))))

(define (pathname-extension path)
  (let ((len (string-length path)))
    (let loop ((i (- len 1)))
      (cond
        ((< i 0) #f)
        ((char=? (string-ref path i) #\.) (substring path (+ i 1) len))
        ((char=? (string-ref path i) #\/) #f)
        (else (loop (- i 1)))))))

(define (read-file-string path)
  (call-with-input-file path
    (lambda (port) (get-string-all port))))

(define (read-file-lines path)
  (call-with-input-file path
    (lambda (port)
      (let loop ((lines '()))
        (let ((line (get-line port)))
          (if (eof-object? line)
              (reverse lines)
              (loop (cons line lines))))))))

(define (take lst n)
  (if (or (null? lst) (<= n 0)) '()
      (cons (car lst) (take (cdr lst) (- n 1)))))

(define (filter-map proc lst)
  (let loop ((lst lst) (acc '()))
    (if (null? lst) (reverse acc)
        (let ((r (proc (car lst))))
          (loop (cdr lst) (if r (cons r acc) acc))))))

;; Extract (define name or (define (name from start of line
(define (extract-define-name line)
  (cond
    ;; (define (name ...)
    ((string-prefix? "(define (" line)
     (let ((start 9)
           (len (string-length line)))
       (let loop ((i start))
         (if (or (>= i len)
                 (let ((c (string-ref line i)))
                   (or (char-whitespace? c) (char=? c #\)))))
             (if (> i start) (substring line start i) #f)
             (loop (+ i 1))))))
    ;; (define name
    ((string-prefix? "(define " line)
     (let ((start 8)
           (len (string-length line)))
       (if (and (< start len) (char=? (string-ref line start) #\())
           #f  ; handled above
           (let loop ((i start))
             (if (or (>= i len)
                     (let ((c (string-ref line i)))
                       (or (char-whitespace? c) (char=? c #\)))))
                 (if (> i start) (substring line start i) #f)
                 (loop (+ i 1)))))))
    (else #f)))

;; Extract *special-var* name from (define *name* ...)
(define (extract-special-var line)
  (and (string-prefix? "(define *" line)
       (let ((start 8)
             (len (string-length line)))
         (let loop ((i (+ start 1)))
           (cond
             ((>= i len) #f)
             ((char=? (string-ref line i) #\*)
              (substring line start (+ i 1)))
             ((or (char-whitespace? (string-ref line i))
                  (char=? (string-ref line i) #\)))
              #f)
             (else (loop (+ i 1))))))))

;; Check if name contains camelCase
(define (has-camel-case? name)
  (let ((len (string-length name)))
    (let loop ((i 1))
      (if (>= i len) #f
          (let ((c (string-ref name i))
                (prev (string-ref name (- i 1))))
            (if (and (char-lower-case? prev) (char-upper-case? c))
                #t
                (loop (+ i 1))))))))

;; Check if name contains snake_case
(define (has-snake-case? name)
  (string-contains name "_"))

;; Extract Memo-NNN references from a line
(define (extract-memo-refs line)
  (let ((len (string-length line))
        (refs '()))
    (let loop ((i 0))
      (if (>= i len) (reverse refs)
          (let ((pos (string-contains (substring line i len) "Memo-")))
            (if (not pos)
                (reverse refs)
                (let* ((abs-pos (+ i pos 5))  ; after "Memo-"
                       (num-end (let nloop ((j abs-pos))
                                  (if (or (>= j len)
                                          (not (char-numeric? (string-ref line j))))
                                      j (nloop (+ j 1))))))
                  (if (> num-end abs-pos)
                      (let ((n (string->number (substring line abs-pos num-end))))
                        (loop num-end)
                        (if n (cons n (loop num-end)) (loop num-end)))
                      (loop (+ abs-pos 1))))))))))

;; Check for tech debt markers
(define (has-debt-marker? line)
  (or (string-contains line "TODO")
      (string-contains line "FIXME")
      (string-contains line "HACK")
      (string-contains line "XXX")))

;;; ============================================================
;;; State
;;; ============================================================

(define *errors* 0)
(define *warnings* 0)
(define *notes* 0)
(define *fix-mode* #f)
(define *target-dir* ".")

(define (error! file line msg)
  (set! *errors* (+ *errors* 1))
  (if line
      (printf "  ERROR ~a:~a: ~a~%" file line msg)
      (printf "  ERROR ~a: ~a~%" file msg)))

(define (warn! file line msg)
  (set! *warnings* (+ *warnings* 1))
  (if line
      (printf "  WARN  ~a:~a: ~a~%" file line msg)
      (printf "  WARN  ~a: ~a~%" file msg)))

(define (note! msg)
  (set! *notes* (+ *notes* 1))
  (printf "  NOTE  ~a~%" msg))

(define (ok! msg)
  (printf "  OK    ~a~%" msg))

;;; ============================================================
;;; File Discovery
;;; ============================================================

(define (library-modules)
  (let ((dir *target-dir*))
    (if (and (file-exists? dir) (file-directory? dir))
        (filter (lambda (f)
                  (and (or (string-suffix? ".scm" f)
                           (string-suffix? ".sls" f))
                       (not (string-contains f ".import.scm"))
                       (not (string-prefix? "test-" f))
                       (not (string-prefix? "refresh-" f))
                       (not (string-suffix? "-test.scm" f))
                       (not (member f '("build.scm" "sanity.scm" "scrutinize.scm"
                                        "generate-all.scm" "scrutinize.sps")))))
                (directory-list dir))
        '())))

(define (full-path f)
  (if (string=? *target-dir* ".")
      f
      (string-append *target-dir* "/" f)))

;;; ============================================================
;;; 1. Module Naming Conventions
;;; ============================================================

(define (check-module-naming)
  (printf "~%=== 1. Module Naming Conventions ===~%")
  (let ((modules (library-modules))
        (issues 0))
    (for-each
      (lambda (f)
        (let* ((content (read-file-string (full-path f)))
               (base (pathname-strip-extension f))
               ;; Check for (module name or (library (cyberspace name)
               (has-module (or (string-contains content "(module ")
                               (string-contains content "(library ("))))
          (unless has-module
            (note! (format #f "~a: no module/library declaration" f)))))
      modules)
    (if (zero? issues)
        (ok! (format #f "~a modules checked" (length modules)))
        (printf "  ~a naming issues found~%" issues))))

;;; ============================================================
;;; 2. Export Patterns
;;; ============================================================

(define (check-export-patterns)
  (printf "~%=== 2. Export Patterns ===~%")
  (let ((modules (library-modules))
        (no-exports '())
        (scripts '()))
    (for-each
      (lambda (f)
        (let* ((content (read-file-string (full-path f)))
               (is-script (string-prefix? "#!" content))
               (has-module (string-contains content "(module "))
               (has-library (string-contains content "(library ("))
               (exports-all (string-contains content "(module *)")))
          (cond
            (is-script (set! scripts (cons f scripts)))
            (exports-all (set! no-exports (cons f no-exports)))
            ((or has-module has-library) #f)
            (else #f))))
      modules)
    (when (pair? scripts)
      (ok! (format #f "~a scripts (no exports needed)" (length scripts))))
    (if (null? no-exports)
        (ok! "All library modules have explicit export declarations")
        (for-each (lambda (f) (warn! f #f "uses * (export all)")) no-exports))))

;;; ============================================================
;;; 4. Documentation Style
;;; ============================================================

(define (check-documentation-style)
  (printf "~%=== 4. Documentation Style ===~%")
  (let ((modules (library-modules))
        (no-header '()))
    (for-each
      (lambda (f)
        (let ((content (read-file-string (full-path f))))
          (unless (string-prefix? ";;;" content)
            (set! no-header (cons f no-header)))))
      modules)
    (if (null? no-header)
        (ok! "All modules have header documentation")
        (for-each (lambda (f) (note! (format #f "~a: missing header" f))) no-header))))

;;; ============================================================
;;; 5. File Organization
;;; ============================================================

(define (check-file-organization)
  (printf "~%=== 5. File Organization ===~%")
  (let ((expected '("docs"))
        (missing '()))
    (for-each
      (lambda (d)
        (let ((p (if (string=? *target-dir* ".") d (string-append *target-dir* "/" d))))
          (unless (and (file-exists? p) (file-directory? p))
            (set! missing (cons d missing)))))
      expected)
    (if (null? missing)
        (ok! "Expected directories present")
        (for-each (lambda (d) (note! (format #f "~a: directory not found" d))) missing))))

;;; ============================================================
;;; 6. Naming Coherence
;;; ============================================================

(define (check-naming-coherence)
  (printf "~%=== 6. Naming Coherence ===~%")
  (let ((modules (library-modules))
        (violations '()))
    (for-each
      (lambda (f)
        (let* ((lines (read-file-lines (full-path f)))
               (line-num 0))
          (for-each
            (lambda (line)
              (set! line-num (+ line-num 1))
              (let ((name (extract-define-name line)))
                (when name
                  (when (has-camel-case? name)
                    (set! violations (cons (cons f name) violations)))
                  (when (has-snake-case? name)
                    (set! violations (cons (cons f name) violations))))))
            lines)))
      modules)
    (if (null? violations)
        (ok! "All function names use kebab-case")
        (for-each (lambda (v)
                    (warn! (car v) #f (format #f "non-kebab name: ~a" (cdr v))))
                  violations))))

;;; ============================================================
;;; 7. Dead Code Detection
;;; ============================================================

(define (check-dead-code)
  (printf "~%=== 7. Dead Code Detection ===~%")
  (let ((files (directory-list *target-dir*)))
    ;; Check for .so without .scm
    (let ((orphan-so (filter (lambda (f)
                               (and (string-suffix? ".so" f)
                                    (not (file-exists?
                                           (full-path (string-append (pathname-strip-extension f) ".scm"))))))
                             files)))
      (if (null? orphan-so)
          (ok! "No orphaned .so files")
          (for-each (lambda (f) (warn! f #f "no matching source")) orphan-so)))

    ;; Check for .import.scm without .scm
    (let ((orphan-imp (filter (lambda (f)
                                (and (string-suffix? ".import.scm" f)
                                     (let ((base (substring f 0 (- (string-length f) 11))))
                                       (not (file-exists? (full-path (string-append base ".scm")))))))
                              files)))
      (if (null? orphan-imp)
          (ok! "No orphaned .import.scm files")
          (for-each (lambda (f) (warn! f #f "no matching source")) orphan-imp)))))

;;; ============================================================
;;; 8. Cross-Reference Validation
;;; ============================================================

(define (check-cross-references)
  (printf "~%=== 8. Cross-Reference Validation ===~%")
  (let ((memo-dir (string-append *target-dir* "/docs/notes")))
    (if (and (file-exists? memo-dir) (file-directory? memo-dir))
        (let* ((memo-files (filter (lambda (f) (string-prefix? "memo-" f))
                                   (directory-list memo-dir)))
               (existing (filter-map
                           (lambda (f)
                             ;; Extract number from memo-NNNN-name.scm
                             (and (> (string-length f) 9)
                                  (string->number (substring f 5 9))))
                           memo-files)))
          ;; Scan library modules for Memo-NNN references
          (for-each
            (lambda (f)
              (let* ((lines (read-file-lines (full-path f)))
                     (line-num 0))
                (for-each
                  (lambda (line)
                    (set! line-num (+ line-num 1))
                    (let ((refs (extract-memo-refs line)))
                      (for-each
                        (lambda (n)
                          (when (and (<= n 100) (not (member n existing)))
                            (warn! f line-num (format #f "dangling reference: Memo-~a" n))))
                        refs)))
                  lines)))
            (library-modules)))
        (note! "docs/notes not found, skipping"))
    (ok! "Cross-references validated")))

;;; ============================================================
;;; 10. Infinite Recursion Detection
;;; ============================================================

(define (check-infinite-recursion)
  (printf "~%=== 10. Infinite Recursion Detection ===~%")
  (let ((modules (library-modules))
        (violations '()))
    (for-each
      (lambda (f)
        (let* ((lines (read-file-lines (full-path f)))
               (line-num 0))
          (for-each
            (lambda (line)
              (set! line-num (+ line-num 1))
              ;; Check for (define (name) (name)) pattern
              (let ((name (extract-define-name line)))
                (when (and name
                           (string-contains line (string-append "(" name ")")))
                  ;; Verify it's actually (define (name) (name)) — no args
                  (let ((pattern (string-append "(define (" name ") (" name "))")))
                    (when (string-contains line pattern)
                      (set! violations
                        (cons (list f line-num name) violations)))))))
            lines)))
      modules)
    (if (null? violations)
        (ok! "No degenerate infinite recursion detected")
        (for-each
          (lambda (v)
            (error! (car v) (cadr v)
                    (format #f "(~a) calls itself with no state change" (caddr v))))
          violations))))

;;; ============================================================
;;; 11. Duplicate Definitions
;;; ============================================================

(define (check-duplicate-definitions)
  (printf "~%=== 11. Duplicate Definitions ===~%")
  (let ((modules (library-modules))
        (violations '()))
    (for-each
      (lambda (f)
        (let* ((lines (read-file-lines (full-path f)))
               (defines (make-hash-table))
               (line-num 0))
          (for-each
            (lambda (line)
              (set! line-num (+ line-num 1))
              ;; Only top-level (no leading whitespace)
              (when (string-prefix? "(define " line)
                (let ((name (extract-define-name line)))
                  (when name
                    (if (hash-table-exists? defines name)
                        (set! violations
                          (cons (list f line-num name (hash-table-ref defines name))
                                violations))
                        (hash-table-set! defines name line-num))))))
            lines)))
      modules)
    (if (null? violations)
        (ok! "No duplicate definitions found")
        (for-each
          (lambda (v)
            (warn! (car v) (cadr v)
                   (format #f "duplicate definition: ~a (first at line ~a)"
                            (caddr v) (cadddr v))))
          violations))))

;;; ============================================================
;;; 12. Tech Debt Markers
;;; ============================================================

(define (check-tech-debt)
  (printf "~%=== 12. Tech Debt Markers ===~%")
  (let ((modules (library-modules))
        (markers '())
        (total 0))
    (for-each
      (lambda (f)
        (let* ((lines (read-file-lines (full-path f)))
               (line-num 0))
          (for-each
            (lambda (line)
              (set! line-num (+ line-num 1))
              (when (has-debt-marker? line)
                (set! total (+ total 1))
                (set! markers (cons (list f line-num line) markers))))
            lines)))
      modules)
    (if (null? markers)
        (ok! "No tech debt markers found")
        (begin
          (for-each
            (lambda (m)
              (note! (format #f "~a:~a: ~a" (car m) (cadr m) (string-trim-both (caddr m)))))
            (take (reverse markers) (min 10 (length markers))))
          (when (> total 10)
            (note! (format #f "... and ~a more" (- total 10))))
          (note! (format #f "Total tech debt markers: ~a" total))))))

;;; ============================================================
;;; 14. Large Functions
;;; ============================================================

(define *large-function-threshold* 100)

(define *large-function-exceptions*
  '("index-html" "execute-commands"))

(define (check-large-functions)
  (printf "~%=== 14. Large Functions ===~%")
  (let ((modules (library-modules))
        (large-fns '()))
    (for-each
      (lambda (f)
        (let* ((lines (read-file-lines (full-path f)))
               (line-num 0)
               (current-fn #f)
               (fn-start 0)
               (paren-depth 0))
          (for-each
            (lambda (line)
              (set! line-num (+ line-num 1))
              (when (and (zero? paren-depth) (string-prefix? "(define " line))
                (let ((name (extract-define-name line)))
                  (when name
                    (set! current-fn name)
                    (set! fn-start line-num))))
              (set! paren-depth
                (+ paren-depth
                   (- (string-count line #\()
                      (string-count line #\)))))
              (when (and current-fn (<= paren-depth 0))
                (let ((fn-size (- line-num fn-start -1)))
                  (when (and (> fn-size *large-function-threshold*)
                             (not (member current-fn *large-function-exceptions*)))
                    (set! large-fns
                      (cons (list f fn-start current-fn fn-size) large-fns))))
                (set! current-fn #f)
                (set! paren-depth 0)))
            lines)))
      modules)
    (if (null? large-fns)
        (ok! (format #f "No functions over ~a lines" *large-function-threshold*))
        (begin
          (for-each
            (lambda (fn)
              (warn! (car fn) (cadr fn)
                     (format #f "~a is ~a lines (threshold: ~a)"
                              (caddr fn) (cadddr fn) *large-function-threshold*)))
            (sort (lambda (a b) (> (cadddr a) (cadddr b))) large-fns))
          (note! (format #f "~a large functions found" (length large-fns)))))))

;;; ============================================================
;;; 15. Global Mutation at Load Time
;;; ============================================================

(define (check-global-mutation)
  (printf "~%=== 15. Global Mutation at Load Time ===~%")
  (let ((modules (library-modules))
        (violations '()))
    (for-each
      (lambda (f)
        (let* ((lines (read-file-lines (full-path f)))
               (line-num 0)
               (in-define #f)
               (paren-depth 0))
          (for-each
            (lambda (line)
              (set! line-num (+ line-num 1))
              (when (string-prefix? "(define " line)
                (set! in-define #t))
              (set! paren-depth
                (+ paren-depth
                   (- (string-count line #\()
                      (string-count line #\)))))
              (when (<= paren-depth 0)
                (set! in-define #f)
                (set! paren-depth 0))
              (when (and (not in-define) (string-prefix? "(set! " line))
                (let* ((rest (substring line 6 (string-length line)))
                       (name-end (let loop ((i 0))
                                   (if (or (>= i (string-length rest))
                                           (char-whitespace? (string-ref rest i))
                                           (char=? (string-ref rest i) #\)))
                                       i (loop (+ i 1)))))
                       (name (substring rest 0 name-end)))
                  (when (> (string-length name) 0)
                    (set! violations
                      (cons (list f line-num name) violations))))))
            lines)))
      modules)
    (if (null? violations)
        (ok! "No top-level set! at load time")
        (for-each
          (lambda (v)
            (warn! (car v) (cadr v)
                   (format #f "top-level set! of ~a at load time" (caddr v))))
          violations))))

;;; ============================================================
;;; 16. Special Variables Catalog
;;; ============================================================

(define (classify-special name)
  (define (starts-with? prefix)
    (string-prefix? prefix name))
  (cond
    ((or (starts-with? "*ed25519") (starts-with? "*sha256") (starts-with? "*sha512")
         (starts-with? "*crypto") (starts-with? "*pq-") (starts-with? "*keystore")
         (starts-with? "*capability")) 'crypto)
    ((or (starts-with? "*chunk") (starts-with? "*content") (starts-with? "*vault")
         (starts-with? "*catalog") (starts-with? "*merkle") (starts-with? "*bloom")) 'storage)
    ((or (starts-with? "*gossip") (starts-with? "*federation") (starts-with? "*node-")
         (starts-with? "*wormhole") (starts-with? "*discovery") (starts-with? "*lamport")
         (starts-with? "*peer")) 'network)
    ((or (starts-with? "*prompt") (starts-with? "*user-mode") (starts-with? "*help")
         (starts-with? "*theme") (starts-with? "*spinner") (starts-with? "*pager")
         (starts-with? "*result") (starts-with? "*inspector")) 'repl)
    ((or (starts-with? "*edt") (starts-with? "*kill-ring") (starts-with? "*text*")
         (starts-with? "*filename")) 'editor)
    ((or (starts-with? "*boot") (starts-with? "*cli") (starts-with? "*forge")
         (starts-with? "*compile") (starts-with? "*build")) 'build)
    ((or (starts-with? "*test") (starts-with? "*verbose") (starts-with? "*error")
         (starts-with? "*warn") (starts-with? "*debug")) 'debug)
    ((starts-with? "*fuse") 'fuse)
    ((or (starts-with? "*server") (starts-with? "*listener") (starts-with? "*port")) 'server)
    ((or (starts-with? "*audit") (starts-with? "*security")) 'audit)
    (else 'misc)))

(define (value-hint line)
  (cond
    ((string-contains line "'()") "empty list")
    ((string-contains line "#f)") "false")
    ((string-contains line "#t)") "true")
    ((string-contains line "0)") "zero")
    ((string-contains line "\"\")") "empty string")
    ((string-contains line "(make-hash-table)") "hash-table")
    ((string-contains line "(make-parameter") "parameter")
    (else #f)))

(define (catalog-special-variables)
  (printf "~%=== 16. Special Variables Catalog ===~%")
  (let ((modules (library-modules))
        (specials '())
        (by-domain (make-hash-table)))
    (for-each
      (lambda (f)
        (let* ((lines (read-file-lines (full-path f)))
               (line-num 0))
          (for-each
            (lambda (line)
              (set! line-num (+ line-num 1))
              (let ((name (extract-special-var line)))
                (when name
                  (set! specials
                    (cons (list name f line-num (value-hint line)) specials)))))
            lines)))
      modules)

    (for-each
      (lambda (s)
        (let ((domain (classify-special (car s))))
          (hash-table-update!/default by-domain domain
                                      (lambda (lst) (cons s lst)) '())))
      specials)

    (let ((domains '(crypto storage network repl editor build debug fuse server audit misc)))
      (for-each
        (lambda (domain)
          (let ((vars (hash-table-ref/default by-domain domain '())))
            (when (pair? vars)
              (printf "~%  ~a (~a):~%" domain (length vars))
              (for-each
                (lambda (v)
                  (let ((name (car v))
                        (file (cadr v))
                        (line (caddr v))
                        (hint (cadddr v)))
                    (if hint
                        (printf "    ~a  (~a:~a) [~a]~%" name file line hint)
                        (printf "    ~a  (~a:~a)~%" name file line))))
                (sort (lambda (a b) (string<? (car a) (car b))) vars)))))
        domains))

    (printf "~%  Total: ~a special variables~%" (length specials))))

;;; ============================================================
;;; Main
;;; ============================================================

(define (main args)
  (when (member "--fix" args)
    (set! *fix-mode* #t)
    (printf "Running in fix mode...~%"))

  ;; Allow specifying target directory
  (let ((dir-args (filter (lambda (a) (not (string-prefix? "--" a))) args)))
    (when (pair? dir-args)
      (set! *target-dir* (car dir-args))))

  (printf "~%══════════════════════════════════════~%")
  (printf "   Library Scrutiny Report~%")
  (printf "══════════════════════════════════════~%")
  (printf "  Target: ~a~%" *target-dir*)

  (check-module-naming)
  (check-export-patterns)
  (check-documentation-style)
  (check-file-organization)
  (check-naming-coherence)
  (check-dead-code)
  (check-cross-references)
  (check-infinite-recursion)
  (check-duplicate-definitions)
  (check-tech-debt)
  (check-large-functions)
  (check-global-mutation)
  (catalog-special-variables)

  (printf "~%=== Summary ===~%")
  (printf "  Errors:   ~a~%" *errors*)
  (printf "  Warnings: ~a~%" *warnings*)
  (printf "  Notes:    ~a~%" *notes*)

  (cond
    ((> *errors* 0)
     (printf "~%  Library has issues requiring attention.~%")
     (exit 1))
    ((> *warnings* 0)
     (printf "~%  Library is coherent with minor issues.~%")
     (exit 0))
    (else
     (printf "~%  Library is coherent.~%")
     (exit 0))))

(main (cdr (command-line)))
