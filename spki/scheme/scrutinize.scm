#!/usr/bin/env csi -s
;;; scrutinize.scm - Comprehensive library consistency and coherence review
;;;
;;; Performs deep analysis of the Cyberspace library:
;;; 1. Module naming conventions
;;; 2. Export patterns
;;; 3. Import patterns
;;; 4. Documentation style
;;; 5. File organization
;;; 6. Naming coherence (kebab-case, *globals*, predicates?)
;;; 7. Dead code detection
;;; 8. Cross-reference validation
;;; 9. Build artifact hygiene
;;;
;;; Usage: ./scrutinize.scm [--fix]

(import scheme
        (chicken base)
        (chicken io)
        (chicken file)
        (chicken file posix)
        (chicken pathname)
        (chicken string)
        (chicken format)
        (chicken sort)
        (chicken process)
        (chicken process-context)
        (chicken irregex)
        srfi-1
        srfi-13
        srfi-69)

(define *errors* 0)
(define *warnings* 0)
(define *notes* 0)
(define *fix-mode* #f)

(define (error! file line msg)
  (set! *errors* (+ *errors* 1))
  (if line
      (printf "  ERROR ~a:~a: ~a~n" file line msg)
      (printf "  ERROR ~a: ~a~n" file msg)))

(define (warn! file line msg)
  (set! *warnings* (+ *warnings* 1))
  (if line
      (printf "  WARN  ~a:~a: ~a~n" file line msg)
      (printf "  WARN  ~a: ~a~n" file msg)))

(define (note! msg)
  (set! *notes* (+ *notes* 1))
  (printf "  NOTE  ~a~n" msg))

(define (ok! msg)
  (printf "  OK    ~a~n" msg))

;;; ============================================================
;;; 1. Module Naming Conventions
;;; ============================================================

(define (library-modules)
  "List all .scm library modules (excludes test/script/import files)"
  (filter (lambda (f)
            (and (string-suffix? ".scm" f)
                 (not (string-suffix? ".import.scm" f))
                 (not (string-prefix? "test-" f))
                 (not (string-prefix? "refresh-" f))
                 (not (string-suffix? "-test.scm" f))
                 (not (member f '("build.scm" "sanity.scm" "scrutinize.scm"
                                  "generate-all.scm")))))
          (directory ".")))

(define (check-module-naming)
  (print "\n=== 1. Module Naming Conventions ===")
  (let ((modules (library-modules))
        (issues 0))
    (for-each
      (lambda (f)
        (let* ((content (with-input-from-file f read-string))
               (base (pathname-strip-extension f))
               ;; Check for (module name ...) declaration
               (mod-match (irregex-search "\\(module ([a-z0-9-]+)" content)))
          (cond
            ((not mod-match)
             (note! (sprintf "~a: no module declaration" f)))
            ((not (string=? base (irregex-match-substring mod-match 1)))
             (set! issues (+ issues 1))
             (warn! f #f (sprintf "module name '~a' != filename '~a'"
                                 (irregex-match-substring mod-match 1) base))))))
      modules)
    (if (zero? issues)
        (ok! (sprintf "~a modules follow naming conventions" (length modules)))
        (printf "  ~a naming issues found~n" issues))))

;;; ============================================================
;;; 2. Export Patterns
;;; ============================================================

(define (check-export-patterns)
  (print "\n=== 2. Export Patterns ===")
  (let ((modules (library-modules))
        (no-exports '())
        (scripts '()))
    (for-each
      (lambda (f)
        (let* ((content (with-input-from-file f read-string))
               (is-script (irregex-search "^#!" content))
               (has-module (irregex-search "\\(module [a-z0-9-]+" content))
               (has-exports (irregex-search "\\(module [a-z0-9-]+ \\(" content)))
          (cond
            ;; Scripts don't need exports
            (is-script
             (set! scripts (cons f scripts)))
            ;; Has module but no export list
            ((and has-module (not has-exports))
             (set! no-exports (cons f no-exports)))
            ;; No module declaration - already flagged in check 1
            ((not has-module) #f)
            ;; Has exports - good
            (else #f))))
      modules)
    (when (pair? scripts)
      (ok! (sprintf "~a scripts (no exports needed)" (length scripts))))
    (if (null? no-exports)
        (ok! "All library modules have export declarations")
        (for-each (lambda (f) (warn! f #f "module without explicit exports")) no-exports))))

;;; ============================================================
;;; 3. Import Patterns
;;; ============================================================

(define (check-import-patterns)
  (print "\n=== 3. Import Patterns ===")
  (let ((modules (library-modules))
        (missing-imports '()))
    (for-each
      (lambda (f)
        (let* ((content (with-input-from-file f read-string))
               ;; Find all (import ...) blocks and extract module names
               (imports (irregex-fold
                          "\\(import ([^)]+)\\)"
                          (lambda (i m acc)
                            (cons (irregex-match-substring m 1) acc))
                          '() content)))
          ;; Check for custom module imports that don't exist
          (for-each
            (lambda (imp-block)
              (irregex-fold
                "\\b([a-z]+-[a-z0-9-]+)\\b"
                (lambda (i m acc)
                  (let ((mod (irregex-match-substring m 1)))
                    (when (and (not (string-prefix? "chicken" mod))
                               (not (string-prefix? "srfi-" mod))
                               (not (file-exists? (string-append mod ".scm")))
                               (not (member mod '("scheme"))))
                      (set! missing-imports (cons (cons f mod) missing-imports)))))
                #f imp-block))
            imports)))
      modules)
    (if (null? missing-imports)
        (ok! "All imports resolve to existing modules")
        (for-each (lambda (pair)
                    (warn! (car pair) #f (sprintf "imports non-existent module: ~a" (cdr pair))))
                  missing-imports))))

;;; ============================================================
;;; 4. Documentation Style
;;; ============================================================

(define (check-documentation-style)
  (print "\n=== 4. Documentation Style ===")
  (let ((modules (library-modules))
        (no-header '())
        (no-docstrings '()))
    (for-each
      (lambda (f)
        (let* ((content (with-input-from-file f read-string))
               ;; Check for ;;; header comment
               (has-header (irregex-search "^;;;" content))
               ;; Count functions with docstrings
               (define-count (length (irregex-extract "\\(define \\(" content)))
               (docstring-count (length (irregex-extract "\\(define \\([^)]+\\)\\s+\"[^\"]+\"" content))))
          (unless has-header
            (set! no-header (cons f no-header)))
          (when (and (> define-count 5) (< docstring-count (/ define-count 2)))
            (set! no-docstrings (cons f no-docstrings)))))
      modules)
    (when (pair? no-header)
      (for-each (lambda (f) (note! (sprintf "~a: missing header documentation" f))) no-header))
    (when (pair? no-docstrings)
      (for-each (lambda (f) (note! (sprintf "~a: few docstrings" f))) no-docstrings))
    (when (and (null? no-header) (null? no-docstrings))
      (ok! "Documentation style consistent"))))

;;; ============================================================
;;; 5. File Organization
;;; ============================================================

(define (check-file-organization)
  (print "\n=== 5. File Organization ===")
  ;; Check expected directories exist
  (let ((expected '("docs" "darwin" "linux" "eggs"))
        (missing '()))
    (for-each
      (lambda (d)
        (unless (directory-exists? d)
          (set! missing (cons d missing))))
      expected)
    (if (null? missing)
        (ok! "Expected directories present")
        (for-each (lambda (d) (warn! d #f "directory missing")) missing)))

  ;; Check for orphaned files
  (let ((orphans (filter (lambda (f)
                           (and (string-suffix? ".c" f)
                                (not (file-exists?
                                       (string-append (pathname-strip-extension f) ".scm")))))
                         (directory "."))))
    (if (null? orphans)
        (ok! "No orphaned generated files")
        (for-each (lambda (f) (note! (sprintf "orphaned: ~a" f))) orphans))))

;;; ============================================================
;;; 6. Naming Coherence
;;; ============================================================

(define (check-naming-coherence)
  (print "\n=== 6. Naming Coherence ===")
  (let ((modules (library-modules))
        (violations '()))
    (for-each
      (lambda (f)
        (let ((content (with-input-from-file f read-string)))
          ;; Check for camelCase (should be kebab-case)
          (irregex-fold
            "\\(define \\(([a-z]+[A-Z][a-zA-Z]*)"
            (lambda (i m acc)
              (set! violations (cons (cons f (irregex-match-substring m 1)) violations)))
            #f content)
          ;; Check for snake_case (should be kebab-case)
          (irregex-fold
            "\\(define \\(([a-z]+_[a-z_]+)"
            (lambda (i m acc)
              (set! violations (cons (cons f (irregex-match-substring m 1)) violations)))
            #f content)))
      modules)
    (if (null? violations)
        (ok! "All function names use kebab-case")
        (for-each (lambda (v)
                    (warn! (car v) #f (sprintf "non-kebab name: ~a" (cdr v))))
                  violations))))

;;; ============================================================
;;; 7. Dead Code Detection
;;; ============================================================

(define (check-dead-code)
  (print "\n=== 7. Dead Code Detection ===")
  ;; Check for .so files without .scm
  (let* ((so-files (filter (lambda (f) (string-suffix? ".so" f)) (directory ".")))
         (orphan-so (filter (lambda (f)
                              (not (file-exists?
                                     (string-append (pathname-strip-extension f) ".scm"))))
                            so-files)))
    (if (null? orphan-so)
        (ok! "No orphaned .so files")
        (for-each (lambda (f) (warn! f #f "no matching .scm source")) orphan-so)))

  ;; Check for .import.scm without .scm
  (let* ((import-files (filter (lambda (f) (string-suffix? ".import.scm" f)) (directory ".")))
         (orphan-import (filter (lambda (f)
                                  (let ((base (string-drop-right f 11))) ; remove .import.scm
                                    (not (file-exists? (string-append base ".scm")))))
                                import-files)))
    (if (null? orphan-import)
        (ok! "No orphaned .import.scm files")
        (for-each (lambda (f) (warn! f #f "no matching .scm source")) orphan-import))))

;;; ============================================================
;;; 8. Cross-Reference Validation
;;; ============================================================

(define (check-cross-references)
  (print "\n=== 8. Cross-Reference Validation ===")
  (let ((memo-dir "docs/memo")
        (refs '())
        (existing '()))

    (when (directory-exists? memo-dir)
      ;; Get existing memo numbers
      (set! existing
        (filter-map
          (lambda (f)
            (let ((m (irregex-search "memo-([0-9]+)-" f)))
              (and m (string->number (irregex-match-substring m 1)))))
          (directory memo-dir)))

      ;; Scan for Memo-NNN references with line numbers
      (for-each
        (lambda (f)
          (let* ((path f)
                 (lines (with-input-from-file path read-lines))
                 (line-num 0))
            (for-each
              (lambda (line)
                (set! line-num (+ line-num 1))
                (irregex-fold
                  "Memo-([0-9]+)"
                  (lambda (i m acc)
                    (let ((n (string->number (irregex-match-substring m 1))))
                      (when (and n (<= n 100) (not (member n existing)))
                        (warn! f line-num (sprintf "dangling reference: Memo-~a" n)))))
                  #f line))
              lines)))
        (library-modules)))

    (ok! "Cross-references validated")))

;;; ============================================================
;;; 9. Build Artifact Hygiene
;;; ============================================================

(define (check-build-artifacts)
  (print "\n=== 9. Build Artifact Hygiene ===")
  (let ((scm-files (filter (lambda (f)
                             (and (string-suffix? ".scm" f)
                                  (not (string-suffix? ".import.scm" f))))
                           (directory ".")))
        (so-files (filter (lambda (f) (string-suffix? ".so" f)) (directory "."))))

    ;; Check .so age vs .scm
    (for-each
      (lambda (so)
        (let* ((base (pathname-strip-extension so))
               (scm (string-append base ".scm")))
          (when (and (file-exists? scm)
                     (> (file-modification-time scm)
                        (file-modification-time so)))
            (warn! so #f "stale: .scm is newer"))))
      so-files)

    (ok! (sprintf "~a .so files checked" (length so-files)))))

;;; ============================================================
;;; 10. Infinite Recursion Detection
;;; ============================================================

(define (check-infinite-recursion)
  (print "\n=== 10. Infinite Recursion Detection ===")
  (let ((modules (library-modules))
        (violations '()))
    (for-each
      (lambda (f)
        (let* ((lines (with-input-from-file f read-lines))
               (line-num 0))
          ;; Pattern: (define (name) (name)) - no args, calls itself
          (for-each
            (lambda (line)
              (set! line-num (+ line-num 1))
              ;; Simple pattern: (define (name) (name)) with no body
              (let ((m (irregex-search
                         "\\(define\\s+\\(([a-zA-Z][a-zA-Z0-9*+/<=>!?-]*)\\)\\s*\\(\\1\\)\\)"
                         line)))
                (when m
                  (set! violations
                    (cons (list f line-num (irregex-match-substring m 1))
                          violations)))))
            lines)))
      modules)
    (if (null? violations)
        (ok! "No degenerate infinite recursion detected")
        (for-each
          (lambda (v)
            (error! (car v) (cadr v)
                    (sprintf "infinite recursion: (~a) calls itself with no state change"
                             (caddr v))))
          violations))))

;;; ============================================================
;;; 11. Duplicate Definitions
;;; ============================================================

(define (check-duplicate-definitions)
  (print "\n=== 11. Duplicate Definitions ===")
  (let ((modules (library-modules))
        (violations '()))
    (for-each
      (lambda (f)
        (let* ((lines (with-input-from-file f read-lines))
               (defines (make-hash-table))
               (line-num 0))
          (for-each
            (lambda (line)
              (set! line-num (+ line-num 1))
              ;; Match (define (name ...) or (define name
              (let ((m (irregex-search "^\\s*\\(define\\s+\\(?([a-zA-Z][a-zA-Z0-9*+/<=>!?-]*)" line)))
                (when m
                  (let ((name (irregex-match-substring m 1)))
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
                   (sprintf "duplicate definition: ~a (first at line ~a)"
                            (caddr v) (cadddr v))))
          violations))))

;;; ============================================================
;;; 12. Tech Debt Markers (TODO/FIXME/HACK/XXX)
;;; ============================================================

(define (check-tech-debt)
  (print "\n=== 12. Tech Debt Markers ===")
  (let ((modules (library-modules))
        (markers '())
        (total 0))
    (for-each
      (lambda (f)
        (let* ((lines (with-input-from-file f read-lines))
               (line-num 0))
          (for-each
            (lambda (line)
              (set! line-num (+ line-num 1))
              (when (irregex-search "\\b(TODO|FIXME|HACK|XXX)\\b" line)
                (set! total (+ total 1))
                (set! markers (cons (list f line-num line) markers))))
            lines)))
      modules)
    (if (null? markers)
        (ok! "No tech debt markers found")
        (begin
          (for-each
            (lambda (m)
              (note! (sprintf "~a:~a: ~a"
                             (car m) (cadr m)
                             (string-trim-both (caddr m)))))
            (take (reverse markers) (min 10 (length markers))))
          (when (> total 10)
            (note! (sprintf "... and ~a more" (- total 10))))
          (note! (sprintf "Total tech debt markers: ~a" total))))))

;;; ============================================================
;;; 13. Import-Except Then Use
;;; ============================================================

(define (check-import-except-violations)
  (print "\n=== 13. Import-Except Violations ===")
  (let ((modules (library-modules))
        (violations '()))
    (for-each
      (lambda (f)
        (let ((content (with-input-from-file f read-string)))
          ;; Find all (import (except module name1 name2 ...)) patterns
          ;; Must follow (import to avoid matching "except" in comments/strings
          (irregex-fold
            "\\(import\\s+\\(except\\s+([a-zA-Z0-9-]+)\\s+([^)]+)\\)"
            (lambda (i m acc)
              (let* ((module-name (irregex-match-substring m 1))
                     (excluded-str (irregex-match-substring m 2))
                     (excluded (map string->symbol (string-split excluded-str))))
                ;; Check if any excluded name is used BUT NOT defined locally
                (for-each
                  (lambda (name)
                    (let* ((name-str (symbol->string name))
                           (rest-of-file (substring content (irregex-match-end-index m 0)))
                           ;; Check for local definition: (define name or (define (name
                           (has-local-def (irregex-search
                                            (sprintf "\\(define\\s+\\(?~a[\\s)]"
                                                     (irregex-quote name-str))
                                            rest-of-file))
                           ;; Check for usage
                           (has-usage (irregex-search
                                        (sprintf "\\b~a\\b" (irregex-quote name-str))
                                        rest-of-file)))
                      ;; Only flag if used but NOT defined locally
                      (when (and has-usage (not has-local-def))
                        (set! violations (cons (list f name module-name) violations)))))
                  excluded)))
            #f content)))
      modules)
    (if (null? violations)
        (ok! "No import-except violations found")
        (for-each
          (lambda (v)
            (warn! (car v) #f
                   (sprintf "excluded '~a' from ~a but uses it without local definition"
                            (cadr v) (caddr v))))
          violations))))

;;; ============================================================
;;; 14. Large Functions
;;; ============================================================

(define *large-function-threshold* 100)  ; lines

;; Known large functions that are intentional:
;; - index-html: heredoc HTML template, not procedural code
;; - execute-commands: TECO command interpreter, inherently a big case dispatch
(define *large-function-exceptions*
  '("index-html" "execute-commands"))

(define (check-large-functions)
  (print "\n=== 14. Large Functions ===")
  (let ((modules (library-modules))
        (large-fns '()))
    (for-each
      (lambda (f)
        (let* ((lines (with-input-from-file f read-lines))
               (line-num 0)
               (current-fn #f)
               (fn-start 0)
               (paren-depth 0))
          (for-each
            (lambda (line)
              (set! line-num (+ line-num 1))
              ;; Track start of top-level define
              (when (and (zero? paren-depth)
                         (irregex-search "^\\(define\\s+\\(?([a-zA-Z][a-zA-Z0-9*+/<=>!?-]*)" line))
                (let ((m (irregex-search "^\\(define\\s+\\(?([a-zA-Z][a-zA-Z0-9*+/<=>!?-]*)" line)))
                  (set! current-fn (irregex-match-substring m 1))
                  (set! fn-start line-num)))
              ;; Count parens (rough depth tracking)
              (set! paren-depth
                (+ paren-depth
                   (- (string-count line #\()
                      (string-count line #\)))))
              ;; When we return to depth 0, function ended
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
        (ok! (sprintf "No functions over ~a lines" *large-function-threshold*))
        (begin
          (for-each
            (lambda (fn)
              (warn! (car fn) (cadr fn)
                     (sprintf "~a is ~a lines (threshold: ~a)"
                              (caddr fn) (cadddr fn) *large-function-threshold*)))
            (sort large-fns (lambda (a b) (> (cadddr a) (cadddr b)))))
          (note! (sprintf "~a large functions found" (length large-fns)))))))

;;; ============================================================
;;; 15. Global Mutation at Load Time
;;; ============================================================

(define (check-global-mutation)
  (print "\n=== 15. Global Mutation at Load Time ===")
  (let ((modules (library-modules))
        (violations '()))
    (for-each
      (lambda (f)
        (let* ((lines (with-input-from-file f read-lines))
               (line-num 0)
               (in-define #f)
               (paren-depth 0))
          (for-each
            (lambda (line)
              (set! line-num (+ line-num 1))
              ;; Track if we're inside a define
              (when (irregex-search "^\\(define\\s" line)
                (set! in-define #t))
              ;; Update paren depth
              (set! paren-depth
                (+ paren-depth
                   (- (string-count line #\()
                      (string-count line #\)))))
              (when (<= paren-depth 0)
                (set! in-define #f)
                (set! paren-depth 0))
              ;; Check for top-level set! (not inside define)
              (when (and (not in-define)
                         (irregex-search "^\\(set!\\s" line))
                (let ((m (irregex-search "^\\(set!\\s+([a-zA-Z*][a-zA-Z0-9*+/<=>!?-]*)" line)))
                  (when m
                    (set! violations
                      (cons (list f line-num (irregex-match-substring m 1))
                            violations))))))
            lines)))
      modules)
    (if (null? violations)
        (ok! "No top-level set! at load time")
        (for-each
          (lambda (v)
            (warn! (car v) (cadr v)
                   (sprintf "top-level set! of ~a at load time" (caddr v))))
          violations))))

;;; ============================================================
;;; 16. Special Variables Catalog
;;; ============================================================

(define (catalog-special-variables)
  (print "\n=== 16. Special Variables Catalog ===")
  (let ((modules (library-modules))
        (specials '())
        (by-domain (make-hash-table)))
    ;; Collect all *special* variables
    (for-each
      (lambda (f)
        (let* ((lines (with-input-from-file f read-lines))
               (line-num 0))
          (for-each
            (lambda (line)
              (set! line-num (+ line-num 1))
              ;; Match (define *name* ...) with optional docstring on next line
              (let ((m (irregex-search "^\\(define\\s+(\\*[a-zA-Z0-9-]+\\*)" line)))
                (when m
                  (let* ((name (irregex-match-substring m 1))
                         ;; Check for inline value hint
                         (value-hint
                           (cond
                             ((irregex-search "'\\(\\)" line) "empty list")
                             ((irregex-search "#f\\)" line) "false")
                             ((irregex-search "#t\\)" line) "true")
                             ((irregex-search "0\\)" line) "zero")
                             ((irregex-search "\"\"\\)" line) "empty string")
                             ((irregex-search "\\(make-hash-table\\)" line) "hash-table")
                             ((irregex-search "\\(make-parameter" line) "parameter")
                             (else #f))))
                    (set! specials
                      (cons (list name f line-num value-hint) specials))))))
            lines)))
      modules)

    ;; Categorize by prefix pattern
    (for-each
      (lambda (s)
        (let* ((name (car s))
               (domain (cond
                         ((irregex-search "^\\*ed25519|^\\*sha256|^\\*sha512|^\\*crypto|^\\*pq-|^\\*keystore|^\\*capability" name) 'crypto)
                         ((irregex-search "^\\*chunk|^\\*content|^\\*vault|^\\*catalog|^\\*merkle|^\\*bloom" name) 'storage)
                         ((irregex-search "^\\*gossip|^\\*federation|^\\*node-|^\\*wormhole|^\\*discovery|^\\*lamport|^\\*peer" name) 'network)
                         ((irregex-search "^\\*prompt|^\\*user-mode|^\\*help|^\\*theme|^\\*spinner|^\\*pager|^\\*result|^\\*inspector" name) 'repl)
                         ((irregex-search "^\\*edt|^\\*kill-ring|^\\*text\\*|^\\*filename" name) 'editor)
                         ((irregex-search "^\\*boot|^\\*cli|^\\*forge|^\\*compile|^\\*build" name) 'build)
                         ((irregex-search "^\\*test|^\\*verbose|^\\*error|^\\*warn|^\\*debug" name) 'debug)
                         ((irregex-search "^\\*fuse" name) 'fuse)
                         ((irregex-search "^\\*server|^\\*listener|^\\*port" name) 'server)
                         ((irregex-search "^\\*audit|^\\*security" name) 'audit)
                         (else 'misc))))
          (hash-table-update!/default by-domain domain
                                      (lambda (lst) (cons s lst)) '())))
      specials)

    ;; Report by domain
    (let ((domains '(crypto storage network repl editor build debug fuse server audit misc)))
      (for-each
        (lambda (domain)
          (let ((vars (hash-table-ref/default by-domain domain '())))
            (when (pair? vars)
              (printf "~n  ~a (~a):~n" domain (length vars))
              (for-each
                (lambda (v)
                  (let ((name (car v))
                        (file (cadr v))
                        (line (caddr v))
                        (hint (cadddr v)))
                    (if hint
                        (printf "    ~a  (~a:~a) [~a]~n" name file line hint)
                        (printf "    ~a  (~a:~a)~n" name file line))))
                (sort vars (lambda (a b) (string<? (car a) (car b))))))))
        domains))

    (printf "~n  Total: ~a special variables~n" (length specials))))

;;; ============================================================
;;; Main
;;; ============================================================

(define (main args)
  (when (member "--fix" args)
    (set! *fix-mode* #t)
    (print "Running in fix mode..."))

  (print "\n══════════════════════════════════════")
  (print "   Library Scrutiny Report")
  (print "══════════════════════════════════════")

  (check-module-naming)
  (check-export-patterns)
  (check-import-patterns)
  (check-documentation-style)
  (check-file-organization)
  (check-naming-coherence)
  (check-dead-code)
  (check-cross-references)
  (check-build-artifacts)
  (check-infinite-recursion)
  (check-duplicate-definitions)
  (check-tech-debt)
  (check-import-except-violations)
  (check-large-functions)
  (check-global-mutation)
  (catalog-special-variables)

  (print "\n=== Summary ===")
  (printf "  Errors:   ~a~n" *errors*)
  (printf "  Warnings: ~a~n" *warnings*)
  (printf "  Notes:    ~a~n" *notes*)

  (cond
    ((> *errors* 0)
     (print "\n  Library has issues requiring attention.")
     (exit 1))
    ((> *warnings* 0)
     (print "\n  Library is coherent with minor issues.")
     (exit 0))
    (else
     (print "\n  Library is coherent.")
     (exit 0))))

(main (command-line-arguments))
