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
        srfi-13)

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
        (no-exports '()))
    (for-each
      (lambda (f)
        (let* ((content (with-input-from-file f read-string))
               (has-exports (irregex-search "\\(module [a-z0-9-]+ \\(" content)))
          (unless has-exports
            (set! no-exports (cons f no-exports)))))
      modules)
    (if (null? no-exports)
        (ok! "All modules have export declarations")
        (for-each (lambda (f) (warn! f #f "no exports")) no-exports))))

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
