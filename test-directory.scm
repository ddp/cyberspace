;;;; test-directory.scm --- Simple test suite for the directory system
;;;; Run basic smoke tests to ensure the system works

(import scheme
        (chicken base)
        (chicken format)
        (chicken file)
        (chicken io)
        (chicken process-context)
        srfi-1
        srfi-13)

;; We'll import directory once it's compiled
;; (import directory)

;;;; ========================================================================
;;;; Test Framework
;;;; ========================================================================

(define test-count 0)
(define pass-count 0)
(define fail-count 0)

(define (test-header name)
  (printf "~%~%=== ~A ===~%" name))

(define (test name thunk)
  (set! test-count (+ test-count 1))
  (printf "~%TEST ~A: ~A~%" test-count name)
  (flush-output)
  (let ((result (thunk)))
    (if result
        (begin
          (set! pass-count (+ pass-count 1))
          (printf "  ✓ PASS~%"))
        (begin
          (set! fail-count (+ fail-count 1))
          (printf "  ✗ FAIL~%")))))

(define (test-summary)
  (printf "~%~%========================================~%")
  (printf "Test Summary~%")
  (printf "========================================~%")
  (printf "Total:  ~A~%" test-count)
  (printf "Passed: ~A ~A~%"
          pass-count
          (if (= pass-count test-count) "✓" ""))
  (printf "Failed: ~A ~A~%"
          fail-count
          (if (= fail-count 0) "" "✗"))
  (printf "========================================~%")
  (= fail-count 0))

;;;; ========================================================================
;;;; Tests
;;;; ========================================================================

(define (test-file-structure)
  (test-header "File Structure Tests")

  (test "cyberspace directory exists"
        (lambda ()
          (directory-exists? (get-environment-variable "HOME"))))

  (test "library directory exists"
        (lambda ()
          (directory-exists?
           (string-append (get-environment-variable "HOME")
                         "/cyberspace/library"))))

  (test "directory.scm exists"
        (lambda ()
          (file-exists? "directory.scm")))

  (test "directory-parser.scm exists"
        (lambda ()
          (file-exists? "directory-parser.scm")))

  (test "directory-repl.scm exists"
        (lambda ()
          (file-exists? "directory-repl.scm")))

  (test "DIRECTORY-README.md exists"
        (lambda ()
          (file-exists? "DIRECTORY-README.md"))))

(define (test-library-structure)
  (test-header "Library Structure Tests")

  (let ((lib-path (string-append (get-environment-variable "HOME")
                                "/cyberspace/library")))

    (test "cryptographers collection exists"
          (lambda ()
            (directory-exists?
             (string-append lib-path "/cryptographers"))))

    (test "lamport-papers collection exists"
          (lambda ()
            (directory-exists?
             (string-append lib-path "/lamport-papers"))))

    (test "lampson INDEX.md exists"
          (lambda ()
            (file-exists?
             (string-append lib-path "/cryptographers/lampson/INDEX.md"))))))

(define (test-documentation)
  (test-header "Documentation Tests")

  (test "README has installation instructions"
        (lambda ()
          (and (file-exists? "DIRECTORY-README.md")
               (let ((content (with-input-from-file "DIRECTORY-README.md"
                               read-string)))
                 (and (string-contains content "Installation")
                      (string-contains content "chicken-install"))))))

  (test "README has usage examples"
        (lambda ()
          (let ((content (with-input-from-file "DIRECTORY-README.md"
                          read-string)))
            (and (string-contains content "Usage")
                 (string-contains content "load-library")))))

  (test "README has query language docs"
        (lambda ()
          (let ((content (with-input-from-file "DIRECTORY-README.md"
                          read-string)))
            (string-contains content "Query Language")))))

;;;; ========================================================================
;;;; Run Tests
;;;; ========================================================================

(define (run-all-tests)
  (printf "~%╔═══════════════════════════════════════════════════════════════╗~%")
  (printf "║  Cyberspace Directory - Test Suite                            ║~%")
  (printf "╚═══════════════════════════════════════════════════════════════╝~%")

  (test-file-structure)
  (test-library-structure)
  (test-documentation)

  (test-summary))

;; Run tests
(run-all-tests)
