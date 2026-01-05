#!/usr/bin/env csi -s
;; Demo: Library Search Functionality
;; Demonstrates scanning library and searching for papers

(import scheme)
(import (chicken base))
(import (chicken string))
(import (chicken file))
(import (chicken file posix))
(import (chicken io))
(import (chicken format))
(import (chicken process-context))
(import srfi-1)    ;; List utilities
(import srfi-13)   ;; String libraries
(import srfi-69)   ;; Hash tables

;; ============================================================================
;; Configuration
;; ============================================================================

(define *library-path* "/Users/ddp/cyberspace/library")

;; ============================================================================
;; Helper Functions
;; ============================================================================

(define (file-extension path)
  "Get file extension"
  (let ((parts (string-split path ".")))
    (if (> (length parts) 1)
        (last parts)
        "")))

(define (directory-exists? path)
  "Check if directory exists"
  (and (file-exists? path)
       (directory? path)))

;; ============================================================================
;; Library Scanning
;; ============================================================================

(define (scan-directory dir)
  "Recursively scan directory for PDF files"
  (if (not (directory-exists? dir))
      '()
      (let ((entries (directory dir #t)))
        (apply append
               (map (lambda (entry)
                      (let ((full-path (string-append dir "/" entry)))
                        (cond
                         ;; Skip hidden files and directories
                         ((string-prefix? "." entry) '())

                         ;; Recurse into subdirectories
                         ((directory? full-path)
                          (scan-directory full-path))

                         ;; Collect PDF files
                         ((string=? (file-extension entry) "pdf")
                          (list full-path))

                         ;; Skip other files
                         (else '()))))
                    entries)))))

(define (extract-metadata-from-path path)
  "Extract metadata from file path and name"
  (let* ((relative-path (if (string-prefix? *library-path* path)
                           (substring path (+ 1 (string-length *library-path*)))
                           path))
         (parts (string-split relative-path "/"))
         (filename (last parts))
         (category (if (> (length parts) 1)
                      (car parts)
                      "uncategorized"))
         ;; Remove .pdf extension
         (name (if (string-suffix? ".pdf" filename)
                  (substring filename 0 (- (string-length filename) 4))
                  filename)))

    `((id . ,name)
      (title . ,name)
      (path . ,relative-path)
      (category . ,category))))

(define (scan-library)
  "Scan library directory and return list of papers"
  (let ((pdf-files (scan-directory *library-path*)))
    (map extract-metadata-from-path pdf-files)))

;; ============================================================================
;; Search
;; ============================================================================

(define (matches-query? paper query)
  "Check if paper matches search query"
  (let ((query-lower (string-downcase query))
        (title-lower (string-downcase (alist-ref 'title paper)))
        (category-lower (string-downcase (alist-ref 'category paper)))
        (path-lower (string-downcase (alist-ref 'path paper))))

    (or (string-contains title-lower query-lower)
        (string-contains category-lower query-lower)
        (string-contains path-lower query-lower))))

(define (search-library query)
  "Search library for papers matching query"
  (let ((catalog (scan-library)))
    (filter (lambda (paper)
              (matches-query? paper query))
            catalog)))

;; ============================================================================
;; Display Functions
;; ============================================================================

(define (display-paper paper)
  "Display paper metadata"
  (printf "  ┌─────────────────────────────────────────────────────────────────┐~%")
  (printf "  │ ~A~%" (alist-ref 'title paper))
  (printf "  ├─────────────────────────────────────────────────────────────────┤~%")
  (printf "  │ Category: ~A~%" (alist-ref 'category paper))
  (printf "  │ Path:     ~A~%" (alist-ref 'path paper))
  (printf "  └─────────────────────────────────────────────────────────────────┘~%")
  (printf "~%"))

(define (display-search-results query results)
  "Display search results"
  (printf "╔═══════════════════════════════════════════════════════════════════╗~%")
  (printf "║               CYBERSPACE LIBRARY SEARCH RESULTS                   ║~%")
  (printf "╚═══════════════════════════════════════════════════════════════════╝~%~%")

  (printf "Query: ~A~%" query)
  (printf "Found: ~A papers~%~%" (length results))

  (if (null? results)
      (printf "No papers found matching '~A'~%" query)
      (for-each display-paper results)))

;; ============================================================================
;; Main Demo
;; ============================================================================

(define (demo-search)
  "Demo library search"
  (display "Scanning library...\n\n")

  ;; Search for "lamport"
  (let ((results (search-library "lamport")))
    (display-search-results "lamport" results))

  (newline)

  ;; Search for "merkle"
  (let ((results (search-library "merkle")))
    (display-search-results "merkle" results))

  (newline)

  ;; Search for "crypto"
  (let ((results (search-library "crypto")))
    (display-search-results "crypto" (take results (min 5 (length results))))))

(define (demo-catalog)
  "Demo full catalog"
  (display "Building library catalog...\n\n")

  (let ((catalog (scan-library)))
    (printf "╔═══════════════════════════════════════════════════════════════════╗~%")
    (printf "║                  CYBERSPACE LIBRARY CATALOG                       ║~%")
    (printf "╚═══════════════════════════════════════════════════════════════════╝~%~%")

    (printf "Total papers: ~A~%~%" (length catalog))

    ;; Group by category
    (let ((by-category (make-hash-table equal?)))
      (for-each (lambda (paper)
                  (let ((category (alist-ref 'category paper)))
                    (hash-table-update!/default by-category
                                               category
                                               (lambda (papers) (cons paper papers))
                                               '())))
                catalog)

      ;; Display categories
      (hash-table-walk by-category
        (lambda (category papers)
          (printf "Category: ~A (~A papers)~%" category (length papers)))))))

;; ============================================================================
;; CLI
;; ============================================================================

(cond
 ((null? (command-line-arguments))
  (demo-search))

 ((string=? (car (command-line-arguments)) "catalog")
  (demo-catalog))

 ((string=? (car (command-line-arguments)) "search")
  (if (>= (length (command-line-arguments)) 2)
      (let ((query (cadr (command-line-arguments)))
            (results (search-library (cadr (command-line-arguments)))))
        (display-search-results query results))
      (printf "Usage: ~A search <query>~%" (program-name))))

 (else
  (display "Cyberspace Library Search Demo\n\n")
  (display "Usage:\n")
  (display "  ./demo-library-search.scm           # Run demo searches\n")
  (display "  ./demo-library-search.scm catalog   # Show full catalog\n")
  (display "  ./demo-library-search.scm search <query>\n")
  (display "\n")))
