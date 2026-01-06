;;;; directory-example.scm --- Example usage of the Directory system
;;;; Shows how to use the cyberspace library directory programmatically

(import scheme
        (chicken base)
        (chicken format)
        directory)

;;;; ========================================================================
;;;; Example 1: Load and explore the library
;;;; ========================================================================

(define (example-1-basic-usage)
  (printf "~%=== Example 1: Basic Library Usage ===~%~%")

  ;; Load the library
  (let ((lib (load-library (get-environment-variable "HOME"))))

    ;; Show statistics
    (printf "Library Statistics:~%")
    (display-library-stats lib)

    ;; List first 5 collections
    (printf "~%First 5 collections:~%")
    (for-each (lambda (coll idx)
                (printf "  ~A. ~A~%" idx (collection-name coll)))
              (take (library-collections lib) 5)
              (iota 5 1))))

;;;; ========================================================================
;;;; Example 2: Search for papers by author
;;;; ========================================================================

(define (example-2-author-search)
  (printf "~%=== Example 2: Find Papers by Author ===~%~%")

  (let ((lib (load-library (get-environment-variable "HOME"))))

    ;; Find all Lampson papers
    (printf "Papers by Butler Lampson:~%")
    (let ((lampson-papers (find-by-author lib "Butler Lampson")))
      (printf "Found ~A papers~%~%" (length lampson-papers))
      (for-each (lambda (doc)
                  (printf "  • ~A (~A)~%"
                          (document-title doc)
                          (document-year doc)))
                lampson-papers))))

;;;; ========================================================================
;;;; Example 3: Find papers by topic
;;;; ========================================================================

(define (example-3-topic-search)
  (printf "~%=== Example 3: Find Papers by Topic ===~%~%")

  (let ((lib (load-library (get-environment-variable "HOME"))))

    ;; Find SPKI/SDSI papers
    (printf "Papers about SPKI:~%")
    (let ((spki-papers (find-by-topic lib "SPKI")))
      (printf "Found ~A papers~%~%" (length spki-papers))
      (for-each (lambda (doc)
                  (printf "  • ~A~%    by ~A~%"
                          (document-title doc)
                          (string-join (document-authors doc) ", ")))
                spki-papers))))

;;;; ========================================================================
;;;; Example 4: Generate indexes
;;;; ========================================================================

(define (example-4-generate-indexes)
  (printf "~%=== Example 4: Generate Indexes ===~%~%")

  (let ((lib (load-library (get-environment-variable "HOME"))))

    ;; Author index (alphabetical)
    (printf "Top 10 authors (alphabetically):~%")
    (for-each (lambda (author)
                (printf "  • ~A~%" author))
              (take (generate-author-index lib) 10))

    ;; Topic index (by frequency)
    (printf "~%Top 10 topics (by frequency):~%")
    (for-each (lambda (topic)
                (printf "  • ~A (~A papers)~%"
                        topic
                        (length (find-by-topic lib topic))))
              (take (generate-topic-index lib) 10))

    ;; Chronological index
    (printf "~%Year range:~%")
    (let ((years (generate-chronological-index lib)))
      (printf "  ~A - ~A~%" (car years) (last years)))))

;;;; ========================================================================
;;;; Example 5: Export library to different formats
;;;; ========================================================================

(define (example-5-export-formats)
  (printf "~%=== Example 5: Export to Different Formats ===~%~%")

  (let ((lib (load-library (get-environment-variable "HOME"))))

    ;; Export to S-expression
    (printf "Exporting to library-catalog.scm...~%")
    (export-to-sexp lib "library-catalog.scm")
    (printf "  ✓ S-expression format~%")

    ;; Export to HTML
    (printf "Exporting to library-catalog.html...~%")
    (export-to-html lib "library-catalog.html")
    (printf "  ✓ HTML format~%")

    ;; Export to Markdown
    (printf "Exporting to library-catalog.md...~%")
    (export-to-markdown lib "library-catalog.md")
    (printf "  ✓ Markdown format~%")))

;;;; ========================================================================
;;;; Example 6: Find related papers
;;;; ========================================================================

(define (example-6-find-related)
  (printf "~%=== Example 6: Find Related Papers ===~%~%")

  (let ((lib (load-library (get-environment-variable "HOME"))))

    ;; Find a paper
    (let ((docs (find-by-author lib "Rivest")))
      (when (not (null? docs))
        (let ((doc (car docs)))
          (printf "Starting with: ~A~%" (document-title doc))

          ;; Find related papers
          (let ((related (generate-cross-reference-index lib doc)))
            (printf "~%Found ~A related papers:~%" (length related))
            (for-each (lambda (related-doc idx)
                        (when (< idx 5)  ; Show first 5
                          (printf "  ~A. ~A~%"
                                  (+ idx 1)
                                  (document-title related-doc))))
                      related
                      (iota (length related)))))))))

;;;; ========================================================================
;;;; Run all examples
;;;; ========================================================================

(define (run-all-examples)
  (printf "~%╔═══════════════════════════════════════════════════════════════╗~%")
  (printf "║  Cyberspace Library Directory - Examples                      ║~%")
  (printf "╚═══════════════════════════════════════════════════════════════╝~%")

  (example-1-basic-usage)
  (example-2-author-search)
  (example-3-topic-search)
  (example-4-generate-indexes)
  (example-5-export-formats)
  (example-6-find-related)

  (printf "~%All examples completed!~%~%"))

;; Run if executed as script
(when (member "directory-example.scm" (command-line-arguments))
  (run-all-examples))
