;;;; directory.scm --- Cyberspace Library Directory System
;;;; A comprehensive cataloging and search system for the research library
;;;;
;;;; Philosophy: "All information wants to be found"
;;;;
;;;; This implements a distributed directory service for navigating
;;;; the cyberspace library collection of cryptographic and distributed
;;;; systems research papers.

(module directory
  (;; Core data structures
   make-document
   make-collection
   make-library

   ;; Library operations
   scan-library
   load-library
   save-library

   ;; Query operations
   find-by-author
   find-by-topic
   find-by-year
   find-in-collection
   search-documents

   ;; Index generation
   generate-author-index
   generate-topic-index
   generate-chronological-index
   generate-cross-reference-index

   ;; Display operations
   display-document
   display-collection
   display-library-stats

   ;; Export operations
   export-to-sexp
   export-to-html
   export-to-markdown)

(import scheme
        (chicken base)
        (chicken file)
        (chicken io)
        (chicken pathname)
        (chicken port)
        (chicken process-context)
        (chicken sort)
        (chicken string)
        srfi-1   ; List library
        srfi-13  ; String library
        srfi-69) ; Hash tables

;;;; ========================================================================
;;;; Data Structures
;;;; ========================================================================

;;; Document record: represents a single research paper
(define-record document
  title           ; String: paper title
  authors         ; List of strings: author names
  year            ; Integer: publication year
  file-path       ; String: path to PDF file
  collection      ; String: collection name
  size            ; Integer: file size in bytes
  topics          ; List of strings: topics/keywords
  citations       ; String: citation format
  notes)          ; String: additional notes

;;; Collection record: represents a themed collection of papers
(define-record collection
  name            ; String: collection name
  path            ; String: filesystem path
  documents       ; List of document records
  index-file      ; String: path to INDEX.md
  description     ; String: collection description
  date-collected) ; String: collection date

;;; Library record: the complete cyberspace library
(define-record library
  root-path            ; String: library root directory
  collections          ; List of collection records
  documents            ; List of all document records
  author-index         ; Hash table: author -> list of documents
  topic-index          ; Hash table: topic -> list of documents
  year-index           ; Hash table: year -> list of documents
  collection-index)    ; Hash table: collection -> collection record

;;;; ========================================================================
;;;; INDEX.md Parser
;;;; ========================================================================

;;; Parse an INDEX.md file and extract document metadata
(define (parse-index-file index-path collection-name)
  (if (file-exists? index-path)
      (call-with-input-file index-path
        (lambda (port)
          (parse-index-lines (read-lines port) collection-name '())))
      '()))

;;; Read all lines from a port
(define (read-lines port)
  (let loop ((lines '()))
    (let ((line (read-line port)))
      (if (eof-object? line)
          (reverse lines)
          (loop (cons line lines))))))

;;; Parse INDEX.md lines into document records
(define (parse-index-lines lines collection-name docs)
  (if (null? lines)
      (reverse docs)
      (let ((doc (extract-document-from-section lines collection-name)))
        (if doc
            (parse-index-lines (cdr lines) collection-name (cons doc docs))
            (parse-index-lines (cdr lines) collection-name docs)))))

;;; Extract a document from a markdown section
;;; This is a simplified parser - would need enhancement for full INDEX.md parsing
(define (extract-document-from-section lines collection-name)
  ;; Look for patterns like "**filename.pdf** (size KB)"
  ;; This is a placeholder - real implementation would parse markdown fully
  #f)

;;;; ========================================================================
;;;; Library Scanner
;;;; ========================================================================

;;; Scan the library directory and build a library record
(define (scan-library root-path)
  (let ((collections (find-collections root-path)))
    (make-library
     root-path
     collections
     (apply append (map collection-documents collections))
     (make-hash-table)
     (make-hash-table)
     (make-hash-table)
     (make-hash-table))))

;;; Find all collections in the library (directories with INDEX.md)
(define (find-collections root-path)
  (let ((lib-path (make-pathname root-path "library")))
    (if (directory-exists? lib-path)
        (find-collections-recursive lib-path '())
        '())))

;;; Recursively find collections
(define (find-collections-recursive path collections)
  (let ((index-path (make-pathname path "INDEX.md")))
    (if (file-exists? index-path)
        ;; Found a collection
        (cons (load-collection path index-path) collections)
        ;; Check subdirectories
        (let ((subdirs (get-subdirectories path)))
          (fold (lambda (subdir acc)
                  (find-collections-recursive subdir acc))
                collections
                subdirs)))))

;;; Get subdirectories of a path
(define (get-subdirectories path)
  (if (directory-exists? path)
      (let ((entries (directory path #t)))
        (filter (lambda (entry)
                  (and (not (string=? entry "."))
                       (not (string=? entry ".."))
                       (directory-exists? (make-pathname path entry))))
                entries))
      '()))

;;; Load a collection from its INDEX.md file
(define (load-collection coll-path index-path)
  (let* ((name (pathname-file coll-path))
         (docs (parse-index-file index-path name))
         (desc (extract-collection-description index-path))
         (date (extract-collection-date index-path)))
    (make-collection name coll-path docs index-path desc date)))

;;; Extract collection description from INDEX.md
(define (extract-collection-description index-path)
  ;; Parse ## Overview section
  "Collection description")

;;; Extract collection date from INDEX.md
(define (extract-collection-date index-path)
  ;; Parse **Collection Date**: line
  "2026-01-03")

;;;; ========================================================================
;;;; Indexing Operations
;;;; ========================================================================

;;; Build author index from library
(define (build-author-index library)
  (let ((index (make-hash-table)))
    (for-each
     (lambda (doc)
       (for-each
        (lambda (author)
          (hash-table-update!/default
           index
           author
           (lambda (docs) (cons doc docs))
           '()))
        (document-authors doc)))
     (library-documents library))
    (library-author-index-set! library index)
    library))

;;; Build topic index from library
(define (build-topic-index library)
  (let ((index (make-hash-table)))
    (for-each
     (lambda (doc)
       (for-each
        (lambda (topic)
          (hash-table-update!/default
           index
           topic
           (lambda (docs) (cons doc docs))
           '()))
        (document-topics doc)))
     (library-documents library))
    (library-topic-index-set! library index)
    library))

;;; Build year index from library
(define (build-year-index library)
  (let ((index (make-hash-table)))
    (for-each
     (lambda (doc)
       (let ((year (document-year doc)))
         (when year
           (hash-table-update!/default
            index
            year
            (lambda (docs) (cons doc docs))
            '()))))
     (library-documents library))
    (library-year-index-set! library index)
    library))

;;; Build collection index from library
(define (build-collection-index library)
  (let ((index (make-hash-table)))
    (for-each
     (lambda (coll)
       (hash-table-set! index (collection-name coll) coll))
     (library-collections library))
    (library-collection-index-set! library index)
    library))

;;; Build all indexes
(define (build-indexes library)
  (build-collection-index
   (build-year-index
    (build-topic-index
     (build-author-index library)))))

;;;; ========================================================================
;;;; Query Operations
;;;; ========================================================================

;;; Find documents by author name
(define (find-by-author library author)
  (hash-table-ref/default (library-author-index library) author '()))

;;; Find documents by topic
(define (find-by-topic library topic)
  (hash-table-ref/default (library-topic-index library) topic '()))

;;; Find documents by year
(define (find-by-year library year)
  (hash-table-ref/default (library-year-index library) year '()))

;;; Find documents in a collection
(define (find-in-collection library collection-name)
  (let ((coll (hash-table-ref/default
               (library-collection-index library)
               collection-name
               #f)))
    (if coll
        (collection-documents coll)
        '())))

;;; Search documents by keyword in title
(define (search-documents library keyword)
  (filter (lambda (doc)
            (string-contains-ci (document-title doc) keyword))
          (library-documents library)))

;;;; ========================================================================
;;;; Index Generation
;;;; ========================================================================

;;; Generate author index (sorted alphabetically)
(define (generate-author-index library)
  (let ((authors (hash-table-keys (library-author-index library))))
    (sort authors string<?)))

;;; Generate topic index (sorted by frequency)
(define (generate-topic-index library)
  (let ((topics (hash-table-keys (library-topic-index library))))
    (sort topics
          (lambda (a b)
            (> (length (find-by-topic library a))
               (length (find-by-topic library b)))))))

;;; Generate chronological index (sorted by year)
(define (generate-chronological-index library)
  (let ((years (hash-table-keys (library-year-index library))))
    (sort years <)))

;;; Generate cross-reference index (finds related papers)
(define (generate-cross-reference-index library doc)
  ;; Find papers with overlapping authors or topics
  (let* ((same-authors
          (apply append
                 (map (lambda (author) (find-by-author library author))
                      (document-authors doc))))
         (same-topics
          (apply append
                 (map (lambda (topic) (find-by-topic library topic))
                      (document-topics doc)))))
    (delete-duplicates (append same-authors same-topics))))

;;;; ========================================================================
;;;; Display Operations
;;;; ========================================================================

;;; Display a document in human-readable format
(define (display-document doc)
  (printf "~%Title: ~A~%" (document-title doc))
  (printf "Authors: ~A~%" (string-join (document-authors doc) ", "))
  (printf "Year: ~A~%" (document-year doc))
  (printf "Collection: ~A~%" (document-collection doc))
  (printf "File: ~A~%" (document-file-path doc))
  (printf "Topics: ~A~%" (string-join (document-topics doc) ", "))
  (when (document-citations doc)
    (printf "Citation: ~A~%" (document-citations doc))))

;;; Display a collection summary
(define (display-collection coll)
  (printf "~%Collection: ~A~%" (collection-name coll))
  (printf "Path: ~A~%" (collection-path coll))
  (printf "Documents: ~A~%" (length (collection-documents coll)))
  (printf "Description: ~A~%" (collection-description coll)))

;;; Display library statistics
(define (display-library-stats library)
  (printf "~%Cyberspace Library Statistics~%")
  (printf "=============================~%")
  (printf "Root Path: ~A~%" (library-root-path library))
  (printf "Collections: ~A~%" (length (library-collections library)))
  (printf "Total Documents: ~A~%" (length (library-documents library)))
  (printf "Unique Authors: ~A~%"
          (hash-table-size (library-author-index library)))
  (printf "Unique Topics: ~A~%"
          (hash-table-size (library-topic-index library)))
  (printf "Year Range: ~A - ~A~%"
          (apply min (hash-table-keys (library-year-index library)))
          (apply max (hash-table-keys (library-year-index library)))))

;;;; ========================================================================
;;;; Export Operations
;;;; ========================================================================

;;; Export library to S-expression format
(define (export-to-sexp library filename)
  (call-with-output-file filename
    (lambda (port)
      (write (library->sexp library) port))))

;;; Convert library to S-expression
(define (library->sexp library)
  `(library
    (root-path ,(library-root-path library))
    (collections ,(map collection->sexp (library-collections library)))
    (documents ,(map document->sexp (library-documents library)))))

;;; Convert collection to S-expression
(define (collection->sexp coll)
  `(collection
    (name ,(collection-name coll))
    (path ,(collection-path coll))
    (description ,(collection-description coll))
    (date ,(collection-date-collected coll))))

;;; Convert document to S-expression
(define (document->sexp doc)
  `(document
    (title ,(document-title doc))
    (authors ,(document-authors doc))
    (year ,(document-year doc))
    (file-path ,(document-file-path doc))
    (collection ,(document-collection doc))
    (topics ,(document-topics doc))))

;;; Export library to HTML format
(define (export-to-html library filename)
  (call-with-output-file filename
    (lambda (port)
      (display (library->html library) port))))

;;; Convert library to HTML
(define (library->html library)
  (string-append
   "<!DOCTYPE html>\n"
   "<html>\n<head>\n"
   "<title>Cyberspace Library Directory</title>\n"
   "<style>\n"
   "  body { font-family: monospace; max-width: 80em; margin: 2em auto; }\n"
   "  h1 { border-bottom: 2px solid #000; }\n"
   "  .collection { margin: 2em 0; padding: 1em; background: #f5f5f5; }\n"
   "  .document { margin: 1em 0; padding: 0.5em; }\n"
   "</style>\n"
   "</head>\n<body>\n"
   "<h1>Cyberspace Library Directory</h1>\n"
   "<p><strong>Collections:</strong> "
   (number->string (length (library-collections library)))
   " | <strong>Documents:</strong> "
   (number->string (length (library-documents library)))
   "</p>\n"
   (apply string-append
          (map collection->html (library-collections library)))
   "</body>\n</html>\n"))

;;; Convert collection to HTML
(define (collection->html coll)
  (string-append
   "<div class=\"collection\">\n"
   "<h2>" (collection-name coll) "</h2>\n"
   "<p>" (collection-description coll) "</p>\n"
   "<p><em>Documents: "
   (number->string (length (collection-documents coll)))
   "</em></p>\n"
   "</div>\n"))

;;; Export library to Markdown format
(define (export-to-markdown library filename)
  (call-with-output-file filename
    (lambda (port)
      (display (library->markdown library) port))))

;;; Convert library to Markdown
(define (library->markdown library)
  (string-append
   "# Cyberspace Library Directory\n\n"
   "**Collections:** " (number->string (length (library-collections library)))
   " | **Documents:** " (number->string (length (library-documents library)))
   "\n\n"
   "## Collections\n\n"
   (apply string-append
          (map collection->markdown (library-collections library)))))

;;; Convert collection to Markdown
(define (collection->markdown coll)
  (string-append
   "### " (collection-name coll) "\n\n"
   (collection-description coll) "\n\n"
   "- **Path:** `" (collection-path coll) "`\n"
   "- **Documents:** " (number->string (length (collection-documents coll)))
   "\n\n"))

;;;; ========================================================================
;;;; Main API
;;;; ========================================================================

;;; Load and index the entire library
(define (load-library root-path)
  (let ((library (scan-library root-path)))
    (build-indexes library)))

;;; Save library to file
(define (save-library library filename)
  (export-to-sexp library filename))

) ; end module
