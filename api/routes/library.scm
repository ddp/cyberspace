#!/usr/bin/env csi -s
;; Library Routes for Cyberspace API
;; Endpoints for searching and retrieving research papers

(module library-routes
  (scan-library search-library get-paper-metadata build-catalog)

  (import scheme)
  (import (chicken base))
  (import (chicken string))
  (import (chicken file))
  (import (chicken file posix))
  (import (chicken io))
  (import (chicken port))
  (import srfi-1)    ;; List utilities
  (import srfi-13)   ;; String libraries
  (import srfi-69)   ;; Hash tables

  ;; ============================================================================
  ;; Library Scanning
  ;; ============================================================================

  (define *library-path* "/Users/ddp/cyberspace/library")

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
                    filename))
           ;; Try to extract year from filename (e.g., "paper-1979.pdf")
           (year-match (string-search "-([0-9]{4})" filename))
           (year (if year-match
                    (substring filename (+ year-match 1) (+ year-match 5))
                    "unknown")))

      `((id . ,name)
        (title . ,name)
        (path . ,relative-path)
        (full_path . ,path)
        (category . ,category)
        (year . ,year)
        (type . "pdf"))))

  (define (scan-library)
    "Scan library directory and return list of papers"
    (let ((pdf-files (scan-directory *library-path*)))
      (map extract-metadata-from-path pdf-files)))

  ;; ============================================================================
  ;; Library Catalog
  ;; ============================================================================

  (define *catalog-cache* #f)
  (define *catalog-timestamp* 0)
  (define *catalog-ttl* 300)  ;; 5 minutes

  (define (build-catalog #!optional (force-refresh #f))
    "Build library catalog (cached)"
    (let ((now (current-seconds)))
      (if (or force-refresh
              (not *catalog-cache*)
              (> (- now *catalog-timestamp*) *catalog-ttl*))
          (begin
            (set! *catalog-cache* (scan-library))
            (set! *catalog-timestamp* now)
            *catalog-cache*)
          *catalog-cache*)))

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
    (let ((catalog (build-catalog)))
      (filter (lambda (paper)
                (matches-query? paper query))
              catalog)))

  ;; ============================================================================
  ;; Paper Metadata
  ;; ============================================================================

  (define (get-paper-metadata paper-id)
    "Get metadata for specific paper by ID"
    (let ((catalog (build-catalog)))
      (find (lambda (paper)
              (string=? (alist-ref 'id paper) paper-id))
            catalog)))

  ;; ============================================================================
  ;; Export
  ;; ============================================================================

) ;; end module
