#!/usr/bin/env csi -s
;; The Cyberspace Librarian - Query Engine
;; Natural language search for the Library of Cyberspace

(import scheme)
(import (chicken base))
(import (chicken port))
(import (chicken process-context))
(import (chicken string))
(import (chicken io))
(import (chicken file))
(import (chicken pathname))
(import (chicken sort))
(import srfi-1)
(import srfi-13)

;; Load our modules (relative to this file)
(load "embedder.scm")
(load "index-builder.scm")

;; ============================================================================
;; Configuration
;; ============================================================================

(define *library-root*
  (make-pathname (get-environment-variable "HOME")
                 "cyberspace/library"))

(define *index-cache-file* "library-index.scm")

;; ============================================================================
;; Index Management
;; ============================================================================

(define (load-or-build-index)
  "Load cached index or rebuild from library"
  (if (file-exists? *index-cache-file*)
      (begin
        (print "Loading cached index from " *index-cache-file*)
        (with-input-from-file *index-cache-file* read))
      (begin
        (print "Building index from " *library-root*)
        (let ((index (build-index *library-root*)))
          (print "Caching index to " *index-cache-file*)
          (with-output-to-file *index-cache-file*
            (lambda () (write index)))
          index))))

(define (rebuild-index!)
  "Force rebuild of index"
  (when (file-exists? *index-cache-file*)
    (delete-file* *index-cache-file*))
  (load-or-build-index))

;; ============================================================================
;; Semantic Search
;; ============================================================================

(define (search-library query #!optional (top-k 5))
  "Semantic search across library using embeddings"
  (print "Query: " query)
  (print "")

  ;; Try to generate embedding for query
  (print "Generating query embedding...")
  (let ((query-emb (embed-text query)))

    ;; If embeddings not available, fall back to keyword search
    (when (not query-emb)
      (print "Falling back to keyword search...")
      (print ""))

    ;; Load library index
    (print "Loading library index...")
    (let ((index (load-or-build-index)))

      ;; For now, use simple text matching until we have embeddings for all docs
      ;; TODO: Generate and cache embeddings for all INDEX.md files
      (print "Searching " (length index) " collections...")
      (print "")

      ;; Simple keyword search (works with or without embeddings)
      (keyword-search query index top-k))))

;; ============================================================================
;; Keyword Search (Fallback until embeddings are cached)
;; ============================================================================

(define (keyword-search query index top-k)
  "Simple keyword-based search through index"
  (let* ((query-lower (string-downcase query))
         (keywords (string-split query-lower))
         (scored-docs
          (map (lambda (doc)
                 (let* ((content (cdr (assoc 'content doc)))
                        (content-lower (string-downcase content))
                        (score (count-keyword-matches keywords content-lower)))
                   (cons (cons 'score score) doc)))
               index))
         (sorted (sort scored-docs
                      (lambda (a b)
                        (> (cdr (assoc 'score a))
                           (cdr (assoc 'score b))))))
         (results (take* sorted top-k)))

    ;; Display results
    (print "Found " (length (filter (lambda (doc)
                                      (> (cdr (assoc 'score doc)) 0))
                                    scored-docs))
           " relevant collections")
    (print "")
    (print "Top " top-k " results:")
    (print "")

    (for-each display-result results)
    results))

(define (count-keyword-matches keywords text)
  "Count how many query keywords appear in text"
  (apply + (map (lambda (kw)
                  (if (string-contains text kw) 1 0))
                keywords)))

(define (display-result doc)
  "Pretty print a search result"
  (let ((score (cdr (assoc 'score doc)))
        (title (cdr (assoc 'title doc)))
        (path (cdr (assoc 'path doc)))
        (papers (cdr (assoc 'papers doc)))
        (years (cdr (assoc 'years doc))))

    (when (> score 0)
      (print "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
      (print "Score: " score " | " title)
      (print "Path: " path)
      (when (not (null? years))
        (print "Years: " (string-join years ", ")))
      (print "Papers: " (length papers))
      (when (> (length papers) 0)
        (for-each (lambda (paper)
                    (print "  • " paper))
                  (take* papers 3)))
      (when (> (length papers) 3)
        (print "  ... and " (- (length papers) 3) " more"))
      (print ""))))

(define (take* lst n)
  "Take up to n elements from list"
  (if (or (null? lst) (<= n 0))
      '()
      (cons (car lst) (take* (cdr lst) (- n 1)))))

;; ============================================================================
;; Example Queries
;; ============================================================================

(define (demo-queries)
  "Run example queries to demonstrate the system"
  (let ((queries '("Papers about hash-based crypto before PKI"
                   "microkernels and formal verification"
                   "one-time passwords and authentication"
                   "Merkle trees and content-addressable storage"
                   "verified systems and theorem proving")))

    (print "==============================================")
    (print "Cyberspace Librarian - Demo Queries")
    (print "==============================================")
    (print "")

    (for-each (lambda (q)
                (print "")
                (print "========================================")
                (search-library q 3)
                (print "========================================")
                (print ""))
              queries)))

;; ============================================================================
;; CLI Interface
;; ============================================================================

(define (show-help)
  (print "Cyberspace Librarian - Query Engine")
  (print "")
  (print "Usage:")
  (print "  ./query.scm \"your natural language query\"")
  (print "  ./query.scm --rebuild    # Rebuild index")
  (print "  ./query.scm --demo       # Run example queries")
  (print "")
  (print "Examples:")
  (print "  ./query.scm \"Papers about hash-based crypto before PKI\"")
  (print "  ./query.scm \"microkernels and formal verification\"")
  (print "  ./query.scm \"one-time passwords\"")
  (print ""))

;; Main entry point
(when (not (zero? (length (command-line-arguments))))
  (let ((arg (car (command-line-arguments))))
    (cond
     ((string=? arg "--help")
      (show-help))

     ((string=? arg "--rebuild")
      (print "Rebuilding index...")
      (rebuild-index!)
      (print "Done!"))

     ((string=? arg "--demo")
      (demo-queries))

     (else
      ;; Treat as query
      (search-library arg 5)))))

;; REPL usage
(when (equal? (program-name) "csi")
  (print "Cyberspace Librarian - Query Engine")
  (print "")
  (print "Functions available:")
  (print "  (search-library \"query\" [top-k])  ; Search library")
  (print "  (rebuild-index!)                   ; Rebuild index")
  (print "  (demo-queries)                     ; Run examples")
  (print ""))
