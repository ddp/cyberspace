#!/usr/bin/env csi -s
;; The Cyberspace Librarian - Index Builder
;; Walks ~/cyberspace/library/ and builds searchable index from INDEX.md files

(import scheme)
(import (chicken base))
(import (chicken file))
(import (chicken file posix))
(import (chicken pathname))
(import (chicken port))
(import (chicken io))
(import (chicken process-context))
(import (chicken string))
(import (chicken irregex))
(import srfi-1)
(import srfi-13)

;; ============================================================================
;; File Walking
;; ============================================================================

(define (find-index-files root)
  "Recursively find all INDEX.md files under root directory"
  (define (walk-directory dir)
    (let ((entries (directory dir #t)))
      (append-map
       (lambda (entry)
         (let ((path (make-pathname dir entry)))
           (cond
            ((and (directory? path)
                  (not (string-prefix? "." entry)))  ; Skip hidden dirs
             (walk-directory path))
            ((string=? entry "INDEX.md")
             (list path))
            (else '()))))
       entries)))

  (if (directory-exists? root)
      (walk-directory root)
      (begin
        (print "Error: Directory not found: " root)
        '())))

;; ============================================================================
;; INDEX.md Parsing
;; ============================================================================

(define (parse-index-file path)
  "Parse an INDEX.md file and extract metadata"
  (let ((content (call-with-input-file path
                   (lambda (port)
                     (read-string #f port))))
        (collection (pathname-directory path)))

    ;; Extract key information using irregex
    (let ((title (extract-title content))
          (papers (extract-papers content))
          (years (extract-years content))
          (authors (extract-authors content))
          (keywords (extract-keywords content)))

      `((path . ,path)
        (collection . ,collection)
        (title . ,title)
        (papers . ,papers)
        (years . ,years)
        (authors . ,authors)
        (keywords . ,keywords)
        (content . ,content)))))

(define (extract-title content)
  "Extract main title (first # heading)"
  (let ((match (irregex-search '(: bol "#" (+ space) (submatch (* any)) eol) content)))
    (if match
        (irregex-match-substring match 1)
        "Untitled")))

(define (extract-papers content)
  "Extract paper titles (### headings that look like filenames)"
  (let ((matches (irregex-fold
                  '(: bol "###" (+ space) (submatch (+ (~ "\n"))) eol)
                  (lambda (i match seed)
                    (cons (string-trim-both (irregex-match-substring match 1))
                          seed))
                  '()
                  content)))
    (reverse matches)))

(define (extract-years content)
  "Extract years mentioned (4-digit numbers 1900-2099)"
  (let ((matches (irregex-fold
                  '(: (submatch (: (or "1" "2") digit digit digit)))
                  (lambda (i match seed)
                    (let ((year (irregex-match-substring match 1)))
                      (if (and (>= (string->number year) 1900)
                               (<= (string->number year) 2099))
                          (cons year seed)
                          seed)))
                  '()
                  content)))
    (delete-duplicates (reverse matches) string=?)))

(define (extract-authors content)
  "Extract author names (heuristic: capitalized words before publication years)"
  ;; Simplified: look for patterns like "Name (year)" or "Name et al"
  (let ((matches (irregex-fold
                  '(: (submatch (: upper (* (or alnum space "-"))
                                   (? " et al")))
                      (or (: space "(" digit digit digit digit ")")
                          (: space "(")
                          ":"
                          ","))
                  (lambda (i match seed)
                    (let ((author (string-trim-both (irregex-match-substring match 1))))
                      (if (> (string-length author) 3)  ; Skip short matches
                          (cons author seed)
                          seed)))
                  '()
                  content)))
    (delete-duplicates (reverse matches) string=?)))

(define (extract-keywords content)
  "Extract important keywords (technical terms in **bold**)"
  (let ((matches (irregex-fold
                  '(: "**" (submatch (+ (~ "*"))) "**")
                  (lambda (i match seed)
                    (cons (irregex-match-substring match 1) seed))
                  '()
                  content)))
    (delete-duplicates (reverse matches) string=?)))

;; ============================================================================
;; Pretty Printing
;; ============================================================================

(define (print-index-entry entry)
  "Pretty print an index entry"
  (print "\n========================================")
  (print "Collection: " (cdr (assoc 'collection entry)))
  (print "Title: " (cdr (assoc 'title entry)))
  (print "Papers: " (length (cdr (assoc 'papers entry))))
  (for-each (lambda (paper) (print "  - " paper))
            (take* (cdr (assoc 'papers entry)) 3))  ; Show first 3
  (print "Years: " (string-join (cdr (assoc 'years entry)) ", "))
  (print "Authors: " (length (cdr (assoc 'authors entry))))
  (print "Keywords: " (length (cdr (assoc 'keywords entry)))))

(define (take* lst n)
  "Take up to n elements from list"
  (if (or (null? lst) (<= n 0))
      '()
      (cons (car lst) (take* (cdr lst) (- n 1)))))

;; ============================================================================
;; Main
;; ============================================================================

(define (build-index library-root)
  "Build index of all INDEX.md files in library"
  (print "Building index for: " library-root)
  (let ((index-files (find-index-files library-root)))
    (print "Found " (length index-files) " INDEX.md files")
    (print "")

    (let ((entries (map parse-index-file index-files)))
      (for-each print-index-entry entries)
      (print "\n========================================")
      (print "Total collections: " (length entries))

      ;; Return parsed entries
      entries)))

;; Run if executed as script
(when (not (zero? (length (command-line-arguments))))
  (let ((library-root (car (command-line-arguments))))
    (build-index library-root)))

;; Export for use as module
(define library-root
  (make-pathname (get-environment-variable "HOME")
                 "cyberspace/library"))

;; Example usage
(when (equal? (program-name) "csi")
  (print "Usage: ./index-builder.scm ~/cyberspace/library")
  (print "Or from REPL: (build-index \"~/cyberspace/library\")"))
