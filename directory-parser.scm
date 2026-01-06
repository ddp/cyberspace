;;;; directory-parser.scm --- INDEX.md Markdown Parser
;;;; Extracts structured metadata from INDEX.md files
;;;;
;;;; Parses the INDEX.md format used in the cyberspace library collections

(module directory-parser
  (parse-index-md
   extract-metadata
   extract-papers
   extract-collection-info)

(import scheme
        (chicken base)
        (chicken io)
        (chicken file)
        (chicken string)
        (chicken irregex)
        srfi-1
        srfi-13)

;;;; ========================================================================
;;;; Parser State
;;;; ========================================================================

(define-record parser-state
  lines           ; List of lines
  current-line    ; Current line number
  collection-name ; Collection name
  collection-date ; Collection date
  collection-size ; Total size
  description     ; Overview description
  papers)         ; List of paper records

(define-record paper-metadata
  filename        ; PDF filename
  size            ; File size
  title           ; Paper title
  authors         ; List of authors
  published       ; Publication venue/date
  significance    ; Why important
  concepts        ; Key concepts
  source-url)     ; Source URL

;;;; ========================================================================
;;;; Main Parser
;;;; ========================================================================

;;; Parse an INDEX.md file into structured data
(define (parse-index-md filepath collection-name)
  (if (file-exists? filepath)
      (call-with-input-file filepath
        (lambda (port)
          (let ((lines (port->lines port)))
            (parse-lines lines collection-name))))
      (begin
        (fprintf (current-error-port)
                 "Warning: INDEX.md not found: ~A~%" filepath)
        '())))

;;; Read all lines from port
(define (port->lines port)
  (let loop ((lines '()))
    (let ((line (read-line port)))
      (if (eof-object? line)
          (reverse lines)
          (loop (cons line lines))))))

;;; Parse lines into structured data
(define (parse-lines lines collection-name)
  (let ((state (make-parser-state lines 0 collection-name "" "" "" '())))
    ;; Extract metadata from header
    (set! state (extract-collection-metadata state))
    ;; Extract papers section
    (set! state (extract-papers-section state))
    ;; Return parsed data
    `((collection-name . ,(parser-state-collection-name state))
      (collection-date . ,(parser-state-collection-date state))
      (collection-size . ,(parser-state-collection-size state))
      (description . ,(parser-state-description state))
      (papers . ,(parser-state-papers state)))))

;;;; ========================================================================
;;;; Metadata Extraction
;;;; ========================================================================

;;; Extract collection metadata from header
(define (extract-collection-metadata state)
  (let loop ((idx 0))
    (if (>= idx (length (parser-state-lines state)))
        state
        (let ((line (list-ref (parser-state-lines state) idx)))
          (cond
           ;; **Collection Date**: 2026-01-03
           ((irregex-search "^\\*\\*Collection Date\\*\\*: (.+)$" line)
            => (lambda (m)
                 (parser-state-collection-date-set!
                  state
                  (irregex-match-substring m 1))
                 (loop (+ idx 1))))

           ;; **Total Size**: ~674 KB
           ((irregex-search "^\\*\\*Total Size\\*\\*: (.+)$" line)
            => (lambda (m)
                 (parser-state-collection-size-set!
                  state
                  (irregex-match-substring m 1))
                 (loop (+ idx 1))))

           ;; ## Overview
           ((irregex-search "^## Overview$" line)
            (let ((desc (extract-overview (parser-state-lines state) (+ idx 1))))
              (parser-state-description-set! state desc)
              (loop (+ idx 1))))

           (else (loop (+ idx 1))))))))

;;; Extract overview text until next section
(define (extract-overview lines start-idx)
  (let loop ((idx start-idx)
             (text '()))
    (if (or (>= idx (length lines))
            (irregex-search "^##" (list-ref lines idx)))
        (string-join (reverse text) " ")
        (let ((line (string-trim-both (list-ref lines idx))))
          (if (string=? line "")
              (loop (+ idx 1) text)
              (loop (+ idx 1) (cons line text)))))))

;;;; ========================================================================
;;;; Paper Extraction
;;;; ========================================================================

;;; Extract papers section
(define (extract-papers-section state)
  (let loop ((idx 0)
             (papers '())
             (current-paper #f))
    (if (>= idx (length (parser-state-lines state)))
        (begin
          (parser-state-papers-set! state (reverse papers))
          state)
        (let ((line (list-ref (parser-state-lines state) idx)))
          (cond
           ;; **filename.pdf** (size KB)
           ((irregex-search "^\\*\\*([^*]+\\.pdf)\\*\\* \\(([^)]+)\\)$" line)
            => (lambda (m)
                 (let ((new-paper (make-paper-metadata
                                   (irregex-match-substring m 1) ; filename
                                   (irregex-match-substring m 2) ; size
                                   "" '() "" "" '() "")))
                   (if current-paper
                       (loop (+ idx 1) (cons current-paper papers) new-paper)
                       (loop (+ idx 1) papers new-paper)))))

           ;; - **Title**: "..."
           ((and current-paper
                 (irregex-search "^- \\*\\*Title\\*\\*: \"(.+)\"$" line))
            => (lambda (m)
                 (paper-metadata-title-set!
                  current-paper
                  (irregex-match-substring m 1))
                 (loop (+ idx 1) papers current-paper)))

           ;; - **Authors**: Name1, Name2
           ((and current-paper
                 (irregex-search "^- \\*\\*Authors?\\*\\*: (.+)$" line))
            => (lambda (m)
                 (let ((authors-str (irregex-match-substring m 1)))
                   (paper-metadata-authors-set!
                    current-paper
                    (map string-trim-both
                         (string-split authors-str ",")))
                   (loop (+ idx 1) papers current-paper))))

           ;; - **Published**: ...
           ((and current-paper
                 (irregex-search "^- \\*\\*Published\\*\\*: (.+)$" line))
            => (lambda (m)
                 (paper-metadata-published-set!
                  current-paper
                  (irregex-match-substring m 1))
                 (loop (+ idx 1) papers current-paper)))

           ;; - **Source**: http://...
           ((and current-paper
                 (irregex-search "^- \\*\\*Source\\*\\*: (.+)$" line))
            => (lambda (m)
                 (paper-metadata-source-url-set!
                  current-paper
                  (irregex-match-substring m 1))
                 (loop (+ idx 1) papers current-paper)))

           (else (loop (+ idx 1) papers current-paper)))))))

;;;; ========================================================================
;;;; Helper Functions
;;;; ========================================================================

;;; Extract collection info from parsed data
(define (extract-collection-info parsed)
  `((name . ,(alist-ref 'collection-name parsed))
    (date . ,(alist-ref 'collection-date parsed))
    (size . ,(alist-ref 'collection-size parsed))
    (description . ,(alist-ref 'description parsed))))

;;; Extract papers from parsed data
(define (extract-papers parsed)
  (alist-ref 'papers parsed))

;;; Extract specific metadata field
(define (extract-metadata parsed field)
  (alist-ref field parsed))

) ; end module
