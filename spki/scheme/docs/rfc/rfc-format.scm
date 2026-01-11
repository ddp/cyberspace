;; RFC Document Processors
;; S-expression source → txt, ps, html
;;
;; Usage:
;;   (load "rfc-format.scm")
;;   (define doc (read-rfc "rfc-000-declaration.scm"))
;;   (rfc->txt doc "rfc-000-declaration.txt")
;;   (rfc->ps doc "rfc-000-declaration.ps")
;;   (rfc->html doc "rfc-000-declaration.html")

(import scheme
        (chicken base)
        (chicken io)
        (chicken string)
        (chicken format)
        (chicken file)
        (chicken pathname)
        (chicken process)
        srfi-13)

;; Zero-pad a number to width
(define (zero-pad n width)
  (let ((s (number->string n)))
    (string-append (make-string (max 0 (- width (string-length s))) #\0) s)))

;;; ============================================================
;;; Document Reader
;;; ============================================================

(define (read-rfc filename)
  "Read an RFC S-expression from file."
  (with-input-from-file filename read))

;;; ============================================================
;;; Text Output (Plain ASCII, 78 columns)
;;; ============================================================

(define txt-width 78)
(define txt-indent 0)

(define (txt-hr)
  (make-string txt-width #\-))

(define (txt-wrap text width indent)
  "Word-wrap text to width with indent."
  (let* ((words (string-split text))
         (indent-str (make-string indent #\space)))
    (let loop ((words words) (line indent-str) (lines '()))
      (if (null? words)
          (reverse (if (> (string-length line) indent)
                       (cons line lines)
                       lines))
          (let* ((word (car words))
                 (new-line (if (= (string-length line) indent)
                               (string-append line word)
                               (string-append line " " word))))
            (if (> (string-length new-line) width)
                (if (= (string-length line) indent)
                    ;; Word itself too long - emit it and continue
                    (loop (cdr words) indent-str (cons new-line lines))
                    ;; Line + word too long - emit line, retry word
                    (loop words indent-str (cons line lines)))
                (loop (cdr words) new-line lines)))))))

(define (txt-emit-p text port indent)
  (for-each (lambda (line)
              (display line port)
              (newline port))
            (txt-wrap text txt-width indent))
  (newline port))

(define (txt-emit-element elem port indent)
  (cond
    ((string? elem) (txt-emit-p elem port indent))
    ((not (pair? elem)) #f)
    (else
      (case (car elem)
        ((p) (txt-emit-p (apply string-append (map ->string (cdr elem))) port indent))

        ((section)
          (newline port)
          (display (txt-hr) port) (newline port)
          (display (string-upcase (cadr elem)) port) (newline port)
          (display (txt-hr) port) (newline port)
          (newline port)
          (for-each (lambda (e) (txt-emit-element e port indent)) (cddr elem)))

        ((subsection)
          (newline port)
          (display (cadr elem) port) (newline port)
          (display (make-string (string-length (cadr elem)) #\-) port) (newline port)
          (newline port)
          (for-each (lambda (e) (txt-emit-element e port indent)) (cddr elem)))

        ((list)
          (for-each (lambda (item)
                      (display "  * " port)
                      (if (and (pair? item) (eq? (car item) 'item))
                          (let ((content (cdr item)))
                            (if (and (pair? (car content)) (eq? (caar content) 'term))
                                (begin
                                  (display (cadar content) port)
                                  (display ": " port)
                                  (display (cadr content) port))
                                (display (apply string-append (map ->string content)) port)))
                          (display item port))
                      (newline port))
                    (cdr elem))
          (newline port))

        ((blockquote)
          (newline port)
          (let ((content (cadr elem)))
            ;; Don't wrap in quotes if content already starts with a quote
            (if (and (string? content)
                     (> (string-length content) 0)
                     (char=? (string-ref content 0) #\"))
                (begin
                  (display "    " port)
                  (display content port))
                (begin
                  (display "    \"" port)
                  (display content port)
                  (display "\"" port))))
          (newline port)
          (when (and (pair? (cddr elem)) (eq? (caaddr elem) 'cite))
            (display "        -- " port)
            (display (cadr (caddr elem)) port)
            (newline port))
          (newline port))

        ((table)
          ;; Compute column widths dynamically from content
          (let* ((all-rows (filter pair? (cdr elem)))
                 (cell-lists (map cdr all-rows))
                 (ncols (if (null? cell-lists) 0 (apply max (map length cell-lists)))))
            (when (> ncols 0)
              ;; Calculate max width for each column
              (let ((widths (let loop ((rows cell-lists) (widths (make-list ncols 0)))
                              (if (null? rows)
                                  widths
                                  (let* ((row (car rows))
                                         (padded-row (append (map ->string row)
                                                            (make-list (- ncols (length row)) ""))))
                                    (loop (cdr rows)
                                          (map (lambda (w c) (max w (string-length c)))
                                               widths padded-row)))))))
                (newline port)
                (for-each (lambda (row)
                            (when (pair? row)
                              (display "  " port)
                              (let ((cells (map ->string (cdr row))))
                                (for-each (lambda (cell width i)
                                            (display (string-pad-right cell (+ width 2)) port))
                                          cells
                                          (take widths (length cells))
                                          (iota (length cells))))
                              (newline port)))
                          all-rows)
                (newline port)))))

        ((link)
          ;; (link "url" "text") - in txt, show text with URL
          (display (caddr elem) port)
          (display " <" port)
          (display (cadr elem) port)
          (display ">" port)
          (newline port))

        ((code)
          ;; Code blocks - may have optional language tag
          (let ((content (if (and (pair? (cdr elem))
                                  (symbol? (cadr elem)))
                             (caddr elem)  ; (code lang "...")
                             (cadr elem)))) ; (code "...")
            (newline port)
            (for-each (lambda (line)
                        (display "    " port)
                        (display line port)
                        (newline port))
                      (string-split content "\n"))
            (newline port)))

        ((diagram)
          (newline port)
          (display "    [Diagram]" port)
          (newline port)
          (newline port))

        ((references)
          (for-each (lambda (ref)
                      (when (and (pair? ref) (eq? (car ref) 'ref))
                        (display (format "  [~a, ~a] ~a~%"
                                         (cadr ref) (caddr ref) (cadddr ref)) port)))
                    (cdr elem))
          (newline port))

        ((footer sig) #f)  ; Skip in body

        (else #f)))))

(define (->string x)
  (cond ((string? x) x)
        ((symbol? x) (symbol->string x))
        ((number? x) (number->string x))
        (else "")))

(define (get-field doc field default)
  "Get field from doc, or default if missing."
  (let ((entry (assq field (cdr doc))))
    (if entry (cadr entry) default)))

(define (doc-type doc)
  "Return document type: 'rfc or 'document."
  (if (pair? doc) (car doc) 'unknown))

(define (rfc->txt doc filename)
  "Convert RFC or document S-expression to plain text."
  (call-with-output-file filename
    (lambda (port)
      (let ((is-rfc (eq? (doc-type doc) 'rfc))
            (num (get-field doc 'number 0))
            (title (get-field doc 'title "Untitled"))
            (subtitle (get-field doc 'subtitle #f))
            (status (get-field doc 'status #f))
            (date (get-field doc 'date ""))
            (author (assq 'author (cdr doc))))

        ;; Header
        (if is-rfc
            (display (format "RFC-~a: ~a~%" (zero-pad num 3) title) port)
            (display (format "~a~%" title) port))
        (when subtitle
          (display (format "~a~%" subtitle) port))
        (newline port)
        (when status
          (display (format "Status: ~a~%" status) port))
        (when (and date (not (string-null? date)))
          (display (format "Date: ~a~%" date) port))
        (when author
          (display (format "Author: ~a <~a>~%" (cadr author) (caddr author)) port))
        (newline port)
        (display (txt-hr) port)
        (newline port)

        ;; Abstract
        (let ((abstract (assq 'abstract (cdr doc))))
          (when abstract
            (newline port)
            (display "ABSTRACT" port) (newline port)
            (newline port)
            (for-each (lambda (e) (txt-emit-element e port 0)) (cdr abstract))))

        ;; Body
        (for-each (lambda (elem)
                    (when (and (pair? elem) (eq? (car elem) 'section))
                      (txt-emit-element elem port 0)))
                  (cdr doc))

        ;; Footer
        (display (txt-hr) port)
        (newline port)
        (let ((footer (assq 'footer (cdr doc))))
          (when footer
            (for-each (lambda (e) (txt-emit-element e port 0)) (cdr footer))))))))

;;; ============================================================
;;; HTML Output
;;; ============================================================

(define (html-escape str)
  (let ((str (string-translate* str '(("&" . "&amp;") ("<" . "&lt;") (">" . "&gt;")))))
    str))

(define (html-emit-element elem port)
  (cond
    ((string? elem) (display (html-escape elem) port))
    ((not (pair? elem)) #f)
    (else
      (case (car elem)
        ((p)
          (display "<p>" port)
          (for-each (lambda (e) (html-emit-element e port)) (cdr elem))
          (display "</p>\n" port))

        ((section)
          (display (format "<h2>~a</h2>\n" (html-escape (cadr elem))) port)
          (for-each (lambda (e) (html-emit-element e port)) (cddr elem)))

        ((subsection)
          (display (format "<h3>~a</h3>\n" (html-escape (cadr elem))) port)
          (for-each (lambda (e) (html-emit-element e port)) (cddr elem)))

        ((list)
          (display "<ul>\n" port)
          (for-each (lambda (item)
                      (display "<li>" port)
                      (if (and (pair? item) (eq? (car item) 'item))
                          (let ((content (cdr item)))
                            (if (and (pair? (car content)) (eq? (caar content) 'term))
                                (begin
                                  (display "<strong>" port)
                                  (display (html-escape (cadar content)) port)
                                  (display "</strong>: " port)
                                  (display (html-escape (cadr content)) port))
                                (for-each (lambda (e) (html-emit-element e port)) content)))
                          (html-emit-element item port))
                      (display "</li>\n" port))
                    (cdr elem))
          (display "</ul>\n" port))

        ((blockquote)
          (display "<blockquote>\n<p>" port)
          (display (html-escape (cadr elem)) port)
          (display "</p>\n" port)
          (when (and (pair? (cddr elem)) (pair? (caddr elem)) (eq? (caaddr elem) 'cite))
            (display "<footer>— " port)
            (display (html-escape (cadr (caddr elem))) port)
            (display "</footer>\n" port))
          (display "</blockquote>\n" port))

        ((table)
          (display "<table>\n" port)
          (for-each (lambda (row)
                      (when (pair? row)
                        (let ((tag (if (eq? (car row) 'header) "th" "td")))
                          (display "<tr>" port)
                          (for-each (lambda (cell)
                                      (display (format "<~a>~a</~a>" tag (html-escape (->string cell)) tag) port))
                                    (cdr row))
                          (display "</tr>\n" port))))
                    (cdr elem))
          (display "</table>\n" port))

        ((code)
          ;; Code blocks - may have optional language tag
          (let* ((has-lang (and (pair? (cdr elem)) (symbol? (cadr elem))))
                 (lang (if has-lang (symbol->string (cadr elem)) ""))
                 (content (if has-lang (caddr elem) (cadr elem))))
            (display (format "<pre~a>\n"
                           (if (string-null? lang)
                               ""
                               (format " class=\"language-~a\"" lang))) port)
            (display (html-escape content) port)
            (display "\n</pre>\n" port)))

        ((diagram)
          (display "<pre class=\"diagram\">\n" port)
          ;; TODO: render diagram as ASCII art or SVG
          (display "[Diagram]\n" port)
          (display "</pre>\n" port))

        ((references)
          (display "<ul class=\"references\">\n" port)
          (for-each (lambda (ref)
                      (when (and (pair? ref) (eq? (car ref) 'ref))
                        (display (format "<li><strong>~a (~a)</strong>: ~a</li>\n"
                                         (html-escape (->string (cadr ref)))
                                         (caddr ref)
                                         (html-escape (cadddr ref))) port)))
                    (cdr elem))
          (display "</ul>\n" port))

        ((footer)
          (display "<footer>\n" port)
          (for-each (lambda (e) (html-emit-element e port)) (cdr elem))
          (display "</footer>\n" port))

        ((sig)
          (display (format "<p class=\"sig\">— ~a, ~a</p>\n"
                           (html-escape (cadr elem))
                           (html-escape (caddr elem))) port))

        ((link)
          ;; (link "url" "text") - hyperlink
          (display (format "<p><a href=\"~a\">~a</a></p>\n"
                           (html-escape (cadr elem))
                           (html-escape (caddr elem))) port))

        (else #f)))))

(define (rfc->html doc filename)
  "Convert RFC or document S-expression to HTML."
  (call-with-output-file filename
    (lambda (port)
      (let ((is-rfc (eq? (doc-type doc) 'rfc))
            (num (get-field doc 'number 0))
            (title (get-field doc 'title "Untitled"))
            (subtitle (get-field doc 'subtitle #f))
            (status (get-field doc 'status #f))
            (date (get-field doc 'date ""))
            (author (assq 'author (cdr doc))))

        ;; HTML header
        (display "<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n" port)
        (display "  <meta charset=\"UTF-8\">\n" port)
        (if is-rfc
            (display (format "  <title>RFC-~a: ~a</title>\n" (zero-pad num 3) (html-escape title)) port)
            (display (format "  <title>~a</title>\n" (html-escape title)) port))
        (display "  <link rel=\"stylesheet\" href=\"rfc.css\">\n" port)
        (display "</head>\n<body>\n" port)

        ;; Title block
        (if is-rfc
            (display (format "<h1>RFC-~a: ~a</h1>\n" (zero-pad num 3) (html-escape title)) port)
            (display (format "<h1>~a</h1>\n" (html-escape title)) port))
        (when subtitle
          (display (format "<p class=\"subtitle\"><em>~a</em></p>\n" (html-escape subtitle)) port))
        (display "<dl class=\"metadata\">\n" port)
        (when status
          (display (format "  <dt>Status</dt><dd>~a</dd>\n" status) port))
        (when (and date (not (string-null? date)))
          (display (format "  <dt>Date</dt><dd>~a</dd>\n" date) port))
        (when author
          (display (format "  <dt>Author</dt><dd>~a &lt;~a&gt;</dd>\n"
                           (html-escape (->string (cadr author)))
                           (html-escape (->string (caddr author)))) port))
        (display "</dl>\n<hr>\n" port)

        ;; Abstract
        (let ((abstract (assq 'abstract (cdr doc))))
          (when abstract
            (display "<section class=\"abstract\">\n<h2>Abstract</h2>\n" port)
            (for-each (lambda (e) (html-emit-element e port)) (cdr abstract))
            (display "</section>\n" port)))

        ;; Body sections
        (for-each (lambda (elem)
                    (when (and (pair? elem) (eq? (car elem) 'section))
                      (display "<section>\n" port)
                      (html-emit-element elem port)
                      (display "</section>\n" port)))
                  (cdr doc))

        ;; Footer
        (let ((footer (assq 'footer (cdr doc))))
          (when footer
            (html-emit-element footer port)))

        (display "</body>\n</html>\n" port)))))

;;; ============================================================
;;; PostScript Output (via groff ms macros)
;;; ============================================================

(define (ms-escape str)
  (string-translate* str '(("\\" . "\\e") ("." . "\\&."))))

(define (ms-emit-element elem port)
  (cond
    ((string? elem) (display (ms-escape elem) port))
    ((not (pair? elem)) #f)
    (else
      (case (car elem)
        ((p)
          (display ".LP\n" port)
          (for-each (lambda (e) (ms-emit-element e port)) (cdr elem))
          (newline port))

        ((section)
          (display (format ".NH 1\n~a\n" (ms-escape (cadr elem))) port)
          (for-each (lambda (e) (ms-emit-element e port)) (cddr elem)))

        ((subsection)
          (display (format ".NH 2\n~a\n" (ms-escape (cadr elem))) port)
          (for-each (lambda (e) (ms-emit-element e port)) (cddr elem)))

        ((list)
          (for-each (lambda (item)
                      (display ".IP \\(bu 2\n" port)
                      (if (and (pair? item) (eq? (car item) 'item))
                          (let ((content (cdr item)))
                            (if (and (pair? (car content)) (eq? (caar content) 'term))
                                (begin
                                  (display "\\fB" port)
                                  (display (ms-escape (cadar content)) port)
                                  (display "\\fP: " port)
                                  (display (ms-escape (cadr content)) port))
                                (for-each (lambda (e) (ms-emit-element e port)) content)))
                          (ms-emit-element item port))
                      (newline port))
                    (cdr elem))
          (display ".LP\n" port))

        ((blockquote)
          (display ".QP\n" port)
          (display (ms-escape (cadr elem)) port)
          (newline port)
          (when (and (pair? (cddr elem)) (pair? (caddr elem)) (eq? (caaddr elem) 'cite))
            (display ".RS\n\\(em " port)
            (display (ms-escape (cadr (caddr elem))) port)
            (display "\n.RE\n" port))
          (display ".LP\n" port))

        ((table)
          ;; Find header and data rows
          (let* ((rows (cdr elem))
                 (header-row (find (lambda (r) (and (pair? r) (eq? (car r) 'header))) rows))
                 (data-rows (filter (lambda (r) (and (pair? r) (eq? (car r) 'row))) rows))
                 (ncols (if header-row (length (cdr header-row)) 3))
                 (col-spec (string-intersperse (make-list ncols "l") " ")))
            (display ".TS\n" port)
            (display "center box;\n" port)
            ;; Header row bold, data rows normal
            (when header-row
              (display (string-intersperse (make-list ncols "cb") " ") port)
              (newline port))
            (display col-spec port)
            (display ".\n" port)
            ;; Emit header
            (when header-row
              (display (string-intersperse
                         (map (lambda (c) (ms-escape (->string c))) (cdr header-row))
                         "\t") port)
              (newline port))
            ;; Emit data rows
            (for-each (lambda (row)
                        (display (string-intersperse
                                   (map (lambda (c) (ms-escape (->string c))) (cdr row))
                                   "\t") port)
                        (newline port))
                      data-rows)
            (display ".TE\n" port)))

        ((code)
          ;; Code blocks - may have optional language tag
          (let ((content (if (and (pair? (cdr elem)) (symbol? (cadr elem)))
                             (caddr elem)
                             (cadr elem))))
            (display ".DS\n.ft CW\n.ps 8\n" port)
            (display (ms-escape content) port)
            (display "\n.ps\n.ft\n.DE\n" port)))

        ((diagram)
          (display ".DS C\n[Diagram]\n.DE\n" port))

        ((references)
          (for-each (lambda (ref)
                      (when (and (pair? ref) (eq? (car ref) 'ref))
                        (display (format ".IP \"[~a, ~a]\" 4\n~a\n"
                                         (ms-escape (->string (cadr ref)))
                                         (caddr ref)
                                         (ms-escape (cadddr ref))) port)))
                    (cdr elem)))

        ((link)
          ;; (link "url" "text") - in PS, show text with URL on next line, left-aligned
          (display (format ".LP\n~a\n.br\n\\fI~a\\fP\n"
                           (ms-escape (caddr elem))
                           (ms-escape (cadr elem))) port))

        ((footer sig) #f)

        (else #f)))))

(define (rfc->ms doc filename)
  "Convert RFC or document S-expression to groff ms macros."
  (call-with-output-file filename
    (lambda (port)
      (let ((is-rfc (eq? (doc-type doc) 'rfc))
            (num (get-field doc 'number 0))
            (title (get-field doc 'title "Untitled"))
            (subtitle (get-field doc 'subtitle #f))
            (status (get-field doc 'status #f))
            (date (get-field doc 'date ""))
            (author (assq 'author (cdr doc))))

        ;; ms preamble
        (display ".nr PS 10\n" port)
        (display ".nr VS 12\n" port)
        (if is-rfc
            (display (format ".ds LH RFC-~a\n" (zero-pad num 3)) port)
            (display ".ds LH\n" port))
        (display ".ds CH\n" port)
        (display ".ds RH \\n%\n" port)

        ;; Title
        (display ".TL\n" port)
        (if is-rfc
            (display (format "RFC-~a: ~a\n" (zero-pad num 3) (ms-escape title)) port)
            (display (format "~a\n" (ms-escape title)) port))
        (when subtitle
          (display (format ".br\n\\fI~a\\fP\n" (ms-escape subtitle)) port))
        (display ".AU\n" port)
        (if author
            (display (format "~a <~a>\n" (cadr author) (caddr author)) port)
            (display "Library of Cyberspace\n" port))
        (display ".AI\n" port)
        (let ((date-str (if (or (not date) (string-null? date)) "2026" date)))
          (if status
              (display (format "~a \\(em ~a\n" date-str status) port)
              (display (format "~a\n" date-str) port)))
        (display ".AB\n" port)

        ;; Abstract
        (let ((abstract (assq 'abstract (cdr doc))))
          (when abstract
            (for-each (lambda (e)
                        (when (and (pair? e) (eq? (car e) 'p))
                          (for-each (lambda (x) (ms-emit-element x port)) (cdr e))))
                      (cdr abstract))))
        (display "\n.AE\n" port)

        ;; Body
        (for-each (lambda (elem)
                    (when (and (pair? elem) (eq? (car elem) 'section))
                      (ms-emit-element elem port)))
                  (cdr doc))

        ;; Footer
        (let ((footer (assq 'footer (cdr doc))))
          (when footer
            (display ".SH\nColophon\n" port)
            (for-each (lambda (e) (ms-emit-element e port)) (cdr footer))))))))

(define (rfc->ps doc filename)
  "Convert RFC S-expression to PostScript via groff."
  (let ((ms-file (string-append filename ".ms")))
    (rfc->ms doc ms-file)
    (system (format "groff -t -ms -Tps ~a > ~a" ms-file filename))
    (delete-file ms-file)))

;;; ============================================================
;;; Batch Processing
;;; ============================================================

(define (rfc-generate src-file)
  "Generate all formats from an RFC source file."
  (let* ((base (pathname-strip-extension src-file))
         (doc (read-rfc src-file)))
    (rfc->txt doc (string-append base ".txt"))
    (rfc->html doc (string-append base ".html"))
    (rfc->ps doc (string-append base ".ps"))
    (print "Generated: " base ".{txt,html,ps}")))

;; Example usage:
;; (rfc-generate "rfc-000-declaration.scm")
