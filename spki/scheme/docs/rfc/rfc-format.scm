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

(define *txt-width* 78)
(define *txt-indent* 0)

(define (txt-hr)
  (make-string *txt-width* #\-))

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
                (loop words indent-str (cons line lines))
                (loop (cdr words) new-line lines)))))))

(define (txt-emit-p text port indent)
  (for-each (lambda (line)
              (display line port)
              (newline port))
            (txt-wrap text *txt-width* indent))
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
          (display "    \"" port)
          (display (cadr elem) port)
          (display "\"" port)
          (newline port)
          (when (and (pair? (cddr elem)) (eq? (caaddr elem) 'cite))
            (display "        -- " port)
            (display (cadr (caddr elem)) port)
            (newline port))
          (newline port))

        ((table)
          (newline port)
          (for-each (lambda (row)
                      (when (pair? row)
                        (display "  " port)
                        (for-each (lambda (cell)
                                    (display (string-pad-right (->string cell) 20) port))
                                  (cdr row))
                        (newline port)))
                    (cdr elem))
          (newline port))

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

(define (rfc->txt doc filename)
  "Convert RFC S-expression to plain text."
  (call-with-output-file filename
    (lambda (port)
      (let ((num (cadr (assq 'number (cdr doc))))
            (title (cadr (assq 'title (cdr doc))))
            (status (cadr (assq 'status (cdr doc))))
            (date (cadr (assq 'date (cdr doc))))
            (author (assq 'author (cdr doc))))

        ;; Header
        (display (format "RFC-~a: ~a~%" (zero-pad num 3) title) port)
        (newline port)
        (display (format "Status: ~a~%" status) port)
        (display (format "Date: ~a~%" date) port)
        (display (format "Author: ~a <~a>~%" (cadr author) (caddr author)) port)
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

        (else #f)))))

(define (rfc->html doc filename)
  "Convert RFC S-expression to HTML."
  (call-with-output-file filename
    (lambda (port)
      (let ((num (cadr (assq 'number (cdr doc))))
            (title (cadr (assq 'title (cdr doc))))
            (status (cadr (assq 'status (cdr doc))))
            (date (cadr (assq 'date (cdr doc))))
            (author (assq 'author (cdr doc))))

        ;; HTML header
        (display "<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n" port)
        (display "  <meta charset=\"UTF-8\">\n" port)
        (display (format "  <title>RFC-~a: ~a</title>\n" (zero-pad num 3) (html-escape title)) port)
        (display "  <link rel=\"stylesheet\" href=\"rfc.css\">\n" port)
        (display "</head>\n<body>\n" port)

        ;; Title block
        (display (format "<h1>RFC-~a: ~a</h1>\n" (zero-pad num 3) (html-escape title)) port)
        (display "<dl class=\"metadata\">\n" port)
        (display (format "  <dt>Status</dt><dd>~a</dd>\n" status) port)
        (display (format "  <dt>Date</dt><dd>~a</dd>\n" date) port)
        (display (format "  <dt>Author</dt><dd>~a &lt;~a&gt;</dd>\n"
                         (html-escape (cadr author))
                         (html-escape (caddr author))) port)
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
          (display ".TS\n" port)
          (display "center box;\n" port)
          (display "l l l.\n" port)
          (for-each (lambda (row)
                      (when (pair? row)
                        (display (string-intersperse
                                   (map (lambda (c) (ms-escape (->string c))) (cdr row))
                                   "\t") port)
                        (newline port)))
                    (cdr elem))
          (display ".TE\n" port))

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

        ((footer sig) #f)

        (else #f)))))

(define (rfc->ms doc filename)
  "Convert RFC S-expression to groff ms macros."
  (call-with-output-file filename
    (lambda (port)
      (let ((num (cadr (assq 'number (cdr doc))))
            (title (cadr (assq 'title (cdr doc))))
            (status (cadr (assq 'status (cdr doc))))
            (date (cadr (assq 'date (cdr doc))))
            (author (assq 'author (cdr doc))))

        ;; ms preamble
        (display ".nr PS 10\n" port)
        (display ".nr VS 12\n" port)
        (display (format ".ds LH RFC-~a\n" (zero-pad num 3)) port)
        (display ".ds CH\n" port)
        (display ".ds RH \\n%\n" port)

        ;; Title
        (display ".TL\n" port)
        (display (format "RFC-~a: ~a\n" (zero-pad num 3) (ms-escape title)) port)
        (display ".AU\n" port)
        (display (format "~a <~a>\n" (cadr author) (caddr author)) port)
        (display ".AI\n" port)
        (display (format "~a \\(em ~a\n" date status) port)
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
    (system (format "groff -ms -Tps ~a > ~a" ms-file filename))
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
