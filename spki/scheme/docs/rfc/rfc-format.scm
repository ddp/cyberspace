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
        (chicken irregex)
        srfi-1
        srfi-13)

;;; ============================================================
;;; Box-Drawing to SVG Conversion
;;; ============================================================
;;; Browsers don't render box-drawing characters at proper monospace
;;; widths. This converts them to SVG at generation time.

;; Box-drawing character detection using regex for UTF-8 strings
;; Chicken's string->list returns UTF-8 bytes, not codepoints
;; So we use irregex for detection
(define box-char-pattern
  (irregex "[\u2500-\u257F\u2580-\u259F\u2190-\u21FF\u2200-\u22FF]"))

(define (string-has-box-chars? str)
  "Check if string contains box-drawing/arrow/math characters."
  (and (irregex-search box-char-pattern str) #t))

;; Helper for 5th element access
(define (cddddr x) (cdr (cdddr x)))

;; UTF-8 decoding helper
;; Returns list of (codepoint . char-string) pairs
(define (utf8-chars str)
  "Extract Unicode characters from UTF-8 string as (codepoint . char-string) pairs."
  (let ((bytes (map char->integer (string->list str))))
    (let loop ((bytes bytes) (result '()))
      (if (null? bytes)
          (reverse result)
          (let ((b0 (car bytes)))
            (cond
              ;; ASCII (0xxxxxxx)
              ((< b0 128)
               (loop (cdr bytes)
                     (cons (cons b0 (string (integer->char b0))) result)))
              ;; 2-byte (110xxxxx 10xxxxxx)
              ((and (>= b0 192) (< b0 224) (>= (length bytes) 2))
               (let* ((b1 (cadr bytes))
                      (cp (+ (* (- b0 192) 64) (- b1 128)))
                      (s (list->string (map integer->char (list b0 b1)))))
                 (loop (cddr bytes) (cons (cons cp s) result))))
              ;; 3-byte (1110xxxx 10xxxxxx 10xxxxxx)
              ((and (>= b0 224) (< b0 240) (>= (length bytes) 3))
               (let* ((b1 (cadr bytes))
                      (b2 (caddr bytes))
                      (cp (+ (* (- b0 224) 4096) (* (- b1 128) 64) (- b2 128)))
                      (s (list->string (map integer->char (list b0 b1 b2)))))
                 (loop (cdddr bytes) (cons (cons cp s) result))))
              ;; 4-byte (11110xxx 10xxxxxx 10xxxxxx 10xxxxxx)
              ((and (>= b0 240) (>= (length bytes) 4))
               (let* ((b1 (cadr bytes))
                      (b2 (caddr bytes))
                      (b3 (cadddr bytes))
                      (cp (+ (* (- b0 240) 262144) (* (- b1 128) 4096) (* (- b2 128) 64) (- b3 128)))
                      (s (list->string (map integer->char (list b0 b1 b2 b3)))))
                 (loop (cddddr bytes) (cons (cons cp s) result))))
              ;; Invalid - skip byte
              (else
               (loop (cdr bytes) result))))))))

;; Character cell dimensions (in SVG units)
(define cell-width 9.6)   ; Width of monospace char
(define cell-height 19.2) ; Height including line spacing

;; Convert box character codepoint to SVG path segments
;; Returns list of (type x1 y1 x2 y2) where type is 'line or 'text
(define (codepoint->svg cp cx cy)
  "Convert a codepoint at grid position to SVG elements.
   cx, cy are center coordinates of the cell."
  (let ((hw (/ cell-width 2))    ; half width
        (hh (/ cell-height 2)))  ; half height
    (cond
      ;; Horizontal lines: ─ (2500), ═ (2550)
      ((or (= cp #x2500) (= cp #x2550))
       `((line ,(- cx hw) ,cy ,(+ cx hw) ,cy)))

      ;; Vertical lines: │ (2502), ║ (2551)
      ((or (= cp #x2502) (= cp #x2551))
       `((line ,cx ,(- cy hh) ,cx ,(+ cy hh))))

      ;; Top-left corners: ┌ (250C), ╭ (256D), ╔ (2554)
      ((or (= cp #x250C) (= cp #x256D) (= cp #x2554))
       `((line ,cx ,cy ,(+ cx hw) ,cy)
         (line ,cx ,cy ,cx ,(+ cy hh))))

      ;; Top-right corners: ┐ (2510), ╮ (256E), ╗ (2557)
      ((or (= cp #x2510) (= cp #x256E) (= cp #x2557))
       `((line ,(- cx hw) ,cy ,cx ,cy)
         (line ,cx ,cy ,cx ,(+ cy hh))))

      ;; Bottom-left corners: └ (2514), ╰ (2570), ╚ (255A)
      ((or (= cp #x2514) (= cp #x2570) (= cp #x255A))
       `((line ,cx ,cy ,(+ cx hw) ,cy)
         (line ,cx ,(- cy hh) ,cx ,cy)))

      ;; Bottom-right corners: ┘ (2518), ╯ (256F), ╝ (255D)
      ((or (= cp #x2518) (= cp #x256F) (= cp #x255D))
       `((line ,(- cx hw) ,cy ,cx ,cy)
         (line ,cx ,(- cy hh) ,cx ,cy)))

      ;; T-junctions
      ((= cp #x251C)  ; ├
       `((line ,cx ,(- cy hh) ,cx ,(+ cy hh))
         (line ,cx ,cy ,(+ cx hw) ,cy)))
      ((= cp #x2524)  ; ┤
       `((line ,cx ,(- cy hh) ,cx ,(+ cy hh))
         (line ,(- cx hw) ,cy ,cx ,cy)))
      ((= cp #x252C)  ; ┬
       `((line ,(- cx hw) ,cy ,(+ cx hw) ,cy)
         (line ,cx ,cy ,cx ,(+ cy hh))))
      ((= cp #x2534)  ; ┴
       `((line ,(- cx hw) ,cy ,(+ cx hw) ,cy)
         (line ,cx ,(- cy hh) ,cx ,cy)))

      ;; Cross: ┼ (253C)
      ((= cp #x253C)
       `((line ,(- cx hw) ,cy ,(+ cx hw) ,cy)
         (line ,cx ,(- cy hh) ,cx ,(+ cy hh))))

      ;; Arrows - render as SVG text
      ((or (= cp #x2192) (= cp #x25BA) (= cp #x25B6))  ; → ► ▶
       `((text ,cx ,cy "→")))
      ((or (= cp #x2190) (= cp #x25C0))  ; ← ◀
       `((text ,cx ,cy "←")))
      ((or (= cp #x2191) (= cp #x25B2))  ; ↑ ▲
       `((text ,cx ,cy "↑")))
      ((or (= cp #x2193) (= cp #x25BC))  ; ↓ ▼
       `((text ,cx ,cy "↓")))

      ;; Block elements
      ((= cp #x2588) `((rect ,(- cx hw) ,(- cy hh) ,cell-width ,cell-height 1.0)))       ; █
      ((= cp #x2587) `((rect ,(- cx hw) ,(- cy (* hh 0.75)) ,cell-width ,(* cell-height 0.875) 1.0)))
      ((= cp #x2586) `((rect ,(- cx hw) ,(- cy (* hh 0.5)) ,cell-width ,(* cell-height 0.75) 1.0)))
      ((= cp #x2585) `((rect ,(- cx hw) ,(- cy (* hh 0.25)) ,cell-width ,(* cell-height 0.625) 1.0)))
      ((= cp #x2584) `((rect ,(- cx hw) ,cy ,cell-width ,(* cell-height 0.5) 1.0)))      ; ▄
      ((= cp #x2583) `((rect ,(- cx hw) ,(+ cy (* hh 0.25)) ,cell-width ,(* cell-height 0.375) 1.0)))
      ((= cp #x2582) `((rect ,(- cx hw) ,(+ cy (* hh 0.5)) ,cell-width ,(* cell-height 0.25) 1.0)))
      ((= cp #x2581) `((rect ,(- cx hw) ,(+ cy (* hh 0.75)) ,cell-width ,(* cell-height 0.125) 1.0)))

      ;; Math symbols - render as text
      ((= cp #x2205) `((text ,cx ,cy "∅")))  ; ∅

      (else '()))))  ; Unknown box char - skip

(define (text->svg-diagram text)
  "Convert multi-line text with box-drawing to SVG string."
  (let* ((lines (string-split text "\n" #t))
         ;; Parse each line into Unicode chars (codepoint . char-string)
         (parsed-lines (map utf8-chars lines))
         (nrows (length lines))
         (ncols (apply max 1 (map length parsed-lines)))
         (width (* ncols cell-width))
         (height (* nrows cell-height))
         (svg-lines '())
         (svg-texts '()))

    ;; Process each character
    (let loop-rows ((parsed-lines parsed-lines) (row 0))
      (when (pair? parsed-lines)
        (let ((chars (car parsed-lines)))  ; list of (codepoint . char-string)
          (let loop-cols ((chars chars) (col 0))
            (when (pair? chars)
              (let* ((char-pair (car chars))
                     (cp (car char-pair))
                     (char-str (cdr char-pair))
                     (cx (+ (* col cell-width) (/ cell-width 2)))
                     (cy (+ (* row cell-height) (/ cell-height 2)))
                     (elems (codepoint->svg cp cx cy)))
                (if (null? elems)
                    ;; Regular character - emit as text if not space
                    (when (not (= cp 32))  ; space
                      (set! svg-texts
                            (cons (format "<text x=\"~a\" y=\"~a\" text-anchor=\"middle\" dominant-baseline=\"central\">~a</text>"
                                         cx cy (html-escape char-str))
                                  svg-texts)))
                    ;; Box character - emit SVG elements
                    (for-each
                      (lambda (elem)
                        (case (car elem)
                          ((line)
                           (set! svg-lines
                                 (cons (format "<line x1=\"~a\" y1=\"~a\" x2=\"~a\" y2=\"~a\"/>"
                                              (cadr elem) (caddr elem)
                                              (cadddr elem) (car (cddddr elem)))
                                       svg-lines)))
                          ((text)
                           (set! svg-texts
                                 (cons (format "<text x=\"~a\" y=\"~a\" text-anchor=\"middle\" dominant-baseline=\"central\">~a</text>"
                                              (cadr elem) (caddr elem) (cadddr elem))
                                       svg-texts)))
                          ((rect)
                           (set! svg-lines
                                 (cons (format "<rect x=\"~a\" y=\"~a\" width=\"~a\" height=\"~a\" fill=\"currentColor\" opacity=\"~a\"/>"
                                              (cadr elem) (caddr elem)
                                              (cadddr elem) (car (cddddr elem))
                                              (cadr (cddddr elem)))
                                       svg-lines)))))
                      elems)))
              (loop-cols (cdr chars) (+ col 1)))))
        (loop-rows (cdr parsed-lines) (+ row 1))))

    ;; Build SVG
    (string-append
      (format "<svg class=\"diagram\" viewBox=\"0 0 ~a ~a\" width=\"~a\" height=\"~a\" xmlns=\"http://www.w3.org/2000/svg\">\n"
              width height width height)
      "<style>\n"
      "  line { stroke: currentColor; stroke-width: 1.5; stroke-linecap: round; }\n"
      "  text { font-family: 'Hack', 'SF Mono', monospace; font-size: 14px; fill: currentColor; }\n"
      "</style>\n"
      (string-intersperse (reverse svg-lines) "\n")
      "\n"
      (string-intersperse (reverse svg-texts) "\n")
      "\n</svg>")))

;; ASCII conversion for text output (using codepoints)
(define (codepoint->ascii cp)
  "Convert codepoint to ASCII equivalent character."
  (cond
    ;; Horizontal lines: ─ ═
    ((or (= cp #x2500) (= cp #x2550)) "-")
    ;; Vertical lines: │ ║
    ((or (= cp #x2502) (= cp #x2551)) "|")
    ;; Corners and T-junctions: all become +
    ((and (>= cp #x250C) (<= cp #x254B)) "+")
    ((and (>= cp #x2554) (<= cp #x256C)) "+")
    ((and (>= cp #x256D) (<= cp #x2570)) "+")
    ;; Arrows
    ((or (= cp #x2192) (= cp #x25BA) (= cp #x25B6)) ">")  ; → ► ▶
    ((or (= cp #x2190) (= cp #x25C0) (= cp #x25C4)) "<")  ; ← ◀ ◄
    ((or (= cp #x2191) (= cp #x25B2)) "^")                ; ↑ ▲
    ((or (= cp #x2193) (= cp #x25BC)) "v")                ; ↓ ▼
    ;; Block elements - use # for filled
    ((and (>= cp #x2581) (<= cp #x2588)) "#")
    ;; Math: ∅
    ((= cp #x2205) "0")
    (else #f)))  ; Return #f for non-box chars

(define (text->ascii text)
  "Convert box-drawing characters in text to ASCII."
  (apply string-append
    (map (lambda (char-pair)
           (let ((cp (car char-pair))
                 (char-str (cdr char-pair)))
             (or (codepoint->ascii cp) char-str)))
         (utf8-chars text))))

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
;;; Text Output (Plain ASCII, 72 columns per RFC tradition)
;;; ============================================================

(define txt-width 72)
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
            (txt-wrap (text->ascii text) txt-width indent))
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
                                  (display (text->ascii (cadar content)) port)
                                  (display ": " port)
                                  (display (text->ascii (cadr content)) port))
                                (display (text->ascii (apply string-append (map ->string content))) port)))
                          (display (text->ascii (->string item)) port))
                      (newline port))
                    (cdr elem))
          (newline port))

        ((blockquote)
          (newline port)
          (let ((content (text->ascii (cadr elem))))
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
                              (let ((cells (map (lambda (c) (text->ascii (->string c))) (cdr row))))
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
          ;; Convert box-drawing to ASCII for plain text output
          (let* ((raw-content (if (and (pair? (cdr elem))
                                       (symbol? (cadr elem)))
                                  (caddr elem)  ; (code lang "...")
                                  (cadr elem))) ; (code "...")
                 (content (text->ascii raw-content)))
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
          ;; If content has box-drawing chars, render as SVG for proper alignment
          (let* ((has-lang (and (pair? (cdr elem)) (symbol? (cadr elem))))
                 (lang (if has-lang (symbol->string (cadr elem)) ""))
                 (content (if has-lang (caddr elem) (cadr elem))))
            (if (string-has-box-chars? content)
                ;; Box-drawing detected - render as SVG
                (begin
                  (display "<div class=\"diagram-container\">\n" port)
                  (display (text->svg-diagram content) port)
                  (display "\n</div>\n" port))
                ;; Regular code - use pre
                (begin
                  (display (format "<pre~a>\n"
                                 (if (string-null? lang)
                                     ""
                                     (format " class=\"language-~a\"" lang))) port)
                  (display (html-escape content) port)
                  (display "\n</pre>\n" port)))))

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
        (display "<!DOCTYPE html>\n<html lang=\"en\" data-theme=\"dark\">\n<head>\n" port)
        (display "  <meta charset=\"UTF-8\">\n" port)
        (if is-rfc
            (display (format "  <title>RFC-~a: ~a</title>\n" (zero-pad num 3) (html-escape title)) port)
            (display (format "  <title>~a</title>\n" (html-escape title)) port))
        (display "  <link rel=\"stylesheet\" href=\"rfc.css\">\n" port)
        (display "</head>\n<body>\n" port)
        ;; Theme toggle
        (display "<span class=\"theme-toggle\" onclick=\"toggleTheme()\" title=\"Toggle light/dark\">[theme]</span>\n" port)

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

        ;; Theme toggle script (supports ?theme=dark|light query param for REPL integration)
        (display "<script>\n" port)
        (display "function toggleTheme() {\n" port)
        (display "  const html = document.documentElement;\n" port)
        (display "  const current = html.getAttribute('data-theme');\n" port)
        (display "  const next = current === 'dark' ? 'light' : 'dark';\n" port)
        (display "  html.setAttribute('data-theme', next);\n" port)
        (display "  localStorage.setItem('theme', next);\n" port)
        (display "}\n" port)
        (display "(function() {\n" port)
        (display "  // Query param override (for REPL: ?theme=dark or ?theme=light)\n" port)
        (display "  const params = new URLSearchParams(window.location.search);\n" port)
        (display "  const param = params.get('theme');\n" port)
        (display "  if (param === 'dark' || param === 'light') {\n" port)
        (display "    document.documentElement.setAttribute('data-theme', param);\n" port)
        (display "    localStorage.setItem('theme', param);\n" port)
        (display "    return;\n" port)
        (display "  }\n" port)
        (display "  // localStorage preference\n" port)
        (display "  const saved = localStorage.getItem('theme');\n" port)
        (display "  if (saved) {\n" port)
        (display "    document.documentElement.setAttribute('data-theme', saved);\n" port)
        (display "  } else if (window.matchMedia('(prefers-color-scheme: light)').matches) {\n" port)
        (display "    document.documentElement.setAttribute('data-theme', 'light');\n" port)
        (display "  }\n" port)
        (display "})();\n" port)
        (display "</script>\n" port)
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
          ;; Convert box-drawing to ASCII for PostScript
          (let* ((raw-content (if (and (pair? (cdr elem)) (symbol? (cadr elem)))
                                  (caddr elem)
                                  (cadr elem)))
                 (content (text->ascii raw-content)))
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
