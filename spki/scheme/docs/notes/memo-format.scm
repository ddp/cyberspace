;; Memo Document Processors
;; S-expression source → txt, ps, html
;;
;; Usage:
;;   (load "memo-format.scm")
;;   (define doc (read-memo "memo-0000-declaration.scm"))
;;   (memo->txt doc "memo-0000-declaration.txt")
;;   (memo->ps doc "memo-0000-declaration.ps")
;;   (memo->html doc "memo-0000-declaration.html")

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
;; Using integers to avoid subpixel rendering artifacts
(define cell-width 10)    ; Width of monospace char
(define cell-height 20)   ; Height including line spacing

;; Convert box character codepoint to SVG path segments
;; Returns list of (type x1 y1 x2 y2) where type is 'line or 'text
;; Overlap for continuous lines (avoids anti-aliasing gaps)
(define overlap 1)

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
      ;; Extended by overlap to connect with adjacent cells
      ((or (= cp #x2502) (= cp #x2551))
       `((line ,cx ,(- cy hh overlap) ,cx ,(+ cy hh overlap))))

      ;; Top-left corners: ┌ (250C), ╭ (256D), ╔ (2554)
      ((or (= cp #x250C) (= cp #x256D) (= cp #x2554))
       `((line ,cx ,cy ,(+ cx hw) ,cy)
         (line ,cx ,cy ,cx ,(+ cy hh overlap))))

      ;; Top-right corners: ┐ (2510), ╮ (256E), ╗ (2557)
      ((or (= cp #x2510) (= cp #x256E) (= cp #x2557))
       `((line ,(- cx hw) ,cy ,cx ,cy)
         (line ,cx ,cy ,cx ,(+ cy hh overlap))))

      ;; Bottom-left corners: └ (2514), ╰ (2570), ╚ (255A)
      ((or (= cp #x2514) (= cp #x2570) (= cp #x255A))
       `((line ,cx ,cy ,(+ cx hw) ,cy)
         (line ,cx ,(- cy hh overlap) ,cx ,cy)))

      ;; Bottom-right corners: ┘ (2518), ╯ (256F), ╝ (255D)
      ((or (= cp #x2518) (= cp #x256F) (= cp #x255D))
       `((line ,(- cx hw) ,cy ,cx ,cy)
         (line ,cx ,(- cy hh overlap) ,cx ,cy)))

      ;; T-junctions
      ((= cp #x251C)  ; ├
       `((line ,cx ,(- cy hh overlap) ,cx ,(+ cy hh overlap))
         (line ,cx ,cy ,(+ cx hw) ,cy)))
      ((= cp #x2524)  ; ┤
       `((line ,cx ,(- cy hh overlap) ,cx ,(+ cy hh overlap))
         (line ,(- cx hw) ,cy ,cx ,cy)))
      ((= cp #x252C)  ; ┬
       `((line ,(- cx hw) ,cy ,(+ cx hw) ,cy)
         (line ,cx ,cy ,cx ,(+ cy hh overlap))))
      ((= cp #x2534)  ; ┴
       `((line ,(- cx hw) ,cy ,(+ cx hw) ,cy)
         (line ,cx ,(- cy hh overlap) ,cx ,cy)))

      ;; Cross: ┼ (253C)
      ((= cp #x253C)
       `((line ,(- cx hw) ,cy ,(+ cx hw) ,cy)
         (line ,cx ,(- cy hh overlap) ,cx ,(+ cy hh overlap))))

      ;; Arrows - render as SVG text
      ((or (= cp #x2192) (= cp #x25BA) (= cp #x25B6))  ; → ► ▶
       `((text ,cx ,cy "→")))
      ((or (= cp #x2190) (= cp #x25C0))  ; ← ◀
       `((text ,cx ,cy "←")))
      ((or (= cp #x2191) (= cp #x25B2))  ; ↑ ▲
       `((text ,cx ,cy "↑")))
      ((or (= cp #x2193) (= cp #x25BC))  ; ↓ ▼
       `((text ,cx ,cy "↓")))

      ;; Block elements (solid)
      ((= cp #x2588) `((rect ,(- cx hw) ,(- cy hh) ,cell-width ,cell-height 1.0)))       ; █
      ((= cp #x2587) `((rect ,(- cx hw) ,(- cy (* hh 0.75)) ,cell-width ,(* cell-height 0.875) 1.0)))
      ((= cp #x2586) `((rect ,(- cx hw) ,(- cy (* hh 0.5)) ,cell-width ,(* cell-height 0.75) 1.0)))
      ((= cp #x2585) `((rect ,(- cx hw) ,(- cy (* hh 0.25)) ,cell-width ,(* cell-height 0.625) 1.0)))
      ((= cp #x2584) `((rect ,(- cx hw) ,cy ,cell-width ,(* cell-height 0.5) 1.0)))      ; ▄
      ((= cp #x2583) `((rect ,(- cx hw) ,(+ cy (* hh 0.25)) ,cell-width ,(* cell-height 0.375) 1.0)))
      ((= cp #x2582) `((rect ,(- cx hw) ,(+ cy (* hh 0.5)) ,cell-width ,(* cell-height 0.25) 1.0)))
      ((= cp #x2581) `((rect ,(- cx hw) ,(+ cy (* hh 0.75)) ,cell-width ,(* cell-height 0.125) 1.0)))

      ;; Shade characters (with opacity)
      ((= cp #x2591) `((rect ,(- cx hw) ,(- cy hh) ,cell-width ,cell-height 0.25)))      ; ░ light shade
      ((= cp #x2592) `((rect ,(- cx hw) ,(- cy hh) ,cell-width ,cell-height 0.50)))      ; ▒ medium shade
      ((= cp #x2593) `((rect ,(- cx hw) ,(- cy hh) ,cell-width ,cell-height 0.75)))      ; ▓ dark shade

      ;; Math symbols - render as text
      ((= cp #x2205) `((text ,cx ,cy "∅")))  ; ∅

      (else '()))))  ; Unknown box char - skip

(define (utf8-length str)
  "Count Unicode characters in UTF-8 string."
  (length (utf8-chars str)))

(define (codepoint-display-width cp)
  "Return display width of a codepoint (1 or 2 cells).
   Emojis and wide characters take 2 cells in monospace fonts."
  (cond
    ;; Devanagari - base characters ~1.5 cells, use 2 for safety
    ((<= #x0900 cp #x097F) 2)     ; Devanagari
    ((<= #x0980 cp #x09FF) 2)     ; Bengali
    ((<= #x0A00 cp #x0A7F) 2)     ; Gurmukhi
    ((<= #x0A80 cp #x0AFF) 2)     ; Gujarati
    ((<= #x0B00 cp #x0B7F) 2)     ; Oriya
    ((<= #x0B80 cp #x0BFF) 2)     ; Tamil
    ((<= #x0C00 cp #x0C7F) 2)     ; Telugu
    ((<= #x0C80 cp #x0CFF) 2)     ; Kannada
    ((<= #x0D00 cp #x0D7F) 2)     ; Malayalam
    ;; Emoji ranges (commonly used)
    ((<= #x1F300 cp #x1F9FF) 2)   ; Miscellaneous Symbols, Emoticons, etc.
    ((<= #x2600 cp #x26FF) 2)     ; Miscellaneous Symbols
    ((<= #x2700 cp #x27BF) 2)     ; Dingbats
    ;; CJK and other wide characters
    ((<= #x1100 cp #x115F) 2)     ; Hangul Jamo
    ((<= #x2E80 cp #x9FFF) 2)     ; CJK
    ((<= #xAC00 cp #xD7A3) 2)     ; Hangul Syllables
    ((<= #xF900 cp #xFAFF) 2)     ; CJK Compatibility
    ((<= #xFE10 cp #xFE1F) 2)     ; Vertical forms
    ((<= #xFF00 cp #xFF60) 2)     ; Fullwidth forms
    ((<= #x20000 cp #x2FFFF) 2)   ; CJK Extension B+
    (else 1)))

(define (display-width str)
  "Calculate display width of string in monospace character cells."
  (apply + (map (lambda (cp-pair) (codepoint-display-width (car cp-pair)))
                (utf8-chars str))))

(define (string-ends-with-box-edge? str)
  "Check if string ends with a box right edge (│ or ┐ or ┘ or ┤)."
  (let ((chars (utf8-chars str)))
    (and (pair? chars)
         (let ((last-cp (car (last-pair chars))))
           (memv (car last-cp) '(#x2502 #x2510 #x2518 #x2524 #x2551 #x2557 #x255D))))))

(define (fix-box-line-widths lines)
  "Auto-fix box diagram lines to have consistent right-edge alignment.
   Lines ending with box edges are adjusted to match the most common width."
  (let* ((char-counts (map display-width lines))
         ;; Find widths of lines ending with box edges
         (box-edge-info (filter-map
                         (lambda (line count)
                           (and (string-ends-with-box-edge? line)
                                (cons count line)))
                         lines char-counts)))
    (if (null? box-edge-info)
        lines  ; No box edges, nothing to fix
        (let* ((edge-widths (map car box-edge-info))
               ;; Target width = most common width among box-edge lines
               (target-width (let ((counts (map (lambda (w)
                                                  (cons w (count (lambda (x) (= x w)) edge-widths)))
                                                (delete-duplicates edge-widths))))
                               (car (car (sort counts (lambda (a b) (> (cdr a) (cdr b)))))))))
          (map (lambda (line count)
                 (if (not (string-ends-with-box-edge? line))
                     line  ; Not a box-edge line, leave unchanged
                     (let ((diff (- target-width count)))
                       (cond
                         ((= diff 0) line)  ; Already correct
                         ((> diff 0)
                          ;; Need to add spaces before the edge
                          (let* ((chars (utf8-chars line))
                                 (n (length chars))
                                 (last-char (cdr (list-ref chars (- n 1))))
                                 (prefix-strs (map cdr (take chars (- n 1))))
                                 (prefix (apply string-append prefix-strs)))
                            (string-append prefix (make-string diff #\space) last-char)))
                         (else
                          ;; Need to remove spaces before the edge
                          (let* ((chars (utf8-chars line))
                                 (n (length chars))
                                 (last-char (cdr (list-ref chars (- n 1))))
                                 ;; Find and remove trailing spaces before edge
                                 (prefix-chars (take chars (- n 1)))
                                 (to-remove (- diff))  ; positive count of columns to remove
                                 (trimmed (let trim-loop ((cs (reverse prefix-chars))
                                                          (remaining to-remove))
                                            (if (or (null? cs) (<= remaining 0))
                                                (reverse cs)
                                                (if (= (car (car cs)) 32)  ; space
                                                    (trim-loop (cdr cs) (- remaining 1))
                                                    (reverse cs))))))
                            (string-append (apply string-append (map cdr trimmed)) last-char)))))))
               lines char-counts)))))

(define (normalize-box-lines lines)
  "Normalize box diagram lines - fix widths and pad to max."
  (let* ((fixed (fix-box-line-widths lines))
         (char-counts (map display-width fixed))
         (max-len (apply max 1 char-counts)))
    (map (lambda (line count)
           (let ((pad (- max-len count)))
             (if (<= pad 0)
                 line
                 (string-append line (make-string pad #\space)))))
         fixed char-counts)))

(define (box-drawing-codepoint? cp)
  "Check if codepoint is a box-drawing character."
  (or (<= #x2500 cp #x257F)   ; Box Drawing
      (<= #x2580 cp #x259F)   ; Block Elements
      (= cp #x2190) (= cp #x2191) (= cp #x2192) (= cp #x2193)  ; Arrows
      (= cp #x25B2) (= cp #x25B6) (= cp #x25BC) (= cp #x25C0)  ; Triangles
      (= cp #x25BA) (= cp #x25C4)))  ; More triangles

;; SVG diagram rendering - converts box-drawing text to geometric SVG
(define (text->svg-diagram text)
  "Convert text with box-drawing characters to SVG.
   Box characters become geometric primitives (lines/rects).
   Text characters are grouped into spans for proper rendering."
  (let* ((raw-lines (string-split text "\n"))
         ;; Normalize line widths so right box edges align properly
         (lines (normalize-box-lines raw-lines))
         (nrows (length lines))
         (ncols (apply max 1 (map display-width lines)))
         (width (* ncols cell-width))
         (height (* nrows cell-height))
         (elements '()))

    ;; Process each line, grouping consecutive text characters
    (let row-loop ((lines lines) (row 0))
      (when (pair? lines)
        (let* ((line (car lines))
               (chars (utf8-chars line))
               (cy (+ (* row cell-height) (/ cell-height 2))))
          ;; Process chars, accumulating text runs
          (let col-loop ((chars chars) (col 0) (text-run '()) (run-start 0))
            (define (flush-text-run)
              (when (pair? text-run)
                (let* ((text-str (apply string-append (reverse text-run)))
                       (start-x (* run-start cell-width)))
                  (set! elements
                        (append elements
                                `((text-span ,start-x ,cy ,text-str)))))))
            (if (null? chars)
                ;; End of line - flush any pending text
                (flush-text-run)
                (let* ((char-pair (car chars))
                       (cp (car char-pair))
                       (char-str (cdr char-pair))
                       (char-width (codepoint-display-width cp))
                       (cx (+ (* col cell-width) (/ cell-width 2))))
                  (cond
                    ;; Box-drawing character - flush text, emit primitive
                    ((box-drawing-codepoint? cp)
                     (flush-text-run)
                     (let ((prims (codepoint->svg cp cx cy)))
                       (set! elements (append elements prims)))
                     (col-loop (cdr chars) (+ col char-width) '() (+ col char-width)))
                    ;; Space - flush text, skip
                    ((= cp 32)
                     (flush-text-run)
                     (col-loop (cdr chars) (+ col 1) '() (+ col 1)))
                    ;; Regular text character - accumulate (advance by char width)
                    (else
                     (col-loop (cdr chars) (+ col char-width)
                               (cons char-str text-run)
                               (if (null? text-run) col run-start))))))))
        (row-loop (cdr lines) (+ row 1))))

    ;; Build SVG string
    (let ((out (open-output-string)))
      ;; viewBox only - CSS max-width:100% handles scaling
      (display (format "<svg class=\"diagram\" viewBox=\"0 0 ~a ~a\" " width height) out)
      (display "xmlns=\"http://www.w3.org/2000/svg\">\n" out)
      ;; Style for lines and text
      (display "<style>\n" out)
      (display "  .diagram line { stroke: currentColor; stroke-width: 1.5; stroke-linecap: square; }\n" out)
      (display "  .diagram rect { fill: currentColor; }\n" out)
      (display "  .diagram text { font-family: 'JetBrains Mono', monospace; font-size: 14px; fill: currentColor; dominant-baseline: central; }\n" out)
      (display "</style>\n" out)

      ;; Emit elements
      (for-each
       (lambda (elem)
         (case (car elem)
           ((line)
            (let ((x1 (list-ref elem 1))
                  (y1 (list-ref elem 2))
                  (x2 (list-ref elem 3))
                  (y2 (list-ref elem 4)))
              (display (format "<line x1=\"~a\" y1=\"~a\" x2=\"~a\" y2=\"~a\"/>\n"
                               x1 y1 x2 y2) out)))
           ((rect)
            (let ((x (list-ref elem 1))
                  (y (list-ref elem 2))
                  (w (list-ref elem 3))
                  (h (list-ref elem 4))
                  (opacity (if (> (length elem) 5) (list-ref elem 5) 1.0)))
              (if (< opacity 1.0)
                  (display (format "<rect x=\"~a\" y=\"~a\" width=\"~a\" height=\"~a\" fill-opacity=\"~a\"/>\n"
                                   x y w h opacity) out)
                  (display (format "<rect x=\"~a\" y=\"~a\" width=\"~a\" height=\"~a\"/>\n"
                                   x y w h) out))))
           ((text-span)
            (let ((x (list-ref elem 1))
                  (y (list-ref elem 2))
                  (s (list-ref elem 3)))
              ;; Escape text for SVG
              (let ((escaped (string-translate* s '(("&" . "&amp;") ("<" . "&lt;") (">" . "&gt;")))))
                (display (format "<text x=\"~a\" y=\"~a\">~a</text>\n" x y escaped) out))))))
       elements)

      (display "</svg>" out)
      (get-output-string out))))

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
  "Keep Unicode box-drawing characters (browsers render them fine now)."
  text)

;; Memo namespace: 0000-9999 (4 digits)
;; This is the single source of truth for memo number formatting
(define *memo-number-width* 4)

;; Zero-pad a number to width
(define (zero-pad n width)
  (let ((s (number->string n)))
    (string-append (make-string (max 0 (- width (string-length s))) #\0) s)))

;; Format memo number using canonical width
(define (memo-number->string n)
  (zero-pad n *memo-number-width*))

;;; ============================================================
;;; Document Reader
;;; ============================================================

(define (read-memo filename)
  "Read an Memo S-expression from file."
  (with-input-from-file filename read))

;;; ============================================================
;;; Text Output (Plain ASCII, 72 columns per Memo tradition)
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

(define (validate-title title filename)
  (let ((warnings '()))
    (when (irregex-search "\\(" title)
      (set! warnings (cons (format "~a: parentheses: ~a" filename title) warnings)))
    (when (irregex-search "\\b[A-Z]{3,}\\b" title)
      (set! warnings (cons (format "~a: acronym: ~a" filename title) warnings)))
    warnings))

(define (validate-memo doc filename)
  (let ((title (get-field doc 'title #f)))
    (if title
        (validate-title title filename)
        (list (format "~a: missing title" filename)))))

(define (doc-type doc)
  "Return document type: 'memo or 'document."
  (if (pair? doc) (car doc) 'unknown))

(define (memo->txt doc filename)
  "Convert Memo or document S-expression to plain text."
  (call-with-output-file filename
    (lambda (port)
      (let ((is-memo (eq? (doc-type doc) 'memo))
            (num (get-field doc 'number 0))
            (title (get-field doc 'title "Untitled"))
            (subtitle (get-field doc 'subtitle #f))
            (status (get-field doc 'status #f))
            (date (get-field doc 'date ""))
            (author (assq 'author (cdr doc))))

        ;; Header
        (if is-memo
            (display (format "Memo ~a: ~a~%" (memo-number->string num) title) port)
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
          ;; Support (table compact ...) for tight spacing
          (let* ((has-class (and (pair? (cdr elem)) (symbol? (cadr elem))))
                 (class (if has-class (symbol->string (cadr elem)) ""))
                 (rows (if has-class (cddr elem) (cdr elem))))
            (display (if (string-null? class)
                         "<table>\n"
                         (format "<table class=\"~a\">\n" class)) port)
            (for-each (lambda (row)
                        (when (pair? row)
                          (let ((tag (if (eq? (car row) 'header) "th" "td")))
                            (display "<tr>" port)
                            (for-each (lambda (cell)
                                        (display (format "<~a>~a</~a>" tag (html-escape (->string cell)) tag) port))
                                      (cdr row))
                            (display "</tr>\n" port))))
                      rows)
            (display "</table>\n" port)))

        ((code)
          ;; Code blocks - may have optional language tag
          ;; If content has box-drawing chars, render as SVG for proper alignment
          (let* ((has-lang (and (pair? (cdr elem)) (symbol? (cadr elem))))
                 (lang (if has-lang (symbol->string (cadr elem)) ""))
                 (content (if has-lang (caddr elem) (cadr elem))))
            (if (string-has-box-chars? content)
                ;; Box-drawing detected - use pre with diagram class (Unicode renders fine)
                (begin
                  (display "<pre class=\"diagram\">\n" port)
                  (display (html-escape content) port)
                  (display "\n</pre>\n" port))
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

(define (memo->html doc filename)
  "Convert Memo or document S-expression to HTML."
  (call-with-output-file filename
    (lambda (port)
      (let ((is-memo (eq? (doc-type doc) 'memo))
            (num (get-field doc 'number 0))
            (title (get-field doc 'title "Untitled"))
            (subtitle (get-field doc 'subtitle #f))
            (status (get-field doc 'status #f))
            (date (get-field doc 'date ""))
            (author (assq 'author (cdr doc))))

        ;; HTML header
        (display "<!DOCTYPE html>\n<html lang=\"en\" data-theme=\"dark\">\n<head>\n" port)
        (display "  <meta charset=\"UTF-8\">\n" port)
        ;; Embed JetBrains Mono - known good box-drawing alignment
        (display "  <link rel=\"preconnect\" href=\"https://fonts.googleapis.com\">\n" port)
        (display "  <link rel=\"preconnect\" href=\"https://fonts.gstatic.com\" crossorigin>\n" port)
        (display "  <link href=\"https://fonts.googleapis.com/css2?family=JetBrains+Mono:wght@400;700&display=swap\" rel=\"stylesheet\">\n" port)
        (if is-memo
            (display (format "  <title>Memo ~a: ~a</title>\n" (memo-number->string num) (html-escape title)) port)
            (display (format "  <title>~a</title>\n" (html-escape title)) port))
        (display "  <link rel=\"icon\" id=\"favicon\" href=\"data:image/svg+xml,<svg xmlns=%27http://www.w3.org/2000/svg%27 viewBox=%270 0 32 32%27><text x=%2716%27 y=%2725%27 font-family=%27serif%27 font-size=%2728%27 fill=%27%230f0%27 text-anchor=%27middle%27 font-weight=%27bold%27>λ</text></svg>\">\n" port)
        ;; Raga favicon - color follows time of day
        (display "  <script>
(function(){
  var h=new Date().getHours(),c;
  if(h>=4&&h<6)c='%23845EC2';       // brahma muhurta - violet
  else if(h>=6&&h<8)c='%23ffd700';  // dawn - gold
  else if(h>=8&&h<11)c='%2300d4aa'; // morning - teal
  else if(h>=11&&h<14)c='%230f0';   // midday - phosphor
  else if(h>=14&&h<17)c='%2339ff14';// afternoon - neon
  else if(h>=17&&h<19)c='%23ff6600';// sunset - orange
  else if(h>=19&&h<22)c='%23ff3366';// evening - coral
  else c='%2300ffff';               // night - cyan
  document.getElementById('favicon').href='data:image/svg+xml,<svg xmlns=%27http://www.w3.org/2000/svg%27 viewBox=%270 0 32 32%27><text x=%2716%27 y=%2725%27 font-family=%27serif%27 font-size=%2728%27 fill=%27'+c+'%27 text-anchor=%27middle%27 font-weight=%27bold%27>λ</text></svg>';
})();
</script>\n" port)
        (display "  <link rel=\"stylesheet\" href=\"memo.css\">\n" port)
        (display "</head>\n<body>\n" port)
        ;; Theme toggle
        (display "<span class=\"theme-toggle\" onclick=\"toggleTheme()\" title=\"Toggle light/dark\">[theme]</span>\n" port)

        ;; Format notice - browsers can't be trusted with box-drawing
        (let ((base (pathname-strip-extension filename)))
          (display (format "<p class=\"format-notice\"><em>For pixel-perfect diagrams: <a href=\"~a.ps\">PostScript</a> or <a href=\"~a.pdf\">PDF</a></em></p>\n" base base) port))

        ;; Title block
        (if is-memo
            (display (format "<h1>Memo ~a: ~a</h1>\n" (memo-number->string num) (html-escape title)) port)
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

(define (memo->ms doc filename)
  "Convert Memo or document S-expression to groff ms macros."
  (call-with-output-file filename
    (lambda (port)
      (let ((is-memo (eq? (doc-type doc) 'memo))
            (num (get-field doc 'number 0))
            (title (get-field doc 'title "Untitled"))
            (subtitle (get-field doc 'subtitle #f))
            (status (get-field doc 'status #f))
            (date (get-field doc 'date ""))
            (author (assq 'author (cdr doc))))

        ;; ms preamble
        (display ".nr PS 10\n" port)
        (display ".nr VS 12\n" port)
        (if is-memo
            (display (format ".ds LH Memo ~a\n" (memo-number->string num)) port)
            (display ".ds LH\n" port))
        (display ".ds CH\n" port)
        (display ".ds RH \\n%\n" port)

        ;; Title
        (display ".TL\n" port)
        (if is-memo
            (display (format "Memo ~a: ~a\n" (memo-number->string num) (ms-escape title)) port)
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

(define (ps-escape str)
  "Escape special PostScript characters in string."
  (let ((out (open-output-string)))
    (string-for-each
     (lambda (c)
       (case c
         ((#\\) (display "\\\\" out))
         ((#\() (display "\\(" out))
         ((#\)) (display "\\)" out))
         (else (display c out))))
     str)
    (get-output-string out)))

(define (memo->ps doc filename)
  "Convert Memo S-expression to PostScript directly (no external tools)."
  (let ((txt-file (string-append (pathname-strip-extension filename) ".txt")))
    (when (file-exists? txt-file)
      (call-with-output-file filename
        (lambda (out)
          ;; PostScript header
          (display "%!PS-Adobe-3.0\n" out)
          (display "%%Title: " out)
          (display (pathname-strip-directory (pathname-strip-extension filename)) out)
          (display "\n%%Creator: Library of Cyberspace Memo Pipeline\n" out)
          (display "%%Pages: (atend)\n" out)
          (display "%%EndComments\n\n" out)

          ;; Setup: Courier 10pt, 72pt margins, 12pt leading
          (display "/Courier findfont 10 scalefont setfont\n" out)
          (display "/margin 72 def\n" out)
          (display "/pagewidth 612 def\n" out)
          (display "/pageheight 792 def\n" out)
          (display "/leading 12 def\n" out)
          (display "/topmargin pageheight margin sub def\n" out)
          (display "/bottommargin margin def\n" out)
          (display "/linewidth pagewidth margin 2 mul sub def\n" out)
          (display "/ypos topmargin def\n" out)
          (display "/pagenum 1 def\n\n" out)

          ;; Newline procedure
          (display "/newline {\n" out)
          (display "  /ypos ypos leading sub def\n" out)
          (display "  ypos bottommargin lt {\n" out)
          (display "    showpage\n" out)
          (display "    /pagenum pagenum 1 add def\n" out)
          (display "    /ypos topmargin def\n" out)
          (display "  } if\n" out)
          (display "  margin ypos moveto\n" out)
          (display "} def\n\n" out)

          ;; Start first page
          (display "margin topmargin moveto\n" out)

          ;; Read text file and emit lines
          (call-with-input-file txt-file
            (lambda (in)
              (let loop ((line (read-line in)))
                (unless (eof-object? line)
                  (display "(" out)
                  (display (ps-escape line) out)
                  (display ") show newline\n" out)
                  (loop (read-line in))))))

          ;; Footer
          (display "\nshowpage\n" out)
          (display "%%Trailer\n" out)
          (display "%%Pages: pagenum\n" out)
          (display "%%EOF\n" out))))))

;;; ============================================================
;;; PDF Output (via Ghostscript)
;;; ============================================================

(define (memo->pdf ps-file pdf-file)
  "Convert PostScript file to PDF using Ghostscript."
  (let ((result (system
                  (string-append
                    "gs -q -dNOPAUSE -dBATCH -sDEVICE=pdfwrite "
                    "-dPDFSETTINGS=/prepress "
                    "-dEmbedAllFonts=true "
                    "-sOutputFile=" pdf-file " "
                    ps-file))))
    (= result 0)))

;;; ============================================================
;;; LaTeX Output
;;; ============================================================
;;; Proper typesetting with TikZ diagrams, xelatex compilation.

(define (latex-escape str)
  "Escape special LaTeX characters in string."
  (let ((out (open-output-string)))
    (string-for-each
     (lambda (c)
       (case c
         ((#\\) (display "\\textbackslash{}" out))
         ((#\{) (display "\\{" out))
         ((#\}) (display "\\}" out))
         ((#\$) (display "\\$" out))
         ((#\&) (display "\\&" out))
         ((#\%) (display "\\%" out))
         ((#\#) (display "\\#" out))
         ((#\_) (display "\\_" out))
         ((#\^) (display "\\textasciicircum{}" out))
         ((#\~) (display "\\textasciitilde{}" out))
         (else (display c out))))
     str)
    (get-output-string out)))

(define (latex-emit-element elem port)
  (cond
    ((string? elem)
     (display (latex-escape elem) port)
     (newline port)
     (newline port))
    ((not (pair? elem)) #f)
    (else
     (case (car elem)
       ((p)
        (for-each (lambda (e)
                    (if (string? e)
                        (display (latex-escape e) port)
                        (latex-emit-element e port)))
                  (cdr elem))
        (newline port)
        (newline port))

       ((section)
        (display "\\section{" port)
        (display (latex-escape (cadr elem)) port)
        (display "}\n\n" port)
        (for-each (lambda (e) (latex-emit-element e port)) (cddr elem)))

       ((subsection)
        (display "\\subsection{" port)
        (display (latex-escape (cadr elem)) port)
        (display "}\n\n" port)
        (for-each (lambda (e) (latex-emit-element e port)) (cddr elem)))

       ((list)
        (display "\\begin{itemize}\n" port)
        (for-each (lambda (item)
                    (cond
                      ((and (pair? item) (eq? (car item) 'item))
                       (display "  \\item " port)
                       (let ((content (cdr item)))
                         (for-each (lambda (e)
                                     (if (string? e)
                                         (display (latex-escape e) port)
                                         (latex-emit-element e port)))
                                   content))
                       (newline port))
                      (else (latex-emit-element item port))))
                  (cdr elem))
        (display "\\end{itemize}\n\n" port))

       ((code)
        (let* ((has-lang (and (pair? (cdr elem)) (symbol? (cadr elem))))
               (lang (if has-lang (symbol->string (cadr elem)) ""))
               (content (if has-lang (caddr elem) (cadr elem))))
          (if (string-has-box-chars? content)
              ;; Box-drawing diagram - use verbatim
              (begin
                (display "\\begin{diagram}\n" port)
                (display content port)
                (display "\n\\end{diagram}\n\n" port))
              ;; Regular code
              (begin
                (display (format "\\begin{lstlisting}[language=~a]\n"
                                 (if (string-null? lang) "Scheme" lang)) port)
                (display content port)
                (display "\n\\end{lstlisting}\n\n" port)))))

       ((table)
        (let* ((header (find (lambda (e) (and (pair? e) (eq? (car e) 'header))) (cdr elem)))
               (rows (filter (lambda (e) (and (pair? e) (eq? (car e) 'row))) (cdr elem)))
               (ncols (if header (length (cdr header)) (if (pair? rows) (length (cdr (car rows))) 3))))
          (display (format "\\begin{tabular}{~a}\n" (make-string ncols #\l)) port)
          (display "\\hline\n" port)
          (when header
            (display (string-join (map latex-escape (map ->string (cdr header))) " & ") port)
            (display " \\\\\n\\hline\n" port))
          (for-each (lambda (row)
                      (display (string-join (map latex-escape (map ->string (cdr row))) " & ") port)
                      (display " \\\\\n" port))
                    rows)
          (display "\\hline\n\\end{tabular}\n\n" port)))

       ((link)
        (let ((url (cadr elem))
              (text (if (> (length elem) 2) (caddr elem) (cadr elem))))
          (display "\\href{" port)
          (display url port)
          (display "}{" port)
          (display (latex-escape text) port)
          (display "}" port)))

       ((bold b strong)
        (display "\\textbf{" port)
        (for-each (lambda (e)
                    (if (string? e)
                        (display (latex-escape e) port)
                        (latex-emit-element e port)))
                  (cdr elem))
        (display "}" port))

       ((em i italic)
        (display "\\textit{" port)
        (for-each (lambda (e)
                    (if (string? e)
                        (display (latex-escape e) port)
                        (latex-emit-element e port)))
                  (cdr elem))
        (display "}" port))

       ((tt code-inline)
        (display "\\texttt{" port)
        (for-each (lambda (e)
                    (if (string? e)
                        (display (latex-escape e) port)
                        (latex-emit-element e port)))
                  (cdr elem))
        (display "}" port))

       ((footer)
        (display "\n\\vfill\n\\hrule\n\\vspace{0.5em}\n\\begin{center}\n" port)
        (for-each (lambda (e) (latex-emit-element e port)) (cdr elem))
        (display "\\end{center}\n" port))

       (else
        ;; Unknown element - try to recurse
        (for-each (lambda (e) (latex-emit-element e port)) (cdr elem)))))))

(define (memo->latex doc filename)
  "Convert Memo S-expression to LaTeX."
  (call-with-output-file filename
    (lambda (port)
      (let ((num (get-field doc 'number 0))
            (title (get-field doc 'title "Untitled"))
            (date (get-field doc 'date ""))
            (author-info (assq 'author (cdr doc)))
            (abstract (assq 'abstract (cdr doc)))
            (sections (filter (lambda (e) (and (pair? e) (eq? (car e) 'section))) (cdr doc)))
            (footer (assq 'footer (cdr doc))))

        (let ((author-name (if author-info (cadr author-info) "Unknown"))
              (author-email (if (and author-info (> (length author-info) 2))
                                (caddr author-info)
                                "")))

          ;; Document preamble
          (display "\\documentclass{memo}\n\n" port)

          ;; Metadata
          (display (format "\\memonumber{~a}\n" (memo-number->string num)) port)
          (display (format "\\memotitle{~a}\n" (latex-escape title)) port)
          (display (format "\\memodate{~a}\n" (latex-escape date)) port)
          (display (format "\\memoauthor{~a}{~a}\n\n"
                           (latex-escape author-name)
                           (latex-escape author-email)) port)

          ;; PDF metadata
          (display (format "\\memopdftitle{Memo ~a: ~a}\n"
                           (memo-number->string num)
                           (latex-escape title)) port)
          (display (format "\\memopdfauthor{~a}\n" (latex-escape author-name)) port)
          (display (format "\\memopdfsubject{Cyberspace Technical Memo}\n") port)
          (display (format "\\memopdfkeywords{cyberspace, spki, ~a}\n\n"
                           (latex-escape (string-downcase title))) port)

          ;; Abstract
          (when abstract
            (display "\\memoabstract{" port)
            (for-each (lambda (e)
                        (if (string? e)
                            (display (latex-escape e) port)
                            (when (and (pair? e) (eq? (car e) 'p))
                              (for-each (lambda (x)
                                          (if (string? x)
                                              (display (latex-escape x) port)
                                              (latex-emit-element x port)))
                                        (cdr e)))))
                      (cdr abstract))
            (display "}\n\n" port))

          ;; Begin document
          (display "\\begin{document}\n" port)
          (display "\\maketitle\n\n" port)

          ;; Sections
          (for-each (lambda (section)
                      (latex-emit-element section port))
                    sections)

          ;; Footer
          (when footer
            (latex-emit-element footer port))

          ;; End document
          (display "\\end{document}\n" port))))))

;;; ============================================================
;;; Markdown Output (local scratch only)
;;; ============================================================
;;; For local previewing with native markdown viewers.
;;; Not part of the publication pipeline - outputs to /tmp.

(define (md-emit-element elem port)
  (cond
    ((string? elem) (display elem port) (newline port) (newline port))
    ((not (pair? elem)) #f)
    (else
      (case (car elem)
        ((p)
          (for-each (lambda (e)
                      (if (string? e) (display e port) (md-emit-element e port)))
                    (cdr elem))
          (newline port) (newline port))

        ((section)
          (display "## " port)
          (display (cadr elem) port)
          (newline port) (newline port)
          (for-each (lambda (e) (md-emit-element e port)) (cddr elem)))

        ((subsection)
          (display "### " port)
          (display (cadr elem) port)
          (newline port) (newline port)
          (for-each (lambda (e) (md-emit-element e port)) (cddr elem)))

        ((list)
          (for-each (lambda (item)
                      (display "- " port)
                      (if (and (pair? item) (eq? (car item) 'item))
                          (display (apply string-append (map ->string (cdr item))) port)
                          (display (->string item) port))
                      (newline port))
                    (cdr elem))
          (newline port))

        ((blockquote)
          (display "> " port)
          (display (cadr elem) port)
          (newline port)
          (when (and (pair? (cddr elem)) (eq? (caaddr elem) 'cite))
            (display "> — " port)
            (display (cadr (caddr elem)) port)
            (newline port))
          (newline port))

        ((code)
          (let* ((has-lang (and (pair? (cdr elem)) (symbol? (cadr elem))))
                 (lang (if has-lang (symbol->string (cadr elem)) ""))
                 (content (if has-lang (caddr elem) (cadr elem))))
            (display "```" port)
            (display lang port)
            (newline port)
            (display content port)
            (newline port)
            (display "```" port)
            (newline port) (newline port)))

        ((link)
          (display "[" port)
          (display (caddr elem) port)
          (display "](" port)
          (display (cadr elem) port)
          (display ")" port)
          (newline port))

        ((table)
          (let ((rows (filter pair? (cdr elem))))
            (when (pair? rows)
              ;; Header row
              (let ((first-row (cdr (car rows))))
                (display "| " port)
                (for-each (lambda (cell)
                            (display (->string cell) port)
                            (display " | " port))
                          first-row)
                (newline port)
                ;; Separator
                (display "|" port)
                (for-each (lambda (_) (display " --- |" port)) first-row)
                (newline port))
              ;; Data rows
              (for-each (lambda (row)
                          (display "| " port)
                          (for-each (lambda (cell)
                                      (display (->string cell) port)
                                      (display " | " port))
                                    (cdr row))
                          (newline port))
                        (cdr rows))
              (newline port))))

        ((references)
          (for-each (lambda (ref)
                      (when (and (pair? ref) (eq? (car ref) 'ref))
                        (display (format "- **[~a, ~a]** ~a~%"
                                         (cadr ref) (caddr ref) (cadddr ref)) port)))
                    (cdr elem))
          (newline port))

        (else #f)))))

(define (memo->md doc #!optional filename)
  "Convert Memo to Markdown in /tmp for local viewing."
  (let* ((num (get-field doc 'number 0))
         (title (get-field doc 'title "Untitled"))
         (is-memo (eq? (doc-type doc) 'memo))
         (default-name (if is-memo
                           (format "/tmp/memo-~a.md" (memo-number->string num))
                           "/tmp/doc.md"))
         (outfile (or filename default-name)))
    (call-with-output-file outfile
      (lambda (port)
        (let ((subtitle (get-field doc 'subtitle #f))
              (status (get-field doc 'status #f))
              (date (get-field doc 'date ""))
              (author (assq 'author (cdr doc))))

          ;; Title
          (display "# " port)
          (if is-memo
              (display (format "Memo ~a: ~a" (memo-number->string num) title) port)
              (display title port))
          (newline port)
          (when subtitle
            (display "*" port)
            (display subtitle port)
            (display "*" port)
            (newline port))
          (newline port)

          ;; Metadata
          (when status
            (display (format "**Status:** ~a  " status) port)
            (newline port))
          (when (and date (not (string-null? date)))
            (display (format "**Date:** ~a  " date) port)
            (newline port))
          (when author
            (display (format "**Author:** ~a <~a>" (cadr author) (caddr author)) port)
            (newline port))
          (newline port)
          (display "---" port)
          (newline port) (newline port)

          ;; Abstract
          (let ((abstract (assq 'abstract (cdr doc))))
            (when abstract
              (display "## Abstract" port)
              (newline port) (newline port)
              (for-each (lambda (e) (md-emit-element e port)) (cdr abstract))))

          ;; Body
          (for-each (lambda (elem)
                      (when (and (pair? elem) (eq? (car elem) 'section))
                        (md-emit-element elem port)))
                    (cdr doc)))))
    (print "  -> " outfile)
    outfile))

;;; ============================================================
;;; Batch Processing
;;; ============================================================

(define (memo-generate src-file)
  "Generate all formats from an Memo source file."
  (let* ((base (pathname-strip-extension src-file))
         (doc (read-memo src-file)))
    (memo->txt doc (string-append base ".txt"))
    (memo->html doc (string-append base ".html"))
    (memo->ps doc (string-append base ".ps"))
    (print "Generated: " base ".{txt,html,ps}")))

;; Example usage:
;; (memo-generate "memo-0000-declaration.scm")
