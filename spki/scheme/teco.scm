#!/usr/bin/env csi -s
;;; teco.scm - TECO: Text Editor and COrrector
;;;
;;; A tribute to Dan Murphy, who created TECO in 1962 while an
;;; undergraduate at MIT: "I started writing TECO in order to edit
;;; programs I was writing on the PDP-1."
;;;
;;; Every character is a command. Every string is a program.
;;; If it looks like line noise, you're doing it right.
;;;
;;; Heritage:
;;;   1962  Dan Murphy creates TECO on PDP-1 at MIT
;;;   1960s Spreads to PDP-8, PDP-11, all DEC systems
;;;   1976  EMACS created as TECO macros (Editor MACroS)
;;;   1970s Jupiter (DECsystem-20 follow-on) cancelled; 36-bit era ends
;;;   1977  Dan Murphy joins VMS Engineering after Jupiter
;;;   2026  Reborn in Cyberspace Scheme
;;;
;;; References:
;;;   Dan Murphy's site: http://www.opost.com/dlm
;;;   IEEE Annals article: "The Beginnings of TECO" (Oct-Dec 2009)
;;;   TECOC (portable C): https://github.com/blakemcbride/TECOC
;;;   TECO-64: https://github.com/fpjohnston/TECO-64
;;;   Tom Almy's macOS builds: https://almy.us/teco.html
;;;
;;; See also: pencil.scm - Michael Shrayer's Electric Pencil (1976)
;;;
;;; Commands (VMS TECO compatible):
;;;   Movement:
;;;     J       Jump to beginning
;;;     nJ      Jump to position n
;;;     ZJ      Jump to end
;;;     nC      Move forward n characters (default 1)
;;;     nR      Move backward n characters (default 1)
;;;     nL      Move forward n lines (default 1)
;;;     .       Current position (as numeric)
;;;     Z       End of buffer position
;;;
;;;   Editing:
;;;     nD      Delete n characters forward
;;;     nK      Kill n lines
;;;     HK      Kill entire buffer
;;;     Itext$  Insert text ($ = ESC)
;;;
;;;   Search:
;;;     Stext$  Search forward
;;;     _text$  Search backward
;;;     Ntext$  Search with wrap
;;;     :Stext$ Search returning value (-1/0)
;;;     FSold$new$  Find and substitute
;;;
;;;   File:
;;;     ERfile$ Read file into buffer
;;;     EWfile$ Write buffer to file
;;;     EX      Exit (save if modified)
;;;     ^C      Abort (no save)
;;;
;;;   Display:
;;;     V       View current line
;;;     HT      Type entire buffer
;;;     nT      Type n lines
;;;     n=      Type numeric value
;;;
;;;   Q-registers (both numeric and text parts):
;;;     nUq     Store n in Q-register q (numeric)
;;;     Qq      Retrieve Q-register q (numeric)
;;;     n%q     Add n to Q-register q
;;;     ^Uqtext$  Store text in Q-register q
;;;     nXq     Extract n lines to Q-register (text)
;;;     Gq      Insert Q-register text into buffer
;;;     :Gq     Type Q-register text (no insert)
;;;     [q      Push Q-register onto stack
;;;     ]q      Pop Q-register from stack
;;;     Mq      Execute Q-register as macro
;;;
;;;   Programming:
;;;     n<cmds> Loop n times (0 = infinite)
;;;     F;      Break from loop
;;;     n"Ecmds' Conditional if n=0
;;;     n"Ncmds' Conditional if n≠0
;;;     n"Gcmds' Conditional if n>0
;;;     n"Lcmds' Conditional if n<0
;;;     +,-,*,/ Arithmetic
;;;     &,#     Bitwise AND, OR
;;;
;;; Heritage: PDP-1 (1962), PDP-8, PDP-11, VAX, EMACS foundation

(import scheme
        (chicken base)
        (chicken format)
        (chicken string)
        (chicken io)
        (chicken file)
        (chicken port)
        (chicken process-context)
        (chicken bitwise)
        srfi-13
        tty-ffi)

;;; ============================================================
;;; Buffer - Simple string buffer with dot (point)
;;; ============================================================

(define *buffer* "")        ; The text buffer
(define *dot* 0)            ; Current position (point)
(define *filename* #f)      ; Current file
(define *modified* #f)      ; Buffer modified?
(define *last-search* "")   ; Last search string (for N command)
;; Q-registers now in separate section below (numeric + text parts)

(define (buffer-size) (string-length *buffer*))

(define (clamp-dot)
  (set! *dot* (max 0 (min *dot* (buffer-size)))))

(define (goto-beginning)
  (set! *dot* 0))

(define (goto-end)
  (set! *dot* (buffer-size)))

(define (move-forward n)
  (set! *dot* (+ *dot* n))
  (clamp-dot))

(define (move-backward n)
  (set! *dot* (- *dot* n))
  (clamp-dot))

(define (move-lines n)
  "Move n lines forward (negative = backward)"
  (let loop ((remaining (abs n)))
    (when (> remaining 0)
      (if (>= n 0)
          ;; Forward: find next newline
          (let ((pos (string-index *buffer* #\newline *dot*)))
            (if pos
                (set! *dot* (+ pos 1))
                (set! *dot* (buffer-size))))
          ;; Backward: find previous newline
          (let loop-back ((p (- *dot* 1)))
            (cond
              ((< p 0) (set! *dot* 0))
              ((char=? (string-ref *buffer* p) #\newline)
               (set! *dot* p))
              (else (loop-back (- p 1))))))
      (loop (- remaining 1))))
  (clamp-dot))

(define (current-line)
  "Return the current line containing dot"
  (let* ((start (let loop ((p *dot*))
                  (cond ((= p 0) 0)
                        ((char=? (string-ref *buffer* (- p 1)) #\newline) p)
                        (else (loop (- p 1))))))
         (end (let loop ((p *dot*))
                (cond ((>= p (buffer-size)) p)
                      ((char=? (string-ref *buffer* p) #\newline) p)
                      (else (loop (+ p 1)))))))
    (substring *buffer* start end)))

(define (delete-chars n)
  "Delete n characters at dot"
  (when (> n 0)
    (let ((end (min (+ *dot* n) (buffer-size))))
      (set! *buffer* (string-append
                       (substring *buffer* 0 *dot*)
                       (substring *buffer* end)))
      (set! *modified* #t)
      (clamp-dot))))

(define (kill-lines n)
  "Kill n lines from dot"
  (let* ((end-pos *dot*))
    (let loop ((remaining n) (pos *dot*))
      (cond
        ((= remaining 0) (set! end-pos pos))
        ((>= pos (buffer-size)) (set! end-pos pos))
        ((char=? (string-ref *buffer* pos) #\newline)
         (loop (- remaining 1) (+ pos 1)))
        (else (loop remaining (+ pos 1)))))
    (set! *buffer* (string-append
                     (substring *buffer* 0 *dot*)
                     (substring *buffer* end-pos)))
    (set! *modified* #t)
    (clamp-dot)))

(define (insert-text text)
  "Insert text at dot"
  (set! *buffer* (string-append
                   (substring *buffer* 0 *dot*)
                   text
                   (substring *buffer* *dot*)))
  (set! *dot* (+ *dot* (string-length text)))
  (set! *modified* #t))

(define (search-forward text)
  "Search for text from dot, return #t if found"
  (let ((pos (string-contains *buffer* text *dot*)))
    (if pos
        (begin (set! *dot* pos) #t)
        #f)))

(define (search-backward text)
  "Search backward for text from dot, return #t if found"
  (let ((len (string-length text)))
    (let loop ((p (- *dot* 1)))
      (cond
        ((< p 0) #f)
        ((and (<= (+ p len) (buffer-size))
              (string=? text (substring *buffer* p (+ p len))))
         (set! *dot* p)
         #t)
        (else (loop (- p 1)))))))

;;; ============================================================
;;; File Operations
;;; ============================================================

(define (read-file filename)
  (if (file-exists? filename)
      (begin
        (set! *buffer* (with-input-from-file filename read-string))
        (set! *filename* filename)
        (set! *dot* 0)
        (set! *modified* #f)
        (printf "~a bytes~%" (buffer-size)))
      (printf "?NFI  Not found: ~a~%" filename)))

(define (write-file filename)
  (with-output-to-file filename
    (lambda () (display *buffer*)))
  (set! *filename* filename)
  (set! *modified* #f)
  (printf "~a bytes written~%" (buffer-size)))

;;; ============================================================
;;; Q-Registers (VMS TECO style)
;;; Each Q-register has both a numeric part and a text part
;;; ============================================================

(define *q-numeric* (make-vector 36 0))     ; Numeric values
(define *q-text* (make-vector 36 ""))       ; Text values
(define *q-stack* '())                       ; Push/pop stack

(define (q-index name)
  "Convert Q-register name to index (A-Z=0-25, 0-9=26-35)"
  (let ((c (if (char? name) name (string-ref (->string name) 0))))
    (cond
      ((char-alphabetic? c) (- (char->integer (char-upcase c)) 65))
      ((char-numeric? c) (+ 26 (- (char->integer c) 48)))
      (else 0))))

(define (q-get name)
  "Get numeric value from Q-register"
  (vector-ref *q-numeric* (q-index name)))

(define (q-set name value)
  "Set numeric value in Q-register"
  (vector-set! *q-numeric* (q-index name) value))

(define (q-get-text name)
  "Get text value from Q-register"
  (vector-ref *q-text* (q-index name)))

(define (q-set-text name text)
  "Set text value in Q-register"
  (vector-set! *q-text* (q-index name) text))

(define (q-push name)
  "Push Q-register onto stack ([q command)"
  (let ((idx (q-index name)))
    (set! *q-stack* (cons (cons (vector-ref *q-numeric* idx)
                                (vector-ref *q-text* idx))
                          *q-stack*))))

(define (q-pop name)
  "]q command - Pop Q-register from stack"
  (when (pair? *q-stack*)
    (let ((idx (q-index name))
          (val (car *q-stack*)))
      (vector-set! *q-numeric* idx (car val))
      (vector-set! *q-text* idx (cdr val))
      (set! *q-stack* (cdr *q-stack*)))))

;;; ============================================================
;;; Command Parser
;;; ============================================================

(define (parse-number str pos)
  "Parse numeric argument, return (value . new-pos) or (#f . pos)"
  (let loop ((p pos) (digits '()))
    (if (and (< p (string-length str))
             (or (char-numeric? (string-ref str p))
                 (and (null? digits) (char=? (string-ref str p) #\-))))
        (loop (+ p 1) (cons (string-ref str p) digits))
        (if (null? digits)
            (cons #f pos)
            (cons (string->number (list->string (reverse digits))) p)))))

(define (parse-string str pos delimiter)
  "Parse string argument until delimiter (ESC=27 or Ctrl-]=29)"
  (let loop ((p pos) (chars '()))
    (cond
      ((>= p (string-length str)) (cons (list->string (reverse chars)) p))
      ((let ((c (char->integer (string-ref str p))))
         (or (= c 27) (= c 29) (char=? (string-ref str p) delimiter)))
       (cons (list->string (reverse chars)) (+ p 1)))
      (else (loop (+ p 1) (cons (string-ref str p) chars))))))

(define (find-matching str pos open close)
  "Find matching delimiter, handling nesting. Returns position after close."
  (let loop ((p pos) (depth 1))
    (cond
      ((>= p (string-length str)) p)
      ((char=? (string-ref str p) open) (loop (+ p 1) (+ depth 1)))
      ((char=? (string-ref str p) close)
       (if (= depth 1) (+ p 1) (loop (+ p 1) (- depth 1))))
      (else (loop (+ p 1) depth)))))

(define (extract-block str pos open close)
  "Extract block between delimiters, return (content . pos-after-close)"
  (let ((end (find-matching str pos open close)))
    (cons (substring str pos (- end 1)) end)))

(define (execute-commands str)
  "Execute a TECO command string"
  (let loop ((pos 0) (num #f))
    (when (< pos (string-length str))
      (let ((c (char-upcase (string-ref str pos))))
        (case c
          ;; Numeric prefix
          ((#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9 #\-)
           (let ((result (parse-number str pos)))
             (loop (cdr result) (car result))))

          ;; Movement
          ((#\J) (if num (set! *dot* num) (goto-beginning)) (loop (+ pos 1) #f))
          ((#\C) (move-forward (or num 1)) (loop (+ pos 1) #f))
          ((#\R) (move-backward (or num 1)) (loop (+ pos 1) #f))
          ((#\L) (move-lines (or num 1)) (loop (+ pos 1) #f))

          ;; Editing
          ((#\D) (delete-chars (or num 1)) (loop (+ pos 1) #f))
          ((#\K) (kill-lines (or num 1)) (loop (+ pos 1) #f))
          ((#\I)
           (let ((result (parse-string str (+ pos 1) #\$)))
             (insert-text (car result))
             (loop (cdr result) #f)))

          ;; Search
          ((#\S)
           (let ((result (parse-string str (+ pos 1) #\$)))
             (set! *last-search* (car result))
             (unless (search-forward (car result))
               (print "?SRH  Search failed"))
             (loop (cdr result) #f)))

          ;; N - search and continue (for single-file, same as S but continues)
          ((#\N)
           (let* ((result (parse-string str (+ pos 1) #\$))
                  (pattern (car result)))
             (set! *last-search* pattern)
             (unless (search-forward pattern)
               ;; Wrap around to beginning
               (set! *dot* 0)
               (unless (search-forward pattern)
                 (print "?SRH  Search failed")))
             (loop (cdr result) #f)))

          ;; _ (underscore) - backward search
          ((#\_)
           (let ((result (parse-string str (+ pos 1) #\$)))
             (set! *last-search* (car result))
             (unless (search-backward (car result))
               (print "?SRH  Search failed"))
             (loop (cdr result) #f)))

          ;; : (colon) - modify next command
          ;; :S = search returning value, :G = type Q-register, etc.
          ((#\:)
           (if (< (+ pos 1) (string-length str))
               (let ((next-cmd (char-upcase (string-ref str (+ pos 1)))))
                 (case next-cmd
                   ;; :S - search returning value (-1=found, 0=not found)
                   ((#\S)
                    (let ((result (parse-string str (+ pos 2) #\$)))
                      (set! *last-search* (car result))
                      (if (search-forward (car result))
                          (set! num -1)  ; found
                          (set! num 0))  ; not found
                      (loop (cdr result) num)))

                   ;; :G - type Q-register contents (don't insert)
                   ((#\G)
                    (when (< (+ pos 2) (string-length str))
                      (let ((text (q-get-text (string-ref str (+ pos 2)))))
                        (when (string? text)
                          (display text)
                          (newline))))
                    (loop (+ pos 3) #f))

                   ;; :EG - return environment variable
                   ((#\E)
                    (loop (+ pos 2) #f))

                   (else (loop (+ pos 2) #f))))
               (loop (+ pos 1) #f)))

          ;; Display
          ((#\V) (print (current-line)) (loop (+ pos 1) #f))
          ((#\T)
           (let ((n (or num 1)))
             (print (current-line))
             (loop (+ pos 1) #f)))

          ;; File operations (E prefix)
          ((#\E)
           (if (< (+ pos 1) (string-length str))
               (let ((e-cmd (char-upcase (string-ref str (+ pos 1)))))
                 (case e-cmd
                   ((#\R)
                    (let ((result (parse-string str (+ pos 2) #\$)))
                      (read-file (string-trim-both (car result)))
                      (loop (cdr result) #f)))
                   ((#\W)
                    (let ((result (parse-string str (+ pos 2) #\$)))
                      (let ((fn (string-trim-both (car result))))
                        (write-file (if (string=? fn "")
                                        (or *filename* "noname.txt")
                                        fn)))
                      (loop (cdr result) #f)))
                   ((#\X)
                    (when (and *modified* *filename*)
                      (write-file *filename*))
                    'exit)
                   (else (loop (+ pos 2) #f))))
               (loop (+ pos 1) #f)))

          ;; Z modifier (end of buffer)
          ((#\Z)
           (if (and (< (+ pos 1) (string-length str))
                    (char-ci=? (string-ref str (+ pos 1)) #\J))
               (begin (goto-end) (loop (+ pos 2) #f))
               (begin (set! num (buffer-size)) (loop (+ pos 1) num))))

          ;; H modifier (whole buffer) - sets range to entire buffer
          ;; HK = kill whole buffer, HT = type whole buffer
          ((#\H)
           (cond
             ((and (< (+ pos 1) (string-length str))
                   (char-ci=? (string-ref str (+ pos 1)) #\T))
              (display *buffer*)
              (loop (+ pos 2) #f))
             ((and (< (+ pos 1) (string-length str))
                   (char-ci=? (string-ref str (+ pos 1)) #\K))
              ;; HK = kill whole buffer
              (set! *buffer* "")
              (set! *dot* 0)
              (set! *modified* #t)
              (loop (+ pos 2) #f))
             (else
              ;; H alone sets num to buffer size, dot to 0
              (goto-beginning)
              (loop (+ pos 1) (buffer-size)))))

          ;; Q-registers
          ((#\U)
           (when (< (+ pos 1) (string-length str))
             (q-set (string-ref str (+ pos 1)) (or num 0)))
           (loop (+ pos 2) #f))
          ((#\Q)
           (when (< (+ pos 1) (string-length str))
             (set! num (q-get (string-ref str (+ pos 1)))))
           (loop (+ pos 2) num))
          ;; Mq - execute macro in Q-register
          ((#\M)
           (when (< (+ pos 1) (string-length str))
             (let ((macro (q-get-text (string-ref str (+ pos 1)))))
               (when (and (string? macro) (> (string-length macro) 0))
                 (execute-commands macro))))
           (loop (+ pos 2) #f))

          ;; Gq - insert Q-register text into buffer at dot
          ((#\G)
           (when (< (+ pos 1) (string-length str))
             (let ((text (q-get-text (string-ref str (+ pos 1)))))
               (when (string? text)
                 (insert-text text))))
           (loop (+ pos 2) #f))

          ;; nXq - extract n lines to Q-register (default 1)
          ;; Stores text from dot to end of n lines
          ((#\X)
           (when (< (+ pos 1) (string-length str))
             (let* ((n (or num 1))
                    (start *dot*)
                    (end-pos (let find-end ((p *dot*) (lines n))
                               (cond
                                 ((= lines 0) p)
                                 ((>= p (buffer-size)) p)
                                 ((char=? (string-ref *buffer* p) #\newline)
                                  (find-end (+ p 1) (- lines 1)))
                                 (else (find-end (+ p 1) lines))))))
               (q-set-text (string-ref str (+ pos 1))
                           (substring *buffer* start end-pos))))
           (loop (+ pos 2) #f))

          ;; [q - push Q-register onto stack
          ((#\[)
           (when (< (+ pos 1) (string-length str))
             (q-push (string-ref str (+ pos 1))))
           (loop (+ pos 2) #f))

          ;; ]q - pop Q-register from stack
          ((#\])
           (when (< (+ pos 1) (string-length str))
             (q-pop (string-ref str (+ pos 1))))
           (loop (+ pos 2) #f))

          ;; %q - add numeric arg to Q-register (returns new value)
          ((#\%)
           (when (< (+ pos 1) (string-length str))
             (let* ((reg (string-ref str (+ pos 1)))
                    (val (+ (q-get reg) (or num 1))))
               (q-set reg val)
               (set! num val)))
           (loop (+ pos 2) num))

          ;; Value commands - return numeric values
          ((#\.) (loop (+ pos 1) *dot*))          ; . = current position
          ((#\B) (loop (+ pos 1) 0))              ; B = beginning (always 0)
          ;; Z already handled above as modifier

          ;; A - ASCII value of character at dot+n (default 0)
          ;; nA returns ASCII of character at position dot+n
          ((#\A)
           (let* ((offset (or num 0))
                  (pos-at (+ *dot* offset)))
             (if (and (>= pos-at 0) (< pos-at (buffer-size)))
                 (set! num (char->integer (string-ref *buffer* pos-at)))
                 (set! num -1)))  ; -1 for end of buffer
           (loop (+ pos 1) num))

          ;; ^^ - ASCII value of next character in command string
          ((#\^)
           (if (and (< (+ pos 1) (string-length str))
                    (char=? (string-ref str (+ pos 1)) #\^))
               ;; ^^ = get ASCII of following char
               (if (< (+ pos 2) (string-length str))
                   (begin
                     (set! num (char->integer (string-ref str (+ pos 2))))
                     (loop (+ pos 3) num))
                   (loop (+ pos 2) #f))
               ;; Single ^ - could be control char prefix
               (if (< (+ pos 1) (string-length str))
                   (let ((ctl-char (char-upcase (string-ref str (+ pos 1)))))
                     ;; ^A = 1, ^B = 2, etc.
                     (set! num (- (char->integer ctl-char) 64))
                     (loop (+ pos 2) num))
                   (loop (+ pos 1) #f))))

          ;; Arithmetic
          ((#\+)
           (if num
               (let ((result (parse-number str (+ pos 1))))
                 (loop (cdr result) (+ num (or (car result) 0))))
               (loop (+ pos 1) num)))
          ((#\*)
           (if num
               (let ((result (parse-number str (+ pos 1))))
                 (loop (cdr result) (* num (or (car result) 1))))
               (loop (+ pos 1) num)))
          ((#\/)
           (if num
               (let ((result (parse-number str (+ pos 1))))
                 (let ((divisor (or (car result) 1)))
                   (loop (cdr result) (if (zero? divisor) 0 (quotient num divisor)))))
               (loop (+ pos 1) num)))
          ((#\&)  ; bitwise AND
           (if num
               (let ((result (parse-number str (+ pos 1))))
                 (loop (cdr result) (bitwise-and num (or (car result) 0))))
               (loop (+ pos 1) num)))
          ((#\#)  ; bitwise OR
           (if num
               (let ((result (parse-number str (+ pos 1))))
                 (loop (cdr result) (bitwise-ior num (or (car result) 0))))
               (loop (+ pos 1) num)))

          ;; Conditionals: n"Xcommands'
          ;; "E = if equal to 0, "N = if not equal, "G = if greater, "L = if less
          ((#\")
           (if (< (+ pos 1) (string-length str))
               (let* ((cond-type (char-upcase (string-ref str (+ pos 1))))
                      (test-val (or num 0))
                      (block (extract-block str (+ pos 2) #\" #\'))
                      (body (car block))
                      (end-pos (cdr block))
                      (do-it (case cond-type
                               ((#\E) (zero? test-val))        ; Equal to 0
                               ((#\N) (not (zero? test-val)))  ; Not equal to 0
                               ((#\G) (> test-val 0))          ; Greater than 0
                               ((#\L) (< test-val 0))          ; Less than 0
                               ((#\T) #t)                       ; Always true
                               ((#\F) #f)                       ; Always false
                               (else #f))))
                 (when do-it (execute-commands body))
                 (loop end-pos #f))
               (loop (+ pos 1) #f)))

          ;; Loops: n<commands> - repeat n times (0 = infinite until F;)
          ((#\<)
           (let* ((block (extract-block str (+ pos 1) #\< #\>))
                  (body (car block))
                  (end-pos (cdr block))
                  (count (or num 1)))
             (if (zero? count)
                 ;; Infinite loop - need F; to break
                 (let inf-loop ()
                   (let ((result (execute-commands body)))
                     (unless (eq? result 'break)
                       (inf-loop))))
                 ;; Counted loop
                 (let count-loop ((n count))
                   (when (> n 0)
                     (let ((result (execute-commands body)))
                       (unless (eq? result 'break)
                         (count-loop (- n 1)))))))
             (loop end-pos #f)))

          ;; F commands - F; (break), FS (find/substitute), etc.
          ((#\F)
           (if (< (+ pos 1) (string-length str))
               (let ((f-cmd (char-upcase (string-ref str (+ pos 1)))))
                 (case f-cmd
                   ;; F; - break from loop
                   ((#\;) 'break)

                   ;; FSold$new$ - find and substitute
                   ((#\S)
                    (let* ((old-result (parse-string str (+ pos 2) #\$))
                           (old-str (car old-result))
                           (new-result (parse-string str (cdr old-result) #\$))
                           (new-str (car new-result)))
                      (if (search-forward old-str)
                          (begin
                            ;; Delete old string and insert new
                            (delete-chars (string-length old-str))
                            (insert-text new-str))
                          (print "?SRH  Search failed"))
                      (loop (cdr new-result) #f)))

                   ;; FR - replace (at current position, no search)
                   ((#\R)
                    (let* ((old-result (parse-string str (+ pos 2) #\$))
                           (old-str (car old-result))
                           (new-result (parse-string str (cdr old-result) #\$))
                           (new-str (car new-result)))
                      ;; Assume we just found old-str, delete and replace
                      (delete-chars (string-length old-str))
                      (insert-text new-str)
                      (loop (cdr new-result) #f)))

                   ;; FC - find and change (like FS but bounded search)
                   ((#\C)
                    (let* ((old-result (parse-string str (+ pos 2) #\$))
                           (old-str (car old-result))
                           (new-result (parse-string str (cdr old-result) #\$))
                           (new-str (car new-result)))
                      (if (search-forward old-str)
                          (begin
                            (delete-chars (string-length old-str))
                            (insert-text new-str))
                          (print "?SRH  Search failed"))
                      (loop (cdr new-result) #f)))

                   (else (loop (+ pos 2) #f))))
               (loop (+ pos 1) #f)))

          ;; = - type numeric value (== for octal, === for hex)
          ((#\=)
           (cond
             ((and (< (+ pos 2) (string-length str))
                   (char=? (string-ref str (+ pos 1)) #\=)
                   (char=? (string-ref str (+ pos 2)) #\=))
              ;; === hex
              (printf "~x~%" (or num 0))
              (loop (+ pos 3) #f))
             ((and (< (+ pos 1) (string-length str))
                   (char=? (string-ref str (+ pos 1)) #\=))
              ;; == octal
              (printf "~o~%" (or num 0))
              (loop (+ pos 2) #f))
             (else
              ;; = decimal
              (printf "~a~%" (or num 0))
              (loop (+ pos 1) #f))))

          ;; ; - conditional exit from loop/iteration
          ;; n; exits if n >= 0
          ((#\;)
           (if (and num (>= num 0))
               'break
               (loop (+ pos 1) #f)))

          ;; Ctrl-C (in command string) = abort
          ((#\x03) 'abort)

          ;; ^Uqtext$ - store text in Q-register q (text part)
          ((#\x15)  ; Ctrl-U
           (if (< (+ pos 1) (string-length str))
               (let* ((reg (string-ref str (+ pos 1)))
                      (result (parse-string str (+ pos 2) #\$)))
                 (q-set-text reg (car result))
                 (loop (cdr result) #f))
               (loop (+ pos 1) #f)))

          ;; ^T - type character at dot as numeric (returns ASCII value)
          ((#\x14)  ; Ctrl-T
           (if (< *dot* (buffer-size))
               (set! num (char->integer (string-ref *buffer* *dot*)))
               (set! num -1))
           (loop (+ pos 1) num))

          ;; ^S - return negative of last string length
          ((#\x13)  ; Ctrl-S
           (set! num (- (string-length *last-search*)))
           (loop (+ pos 1) num))

          ;; ^Q - quote next char (insert literal)
          ((#\x11)  ; Ctrl-Q
           (when (< (+ pos 1) (string-length str))
             (insert-text (string (string-ref str (+ pos 1)))))
           (loop (+ pos 2) #f))

          ;; Whitespace/delimiters - ignore (ESC = $ = x1b)
          ((#\space #\tab #\newline #\$ #\return #\x0d #\x1b) (loop (+ pos 1) num))

          ;; Unknown command
          (else
           (printf "?ILL  Illegal command: ~a~%" c)
           (loop (+ pos 1) #f)))))))

;;; ============================================================
;;; TECO REPL
;;; ============================================================

(define (teco-banner)
  (print "")
  (print "TECO - Text Editor and COrrector")
  (print "A tribute to Dan Murphy (MIT '65, BBN, DEC)")
  (print "\"I started writing TECO in 1962 in order to edit")
  (print " programs I was writing on the PDP-1.\"")
  (print "opost.com/tenex/")
  (print "")
  (print "Movement:        Editing:          Search:")
  (print "  J   beginning    Itext$  insert    Stext$  forward")
  (print "  ZJ  end          nD      delete    _text$  backward")
  (print "  nC  forward      nK      kill      FSold$new$  subst")
  (print "  nR  backward     HK      kill all")
  (print "  nL  n lines")
  (print "")
  (print "File:            Q-registers:      Programming:")
  (print "  ERfile$  read    nUq  store       n<cmds>  loop")
  (print "  EWfile$  write   Qq   get         n\"Ecmds' if =0")
  (print "  EX       exit    Gq   insert      F;       break")
  (print "  HT       type    Mq   execute")
  (print "")
  (print "  V  view line   .  position   =  print   ?  help")
  (print "")
  (print "  $$ = execute (ESC ESC)    ^G = cancel    ^U = kill line")
  (print ""))

(define (teco-prompt)
  "VMS TECO style prompt: accumulate commands, $$ executes.
   ESC echoes as $, double-ESC executes command string."
  (display "*")
  (flush-output)
  (tty-set-raw)
  (let loop ((chars '()) (last-was-esc #f))
    (let ((c (tty-raw-char)))
      (cond
        ;; EOF or error
        ((< c 0)
         (tty-set-cooked)
         (newline)
         #f)

        ;; ESC (27)
        ((= c 27)
         (display "$")
         (flush-output)
         (if last-was-esc
             ;; Double ESC - execute!
             (begin
               (tty-set-cooked)
               (newline)
               (list->string (reverse chars)))
             ;; First ESC - add to command string, remember
             (loop (cons (integer->char c) chars) #t)))

        ;; Ctrl-G (7) - cancel current input, reprompt
        ((= c 7)
         (tty-set-cooked)
         (newline)
         (print "^G")
         "")

        ;; Ctrl-C (3) - abort, exit TECO
        ((= c 3)
         (tty-set-cooked)
         (newline)
         'abort)

        ;; Backspace (127) or DEL (8)
        ((or (= c 127) (= c 8))
         (when (pair? chars)
           ;; Erase character from display
           (display "\b \b")
           (flush-output))
         (loop (if (pair? chars) (cdr chars) chars) #f))

        ;; Ctrl-U (21) - kill line
        ((= c 21)
         ;; Erase all characters
         (let erase ((n (length chars)))
           (when (> n 0)
             (display "\b \b")
             (erase (- n 1))))
         (flush-output)
         (loop '() #f))

        ;; CR (13) or LF (10) - execute (alternate to $$)
        ((or (= c 13) (= c 10))
         (tty-set-cooked)
         (newline)
         (list->string (reverse chars)))

        ;; Regular character
        (else
         (let ((ch (integer->char c)))
           ;; Echo the character (control chars as ^X)
           (if (< c 32)
               (begin
                 (display "^")
                 (display (integer->char (+ c 64))))
               (display ch))
           (flush-output)
           (loop (cons ch chars) #f)))))))

(define (teco #!optional filename)
  "TECO main entry point"
  (set! *buffer* "")
  (set! *dot* 0)
  (set! *filename* #f)
  (set! *modified* #f)

  (teco-banner)

  ;; Load initial file if specified
  (when filename
    (read-file filename))

  ;; Command loop
  (let loop ()
    (let ((cmd (teco-prompt)))
      (cond
        ((or (eof-object? cmd) (not cmd) (eq? cmd 'abort))
         (void))
        ((not (string? cmd))
         ;; Non-string result (symbol) - exit
         (void))
        ((string=? cmd "?")
         (teco-banner)
         (loop))
        ((string=? cmd "")
         ;; Empty command - just reprompt
         (loop))
        ((member cmd '("q" "quit" "exit"))
         (when (and *modified* *filename*)
           (printf "Save ~a? " *filename*)
           (flush-output)
           (let ((ans (read-line)))
             (when (and (string? ans)
                        (> (string-length ans) 0)
                        (char-ci=? (string-ref ans 0) #\y))
               (write-file *filename*))))
         (void))
        (else
         (let ((result (execute-commands cmd)))
           (case result
             ((exit)
              (void))
             ((abort)
              (print "^C")
              (void))
             (else (loop)))))))))

(print "TECO loaded. (teco) or (teco \"file.txt\") to edit.")

;; If run as script
(when (or (member "-s" (command-line-arguments))
          (member "--script" (command-line-arguments)))
  (teco))
