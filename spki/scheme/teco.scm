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
;;; Commands (subset):
;;;   Movement:
;;;     j       Jump to beginning
;;;     zj      Jump to end
;;;     nC      Move forward n characters (default 1)
;;;     nR      Move backward n characters (default 1)
;;;     nL      Move forward n lines (default 1)
;;;
;;;   Editing:
;;;     nD      Delete n characters forward
;;;     nK      Kill n lines
;;;     Itext$  Insert text ($ = ESC or Ctrl-])
;;;
;;;   Search:
;;;     Stext$  Search forward for text
;;;     Ntext$  Search and continue
;;;
;;;   File:
;;;     ERfile$ Read file into buffer
;;;     EWfile$ Write buffer to file
;;;     EX      Exit (save if modified)
;;;     ^^C     Abort (no save)
;;;
;;;   Display:
;;;     V       View current line
;;;     HT      Type entire buffer
;;;     nT      Type n lines
;;;
;;;   Q-registers:
;;;     nUq     Store n in Q-register q
;;;     Qq      Retrieve Q-register q
;;;     n%q     Add n to Q-register q
;;;
;;;   Macros:
;;;     Mq      Execute macro in Q-register q
;;;     @       Modify next command
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
        srfi-13)

;;; ============================================================
;;; Buffer - Simple string buffer with dot (point)
;;; ============================================================

(define *buffer* "")        ; The text buffer
(define *dot* 0)            ; Current position (point)
(define *filename* #f)      ; Current file
(define *modified* #f)      ; Buffer modified?
(define *q-registers* (make-vector 36 ""))  ; Q-registers A-Z, 0-9

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
;;; Q-Registers
;;; ============================================================

(define (q-index name)
  "Convert Q-register name to index (A-Z=0-25, 0-9=26-35)"
  (let ((c (if (char? name) name (string-ref (->string name) 0))))
    (cond
      ((char-alphabetic? c) (- (char->integer (char-upcase c)) 65))
      ((char-numeric? c) (+ 26 (- (char->integer c) 48)))
      (else 0))))

(define (q-get name)
  (vector-ref *q-registers* (q-index name)))

(define (q-set name value)
  (vector-set! *q-registers* (q-index name) value))

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
             (unless (search-forward (car result))
               (print "?SRH  Search failed"))
             (loop (cdr result) #f)))

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

          ;; H modifier (whole buffer)
          ((#\H)
           (if (and (< (+ pos 1) (string-length str))
                    (char-ci=? (string-ref str (+ pos 1)) #\T))
               (begin (display *buffer*) (loop (+ pos 2) #f))
               (loop (+ pos 1) #f)))

          ;; Q-registers
          ((#\U)
           (when (< (+ pos 1) (string-length str))
             (q-set (string-ref str (+ pos 1)) (or num 0)))
           (loop (+ pos 2) #f))
          ((#\Q)
           (when (< (+ pos 1) (string-length str))
             (set! num (q-get (string-ref str (+ pos 1)))))
           (loop (+ pos 2) num))

          ;; Ctrl-C (in command string) = abort
          ((#\x03) 'abort)

          ;; Whitespace/delimiters - ignore
          ((#\space #\tab #\newline #\$ #\return #\x0d) (loop (+ pos 1) num))

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
  (print "opost.com/tenex/")
  (print "")
  (print "  ERfile$  Read file       EWfile$  Write file")
  (print "  Itext$   Insert          nD       Delete n chars")
  (print "  Stext$   Search          V        View line")
  (print "  J        Beginning       ZJ       End")
  (print "  nC/nR    Move fwd/back   nL       Move n lines")
  (print "  HT       Type all        EX       Exit")
  (print "  ?        This help       $ = ESC")
  (print "")
  (print "\"I started writing TECO in 1962 in order to edit")
  (print " programs I was writing on the PDP-1.\" - Dan Murphy"))

(define (teco-prompt)
  (display "*")
  (flush-output)
  (read-line))

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
        ((or (eof-object? cmd) (not cmd))
         (print "")
         (void))
        ((string=? cmd "?")
         (teco-banner)
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
              (print "")
              (void))
             ((abort)
              (print "^C")
              (void))
             (else (loop)))))))))

;; If run as script
(when (or (member "-s" (command-line-arguments))
          (member "--script" (command-line-arguments)))
  (teco))
