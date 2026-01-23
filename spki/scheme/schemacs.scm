#!/usr/bin/env csi -s
;;; Schemacs - Emacs-like editor in Scheme
;;;
;;; Inspired by guenchi/Schemacs (Chez) but built for Chicken Scheme.
;;; Uses same gap buffer as Electric Pencil but with Emacs keybindings.
;;;
;;; Heritage:
;;;   1976  EMACS - Richard Stallman at MIT AI Lab
;;;   1984  GNU Emacs - self-documenting, extensible
;;;   2026  Schemacs - Emacs spirit, Scheme soul
;;;
;;; The key insight: where Emacs has elisp, we have Scheme.
;;; The REPL *is* the extension language.
;;;
;;; Basic commands:
;;;   C-f/b/n/p   forward/back char, next/prev line
;;;   C-a/e       start/end of line
;;;   M-f/b       forward/back word
;;;   C-v/M-v     page down/up
;;;   M-</>       beginning/end of buffer
;;;
;;;   C-d         delete char
;;;   C-k         kill to end of line
;;;   C-y         yank (paste)
;;;   M-y         yank-pop (cycle kill ring)
;;;   C-w         kill region
;;;   M-w         copy region
;;;   C-space     set mark
;;;   C-x C-x     exchange point and mark
;;;
;;;   C-s         incremental search forward
;;;   C-r         incremental search backward
;;;   M-%         query replace
;;;
;;;   C-x C-f     find file
;;;   C-x C-s     save file
;;;   C-x C-c     quit
;;;   C-x C-w     write file (save as)
;;;
;;;   C-g         cancel
;;;   C-l         recenter
;;;   M-x         execute command

(import scheme
        (chicken base)
        (chicken format)
        (chicken string)
        (chicken io)
        (chicken port)
        (chicken file)
        (chicken process-context)
        srfi-13
        tty-ffi)

;;; ============================================================
;;; Screen Module - ANSI Terminal Control (shared with pencil)
;;; ============================================================

(define ESC (integer->char 27))

(define (screen-escape . args)
  (apply string-append (cons (string ESC #\[) args)))

(define (screen-goto row col)
  (display (screen-escape (number->string row) ";" (number->string col) "H")))

(define (screen-up #!optional (n 1))
  (display (screen-escape (number->string n) "A")))

(define (screen-down #!optional (n 1))
  (display (screen-escape (number->string n) "B")))

(define (screen-right #!optional (n 1))
  (display (screen-escape (number->string n) "C")))

(define (screen-left #!optional (n 1))
  (display (screen-escape (number->string n) "D")))

(define (screen-home)
  (display (screen-escape "H")))

(define (screen-clear)
  (display (screen-escape "2J"))
  (screen-home))

(define (screen-clear-line)
  (display (screen-escape "2K")))

(define (screen-clear-eol)
  (display (screen-escape "K")))

(define (screen-clear-eos)
  (display (screen-escape "J")))

(define (screen-reset)
  (display (screen-escape "0m")))

(define (screen-bold)
  (display (screen-escape "1m")))

(define (screen-dim)
  (display (screen-escape "2m")))

(define (screen-reverse)
  (display (screen-escape "7m")))

(define (screen-green)
  (display (screen-escape "32m")))

(define (screen-bright-green)
  (display (screen-escape "92m")))

(define (screen-black-bg)
  (display (screen-escape "40m")))

(define (screen-cursor-hide)
  (display (screen-escape "?25l")))

(define (screen-cursor-show)
  (display (screen-escape "?25h")))

(define (screen-alt-buffer)
  (display (screen-escape "?1049h")))

(define (screen-main-buffer)
  (display (screen-escape "?1049l")))

;;; ============================================================
;;; Gap Buffer (sgb- prefix to avoid conflict with pencil/text)
;;; ============================================================

(define-record-type <sgb>
  (make-gap-buffer-internal vec gap-start gap-end size)
  sgb?
  (vec sgb-vec set-sgb-vec!)
  (gap-start sgb-gap-start set-sgb-gap-start!)
  (gap-end sgb-gap-end set-sgb-gap-end!)
  (size sgb-size set-sgb-size!))

(define *default-gap-size* 256)
(define *initial-size* 1024)

(define (sgb-new #!optional (initial-size *initial-size*))
  (make-gap-buffer-internal
   (make-vector initial-size #\space)
   0 initial-size initial-size))

(define (sgb-length buf)
  (- (sgb-size buf) (- (sgb-gap-end buf) (sgb-gap-start buf))))

(define (sgb-gap-size buf)
  (- (sgb-gap-end buf) (sgb-gap-start buf)))

(define (sgb-cursor buf)
  (sgb-gap-start buf))

(define (sgb-grow! buf #!optional (min-gap *default-gap-size*))
  (when (< (sgb-gap-size buf) min-gap)
    (let* ((old-vec (sgb-vec buf))
           (old-size (sgb-size buf))
           (new-size (* 2 (+ old-size min-gap)))
           (new-vec (make-vector new-size #\space))
           (gap-start (sgb-gap-start buf))
           (gap-end (sgb-gap-end buf))
           (after-gap (- old-size gap-end))
           (new-gap-end (- new-size after-gap)))
      (do ((i 0 (+ i 1))) ((>= i gap-start))
        (vector-set! new-vec i (vector-ref old-vec i)))
      (do ((i 0 (+ i 1))) ((>= i after-gap))
        (vector-set! new-vec (+ new-gap-end i) (vector-ref old-vec (+ gap-end i))))
      (set-sgb-vec! buf new-vec)
      (set-sgb-gap-end! buf new-gap-end)
      (set-sgb-size! buf new-size))))

(define (sgb-move-gap! buf pos)
  (let ((gap-start (sgb-gap-start buf))
        (gap-end (sgb-gap-end buf))
        (vec (sgb-vec buf)))
    (cond
     ((= pos gap-start) #t)
     ((< pos gap-start)
      (let ((shift (- gap-start pos)))
        (do ((i (- gap-start 1) (- i 1))
             (j (- gap-end 1) (- j 1)))
            ((< i pos))
          (vector-set! vec j (vector-ref vec i)))
        (set-sgb-gap-start! buf pos)
        (set-sgb-gap-end! buf (- gap-end shift))))
     (else
      (let ((delta (- pos gap-start)))
        (do ((i 0 (+ i 1))) ((>= i delta))
          (vector-set! vec (+ gap-start i) (vector-ref vec (+ gap-end i))))
        (set-sgb-gap-start! buf pos)
        (set-sgb-gap-end! buf (+ gap-end delta)))))))

(define (sgb-insert! buf char)
  (sgb-grow! buf 1)
  (let ((gap-start (sgb-gap-start buf)))
    (vector-set! (sgb-vec buf) gap-start char)
    (set-sgb-gap-start! buf (+ gap-start 1))))

(define (sgb-insert-string! buf str)
  (for-each (lambda (c) (sgb-insert! buf c)) (string->list str)))

(define (sgb-delete-forward! buf #!optional (n 1))
  (let ((gap-end (sgb-gap-end buf))
        (size (sgb-size buf)))
    (let ((actual (min n (- size gap-end))))
      (set-sgb-gap-end! buf (+ gap-end actual))
      actual)))

(define (sgb-delete-backward! buf #!optional (n 1))
  (let ((gap-start (sgb-gap-start buf)))
    (let ((actual (min n gap-start)))
      (set-sgb-gap-start! buf (- gap-start actual))
      actual)))

(define (sgb-char-at buf pos)
  (let ((gap-start (sgb-gap-start buf))
        (gap-end (sgb-gap-end buf))
        (vec (sgb-vec buf)))
    (cond
     ((< pos gap-start) (vector-ref vec pos))
     (else (vector-ref vec (+ gap-end (- pos gap-start)))))))

(define (sgb->string buf)
  (let ((len (sgb-length buf)))
    (let ((result (make-string len)))
      (do ((i 0 (+ i 1))) ((>= i len) result)
        (string-set! result i (sgb-char-at buf i))))))

(define (string->sgb str)
  (let* ((len (string-length str))
         (buf (sgb-new (max *initial-size* (* 2 len)))))
    (sgb-insert-string! buf str)
    buf))

(define (sgb-goto! buf pos)
  (let ((len (sgb-length buf)))
    (sgb-move-gap! buf (max 0 (min pos len)))))

(define (sgb-forward! buf #!optional (n 1))
  (sgb-goto! buf (+ (sgb-cursor buf) n)))

(define (sgb-backward! buf #!optional (n 1))
  (sgb-goto! buf (- (sgb-cursor buf) n)))

;;; Line operations

(define (sgb-line-start buf pos)
  (let loop ((p pos))
    (cond
     ((<= p 0) 0)
     ((char=? (sgb-char-at buf (- p 1)) #\newline) p)
     (else (loop (- p 1))))))

(define (sgb-line-end buf pos)
  (let ((len (sgb-length buf)))
    (let loop ((p pos))
      (cond
       ((>= p len) len)
       ((char=? (sgb-char-at buf p) #\newline) p)
       (else (loop (+ p 1)))))))

(define (sgb-line-number buf pos)
  (let loop ((i 0) (line 1))
    (cond
     ((>= i pos) line)
     ((char=? (sgb-char-at buf i) #\newline) (loop (+ i 1) (+ line 1)))
     (else (loop (+ i 1) line)))))

(define (sgb-column buf pos)
  (+ 1 (- pos (sgb-line-start buf pos))))

(define (sgb-line-at buf line-num)
  (let ((len (sgb-length buf)))
    (let loop ((i 0) (line 1))
      (cond
       ((>= line line-num) i)
       ((>= i len) len)
       ((char=? (sgb-char-at buf i) #\newline) (loop (+ i 1) (+ line 1)))
       (else (loop (+ i 1) line))))))

(define (sgb-extract buf start end)
  "Extract text from start to end as string"
  (let* ((len (- end start))
         (result (make-string len)))
    (do ((i start (+ i 1))
         (j 0 (+ j 1)))
        ((>= i end) result)
      (string-set! result j (sgb-char-at buf i)))))

;;; ============================================================
;;; Kill Ring - Emacs-style clipboard with history
;;; ============================================================

(define *kill-ring* '())
(define *kill-ring-max* 60)
(define *kill-ring-index* 0)

(define (kill-ring-push str)
  "Add string to kill ring"
  (set! *kill-ring* (cons str (take-at-most *kill-ring* (- *kill-ring-max* 1))))
  (set! *kill-ring-index* 0))

(define (kill-ring-top)
  "Get most recent kill"
  (if (null? *kill-ring*) "" (car *kill-ring*)))

(define (kill-ring-pop)
  "Cycle to next item in kill ring"
  (when (not (null? *kill-ring*))
    (set! *kill-ring-index* (modulo (+ *kill-ring-index* 1) (length *kill-ring*))))
  (if (null? *kill-ring*)
      ""
      (list-ref *kill-ring* *kill-ring-index*)))

(define (take-at-most lst n)
  (if (or (null? lst) (<= n 0))
      '()
      (cons (car lst) (take-at-most (cdr lst) (- n 1)))))

;;; ============================================================
;;; Editor State
;;; ============================================================

(define-record-type <schemacs>
  (make-schemacs-internal buf filename modified mark
                          screen-top cursor-goal-col
                          rows cols minibuf-msg
                          last-command last-yank-size)
  schemacs?
  (buf sm-buf set-sm-buf!)
  (filename sm-filename set-sm-filename!)
  (modified sm-modified? set-sm-modified!)
  (mark sm-mark set-sm-mark!)                    ; position or #f
  (screen-top sm-screen-top set-sm-screen-top!)
  (cursor-goal-col sm-goal-col set-sm-goal-col!) ; for vertical movement
  (rows sm-rows set-sm-rows!)
  (cols sm-cols set-sm-cols!)
  (minibuf-msg sm-minibuf set-sm-minibuf!)
  (last-command sm-last-cmd set-sm-last-cmd!)
  (last-yank-size sm-yank-size set-sm-yank-size!))

(define (schemacs-new)
  (make-schemacs-internal
   (sgb-new)                             ; buffer
   #f                                   ; filename
   #f                                   ; modified
   #f                                   ; mark
   0                                    ; screen-top
   1                                    ; goal column
   (tty-rows)                           ; rows
   (tty-cols)                           ; cols
   ""                                   ; minibuffer message
   #f                                   ; last command
   0))                                  ; last yank size

;;; ============================================================
;;; Cursor Movement - Emacs style
;;; ============================================================

(define (sm-forward-char! ed #!optional (n 1))
  "C-f: Move forward n characters"
  (sgb-forward! (sm-buf ed) n)
  (set-sm-goal-col! ed (sgb-column (sm-buf ed) (sgb-cursor (sm-buf ed)))))

(define (sm-backward-char! ed #!optional (n 1))
  "C-b: Move backward n characters"
  (sgb-backward! (sm-buf ed) n)
  (set-sm-goal-col! ed (sgb-column (sm-buf ed) (sgb-cursor (sm-buf ed)))))

(define (sm-next-line! ed)
  "C-n: Move to next line, preserving column"
  (let* ((buf (sm-buf ed))
         (pos (sgb-cursor buf))
         (goal (sm-goal-col ed))
         (line-end (sgb-line-end buf pos))
         (len (sgb-length buf)))
    (when (< line-end len)
      (let* ((next-start (+ line-end 1))
             (next-end (sgb-line-end buf next-start))
             (next-len (- next-end next-start))
             (new-col (min (- goal 1) next-len)))
        (sgb-goto! buf (+ next-start new-col))))))

(define (sm-previous-line! ed)
  "C-p: Move to previous line, preserving column"
  (let* ((buf (sm-buf ed))
         (pos (sgb-cursor buf))
         (goal (sm-goal-col ed))
         (line-start (sgb-line-start buf pos)))
    (when (> line-start 0)
      (let* ((prev-end (- line-start 1))
             (prev-start (sgb-line-start buf prev-end))
             (prev-len (- prev-end prev-start))
             (new-col (min (- goal 1) prev-len)))
        (sgb-goto! buf (+ prev-start new-col))))))

(define (sm-beginning-of-line! ed)
  "C-a: Move to beginning of line"
  (let ((buf (sm-buf ed)))
    (sgb-goto! buf (sgb-line-start buf (sgb-cursor buf)))
    (set-sm-goal-col! ed 1)))

(define (sm-end-of-line! ed)
  "C-e: Move to end of line"
  (let ((buf (sm-buf ed)))
    (sgb-goto! buf (sgb-line-end buf (sgb-cursor buf)))
    (set-sm-goal-col! ed (sgb-column buf (sgb-cursor buf)))))

(define (sm-forward-word! ed)
  "M-f: Move forward one word"
  (let* ((buf (sm-buf ed))
         (len (sgb-length buf))
         (pos (sgb-cursor buf)))
    ;; Skip non-word chars, then word chars
    (let loop ((p pos))
      (cond
       ((>= p len) (sgb-goto! buf len))
       ((char-alphabetic? (sgb-char-at buf p))
        ;; In word, find end
        (let word ((q p))
          (cond
           ((>= q len) (sgb-goto! buf len))
           ((not (char-alphabetic? (sgb-char-at buf q)))
            (sgb-goto! buf q))
           (else (word (+ q 1))))))
       (else (loop (+ p 1)))))
    (set-sm-goal-col! ed (sgb-column buf (sgb-cursor buf)))))

(define (sm-backward-word! ed)
  "M-b: Move backward one word"
  (let* ((buf (sm-buf ed))
         (pos (sgb-cursor buf)))
    (when (> pos 0)
      (let loop ((p (- pos 1)))
        (cond
         ((<= p 0) (sgb-goto! buf 0))
         ((char-alphabetic? (sgb-char-at buf p))
          ;; In word, find start
          (let word ((q p))
            (cond
             ((<= q 0) (sgb-goto! buf 0))
             ((not (char-alphabetic? (sgb-char-at buf (- q 1))))
              (sgb-goto! buf q))
             (else (word (- q 1))))))
         (else (loop (- p 1))))))
    (set-sm-goal-col! ed (sgb-column buf (sgb-cursor buf)))))

(define (sm-beginning-of-buffer! ed)
  "M-<: Move to beginning of buffer"
  (sgb-goto! (sm-buf ed) 0)
  (set-sm-goal-col! ed 1))

(define (sm-end-of-buffer! ed)
  "M->: Move to end of buffer"
  (let ((buf (sm-buf ed)))
    (sgb-goto! buf (sgb-length buf))
    (set-sm-goal-col! ed (sgb-column buf (sgb-cursor buf)))))

(define (sm-scroll-up! ed)
  "C-v: Scroll down (move forward) one page"
  (let ((visible (- (sm-rows ed) 2)))
    (do ((i 0 (+ i 1))) ((>= i visible))
      (sm-next-line! ed))))

(define (sm-scroll-down! ed)
  "M-v: Scroll up (move backward) one page"
  (let ((visible (- (sm-rows ed) 2)))
    (do ((i 0 (+ i 1))) ((>= i visible))
      (sm-previous-line! ed))))

;;; ============================================================
;;; Editing Commands
;;; ============================================================

(define (sm-delete-char! ed)
  "C-d: Delete character at point"
  (let ((buf (sm-buf ed)))
    (when (< (sgb-cursor buf) (sgb-length buf))
      (sgb-delete-forward! buf)
      (set-sm-modified! ed #t))))

(define (sm-delete-backward-char! ed)
  "DEL: Delete character before point"
  (let ((buf (sm-buf ed)))
    (when (> (sgb-cursor buf) 0)
      (sgb-delete-backward! buf)
      (set-sm-modified! ed #t))))

(define (sm-kill-line! ed)
  "C-k: Kill to end of line"
  (let* ((buf (sm-buf ed))
         (pos (sgb-cursor buf))
         (eol (sgb-line-end buf pos)))
    (if (= pos eol)
        ;; At end of line, kill the newline
        (when (< pos (sgb-length buf))
          (kill-ring-push "\n")
          (sgb-delete-forward! buf)
          (set-sm-modified! ed #t))
        ;; Kill to end of line
        (let ((text (sgb-extract buf pos eol)))
          (kill-ring-push text)
          (sgb-delete-forward! buf (- eol pos))
          (set-sm-modified! ed #t)))))

(define (sm-kill-region! ed)
  "C-w: Kill region (between mark and point)"
  (let ((mark (sm-mark ed))
        (buf (sm-buf ed)))
    (when mark
      (let* ((pos (sgb-cursor buf))
             (start (min mark pos))
             (end (max mark pos))
             (text (sgb-extract buf start end)))
        (kill-ring-push text)
        (sgb-goto! buf start)
        (sgb-delete-forward! buf (- end start))
        (set-sm-mark! ed #f)
        (set-sm-modified! ed #t)))))

(define (sm-copy-region! ed)
  "M-w: Copy region to kill ring without deleting"
  (let ((mark (sm-mark ed))
        (buf (sm-buf ed)))
    (when mark
      (let* ((pos (sgb-cursor buf))
             (start (min mark pos))
             (end (max mark pos))
             (text (sgb-extract buf start end)))
        (kill-ring-push text)
        (set-sm-mark! ed #f)
        (set-sm-minibuf! ed "Region copied")))))

(define (sm-yank! ed)
  "C-y: Yank (paste) from kill ring"
  (let ((text (kill-ring-top))
        (buf (sm-buf ed)))
    (when (> (string-length text) 0)
      (sgb-insert-string! buf text)
      (set-sm-modified! ed #t)
      (set-sm-yank-size! ed (string-length text)))))

(define (sm-yank-pop! ed)
  "M-y: Replace just-yanked text with next kill ring entry"
  (when (eq? (sm-last-cmd ed) 'yank)
    (let* ((buf (sm-buf ed))
           (old-size (sm-yank-size ed)))
      ;; Delete what we just yanked
      (sgb-backward! buf old-size)
      (sgb-delete-forward! buf old-size)
      ;; Yank next item
      (let ((text (kill-ring-pop)))
        (sgb-insert-string! buf text)
        (set-sm-yank-size! ed (string-length text))))))

(define (sm-set-mark! ed)
  "C-space: Set mark at point"
  (set-sm-mark! ed (sgb-cursor (sm-buf ed)))
  (set-sm-minibuf! ed "Mark set"))

(define (sm-exchange-point-and-mark! ed)
  "C-x C-x: Exchange point and mark"
  (let ((mark (sm-mark ed))
        (buf (sm-buf ed)))
    (when mark
      (let ((pos (sgb-cursor buf)))
        (set-sm-mark! ed pos)
        (sgb-goto! buf mark)
        (set-sm-goal-col! ed (sgb-column buf (sgb-cursor buf)))))))

(define (sm-insert-char! ed char)
  "Self-insert character"
  (sgb-insert! (sm-buf ed) char)
  (set-sm-modified! ed #t))

(define (sm-newline! ed)
  "RET: Insert newline"
  (sgb-insert! (sm-buf ed) #\newline)
  (set-sm-modified! ed #t))

(define (sm-kill-word! ed)
  "M-d: Kill word forward"
  (let* ((buf (sm-buf ed))
         (start (sgb-cursor buf))
         (len (sgb-length buf)))
    ;; Find word end
    (let loop ((p start))
      (cond
       ((>= p len)
        (let ((text (sgb-extract buf start len)))
          (kill-ring-push text)
          (sgb-delete-forward! buf (- len start))
          (set-sm-modified! ed #t)))
       ((and (> p start) (not (char-alphabetic? (sgb-char-at buf p))))
        (let ((text (sgb-extract buf start p)))
          (kill-ring-push text)
          (sgb-delete-forward! buf (- p start))
          (set-sm-modified! ed #t)))
       (else (loop (+ p 1)))))))

(define (sm-backward-kill-word! ed)
  "M-DEL: Kill word backward"
  (let* ((buf (sm-buf ed))
         (end (sgb-cursor buf)))
    (when (> end 0)
      (let loop ((p (- end 1)))
        (cond
         ((<= p 0)
          (let ((text (sgb-extract buf 0 end)))
            (kill-ring-push text)
            (sgb-goto! buf 0)
            (sgb-delete-forward! buf end)
            (set-sm-modified! ed #t)))
         ((and (< p (- end 1)) (not (char-alphabetic? (sgb-char-at buf p))))
          (let* ((start (+ p 1))
                 (text (sgb-extract buf start end)))
            (kill-ring-push text)
            (sgb-goto! buf start)
            (sgb-delete-forward! buf (- end start))
            (set-sm-modified! ed #t)))
         (else (loop (- p 1))))))))

;;; ============================================================
;;; Display
;;; ============================================================

(define (sm-ensure-visible! ed)
  "Scroll if cursor is outside visible area"
  (let* ((buf (sm-buf ed))
         (line (sgb-line-number buf (sgb-cursor buf)))
         (top (sm-screen-top ed))
         (visible (- (sm-rows ed) 2)))
    (cond
     ((< line (+ top 1))
      (set-sm-screen-top! ed (max 0 (- line 1))))
     ((> line (+ top visible))
      (set-sm-screen-top! ed (- line visible))))))

(define (sm-recenter! ed)
  "C-l: Recenter display around cursor"
  (let* ((buf (sm-buf ed))
         (line (sgb-line-number buf (sgb-cursor buf)))
         (visible (- (sm-rows ed) 2))
         (center (quotient visible 2)))
    (set-sm-screen-top! ed (max 0 (- line center)))))

(define (sm-draw! ed)
  "Redraw screen"
  (sm-ensure-visible! ed)
  (let* ((buf (sm-buf ed))
         (rows (sm-rows ed))
         (cols (sm-cols ed))
         (top (sm-screen-top ed))
         (visible (- rows 2))
         (mark (sm-mark ed))
         (pos (sgb-cursor buf)))

    (screen-cursor-hide)
    (screen-home)
    (screen-black-bg)
    (screen-green)

    ;; Draw text
    (do ((screen-row 1 (+ screen-row 1))
         (line (+ top 1) (+ line 1)))
        ((> screen-row visible))
      (screen-goto screen-row 1)
      (screen-clear-eol)
      (let ((line-start (sgb-line-at buf line)))
        (when (< line-start (sgb-length buf))
          (let* ((line-end (sgb-line-end buf line-start))
                 (line-len (- line-end line-start))
                 (display-len (min line-len (- cols 1))))
            ;; Check for region highlight
            (if mark
                (let ((region-start (min mark pos))
                      (region-end (max mark pos)))
                  (do ((i 0 (+ i 1))) ((>= i display-len))
                    (let ((char-pos (+ line-start i)))
                      (if (and (>= char-pos region-start) (< char-pos region-end))
                          (begin (screen-reverse)
                                 (display (sgb-char-at buf char-pos))
                                 (screen-reset)
                                 (screen-green))
                          (display (sgb-char-at buf char-pos))))))
                ;; No region
                (do ((i 0 (+ i 1))) ((>= i display-len))
                  (display (sgb-char-at buf (+ line-start i)))))))))

    ;; Mode line
    (screen-goto (- rows 1) 1)
    (screen-reverse)
    (let* ((filename (or (sm-filename ed) "*scratch*"))
           (modified (if (sm-modified? ed) "**" "--"))
           (line-num (sgb-line-number buf pos))
           (col-num (sgb-column buf pos))
           (percent (if (= (sgb-length buf) 0)
                        "All"
                        (let ((p (quotient (* 100 pos) (sgb-length buf))))
                          (cond ((= pos 0) "Top")
                                ((= pos (sgb-length buf)) "Bot")
                                (else (format #f "~a%" p))))))
           (mode-str (format #f "-~a- ~a   (~a,~a)  ~a"
                            modified filename line-num col-num percent)))
      (display mode-str)
      (display (make-string (max 0 (- cols (string-length mode-str))) #\-)))
    (screen-reset)

    ;; Minibuffer
    (screen-goto rows 1)
    (screen-clear-eol)
    (screen-green)
    (display (sm-minibuf ed))

    ;; Position cursor
    (let ((line (sgb-line-number buf pos))
          (col (sgb-column buf pos)))
      (screen-goto (- line (sm-screen-top ed)) col))
    (screen-cursor-show)
    (flush-output)))

;;; ============================================================
;;; File Operations
;;; ============================================================

(define (sm-find-file! ed filename)
  "C-x C-f: Find (open) file"
  (if (file-exists? filename)
      (let ((content (with-input-from-file filename read-string)))
        (set-sm-buf! ed (string->sgb content))
        (set-sm-filename! ed filename)
        (set-sm-modified! ed #f)
        (sgb-goto! (sm-buf ed) 0)
        (set-sm-screen-top! ed 0)
        (set-sm-minibuf! ed (format #f "Loaded ~a" filename)))
      (begin
        (set-sm-filename! ed filename)
        (set-sm-minibuf! ed "(New file)"))))

(define (sm-save-file! ed)
  "C-x C-s: Save file"
  (let ((fname (sm-filename ed)))
    (if fname
        (begin
          (with-output-to-file fname
            (lambda () (display (sgb->string (sm-buf ed)))))
          (set-sm-modified! ed #f)
          (set-sm-minibuf! ed (format #f "Wrote ~a" fname)))
        (set-sm-minibuf! ed "No file name"))))

(define (sm-write-file! ed filename)
  "C-x C-w: Write file (save as)"
  (with-output-to-file filename
    (lambda () (display (sgb->string (sm-buf ed)))))
  (set-sm-filename! ed filename)
  (set-sm-modified! ed #f)
  (set-sm-minibuf! ed (format #f "Wrote ~a" filename)))

;;; ============================================================
;;; Input Handling
;;; ============================================================

(define (sm-read-key)
  "Read a key, handling escape sequences"
  (let ((c (tty-raw-char)))
    (cond
     ((= c 27)  ; ESC - could be Meta or escape sequence
      (if (tty-char-ready? 50)
          (let ((c2 (tty-raw-char)))
            (cond
             ((= c2 91)  ; [ - ANSI sequence
              (let ((c3 (tty-raw-char)))
                (case c3
                  ((65) 'up)
                  ((66) 'down)
                  ((67) 'right)
                  ((68) 'left)
                  ((72) 'home)
                  ((70) 'end)
                  ((51) (tty-raw-char) 'delete)
                  ((53) (tty-raw-char) 'page-up)
                  ((54) (tty-raw-char) 'page-down)
                  (else 'unknown))))
             ;; Meta key - ESC followed by char
             ((= c2 27) 'escape)                  ; ESC ESC
             ((= c2 102) '(meta . #\f))           ; M-f
             ((= c2 98) '(meta . #\b))            ; M-b
             ((= c2 100) '(meta . #\d))           ; M-d
             ((= c2 119) '(meta . #\w))           ; M-w
             ((= c2 121) '(meta . #\y))           ; M-y
             ((= c2 118) '(meta . #\v))           ; M-v
             ((= c2 60) '(meta . #\<))            ; M-<
             ((= c2 62) '(meta . #\>))            ; M->
             ((= c2 37) '(meta . #\%))            ; M-%
             ((= c2 120) '(meta . #\x))           ; M-x
             ((= c2 127) '(meta . backspace))     ; M-DEL
             (else `(meta . ,(integer->char c2)))))
          'escape))
     ((= c 127) 'backspace)
     ((= c 13) 'enter)
     ((= c 9) 'tab)
     ((= c 0) '(ctrl . #\space))  ; C-space
     ((< c 32) (cons 'ctrl (integer->char (+ c 64))))
     (else (integer->char c)))))

(define (sm-minibuf-read ed prompt)
  "Read a line from minibuffer"
  (let ((rows (sm-rows ed)))
    (screen-goto rows 1)
    (screen-clear-eol)
    (screen-bright-green)
    (display prompt)
    (screen-reset)
    (screen-green)
    (flush-output)
    (tty-set-cooked)
    (let ((line (read-line)))
      (tty-set-raw)
      line)))

(define (sm-minibuf-ask ed prompt)
  "Ask yes/no question in minibuffer"
  (let ((rows (sm-rows ed)))
    (screen-goto rows 1)
    (screen-clear-eol)
    (screen-bright-green)
    (display prompt)
    (display " (y/n) ")
    (screen-reset)
    (flush-output)
    (let ((c (tty-raw-char)))
      (or (= c 121) (= c 89)))))

;;; ============================================================
;;; Search
;;; ============================================================

(define *last-search* "")

(define (sm-isearch! ed)
  "C-s: Incremental search forward"
  (let ((pattern (sm-minibuf-read ed "I-search: ")))
    (when (and pattern (> (string-length pattern) 0))
      (set! *last-search* pattern)
      (sm-search-forward! ed pattern))))

(define (sm-search-forward! ed pattern)
  "Search forward for pattern"
  (let* ((buf (sm-buf ed))
         (len (sgb-length buf))
         (start (+ (sgb-cursor buf) 1))
         (plen (string-length pattern)))
    (let search ((pos start))
      (cond
       ((> pos (- len plen))
        ;; Wrap around
        (let wrap ((pos 0))
          (cond
           ((>= pos start)
            (set-sm-minibuf! ed "Failing I-search"))
           ((string-match-at-gb? buf pos pattern plen)
            (sgb-goto! buf pos)
            (set-sm-goal-col! ed (sgb-column buf pos))
            (set-sm-minibuf! ed pattern))
           (else (wrap (+ pos 1))))))
       ((string-match-at-gb? buf pos pattern plen)
        (sgb-goto! buf pos)
        (set-sm-goal-col! ed (sgb-column buf pos))
        (set-sm-minibuf! ed pattern))
       (else (search (+ pos 1)))))))

(define (string-match-at-gb? buf pos pattern plen)
  "Check if pattern matches at position"
  (let ((len (sgb-length buf)))
    (and (<= (+ pos plen) len)
         (let loop ((i 0))
           (cond
            ((>= i plen) #t)
            ((char=? (sgb-char-at buf (+ pos i)) (string-ref pattern i))
             (loop (+ i 1)))
            (else #f))))))

(define (sm-isearch-backward! ed)
  "C-r: Incremental search backward"
  (let ((pattern (sm-minibuf-read ed "I-search backward: ")))
    (when (and pattern (> (string-length pattern) 0))
      (set! *last-search* pattern)
      (sm-search-backward! ed pattern))))

(define (sm-search-backward! ed pattern)
  "Search backward for pattern"
  (let* ((buf (sm-buf ed))
         (start (- (sgb-cursor buf) 1))
         (plen (string-length pattern)))
    (let search ((pos start))
      (cond
       ((< pos 0)
        (set-sm-minibuf! ed "Failing I-search backward"))
       ((string-match-at-gb? buf pos pattern plen)
        (sgb-goto! buf pos)
        (set-sm-goal-col! ed (sgb-column buf pos))
        (set-sm-minibuf! ed pattern))
       (else (search (- pos 1)))))))

;;; ============================================================
;;; M-x Command System
;;; ============================================================

(define *mx-commands*
  '(("goto-line" . sm-mx-goto-line)
    ("what-cursor-position" . sm-mx-what-cursor)
    ("count-words" . sm-mx-count-words)
    ("describe-key" . sm-mx-describe-key)))

(define (sm-execute-extended-command! ed)
  "M-x: Execute extended command"
  (let ((cmd (sm-minibuf-read ed "M-x ")))
    (when (and cmd (> (string-length cmd) 0))
      (let ((entry (assoc cmd *mx-commands*)))
        (if entry
            ((cdr entry) ed)
            (set-sm-minibuf! ed (format #f "[No match: ~a]" cmd)))))))

(define (sm-mx-goto-line ed)
  "M-x goto-line"
  (let ((line-str (sm-minibuf-read ed "Goto line: ")))
    (when (and line-str (> (string-length line-str) 0))
      (let ((line (string->number line-str)))
        (when line
          (let ((buf (sm-buf ed)))
            (sgb-goto! buf (sgb-line-at buf line))
            (set-sm-goal-col! ed 1)))))))

(define (sm-mx-what-cursor ed)
  "M-x what-cursor-position"
  (let* ((buf (sm-buf ed))
         (pos (sgb-cursor buf))
         (len (sgb-length buf)))
    (if (< pos len)
        (let ((c (sgb-char-at buf pos)))
          (set-sm-minibuf! ed
                           (format #f "Char: ~a (0~o, ~a, 0x~x) point=~a of ~a"
                                   (if (char-graphic? c) (string c) "^?")
                                   (char->integer c)
                                   (char->integer c)
                                   (char->integer c)
                                   pos len)))
        (set-sm-minibuf! ed (format #f "Point=~a of ~a (EOB)" pos len)))))

(define (sm-mx-count-words ed)
  "M-x count-words"
  (let* ((buf (sm-buf ed))
         (len (sgb-length buf)))
    (let loop ((i 0) (words 0) (in-word #f))
      (if (>= i len)
          (set-sm-minibuf! ed (format #f "~a words" words))
          (let ((c (sgb-char-at buf i)))
            (if (char-alphabetic? c)
                (loop (+ i 1) (if in-word words (+ words 1)) #t)
                (loop (+ i 1) words #f)))))))

(define (sm-mx-describe-key ed)
  "M-x describe-key"
  (set-sm-minibuf! ed "Type a key: ")
  (sm-draw! ed)
  (let ((key (sm-read-key)))
    (set-sm-minibuf! ed (format #f "~a is ~a" key (key->command key)))))

(define (key->command key)
  "Return command name for key"
  (cond
   ((equal? key '(ctrl . #\F)) "forward-char")
   ((equal? key '(ctrl . #\B)) "backward-char")
   ((equal? key '(ctrl . #\N)) "next-line")
   ((equal? key '(ctrl . #\P)) "previous-line")
   ((equal? key '(ctrl . #\A)) "beginning-of-line")
   ((equal? key '(ctrl . #\E)) "end-of-line")
   ((equal? key '(ctrl . #\D)) "delete-char")
   ((equal? key '(ctrl . #\K)) "kill-line")
   ((equal? key '(ctrl . #\Y)) "yank")
   ((equal? key '(ctrl . #\W)) "kill-region")
   ((equal? key '(ctrl . #\space)) "set-mark-command")
   ((equal? key '(ctrl . #\S)) "isearch-forward")
   ((equal? key '(ctrl . #\R)) "isearch-backward")
   ((equal? key '(ctrl . #\G)) "keyboard-quit")
   ((equal? key '(ctrl . #\L)) "recenter")
   ((equal? key '(ctrl . #\V)) "scroll-up")
   ((equal? key '(meta . #\v)) "scroll-down")
   ((equal? key '(meta . #\f)) "forward-word")
   ((equal? key '(meta . #\b)) "backward-word")
   ((equal? key '(meta . #\d)) "kill-word")
   ((equal? key '(meta . #\w)) "copy-region-as-kill")
   ((equal? key '(meta . #\y)) "yank-pop")
   ((equal? key '(meta . #\<)) "beginning-of-buffer")
   ((equal? key '(meta . #\>)) "end-of-buffer")
   ((equal? key '(meta . #\x)) "execute-extended-command")
   (else "self-insert-command")))

;;; ============================================================
;;; Main Loop
;;; ============================================================

(define (schemacs-run ed)
  "Main editor loop"
  (tty-flush-input)  ; Clear any buffered garbage
  (tty-set-raw)
  (screen-alt-buffer)
  (screen-clear)

  (let loop ()
    (sm-draw! ed)
    (let ((key (sm-read-key)))
      ;; Clear minibuffer message unless it's an error
      (unless (string-prefix? "[" (sm-minibuf ed))
        (set-sm-minibuf! ed ""))

      (cond
       ;; C-x prefix
       ((equal? key '(ctrl . #\X))
        (set-sm-minibuf! ed "C-x-")
        (sm-draw! ed)
        (let ((key2 (sm-read-key)))
          (cond
           ((equal? key2 '(ctrl . #\C))  ; C-x C-c = quit
            (if (and (sm-modified? ed)
                     (not (sm-minibuf-ask ed "Buffer modified; kill anyway?")))
                (loop)
                (void)))
           ((equal? key2 '(ctrl . #\S))  ; C-x C-s = save
            (sm-save-file! ed) (loop))
           ((equal? key2 '(ctrl . #\F))  ; C-x C-f = find file
            (let ((fname (sm-minibuf-read ed "Find file: ")))
              (when (and fname (> (string-length fname) 0))
                (sm-find-file! ed fname)))
            (loop))
           ((equal? key2 '(ctrl . #\W))  ; C-x C-w = write file
            (let ((fname (sm-minibuf-read ed "Write file: ")))
              (when (and fname (> (string-length fname) 0))
                (sm-write-file! ed fname)))
            (loop))
           ((equal? key2 '(ctrl . #\X))  ; C-x C-x = exchange point and mark
            (sm-exchange-point-and-mark! ed) (loop))
           (else
            (set-sm-minibuf! ed (format #f "C-x ~a is undefined" key2))
            (loop)))))

       ;; Cancel
       ((equal? key '(ctrl . #\G))
        (set-sm-mark! ed #f)
        (set-sm-minibuf! ed "Quit")
        (loop))

       ;; Movement
       ((or (equal? key '(ctrl . #\F)) (eq? key 'right))
        (sm-forward-char! ed) (set-sm-last-cmd! ed 'move) (loop))
       ((or (equal? key '(ctrl . #\B)) (eq? key 'left))
        (sm-backward-char! ed) (set-sm-last-cmd! ed 'move) (loop))
       ((or (equal? key '(ctrl . #\N)) (eq? key 'down))
        (sm-next-line! ed) (set-sm-last-cmd! ed 'move) (loop))
       ((or (equal? key '(ctrl . #\P)) (eq? key 'up))
        (sm-previous-line! ed) (set-sm-last-cmd! ed 'move) (loop))
       ((or (equal? key '(ctrl . #\A)) (eq? key 'home))
        (sm-beginning-of-line! ed) (set-sm-last-cmd! ed 'move) (loop))
       ((equal? key '(ctrl . #\E))
        (sm-end-of-line! ed) (set-sm-last-cmd! ed 'move) (loop))
       ((eq? key 'end)
        (sm-end-of-line! ed) (set-sm-last-cmd! ed 'move) (loop))
       ((equal? key '(meta . #\f))
        (sm-forward-word! ed) (set-sm-last-cmd! ed 'move) (loop))
       ((equal? key '(meta . #\b))
        (sm-backward-word! ed) (set-sm-last-cmd! ed 'move) (loop))
       ((equal? key '(meta . #\<))
        (sm-beginning-of-buffer! ed) (set-sm-last-cmd! ed 'move) (loop))
       ((equal? key '(meta . #\>))
        (sm-end-of-buffer! ed) (set-sm-last-cmd! ed 'move) (loop))
       ((or (equal? key '(ctrl . #\V)) (eq? key 'page-down))
        (sm-scroll-up! ed) (set-sm-last-cmd! ed 'move) (loop))
       ((or (equal? key '(meta . #\v)) (eq? key 'page-up))
        (sm-scroll-down! ed) (set-sm-last-cmd! ed 'move) (loop))

       ;; Editing
       ((equal? key '(ctrl . #\D))
        (sm-delete-char! ed) (set-sm-last-cmd! ed 'delete) (loop))
       ((or (eq? key 'backspace) (eq? key 'delete))
        (sm-delete-backward-char! ed) (set-sm-last-cmd! ed 'delete) (loop))
       ((equal? key '(ctrl . #\K))
        (sm-kill-line! ed) (set-sm-last-cmd! ed 'kill) (loop))
       ((equal? key '(ctrl . #\W))
        (sm-kill-region! ed) (set-sm-last-cmd! ed 'kill) (loop))
       ((equal? key '(meta . #\w))
        (sm-copy-region! ed) (set-sm-last-cmd! ed 'copy) (loop))
       ((equal? key '(ctrl . #\Y))
        (sm-yank! ed) (set-sm-last-cmd! ed 'yank) (loop))
       ((equal? key '(meta . #\y))
        (sm-yank-pop! ed) (set-sm-last-cmd! ed 'yank) (loop))
       ((equal? key '(meta . #\d))
        (sm-kill-word! ed) (set-sm-last-cmd! ed 'kill) (loop))
       ((equal? key '(meta . backspace))
        (sm-backward-kill-word! ed) (set-sm-last-cmd! ed 'kill) (loop))
       ((eq? key 'enter)
        (sm-newline! ed) (set-sm-last-cmd! ed 'insert) (loop))

       ;; Mark
       ((equal? key '(ctrl . #\space))
        (sm-set-mark! ed) (set-sm-last-cmd! ed 'mark) (loop))

       ;; Search
       ((equal? key '(ctrl . #\S))
        (sm-isearch! ed) (set-sm-last-cmd! ed 'search) (loop))
       ((equal? key '(ctrl . #\R))
        (sm-isearch-backward! ed) (set-sm-last-cmd! ed 'search) (loop))

       ;; Display
       ((equal? key '(ctrl . #\L))
        (sm-recenter! ed) (screen-clear) (set-sm-last-cmd! ed 'display) (loop))

       ;; Extended commands
       ((equal? key '(meta . #\x))
        (sm-execute-extended-command! ed) (set-sm-last-cmd! ed 'mx) (loop))

       ;; Self-insert
       ((char? key)
        (sm-insert-char! ed key) (set-sm-last-cmd! ed 'insert) (loop))

       ;; Unknown
       (else
        (set-sm-minibuf! ed (format #f "~a is undefined" key))
        (loop)))))

  ;; Cleanup
  (screen-main-buffer)
  (screen-reset)
  (tty-set-cooked)
  (void))

;;; ============================================================
;;; Entry Point
;;; ============================================================

(define (schemacs #!optional arg)
  "Start Schemacs editor.
   (schemacs)              - new *scratch* buffer
   (schemacs \"file.txt\")   - edit file"
  (let ((ed (schemacs-new)))
    (when arg
      (sm-find-file! ed arg))
    (schemacs-run ed)))

;; Run if executed directly
(when (and (pair? (command-line-arguments))
           (not (string-prefix? "-" (car (command-line-arguments)))))
  (schemacs (car (command-line-arguments))))

(when (condition-case *verbose-load* ((exn) #f))
  (print "Schemacs loaded. (schemacs) to edit, C-x C-c to quit."))
