#!/usr/bin/env csi -s
;;; Electric Pencil - Character-oriented word processor
;;;
;;; A tribute to Michael Shrayer's 1976 Electric Pencil,
;;; the first word processor for microcomputers.
;;;
;;; Gap buffer implementation for efficient editing.
;;; Full-screen ANSI terminal control.
;;;
;;; Heritage:
;;;   1976  Michael Shrayer writes Electric Pencil on MITS Altair (8K RAM)
;;;   1977  Ports to TRS-80, Apple II, CP/M - launches microcomputer word processing
;;;   2026  Reborn in Cyberspace Scheme as bootstrap editor
;;;
;;; See also: teco.scm - Dan Murphy's TECO (1962), foundation of EMACS
;;;
;;; The Electric Pencil exists for bootstrapping - when Emacs isn't available,
;;; when you're on a minimal system, when you need to edit and nothing else
;;; is there. Like nano for Unix, but for Cyberspace.
;;;
;;; Commands (Ctrl-key):
;;;   Movement (WASDZX diamond):
;;;     Ctrl-W  up          Ctrl-A  left
;;;     Ctrl-S  down        Ctrl-D  right
;;;     Ctrl-Z  start line  Ctrl-X  end line
;;;
;;;   Editing:
;;;     Ctrl-I  toggle insert/overwrite
;;;     Ctrl-G  delete char
;;;     Ctrl-T  delete word
;;;     Ctrl-Y  delete line
;;;
;;;   Block:
;;;     Ctrl-B  begin block
;;;     Ctrl-K  end block (kopy to clipboard)
;;;     Ctrl-V  paste block
;;;     Ctrl-U  unmark block
;;;
;;;   Search:
;;;     Ctrl-F  find
;;;     Ctrl-R  replace
;;;     Ctrl-N  next occurrence
;;;
;;;   File:
;;;     Ctrl-O  open (from vault)
;;;     Ctrl-P  put (save to vault)
;;;     Ctrl-Q  quit
;;;
;;;   Display:
;;;     Ctrl-L  refresh screen
;;;     Ctrl-E  toggle word wrap

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

(load "text.scm")
(import text)

;;; ============================================================
;;; Screen Module - ANSI Terminal Control
;;; ============================================================

(define ESC (integer->char 27))

(define (screen-escape . args)
  "Build ANSI escape sequence"
  (apply string-append (cons (string ESC #\[) args)))

;; Cursor positioning
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

;; Clearing
(define (screen-clear)
  (display (screen-escape "2J"))
  (screen-home))

(define (screen-clear-line)
  (display (screen-escape "2K")))

(define (screen-clear-eol)
  (display (screen-escape "K")))

(define (screen-clear-eos)
  (display (screen-escape "J")))

;; Attributes
(define (screen-reset)
  (display (screen-escape "0m")))

(define (screen-bold)
  (display (screen-escape "1m")))

(define (screen-dim)
  (display (screen-escape "2m")))

(define (screen-reverse)
  (display (screen-escape "7m")))

;; Colors (phosphor green theme)
(define (screen-green)
  (display (screen-escape "32m")))

(define (screen-bright-green)
  (display (screen-escape "92m")))

(define (screen-black-bg)
  (display (screen-escape "40m")))

;; Cursor visibility
(define (screen-cursor-hide)
  (display (screen-escape "?25l")))

(define (screen-cursor-show)
  (display (screen-escape "?25h")))

;; Save/restore cursor
(define (screen-save-cursor)
  (display (screen-escape "s")))

(define (screen-restore-cursor)
  (display (screen-escape "u")))

;; Alternative screen buffer (like vi/less)
(define (screen-alt-buffer)
  (display (screen-escape "?1049h")))

(define (screen-main-buffer)
  (display (screen-escape "?1049l")))

;; Scroll region
(define (screen-scroll-region top bottom)
  (display (screen-escape (number->string top) ";" (number->string bottom) "r")))

(define (screen-scroll-reset)
  (display (screen-escape "r")))

;;; ============================================================
;;; Gap Buffer - Efficient Text Storage
;;; ============================================================
;;;
;;; Text is stored in a vector with a gap at the cursor position.
;;; Operations at cursor are O(1), moving gap is O(n) but amortized.
;;;
;;; Gap buffer operations now delegate to text.scm
;;; These wrappers maintain API compatibility during transition

(define (gb-length t) (text-length t))
(define (gb-cursor t) (text-cursor t))
(define (gb-char-at t pos) (text-char-at t pos))
(define (gb->string t) (text->string t))
(define (string->gb str) (text-from-string str))
(define (gb-goto! t pos) (text-goto! t pos))
(define (gb-forward! t #!optional (n 1)) (text-move! t n))
(define (gb-backward! t #!optional (n 1)) (text-move! t (- n)))
(define (gb-insert! t char) (text-insert! t (string char)))
(define (gb-insert-string! t str) (text-insert! t str))
(define (gb-delete-forward! t #!optional (n 1)) (text-delete! t n))
(define (gb-delete-backward! t #!optional (n 1))
  (when (> (text-cursor t) 0)
    (text-move! t (- (min n (text-cursor t))))
    (text-delete! t (min n (text-cursor t)))))

;; For overwrite mode - set char at position
(define (gb-set-char! t pos char)
  (let ((saved (text-cursor t)))
    (text-goto! t pos)
    (text-delete! t 1)
    (text-insert! t (string char))
    (text-goto! t saved)))

;;; ============================================================
;;; Editor State
;;; ============================================================

(define-record-type <editor>
  (make-editor-internal txt filename insert-mode
                        screen-top cursor-row cursor-col
                        mark-start mark-end clipboard
                        search-string wrap-mode
                        rows cols status-msg novice)
  editor?
  (txt editor-text set-editor-text!)      ; text object (was buf)
  (filename editor-filename set-editor-filename!)
  (insert-mode editor-insert-mode? set-editor-insert-mode!)
  (screen-top editor-screen-top set-editor-screen-top!)
  (cursor-row editor-cursor-row set-editor-cursor-row!)
  (cursor-col editor-cursor-col set-editor-cursor-col!)
  (mark-start editor-mark-start set-editor-mark-start!)
  (mark-end editor-mark-end set-editor-mark-end!)
  (clipboard editor-clipboard set-editor-clipboard!)
  (search-string editor-search-string set-editor-search-string!)
  (wrap-mode editor-wrap-mode? set-editor-wrap-mode!)
  (rows editor-rows set-editor-rows!)
  (cols editor-cols set-editor-cols!)
  (status-msg editor-status set-editor-status!)
  (novice editor-novice? set-editor-novice!))

;; Compatibility: modified comes from text object now
(define (editor-modified? ed) (text-modified? (editor-text ed)))

(define (editor-new #!optional novice)
  "Create new editor state"
  (make-editor-internal
   (text-new)                           ; text object
   #f                                   ; filename
   #t                                   ; insert mode (not overwrite)
   0                                    ; screen-top line
   1                                    ; cursor row (1-indexed for screen)
   1                                    ; cursor col
   #f                                   ; mark-start
   #f                                   ; mark-end
   ""                                   ; clipboard
   ""                                   ; search string
   #t                                   ; wrap mode on
   (tty-rows)                           ; terminal rows
   (tty-cols)                           ; terminal cols
   ""                                   ; status message
   (or novice #f)))                     ; novice mode

;;; ============================================================
;;; Line Operations (for screen display)
;;; ============================================================

(define (gb-line-start buf pos)
  "Find start of line containing pos"
  (let loop ((p pos))
    (cond
     ((<= p 0) 0)
     ((char=? (gb-char-at buf (- p 1)) #\newline) p)
     (else (loop (- p 1))))))

(define (gb-line-end buf pos)
  "Find end of line containing pos (before newline)"
  (let ((len (gb-length buf)))
    (let loop ((p pos))
      (cond
       ((>= p len) len)
       ((char=? (gb-char-at buf p) #\newline) p)
       (else (loop (+ p 1)))))))

(define (gb-count-lines buf)
  "Count total lines in buffer"
  (let ((len (gb-length buf)))
    (let loop ((i 0) (count 1))
      (if (>= i len)
          count
          (loop (+ i 1)
                (if (char=? (gb-char-at buf i) #\newline)
                    (+ count 1)
                    count))))))

(define (gb-line-number buf pos)
  "Get line number (1-indexed) for position"
  (let loop ((i 0) (line 1))
    (cond
     ((>= i pos) line)
     ((char=? (gb-char-at buf i) #\newline) (loop (+ i 1) (+ line 1)))
     (else (loop (+ i 1) line)))))

(define (gb-column buf pos)
  "Get column (1-indexed) for position"
  (+ 1 (- pos (gb-line-start buf pos))))

(define (gb-line-at buf line-num)
  "Get position of start of line-num (1-indexed)"
  (let ((len (gb-length buf)))
    (let loop ((i 0) (line 1))
      (cond
       ((>= line line-num) i)
       ((>= i len) len)
       ((char=? (gb-char-at buf i) #\newline) (loop (+ i 1) (+ line 1)))
       (else (loop (+ i 1) line))))))

(define (gb-extract-line buf pos)
  "Extract line containing pos as string"
  (let* ((start (gb-line-start buf pos))
         (end (gb-line-end buf pos)))
    (let ((result (make-string (- end start))))
      (do ((i start (+ i 1))
           (j 0 (+ j 1)))
          ((>= i end) result)
        (string-set! result j (gb-char-at buf i))))))

;;; ============================================================
;;; Cursor Movement
;;; ============================================================

(define (editor-move-up! ed)
  "Move cursor up one line"
  (let* ((buf (editor-text ed))
         (pos (gb-cursor buf))
         (col (- pos (gb-line-start buf pos)))
         (line-start (gb-line-start buf pos)))
    (when (> line-start 0)
      (let* ((prev-line-end (- line-start 1))
             (prev-line-start (gb-line-start buf prev-line-end))
             (prev-line-len (- prev-line-end prev-line-start))
             (new-col (min col prev-line-len)))
        (gb-goto! buf (+ prev-line-start new-col))))))

(define (editor-move-down! ed)
  "Move cursor down one line"
  (let* ((buf (editor-text ed))
         (pos (gb-cursor buf))
         (col (- pos (gb-line-start buf pos)))
         (line-end (gb-line-end buf pos))
         (len (gb-length buf)))
    (when (< line-end len)
      (let* ((next-line-start (+ line-end 1))
             (next-line-end (gb-line-end buf next-line-start))
             (next-line-len (- next-line-end next-line-start))
             (new-col (min col next-line-len)))
        (gb-goto! buf (+ next-line-start new-col))))))

(define (editor-move-left! ed)
  "Move cursor left"
  (gb-backward! (editor-text ed)))

(define (editor-move-right! ed)
  "Move cursor right"
  (gb-forward! (editor-text ed)))

(define (editor-move-line-start! ed)
  "Move to start of line"
  (let ((buf (editor-text ed)))
    (gb-goto! buf (gb-line-start buf (gb-cursor buf)))))

(define (editor-move-line-end! ed)
  "Move to end of line"
  (let ((buf (editor-text ed)))
    (gb-goto! buf (gb-line-end buf (gb-cursor buf)))))

(define (editor-move-word-forward! ed)
  "Move forward one word"
  (let* ((buf (editor-text ed))
         (len (gb-length buf))
         (pos (gb-cursor buf)))
    ;; Skip current word
    (let loop ((p pos))
      (cond
       ((>= p len) (gb-goto! buf len))
       ((char-whitespace? (gb-char-at buf p))
        ;; Skip whitespace
        (let skip ((q p))
          (cond
           ((>= q len) (gb-goto! buf len))
           ((char-whitespace? (gb-char-at buf q)) (skip (+ q 1)))
           (else (gb-goto! buf q)))))
       (else (loop (+ p 1)))))))

(define (editor-move-word-backward! ed)
  "Move backward one word"
  (let* ((buf (editor-text ed))
         (pos (gb-cursor buf)))
    (when (> pos 0)
      ;; Skip whitespace
      (let skip ((p (- pos 1)))
        (cond
         ((<= p 0) (gb-goto! buf 0))
         ((char-whitespace? (gb-char-at buf p)) (skip (- p 1)))
         (else
          ;; Skip word
          (let word ((q p))
            (cond
             ((<= q 0) (gb-goto! buf 0))
             ((char-whitespace? (gb-char-at buf (- q 1)))
              (gb-goto! buf q))
             (else (word (- q 1)))))))))))

;;; ============================================================
;;; Editing Operations
;;; ============================================================

(define (editor-insert-char! ed char)
  "Insert character at cursor"
  (let ((buf (editor-text ed)))
    (if (editor-insert-mode? ed)
        (gb-insert! buf char)
        ;; Overwrite mode
        (let ((pos (gb-cursor buf))
              (len (gb-length buf)))
          (if (and (< pos len) (not (char=? (gb-char-at buf pos) #\newline)))
              (begin
                (gb-set-char! buf pos char)
                (gb-forward! buf))
              (gb-insert! buf char)))))) ;; modified tracked by text object

(define (editor-insert-newline! ed)
  "Insert newline"
  (gb-insert! (editor-text ed) #\newline)) ;; modified tracked by text object

(define (editor-delete-char! ed)
  "Delete character at cursor"
  (let* ((buf (editor-text ed))
         (len (gb-length buf))
         (pos (gb-cursor buf)))
    (when (< pos len)
      (gb-delete-forward! buf)))) ;; modified tracked by text object

(define (editor-backspace! ed)
  "Delete character before cursor"
  (let ((buf (editor-text ed)))
    (when (> (gb-cursor buf) 0)
      (gb-delete-backward! buf)))) ;; modified tracked by text object

(define (editor-delete-word! ed)
  "Delete word at cursor"
  (let* ((buf (editor-text ed))
         (start (gb-cursor buf))
         (len (gb-length buf)))
    ;; Find word end
    (let loop ((p start))
      (cond
       ((>= p len)
        (gb-delete-forward! buf (- p start)))
       ((char-whitespace? (gb-char-at buf p))
        ;; Include trailing whitespace
        (let skip ((q p))
          (cond
           ((>= q len) (gb-delete-forward! buf (- q start)))
           ((char-whitespace? (gb-char-at buf q)) (skip (+ q 1)))
           (else (gb-delete-forward! buf (- q start))))))
       (else (loop (+ p 1))))))) ;; modified tracked by text object

(define (editor-delete-line! ed)
  "Delete current line"
  (let* ((buf (editor-text ed))
         (pos (gb-cursor buf))
         (start (gb-line-start buf pos))
         (end (gb-line-end buf pos))
         (len (gb-length buf)))
    (gb-goto! buf start)
    ;; Delete including newline if present
    (gb-delete-forward! buf (if (< end len) (+ 1 (- end start)) (- end start))))) ;; modified tracked by text object

;;; ============================================================
;;; Block Operations
;;; ============================================================

(define (editor-mark-begin! ed)
  "Set block start mark"
  (set-editor-mark-start! ed (gb-cursor (editor-text ed)))
  (set-editor-status! ed "Block start marked"))

(define (editor-mark-end! ed)
  "Set block end and copy to clipboard"
  (let ((start (editor-mark-start ed))
        (buf (editor-text ed)))
    (if start
        (let* ((end (gb-cursor buf))
               (actual-start (min start end))
               (actual-end (max start end))
               (text (let ((result (make-string (- actual-end actual-start))))
                       (do ((i actual-start (+ i 1))
                            (j 0 (+ j 1)))
                           ((>= i actual-end) result)
                         (string-set! result j (gb-char-at buf i))))))
          (set-editor-clipboard! ed text)
          (set-editor-mark-end! ed end)
          (set-editor-status! ed (format #f "Copied ~a chars" (string-length text))))
        (set-editor-status! ed "No block start marked"))))

(define (editor-paste! ed)
  "Paste clipboard at cursor"
  (let ((text (editor-clipboard ed))
        (buf (editor-text ed)))
    (when (and text (> (string-length text) 0))
      (gb-insert-string! buf text)
      ;; modified tracked by text object
      (set-editor-status! ed (format #f "Pasted ~a chars" (string-length text))))))

(define (editor-unmark! ed)
  "Clear block marks"
  (set-editor-mark-start! ed #f)
  (set-editor-mark-end! ed #f)
  (set-editor-status! ed "Block unmarked"))

;;; ============================================================
;;; Search
;;; ============================================================

(define (editor-find! ed pattern)
  "Find next occurrence of pattern"
  (let* ((buf (editor-text ed))
         (len (gb-length buf))
         (start (+ (gb-cursor buf) 1))
         (plen (string-length pattern)))
    (if (= plen 0)
        (set-editor-status! ed "Empty search pattern")
        (let search ((pos start))
          (cond
           ((> pos (- len plen))
            ;; Wrap around
            (let wrap ((pos 0))
              (cond
               ((>= pos start)
                (set-editor-status! ed "Not found"))
               ((string-match-at? buf pos pattern plen)
                (gb-goto! buf pos)
                (set-editor-status! ed (format #f "Found at ~a" pos)))
               (else (wrap (+ pos 1))))))
           ((string-match-at? buf pos pattern plen)
            (gb-goto! buf pos)
            (set-editor-status! ed (format #f "Found at ~a" pos)))
           (else (search (+ pos 1))))))))

(define (string-match-at? buf pos pattern plen)
  "Check if pattern matches at position in buffer"
  (let ((len (gb-length buf)))
    (and (<= (+ pos plen) len)
         (let loop ((i 0))
           (cond
            ((>= i plen) #t)
            ((char=? (gb-char-at buf (+ pos i)) (string-ref pattern i))
             (loop (+ i 1)))
            (else #f))))))

(define (editor-replace! ed old new)
  "Replace occurrence at cursor"
  (let* ((buf (editor-text ed))
         (olen (string-length old)))
    (when (string-match-at? buf (gb-cursor buf) old olen)
      (gb-delete-forward! buf olen)
      (gb-insert-string! buf new)
      ;; modified tracked by text object
      (set-editor-status! ed "Replaced"))))

;;; ============================================================
;;; Display
;;; ============================================================

(define (editor-update-position! ed)
  "Update cursor row/col from buffer position"
  (let* ((buf (editor-text ed))
         (pos (gb-cursor buf)))
    (set-editor-cursor-row! ed (gb-line-number buf pos))
    (set-editor-cursor-col! ed (gb-column buf pos))))

(define (editor-ensure-visible! ed)
  "Scroll if cursor is outside visible area"
  (let ((row (editor-cursor-row ed))
        (top (editor-screen-top ed))
        (visible-rows (- (editor-rows ed) 3))) ; minus status and prompt
    (cond
     ((< row (+ top 1))
      (set-editor-screen-top! ed (max 0 (- row 1))))
     ((> row (+ top visible-rows))
      (set-editor-screen-top! ed (- row visible-rows))))))

(define (editor-draw! ed)
  "Redraw screen"
  (editor-update-position! ed)
  (editor-ensure-visible! ed)
  (let* ((buf (editor-text ed))
         (rows (editor-rows ed))
         (cols (editor-cols ed))
         (top (editor-screen-top ed))
         (visible-rows (- rows 3)))
    (screen-cursor-hide)
    (screen-home)
    (screen-black-bg)
    (screen-green)

    ;; Draw text lines
    (do ((screen-row 1 (+ screen-row 1))
         (line (+ top 1) (+ line 1)))
        ((> screen-row visible-rows))
      (screen-goto screen-row 1)
      (screen-clear-eol)
      (let ((line-start (gb-line-at buf line)))
        (when (< line-start (gb-length buf))
          (let* ((line-end (gb-line-end buf line-start))
                 (line-len (- line-end line-start))
                 (display-len (min line-len (- cols 1))))
            ;; Check for block highlight
            (let ((mark-s (editor-mark-start ed))
                  (mark-e (editor-mark-end ed)))
              (if (and mark-s mark-e)
                  ;; Draw with highlight
                  (let ((actual-start (min mark-s mark-e))
                        (actual-end (max mark-s mark-e)))
                    (do ((i 0 (+ i 1)))
                        ((>= i display-len))
                      (let ((pos (+ line-start i)))
                        (if (and (>= pos actual-start) (< pos actual-end))
                            (begin (screen-reverse) (display (gb-char-at buf pos)) (screen-reset) (screen-green))
                            (display (gb-char-at buf pos))))))
                  ;; Draw normal
                  (do ((i 0 (+ i 1)))
                      ((>= i display-len))
                    (display (gb-char-at buf (+ line-start i))))))))))

    ;; Status line
    (screen-goto (- rows 1) 1)
    (screen-reverse)
    (let* ((filename (or (editor-filename ed) "[untitled]"))
           (modified (if (editor-modified? ed) " [+]" ""))
           (mode (if (editor-insert-mode? ed) "INS" "OVR"))
           (pos-info (format #f "L~a C~a" (editor-cursor-row ed) (editor-cursor-col ed)))
           (status (format #f " ~a~a  ~a  ~a  ~a"
                           filename modified mode pos-info
                           (editor-status ed))))
      (display (string-take status (min (string-length status) cols)))
      (display (make-string (max 0 (- cols (string-length status))) #\space)))
    (screen-reset)

    ;; Menu bar (Sol-20 style command hints)
    (screen-goto rows 1)
    (screen-dim)
    (let ((menu (if (editor-novice? ed)
                    "Ctrl-Q=Quit  Ctrl-O=Open  Ctrl-P=Save  Ctrl-F=Find  Arrows=Move  Type to insert"
                    "^Q quit  ^O open  ^P save  ^F find  ^R replace  ^B/K block  ^V paste  ^I ins/ovr")))
      (display (string-take menu (min (string-length menu) cols)))
      (display (make-string (max 0 (- cols (string-length menu))) #\space)))
    (screen-reset)
    (screen-green)

    ;; Position cursor
    (let ((screen-row (- (editor-cursor-row ed) (editor-screen-top ed)))
          (screen-col (editor-cursor-col ed)))
      (screen-goto screen-row screen-col))
    (screen-cursor-show)
    (flush-output)))

(define (string-take str n)
  "Take first n chars of string"
  (if (<= (string-length str) n)
      str
      (substring str 0 n)))

;;; ============================================================
;;; File Operations
;;; ============================================================

(define (editor-load! ed filename)
  "Load file into editor"
  (if (file-exists? filename)
      (let ((content (with-input-from-file filename read-string)))
        (set-editor-text! ed (string->gb content))
        (set-editor-filename! ed filename)
        (text-clear-modified! (editor-text ed))
        (gb-goto! (editor-text ed) 0)
        (set-editor-screen-top! ed 0)
        (set-editor-status! ed (format #f "Loaded ~a" filename)))
      (begin
        (set-editor-filename! ed filename)
        (set-editor-status! ed "New file"))))

(define (editor-save! ed #!optional filename)
  "Save editor to file"
  (let ((fname (or filename (editor-filename ed))))
    (if fname
        (begin
          (with-output-to-file fname
            (lambda () (display (gb->string (editor-text ed)))))
          (set-editor-filename! ed fname)
          (text-clear-modified! (editor-text ed))
          (set-editor-status! ed (format #f "Saved ~a" fname)))
        (set-editor-status! ed "No filename"))))

;;; ============================================================
;;; Input Handling
;;; ============================================================

;; Buffer for QMK command reading
(define *qmk-buffer* (make-string 64))

;; Read rest of QMK line after #; prefix (returns string without #;)
(define (read-qmk-line)
  (let loop ((i 0))
    (if (>= i 63)
        #f  ; overflow, not QMK
        (let ((c (tty-raw-char)))
          (cond
           ((or (= c 10) (= c 13))  ; newline
            (substring *qmk-buffer* 0 i))
           ((< c 0) #f)  ; EOF
           (else
            (string-set! *qmk-buffer* i (integer->char c))
            (loop (+ i 1))))))))

;; Handle QMK command (payload after "QMK ")
(define (handle-qmk-command payload)
  (condition-case
    (let ((sexp (with-input-from-string payload read)))
      (when (edt-available?)
        (eval `(edt#qmk-eval ',sexp))))
    ((exn) #f)))  ; silently ignore errors during editing

(define (read-key)
  "Read a key, handling escape sequences and QMK commands"
  (let ((c (tty-raw-char)))
    (cond
     ;; QMK command prefix detection: # followed quickly by ;QMK
     ((= c 35)  ; #
      (if (tty-char-ready? 5)  ; QMK sends fast, typing is slow
          (let ((c2 (tty-raw-char)))
            (if (= c2 59)  ; ;
                (let ((buf (read-qmk-line)))
                  (if (and buf (string-prefix? "QMK " buf))
                      (begin
                        (handle-qmk-command (substring buf 4))
                        'qmk-handled)
                      #\#))  ; wasn't QMK, return #
                #\#))  ; wasn't ;, return #
          #\#))  ; no quick follow-up, return #
     ((= c 27)  ; ESC
      ;; Check if more input within 50ms (escape sequence) or bare ESC
      (if (tty-char-ready? 50)
          (let ((c2 (tty-raw-char)))
            (cond
             ((= c2 91)  ; [
              (let ((c3 (tty-raw-char)))
                (case c3
                  ((65) 'up)
                  ((66) 'down)
                  ((67) 'right)
                  ((68) 'left)
                  ((72) 'home)
                  ((70) 'end)
                  ((51) (tty-raw-char) 'delete)  ; ~
                  ((53) (tty-raw-char) 'page-up)
                  ((54) (tty-raw-char) 'page-down)
                  (else 'unknown))))
             ((= c2 27)  ; ESC ESC = still just escape
              'escape)
             (else 'escape)))
          'escape))
     ((= c 127) 'backspace)
     ((= c 13) 'enter)
     ((= c 9) 'tab)
     ((< c 32) (cons 'ctrl (integer->char (+ c 64))))  ; Ctrl-A = 1, etc.
     (else (integer->char c)))))

(define (editor-prompt ed message)
  "Prompt for input on status line"
  (let ((rows (editor-rows ed))
        (cols (editor-cols ed)))
    (screen-goto rows 1)
    (screen-clear-eol)
    (screen-bright-green)
    (display message)
    (screen-reset)
    (screen-green)
    (flush-output)
    ;; Read input with basic line editing
    (tty-set-cooked)  ; restore for input
    (let ((line (read-line)))
      (tty-set-raw)
      line)))

(define (editor-confirm ed message)
  "Confirm action (y/n)"
  (let ((rows (editor-rows ed)))
    (screen-goto rows 1)
    (screen-clear-eol)
    (screen-bright-green)
    (display message)
    (display " (y/n) ")
    (screen-reset)
    (flush-output)
    (let ((c (tty-raw-char)))
      (or (= c 121) (= c 89)))))  ; y or Y

;;; ============================================================
;;; Main Loop
;;; ============================================================

(define (editor-run ed)
  "Main editor loop"
  (tty-flush-input)  ; Clear any buffered garbage
  (tty-set-raw)
  (screen-alt-buffer)
  (screen-clear)
  (edt-register! ed)  ; Register EDT keypad handlers if available

  (let loop ()
    (editor-draw! ed)
    (let ((key (read-key)))
      (cond
       ;; Quit
       ((equal? key '(ctrl . #\Q))
        (if (and (editor-modified? ed)
                 (not (editor-confirm ed "Unsaved changes. Quit anyway?")))
            (loop)
            (void)))

       ;; Movement - WASDZX diamond
       ((or (equal? key '(ctrl . #\W)) (eq? key 'up))
        (editor-move-up! ed) (loop))
       ((or (equal? key '(ctrl . #\S)) (eq? key 'down))
        (editor-move-down! ed) (loop))
       ((or (equal? key '(ctrl . #\A)) (eq? key 'left))
        (editor-move-left! ed) (loop))
       ((or (equal? key '(ctrl . #\D)) (eq? key 'right))
        (editor-move-right! ed) (loop))
       ((or (equal? key '(ctrl . #\Z)) (eq? key 'home))
        (editor-move-line-start! ed) (loop))
       ((or (equal? key '(ctrl . #\X)) (eq? key 'end))
        (editor-move-line-end! ed) (loop))

       ;; Word movement
       ((equal? key '(ctrl . #\[))  ; Ctrl-[ = word left
        (editor-move-word-backward! ed) (loop))
       ((equal? key '(ctrl . #\]))  ; Ctrl-] = word right
        (editor-move-word-forward! ed) (loop))

       ;; Editing
       ((equal? key '(ctrl . #\I))  ; Toggle insert/overwrite
        (set-editor-insert-mode! ed (not (editor-insert-mode? ed)))
        (loop))
       ((or (equal? key '(ctrl . #\G)) (eq? key 'delete))
        (editor-delete-char! ed) (loop))
       ((eq? key 'backspace)
        (editor-backspace! ed) (loop))
       ((equal? key '(ctrl . #\T))
        (editor-delete-word! ed) (loop))
       ((equal? key '(ctrl . #\Y))
        (editor-delete-line! ed) (loop))
       ((eq? key 'enter)
        (editor-insert-newline! ed) (loop))

       ;; Block operations
       ((equal? key '(ctrl . #\B))
        (editor-mark-begin! ed) (loop))
       ((equal? key '(ctrl . #\K))
        (editor-mark-end! ed) (loop))
       ((equal? key '(ctrl . #\V))
        (editor-paste! ed) (loop))
       ((equal? key '(ctrl . #\U))
        (editor-unmark! ed) (loop))

       ;; Search
       ((equal? key '(ctrl . #\F))
        (let ((pattern (editor-prompt ed "Find: ")))
          (when (and pattern (> (string-length pattern) 0))
            (set-editor-search-string! ed pattern)
            (editor-find! ed pattern)))
        (loop))
       ((equal? key '(ctrl . #\N))
        (let ((pattern (editor-search-string ed)))
          (if (> (string-length pattern) 0)
              (editor-find! ed pattern)
              (set-editor-status! ed "No search pattern")))
        (loop))
       ((equal? key '(ctrl . #\R))
        (let ((old (editor-prompt ed "Replace: ")))
          (when (and old (> (string-length old) 0))
            (let ((new (editor-prompt ed "With: ")))
              (when new
                (editor-replace! ed old new)))))
        (loop))

       ;; File operations
       ((equal? key '(ctrl . #\O))
        (let ((fname (editor-prompt ed "Open: ")))
          (when (and fname (> (string-length fname) 0))
            (editor-load! ed fname)))
        (loop))
       ((equal? key '(ctrl . #\P))
        (if (editor-filename ed)
            (editor-save! ed)
            (let ((fname (editor-prompt ed "Save as: ")))
              (when (and fname (> (string-length fname) 0))
                (editor-save! ed fname))))
        (loop))

       ;; Display
       ((equal? key '(ctrl . #\L))
        (screen-clear) (loop))
       ((equal? key '(ctrl . #\E))
        (set-editor-wrap-mode! ed (not (editor-wrap-mode? ed)))
        (loop))

       ;; ESC - cancel/clear
       ((eq? key 'escape)
        (editor-unmark! ed)
        (set-editor-status! ed "")
        (loop))

       ;; Page up/down
       ((eq? key 'page-up)
        (let ((visible (- (editor-rows ed) 3)))
          (do ((i 0 (+ i 1))) ((>= i visible)) (editor-move-up! ed)))
        (loop))
       ((eq? key 'page-down)
        (let ((visible (- (editor-rows ed) 3)))
          (do ((i 0 (+ i 1))) ((>= i visible)) (editor-move-down! ed)))
        (loop))

       ;; Regular character
       ((char? key)
        (editor-insert-char! ed key) (loop))

       ;; Unknown
       (else (loop)))))

  ;; Cleanup
  (edt-unregister!)  ; Clear EDT handlers
  (screen-main-buffer)
  (screen-reset)
  (tty-set-cooked)
  (print "Goodbye."))

;;; ============================================================
;;; EDT Keypad Integration (optional, when loaded from REPL)
;;; ============================================================

;; Check if EDT module is available
(define (edt-available?)
  (condition-case
    (begin (eval 'edt#*edt-editor*) #t)
    ((exn) #f)))

;; Register Pencil's EDT handlers
(define (edt-register! ed)
  (when (edt-available?)
    (eval
      `(set! edt#*edt-editor*
         '((page-down . ,(lambda () (pencil-page-down ed)))
           (page-up . ,(lambda () (pencil-page-up ed)))
           (forward-char . ,(lambda () (editor-move-right! ed)))
           (backward-char . ,(lambda () (editor-move-left! ed)))
           (forward-word . ,(lambda () (editor-move-word-forward! ed)))
           (backward-word . ,(lambda () (editor-move-word-backward! ed)))
           (up . ,(lambda () (editor-move-up! ed)))
           (down . ,(lambda () (editor-move-down! ed)))
           (beginning-of-line . ,(lambda () (editor-move-line-start! ed)))
           (end-of-line . ,(lambda () (editor-move-line-end! ed)))
           (delete-char . ,(lambda () (editor-delete-char! ed)))
           (delete-word . ,(lambda () (editor-delete-word! ed)))
           (delete-line . ,(lambda () (editor-delete-line! ed)))
           (select . ,(lambda () (editor-mark-begin! ed)))
           (cut . ,(lambda () (editor-mark-end! ed)))
           (paste . ,(lambda () (editor-paste! ed)))
           (find . ,(lambda () (pencil-find ed)))
           (find-next . ,(lambda () (pencil-find-next ed)))
           (help . ,(lambda () (pencil-help ed))))))))

;; Unregister EDT handlers
(define (edt-unregister!)
  (when (edt-available?)
    (eval '(set! edt#*edt-editor* #f))))

;; EDT helper functions (need refresh after)
(define (pencil-page-down ed)
  (let ((visible (- (editor-rows ed) 3)))
    (do ((i 0 (+ i 1))) ((>= i visible)) (editor-move-down! ed)))
  (editor-draw! ed))

(define (pencil-page-up ed)
  (let ((visible (- (editor-rows ed) 3)))
    (do ((i 0 (+ i 1))) ((>= i visible)) (editor-move-up! ed)))
  (editor-draw! ed))

(define (pencil-find ed)
  ;; Would need to handle prompt in EDT context
  (set-editor-status! ed "Use Ctrl-F to find")
  (editor-draw! ed))

(define (pencil-find-next ed)
  (let ((pattern (editor-search-string ed)))
    (if (> (string-length pattern) 0)
        (editor-find! ed pattern)
        (set-editor-status! ed "No search pattern")))
  (editor-draw! ed))

(define (pencil-help ed)
  (set-editor-status! ed "Ctrl-Q quit | WASD move | Ctrl-F find")
  (editor-draw! ed))

;;; ============================================================
;;; Entry Point
;;; ============================================================

(define (pencil-internal arg novice)
  "Internal: start editor with optional novice mode"
  (let ((ed (editor-new novice)))
    (when arg
      (if (file-exists? arg)
          (editor-load! ed arg)
          (begin
            (gb-insert-string! (editor-text ed) arg)
            (gb-goto! (editor-text ed) 0)
            (set-editor-status! ed "Scratch"))))
    (when novice
      (set-editor-status! ed "Novice mode - Ctrl-Q to quit"))
    (editor-run ed)))

(define (pencil #!optional arg)
  "Start Electric Pencil editor.
   (pencil)              - new empty buffer
   (pencil \"file.txt\")   - edit file
   (pencil \"hello!\")     - edit text directly (Newton-style)"
  (pencil-internal arg #f))

(define (pencil-novice #!optional arg)
  "Start Electric Pencil in novice mode (extra help, verbose prompts).
   (pencil-novice)            - new empty buffer with guidance
   (pencil-novice \"file.txt\") - edit file with training wheels"
  (pencil-internal arg #t))

;; Run if executed directly
(when (and (pair? (command-line-arguments))
           (not (string-prefix? "-" (car (command-line-arguments)))))
  (pencil (car (command-line-arguments))))

(when (condition-case *verbose-load* ((exn) #f))
  (print "Electric Pencil loaded. (pencil) or (pencil-novice) to edit."))
