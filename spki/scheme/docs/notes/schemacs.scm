#!/usr/bin/env csi -s
;;; schemacs.scm - Schemacs: Emacs keybindings for Cyberspace
;;;
;;; For those whose fingers speak Emacs, Schemacs is home.
;;; Same text object substrate as TECO and Electric Pencil.
;;;
;;; Keybindings (Emacs compatible):
;;;   Movement:
;;;     C-f     Forward character
;;;     C-b     Backward character
;;;     C-n     Next line
;;;     C-p     Previous line
;;;     C-a     Beginning of line
;;;     C-e     End of line
;;;     M-f     Forward word
;;;     M-b     Backward word
;;;     M-<     Beginning of buffer
;;;     M->     End of buffer
;;;
;;;   Editing:
;;;     C-d     Delete character
;;;     DEL     Backspace
;;;     C-k     Kill line
;;;     C-y     Yank (paste)
;;;     M-d     Kill word forward
;;;     M-DEL   Kill word backward
;;;
;;;   Search:
;;;     C-s     Incremental search forward
;;;     C-r     Incremental search backward
;;;
;;;   File:
;;;     C-x C-f Find file (open)
;;;     C-x C-s Save file
;;;     C-x C-c Exit
;;;
;;;   Display:
;;;     C-l     Recenter/refresh
;;;
;;; See also:
;;;   pencil.scm - Electric Pencil (Shrayer 1976)
;;;   teco.scm   - TECO (Murphy 1962)

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

;; Load text module (gap buffer implementation)
(load "text.scm")
(import text)

;;; ============================================================
;;; Screen Module - ANSI Terminal Control
;;; ============================================================

(define ESC (integer->char 27))

(define (screen-escape . args)
  (apply string-append (cons (string ESC #\[) args)))

(define (screen-goto row col)
  (display (screen-escape (number->string row) ";" (number->string col) "H")))

(define (screen-home)
  (display (screen-escape "H")))

(define (screen-clear)
  (display (screen-escape "2J"))
  (screen-home))

(define (screen-clear-eol)
  (display (screen-escape "K")))

(define (screen-reset)
  (display (screen-escape "0m")))

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
;;; Editor State
;;; ============================================================

(define-record-type <schemacs>
  (make-schemacs-internal buf filename screen-top
                          mark kill-ring
                          search-string rows cols status)
  schemacs?
  (buf schemacs-buf set-schemacs-buf!)
  (filename schemacs-filename set-schemacs-filename!)
  (screen-top schemacs-screen-top set-schemacs-screen-top!)
  (mark schemacs-mark set-schemacs-mark!)
  (kill-ring schemacs-kill-ring set-schemacs-kill-ring!)
  (search-string schemacs-search-string set-schemacs-search-string!)
  (rows schemacs-rows set-schemacs-rows!)
  (cols schemacs-cols set-schemacs-cols!)
  (status schemacs-status set-schemacs-status!))

(define (schemacs-new)
  (make-schemacs-internal
   (text-new)        ; buffer
   #f                ; filename
   0                 ; screen-top line
   #f                ; mark position
   ""                ; kill-ring
   ""                ; search string
   (tty-rows)        ; terminal rows
   (tty-cols)        ; terminal cols
   ""))              ; status message

;;; ============================================================
;;; Movement Commands
;;; ============================================================

(define (em-forward-char! ed)
  (text-move! (schemacs-buf ed) 1))

(define (em-backward-char! ed)
  (text-move! (schemacs-buf ed) -1))

(define (em-next-line! ed)
  (let* ((buf (schemacs-buf ed))
         (pos (text-cursor buf))
         (col (text-column buf pos))
         (line (text-line-number buf pos))
         (next-start (text-line-at buf (+ line 1))))
    (when next-start
      (let* ((next-end-pos
              (let loop ((p next-start))
                (let ((c (text-char-at buf p)))
                  (cond
                   ((not c) p)
                   ((char=? c #\newline) p)
                   (else (loop (+ p 1)))))))
             (next-len (- next-end-pos next-start))
             (new-col (min (- col 1) next-len)))
        (text-goto! buf (+ next-start new-col))))))

(define (em-previous-line! ed)
  (let* ((buf (schemacs-buf ed))
         (pos (text-cursor buf))
         (col (text-column buf pos))
         (line (text-line-number buf pos)))
    (when (> line 1)
      (let* ((prev-start (text-line-at buf (- line 1)))
             (prev-end-pos
              (let loop ((p prev-start))
                (let ((c (text-char-at buf p)))
                  (cond
                   ((not c) p)
                   ((char=? c #\newline) p)
                   (else (loop (+ p 1)))))))
             (prev-len (- prev-end-pos prev-start))
             (new-col (min (- col 1) prev-len)))
        (text-goto! buf (+ prev-start new-col))))))

(define (em-beginning-of-line! ed)
  (text-line-start! (schemacs-buf ed)))

(define (em-end-of-line! ed)
  (text-line-end! (schemacs-buf ed)))

(define (em-beginning-of-buffer! ed)
  (text-beginning! (schemacs-buf ed)))

(define (em-end-of-buffer! ed)
  (text-end! (schemacs-buf ed)))

(define (em-forward-word! ed)
  (let* ((buf (schemacs-buf ed))
         (len (text-length buf))
         (pos (text-cursor buf)))
    ;; Skip non-word chars, then skip word chars
    (let skip-nonword ((p pos))
      (if (>= p len)
          (text-goto! buf len)
          (let ((c (text-char-at buf p)))
            (if (or (char-whitespace? c) (char=? c #\newline))
                (skip-nonword (+ p 1))
                (let skip-word ((q p))
                  (if (>= q len)
                      (text-goto! buf len)
                      (let ((c (text-char-at buf q)))
                        (if (or (char-whitespace? c) (char=? c #\newline))
                            (text-goto! buf q)
                            (skip-word (+ q 1))))))))))))

(define (em-backward-word! ed)
  (let* ((buf (schemacs-buf ed))
         (pos (text-cursor buf)))
    (when (> pos 0)
      ;; Skip whitespace, then skip word
      (let skip-nonword ((p (- pos 1)))
        (if (<= p 0)
            (text-goto! buf 0)
            (let ((c (text-char-at buf p)))
              (if (or (char-whitespace? c) (char=? c #\newline))
                  (skip-nonword (- p 1))
                  (let skip-word ((q p))
                    (if (<= q 0)
                        (text-goto! buf 0)
                        (let ((c (text-char-at buf (- q 1))))
                          (if (or (char-whitespace? c) (char=? c #\newline))
                              (text-goto! buf q)
                              (skip-word (- q 1)))))))))))))

;;; ============================================================
;;; Editing Commands
;;; ============================================================

(define (em-delete-char! ed)
  (text-delete! (schemacs-buf ed) 1))

(define (em-backspace! ed)
  (text-delete-backward! (schemacs-buf ed) 1))

(define (em-kill-line! ed)
  (let* ((buf (schemacs-buf ed))
         (pos (text-cursor buf))
         (end-pos (text-find-line-end buf pos))
         (killed (text-substring buf pos end-pos)))
    (if (= pos end-pos)
        ;; At end of line - kill the newline
        (begin
          (text-delete! buf 1)
          (set-schemacs-kill-ring! ed "\n"))
        ;; Kill to end of line
        (begin
          (text-delete! buf (- end-pos pos))
          (set-schemacs-kill-ring! ed killed)))))

(define (em-yank! ed)
  (let ((killed (schemacs-kill-ring ed)))
    (when (> (string-length killed) 0)
      (text-insert! (schemacs-buf ed) killed))))

(define (em-kill-word! ed)
  (let* ((buf (schemacs-buf ed))
         (start (text-cursor buf)))
    (em-forward-word! ed)
    (let* ((end (text-cursor buf))
           (killed (text-substring buf start end)))
      (text-goto! buf start)
      (text-delete! buf (- end start))
      (set-schemacs-kill-ring! ed killed))))

(define (em-backward-kill-word! ed)
  (let* ((buf (schemacs-buf ed))
         (end (text-cursor buf)))
    (em-backward-word! ed)
    (let* ((start (text-cursor buf))
           (killed (text-substring buf start end)))
      (text-delete! buf (- end start))
      (set-schemacs-kill-ring! ed killed))))

(define (em-self-insert! ed char)
  (text-insert-char! (schemacs-buf ed) char))

(define (em-newline! ed)
  (text-insert-char! (schemacs-buf ed) #\newline))

;;; ============================================================
;;; Search
;;; ============================================================

(define (em-search-forward! ed pattern)
  (let ((pos (text-search (schemacs-buf ed) pattern)))
    (if pos
        (begin
          (text-goto! (schemacs-buf ed) pos)
          (set-schemacs-status! ed (format #f "Found: ~a" pattern)))
        (set-schemacs-status! ed "Not found"))))

(define (em-search-backward! ed pattern)
  (let ((pos (text-search-backward (schemacs-buf ed) pattern)))
    (if pos
        (begin
          (text-goto! (schemacs-buf ed) pos)
          (set-schemacs-status! ed (format #f "Found: ~a" pattern)))
        (set-schemacs-status! ed "Not found"))))

;;; ============================================================
;;; File Operations
;;; ============================================================

(define (em-find-file! ed filename)
  (if (file-exists? filename)
      (begin
        (set-schemacs-buf! ed (text-from-file filename))
        (set-schemacs-filename! ed filename)
        (set-schemacs-status! ed (format #f "Loaded: ~a" filename)))
      (begin
        (set-schemacs-buf! ed (text-new))
        (set-schemacs-filename! ed filename)
        (set-schemacs-status! ed "New file"))))

(define (em-save-file! ed)
  (let ((filename (schemacs-filename ed)))
    (if filename
        (begin
          (with-output-to-file filename
            (lambda () (display (text->string (schemacs-buf ed)))))
          (text-clear-modified! (schemacs-buf ed))
          (set-schemacs-status! ed (format #f "Saved: ~a" filename)))
        (set-schemacs-status! ed "No filename"))))

(define (em-seal! ed #!optional name)
  "Seal buffer to vault. If name given, use named ref. Returns hash."
  (let* ((buf (schemacs-buf ed))
         (hash (if name (seal-as buf name) (text-seal buf)))
         (short-hash (substring hash 7 (min 19 (string-length hash)))))
    (when name (set-schemacs-filename! ed name))
    (set-schemacs-status! ed (format #f "Sealed: ~a~a"
                                     (if name (string-append name " ") "")
                                     short-hash))
    hash))

(define (em-unseal! ed spec)
  "Load buffer from vault by hash or name (with optional @version)"
  (condition-case
    (let* ((is-hash (string-prefix? "blake2b:" spec))
           (buf (if is-hash (text-unseal spec) (unseal-named spec)))
           (name (and (not is-hash) (car (em-parse-name-spec spec)))))
      (set-schemacs-buf! ed buf)
      (text-goto! buf 0)
      (set-schemacs-screen-top! ed 0)
      (set-schemacs-filename! ed name)
      (let* ((hash (text-source-hash buf))
             (short-hash (substring hash 7 (min 19 (string-length hash)))))
        (set-schemacs-status! ed (format #f "Loaded: ~a~a"
                                         (if name (string-append name " ") "")
                                         short-hash))))
    ((exn)
     (set-schemacs-status! ed (format #f "Failed: ~a" spec)))))

(define (em-parse-name-spec spec)
  "Parse 'name' or 'name;version' into (name . version) (VMS style)"
  (let ((semi-pos (string-index spec #\;)))
    (if semi-pos
        (let ((ver-str (substring spec (+ semi-pos 1))))
          (cons (substring spec 0 semi-pos)
                (if (string=? ver-str "")
                    #f
                    (string->number ver-str))))
        (cons spec #f))))

;;; ============================================================
;;; Display
;;; ============================================================

(define (em-update-screen-top! ed)
  (let* ((buf (schemacs-buf ed))
         (line (text-line-number buf (text-cursor buf)))
         (top (schemacs-screen-top ed))
         (visible (- (schemacs-rows ed) 2)))
    (cond
     ((< line (+ top 1))
      (set-schemacs-screen-top! ed (max 0 (- line 1))))
     ((> line (+ top visible))
      (set-schemacs-screen-top! ed (- line visible))))))

(define (em-draw! ed)
  (em-update-screen-top! ed)
  (let* ((buf (schemacs-buf ed))
         (rows (schemacs-rows ed))
         (cols (schemacs-cols ed))
         (top (schemacs-screen-top ed))
         (visible (- rows 2))
         (cursor-line (text-line-number buf (text-cursor buf)))
         (cursor-col (text-column buf (text-cursor buf))))
    (screen-cursor-hide)
    (screen-home)
    (screen-black-bg)
    (screen-green)

    ;; Draw text lines
    (do ((screen-row 1 (+ screen-row 1))
         (line (+ top 1) (+ line 1)))
        ((> screen-row visible))
      (screen-goto screen-row 1)
      (screen-clear-eol)
      (let ((line-start (text-line-at buf line)))
        (when line-start
          (let* ((len (text-length buf))
                 (line-end (text-find-line-end buf line-start))
                 (line-len (- line-end line-start))
                 (display-len (min line-len (- cols 1))))
            (do ((i 0 (+ i 1)))
                ((>= i display-len))
              (display (text-char-at buf (+ line-start i))))))))

    ;; Mode line
    (screen-goto (- rows 1) 1)
    (screen-reverse)
    (let* ((filename (or (schemacs-filename ed) "*scratch*"))
           (modified (if (text-modified? (schemacs-buf ed)) "**" "--"))
           (pos-info (format #f "(~a,~a)" cursor-line cursor-col))
           ;; Vault status: show short hash if sealed
           (source-hash (text-source-hash (schemacs-buf ed)))
           (vault-status (if source-hash
                             (format #f " [~a]" (substring source-hash 7 (min 19 (string-length source-hash))))
                             ""))
           (mode-line (format #f "~a ~a  ~a~a  Schemacs" modified filename pos-info vault-status)))
      (display (string-take mode-line (min (string-length mode-line) cols)))
      (display (make-string (max 0 (- cols (string-length mode-line))) #\space)))
    (screen-reset)
    (screen-green)

    ;; Mini-buffer (status)
    (screen-goto rows 1)
    (screen-clear-eol)
    (display (schemacs-status ed))

    ;; Position cursor
    (let ((screen-row (- cursor-line (schemacs-screen-top ed)))
          (screen-col cursor-col))
      (screen-goto screen-row screen-col))
    (screen-cursor-show)
    (flush-output)))

(define (string-take str n)
  (if (<= (string-length str) n)
      str
      (substring str 0 n)))

;;; ============================================================
;;; Input Handling
;;; ============================================================

(define (read-key)
  (let ((c (tty-raw-char)))
    (cond
     ((= c 27)  ; ESC
      (if (tty-char-ready? 50)
          (let ((c2 (tty-raw-char)))
            (cond
             ((= c2 91)  ; [
              (let ((c3 (tty-raw-char)))
                (case c3
                  ((65) 'up) ((66) 'down) ((67) 'right) ((68) 'left)
                  ((72) 'home) ((70) 'end)
                  ((51) (tty-raw-char) 'delete)
                  (else 'unknown))))
             ;; M-key (ESC followed by key)
             ((= c2 102) 'M-f)    ; M-f
             ((= c2 98) 'M-b)     ; M-b
             ((= c2 100) 'M-d)    ; M-d
             ((= c2 60) 'M-<)     ; M-<
             ((= c2 62) 'M->)     ; M->
             ((= c2 127) 'M-DEL)  ; M-DEL
             (else 'escape)))
          'escape))
     ((= c 127) 'backspace)
     ((= c 13) 'enter)
     ((= c 9) 'tab)
     ((< c 32) (cons 'ctrl (integer->char (+ c 64))))
     (else (integer->char c)))))

(define (em-prompt ed message)
  (let ((rows (schemacs-rows ed)))
    (screen-goto rows 1)
    (screen-clear-eol)
    (screen-bright-green)
    (display message)
    (screen-reset)
    (screen-green)
    (flush-output)
    (tty-set-cooked)
    (let ((line (read-line)))
      (tty-set-raw)
      line)))

(define (em-confirm ed message)
  (let ((rows (schemacs-rows ed)))
    (screen-goto rows 1)
    (screen-clear-eol)
    (display message)
    (display " (y/n) ")
    (flush-output)
    (let ((c (tty-raw-char)))
      (or (= c 121) (= c 89)))))

;;; ============================================================
;;; Main Loop
;;; ============================================================

(define (schemacs-run ed)
  (tty-set-raw)
  (screen-alt-buffer)
  (screen-clear)

  (let loop ()
    (em-draw! ed)
    (let ((key (read-key)))
      (cond
       ;; Exit: C-x C-c
       ((equal? key '(ctrl . #\X))
        (let ((next (read-key)))
          (cond
           ((equal? next '(ctrl . #\C))
            (if (and (text-modified? (schemacs-buf ed))
                     (not (em-confirm ed "Buffer modified. Quit anyway?")))
                (loop)
                'quit))
           ((equal? next '(ctrl . #\S))
            ;; Seal to vault with name
            (let ((name (or (schemacs-filename ed)
                            (em-prompt ed "Save as: "))))
              (when (and name (> (string-length name) 0))
                (em-seal! ed name)))
            (loop))
           ((equal? next '(ctrl . #\F))
            (let ((input (em-prompt ed "Find (name, file, or hash): ")))
              (when (and input (> (string-length input) 0))
                (cond
                 ;; Full hash
                 ((string-prefix? "blake2b:" input)
                  (em-unseal! ed input))
                 ;; Bare 64 hex chars
                 ((and (= (string-length input) 64)
                       (string-every (lambda (c)
                                       (or (char-numeric? c)
                                           (and (char>=? c #\a) (char<=? c #\f))))
                                     input))
                  (em-unseal! ed (string-append "blake2b:" input)))
                 ;; Named ref (possibly with @version)
                 ((ref-current (car (em-parse-name-spec input)))
                  (em-unseal! ed input))
                 ;; Fallback: filesystem
                 (else
                  (em-find-file! ed input)))))
            (loop))
           (else (loop)))))

       ;; Movement
       ((or (equal? key '(ctrl . #\F)) (eq? key 'right))
        (em-forward-char! ed) (loop))
       ((or (equal? key '(ctrl . #\B)) (eq? key 'left))
        (em-backward-char! ed) (loop))
       ((or (equal? key '(ctrl . #\N)) (eq? key 'down))
        (em-next-line! ed) (loop))
       ((or (equal? key '(ctrl . #\P)) (eq? key 'up))
        (em-previous-line! ed) (loop))
       ((or (equal? key '(ctrl . #\A)) (eq? key 'home))
        (em-beginning-of-line! ed) (loop))
       ((or (equal? key '(ctrl . #\E)) (eq? key 'end))
        (em-end-of-line! ed) (loop))
       ((eq? key 'M-f)
        (em-forward-word! ed) (loop))
       ((eq? key 'M-b)
        (em-backward-word! ed) (loop))
       ((eq? key 'M-<)
        (em-beginning-of-buffer! ed) (loop))
       ((eq? key 'M->)
        (em-end-of-buffer! ed) (loop))

       ;; Editing
       ((or (equal? key '(ctrl . #\D)) (eq? key 'delete))
        (em-delete-char! ed) (loop))
       ((eq? key 'backspace)
        (em-backspace! ed) (loop))
       ((equal? key '(ctrl . #\K))
        (em-kill-line! ed) (loop))
       ((equal? key '(ctrl . #\Y))
        (em-yank! ed) (loop))
       ((eq? key 'M-d)
        (em-kill-word! ed) (loop))
       ((eq? key 'M-DEL)
        (em-backward-kill-word! ed) (loop))
       ((eq? key 'enter)
        (em-newline! ed) (loop))

       ;; Search
       ((equal? key '(ctrl . #\S))
        (let ((pattern (em-prompt ed "Search: ")))
          (when (and pattern (> (string-length pattern) 0))
            (set-schemacs-search-string! ed pattern)
            (em-search-forward! ed pattern)))
        (loop))
       ((equal? key '(ctrl . #\R))
        (let ((pattern (em-prompt ed "Search backward: ")))
          (when (and pattern (> (string-length pattern) 0))
            (set-schemacs-search-string! ed pattern)
            (em-search-backward! ed pattern)))
        (loop))

       ;; Display
       ((equal? key '(ctrl . #\L))
        (screen-clear) (loop))

       ;; Cancel
       ((or (equal? key '(ctrl . #\G)) (eq? key 'escape))
        (set-schemacs-status! ed "Quit")
        (loop))

       ;; Self-insert
       ((char? key)
        (em-self-insert! ed key) (loop))

       ;; Unknown
       (else (loop)))))

  ;; Cleanup
  (screen-main-buffer)
  (screen-reset)
  (tty-set-cooked)
  (print "Goodbye."))

;;; ============================================================
;;; Entry Point
;;; ============================================================

(define (schemacs #!optional arg)
  "Start Schemacs editor.
   (schemacs)            - new scratch buffer
   (schemacs \"file.txt\") - edit file"
  (let ((ed (schemacs-new)))
    (when arg
      (if (file-exists? arg)
          (em-find-file! ed arg)
          (begin
            (set-schemacs-filename! ed arg)
            (set-schemacs-status! ed "New file"))))
    (schemacs-run ed)))

;; Run if executed directly
(when (and (pair? (command-line-arguments))
           (not (string-prefix? "-" (car (command-line-arguments)))))
  (schemacs (car (command-line-arguments))))

(print "Schemacs loaded. (schemacs \"file.txt\") to edit.")
