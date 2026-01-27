;;; EDT - DEC's EDT keypad editor bindings for QMK
;;;
;;; LK201 keyboard heritage - the standard DEC keyboard for VAX/VMS.
;;; Supports Glorious GMMK and similar QMK-based wireless keypads.
;;; QMK firmware sends tagged s-expressions: #;QMK (edt 'key)
;;;
;;; LK201 EDT Keypad Layout:
;;;
;;;   PF1=GOLD  PF2=HELP   PF3=FNDNXT  PF4=DEL-L
;;;   7=PAGE    8=SECT     9=APPEND    -=DEL-W
;;;   4=ADVANCE 5=BACKUP   6=CUT       +=PASTE
;;;   1=WORD    2=EOL      3=CHAR      ENTER=SUBS
;;;   0=LINE               .=SELECT
;;;
;;; GOLD (PF1) is a prefix key - press GOLD then another key for
;;; alternate functions. Example: GOLD+7 = top of file.
;;;
;;; See: VMS EDT Reference Manual

(module edt
  (;; QMK command interface
   qmk-dispatch
   qmk-prefix
   ;; EDT keypad commands
   edt
   edt-gold
   edt-reset
   ;; State
   *edt-gold-active*
   *edt-editor*)

  (import scheme
          (chicken base)
          (chicken format)
          (chicken string)
          (chicken port))

  ;; Current editor hook - set by editor when active
  ;; Should be an alist: ((move-up . proc) (move-down . proc) ...)
  (define *edt-editor* #f)

  ;; GOLD prefix state
  (define *edt-gold-active* #f)

  ;; QMK command prefix
  (define qmk-prefix "#;QMK ")

  ;; Check if line is a QMK command
  (define (qmk-command? line)
    (and (string? line)
         (>= (string-length line) 6)
         (string=? (substring line 0 6) qmk-prefix)))

  ;; Parse and dispatch QMK command
  ;; Returns #t if handled, #f if not a QMK command
  (define (qmk-dispatch line)
    (if (qmk-command? line)
        (let* ((payload (substring line 6))
               (sexp (with-input-from-string payload read)))
          (qmk-eval sexp)
          #t)
        #f))

  ;; Evaluate QMK command s-expression
  ;; Accepts: (edt page) or (edt 'page) - both work
  (define (qmk-eval sexp)
    (cond
      ;; (edt key) or (edt 'key) - EDT keypad command
      ((and (pair? sexp) (eq? (car sexp) 'edt))
       (let ((keys (map unquote-key (cdr sexp))))
         (apply edt-key keys)))
      ;; (gold) - set GOLD prefix
      ((or (equal? sexp '(gold)) (eq? sexp 'gold))
       (edt-gold))
      ;; (reset) - clear GOLD
      ((or (equal? sexp '(reset)) (eq? sexp 'reset))
       (edt-reset))
      ;; Unknown - print for debugging
      (else
       (printf "QMK: ~s~n" sexp))))

  ;; Strip quote from 'foo -> foo, leave foo as foo
  (define (unquote-key k)
    (if (and (pair? k) (eq? (car k) 'quote) (pair? (cdr k)))
        (cadr k)
        k))

  ;; Set GOLD prefix active
  (define (edt-gold)
    (set! *edt-gold-active* #t))

  ;; Clear GOLD prefix
  (define (edt-reset)
    (set! *edt-gold-active* #f))

  ;; Main EDT dispatch
  (define (edt . keys)
    (apply edt-key keys))

  ;; Handle EDT keypad key
  ;; key is a symbol: 'pf1, 'pf2, 'pf3, 'pf4, 'kp0-9, 'kp-minus, 'kp-plus, etc.
  (define (edt-key . keys)
    (let ((key (if (null? keys) 'nop (car keys))))
      (if *edt-gold-active*
          (begin
            (set! *edt-gold-active* #f)
            (edt-gold-cmd key))
          (edt-cmd key))))

  ;; Standard EDT commands (no GOLD prefix)
  (define (edt-cmd key)
    (case key
      ;; PF keys
      ((pf1 gold) (edt-gold))           ; GOLD prefix
      ((pf2 help) (editor-cmd 'help))   ; Help
      ((pf3 fndnxt find-next) (editor-cmd 'find-next)) ; Find next
      ((pf4 del-l delete-line) (editor-cmd 'delete-line)) ; Delete line
      ;; Keypad numbers
      ((kp7 page page-down) (editor-cmd 'page-down))   ; Page
      ((kp8 sect section) (editor-cmd 'section-down))  ; Section (paragraph)
      ((kp9 append) (editor-cmd 'append))              ; Append to paste buffer
      ((kp4 advance forward) (editor-cmd 'forward-char)) ; Advance (char)
      ((kp5 backup backward) (editor-cmd 'backward-char)) ; Backup (char)
      ((kp6 cut) (editor-cmd 'cut))                    ; Cut
      ((kp1 word forward-word) (editor-cmd 'forward-word)) ; Word
      ((kp2 eol end-of-line) (editor-cmd 'end-of-line)) ; End of line
      ((kp3 char delete-char) (editor-cmd 'delete-char)) ; Delete char
      ((kp0 line beginning-of-line) (editor-cmd 'beginning-of-line)) ; Line start
      ;; Operators
      ((kp-minus del-w delete-word) (editor-cmd 'delete-word)) ; Delete word
      ((kp-plus paste) (editor-cmd 'paste))            ; Paste
      ((kp-dot select) (editor-cmd 'select))           ; Select/mark
      ((kp-enter subs substitute) (editor-cmd 'substitute)) ; Substitute
      ;; Arrows (for non-numpad fallback)
      ((up) (editor-cmd 'up))
      ((down) (editor-cmd 'down))
      ((left) (editor-cmd 'backward-char))
      ((right) (editor-cmd 'forward-char))
      (else
       (printf "EDT: unknown key ~a~n" key))))

  ;; GOLD-prefixed commands (alternate functions)
  (define (edt-gold-cmd key)
    (case key
      ;; GOLD + PF keys
      ((pf1 gold) (editor-cmd 'gold-gold)) ; GOLD GOLD = command mode?
      ((pf2 help) (editor-cmd 'help-keypad)) ; Keypad help
      ((pf3 fndnxt) (editor-cmd 'find))  ; Find (start new search)
      ((pf4 del-l) (editor-cmd 'undelete-line)) ; Undelete line
      ;; GOLD + keypad = reverse/alternate
      ((kp7 page) (editor-cmd 'page-up)) ; Page up (vs down)
      ((kp8 sect) (editor-cmd 'section-up)) ; Section up
      ((kp9 append) (editor-cmd 'replace)) ; Replace (vs append)
      ((kp4 advance) (editor-cmd 'end-of-buffer)) ; End of buffer
      ((kp5 backup) (editor-cmd 'beginning-of-buffer)) ; Beginning of buffer
      ((kp6 cut) (editor-cmd 'paste-replace)) ; Paste & replace
      ((kp1 word) (editor-cmd 'backward-word)) ; Word backward
      ((kp2 eol) (editor-cmd 'delete-to-eol)) ; Delete to EOL
      ((kp3 char) (editor-cmd 'special-insert)) ; Special insert
      ((kp0 line) (editor-cmd 'open-line)) ; Open line
      ;; GOLD + operators
      ((kp-minus) (editor-cmd 'undelete-word)) ; Undelete word
      ((kp-plus) (editor-cmd 'paste-replace)) ; Paste & replace
      ((kp-dot) (editor-cmd 'reset-select)) ; Reset selection
      ((kp-enter) (editor-cmd 'enter-specials)) ; Enter specials
      (else
       (printf "EDT GOLD: unknown key ~a~n" key))))

  ;; Send command to active editor
  (define (editor-cmd cmd)
    (if *edt-editor*
        (let ((handler (assq cmd *edt-editor*)))
          (if handler
              ((cdr handler))
              (printf "EDT: editor doesn't support ~a~n" cmd)))
        (printf "EDT: no editor active~n")))

) ;; end module
