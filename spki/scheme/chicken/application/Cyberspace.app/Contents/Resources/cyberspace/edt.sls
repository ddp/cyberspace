;;; EDT - DEC's EDT keypad editor bindings for QMK
;;;
;;; LK201 keyboard heritage - the standard DEC keyboard for VAX/VMS.
;;; Supports Glorious GMMK and similar QMK-based wireless keypads.
;;; QMK firmware sends tagged s-expressions: #;QMK (edt 'key)
;;;
;;; See: VMS EDT Reference Manual

(library (cyberspace edt)
  (export
    ;; QMK command interface
    qmk-dispatch
    qmk-prefix
    ;; EDT keypad commands
    edt
    edt-gold
    edt-reset
    ;; State (accessors - R6RS can't export set! variables)
    edt-gold-active?
    set-edt-editor!
    edt-editor)

  (import (rnrs)
          (only (chezscheme) printf format with-input-from-string void))

  ;; Current editor hook - set by editor when active
  ;; Should be an alist: ((move-up . proc) (move-down . proc) ...)
  (define *edt-editor* #f)

  (define (edt-editor) *edt-editor*)
  (define (set-edt-editor! v) (set! *edt-editor* v))

  ;; GOLD prefix state
  (define *edt-gold-active* #f)

  (define (edt-gold-active?) *edt-gold-active*)

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
        (let* ((payload (substring line 6 (string-length line)))
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
      ((pf1 gold) (edt-gold))
      ((pf2 help) (editor-cmd 'help))
      ((pf3 fndnxt find-next) (editor-cmd 'find-next))
      ((pf4 del-l delete-line) (editor-cmd 'delete-line))
      ;; Keypad numbers
      ((kp7 page page-down) (editor-cmd 'page-down))
      ((kp8 sect section) (editor-cmd 'section-down))
      ((kp9 append) (editor-cmd 'append))
      ((kp4 advance forward) (editor-cmd 'forward-char))
      ((kp5 backup backward) (editor-cmd 'backward-char))
      ((kp6 cut) (editor-cmd 'cut))
      ((kp1 word forward-word) (editor-cmd 'forward-word))
      ((kp2 eol end-of-line) (editor-cmd 'end-of-line))
      ((kp3 char delete-char) (editor-cmd 'delete-char))
      ((kp0 line beginning-of-line) (editor-cmd 'beginning-of-line))
      ;; Operators
      ((kp-minus del-w delete-word) (editor-cmd 'delete-word))
      ((kp-plus paste) (editor-cmd 'paste))
      ((kp-dot select) (editor-cmd 'select))
      ((kp-enter subs substitute) (editor-cmd 'substitute))
      ;; Arrows
      ((up) (editor-cmd 'up))
      ((down) (editor-cmd 'down))
      ((left) (editor-cmd 'backward-char))
      ((right) (editor-cmd 'forward-char))
      (else
       (printf "EDT: unknown key ~a~n" key))))

  ;; GOLD-prefixed commands (alternate functions)
  (define (edt-gold-cmd key)
    (case key
      ((pf1 gold) (editor-cmd 'gold-gold))
      ((pf2 help) (editor-cmd 'help-keypad))
      ((pf3 fndnxt) (editor-cmd 'find))
      ((pf4 del-l) (editor-cmd 'undelete-line))
      ((kp7 page) (editor-cmd 'page-up))
      ((kp8 sect) (editor-cmd 'section-up))
      ((kp9 append) (editor-cmd 'replace))
      ((kp4 advance) (editor-cmd 'end-of-buffer))
      ((kp5 backup) (editor-cmd 'beginning-of-buffer))
      ((kp6 cut) (editor-cmd 'paste-replace))
      ((kp1 word) (editor-cmd 'backward-word))
      ((kp2 eol) (editor-cmd 'delete-to-eol))
      ((kp3 char) (editor-cmd 'special-insert))
      ((kp0 line) (editor-cmd 'open-line))
      ((kp-minus) (editor-cmd 'undelete-word))
      ((kp-plus) (editor-cmd 'paste-replace))
      ((kp-dot) (editor-cmd 'reset-select))
      ((kp-enter) (editor-cmd 'enter-specials))
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

) ;; end library
