;;; edt.sls - DEC's EDT Keypad Editor Bindings (Chez Port)
;;; Library of Cyberspace
;;;
;;; LK201 keyboard heritage - the standard DEC keyboard for VAX/VMS.
;;; Supports QMK-based wireless keypads.
;;; QMK firmware sends tagged s-expressions: #;QMK (edt 'key)
;;;
;;; Ported from edt.scm.
;;; Copyright (c) 2026 Yoyodyne. See LICENSE.

(library (cyberspace edt)
  (export
    ;; QMK command interface
    qmk-dispatch
    qmk-prefix
    ;; EDT keypad commands
    edt
    edt-gold
    edt-reset
    ;; State
    *edt-gold-active*
    *edt-editor*)

  (import (rnrs)
          (only (chezscheme)
                printf format void
                with-input-from-string))

  ;; Current editor hook - set by editor when active
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
  (define (qmk-dispatch line)
    (if (qmk-command? line)
        (let* ((payload (substring line 6 (string-length line)))
               (sexp (with-input-from-string payload read)))
          (qmk-eval sexp)
          #t)
        #f))

  ;; Evaluate QMK command s-expression
  (define (qmk-eval sexp)
    (cond
      ((and (pair? sexp) (eq? (car sexp) 'edt))
       (let ((keys (map unquote-key (cdr sexp))))
         (apply edt-key keys)))
      ((or (equal? sexp '(gold)) (eq? sexp 'gold))
       (edt-gold))
      ((or (equal? sexp '(reset)) (eq? sexp 'reset))
       (edt-reset))
      (else
       (printf "QMK: ~s~%" sexp))))

  ;; Strip quote from 'foo -> foo
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
      ((pf1 gold) (edt-gold))
      ((pf2 help) (editor-cmd 'help))
      ((pf3 fndnxt find-next) (editor-cmd 'find-next))
      ((pf4 del-l delete-line) (editor-cmd 'delete-line))
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
      ((kp-minus del-w delete-word) (editor-cmd 'delete-word))
      ((kp-plus paste) (editor-cmd 'paste))
      ((kp-dot select) (editor-cmd 'select))
      ((kp-enter subs substitute) (editor-cmd 'substitute))
      ((up) (editor-cmd 'up))
      ((down) (editor-cmd 'down))
      ((left) (editor-cmd 'backward-char))
      ((right) (editor-cmd 'forward-char))
      (else
       (printf "EDT: unknown key ~a~%" key))))

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
       (printf "EDT GOLD: unknown key ~a~%" key))))

  ;; Send command to active editor
  (define (editor-cmd cmd)
    (if *edt-editor*
        (let ((handler (assq cmd *edt-editor*)))
          (if handler
              ((cdr handler))
              (printf "EDT: editor doesn't support ~a~%" cmd)))
        (printf "EDT: no editor active~%")))

) ;; end library
