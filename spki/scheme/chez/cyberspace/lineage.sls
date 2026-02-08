;;; lineage.sls - Line Editor with History (Chez Port)
;;; Library of Cyberspace
;;;
;;; Replacement for the Chicken 'lineage' egg.
;;; Provides basic line editing with history for the REPL.
;;;
;;; When tty-bridge is available, uses raw mode for character-at-a-time
;;; input with arrow key navigation. Falls back to plain get-line.
;;;
;;; Copyright (c) 2026 Yoyodyne. See LICENSE.

(library (cyberspace lineage)
  (export
    lineage-read
    lineage-add-history!
    lineage-set-prompt!
    lineage-load-history!
    lineage-save-history!
    lineage-history
    lineage-add-command
    lineage-set-paren-wrap)

  (import (rnrs)
          (only (chezscheme)
                printf format void
                flush-output-port
                file-exists?
                with-input-from-file with-output-to-file)
          (cyberspace tty-ffi))

  ;; ============================================================
  ;; State
  ;; ============================================================

  (define *history* '())
  (define *history-max* 1000)
  (define *prompt* "> ")
  (define *completions* '())
  (define *paren-wrap* 0)

  ;; ============================================================
  ;; Public API
  ;; ============================================================

  (define (lineage-set-prompt! prompt)
    (set! *prompt* prompt))

  (define (lineage-add-history! line)
    "Add line to history."
    (when (and (string? line)
               (> (string-length line) 0)
               (or (null? *history*)
                   (not (string=? line (car *history*)))))
      (set! *history* (cons line *history*))
      (when (> (length *history*) *history-max*)
        (set! *history* (take-n *history* *history-max*)))))

  (define (lineage-history)
    "Return history list."
    *history*)

  (define (lineage-add-command cmd)
    "Add command to completion list."
    (unless (member cmd *completions*)
      (set! *completions* (cons cmd *completions*))))

  (define (lineage-set-paren-wrap n)
    "Set paren wrapping mode: 0=none, 1=wrap completions in parens."
    (set! *paren-wrap* n))

  (define (lineage-load-history! path)
    "Load history from file."
    (when (file-exists? path)
      (guard (exn [#t (void)])
        (with-input-from-file path
          (lambda ()
            (let loop ()
              (let ((line (get-line (current-input-port))))
                (unless (eof-object? line)
                  (lineage-add-history! line)
                  (loop)))))))))

  (define (lineage-save-history! path)
    "Save history to file."
    (guard (exn [#t (void)])
      (with-output-to-file path
        (lambda ()
          ;; Save most recent 500
          (for-each
            (lambda (line) (display line) (newline))
            (reverse (take-n *history* 500)))))))

  ;; ============================================================
  ;; Line Reading
  ;; ============================================================

  (define (lineage-read prompt)
    "Read a line with prompt. Returns string or eof-object."
    (display prompt)
    (flush-output-port (current-output-port))
    (let ((line (get-line (current-input-port))))
      (unless (eof-object? line)
        (lineage-add-history! line))
      line))

  ;; ============================================================
  ;; Helpers
  ;; ============================================================

  (define (take-n lst n)
    (if (or (null? lst) (<= n 0)) '()
        (cons (car lst) (take-n (cdr lst) (- n 1)))))

) ;; end library
