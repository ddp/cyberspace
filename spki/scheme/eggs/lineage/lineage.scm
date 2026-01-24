;;; lineage - BSD line editing with history
;;;
;;; A polished alternative to GNU readline.
;;; Based on linenoise with fixes for:
;;;   - Clear line before prompt (handles pre-displayed content)
;;;   - Initial buffer content (lineage-with-initial)
;;;   - Suppress spurious newline on empty input
;;;   - Home/End key support
;;;
;;; Copyright (c) 2010-2014 Salvatore Sanfilippo <antirez@gmail.com>
;;; Copyright (c) 2010-2013 Pieter Noordhuis <pcnoordhuis@gmail.com>
;;; Copyright (c) 2026 Derrell Piper <ddp@eludom.net>
;;; BSD licensed.

(module lineage
  (lineage
   lineage-with-initial
   history-add
   set-history-length!
   save-history-to-file
   load-history-from-file
   make-lineage-port)

  (import scheme (chicken base) (chicken process signal) (chicken repl) (chicken foreign) (chicken port))

  (foreign-declare  "#include \"lineage-src.c\"")

  (define history-add (foreign-lambda int linenoiseHistoryAdd c-string))
  (define set-history-length! (foreign-lambda int linenoiseHistorySetMaxLen int))
  (define load-history-from-file (foreign-lambda int linenoiseHistoryLoad c-string))
  (define save-history-to-file (foreign-lambda int linenoiseHistorySave c-string))
  (define lineage (foreign-lambda c-string linenoise c-string))
  (define lineage-with-initial (foreign-lambda c-string linenoiseWithInitial c-string c-string))

  (define (make-lineage-port #!optional prompt)
    (let ((l "")
          (handle #f)
          (p1 prompt)
          (pos 0))
      (letrec ((char-ready?
                (lambda ()
                  (< pos (string-length l))))
               (get-next-char!
                (lambda ()
                  (cond ((not l)
                         #!eof)
                        ((char-ready?)
                         (let ((ch (string-ref l pos)))
                           (set! pos (+ 1 pos))
                           ch))
                        (else
                         (set! pos 0)
                         (set! l
                               (let* ((prompt (or p1 ((repl-prompt))))
                                      (r (lineage prompt)))
                                 (when r (history-add r))
                                 r))
                         (if (string? l)
                             (set! l (string-append l "\n")))
                         (get-next-char!))))))
        (set! handle (lambda (s)
                       (print-call-chain)
                       (set! pos 0)
                       (set! l "")
                       (##sys#user-interrupt-hook)))
        (set-signal-handler! signal/int handle)
        (let ((p (make-input-port
                  get-next-char!
                  char-ready?
                  (lambda ()
                    (set-signal-handler! signal/int #f)
                    'closed-lineage-port))))
          (set-port-name! p "(lineage)")
          p)))))
