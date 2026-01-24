;;; lineage.scm - Line editing wrapper for Cyberspace REPL
;;;
;;; Provides a unified line editing interface using linenoise.
;;; Named "lineage" for the capability lineage/history it maintains.

(module lineage
  (lineage
   lineage-with-initial
   history-add
   load-history-from-file
   save-history-to-file)

(import scheme
        (chicken base)
        (chicken string)
        (prefix linenoise ln:))

;; Re-export linenoise functions with lineage names
(define (lineage prompt)
  "Read a line with editing and history support."
  (ln:linenoise prompt))

(define (lineage-with-initial prompt initial)
  "Read a line with initial content pre-filled.
   Note: linenoise doesn't support initial content directly,
   so we append it to the prompt as a hint."
  ;; linenoise doesn't have lineEditSetBuffer equivalent in the egg,
  ;; so we use a workaround: prompt includes hint, user sees it
  ;; For real initial content, we'd need to patch linenoise or use
  ;; raw terminal control. For now, just call linenoise - the caller
  ;; handles initial content display.
  (ln:linenoise prompt))

;; Re-export history functions
(define history-add ln:history-add)
(define load-history-from-file ln:load-history-from-file)
(define save-history-to-file ln:save-history-to-file)

) ;; end module
