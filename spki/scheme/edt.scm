;;; edt.scm - LK201/EDT keypad bindings stub
;;;
;;; Placeholder for EDT-style keypad editing commands.
;;; The LK201 keypad layout maps numeric keypad keys to editing functions
;;; in the tradition of VMS EDT and DECwindows.

(module edt (qmk-dispatch)
  (import scheme (chicken base))

  ;; Stub dispatcher - returns #f to indicate no binding
  (define (qmk-dispatch line)
    "Dispatch QMK keypad sequences to EDT commands. Returns #f if not handled."
    #f))
