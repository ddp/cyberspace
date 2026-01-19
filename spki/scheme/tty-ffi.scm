;;; TTY FFI - Raw character input via getchar
;;;
;;; Scheme's read-char uses stdio buffering that ignores stty.
;;; This provides raw getchar for immediate keypress detection.

(module tty-ffi
  (tty-raw-char
   tty-set-raw
   tty-set-cooked)

  (import scheme
          (chicken base)
          (chicken foreign))

  ;; Raw getchar - returns char code, -1 on EOF
  ;; Also disables stdin buffering before read
  (define tty-raw-char
    (foreign-lambda* int ()
      "setvbuf(stdin, NULL, _IONBF, 0);"
      "return getchar();"))

  ;; Set terminal to raw mode via system() - runs in same process
  (define tty-set-raw
    (foreign-lambda* int ()
      "return system(\"stty -icanon min 1 -echo\");"))

  ;; Restore terminal to cooked mode
  (define tty-set-cooked
    (foreign-lambda* int ()
      "return system(\"stty icanon echo\");"))

) ;; end module
