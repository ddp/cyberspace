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
          (chicken foreign)
          (chicken process))

  ;; Raw getchar - returns char code, -1 on EOF
  (define tty-raw-char
    (foreign-lambda int "getchar"))

  ;; Set terminal to raw mode (no line buffering, no echo)
  (define (tty-set-raw)
    (process-wait (process-run "stty" '("-icanon" "min" "1" "-echo"))))

  ;; Restore terminal to cooked mode
  (define (tty-set-cooked)
    (process-wait (process-run "stty" '("icanon" "echo"))))

) ;; end module
