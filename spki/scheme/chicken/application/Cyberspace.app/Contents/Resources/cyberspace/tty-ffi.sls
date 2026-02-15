;;; TTY FFI - Raw character input via termios
;;;
;;; Scheme's read-char uses stdio buffering that ignores stty.
;;; This uses termios directly for true unbuffered input.
;;; Also provides terminal size detection for full-screen apps.
;;;
;;; Build the bridge: cc -shared -o libtty-bridge.dylib tty-bridge.c

(library (cyberspace tty-ffi)
  (export
    tty-raw-char
    tty-char-ready?
    tty-set-raw
    tty-set-cooked
    tty-flush-input
    tty-unread-char
    tty-rows
    tty-cols
    tty?
    tty-available?)

  (import (rnrs)
          (only (chezscheme)
                load-shared-object foreign-procedure))

  ;; ============================================================
  ;; Library Loading
  ;; ============================================================

  (define *tty-bridge-loaded*
    (let loop ((paths '("./libtty-bridge.dylib"
                        "../libtty-bridge.dylib"
                        "libtty-bridge.dylib"
                        "./libtty-bridge.so"
                        "../libtty-bridge.so"
                        "libtty-bridge.so")))
      (if (null? paths)
          #f
          (guard (exn [#t (loop (cdr paths))])
            (load-shared-object (car paths))
            #t))))

  (define (tty-available?) *tty-bridge-loaded*)

  ;; ============================================================
  ;; Foreign Procedures
  ;; ============================================================

  (define-syntax define-tty-foreign
    (syntax-rules ()
      [(_ name expr)
       (define name
         (if *tty-bridge-loaded*
             expr
             (lambda args
               (error 'tty-ffi "TTY bridge not loaded -- build libtty-bridge"))))]))

  (define-tty-foreign tty-raw-char
    (foreign-procedure "tty_read_char" () int))

  (define-tty-foreign %tty-char-ready
    (foreign-procedure "tty_char_ready" (int) int))

  (define-tty-foreign tty-set-raw
    (foreign-procedure "tty_set_raw_mode" () int))

  (define-tty-foreign tty-set-cooked
    (foreign-procedure "tty_set_cooked_mode" () int))

  (define-tty-foreign tty-rows
    (foreign-procedure "tty_get_rows" () int))

  (define-tty-foreign tty-cols
    (foreign-procedure "tty_get_cols" () int))

  (define-tty-foreign %tty-is-tty
    (foreign-procedure "tty_is_tty" () int))

  (define-tty-foreign tty-flush-input
    (foreign-procedure "tty_flush_input_buffer" () int))

  (define-tty-foreign tty-unread-char
    (foreign-procedure "tty_unread_char" (int) int))

  ;; ============================================================
  ;; Scheme API Wrappers
  ;; ============================================================

  ;; Return boolean instead of int
  (define (tty-char-ready? timeout-ms)
    (not (zero? (%tty-char-ready timeout-ms))))

  (define (tty?)
    (not (zero? (%tty-is-tty))))

) ;; end library
