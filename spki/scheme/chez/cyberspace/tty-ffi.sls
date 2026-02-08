;;; tty-ffi.sls - Raw Character Input via termios (Chez Port)
;;; Library of Cyberspace
;;;
;;; Scheme's read-char uses stdio buffering that ignores stty.
;;; This uses termios directly for true unbuffered input.
;;; Also provides terminal size detection for full-screen apps.
;;;
;;; Requires tty-bridge.c compiled as shared object:
;;;   cc -shared -fPIC -o tty-bridge.so tty-bridge.c    (Linux)
;;;   cc -dynamiclib -o tty-bridge.dylib tty-bridge.c   (macOS)
;;;
;;; When the bridge is not available, falls back to shell commands
;;; for terminal size and stty for raw mode.
;;;
;;; Ported from tty-ffi.scm.
;;; Copyright (c) 2026 Yoyodyne. See LICENSE.

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
    tty?)

  (import (rnrs)
          (only (chezscheme)
                printf format void system
                load-shared-object foreign-procedure
                file-exists? getenv
                open-process-ports native-transcoder))

  ;; ============================================================
  ;; Bridge Loading
  ;; ============================================================

  (define *bridge-loaded* #f)

  (define (try-load-bridge)
    "Attempt to load tty-bridge shared library."
    (define paths
      (list "tty-bridge.so"
            "tty-bridge.dylib"
            "./tty-bridge.so"
            "./tty-bridge.dylib"
            "cyberspace/tty-bridge.so"
            "cyberspace/tty-bridge.dylib"))
    (let loop ((ps paths))
      (if (null? ps)
          #f
          (guard (exn [#t (loop (cdr ps))])
            (load-shared-object (car ps))
            #t))))

  (define dummy (set! *bridge-loaded* (try-load-bridge)))

  ;; ============================================================
  ;; Foreign Bindings (when bridge loaded)
  ;; ============================================================

  (define c-tty-read-char
    (if *bridge-loaded*
        (foreign-procedure "tty_read_char" () int)
        (lambda () -1)))

  (define c-tty-char-ready
    (if *bridge-loaded*
        (foreign-procedure "tty_char_ready" (int) int)
        (lambda (ms) 0)))

  (define c-tty-set-raw
    (if *bridge-loaded*
        (foreign-procedure "tty_set_raw_mode" () int)
        (lambda () -1)))

  (define c-tty-set-cooked
    (if *bridge-loaded*
        (foreign-procedure "tty_set_cooked_mode" () int)
        (lambda () -1)))

  (define c-tty-get-rows
    (if *bridge-loaded*
        (foreign-procedure "tty_get_rows" () int)
        (lambda () 24)))

  (define c-tty-get-cols
    (if *bridge-loaded*
        (foreign-procedure "tty_get_cols" () int)
        (lambda () 80)))

  (define c-tty-is-tty
    (if *bridge-loaded*
        (foreign-procedure "tty_is_tty" () int)
        (lambda () 0)))

  (define c-tty-flush-input
    (if *bridge-loaded*
        (foreign-procedure "tty_flush_input_buffer" () int)
        (lambda () -1)))

  (define c-tty-unread-char
    (if *bridge-loaded*
        (foreign-procedure "tty_unread_char" (int) int)
        (lambda (c) -1)))

  ;; ============================================================
  ;; Shell Fallbacks
  ;; ============================================================

  (define (shell-command cmd)
    "Run shell command, return trimmed output or #f."
    (guard (exn [#t #f])
      (let-values (((to-stdin from-stdout from-stderr)
                    (open-process-ports cmd 'line (native-transcoder))))
        (let ((result (get-line from-stdout)))
          (close-port to-stdin)
          (close-port from-stdout)
          (close-port from-stderr)
          (if (eof-object? result) #f result)))))

  (define (fallback-rows)
    (let ((r (shell-command "tput lines 2>/dev/null")))
      (if r (or (string->number r) 24) 24)))

  (define (fallback-cols)
    (let ((r (shell-command "tput cols 2>/dev/null")))
      (if r (or (string->number r) 80) 80)))

  (define (fallback-set-raw)
    (system "stty raw -echo 2>/dev/null")
    0)

  (define (fallback-set-cooked)
    (system "stty cooked echo 2>/dev/null")
    0)

  ;; ============================================================
  ;; Public API
  ;; ============================================================

  ;; Read one char directly from fd 0 (bypasses all buffering)
  (define (tty-raw-char)
    (c-tty-read-char))

  ;; Check if input is ready (with timeout in ms, 0 = poll)
  (define (tty-char-ready? timeout-ms)
    (not (zero? (c-tty-char-ready timeout-ms))))

  ;; Set terminal to raw mode via termios
  (define (tty-set-raw)
    (if *bridge-loaded*
        (c-tty-set-raw)
        (fallback-set-raw)))

  ;; Restore terminal to cooked mode
  (define (tty-set-cooked)
    (if *bridge-loaded*
        (c-tty-set-cooked)
        (fallback-set-cooked)))

  ;; Terminal dimensions
  (define (tty-rows)
    (if *bridge-loaded*
        (c-tty-get-rows)
        (fallback-rows)))

  (define (tty-cols)
    (if *bridge-loaded*
        (c-tty-get-cols)
        (fallback-cols)))

  ;; Check if stdin is a tty
  (define (tty?)
    (not (zero? (c-tty-is-tty))))

  ;; Flush pending input (clear buffer after pager exits)
  (define (tty-flush-input)
    (c-tty-flush-input))

  ;; Push char back onto stdin (TIOCSTI) so next read sees it
  (define (tty-unread-char c)
    (c-tty-unread-char c))

) ;; end library
