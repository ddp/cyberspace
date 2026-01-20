;;; TTY FFI - Raw character input via termios
;;;
;;; Scheme's read-char uses stdio buffering that ignores stty.
;;; This uses termios directly for true unbuffered input.
;;; Also provides terminal size detection for full-screen apps.

#>
#include <termios.h>
#include <unistd.h>
#include <stdio.h>
#include <sys/ioctl.h>

static struct termios orig_termios;
static int raw_mode = 0;

int tty_set_raw_mode(void) {
    struct termios raw;
    if (!isatty(STDIN_FILENO)) return -1;
    if (tcgetattr(STDIN_FILENO, &orig_termios) < 0) return -1;
    raw = orig_termios;
    raw.c_lflag &= ~(ICANON | ECHO);  /* disable canonical mode and echo */
    raw.c_cc[VMIN] = 1;   /* read returns after 1 char */
    raw.c_cc[VTIME] = 0;  /* no timeout */
    if (tcsetattr(STDIN_FILENO, TCSAFLUSH, &raw) < 0) return -1;
    setvbuf(stdin, NULL, _IONBF, 0);  /* disable stdio buffering too */
    raw_mode = 1;
    return 0;
}

int tty_set_cooked_mode(void) {
    if (!raw_mode) return 0;
    tcsetattr(STDIN_FILENO, TCSAFLUSH, &orig_termios);
    raw_mode = 0;
    return 0;
}

int tty_read_char(void) {
    unsigned char c;
    if (read(STDIN_FILENO, &c, 1) == 1) return c;
    return -1;
}

/* Terminal size detection */
int tty_get_rows(void) {
    struct winsize ws;
    if (ioctl(STDOUT_FILENO, TIOCGWINSZ, &ws) == -1) return 24;
    return ws.ws_row;
}

int tty_get_cols(void) {
    struct winsize ws;
    if (ioctl(STDOUT_FILENO, TIOCGWINSZ, &ws) == -1) return 80;
    return ws.ws_col;
}

/* Check if we have a tty */
int tty_is_tty(void) {
    return isatty(STDIN_FILENO);
}
<#

(module tty-ffi
  (tty-raw-char
   tty-set-raw
   tty-set-cooked
   tty-rows
   tty-cols
   tty?)

  (import scheme
          (chicken base)
          (chicken foreign))

  ;; Read one char directly from fd 0 (bypasses all buffering)
  (define tty-raw-char
    (foreign-lambda int "tty_read_char"))

  ;; Set terminal to raw mode via termios
  (define tty-set-raw
    (foreign-lambda int "tty_set_raw_mode"))

  ;; Restore terminal to cooked mode
  (define tty-set-cooked
    (foreign-lambda int "tty_set_cooked_mode"))

  ;; Terminal dimensions
  (define tty-rows
    (foreign-lambda int "tty_get_rows"))

  (define tty-cols
    (foreign-lambda int "tty_get_cols"))

  ;; Check if stdin is a tty
  (define tty?
    (foreign-lambda int "tty_is_tty"))

) ;; end module
