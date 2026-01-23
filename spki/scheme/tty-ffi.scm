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
#include <sys/select.h>

static struct termios orig_termios;
static int raw_mode = 0;

int tty_set_raw_mode(void) {
    struct termios raw;
    if (!isatty(STDIN_FILENO)) return -1;
    if (tcgetattr(STDIN_FILENO, &orig_termios) < 0) return -1;
    raw = orig_termios;
    raw.c_iflag &= ~(IXON | ICRNL | BRKINT | INPCK | ISTRIP);  /* disable flow control, etc. */
    raw.c_lflag &= ~(ICANON | ECHO | ISIG);  /* disable canonical mode, echo, and signals */
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

/* Check if input is available (with timeout in milliseconds) */
int tty_char_ready(int timeout_ms) {
    fd_set fds;
    struct timeval tv;
    FD_ZERO(&fds);
    FD_SET(STDIN_FILENO, &fds);
    tv.tv_sec = timeout_ms / 1000;
    tv.tv_usec = (timeout_ms % 1000) * 1000;
    return select(STDIN_FILENO + 1, &fds, NULL, NULL, &tv) > 0;
}

/* Flush pending input (discard anything queued) */
int tty_flush_input_buffer(void) {
    return tcflush(STDIN_FILENO, TCIFLUSH);
}

/* Push a character back onto stdin (TIOCSTI) */
int tty_unread_char(int c) {
    unsigned char ch = (unsigned char)c;
    return ioctl(STDIN_FILENO, TIOCSTI, &ch);
}
<#

(module tty-ffi
  (tty-raw-char
   tty-char-ready?
   tty-set-raw
   tty-set-cooked
   tty-flush-input
   tty-unread-char
   tty-rows
   tty-cols
   tty?)

  (import scheme
          (chicken base)
          (chicken foreign))

  ;; Read one char directly from fd 0 (bypasses all buffering)
  (define tty-raw-char
    (foreign-lambda int "tty_read_char"))

  ;; Check if input is ready (with timeout in ms, 0 = poll)
  (define tty-char-ready?
    (foreign-lambda bool "tty_char_ready" int))

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

  ;; Flush pending input (clear buffer after pager exits)
  (define tty-flush-input
    (foreign-lambda int "tty_flush_input_buffer"))

  ;; Push char back onto stdin (TIOCSTI) so next read sees it
  (define tty-unread-char
    (foreign-lambda int "tty_unread_char" int))

) ;; end module
