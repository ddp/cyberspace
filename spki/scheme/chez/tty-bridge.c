/*
 * tty-bridge.c - Terminal control bridge for Chez Scheme
 *
 * Provides raw character input via termios, terminal size detection,
 * and input buffer management for full-screen terminal apps.
 *
 * Build: cc -shared -o libtty-bridge.dylib tty-bridge.c   (macOS)
 *        cc -shared -fPIC -o libtty-bridge.so tty-bridge.c (Linux)
 */

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
    raw.c_iflag &= ~(IXON | ICRNL | BRKINT | INPCK | ISTRIP);
    raw.c_lflag &= ~(ICANON | ECHO | ISIG);
    raw.c_cc[VMIN] = 1;
    raw.c_cc[VTIME] = 0;
    if (tcsetattr(STDIN_FILENO, TCSAFLUSH, &raw) < 0) return -1;
    setvbuf(stdin, NULL, _IONBF, 0);
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

int tty_is_tty(void) {
    return isatty(STDIN_FILENO);
}

int tty_char_ready(int timeout_ms) {
    fd_set fds;
    struct timeval tv;
    FD_ZERO(&fds);
    FD_SET(STDIN_FILENO, &fds);
    tv.tv_sec = timeout_ms / 1000;
    tv.tv_usec = (timeout_ms % 1000) * 1000;
    return select(STDIN_FILENO + 1, &fds, NULL, NULL, &tv) > 0;
}

int tty_flush_input_buffer(void) {
    return tcflush(STDIN_FILENO, TCIFLUSH);
}

int tty_unread_char(int c) {
    unsigned char ch = (unsigned char)c;
    return ioctl(STDIN_FILENO, TIOCSTI, &ch);
}
