/*
 * tcp-bridge.c - Minimal TCP socket bridge for Chez Scheme
 *
 * Provides connect/listen/accept/close operations returning
 * file descriptors that Chez wraps with open-fd-input/output-port.
 *
 * Build: cc -shared -o libtcp-bridge.dylib tcp-bridge.c   (macOS)
 *        cc -shared -fPIC -o libtcp-bridge.so tcp-bridge.c (Linux)
 */

#include <stdio.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <netdb.h>
#include <unistd.h>
#include <fcntl.h>
#include <string.h>
#include <errno.h>

/* tcp_connect(host, port) -> fd or -1 */
int tcp_connect(const char *host, int port) {
    struct addrinfo hints, *res, *rp;
    char port_str[16];
    int fd = -1;

    memset(&hints, 0, sizeof(hints));
    hints.ai_family = AF_UNSPEC;
    hints.ai_socktype = SOCK_STREAM;
    snprintf(port_str, sizeof(port_str), "%d", port);

    if (getaddrinfo(host, port_str, &hints, &res) != 0)
        return -1;

    for (rp = res; rp != NULL; rp = rp->ai_next) {
        fd = socket(rp->ai_family, rp->ai_socktype, rp->ai_protocol);
        if (fd == -1) continue;
        if (connect(fd, rp->ai_addr, rp->ai_addrlen) == 0) break;
        close(fd);
        fd = -1;
    }
    freeaddrinfo(res);
    return fd;
}

/* tcp_listen(port, backlog) -> listening fd or -1 */
int tcp_listen(int port, int backlog) {
    int fd, opt = 1;
    struct sockaddr_in6 addr;

    fd = socket(AF_INET6, SOCK_STREAM, 0);
    if (fd < 0) return -1;

    setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &opt, sizeof(opt));

    /* Dual-stack: accept both IPv4 and IPv6 */
    opt = 0;
    setsockopt(fd, IPPROTO_IPV6, IPV6_V6ONLY, &opt, sizeof(opt));

    memset(&addr, 0, sizeof(addr));
    addr.sin6_family = AF_INET6;
    addr.sin6_port = htons(port);
    addr.sin6_addr = in6addr_any;

    if (bind(fd, (struct sockaddr *)&addr, sizeof(addr)) < 0) {
        close(fd);
        return -1;
    }
    if (listen(fd, backlog) < 0) {
        close(fd);
        return -1;
    }
    return fd;
}

/* tcp_accept(listen_fd) -> connected fd or -1 */
int tcp_accept(int listen_fd) {
    struct sockaddr_storage addr;
    socklen_t len = sizeof(addr);
    return accept(listen_fd, (struct sockaddr *)&addr, &len);
}

/* tcp_close(fd) -> 0 on success */
int tcp_close(int fd) {
    return close(fd);
}

/* tcp_fd_dup(fd) -> duplicated fd (for separate in/out ports) */
int tcp_fd_dup(int fd) {
    return dup(fd);
}

/* tcp_get_errno() -> errno value for error diagnosis */
int tcp_get_errno(void) {
    return errno;
}
