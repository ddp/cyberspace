/* tcp-bridge.c - POSIX TCP socket helpers for Chez Scheme
 * Library of Cyberspace - Chez Port
 *
 * Provides thin wrappers around POSIX socket API that return
 * file descriptors.  Chez wraps these with open-fd-input/output-port.
 *
 * Functions:
 *   tcp_connect_fd(host, port) -> fd or -1
 *   tcp_listen_fd(port, backlog) -> listen_fd or -1
 *   tcp_accept_fd(listen_fd) -> client_fd or -1
 *   tcp_close_fd(fd) -> void
 *   tcp_dup_fd(fd) -> dup'd fd or -1
 *
 * Copyright (c) 2026 Yoyodyne. See LICENSE.
 */

#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <arpa/inet.h>
#include <netdb.h>
#include <unistd.h>
#include <fcntl.h>
#include <string.h>
#include <errno.h>
#include <stdio.h>

/*
 * Connect to host:port.  Returns socket fd on success, -1 on failure.
 * Uses getaddrinfo for IPv4/IPv6 dual-stack support.
 */
int tcp_connect_fd(const char *host, int port) {
    struct addrinfo hints, *res, *rp;
    char port_str[16];
    int fd = -1;

    memset(&hints, 0, sizeof(hints));
    hints.ai_family = AF_UNSPEC;      /* IPv4 or IPv6 */
    hints.ai_socktype = SOCK_STREAM;

    snprintf(port_str, sizeof(port_str), "%d", port);

    if (getaddrinfo(host, port_str, &hints, &res) != 0)
        return -1;

    /* Try each address until one succeeds */
    for (rp = res; rp != NULL; rp = rp->ai_next) {
        fd = socket(rp->ai_family, rp->ai_socktype, rp->ai_protocol);
        if (fd < 0)
            continue;

        if (connect(fd, rp->ai_addr, rp->ai_addrlen) == 0)
            break;  /* Success */

        close(fd);
        fd = -1;
    }

    freeaddrinfo(res);

    if (fd >= 0) {
        /* Enable TCP_NODELAY for low-latency gossip messages */
        int one = 1;
        setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &one, sizeof(one));
    }

    return fd;
}

/*
 * Create a listening socket on port.  Returns listen fd or -1.
 * Tries IPv6 with dual-stack first, falls back to IPv4.
 */
int tcp_listen_fd(int port, int backlog) {
    int fd, one = 1;
    struct sockaddr_in6 addr6;
    struct sockaddr_in addr4;

    /* Try IPv6 dual-stack first */
    fd = socket(AF_INET6, SOCK_STREAM, 0);
    if (fd >= 0) {
        setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one));

        /* Allow both IPv4 and IPv6 */
        int zero = 0;
        setsockopt(fd, IPPROTO_IPV6, IPV6_V6ONLY, &zero, sizeof(zero));

        memset(&addr6, 0, sizeof(addr6));
        addr6.sin6_family = AF_INET6;
        addr6.sin6_port = htons(port);
        addr6.sin6_addr = in6addr_any;

        if (bind(fd, (struct sockaddr *)&addr6, sizeof(addr6)) == 0) {
            if (listen(fd, backlog) == 0)
                return fd;
        }
        close(fd);
    }

    /* Fallback to IPv4 */
    fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd < 0)
        return -1;

    setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one));

    memset(&addr4, 0, sizeof(addr4));
    addr4.sin_family = AF_INET;
    addr4.sin_port = htons(port);
    addr4.sin_addr.s_addr = INADDR_ANY;

    if (bind(fd, (struct sockaddr *)&addr4, sizeof(addr4)) < 0) {
        close(fd);
        return -1;
    }

    if (listen(fd, backlog) < 0) {
        close(fd);
        return -1;
    }

    return fd;
}

/*
 * Accept a connection on a listening socket.
 * Returns client fd or -1.
 */
int tcp_accept_fd(int listen_fd) {
    struct sockaddr_storage addr;
    socklen_t addrlen = sizeof(addr);
    int fd;

    fd = accept(listen_fd, (struct sockaddr *)&addr, &addrlen);
    if (fd >= 0) {
        int one = 1;
        setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &one, sizeof(one));
    }
    return fd;
}

/*
 * Close a socket fd.
 */
void tcp_close_fd(int fd) {
    close(fd);
}

/*
 * Duplicate a fd (for separate input/output port ownership).
 */
int tcp_dup_fd(int fd) {
    return dup(fd);
}

/*
 * Get the last socket error number.
 */
int tcp_errno(void) {
    return errno;
}
