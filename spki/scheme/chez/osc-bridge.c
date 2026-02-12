/*
 * osc-bridge.c - UDP socket + IEEE 754 float bridge for Chez Scheme
 *
 * Provides:
 *   - UDP socket operations (open, bind, sendto, recvfrom, close)
 *   - IEEE 754 float-to-bytes and bytes-to-float conversion
 *
 * Build: cc -shared -o libosc-bridge.dylib osc-bridge.c   (macOS)
 *        cc -shared -fPIC -o libosc-bridge.so osc-bridge.c (Linux)
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <unistd.h>
#include <errno.h>

/* ============================================================
 * IEEE 754 Float Conversion
 * ============================================================ */

/* Convert float to 4 big-endian bytes, store at out[0..3] */
void osc_float_to_bytes(float f, unsigned char *out) {
    uint32_t bits;
    memcpy(&bits, &f, 4);
    out[0] = (bits >> 24) & 0xff;
    out[1] = (bits >> 16) & 0xff;
    out[2] = (bits >> 8) & 0xff;
    out[3] = bits & 0xff;
}

/* Convert 4 big-endian bytes to float */
float osc_bytes_to_float(unsigned char *in) {
    uint32_t bits = ((uint32_t)in[0] << 24) |
                    ((uint32_t)in[1] << 16) |
                    ((uint32_t)in[2] << 8) |
                    (uint32_t)in[3];
    float f;
    memcpy(&f, &bits, 4);
    return f;
}

/* ============================================================
 * UDP Socket Operations
 * ============================================================ */

/* Open a UDP socket, return fd or -1 */
int osc_udp_open(void) {
    return socket(AF_INET, SOCK_DGRAM, 0);
}

/* Bind UDP socket to port on all interfaces */
int osc_udp_bind(int fd, int port) {
    struct sockaddr_in addr;
    int opt = 1;
    setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &opt, sizeof(opt));
    memset(&addr, 0, sizeof(addr));
    addr.sin_family = AF_INET;
    addr.sin_port = htons(port);
    addr.sin_addr.s_addr = INADDR_ANY;
    return bind(fd, (struct sockaddr *)&addr, sizeof(addr));
}

/* Send data via UDP to host:port.
 * Returns bytes sent or -1 on error. */
int osc_udp_sendto(int fd, const char *host, int port,
                   const char *data, int len) {
    struct sockaddr_in addr;
    memset(&addr, 0, sizeof(addr));
    addr.sin_family = AF_INET;
    addr.sin_port = htons(port);
    inet_pton(AF_INET, host, &addr.sin_addr);
    return (int)sendto(fd, data, len, 0,
                       (struct sockaddr *)&addr, sizeof(addr));
}

/* Receive data via UDP.
 * Stores sender host as string in host_out (must be >= 64 bytes).
 * Stores sender port in *port_out.
 * Returns bytes received or -1 on error. */
int osc_udp_recvfrom(int fd, char *buf, int buflen,
                     char *host_out, int *port_out) {
    struct sockaddr_in addr;
    socklen_t addrlen = sizeof(addr);
    int n = (int)recvfrom(fd, buf, buflen, 0,
                          (struct sockaddr *)&addr, &addrlen);
    if (n >= 0) {
        inet_ntop(AF_INET, &addr.sin_addr, host_out, 64);
        *port_out = ntohs(addr.sin_port);
    }
    return n;
}

/* Close UDP socket */
int osc_udp_close(int fd) {
    return close(fd);
}
