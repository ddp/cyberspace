# tcp6 - IPv4/IPv6 TCP Socket Library

**Source:** http://wiki.call-cc.org/eggref/5/tcp6

**Dependencies:** socket

## Overview

The tcp6 egg is a CHICKEN Scheme extension that provides facilities for communicating over TCP sockets with an interface that is backwards-compatible with the core tcp unit. It supports both IPv4 and IPv6 protocols.

## Key Features

- **Dual protocol support** - IPv4 and IPv6
- **Non-blocking operations** on Windows
- **Improved error detection** on Windows platforms
- Network errors raise conditions of kind `(exn i/o net)`
- Timeouts raise `(exn i/o net timeout)` conditions

## Server Operations

### `tcp-listen`

```scheme
(tcp-listen PORT [HOST])
```

Creates a TCP listener on the specified port.

**Parameters:**
- `PORT` - Port number to listen on
- `HOST` (optional) - Restricts connections to specific interface

When `HOST` is omitted, behavior depends on the operating system but typically defaults to IPv4-only listening.

### `tcp-accept`

```scheme
(tcp-accept LISTENER)
```

Waits for incoming connections and returns input/output ports. Respects timeout settings and does not block other threads.

**Returns:** `(values input-port output-port)`

### Listener Management

```scheme
(tcp-listener? OBJECT)                  ; Check if object is a listener
(tcp-close LISTENER)                    ; Close listener
(tcp-accept-ready? LISTENER)            ; Check if connection is waiting
(tcp-listener-port LISTENER)            ; Get listener port number
(tcp-listener-socket LISTENER)          ; Get underlying socket
(tcp-listener-fileno LISTENER)          ; Get file descriptor
```

## Client Operations

### `tcp-connect`

```scheme
(tcp-connect HOST PORT)
```

Establishes outbound connection to remote host.

**Parameters:**
- `HOST` - Hostname or IP address (supports `[HOST]:PORT` notation for IPv6)
- `PORT` - Port number (can be parsed from HOST if using bracket notation)

**Examples:**

```scheme
(tcp-connect "example.com" 80)
(tcp-connect "192.168.1.1" 8080)
(tcp-connect "[::1]:9000")              ; IPv6 localhost with port
(tcp-connect "[2001:db8::1]" 80)        ; IPv6 address
```

### `tcp-connect/ai`

```scheme
(tcp-connect/ai ADDRESS-INFO-LIST)
```

Attempts connections to multiple addresses sequentially, useful for failover scenarios or multi-address hosts.

## Port Operations

### `tcp-addresses`

```scheme
(tcp-addresses PORT)
```

Retrieves connection metadata (local and remote addresses).

### `tcp-port-numbers`

```scheme
(tcp-port-numbers PORT)
```

Returns local and remote port numbers.

### `tcp-abandon-port`

```scheme
(tcp-abandon-port PORT)
```

Closes port and abandons connection.

### `tcp-port->socket`

```scheme
(tcp-port->socket PORT)
```

Provides socket-level access to the underlying socket.

## Configuration Parameters

### Timeouts

```scheme
tcp-read-timeout                        ; Default: 60000 ms
tcp-write-timeout                       ; Default: 60000 ms
tcp-connect-timeout                     ; Connection establishment timeout
tcp-accept-timeout                      ; Incoming connection wait timeout
```

**Example:**

```scheme
(tcp-read-timeout 30000)                ; 30 second read timeout
(tcp-write-timeout 30000)
```

### Buffering

```scheme
tcp-buffer-size                         ; Default: disabled
```

Controls output buffering.

### IPv6 Configuration

```scheme
tcp-bind-ipv6-only                      ; Controls IPv4-in-IPv6 socket behavior
```

## Usage Examples

### Basic Server

```scheme
(import tcp6)

(define listener (tcp-listen 8080))

(let-values (((in out) (tcp-accept listener)))
  (display "Hello, client!\n" out)
  (flush-output out)
  (close-input-port in)
  (close-output-port out))

(tcp-close listener)
```

### Echo Server

```scheme
(import tcp6)
(import (chicken io))

(define listener (tcp-listen 9000))

(let loop ()
  (let-values (((in out) (tcp-accept listener)))
    (thread-start!
      (make-thread
        (lambda ()
          (let echo-loop ()
            (let ((line (read-line in)))
              (unless (eof-object? line)
                (write-line line out)
                (flush-output out)
                (echo-loop))))
          (close-input-port in)
          (close-output-port out)))))
  (loop))
```

### Simple Client

```scheme
(import tcp6)
(import (chicken io))

(let-values (((in out) (tcp-connect "example.com" 80)))
  (display "GET / HTTP/1.0\r\n\r\n" out)
  (flush-output out)
  (let loop ()
    (let ((line (read-line in)))
      (unless (eof-object? line)
        (print line)
        (loop))))
  (close-input-port in)
  (close-output-port out))
```

### IPv6 Server

```scheme
(import tcp6)

;; Listen on IPv6 address
(define listener (tcp-listen 8080 "::1"))  ; IPv6 localhost

(let-values (((in out) (tcp-accept listener)))
  (let ((addrs (tcp-addresses in)))
    (print "Connection from: " addrs))
  (display "Hello, IPv6!\n" out)
  (flush-output out)
  (close-input-port in)
  (close-output-port out))

(tcp-close listener)
```

### Client with Timeout

```scheme
(import tcp6)

(tcp-connect-timeout 5000)              ; 5 second timeout

(handle-exceptions exn
  (print "Connection failed: " ((condition-property-accessor 'exn 'message) exn))
  (let-values (((in out) (tcp-connect "slow-server.com" 80)))
    (print "Connected!")
    (close-input-port in)
    (close-output-port out)))
```

### Multi-address Connection

```scheme
(import tcp6)

;; Try multiple addresses
(define addrs '(("backup1.example.com" 8080)
                ("backup2.example.com" 8080)
                ("backup3.example.com" 8080)))

(let ((result #f))
  (let loop ((addrs addrs))
    (unless (null? addrs)
      (handle-exceptions exn
        (loop (cdr addrs))
        (let-values (((in out) (apply tcp-connect (car addrs))))
          (set! result (cons in out))))))
  result)
```

## Migration from tcp

Replace `(use tcp)` with `(use tcp6)`. The API remains compatible while adding extensions:

**New features in tcp6:**
- `tcp-bind-v6-only` parameter
- `tcp-connect/ai` procedure
- `tcp-listener-socket` procedure
- Better IPv6 support
- Improved Windows compatibility

## Installation

```bash
chicken-install tcp6
```

## See Also

- tcp (core TCP unit)
- socket (underlying socket implementation)
- tcp-server (multithreaded server)
- openssl (SSL/TLS support)
