# tcp-server - Generic Multithreaded TCP Server

**Source:** http://wiki.call-cc.org/eggref/5/tcp-server

**Author:** Felix Winkelmann

**Dependencies:** srfi-18

## Overview

The tcp-server is "a generic multithreaded TCP server" for CHICKEN Scheme. It provides a simple way to create threaded network servers that handle multiple concurrent connections.

## Core API

### `make-tcp-server`

```scheme
(make-tcp-server LISTENER THUNK [MAXREQUESTS])
```

Returns a callable procedure that initiates the server.

**Parameters:**

- `LISTENER` - A tcp-listener object from `tcp-listen`
- `THUNK` - Zero-argument function executed for each connection
- `MAXREQUESTS` (optional) - Limits concurrent requests

**Behavior:**

For each incoming connection, a new thread executes THUNK with input/output ports connected to the client.

The returned server function accepts verbosity settings:
- `#t` - Enable default diagnostic messaging
- String - Use as prefix for diagnostic output to error port
- `#f` - Disable diagnostic output

## Customization Parameters

### Socket Operation Hooks

Three parameters allow customization of socket behavior:

```scheme
tcp-server-prepare-hard-close-procedure
tcp-server-accept-connection-procedure
tcp-server-get-addresses-procedure
```

**Default values:**
- `tcp-abandon-port` - For connection closure
- `tcp-accept` - For managing incoming connections
- `tcp-addresses` - For retrieving peer address information

## Usage Examples

### Simple Time Server

A minimal time-of-day server:

```scheme
(import tcp-server)
(import (chicken tcp))
(import (chicken time posix))

((make-tcp-server
  (tcp-listen 6504)
  (lambda ()
    (write-line (seconds->string (current-seconds)))))
 #t)  ; Enable verbose output
```

### Echo Server with Multiple Connections

```scheme
(import tcp-server)
(import (chicken tcp))
(import (chicken io))

(define (echo-handler)
  (let loop ()
    (let ((line (read-line)))
      (unless (eof-object? line)
        (write-line line)
        (flush-output)
        (loop)))))

(define server
  (make-tcp-server
    (tcp-listen 8080)
    echo-handler
    10))  ; Max 10 concurrent connections

;; Start server with verbose output
(server #t)
```

### HTTP-like Server with Custom Handler

```scheme
(import tcp-server)
(import (chicken tcp))
(import (chicken io))

(define (http-handler)
  ;; Read request
  (let ((request (read-line)))
    (display "HTTP/1.0 200 OK\r\n")
    (display "Content-Type: text/plain\r\n")
    (display "\r\n")
    (display "Hello from CHICKEN Scheme!\r\n")
    (flush-output)))

(define http-server
  (make-tcp-server
    (tcp-listen 8000)
    http-handler
    50))  ; Allow 50 concurrent connections

;; Start with custom prefix
(http-server "HTTP-SERVER: ")
```

### Server with Connection Limit

```scheme
(define limited-server
  (make-tcp-server
    (tcp-listen 9000)
    my-handler
    5))  ; Only 5 concurrent connections allowed

;; When 6th connection attempts, it will wait or be rejected
(limited-server #t)
```

## Threading Behavior

- Each connection spawns a new thread via SRFI-18
- Threads run concurrently
- MAXREQUESTS parameter controls maximum simultaneous threads
- Server blocks accepting new connections when limit is reached
- Threads terminate when handler THUNK returns

## Error Handling

The server handles connection errors gracefully:

```scheme
(define (safe-handler)
  (with-exception-handler
    (lambda (exn)
      (print "Error: " exn))
    (lambda ()
      ;; Your handler code
      (process-request))))
```

## Connection Management

The server manages connections through customizable procedures:

```scheme
;; Custom connection acceptance
(tcp-server-accept-connection-procedure
  (lambda (listener)
    (print "Accepting connection...")
    (tcp-accept listener)))

;; Custom connection closure
(tcp-server-prepare-hard-close-procedure
  (lambda (in out)
    (print "Closing connection...")
    (tcp-abandon-port in)
    (tcp-abandon-port out)))

;; Custom address retrieval
(tcp-server-get-addresses-procedure
  (lambda (in)
    (let ((addr (tcp-addresses in)))
      (print "Connection from: " addr)
      addr)))
```

## Installation

```bash
chicken-install tcp-server
```

## See Also

- tcp / tcp6 (TCP socket operations)
- srfi-18 (threading)
- spiffy (HTTP server framework)
