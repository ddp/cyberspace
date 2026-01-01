# udp6 - UDP Socket Interface for IPv4 and IPv6

**Source:** http://wiki.call-cc.org/eggref/5/udp6

**License:** BSD 2-Clause

**Dependencies:** socket

## Overview

The udp6 extension provides "an interface to User Datagram Protocol sockets over IPv4 and IPv6." It extends the earlier udp egg while maintaining backward compatibility and leverages the socket egg for implementation.

## Core Procedures

### Socket Creation

```scheme
(udp-open-socket [family])
(udp-open-socket* [family])              ; Nonblocking variant (identical)
```

Creates a UDP socket.

**Parameters:**
- `family` - Socket family: `'inet` (IPv4, default) or `'inet6` (IPv6)

**Returns:** UDP socket object

**Examples:**

```scheme
(define sock4 (udp-open-socket))         ; IPv4 socket
(define sock6 (udp-open-socket 'inet6))  ; IPv6 socket
```

### Connection Operations

#### `udp-bind!`

```scheme
(udp-bind! socket host port)
```

Binds socket to address/port.

**Parameters:**
- `socket` - UDP socket
- `host` - IP string, hostname, or `#f` for unspecified address
- `port` - Port number

**Examples:**

```scheme
(udp-bind! sock4 "127.0.0.1" 8080)       ; IPv4 localhost
(udp-bind! sock6 "::" 9000)              ; IPv6 unspecified address
(udp-bind! sock4 #f 7000)                ; Bind to any interface
```

#### `udp-connect!`

```scheme
(udp-connect! socket host port)
```

Associates peer address with socket for later sends.

**Examples:**

```scheme
(udp-connect! sock4 "example.com" 5000)
(udp-connect! sock6 "::1" 6000)          ; IPv6 localhost
```

### Data Transfer

#### `udp-send`

```scheme
(udp-send socket string)
```

Sends data to connected peer.

**Returns:** Number of bytes sent

**Example:**

```scheme
(udp-connect! sock "example.com" 5000)
(udp-send sock "Hello, UDP!")
```

#### `udp-sendto`

```scheme
(udp-sendto socket host port string)
```

Sends data to specified destination (no prior connection needed).

**Returns:** Number of bytes sent

**Example:**

```scheme
(udp-sendto sock "192.168.1.100" 8080 "Direct message")
```

#### `udp-recv`

```scheme
(udp-recv socket length)
```

Receives up to `length` bytes from socket.

**Returns:** `(values byte-count message-string)`

**Example:**

```scheme
(let-values (((n msg) (udp-recv sock 1024)))
  (printf "Received ~A bytes: ~A~%" n msg))
```

#### `udp-recvfrom`

```scheme
(udp-recvfrom socket length)
```

Like `udp-recv` but also returns source host and port.

**Returns:** `(values byte-count message-string source-host source-port)`

**Example:**

```scheme
(let-values (((n msg host port) (udp-recvfrom sock 1024)))
  (printf "~A bytes from ~A:~A: ~A~%" n host port msg))
```

### Utility Functions

```scheme
(udp-close-socket socket)               ; Closes socket
(udp-socket? thing)                     ; Tests if object is UDP socket
(udp-bound? socket)                     ; Tests binding status
(udp-connected? socket)                 ; Tests peer association
(udp-bound-port socket)                 ; Returns bound port number
```

## IPv6 Considerations

To use IPv6, create sockets with `family 'inet6`:

```scheme
(define sock6 (udp-open-socket 'inet6))
```

**Important Notes:**
- Binding to "::" (unspecified IPv6 address) may permit IPv4 connections depending on OS configuration
- IPv4 sockets cannot bind to IPv6 addresses
- IPv6 addresses can be in standard notation: "2001:db8::1", "::1", etc.

## Complete Examples

### Daytime Client

```scheme
(import udp6)

(define sock (udp-open-socket))
(udp-connect! sock "time.nist.gov" 13)
(udp-send sock "")

(let-values (((n msg) (udp-recv sock 1024)))
  (print "Time server says: " msg))

(udp-close-socket sock)
```

### Echo Server (IPv6)

```scheme
(import udp6)

(define sock (udp-open-socket 'inet6))
(udp-bind! sock "::" 1337)               ; Listen on all interfaces

(print "Echo server listening on port 1337...")

(let loop ()
  (let-values (((n msg host port) (udp-recvfrom sock 1024)))
    (printf "Received from ~A:~A: ~A~%" host port msg)
    (udp-sendto sock host port msg)     ; Echo back
    (loop)))
```

### Daytime Server

```scheme
(import udp6)
(import (chicken time posix))

(define sock (udp-open-socket))
(udp-bind! sock #f 5013)                 ; Bind to any interface

(print "Daytime server on port 5013...")

(let loop ()
  (let-values (((n msg host port) (udp-recvfrom sock 1024)))
    (let ((time-str (seconds->string (current-seconds))))
      (udp-sendto sock host port time-str)
      (printf "Sent time to ~A:~A~%" host port)
      (loop))))
```

### Simple UDP Chat

```scheme
(import udp6)
(import (chicken io))

;; Receiver thread
(define (receiver sock)
  (thread-start!
    (make-thread
      (lambda ()
        (let loop ()
          (let-values (((n msg host port) (udp-recvfrom sock 1024)))
            (printf "~A:~A> ~A~%" host port msg)
            (loop)))))))

;; Sender
(define (sender sock dest-host dest-port)
  (let loop ()
    (let ((msg (read-line)))
      (unless (eof-object? msg)
        (udp-sendto sock dest-host dest-port msg)
        (loop)))))

;; Usage
(define sock (udp-open-socket))
(udp-bind! sock #f 9000)
(receiver sock)
(sender sock "peer.example.com" 9000)
```

### Broadcast Example

```scheme
(import udp6)

(define sock (udp-open-socket))
(udp-bind! sock #f 0)                    ; Bind to ephemeral port

;; Send broadcast message
(udp-sendto sock "255.255.255.255" 8080 "Broadcast message!")

(udp-close-socket sock)
```

## Limitations

**Multicast:** Multicast functionality is not currently implemented.

## Error Handling

UDP operations can raise I/O exceptions:

```scheme
(handle-exceptions exn
  (print "UDP error: " ((condition-property-accessor 'exn 'message) exn))
  (udp-sendto sock "example.com" 5000 "Message"))
```

## Installation

```bash
chicken-install udp6
```

## See Also

- tcp6 (TCP socket interface)
- socket (underlying socket implementation)
- srfi-18 (threading for server examples)
