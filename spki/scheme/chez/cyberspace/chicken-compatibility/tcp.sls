;;; TCP Compatibility Library
;;; Library of Cyberspace - Chez Port
;;;
;;; Maps Chicken's (chicken tcp) API to POSIX sockets via a C bridge.
;;;
;;; Chicken API:
;;;   (tcp-connect host port) -> (values input-port output-port)
;;;   (tcp-listen port)       -> listener
;;;   (tcp-accept listener)   -> (values input-port output-port)
;;;   (tcp-close listener)    -> void
;;;
;;; Implementation:
;;;   tcp-bridge.c provides socket() / connect() / bind() / listen() /
;;;   accept() wrappers that return plain file descriptors.  Chez wraps
;;;   these with open-fd-input-port / open-fd-output-port.
;;;
;;; The fd is dup'd so that input and output ports own separate fds
;;; and can be closed independently without affecting each other.
;;;
;;; Copyright (c) 2026 Yoyodyne. See LICENSE.

(library (cyberspace chicken-compatibility tcp)
  (export
    tcp-connect
    tcp-listen
    tcp-accept
    tcp-close)

  (import (rnrs)
          (only (chezscheme)
                load-shared-object foreign-procedure
                open-fd-input-port open-fd-output-port
                buffer-mode native-transcoder
                void))

  ;; ============================================================
  ;; Load C bridge
  ;; ============================================================

  (define *tcp-bridge-loaded*
    (guard (exn [#t
      (guard (exn2 [#t
        (error 'cyberspace-tcp "Cannot load libtcp-bridge")])
        (load-shared-object "libtcp-bridge.dylib")
        #t)])
      (load-shared-object "libtcp-bridge.so")
      #t))

  ;; ============================================================
  ;; Foreign procedures
  ;; ============================================================

  (define %tcp-connect  (foreign-procedure "tcp_connect_fd" (string int) int))
  (define %tcp-listen   (foreign-procedure "tcp_listen_fd"  (int int) int))
  (define %tcp-accept   (foreign-procedure "tcp_accept_fd"  (int) int))
  (define %tcp-close    (foreign-procedure "tcp_close_fd"   (int) void))
  (define %tcp-dup      (foreign-procedure "tcp_dup_fd"     (int) int))

  ;; ============================================================
  ;; Listener record (wraps listen fd)
  ;; ============================================================

  (define *listener-tag* (list 'tcp-listener))

  (define (make-listener fd port)
    (vector *listener-tag* fd port))

  (define (listener? x)
    (and (vector? x)
         (>= (vector-length x) 3)
         (eq? (vector-ref x 0) *listener-tag*)))

  (define (listener-fd l) (vector-ref l 1))
  (define (listener-port l) (vector-ref l 2))

  ;; ============================================================
  ;; API: tcp-connect
  ;;
  ;; (tcp-connect host port) -> (values input-port output-port)
  ;;
  ;; Returns two textual ports (line-buffered output, block input)
  ;; suitable for s-expression I/O with read/write.
  ;; ============================================================

  (define (tcp-connect host port)
    (let ((fd (%tcp-connect host port)))
      (when (< fd 0)
        (error 'tcp-connect "Connection failed" host port))
      (let ((fd2 (%tcp-dup fd)))
        (when (< fd2 0)
          (%tcp-close fd)
          (error 'tcp-connect "dup failed" host port))
        (values
          (open-fd-input-port fd (buffer-mode block) (native-transcoder))
          (open-fd-output-port fd2 (buffer-mode line) (native-transcoder))))))

  ;; ============================================================
  ;; API: tcp-listen
  ;;
  ;; (tcp-listen port) -> listener
  ;; (tcp-listen port backlog) -> listener
  ;; ============================================================

  (define (tcp-listen port . rest)
    (let* ((backlog (if (null? rest) 16 (car rest)))
           (fd (%tcp-listen port backlog)))
      (when (< fd 0)
        (error 'tcp-listen "Cannot listen on port" port))
      (make-listener fd port)))

  ;; ============================================================
  ;; API: tcp-accept
  ;;
  ;; (tcp-accept listener) -> (values input-port output-port)
  ;; ============================================================

  (define (tcp-accept listener)
    (let ((fd (%tcp-accept (listener-fd listener))))
      (when (< fd 0)
        (error 'tcp-accept "Accept failed"))
      (let ((fd2 (%tcp-dup fd)))
        (when (< fd2 0)
          (%tcp-close fd)
          (error 'tcp-accept "dup failed"))
        (values
          (open-fd-input-port fd (buffer-mode block) (native-transcoder))
          (open-fd-output-port fd2 (buffer-mode line) (native-transcoder))))))

  ;; ============================================================
  ;; API: tcp-close
  ;;
  ;; (tcp-close listener) -> void
  ;; ============================================================

  (define (tcp-close listener)
    (%tcp-close (listener-fd listener)))

) ;; end library
