;;; TCP Socket Abstraction - Chez Scheme
;;;
;;; Wraps POSIX TCP operations via libtcp-bridge for use by gossip protocol.
;;; Returns Chez Scheme ports from file descriptors.
;;;
;;; Build the bridge: cc -shared -o libtcp-bridge.dylib tcp-bridge.c
;;;
;;; Architecture:
;;;   Chez Scheme → foreign-procedure → libtcp-bridge → POSIX sockets

(library (cyberspace tcp)
  (export
    tcp-connect       ; (host port) → (values input-port output-port)
    tcp-listen        ; (port) → listener
    tcp-accept        ; (listener) → (values input-port output-port)
    tcp-close         ; (listener) → void
    tcp-available?)   ; → #t if bridge loaded

  (import (rnrs)
          (only (chezscheme)
                load-shared-object foreign-procedure
                open-fd-input-port open-fd-output-port
                make-transcoder utf-8-codec
                native-eol-style buffer-mode))

  ;; ============================================================
  ;; Library Loading
  ;; ============================================================

  (define *tcp-bridge-loaded*
    (let loop ((paths '("./libtcp-bridge.dylib"
                        "../libtcp-bridge.dylib"
                        "libtcp-bridge.dylib"
                        "./libtcp-bridge.so"
                        "../libtcp-bridge.so"
                        "libtcp-bridge.so")))
      (if (null? paths)
          #f
          (guard (exn [#t (loop (cdr paths))])
            (load-shared-object (car paths))
            #t))))

  (define (tcp-available?) *tcp-bridge-loaded*)

  ;; ============================================================
  ;; Foreign Procedures (deferred)
  ;; ============================================================

  (define-syntax define-tcp-foreign
    (syntax-rules ()
      [(_ name expr)
       (define name
         (if *tcp-bridge-loaded*
             expr
             (lambda args
               (error 'tcp "TCP bridge not loaded -- build libtcp-bridge"))))]))

  (define-tcp-foreign %tcp-connect
    (foreign-procedure "tcp_connect" (string int) int))

  (define-tcp-foreign %tcp-listen
    (foreign-procedure "tcp_listen" (int int) int))

  (define-tcp-foreign %tcp-accept
    (foreign-procedure "tcp_accept" (int) int))

  (define-tcp-foreign %tcp-close
    (foreign-procedure "tcp_close" (int) int))

  (define-tcp-foreign %tcp-fd-dup
    (foreign-procedure "tcp_fd_dup" (int) int))

  ;; ============================================================
  ;; Scheme API
  ;; ============================================================

  (define *text-transcoder*
    (make-transcoder (utf-8-codec) (native-eol-style)))

  (define (fd->ports fd)
    "Convert a file descriptor into separate input and output ports."
    (let ((fd2 (%tcp-fd-dup fd)))
      (values
       (open-fd-input-port fd (buffer-mode block) *text-transcoder*)
       (open-fd-output-port fd2 (buffer-mode line) *text-transcoder*))))

  (define (tcp-connect host port)
    "Connect to host:port, return (values input-port output-port)."
    (let ((fd (%tcp-connect host port)))
      (when (< fd 0)
        (error 'tcp-connect "Connection failed" host port))
      (fd->ports fd)))

  (define (tcp-listen port)
    "Listen on port, return listener handle (fd)."
    (let ((fd (%tcp-listen port 16)))
      (when (< fd 0)
        (error 'tcp-listen "Listen failed" port))
      fd))

  (define (tcp-accept listener)
    "Accept connection on listener, return (values input-port output-port)."
    (let ((fd (%tcp-accept listener)))
      (when (< fd 0)
        (error 'tcp-accept "Accept failed"))
      (fd->ports fd)))

  (define (tcp-close listener)
    "Close a listener socket."
    (%tcp-close listener))

) ;; end library
