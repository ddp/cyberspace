;;; osc.sls - Open Sound Control for Cyberspace
;;;
;;; Simple OSC send/receive for Max/MSP, TouchOSC, etc.
;;; UDP-based, real-time control protocol.
;;;
;;; Build the bridge: cc -shared -o libosc-bridge.dylib osc-bridge.c

(library (cyberspace osc)
  (export
    osc-send osc-listen osc-server
    osc-connect osc-close osc-encode osc-decode
    osc-available?
    ;; Address patterns
    osc/status osc/soup osc/gossip osc/lamport osc/keys)

  (import (rnrs)
          (rnrs mutable-strings)
          (only (chezscheme)
                printf format
                load-shared-object foreign-procedure
                foreign-alloc foreign-free foreign-ref foreign-set!
                fork-thread make-mutex mutex-acquire mutex-release
                sleep make-time))

  ;; ============================================================
  ;; Library Loading
  ;; ============================================================

  (define *osc-bridge-loaded*
    (let loop ((paths '("./libosc-bridge.dylib"
                        "../libosc-bridge.dylib"
                        "libosc-bridge.dylib"
                        "./libosc-bridge.so"
                        "../libosc-bridge.so"
                        "libosc-bridge.so")))
      (if (null? paths)
          #f
          (guard (exn [#t (loop (cdr paths))])
            (load-shared-object (car paths))
            #t))))

  (define (osc-available?) *osc-bridge-loaded*)

  ;; ============================================================
  ;; Foreign Procedures
  ;; ============================================================

  (define-syntax define-osc-foreign
    (syntax-rules ()
      [(_ name expr)
       (define name
         (if *osc-bridge-loaded*
             expr
             (lambda args
               (error 'osc "OSC bridge not loaded -- build libosc-bridge"))))]))

  (define-osc-foreign %udp-open
    (foreign-procedure "osc_udp_open" () int))

  (define-osc-foreign %udp-bind
    (foreign-procedure "osc_udp_bind" (int int) int))

  (define-osc-foreign %udp-sendto
    (foreign-procedure "osc_udp_sendto" (int string int string int) int))

  (define-osc-foreign %udp-recvfrom
    (foreign-procedure "osc_udp_recvfrom" (int void* int void* void*) int))

  (define-osc-foreign %udp-close
    (foreign-procedure "osc_udp_close" (int) int))

  (define-osc-foreign %float-to-bytes
    (foreign-procedure "osc_float_to_bytes" (float void*) void))

  (define-osc-foreign %bytes-to-float
    (foreign-procedure "osc_bytes_to_float" (void*) float))

  ;; ============================================================
  ;; OSC Packet Encoding
  ;; ============================================================

  (define (pad-to-4 len)
    (* 4 (div (+ len 4) 4)))

  (define (string->osc-bytes s)
    (let* ((len (string-length s))
           (padded-len (pad-to-4 (+ len 1)))
           (result (make-bytevector padded-len 0)))
      (do ((i 0 (+ i 1))) ((= i len))
        (bytevector-u8-set! result i (char->integer (string-ref s i))))
      result))

  (define (int32->bytes n)
    (let ((bv (make-bytevector 4 0)))
      (bytevector-u8-set! bv 0 (bitwise-and (bitwise-arithmetic-shift-right n 24) #xff))
      (bytevector-u8-set! bv 1 (bitwise-and (bitwise-arithmetic-shift-right n 16) #xff))
      (bytevector-u8-set! bv 2 (bitwise-and (bitwise-arithmetic-shift-right n 8) #xff))
      (bytevector-u8-set! bv 3 (bitwise-and n #xff))
      bv))

  (define (float32->bytes f)
    (let ((buf (foreign-alloc 4))
          (result (make-bytevector 4 0)))
      (%float-to-bytes (inexact f) buf)
      (do ((i 0 (+ i 1))) ((= i 4))
        (bytevector-u8-set! result i (foreign-ref 'unsigned-8 buf i)))
      (foreign-free buf)
      result))

  (define (bytes->int32 data offset)
    (bitwise-ior
      (bitwise-arithmetic-shift-left (bytevector-u8-ref data offset) 24)
      (bitwise-arithmetic-shift-left (bytevector-u8-ref data (+ offset 1)) 16)
      (bitwise-arithmetic-shift-left (bytevector-u8-ref data (+ offset 2)) 8)
      (bytevector-u8-ref data (+ offset 3))))

  (define (bytes->float32 data offset)
    (let ((buf (foreign-alloc 4)))
      (do ((i 0 (+ i 1))) ((= i 4))
        (foreign-set! 'unsigned-8 buf i (bytevector-u8-ref data (+ offset i))))
      (let ((f (%bytes-to-float buf)))
        (foreign-free buf)
        f)))

  (define (bytes->osc-string data offset)
    (let loop ((i offset) (chars '()))
      (if (or (>= i (bytevector-length data))
              (= (bytevector-u8-ref data i) 0))
          (let* ((s (list->string (reverse chars)))
                 (end (pad-to-4 (+ (- i offset) 1))))
            (cons s (+ offset end)))
          (loop (+ i 1) (cons (integer->char (bytevector-u8-ref data i)) chars)))))

  (define (bytevector-append . bvs)
    (let* ((total (apply + (map bytevector-length bvs)))
           (result (make-bytevector total 0)))
      (let loop ((bvs bvs) (offset 0))
        (if (null? bvs)
            result
            (let ((bv (car bvs)))
              (bytevector-copy! bv 0 result offset (bytevector-length bv))
              (loop (cdr bvs) (+ offset (bytevector-length bv))))))))

  (define (osc-encode address . args)
    (let* ((addr-bytes (string->osc-bytes address))
           (type-tag (string-append ","
                       (apply string-append
                         (map (lambda (a)
                                (cond ((and (integer? a) (exact? a)) "i")
                                      ((and (number? a) (inexact? a)) "f")
                                      ((string? a) "s")
                                      (else "i")))
                              args))))
           (tag-bytes (string->osc-bytes type-tag))
           (arg-bytes (apply bytevector-append
                        (map (lambda (a)
                               (cond ((and (integer? a) (exact? a)) (int32->bytes a))
                                     ((and (number? a) (inexact? a)) (float32->bytes a))
                                     ((string? a) (string->osc-bytes a))
                                     (else (int32->bytes 0))))
                             args))))
      (bytevector-append addr-bytes tag-bytes arg-bytes)))

  ;; ============================================================
  ;; OSC Packet Decoding
  ;; ============================================================

  (define (osc-decode packet)
    (let* ((data (if (bytevector? packet) packet
                     (string->utf8 packet)))
           (len (bytevector-length data)))
      (if (< len 4)
          #f
          (let* ((addr-result (bytes->osc-string data 0))
                 (address (car addr-result))
                 (tag-offset (cdr addr-result)))
            (if (>= tag-offset len)
                (list address)
                (let* ((tag-result (bytes->osc-string data tag-offset))
                       (type-tag (car tag-result))
                       (arg-offset (cdr tag-result))
                       (types (if (and (> (string-length type-tag) 0)
                                       (char=? (string-ref type-tag 0) #\,))
                                  (substring type-tag 1 (string-length type-tag))
                                  type-tag)))
                  (let loop ((i 0) (offset arg-offset) (args '()))
                    (if (>= i (string-length types))
                        (cons address (cons type-tag (reverse args)))
                        (let ((type (string-ref types i)))
                          (cond
                            ((char=? type #\i)
                             (if (> (+ offset 4) len)
                                 (cons address (cons type-tag (reverse args)))
                                 (loop (+ i 1) (+ offset 4)
                                       (cons (bytes->int32 data offset) args))))
                            ((char=? type #\f)
                             (if (> (+ offset 4) len)
                                 (cons address (cons type-tag (reverse args)))
                                 (loop (+ i 1) (+ offset 4)
                                       (cons (bytes->float32 data offset) args))))
                            ((char=? type #\s)
                             (let* ((str-result (bytes->osc-string data offset))
                                    (s (car str-result))
                                    (new-offset (cdr str-result)))
                               (loop (+ i 1) new-offset (cons s args))))
                            (else
                             (loop (+ i 1) offset args))))))))))))

  ;; ============================================================
  ;; Connection State
  ;; ============================================================

  (define *osc-host* "127.0.0.1")
  (define *osc-port* 9000)
  (define *osc-socket* -1)
  (define *osc-listener* -1)
  (define *osc-running* #f)

  (define (osc-connect . rest)
    (let ((host (if (null? rest) "127.0.0.1" (car rest)))
          (port (if (or (null? rest) (null? (cdr rest))) 9000 (cadr rest))))
      (set! *osc-host* host)
      (set! *osc-port* port)
      (when (< *osc-socket* 0)
        (set! *osc-socket* (%udp-open)))
      (printf "OSC connected to ~a:~a~n" host port)))

  (define (osc-send address . args)
    (let ((packet (apply osc-encode address args)))
      (when (< *osc-socket* 0)
        (set! *osc-socket* (%udp-open)))
      ;; Convert bytevector to string for sendto
      (let ((str (make-string (bytevector-length packet))))
        (do ((i 0 (+ i 1))) ((= i (bytevector-length packet)))
          (string-set! str i (integer->char (bytevector-u8-ref packet i))))
        (%udp-sendto *osc-socket* *osc-host* *osc-port* str (string-length str)))
      packet))

  (define (osc-close)
    (set! *osc-running* #f)
    (when (>= *osc-socket* 0)
      (%udp-close *osc-socket*)
      (set! *osc-socket* -1))
    (when (>= *osc-listener* 0)
      (%udp-close *osc-listener*)
      (set! *osc-listener* -1))
    (display "OSC closed") (newline))

  ;; ============================================================
  ;; Convenience Addresses
  ;; ============================================================

  (define (osc/status)
    (osc-send "/cyberspace/status" 1))

  (define (osc/soup . rest)
    (osc-send "/cyberspace/soup" (if (null? rest) 0 (car rest))))

  (define (osc/gossip msg)
    (osc-send "/cyberspace/gossip" msg))

  (define (osc/lamport tick)
    (osc-send "/cyberspace/lamport" tick))

  (define (osc/keys count)
    (osc-send "/cyberspace/keys" count))

  ;; ============================================================
  ;; Receiver
  ;; ============================================================

  (define (osc-listen port handler)
    (set! *osc-listener* (%udp-open))
    (%udp-bind *osc-listener* port)
    (set! *osc-running* #t)
    (printf "OSC listening on port ~a~n" port)
    (fork-thread
      (lambda ()
        (let ((buf (foreign-alloc 1024))
              (host-buf (foreign-alloc 64))
              (port-buf (foreign-alloc 4)))
          (let loop ()
            (when *osc-running*
              (let ((n (%udp-recvfrom *osc-listener* buf 1024 host-buf port-buf)))
                (when (> n 0)
                  (let ((data (make-bytevector n)))
                    (do ((i 0 (+ i 1))) ((= i n))
                      (bytevector-u8-set! data i (foreign-ref 'unsigned-8 buf i)))
                    (let ((msg (osc-decode data)))
                      (when msg (handler msg))))))
              (loop)))
          (foreign-free buf)
          (foreign-free host-buf)
          (foreign-free port-buf)))))

  (define (osc-server port)
    (osc-listen port
      (lambda (msg)
        (let ((address (car msg)))
          (printf "OSC recv: ~a~n" address)
          (osc-send (string-append address "/ack") 1)))))

) ;; end library
