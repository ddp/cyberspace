;;; osc.scm - Open Sound Control for Cyberspace
;;;
;;; Simple OSC send/receive for Max/MSP, TouchOSC, etc.
;;; UDP-based, real-time control protocol.
;;;
;;; Copyright (c) 2026 Yoyodyne. See LICENSE.

(module osc
  (osc-send osc-listen osc-server
   osc-connect osc-close osc-encode
   ;; Address patterns
   /status /soup /gossip /lamport /keys)

(import scheme)
(import (chicken base))
(import (chicken format))
(import (chicken blob))
(import (chicken bitwise))
(import (chicken io))
(import (chicken port))
(import (chicken foreign))
(import srfi-1)
(import srfi-4)  ; u8vector
(import srfi-18) ; threads
(import udp)

;; IEEE 754 float conversion via FFI
(foreign-declare #<<EOF
#include <stdint.h>
#include <string.h>

/* Convert float to big-endian bytes */
static void float_to_bytes(float f, unsigned char *out) {
    uint32_t bits;
    memcpy(&bits, &f, 4);
    /* Convert to big-endian */
    out[0] = (bits >> 24) & 0xff;
    out[1] = (bits >> 16) & 0xff;
    out[2] = (bits >> 8) & 0xff;
    out[3] = bits & 0xff;
}

/* Convert big-endian bytes to float */
static float bytes_to_float(unsigned char *in) {
    uint32_t bits = ((uint32_t)in[0] << 24) |
                    ((uint32_t)in[1] << 16) |
                    ((uint32_t)in[2] << 8) |
                    (uint32_t)in[3];
    float f;
    memcpy(&f, &bits, 4);
    return f;
}
EOF
)

(define c-float-to-bytes
  (foreign-lambda* void ((float f) (u8vector out))
    "float_to_bytes(f, out);"))

(define c-bytes-to-float
  (foreign-lambda* float ((u8vector in))
    "C_return(bytes_to_float(in));"))

;; OSC packet encoding
;; Address: null-terminated, padded to 4 bytes
;; Type tag: ,ifs... (int, float, string)
;; Data: each arg padded to 4 bytes

(define (pad-to-4 len)
  "Round up to next multiple of 4"
  (* 4 (quotient (+ len 4) 4)))

(define (string->osc-bytes s)
  "Encode string as null-terminated, 4-byte padded"
  (let* ((len (string-length s))
         (padded-len (pad-to-4 (+ len 1)))
         (result (make-u8vector padded-len 0)))
    (do ((i 0 (+ i 1)))
        ((= i len))
      (u8vector-set! result i (char->integer (string-ref s i))))
    result))

(define (int32->bytes n)
  "Encode 32-bit int big-endian"
  (u8vector
    (bitwise-and (arithmetic-shift n -24) #xff)
    (bitwise-and (arithmetic-shift n -16) #xff)
    (bitwise-and (arithmetic-shift n -8) #xff)
    (bitwise-and n #xff)))

(define (float32->bytes f)
  "Encode 32-bit float (IEEE 754 big-endian)"
  (let ((out (make-u8vector 4 0)))
    (c-float-to-bytes (exact->inexact f) out)
    out))

(define (bytes->int32 data offset)
  "Decode 32-bit int from big-endian bytes"
  (let ((b0 (u8vector-ref data offset))
        (b1 (u8vector-ref data (+ offset 1)))
        (b2 (u8vector-ref data (+ offset 2)))
        (b3 (u8vector-ref data (+ offset 3))))
    (bitwise-ior (arithmetic-shift b0 24)
                 (arithmetic-shift b1 16)
                 (arithmetic-shift b2 8)
                 b3)))

(define (bytes->float32 data offset)
  "Decode 32-bit float (IEEE 754 big-endian)"
  (let ((tmp (make-u8vector 4)))
    (u8vector-set! tmp 0 (u8vector-ref data offset))
    (u8vector-set! tmp 1 (u8vector-ref data (+ offset 1)))
    (u8vector-set! tmp 2 (u8vector-ref data (+ offset 2)))
    (u8vector-set! tmp 3 (u8vector-ref data (+ offset 3)))
    (c-bytes-to-float tmp)))

(define (bytes->osc-string data offset)
  "Decode null-terminated string, return (string . new-offset)"
  (let loop ((i offset) (chars '()))
    (if (or (>= i (u8vector-length data))
            (= (u8vector-ref data i) 0))
        (let* ((s (list->string (reverse chars)))
               (end (pad-to-4 (+ (- i offset) 1))))
          (cons s (+ offset end)))
        (loop (+ i 1) (cons (integer->char (u8vector-ref data i)) chars)))))

(define (osc-encode address . args)
  "Encode OSC message: address + type tag + args"
  (let* ((addr-bytes (string->osc-bytes address))
         (type-tag (string-append ","
                     (apply string-append
                       (map (lambda (a)
                              (cond ((integer? a) "i")
                                    ((flonum? a) "f")
                                    ((string? a) "s")
                                    (else "i")))
                            args))))
         (tag-bytes (string->osc-bytes type-tag))
         (arg-bytes (apply u8vector-append
                      (map (lambda (a)
                             (cond ((integer? a) (int32->bytes a))
                                   ((flonum? a) (float32->bytes a))
                                   ((string? a) (string->osc-bytes a))
                                   (else (int32->bytes 0))))
                           args))))
    (u8vector-append addr-bytes tag-bytes arg-bytes)))

(define (u8vector-append . vecs)
  "Concatenate u8vectors"
  (let* ((total (apply + (map u8vector-length vecs)))
         (result (make-u8vector total)))
    (let loop ((vecs vecs) (offset 0))
      (if (null? vecs)
          result
          (let ((v (car vecs)))
            (do ((i 0 (+ i 1)))
                ((= i (u8vector-length v)))
              (u8vector-set! result (+ offset i) (u8vector-ref v i)))
            (loop (cdr vecs) (+ offset (u8vector-length v))))))))

;; Connection state
(define *osc-host* "127.0.0.1")
(define *osc-port* 9000)  ; TouchOSC default
(define *osc-socket* #f)
(define *osc-listener* #f)
(define *osc-running* #f)

(define (osc-connect #!optional (host "127.0.0.1") (port 9000))
  "Connect to OSC destination (Max, TouchOSC, etc.)"
  (set! *osc-host* host)
  (set! *osc-port* port)
  (unless *osc-socket*
    (set! *osc-socket* (udp-open-socket)))
  (printf "OSC connected to ~a:~a~%" host port))

(define (osc-send address . args)
  "Send OSC message via UDP"
  (let ((packet (apply osc-encode address args)))
    (unless *osc-socket*
      (set! *osc-socket* (udp-open-socket)))
    (udp-sendto *osc-socket* *osc-host* *osc-port*
                (blob->string (u8vector->blob/shared packet)))
    packet))

(define (osc-close)
  "Close OSC connection"
  (set! *osc-running* #f)
  (when *osc-socket*
    (udp-close-socket *osc-socket*)
    (set! *osc-socket* #f))
  (when *osc-listener*
    (udp-close-socket *osc-listener*)
    (set! *osc-listener* #f))
  (print "OSC closed"))

;; Convenience addresses for Cyberspace
(define (/status)
  "Send vault status via OSC"
  (osc-send "/cyberspace/status" 1))

(define (/soup #!optional (count 0))
  "Send soup object count"
  (osc-send "/cyberspace/soup" count))

(define (/gossip msg)
  "Send gossip event"
  (osc-send "/cyberspace/gossip" msg))

(define (/lamport tick)
  "Send Lamport clock tick"
  (osc-send "/cyberspace/lamport" tick))

(define (/keys count)
  "Send key count"
  (osc-send "/cyberspace/keys" count))

;; OSC packet decoding
(define (osc-decode packet)
  "Decode OSC packet, return (address type-tag arg1 arg2 ...)"
  (let* ((data (if (blob? packet) (blob->u8vector/shared packet) packet))
         (len (u8vector-length data)))
    (if (< len 4)
        #f
        ;; Parse address
        (let* ((addr-result (bytes->osc-string data 0))
               (address (car addr-result))
               (tag-offset (cdr addr-result)))
          (if (>= tag-offset len)
              (list address)
              ;; Parse type tag
              (let* ((tag-result (bytes->osc-string data tag-offset))
                     (type-tag (car tag-result))
                     (arg-offset (cdr tag-result))
                     ;; Skip leading comma in type-tag
                     (types (if (and (> (string-length type-tag) 0)
                                     (char=? (string-ref type-tag 0) #\,))
                                (substring type-tag 1)
                                type-tag)))
                ;; Parse arguments based on type-tag
                (let loop ((i 0) (offset arg-offset) (args '()))
                  (if (>= i (string-length types))
                      (cons address (cons type-tag (reverse args)))
                      (let ((type (string-ref types i)))
                        (cond
                          ;; Integer (4 bytes)
                          ((char=? type #\i)
                           (if (> (+ offset 4) len)
                               (cons address (cons type-tag (reverse args)))
                               (loop (+ i 1) (+ offset 4)
                                     (cons (bytes->int32 data offset) args))))
                          ;; Float (4 bytes)
                          ((char=? type #\f)
                           (if (> (+ offset 4) len)
                               (cons address (cons type-tag (reverse args)))
                               (loop (+ i 1) (+ offset 4)
                                     (cons (bytes->float32 data offset) args))))
                          ;; String (null-terminated, padded)
                          ((char=? type #\s)
                           (let* ((str-result (bytes->osc-string data offset))
                                  (s (car str-result))
                                  (new-offset (cdr str-result)))
                             (loop (+ i 1) new-offset (cons s args))))
                          ;; Unknown type, skip
                          (else
                           (loop (+ i 1) offset args))))))))))))

;; Receiver
(define (osc-listen port handler)
  "Listen for incoming OSC on port, call handler for each message.
   Handler receives: (address type-tag . args)"
  (set! *osc-listener* (udp-open-socket))
  (udp-bind! *osc-listener* port "0.0.0.0")
  (set! *osc-running* #t)
  (printf "OSC listening on port ~a~%" port)
  (thread-start!
   (make-thread
    (lambda ()
      (let loop ()
        (when *osc-running*
          (let-values (((n data host port) (udp-recvfrom *osc-listener* 1024)))
            (when (> n 0)
              (let ((msg (osc-decode data)))
                (when msg
                  (handler msg)))))
          (loop))))
    'osc-listener)))

(define (osc-server port)
  "Start OSC server (bidirectional) - listen and respond"
  (osc-listen port
    (lambda (msg)
      (let ((address (car msg)))
        (printf "OSC recv: ~a~%" address)
        ;; Echo back acknowledgment
        (osc-send (string-append address "/ack") 1)))))

) ; end module
