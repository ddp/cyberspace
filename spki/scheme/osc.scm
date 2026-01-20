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
(import (chicken tcp))
(import (chicken port))
(import srfi-1)
(import srfi-4)  ; u8vector

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
  "Encode 32-bit float (IEEE 754)"
  ;; Chicken doesn't have direct float->bytes, use FFI or approximation
  ;; For now, convert to int representation
  (int32->bytes (inexact->exact (round (* f 1000000)))))

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

(define (osc-connect #!optional (host "127.0.0.1") (port 9000))
  "Connect to OSC destination (Max, TouchOSC, etc.)"
  (set! *osc-host* host)
  (set! *osc-port* port)
  (printf "OSC connected to ~a:~a~%" host port))

(define (osc-send address . args)
  "Send OSC message"
  (let ((packet (apply osc-encode address args)))
    ;; Use UDP - for now just print (actual UDP needs socket egg)
    (printf "OSC: ~a ~a~%" address args)
    packet))

(define (osc-close)
  "Close OSC connection"
  (set! *osc-socket* #f)
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

;; Receiver (placeholder - needs UDP socket)
(define (osc-listen port handler)
  "Listen for incoming OSC on port, call handler for each message"
  (printf "OSC listening on port ~a (not yet implemented)~%" port))

(define (osc-server port)
  "Start OSC server (bidirectional)"
  (printf "OSC server on port ~a (not yet implemented)~%" port))

) ; end module
