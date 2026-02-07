;;; osc.sls - Open Sound Control for Cyberspace (Chez Port)
;;; Library of Cyberspace
;;;
;;; Simple OSC send/receive for Max/MSP, TouchOSC, etc.
;;; UDP-based, real-time control protocol.
;;;
;;; IEEE 754 float encoding uses R6RS bytevector-ieee-single-ref/set!
;;; (replaces Chicken's C FFI float conversion).
;;;
;;; Note: UDP send/receive requires udp-bridge.c (not yet built).
;;; Encoding/decoding is fully functional for testing without network.
;;;
;;; Ported from osc.scm.
;;; Copyright (c) 2026 Yoyodyne. See LICENSE.

(library (cyberspace osc)
  (export
    osc-send osc-listen osc-server
    osc-connect osc-close osc-encode osc-decode
    ;; Address patterns
    /status /soup /gossip /lamport /keys)

  (import (rnrs)
          (only (chezscheme)
                printf format void
                bytevector-ieee-single-native-ref
                bytevector-ieee-single-native-set!
                flush-output-port)
          (cyberspace chicken-compatibility chicken)
          (cyberspace chicken-compatibility thread))

  ;; ============================================================
  ;; OSC Packet Encoding
  ;; ============================================================
  ;;
  ;; Address: null-terminated, padded to 4 bytes
  ;; Type tag: ,ifs... (int, float, string)
  ;; Data: each arg padded to 4 bytes

  (define (pad-to-4 len)
    "Round up to next multiple of 4"
    (* 4 (quotient (+ len 4) 4)))

  (define (string->osc-bytes s)
    "Encode string as null-terminated, 4-byte padded bytevector"
    (let* ((len (string-length s))
           (padded-len (pad-to-4 (+ len 1)))
           (result (make-bytevector padded-len 0)))
      (do ((i 0 (+ i 1)))
          ((= i len))
        (bytevector-u8-set! result i (char->integer (string-ref s i))))
      result))

  (define (int32->bytes n)
    "Encode 32-bit int big-endian"
    (let ((bv (make-bytevector 4 0)))
      (bytevector-u8-set! bv 0 (bitwise-and (bitwise-arithmetic-shift-right n 24) #xff))
      (bytevector-u8-set! bv 1 (bitwise-and (bitwise-arithmetic-shift-right n 16) #xff))
      (bytevector-u8-set! bv 2 (bitwise-and (bitwise-arithmetic-shift-right n 8) #xff))
      (bytevector-u8-set! bv 3 (bitwise-and n #xff))
      bv))

  (define (float32->bytes f)
    "Encode 32-bit float (IEEE 754 big-endian)"
    (let ((bv (make-bytevector 4 0)))
      ;; Use R6RS bytevector-ieee-single-set! with big endian
      (bytevector-ieee-single-set! bv 0 (inexact f) (endianness big))
      bv))

  (define (bytes->int32 data offset)
    "Decode 32-bit int from big-endian bytes"
    (let ((b0 (bytevector-u8-ref data offset))
          (b1 (bytevector-u8-ref data (+ offset 1)))
          (b2 (bytevector-u8-ref data (+ offset 2)))
          (b3 (bytevector-u8-ref data (+ offset 3))))
      (bitwise-ior (bitwise-arithmetic-shift-left b0 24)
                   (bitwise-arithmetic-shift-left b1 16)
                   (bitwise-arithmetic-shift-left b2 8)
                   b3)))

  (define (bytes->float32 data offset)
    "Decode 32-bit float (IEEE 754 big-endian)"
    (bytevector-ieee-single-ref data offset (endianness big)))

  (define (bytes->osc-string data offset)
    "Decode null-terminated string, return (string . new-offset)"
    (let loop ((i offset) (chars '()))
      (if (or (>= i (bytevector-length data))
              (= (bytevector-u8-ref data i) 0))
          (let* ((s (list->string (reverse chars)))
                 (end (pad-to-4 (+ (- i offset) 1))))
            (cons s (+ offset end)))
          (loop (+ i 1) (cons (integer->char (bytevector-u8-ref data i)) chars)))))

  (define (bytevector-append . bvs)
    "Concatenate bytevectors"
    (let* ((total (apply + (map bytevector-length bvs)))
           (result (make-bytevector total 0)))
      (let loop ((bvs bvs) (offset 0))
        (if (null? bvs)
            result
            (let ((v (car bvs)))
              (bytevector-copy! v 0 result offset (bytevector-length v))
              (loop (cdr bvs) (+ offset (bytevector-length v))))))))

  (define (osc-encode address . args)
    "Encode OSC message: address + type tag + args.
     Returns bytevector."
    (let* ((addr-bytes (string->osc-bytes address))
           (type-tag (string-append ","
                       (apply string-append
                         (map (lambda (a)
                                (cond ((and (integer? a) (exact? a)) "i")
                                      ((real? a) "f")
                                      ((string? a) "s")
                                      (else "i")))
                              args))))
           (tag-bytes (string->osc-bytes type-tag))
           (arg-bytes (apply bytevector-append
                        (if (null? args)
                            (list (make-bytevector 0))
                            (map (lambda (a)
                                   (cond ((and (integer? a) (exact? a)) (int32->bytes a))
                                         ((real? a) (float32->bytes a))
                                         ((string? a) (string->osc-bytes a))
                                         (else (int32->bytes 0))))
                                 args)))))
      (bytevector-append addr-bytes tag-bytes arg-bytes)))

  ;; ============================================================
  ;; OSC Packet Decoding
  ;; ============================================================

  (define (osc-decode packet)
    "Decode OSC packet, return (address type-tag arg1 arg2 ...) or #f"
    (let ((data (if (bytevector? packet) packet
                    (error 'osc-decode "Expected bytevector" packet))))
      (let ((len (bytevector-length data)))
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
                                    (substring type-tag 1 (string-length type-tag))
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
                               (loop (+ i 1) offset args)))))))))))))

  ;; ============================================================
  ;; Connection State (UDP stubs)
  ;; ============================================================

  (define *osc-host* "127.0.0.1")
  (define *osc-port* 9000)  ; TouchOSC default
  (define *osc-connected* #f)
  (define *osc-running* #f)

  (define (osc-connect . rest)
    "Connect to OSC destination (Max, TouchOSC, etc.)
     Note: UDP transport requires udp-bridge.c (not yet ported to Chez)."
    (let ((host (get-opt rest 0 "127.0.0.1"))
          (port (get-opt rest 1 9000)))
      (set! *osc-host* host)
      (set! *osc-port* port)
      (set! *osc-connected* #t)
      (printf "OSC target set to ~a:~a (UDP transport pending udp-bridge.c)~%" host port)))

  (define (osc-send address . args)
    "Send OSC message via UDP.
     Currently encodes the packet but cannot transmit without udp-bridge.c."
    (let ((packet (apply osc-encode address args)))
      (unless *osc-connected*
        (printf "[osc] Warning: not connected, packet encoded but not sent~%"))
      ;; TODO: UDP sendto via udp-bridge.c
      ;; For now, return the encoded packet for testing
      packet))

  (define (osc-close)
    "Close OSC connection"
    (set! *osc-running* #f)
    (set! *osc-connected* #f)
    (print "OSC closed"))

  ;; ============================================================
  ;; Convenience Addresses for Cyberspace
  ;; ============================================================

  (define (/status)
    "Send vault status via OSC"
    (osc-send "/cyberspace/status" 1))

  (define (/soup . rest)
    "Send soup object count"
    (let ((count (get-opt rest 0 0)))
      (osc-send "/cyberspace/soup" count)))

  (define (/gossip msg)
    "Send gossip event"
    (osc-send "/cyberspace/gossip" msg))

  (define (/lamport tick)
    "Send Lamport clock tick"
    (osc-send "/cyberspace/lamport" tick))

  (define (/keys count)
    "Send key count"
    (osc-send "/cyberspace/keys" count))

  ;; ============================================================
  ;; Receiver (stub until UDP bridge)
  ;; ============================================================

  (define (osc-listen port handler)
    "Listen for incoming OSC on port, call handler for each message.
     Requires udp-bridge.c for actual UDP reception."
    (printf "OSC listen on port ~a (UDP transport pending udp-bridge.c)~%" port)
    (set! *osc-running* #t)
    ;; Return immediately; actual listening needs UDP bridge
    (void))

  (define (osc-server port)
    "Start OSC server (bidirectional)"
    (osc-listen port
      (lambda (msg)
        (let ((address (car msg)))
          (printf "OSC recv: ~a~%" address)
          (osc-send (string-append address "/ack") 1)))))

) ;; end library
