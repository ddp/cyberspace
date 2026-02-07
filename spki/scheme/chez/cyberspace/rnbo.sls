;;; rnbo.sls - Cycling '74 Max/RNBO Bridge for Cyberspace (Chez Port)
;;; Library of Cyberspace
;;;
;;; Streams vault events to Max/MSP via OSC for sonification.
;;; Works with RNBO exports and native Max patches.
;;;
;;; Event types:
;;; - Gossip protocol messages
;;; - Lamport clock ticks
;;; - Object store changes
;;; - Key operations
;;; - Sync state changes
;;;
;;; Ported from rnbo.scm.
;;; Copyright (c) 2026 Yoyodyne. See LICENSE.

(library (cyberspace rnbo)
  (export
    ;; Connection
    rnbo-connect
    rnbo-disconnect
    ;; Event streaming
    stream-gossip
    stream-lamport
    stream-object
    stream-key
    stream-sync
    stream-heartbeat
    ;; Batch operations
    stream-vault-state
    stream-introspection
    ;; Control
    rnbo-mute
    rnbo-unmute
    rnbo-status)

  (import (rnrs)
          (only (chezscheme)
                printf format void flush-output-port)
          (cyberspace chicken-compatibility chicken)
          (cyberspace chicken-compatibility thread)
          (cyberspace osc)
          (only (cyberspace vault) lamport-time lamport-tick!))

  ;; RNBO/Max default port (Max udpreceive default)
  (define *rnbo-port* 7400)
  (define *rnbo-host* "127.0.0.1")
  (define *rnbo-muted* #f)
  (define *rnbo-connected* #f)
  (define *heartbeat-thread* #f)
  (define *heartbeat-running* #f)

  ;; OSC address namespace for Cyberspace
  (define *ns* "/cyberspace")

  (define (rnbo-connect . rest)
    "Connect to Max/RNBO via OSC.
     Default port 7400 matches Max udpreceive default."
    (let ((host (get-opt rest 0 "127.0.0.1"))
          (port (get-opt rest 1 7400)))
      (set! *rnbo-host* host)
      (set! *rnbo-port* port)
      (osc-connect host port)
      (set! *rnbo-connected* #t)
      ;; Send hello
      (osc-send (string-append *ns* "/hello") 1)
      (printf "RNBO bridge connected to ~a:~a~%" host port)
      `(rnbo-connected (host ,host) (port ,port))))

  (define (rnbo-disconnect)
    "Disconnect from Max/RNBO"
    (when *heartbeat-running*
      (set! *heartbeat-running* #f))
    (osc-send (string-append *ns* "/goodbye") 1)
    (osc-close)
    (set! *rnbo-connected* #f)
    (print "RNBO bridge disconnected"))

  (define (rnbo-mute)
    "Mute event streaming (connection stays open)"
    (set! *rnbo-muted* #t)
    (print "RNBO muted"))

  (define (rnbo-unmute)
    "Resume event streaming"
    (set! *rnbo-muted* #f)
    (print "RNBO unmuted"))

  (define (rnbo-status)
    "Get bridge status"
    `(rnbo-status
      (connected ,*rnbo-connected*)
      (muted ,*rnbo-muted*)
      (host ,*rnbo-host*)
      (port ,*rnbo-port*)
      (heartbeat ,(if *heartbeat-running* 'running 'stopped))))

  ;; ============================================================
  ;; Event Streaming - Individual Events
  ;; ============================================================

  (define (send-if-active address . args)
    "Send OSC message if connected and not muted"
    (when (and *rnbo-connected* (not *rnbo-muted*))
      (apply osc-send address args)))

  (define (stream-gossip event-type . rest)
    "Stream gossip protocol event.
     event-type: 'announce | 'sync | 'ack | 'nack | 'heartbeat
     Optional: peer (string), data (number)"
    (let ((peer (get-opt rest 0 ""))
          (data (get-opt rest 1 0)))
      (let ((type-num (case event-type
                        ((announce) 1)
                        ((sync) 2)
                        ((ack) 3)
                        ((nack) 4)
                        ((heartbeat) 5)
                        (else 0))))
        (send-if-active (string-append *ns* "/gossip") type-num)
        (when (not (string=? peer ""))
          (send-if-active (string-append *ns* "/gossip/peer") peer))
        (when (not (zero? data))
          (send-if-active (string-append *ns* "/gossip/data") data)))))

  (define (stream-lamport . rest)
    "Stream Lamport clock tick.
     If tick is #f or omitted, uses current lamport-time.
     Also sends tick as normalized float (0.0-1.0) for audio."
    (let* ((tick (get-opt rest 0 #f))
           (t (or tick (lamport-time)))
           (normalized (/ (modulo t 1000) 1000.0)))  ; wrap every 1000
      (send-if-active (string-append *ns* "/lamport") t)
      (send-if-active (string-append *ns* "/lamport/norm") (inexact normalized))))

  (define (stream-object op hash . rest)
    "Stream object store operation.
     op: 'put | 'get | 'delete | 'verify
     hash: first 8 chars of content hash
     Optional: size (integer)"
    (let ((size (get-opt rest 0 0)))
      (let ((op-num (case op
                      ((put) 1)
                      ((get) 2)
                      ((delete) 3)
                      ((verify) 4)
                      (else 0))))
        (send-if-active (string-append *ns* "/object") op-num)
        (send-if-active (string-append *ns* "/object/hash")
                        (if (> (string-length hash) 8)
                            (substring hash 0 8)
                            hash))
        (when (> size 0)
          (send-if-active (string-append *ns* "/object/size") size)))))

  (define (stream-key op . rest)
    "Stream key operation.
     op: 'generate | 'sign | 'verify | 'derive | 'load
     Optional: key-type (symbol), bits (integer)"
    (let ((key-type (get-opt rest 0 'ed25519))
          (bits (get-opt rest 1 256)))
      (let ((op-num (case op
                      ((generate) 1)
                      ((sign) 2)
                      ((verify) 3)
                      ((derive) 4)
                      ((load) 5)
                      (else 0)))
            (type-num (case key-type
                        ((ed25519) 1)
                        ((x25519) 2)
                        ((dilithium) 3)
                        (else 0))))
        (send-if-active (string-append *ns* "/key") op-num)
        (send-if-active (string-append *ns* "/key/type") type-num)
        (send-if-active (string-append *ns* "/key/bits") bits))))

  (define (stream-sync state . rest)
    "Stream sync state change.
     state: 'idle | 'syncing | 'complete | 'error
     Optional: peers (integer), behind (integer)"
    (let ((peers (get-opt rest 0 0))
          (behind (get-opt rest 1 0)))
      (let ((state-num (case state
                         ((idle) 0)
                         ((syncing) 1)
                         ((complete) 2)
                         ((error) 3)
                         (else 0))))
        (send-if-active (string-append *ns* "/sync/state") state-num)
        (send-if-active (string-append *ns* "/sync/peers") peers)
        (when (> behind 0)
          (send-if-active (string-append *ns* "/sync/behind") behind)))))

  (define (stream-heartbeat)
    "Send single heartbeat pulse.
     Useful for keeping Max/RNBO patch in sync."
    (let ((now (current-seconds)))
      (send-if-active (string-append *ns* "/heartbeat") now)))

  ;; ============================================================
  ;; Batch Operations
  ;; ============================================================

  (define (stream-vault-state obj-count key-count audit-count)
    "Stream complete vault state snapshot.
     Sends multiple OSC messages for Max visualization."
    (send-if-active (string-append *ns* "/vault/objects") obj-count)
    (send-if-active (string-append *ns* "/vault/keys") key-count)
    (send-if-active (string-append *ns* "/vault/audits") audit-count)
    (send-if-active (string-append *ns* "/vault/total")
                    (+ obj-count key-count audit-count)))

  (define (stream-introspection hw)
    "Stream hardware introspection data for sonification.
     hw: result of (introspect-hardware) from enroll module"
    (when (and hw (pair? hw))
      (let ((cores (or (and (assq 'cores (cdr hw))
                            (cadr (assq 'cores (cdr hw))))
                       0))
            (mem-gb (or (and (assq 'memory-gb (cdr hw))
                             (cadr (assq 'memory-gb (cdr hw))))
                        0))
            (weave (or (and (assq 'weave (cdr hw))
                            (cadr (assq 'weave (cdr hw))))
                       0))
            (mobile (or (and (assq 'mobile (cdr hw))
                             (cadr (assq 'mobile (cdr hw))))
                        #f)))
        (send-if-active (string-append *ns* "/hw/cores") cores)
        (send-if-active (string-append *ns* "/hw/memory") mem-gb)
        (send-if-active (string-append *ns* "/hw/weave") weave)
        (send-if-active (string-append *ns* "/hw/mobile") (if mobile 1 0)))))

  ;; ============================================================
  ;; Continuous Heartbeat (for Max metro sync)
  ;; ============================================================

  (define (start-heartbeat . rest)
    "Start continuous heartbeat at given interval.
     Default 100ms = 10 Hz, good for Max metro sync."
    (let ((interval-ms (get-opt rest 0 100)))
      (when *heartbeat-running*
        (stop-heartbeat))
      (set! *heartbeat-running* #t)
      (set! *heartbeat-thread*
            (thread-start!
             (make-thread
              (lambda ()
                (let loop ()
                  (when *heartbeat-running*
                    (stream-heartbeat)
                    (thread-sleep! (/ interval-ms 1000.0))
                    (loop))))
              'rnbo-heartbeat)))
      (printf "Heartbeat started at ~ams~%" interval-ms)))

  (define (stop-heartbeat)
    "Stop continuous heartbeat"
    (set! *heartbeat-running* #f)
    (print "Heartbeat stopped"))

) ;; end library
