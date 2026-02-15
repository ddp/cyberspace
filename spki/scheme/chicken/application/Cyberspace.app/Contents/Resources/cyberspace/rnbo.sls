;;; rnbo.sls - Cycling '74 Max/RNBO Bridge for Cyberspace
;;;
;;; Streams vault events to Max/MSP via OSC for sonification.
;;; Works with RNBO exports and native Max patches.

(library (cyberspace rnbo)
  (export
    rnbo-connect rnbo-disconnect
    stream-gossip stream-lamport stream-object
    stream-key stream-sync stream-heartbeat
    stream-vault-state stream-introspection
    rnbo-mute rnbo-unmute rnbo-status)

  (import (rnrs)
          (only (chezscheme) printf format
                fork-thread sleep make-time
                time-second current-time)
          (cyberspace osc)
          (only (cyberspace vault) lamport-time))

  ;; ============================================================
  ;; State
  ;; ============================================================

  (define *rnbo-port* 7400)
  (define *rnbo-host* "127.0.0.1")
  (define *rnbo-muted* #f)
  (define *rnbo-connected* #f)
  (define *heartbeat-running* #f)

  (define *ns* "/cyberspace")

  (define (current-seconds) (time-second (current-time)))

  ;; ============================================================
  ;; Connection
  ;; ============================================================

  (define (rnbo-connect . rest)
    (let ((host (if (null? rest) "127.0.0.1" (car rest)))
          (port (if (or (null? rest) (null? (cdr rest))) 7400 (cadr rest))))
      (set! *rnbo-host* host)
      (set! *rnbo-port* port)
      (osc-connect host port)
      (set! *rnbo-connected* #t)
      (osc-send (string-append *ns* "/hello") 1)
      (printf "RNBO bridge connected to ~a:~a~n" host port)
      `(rnbo-connected (host ,host) (port ,port))))

  (define (rnbo-disconnect)
    (set! *heartbeat-running* #f)
    (osc-send (string-append *ns* "/goodbye") 1)
    (osc-close)
    (set! *rnbo-connected* #f)
    (display "RNBO bridge disconnected") (newline))

  (define (rnbo-mute)
    (set! *rnbo-muted* #t)
    (display "RNBO muted") (newline))

  (define (rnbo-unmute)
    (set! *rnbo-muted* #f)
    (display "RNBO unmuted") (newline))

  (define (rnbo-status)
    `(rnbo-status
      (connected ,*rnbo-connected*)
      (muted ,*rnbo-muted*)
      (host ,*rnbo-host*)
      (port ,*rnbo-port*)
      (heartbeat ,(if *heartbeat-running* 'running 'stopped))))

  ;; ============================================================
  ;; Event Streaming
  ;; ============================================================

  (define (send-if-active address . args)
    (when (and *rnbo-connected* (not *rnbo-muted*))
      (apply osc-send address args)))

  (define (stream-gossip event-type . rest)
    (let ((peer (if (null? rest) "" (car rest)))
          (data (if (or (null? rest) (null? (cdr rest))) 0 (cadr rest))))
      (let ((type-num (case event-type
                        ((announce) 1) ((sync) 2) ((ack) 3)
                        ((nack) 4) ((heartbeat) 5) (else 0))))
        (send-if-active (string-append *ns* "/gossip") type-num)
        (when (not (string=? peer ""))
          (send-if-active (string-append *ns* "/gossip/peer") peer))
        (when (not (zero? data))
          (send-if-active (string-append *ns* "/gossip/data") data)))))

  (define (stream-lamport . rest)
    (let* ((tick (if (null? rest) #f (car rest)))
           (t (or tick (lamport-time)))
           (normalized (/ (mod t 1000) 1000.0)))
      (send-if-active (string-append *ns* "/lamport") t)
      (send-if-active (string-append *ns* "/lamport/norm") normalized)))

  (define (stream-object op hash . rest)
    (let ((size (if (null? rest) 0 (car rest))))
      (let ((op-num (case op
                      ((put) 1) ((get) 2) ((delete) 3) ((verify) 4) (else 0))))
        (send-if-active (string-append *ns* "/object") op-num)
        (send-if-active (string-append *ns* "/object/hash")
                        (if (> (string-length hash) 8)
                            (substring hash 0 8)
                            hash))
        (when (> size 0)
          (send-if-active (string-append *ns* "/object/size") size)))))

  (define (stream-key op . rest)
    (let ((key-type (if (null? rest) 'ed25519 (car rest)))
          (bits (if (or (null? rest) (null? (cdr rest))) 256 (cadr rest))))
      (let ((op-num (case op
                      ((generate) 1) ((sign) 2) ((verify) 3)
                      ((derive) 4) ((load) 5) (else 0)))
            (type-num (case key-type
                        ((ed25519) 1) ((x25519) 2) ((dilithium) 3) (else 0))))
        (send-if-active (string-append *ns* "/key") op-num)
        (send-if-active (string-append *ns* "/key/type") type-num)
        (send-if-active (string-append *ns* "/key/bits") bits))))

  (define (stream-sync state . rest)
    (let ((peers (if (null? rest) 0 (car rest)))
          (behind (if (or (null? rest) (null? (cdr rest))) 0 (cadr rest))))
      (let ((state-num (case state
                         ((idle) 0) ((syncing) 1) ((complete) 2)
                         ((error) 3) (else 0))))
        (send-if-active (string-append *ns* "/sync/state") state-num)
        (send-if-active (string-append *ns* "/sync/peers") peers)
        (when (> behind 0)
          (send-if-active (string-append *ns* "/sync/behind") behind)))))

  (define (stream-heartbeat)
    (send-if-active (string-append *ns* "/heartbeat") (current-seconds)))

  ;; ============================================================
  ;; Batch Operations
  ;; ============================================================

  (define (stream-vault-state obj-count key-count audit-count)
    (send-if-active (string-append *ns* "/vault/objects") obj-count)
    (send-if-active (string-append *ns* "/vault/keys") key-count)
    (send-if-active (string-append *ns* "/vault/audits") audit-count)
    (send-if-active (string-append *ns* "/vault/total")
                    (+ obj-count key-count audit-count)))

  (define (stream-introspection hw)
    (when (and hw (pair? hw))
      (let ((cores (or (and (assq 'cores (cdr hw)) (cadr (assq 'cores (cdr hw)))) 0))
            (mem-gb (or (and (assq 'memory-gb (cdr hw)) (cadr (assq 'memory-gb (cdr hw)))) 0))
            (weave (or (and (assq 'weave (cdr hw)) (cadr (assq 'weave (cdr hw)))) 0))
            (mobile (or (and (assq 'mobile (cdr hw)) (cadr (assq 'mobile (cdr hw)))) #f)))
        (send-if-active (string-append *ns* "/hw/cores") cores)
        (send-if-active (string-append *ns* "/hw/memory") mem-gb)
        (send-if-active (string-append *ns* "/hw/weave") weave)
        (send-if-active (string-append *ns* "/hw/mobile") (if mobile 1 0)))))

) ;; end library
