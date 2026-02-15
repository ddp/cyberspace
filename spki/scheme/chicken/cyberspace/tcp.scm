;;; TCP Socket Abstraction - Chicken Scheme
;;;
;;; Wraps Chicken's built-in (chicken tcp) to provide the same API
;;; as the Chez tcp.sls module (which uses libtcp-bridge).
;;;
;;; Chicken gives us TCP for free; Chez needs an explicit C bridge.

(module tcp
  (tcp-connect
   tcp-listen
   tcp-accept
   tcp-accept-binary
   tcp-close
   tcp-available?)

  (import scheme
          (chicken base)
          (chicken tcp))

  (define (tcp-available?) #t)

  ;; tcp-connect: Chicken's tcp-connect already returns (values in out)
  ;; Re-export directly.

  ;; tcp-accept-binary: accept without transcoding
  (define (tcp-accept-binary listener)
    (tcp-accept listener))

  ;; tcp-close: Chicken's tcp-close works directly
  ;; tcp-listen: Chicken's tcp-listen works directly

) ;; end module
