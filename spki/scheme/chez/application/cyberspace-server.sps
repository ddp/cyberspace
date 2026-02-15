#!/usr/bin/env chez --libdirs . --script
;;; Cyberspace Server - Chez Scheme
;;; HTTP status server (no WebSocket - see NO-WEBSOCKETS.md)
;;;
;;; Standalone:
;;;   chez --libdirs .. --script cyberspace-server.sps [port]
;;;
;;; Copyright (c) 2026 Yoyodyne. See LICENSE.

(import (rnrs)
        (only (chezscheme) command-line printf exit)
        (cyberspace server)
        (cyberspace crypto-ffi)
        (cyberspace fips))

(define (show-help)
  (printf "Cyberspace Server - HTTP status backend~%~%")
  (printf "Usage: cyberspace-server.sps [port]~%~%")
  (printf "Arguments:~%")
  (printf "  port    TCP port to listen on (default: 7780)~%~%")
  (printf "Examples:~%")
  (printf "  cyberspace-server.sps          # Listen on default port 7780~%")
  (printf "  cyberspace-server.sps 8080     # Listen on port 8080~%~%")
  (exit 0))

(sodium-init)
(fips-self-test)

(let* ((args (cdr (command-line)))
       (port (cond
               ;; No arguments - use default
               ((null? args) 7780)
               ;; Help requested
               ((member (car args) '("--help" "-h" "-?"))
                (show-help))
               ;; Port number specified
               ((string->number (car args))
                => (lambda (n)
                     (if (and (integer? n) (> n 0) (< n 65536))
                         n
                         (begin
                           (printf "Error: Port must be between 1 and 65535~%")
                           (exit 1)))))
               ;; Invalid argument
               (else
                 (printf "Error: Invalid port number '~a'~%" (car args))
                 (printf "Use --help for usage information~%")
                 (exit 1)))))
  (start-server port))
