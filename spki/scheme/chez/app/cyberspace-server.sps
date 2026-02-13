#!/usr/bin/env chez --libdirs . --script
;;; Cyberspace Server - Chez Scheme
;;; Backend HTTP/WebSocket server for Cyberspace.app
;;;
;;; Launched by the native macOS app (main.m) or standalone:
;;;   chez --libdirs .. --script cyberspace-server.sps [port]
;;;
;;; Copyright (c) 2026 Yoyodyne. See LICENSE.

(import (rnrs)
        (only (chezscheme) command-line printf)
        (cyberspace server)
        (cyberspace crypto-ffi)
        (cyberspace fips))

(sodium-init)
(fips-self-test)

(let* ((args (cdr (command-line)))
       (port (if (pair? args) (string->number (car args)) 7780)))
  (start-server port))
