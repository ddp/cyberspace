#!/usr/bin/env chez --script
;;; repl.sps - Cyberspace REPL bootstrap for native app
;;;
;;; Launched by native GUI app via PTY.
;;; Starts a simple Chez REPL for now.

(import (chezscheme))

;; Display welcome banner
(printf "~%Cyberspace Scheme (native PTY app)~%")
(printf "Chez Scheme Version ~a~%" (scheme-version))
(printf "~%Type (exit) to quit~%~%")

;; Start interactive REPL
(new-cafe)
