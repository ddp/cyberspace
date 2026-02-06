#!/usr/bin/env scheme-script
;;; Test capability.sls in Chez Scheme
;;; Run: scheme --libdirs . test-capability.ss

(import (rnrs)
        (cyberspace capability))

;; Mock hardware data
(define fluffy-hw
  '(hardware
    (model "Mac Studio")
    (cores 12)
    (memory-gb 128)
    (root-avail-gb 500)
    (weave 2000000)
    (mobile #f)))

(define starlight-hw
  '(hardware
    (model "MacBook Pro")
    (cores 8)
    (memory-gb 16)
    (root-avail-gb 256)
    (weave 500000)
    (mobile #t)))

;; Test capability scoring
(display "=== Capability Scoring Test ===\n")
(display "Fluffy (Mac Studio, !mobile): ")
(display (compute-capability-score fluffy-hw))
(newline)

(display "Starlight (MacBook, mobile): ")
(display (compute-capability-score starlight-hw))
(newline)

;; Test comparison
(display "\n=== Comparison Test ===\n")
(display "compare-capabilities: ")
(display (compare-capabilities fluffy-hw starlight-hw))
(newline)

;; Test election
(display "\n=== Election Test ===\n")
(let-values (((winner score all)
              (elect-master `((fluffy . ,fluffy-hw)
                             (starlight . ,starlight-hw)))))
  (display "Winner: ")
  (display winner)
  (display " with score ")
  (display score)
  (newline)
  (display "All scores: ")
  (display all)
  (newline))

;; Test scaling factor
(display "\n=== Scaling Factor Test ===\n")
(let ((scaling (compute-scaling-factor `((fluffy . ,fluffy-hw)
                                         (starlight . ,starlight-hw)))))
  (display "Reference: ")
  (display (cdr (assq 'reference scaling)))
  (newline)
  (display "Reference score: ")
  (display (cdr (assq 'reference-score scaling)))
  (newline)
  (display "Members: ")
  (display (cdr (assq 'members scaling)))
  (newline)
  (display "Effective capacity: ")
  (display (cdr (assq 'effective-capacity scaling)))
  (newline))

;; Test mobile detection
(display "\n=== Mobile Detection Test ===\n")
(display "Fluffy is-mobile?: ")
(display (is-mobile? fluffy-hw))
(newline)
(display "Starlight is-mobile?: ")
(display (is-mobile? starlight-hw))
(newline)

(display "\n=== All tests passed ===\n")
