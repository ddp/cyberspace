;;; mpe.scm - MIDI Polyphonic Expression for Cyberspace
;;;
;;; MPE: each note gets its own channel (2-16) for:
;;;   - Per-note pitch bend (±48 semitones typical)
;;;   - Per-note pressure (channel aftertouch)
;;;   - Per-note slide (CC74)
;;;
;;; For Roli Seaboard, Linnstrument, Sensel Morph, etc.
;;;
;;; Copyright (c) 2026 Yoyodyne. See LICENSE.

(module mpe
  (mpe-init mpe-note-on mpe-note-off
   mpe-bend mpe-pressure mpe-slide
   mpe-zone mpe-master
   *mpe-lower-zone* *mpe-upper-zone*)

(import scheme)
(import (chicken base))
(import (chicken format))
(import (chicken bitwise))
(import srfi-1)
(import srfi-4)

;; MPE Zone configuration
;; Lower zone: channels 2-8 (master on 1)
;; Upper zone: channels 9-15 (master on 16)
(define *mpe-lower-zone* #t)
(define *mpe-upper-zone* #f)
(define *mpe-bend-range* 48)  ; semitones, MPE default

;; Channel allocation
(define *channel-pool* '(2 3 4 5 6 7 8 9 10 11 12 13 14 15 16))
(define *active-notes* '())  ; ((note . channel) ...)

(define (allocate-channel!)
  "Get next available MPE channel"
  (if (null? *channel-pool*)
      #f
      (let ((ch (car *channel-pool*)))
        (set! *channel-pool* (cdr *channel-pool*))
        ch)))

(define (release-channel! ch)
  "Return channel to pool"
  (set! *channel-pool* (cons ch *channel-pool*)))

;; MIDI message encoding
(define (midi-note-on channel note velocity)
  "Encode note-on: 0x9n nn vv"
  (u8vector (+ #x90 (- channel 1)) note velocity))

(define (midi-note-off channel note)
  "Encode note-off: 0x8n nn 00"
  (u8vector (+ #x80 (- channel 1)) note 0))

(define (midi-pitch-bend channel value)
  "Encode pitch bend: 0xEn ll mm (14-bit, center=8192)"
  (let ((v (+ 8192 (inexact->exact (round (* value 8191))))))
    (u8vector (+ #xE0 (- channel 1))
              (bitwise-and v #x7f)
              (bitwise-and (arithmetic-shift v -7) #x7f))))

(define (midi-aftertouch channel pressure)
  "Encode channel aftertouch: 0xDn pp"
  (u8vector (+ #xD0 (- channel 1))
            (inexact->exact (round (* pressure 127)))))

(define (midi-cc channel cc value)
  "Encode control change: 0xBn cc vv"
  (u8vector (+ #xB0 (- channel 1)) cc
            (inexact->exact (round (* value 127)))))

;; MPE API
(define (mpe-init #!key (bend-range 48) (lower #t) (upper #f))
  "Initialize MPE mode"
  (set! *mpe-bend-range* bend-range)
  (set! *mpe-lower-zone* lower)
  (set! *mpe-upper-zone* upper)
  (printf "MPE initialized: bend=±~a, lower=~a, upper=~a~%"
          bend-range lower upper))

(define (mpe-note-on note velocity)
  "Start MPE note with allocated channel"
  (let ((ch (allocate-channel!)))
    (if ch
        (begin
          (set! *active-notes* (cons (cons note ch) *active-notes*))
          (printf "MPE note-on: ~a vel=~a ch=~a~%" note velocity ch)
          (midi-note-on ch note velocity))
        (begin
          (print "MPE: no channels available")
          #f))))

(define (mpe-note-off note)
  "End MPE note, release channel"
  (let ((entry (assoc note *active-notes*)))
    (if entry
        (let ((ch (cdr entry)))
          (set! *active-notes* (remove (lambda (e) (= (car e) note)) *active-notes*))
          (release-channel! ch)
          (printf "MPE note-off: ~a ch=~a~%" note ch)
          (midi-note-off ch note))
        #f)))

(define (mpe-bend note amount)
  "Per-note pitch bend (-1.0 to +1.0)"
  (let ((entry (assoc note *active-notes*)))
    (if entry
        (midi-pitch-bend (cdr entry) amount)
        #f)))

(define (mpe-pressure note amount)
  "Per-note pressure (0.0 to 1.0)"
  (let ((entry (assoc note *active-notes*)))
    (if entry
        (midi-aftertouch (cdr entry) amount)
        #f)))

(define (mpe-slide note amount)
  "Per-note slide/CC74 (0.0 to 1.0)"
  (let ((entry (assoc note *active-notes*)))
    (if entry
        (midi-cc (cdr entry) 74 amount)
        #f)))

(define (mpe-zone)
  "Report current zone configuration"
  (printf "MPE zones: lower=~a upper=~a bend=±~a~%"
          *mpe-lower-zone* *mpe-upper-zone* *mpe-bend-range*))

(define (mpe-master cc value)
  "Send on master channel (1 for lower zone)"
  (midi-cc 1 cc value))

) ; end module
