;;; mpe.sls - MIDI Polyphonic Expression for Cyberspace
;;;
;;; MPE: each note gets its own channel (2-16) for:
;;;   - Per-note pitch bend (±48 semitones typical)
;;;   - Per-note pressure (channel aftertouch)
;;;   - Per-note slide (CC74)
;;;
;;; For Roli Seaboard, Linnstrument, Sensel Morph, etc.

(library (cyberspace mpe)
  (export mpe-init mpe-note-on mpe-note-off
          mpe-bend mpe-pressure mpe-slide
          mpe-zone mpe-master
          mpe-lower-zone mpe-upper-zone)

  (import (rnrs)
          (only (chezscheme) printf format)
          (cyberspace chicken-compatibility blob)
          (cyberspace chicken-compatibility chicken))

  ;; Chicken's (u8vector a b c) variadic constructor
  (define (u8vector . args)
    (let* ((len (length args))
           (bv (make-bytevector len)))
      (let loop ((i 0) (rest args))
        (if (null? rest)
            bv
            (begin
              (bytevector-u8-set! bv i (car rest))
              (loop (+ i 1) (cdr rest)))))))

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
    (if (null? *channel-pool*)
        #f
        (let ((ch (car *channel-pool*)))
          (set! *channel-pool* (cdr *channel-pool*))
          ch)))

  (define (release-channel! ch)
    (set! *channel-pool* (cons ch *channel-pool*)))

  ;; MIDI message encoding
  (define (midi-note-on channel note velocity)
    (u8vector (+ #x90 (- channel 1)) note velocity))

  (define (midi-note-off channel note)
    (u8vector (+ #x80 (- channel 1)) note 0))

  (define (midi-pitch-bend channel value)
    (let ((v (+ 8192 (exact (round (* value 8191))))))
      (u8vector (+ #xE0 (- channel 1))
                (bitwise-and v #x7f)
                (bitwise-and (bitwise-arithmetic-shift-right v 7) #x7f))))

  (define (midi-aftertouch channel pressure)
    (u8vector (+ #xD0 (- channel 1))
              (exact (round (* pressure 127)))))

  (define (midi-cc channel cc value)
    (u8vector (+ #xB0 (- channel 1)) cc
              (exact (round (* value 127)))))

  ;; MPE API
  (define (mpe-init . opts)
    (let ((bend-range (get-key opts 'bend-range 48))
          (lower (get-key opts 'lower #t))
          (upper (get-key opts 'upper #f)))
      (set! *mpe-bend-range* bend-range)
      (set! *mpe-lower-zone* lower)
      (set! *mpe-upper-zone* upper)
      (printf "MPE initialized: bend=±~a, lower=~a, upper=~a~%" bend-range lower upper)))

  (define (mpe-note-on note velocity)
    (let ((ch (allocate-channel!)))
      (if ch
          (begin
            (set! *active-notes* (cons (cons note ch) *active-notes*))
            (printf "MPE note-on: ~a vel=~a ch=~a~%" note velocity ch)
            (midi-note-on ch note velocity))
          (begin
            (printf "MPE: no channels available~%")
            #f))))

  (define (mpe-note-off note)
    (let ((entry (assoc note *active-notes*)))
      (if entry
          (let ((ch (cdr entry)))
            (set! *active-notes* (remp (lambda (e) (= (car e) note)) *active-notes*))
            (release-channel! ch)
            (printf "MPE note-off: ~a ch=~a~%" note ch)
            (midi-note-off ch note))
          #f)))

  (define (mpe-bend note amount)
    (let ((entry (assoc note *active-notes*)))
      (if entry
          (midi-pitch-bend (cdr entry) amount)
          #f)))

  (define (mpe-pressure note amount)
    (let ((entry (assoc note *active-notes*)))
      (if entry
          (midi-aftertouch (cdr entry) amount)
          #f)))

  (define (mpe-slide note amount)
    (let ((entry (assoc note *active-notes*)))
      (if entry
          (midi-cc (cdr entry) 74 amount)
          #f)))

  ;; Accessors for mutable zone state (R6RS can't export assigned variables)
  (define (mpe-lower-zone) *mpe-lower-zone*)
  (define (mpe-upper-zone) *mpe-upper-zone*)

  (define (mpe-zone)
    (printf "MPE zones: lower=~a upper=~a bend=±~a~%"
            *mpe-lower-zone* *mpe-upper-zone* *mpe-bend-range*))

  (define (mpe-master cc value)
    (midi-cc 1 cc value))

) ; end library
