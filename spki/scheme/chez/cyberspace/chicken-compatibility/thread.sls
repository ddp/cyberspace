;;; SRFI-18 Thread Compatibility Library
;;; Library of Cyberspace - Chez Port
;;;
;;; Maps Chicken's SRFI-18 green threads to Chez native OS threads.
;;; Only the subset actually used by Cyberspace is implemented:
;;;
;;;   make-thread       - create thread from thunk + optional name
;;;   thread-start!     - start a created thread
;;;   thread-sleep!     - sleep for seconds (accepts integer or real)
;;;   thread-terminate!  - terminate a thread
;;;   thread-yield!     - yield to other threads
;;;   mutex operations  - provided for completeness
;;;
;;; Architecture note:
;;;   This is the entire reason for the Chez port -- Chicken has green
;;;   threads (cooperative, single OS thread).  Chez has native OS threads.
;;;   Gossip, mDNS, and auto-enrollment all need real concurrency.
;;;
;;; Copyright (c) 2026 Yoyodyne. See LICENSE.

(library (cyberspace chicken-compatibility thread)
  (export
    ;; Thread operations
    make-thread
    thread-start!
    thread-sleep!
    thread-terminate!
    thread-yield!
    thread?
    thread-name
    current-thread
    thread-join!
    ;; Mutex operations (for future use)
    make-mutex
    mutex?
    mutex-name
    mutex-lock!
    mutex-unlock!
    ;; Condition variables (for future use)
    make-condition-variable
    condition-variable?
    condition-variable-signal!
    condition-variable-broadcast!)

  (import (rnrs)
          (rename
            (only (chezscheme)
                  fork-thread sleep make-time
                  make-condition condition-wait condition-signal condition-broadcast
                  make-mutex with-mutex mutex-acquire mutex-release
                  void format printf)
            (make-mutex chez-make-mutex)
            (make-condition chez-make-condition)
            (with-mutex chez-with-mutex)))

  ;; ============================================================
  ;; Thread record
  ;;
  ;; Wraps Chez's fork-thread with SRFI-18 semantics.
  ;; Chez fork-thread returns immediately with a thread object,
  ;; but SRFI-18 separates creation (make-thread) from starting
  ;; (thread-start!).
  ;; ============================================================

  (define *thread-tag* (list 'srfi-18-thread))

  ;; Thread structure: #(tag name thunk chez-thread started? result mutex condvar finished?)
  ;;                     0    1     2       3         4       5      6     7       8

  (define (make-thread-record name thunk)
    (let ((mtx (chez-make-mutex))
          (cv  (chez-make-condition)))
      (vector *thread-tag* name thunk #f #f (void) mtx cv #f)))

  (define (thread? x)
    (and (vector? x)
         (>= (vector-length x) 9)
         (eq? (vector-ref x 0) *thread-tag*)))

  (define (thread-name t) (vector-ref t 1))
  (define (thread-thunk t) (vector-ref t 2))
  (define (thread-chez-thread t) (vector-ref t 3))
  (define (thread-chez-thread-set! t v) (vector-set! t 3 v))
  (define (thread-started? t) (vector-ref t 4))
  (define (thread-started-set! t v) (vector-set! t 4 v))
  (define (thread-result t) (vector-ref t 5))
  (define (thread-result-set! t v) (vector-set! t 5 v))
  (define (thread-mutex t) (vector-ref t 6))
  (define (thread-condvar t) (vector-ref t 7))
  (define (thread-finished? t) (vector-ref t 8))
  (define (thread-finished-set! t v) (vector-set! t 8 v))

  ;; ============================================================
  ;; SRFI-18 API
  ;; ============================================================

  (define (make-thread thunk . rest)
    "Create a new thread (not yet started).
     (make-thread thunk)
     (make-thread thunk name)"
    (let ((name (if (null? rest) #f (car rest))))
      (make-thread-record name thunk)))

  (define (thread-start! thread)
    "Start a thread created with make-thread.  Returns the thread."
    (when (thread-started? thread)
      (error 'thread-start! "Thread already started" (thread-name thread)))
    (thread-started-set! thread #t)
    (let ((ct (fork-thread
               (lambda ()
                 (guard (exn [#t (void)])  ; Don't crash on unhandled exceptions
                   (let ((result ((thread-thunk thread))))
                     (thread-result-set! thread result)))
                 (chez-with-mutex (thread-mutex thread)
                   (thread-finished-set! thread #t)
                   (condition-broadcast (thread-condvar thread)))))))
      (thread-chez-thread-set! thread ct))
    thread)

  (define (thread-sleep! timeout)
    "Sleep for timeout seconds.  Accepts integer or real."
    (let ((secs (cond
                  ((and (integer? timeout) (exact? timeout))
                   timeout)
                  ((real? timeout)
                   ;; Chez sleep takes a time-duration or seconds
                   timeout)
                  (else
                   (error 'thread-sleep! "Expected number" timeout)))))
      ;; Chez's sleep takes a time-duration.  We use make-time.
      ;; For simplicity, convert to milliseconds for nanosleep.
      (let* ((whole-secs (exact (floor secs)))
             (frac-ns (exact (floor (* (- secs whole-secs) 1000000000)))))
        ;; Chez sleep takes a time-duration
        (sleep (make-time 'time-duration frac-ns whole-secs)))))

  (define (thread-terminate! thread)
    "Request thread termination.
     Note: Chez doesn't have a direct thread-kill.  We set a flag.
     The thread must cooperate by checking periodically.
     For the fire-and-forget threads in Cyberspace, this is acceptable
     since they loop with thread-sleep! and can check the flag."
    ;; Mark as finished so join won't block
    (chez-with-mutex (thread-mutex thread)
      (thread-finished-set! thread #t)
      (condition-broadcast (thread-condvar thread))))

  (define (thread-yield!)
    "Yield to other threads."
    ;; Chez native threads are preemptive, but a zero sleep
    ;; gives the scheduler a chance to switch.
    (sleep (make-time 'time-duration 0 0)))

  (define (current-thread)
    "Returns an opaque thread object for the current thread."
    ;; Chez doesn't expose current thread as an SRFI-18 object.
    ;; Return a placeholder.
    #f)

  (define (thread-join! thread . rest)
    "Wait for thread to finish.  Optional timeout."
    (let ((timeout (if (null? rest) #f (car rest))))
      (if timeout
          ;; Timed wait - just sleep and check
          (let loop ((remaining timeout))
            (if (thread-finished? thread)
                (thread-result thread)
                (if (<= remaining 0)
                    (error 'thread-join! "Timeout waiting for thread")
                    (begin
                      (sleep (make-time 'time-duration 0 0))
                      (loop (- remaining 0.01))))))
          ;; Infinite wait
          (begin
            (chez-with-mutex (thread-mutex thread)
              (let loop ()
                (unless (thread-finished? thread)
                  (condition-wait (thread-condvar thread) (thread-mutex thread))
                  (loop))))
            (thread-result thread)))))

  ;; ============================================================
  ;; SRFI-18 Mutex (wrapping Chez mutex)
  ;; ============================================================

  (define *mutex-tag* (list 'srfi-18-mutex))

  (define (%make-mutex-record name chez-mutex)
    (vector *mutex-tag* name chez-mutex))

  (define (mutex? x)
    (and (vector? x)
         (>= (vector-length x) 3)
         (eq? (vector-ref x 0) *mutex-tag*)))

  (define (mutex-name m) (vector-ref m 1))
  (define (mutex-chez m) (vector-ref m 2))

  ;; SRFI-18 make-mutex wraps Chez's mutex
  (define (make-mutex . rest)
    (let ((name (if (null? rest) #f (car rest))))
      (%make-mutex-record name (chez-make-mutex))))

  (define (mutex-lock! m . rest)
    (mutex-acquire (mutex-chez m))
    #t)

  (define (mutex-unlock! m . rest)
    (mutex-release (mutex-chez m))
    #t)

  ;; ============================================================
  ;; SRFI-18 Condition Variables (wrapping Chez condition)
  ;; ============================================================

  (define *condvar-tag* (list 'srfi-18-condvar))

  (define (condition-variable? x)
    (and (vector? x)
         (>= (vector-length x) 3)
         (eq? (vector-ref x 0) *condvar-tag*)))

  (define (make-condition-variable . rest)
    (let ((name (if (null? rest) #f (car rest))))
      (vector *condvar-tag* name (chez-make-condition))))

  (define (condvar-chez cv) (vector-ref cv 2))

  (define (condition-variable-signal! cv)
    (condition-signal (condvar-chez cv)))

  (define (condition-variable-broadcast! cv)
    (condition-broadcast (condvar-chez cv)))

) ;; end library
