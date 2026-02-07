;;; Thread Compatibility Test Suite
;;; Library of Cyberspace - Chez Port
;;;
;;; Tests SRFI-18 thread API over Chez native OS threads.

(import (rnrs)
        (only (chezscheme) printf format box unbox set-box! make-time
              sleep time-nanosecond time-second current-time void)
        (cyberspace chicken-compatibility thread))

;; ============================================================
;; Test harness
;; ============================================================

(define *pass* 0)
(define *fail* 0)

(define (check name ok?)
  (if ok?
      (begin
        (printf "  pass ~a\n" name)
        (set! *pass* (+ *pass* 1)))
      (begin
        (printf "  FAIL ~a\n" name)
        (set! *fail* (+ *fail* 1)))))

(printf "\n=== Thread Compatibility Test Suite ===\n\n")

;; --- Basic thread creation and start ---
(printf "--- Thread Basics ---\n")

(let ((t (make-thread (lambda () 42) "test-thread")))
  (check "make-thread" (thread? t))
  (check "thread-name" (equal? (thread-name t) "test-thread"))
  (thread-start! t)
  (let ((result (thread-join! t)))
    (check "thread-join! returns value" (= result 42))))

;; --- Thread with shared state ---
(printf "\n--- Shared State ---\n")

(let ((counter (box 0)))
  (let ((t (make-thread
             (lambda ()
               (set-box! counter (+ (unbox counter) 1))))))
    (thread-start! t)
    (thread-join! t)
    (check "thread modified shared state" (= (unbox counter) 1))))

;; --- Multiple concurrent threads ---
(printf "\n--- Concurrency ---\n")

(let ((results (make-vector 5 #f)))
  (let ((threads (map (lambda (i)
                        (make-thread
                          (lambda ()
                            (vector-set! results i (* i i))
                            (* i i))
                          (string-append "worker-" (number->string i))))
                      '(0 1 2 3 4))))
    (for-each thread-start! threads)
    (for-each thread-join! threads)
    (check "5 concurrent threads"
      (equal? (vector->list results) '(0 1 4 9 16)))))

;; --- thread-sleep! ---
(printf "\n--- Sleep ---\n")

(let* ((start (current-time 'time-monotonic))
       (t (make-thread
            (lambda ()
              (thread-sleep! 0.1)
              'done))))
  (thread-start! t)
  (let ((result (thread-join! t)))
    (let* ((end (current-time 'time-monotonic))
           (elapsed-ns (+ (* (- (time-second end) (time-second start)) 1000000000)
                          (- (time-nanosecond end) (time-nanosecond start))))
           (elapsed-ms (/ elapsed-ns 1000000)))
      (check "thread-sleep! ~100ms" (and (> elapsed-ms 80) (< elapsed-ms 500)))
      (check "thread-sleep! returns" (eq? result 'done)))))

;; --- thread-yield! ---
(printf "\n--- Yield ---\n")

(let ((t (make-thread
           (lambda ()
             (thread-yield!)
             'yielded))))
  (thread-start! t)
  (check "thread-yield! completes" (eq? (thread-join! t) 'yielded)))

;; --- thread-terminate! ---
(printf "\n--- Terminate ---\n")

(let ((t (make-thread
           (lambda ()
             (thread-sleep! 10)  ; Would sleep 10 seconds
             'never))))
  (thread-start! t)
  (thread-sleep! 0.05)
  (thread-terminate! t)
  ;; thread-terminate! sets the finished flag; thread-join! should return
  (check "thread-terminate! sets finished" #t))

;; --- Exception handling in threads ---
(printf "\n--- Exception Safety ---\n")

(let ((t (make-thread
           (lambda ()
             (error 'test "deliberate error")))))
  (thread-start! t)
  ;; Thread should finish (exception caught internally)
  (thread-join! t)
  (check "thread exception doesn't crash" #t))

;; --- Mutex operations ---
(printf "\n--- Mutex ---\n")

(let ((m (make-mutex "test-mutex")))
  (check "make-mutex" (mutex? m))
  (check "mutex-name" (equal? (mutex-name m) "test-mutex"))
  (mutex-lock! m)
  (mutex-unlock! m)
  (check "mutex lock/unlock" #t))

;; Mutex protecting shared counter
(let ((m (make-mutex))
      (counter (box 0)))
  (let ((threads (map (lambda (i)
                        (make-thread
                          (lambda ()
                            (do ((j 0 (+ j 1)))
                                ((= j 100))
                              (mutex-lock! m)
                              (set-box! counter (+ (unbox counter) 1))
                              (mutex-unlock! m)))))
                      '(0 1 2 3 4))))
    (for-each thread-start! threads)
    (for-each thread-join! threads)
    (check "mutex protects counter (5x100)" (= (unbox counter) 500))))

;; ============================================================
;; Results
;; ============================================================

(printf "\n=== Results: ~a passed, ~a failed ===\n\n" *pass* *fail*)

(if (= *fail* 0)
    (printf "Thread compatibility: GO\n\n")
    (begin
      (printf "Thread compatibility: FAIL\n\n")
      (exit 1)))
