;;; test-mdns.scm - Regression tests for mDNS enrollment discovery
;;;
;;; Test Categories:
;;;   1. Constants/Configuration
;;;   2. Listener Lifecycle
;;;   3. Announcement Lifecycle
;;;   4. End-to-End Flow (with timeout)
;;;   5. Edge Cases

(import scheme
        (chicken base)
        (chicken format)
        (chicken tcp)
        (chicken port)
        (chicken condition)
        (chicken time)
        srfi-1
        srfi-18
        mdns)

;; ============================================================
;; Test Framework
;; ============================================================

(define *tests-run* 0)
(define *tests-passed* 0)
(define *tests-failed* '())

(define (test name thunk)
  (set! *tests-run* (+ 1 *tests-run*))
  (handle-exceptions exn
    (begin
      (printf "FAIL: ~a~n" name)
      (printf "      ~a~n" (get-condition-property exn 'exn 'message "unknown error"))
      (set! *tests-failed* (cons name *tests-failed*)))
    (let ((result (thunk)))
      (if result
          (begin
            (printf "PASS: ~a~n" name)
            (set! *tests-passed* (+ 1 *tests-passed*)))
          (begin
            (printf "FAIL: ~a (returned #f)~n" name)
            (set! *tests-failed* (cons name *tests-failed*)))))))

(define (assert-equal expected actual)
  (or (equal? expected actual)
      (error (sprintf "expected ~s, got ~s" expected actual))))

(define (assert-true val)
  (or val (error "expected truthy value")))

;; ============================================================
;; 1. Constants
;; ============================================================

(printf "~n=== mDNS Regression Tests ===~n~n")
(printf "--- Constants ---~n")

(test "mdns-port is 5353"
  (lambda () (assert-equal 5353 mdns-port)))

(test "enrollment-port is 7654"
  (lambda () (assert-equal 7654 enrollment-port)))

(test "cyberspace-service is correct"
  (lambda () (assert-equal "_cyberspace-enroll._tcp" cyberspace-service)))

;; ============================================================
;; 2. Listener Lifecycle
;; ============================================================

(printf "~n--- Listener Lifecycle ---~n")

(define *test-requests* '())

(define (test-handler name pubkey host port)
  (set! *test-requests* (cons (list name pubkey host port) *test-requests*)))

(test "listen-for-enrollments returns listener"
  (lambda ()
    (let ((listener (listen-for-enrollments test-handler port: 18001)))
      (thread-sleep! 0.05)
      (stop-listening)
      (handle-exceptions exn #f (tcp-close listener))
      (assert-true listener))))

(test "stop-listening is idempotent"
  (lambda ()
    (stop-listening)
    (stop-listening)
    #t))

;; ============================================================
;; 3. Announcement Lifecycle
;; ============================================================

(printf "~n--- Announcement Lifecycle ---~n")

(test "announce-enrollment returns listener"
  (lambda ()
    (let ((listener (announce-enrollment 'test-node "TESTKEY" port: 18002)))
      (thread-sleep! 0.05)
      (stop-announcement)
      (handle-exceptions exn #f (tcp-close listener))
      (assert-true listener))))

(test "stop-announcement is idempotent"
  (lambda ()
    (stop-announcement)
    (stop-announcement)
    #t))

;; ============================================================
;; 4. End-to-End: Request -> Listener
;; ============================================================

(printf "~n--- End-to-End Flow ---~n")

(test "listener receives enrollment request"
  (lambda ()
    (set! *test-requests* '())
    (let ((listener (listen-for-enrollments test-handler port: 18003)))
      (thread-sleep! 0.1)

      ;; Send request directly via TCP
      (handle-exceptions exn
        (printf "      connect error: ~a~n"
                (get-condition-property exn 'exn 'message "?"))
        (let-values (((in out) (tcp-connect "127.0.0.1" 18003)))
          (display "(enrollment-request (name node-1) (pubkey \"KEY1\") (port 7654))" out)
          (close-output-port out)
          (close-input-port in)))

      (thread-sleep! 0.2)
      (stop-listening)
      (handle-exceptions exn #f (tcp-close listener))

      (printf "      received: ~a requests~n" (length *test-requests*))
      (assert-true (> (length *test-requests*) 0)))))

(test "multiple requests handled"
  (lambda ()
    (set! *test-requests* '())
    (let ((listener (listen-for-enrollments test-handler port: 18004)))
      (thread-sleep! 0.1)

      ;; Send 3 requests
      (do ((i 1 (+ i 1)))
          ((> i 3))
        (handle-exceptions exn #f
          (let-values (((in out) (tcp-connect "127.0.0.1" 18004)))
            (display (sprintf "(enrollment-request (name node-~a) (pubkey \"KEY~a\") (port 7654))" i i) out)
            (close-output-port out)
            (close-input-port in)))
        (thread-sleep! 0.05))

      (thread-sleep! 0.2)
      (stop-listening)
      (handle-exceptions exn #f (tcp-close listener))

      (printf "      received: ~a requests~n" (length *test-requests*))
      (assert-true (>= (length *test-requests*) 2)))))

;; ============================================================
;; 5. Edge Cases
;; ============================================================

(printf "~n--- Edge Cases ---~n")

(test "malformed request doesn't crash"
  (lambda ()
    (let ((listener (listen-for-enrollments test-handler port: 18005)))
      (thread-sleep! 0.1)
      (handle-exceptions exn #f
        (let-values (((in out) (tcp-connect "127.0.0.1" 18005)))
          (display "garbage (((" out)
          (close-output-port out)
          (close-input-port in)))
      (thread-sleep! 0.1)
      (stop-listening)
      (handle-exceptions exn #f (tcp-close listener))
      #t)))

(test "empty request doesn't crash"
  (lambda ()
    (let ((listener (listen-for-enrollments test-handler port: 18006)))
      (thread-sleep! 0.1)
      (handle-exceptions exn #f
        (let-values (((in out) (tcp-connect "127.0.0.1" 18006)))
          (close-output-port out)
          (close-input-port in)))
      (thread-sleep! 0.1)
      (stop-listening)
      (handle-exceptions exn #f (tcp-close listener))
      #t)))

(test "restart listener after stop"
  (lambda ()
    (let ((l1 (listen-for-enrollments test-handler port: 18007)))
      (thread-sleep! 0.05)
      (stop-listening)
      (handle-exceptions exn #f (tcp-close l1))
      (thread-sleep! 0.1)
      (let ((l2 (listen-for-enrollments test-handler port: 18007)))
        (thread-sleep! 0.05)
        (stop-listening)
        (handle-exceptions exn #f (tcp-close l2))
        #t))))

;; ============================================================
;; Summary
;; ============================================================

(printf "~n=== Results ===~n")
(printf "Passed: ~a/~a~n" *tests-passed* *tests-run*)
(when (> (length *tests-failed*) 0)
  (printf "Failed:~n")
  (for-each (lambda (n) (printf "  - ~a~n" n)) (reverse *tests-failed*)))
(newline)
