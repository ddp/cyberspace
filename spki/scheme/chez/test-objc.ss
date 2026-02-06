#!/usr/bin/env scheme-script
;;; Test the Objective-C bridge from Chez Scheme
;;; Library of Cyberspace - Chez Port
;;;
;;; This is the go/no-go test: can Chez Scheme drive Cocoa?
;;;
;;; Run:
;;;   cd spki/scheme/chez
;;;   ./build-objc-bridge.sh
;;;   scheme --libdirs . test-objc.ss
;;;
;;; What this tests:
;;;   1. Foundation: NSString creation and roundtrip
;;;   2. Foundation: NSMutableArray manipulation
;;;   3. Foundation: NSDictionary creation
;;;   4. Foundation: NSNumber boxing
;;;   5. Introspection: class names, responds-to, description
;;;   6. Runtime: Dynamic class creation with Scheme callbacks
;;;   7. NSApplication: Can we bootstrap Cocoa? (non-blocking test)
;;;
;;; If all tests pass, the Chez port is viable.

(import (rnrs)
        (only (chezscheme)
              printf foreign-callable lock-object
              load-shared-object guard format)
        (cyberspace objc))

;; Load the bridge
(objc-init!)

(define pass-count 0)
(define fail-count 0)

(define (test name thunk)
  (guard (exn
          [#t (set! fail-count (+ fail-count 1))
              (printf "  FAIL ~a: ~a~n" name
                      (if (message-condition? exn)
                          (condition-message exn)
                          exn))])
    (thunk)
    (set! pass-count (+ pass-count 1))
    (printf "  pass ~a~n" name)))

(define (assert-equal name expected actual)
  (unless (equal? expected actual)
    (error 'assert-equal
           (format "~a: expected ~s, got ~s" name expected actual))))

;; ============================================================
(printf "~n=== Objective-C Bridge Test Suite ===~n~n")

;; ---- NSString ----
(printf "--- NSString ---~n")

(test "nsstring roundtrip"
  (lambda ()
    (let* ((s (nsstring "Hello from Chez Scheme!"))
           (back (nsstring->string s)))
      (assert-equal "roundtrip" "Hello from Chez Scheme!" back))))

(test "nsstring empty"
  (lambda ()
    (let* ((s (nsstring ""))
           (back (nsstring->string s)))
      (assert-equal "empty" "" back))))

(test "nsstring unicode"
  (lambda ()
    (let* ((s (nsstring "\x03BB; calculus"))  ; lambda
           (back (nsstring->string s)))
      (assert-equal "unicode" "\x03BB; calculus" back))))

(test "nsstring length"
  (lambda ()
    (let* ((s (nsstring "cyberspace"))
           (len (msg/int s (objc-sel "length"))))
      (assert-equal "length" 10 len))))

(test "nsstring uppercaseString"
  (lambda ()
    (let* ((s (nsstring "hello"))
           (upper (msg s (objc-sel "uppercaseString")))
           (result (nsstring->string upper)))
      (assert-equal "uppercase" "HELLO" result))))

(test "nsstring isEqualToString:"
  (lambda ()
    (let* ((a (nsstring "vault"))
           (b (nsstring "vault"))
           (c (nsstring "forge"))
           (eq-sel (objc-sel "isEqualToString:")))
      (assert-equal "equal" #t (msg/bool1 a eq-sel b))
      (assert-equal "not-equal" #f (msg/bool1 a eq-sel c)))))

;; ---- NSNumber ----
(printf "~n--- NSNumber ---~n")

(test "nsnumber int"
  (lambda ()
    (let* ((n (nsnumber/int 42))
           (val (msg/int n (objc-sel "integerValue"))))
      (assert-equal "int" 42 val))))

(test "nsnumber double"
  (lambda ()
    (let* ((n (nsnumber/double 3.14))
           (val (msg/double n (objc-sel "doubleValue"))))
      ;; Floating point: check within epsilon
      (unless (< (abs (- val 3.14)) 0.001)
        (error 'assert "double" val)))))

;; ---- NSMutableArray ----
(printf "~n--- NSArray ---~n")

(test "nsarray create and count"
  (lambda ()
    (let ((arr (nsarray (nsstring "alpha")
                        (nsstring "beta")
                        (nsstring "gamma"))))
      (assert-equal "count" 3 (nsarray-count arr)))))

(test "nsarray element access"
  (lambda ()
    (let ((arr (nsarray (nsstring "vault")
                        (nsstring "gossip")
                        (nsstring "forge"))))
      (assert-equal "element-0" "vault"  (nsstring->string (nsarray-ref arr 0)))
      (assert-equal "element-1" "gossip" (nsstring->string (nsarray-ref arr 1)))
      (assert-equal "element-2" "forge"  (nsstring->string (nsarray-ref arr 2))))))

(test "nsarray addObject: / removeLastObject"
  (lambda ()
    (let* ((arr (nsarray (nsstring "a")))
           (add-sel (objc-sel "addObject:"))
           (rem-sel (objc-sel "removeLastObject")))
      (msg/void1 arr add-sel (nsstring "b"))
      (assert-equal "after-add" 2 (nsarray-count arr))
      (msg/void arr rem-sel)
      (assert-equal "after-remove" 1 (nsarray-count arr)))))

;; ---- NSDictionary ----
(printf "~n--- NSDictionary ---~n")

(test "nsdict create and lookup"
  (lambda ()
    (let* ((d (nsdict (nsstring "name") (nsstring "cyberspace")
                      (nsstring "version") (nsstring "0.4.0")))
           (obj-sel (objc-sel "objectForKey:"))
           (name (msg/1 d obj-sel (nsstring "name")))
           (ver  (msg/1 d obj-sel (nsstring "version"))))
      (assert-equal "name" "cyberspace" (nsstring->string name))
      (assert-equal "version" "0.4.0" (nsstring->string ver)))))

(test "nsdict count"
  (lambda ()
    (let ((d (nsdict (nsstring "k1") (nsstring "v1")
                     (nsstring "k2") (nsstring "v2"))))
      (assert-equal "count" 2 (msg/int d (objc-sel "count"))))))

;; ---- Introspection ----
(printf "~n--- Introspection ---~n")

(test "class name"
  (lambda ()
    ;; NSString class cluster: literals are __NSCFConstantString or similar
    (let ((s (nsstring "test")))
      (let ((name (objc-class-name s)))
        ;; Just verify it returns a non-empty string
        (unless (> (string-length name) 0)
          (error 'assert "empty class name"))))))

(test "responds-to?"
  (lambda ()
    (let ((s (nsstring "test")))
      (assert-equal "responds-length" #t (objc-responds-to? s "length"))
      (assert-equal "responds-bogus"  #f (objc-responds-to? s "xyzzyNotAMethod")))))

(test "is-kind-of?"
  (lambda ()
    (let ((s (nsstring "test")))
      (assert-equal "is-NSString" #t (objc-is-kind-of? s "NSString"))
      (assert-equal "is-NSObject" #t (objc-is-kind-of? s "NSObject"))
      (assert-equal "not-NSArray" #f (objc-is-kind-of? s "NSArray")))))

(test "description"
  (lambda ()
    (let ((n (nsnumber/int 1984)))
      (assert-equal "description" "1984" (objc-description n)))))

;; ---- Autorelease Pool ----
(printf "~n--- Autorelease Pool ---~n")

(test "with-autorelease-pool"
  (lambda ()
    (with-autorelease-pool
      (let* ((s (nsstring "pooled"))
             (back (nsstring->string s)))
        (assert-equal "pooled" "pooled" back)))))

;; ---- Runtime Class Creation ----
(printf "~n--- Runtime Class Creation ---~n")

(test "dynamic class with Scheme callback"
  (lambda ()
    ;; Create a class at runtime with a method implemented in Scheme.
    ;; This proves delegates can work -- the essential pattern for
    ;; NSApplicationDelegate, WKScriptMessageHandler, etc.
    (let* ((cls (objc-create-class "CyberTestDelegate" "NSObject"))

           ;; Create a Scheme callback for -(void)ping
           ;; ObjC type encoding: v = void, @ = id (self), : = SEL
           (ping-called #f)
           (ping-cb (foreign-callable
                     (lambda (self cmd)
                       (set! ping-called #t))
                     (void* void*)
                     void)))

      ;; Lock callback to prevent GC
      (lock-object ping-cb)

      ;; Add method and register class
      (objc-add-method! cls "ping" ping-cb "v@:")
      (objc-register-class! cls)

      ;; Instantiate and call
      (let ((obj (objc-init-obj (objc-alloc cls))))
        (msg/void obj (objc-sel "ping"))
        (assert-equal "callback-invoked" #t ping-called)

        ;; Verify introspection works on dynamic class
        (assert-equal "dynamic-class-name" "CyberTestDelegate"
                      (objc-class-name obj))
        (assert-equal "dynamic-responds" #t
                      (objc-responds-to? obj "ping"))))))

(test "dynamic class with argument"
  (lambda ()
    ;; Method that receives an NSString argument
    (let* ((cls (objc-create-class "CyberTestHandler" "NSObject"))
           (received-msg "")
           (handle-cb (foreign-callable
                       (lambda (self cmd arg)
                         ;; arg is an NSString (void*)
                         (set! received-msg (nsstring->string arg)))
                       (void* void* void*)
                       void)))

      (lock-object handle-cb)
      (objc-add-method! cls "handleMessage:" handle-cb "v@:@")
      (objc-register-class! cls)

      (let ((obj (objc-init-obj (objc-alloc cls))))
        (msg/void1 obj (objc-sel "handleMessage:") (nsstring "seal-commit"))
        (assert-equal "received" "seal-commit" received-msg)))))

;; ---- NSApplication Bootstrap ----
(printf "~n--- NSApplication ---~n")

(test "nsapp creation"
  (lambda ()
    ;; Just verify we can get the shared application instance.
    ;; Don't call nsapp-run! -- that blocks.
    (let ((app (nsapp)))
      (unless (not (objc-null? app))
        (error 'assert "NSApp is nil"))
      ;; Verify it's actually an NSApplication
      (assert-equal "is-NSApplication" #t
                    (objc-is-kind-of? app "NSApplication")))))

(test "nsapp activation policy"
  (lambda ()
    ;; Set to regular (shows in Dock) -- proves we can configure the app
    (nsapp-set-policy! 'regular)
    ;; No assertion needed -- if it doesn't crash, it works
    ))

;; ============================================================
;; Results
;; ============================================================

(printf "~n=== Results: ~d passed, ~d failed ===~n~n"
        pass-count fail-count)

(when (> fail-count 0)
  (printf "*** BRIDGE IS NOT VIABLE -- ~d failures ***~n" fail-count)
  (exit 1))

(printf "Objective-C bridge: GO~n")
(printf "Chez Scheme can drive Cocoa.~n~n")
