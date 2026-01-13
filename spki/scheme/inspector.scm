;;; inspector.scm - Dylan/CCL-style debugger for Cyberspace Scheme
;;;
;;; Integrated inspector that makes the REPL a debugger.
;;; When errors occur, drop into inspection context with:
;;;   - Clean stack traces (not CPS noise)
;;;   - Object browser
;;;   - Frame navigation
;;;   - Restarts
;;;
;;; Heritage: Symbolics, LispWorks, Dylan, CCL, Mach ddb, NT kd
;;;
;;; Copyright (c) 2026 Yoyodyne. See LICENSE.

(module inspector
  (;; Entry points
   inspect
   inspect-error
   inspector-repl

   ;; Call tracking (our own, not CPS)
   traced
   push-frame!
   pop-frame!
   *call-stack*
   clear-stack!

   ;; Stack navigation
   current-frames
   frame-ref
   frame-locals
   frame-source

   ;; Object inspection
   describe
   slots
   slot-ref

   ;; Restarts
   define-restart
   invoke-restart
   available-restarts

   ;; REPL integration
   install-inspector!
   *inspector-enabled*

   ;; Utilities
   pprint
   pp-frame)

  (import scheme
          (chicken base)
          (chicken format)
          (chicken string)
          (chicken condition)
          (chicken port)
          (chicken io)
          (chicken blob)
          (chicken pretty-print)
          (chicken syntax)
          (chicken time)
          (chicken repl)
          (only srfi-1 filter iota)
          srfi-13
          srfi-69)

  ;; ============================================================
  ;; State
  ;; ============================================================

  (define *inspector-enabled* #t)
  (define *current-condition* #f)
  (define *current-frames* '())
  (define *current-frame-index* 0)
  (define *restarts* '())
  (define *inspect-history* '())

  ;; Our own call stack - maintained explicitly
  (define *call-stack* '())
  (define *call-stack-max* 100)

  ;; ============================================================
  ;; Explicit Call Tracking
  ;; ============================================================
  ;;
  ;; Since Chicken's CPS erases call structure, we track it ourselves.
  ;; Wrap functions with (traced name body ...) to record calls.

  (define (push-frame! name args source)
    "Push a frame onto our call stack"
    (set! *call-stack*
      (take-n (cons (list name args source (current-seconds))
                    *call-stack*)
              (min (+ 1 (length *call-stack*)) *call-stack-max*))))

  (define (pop-frame!)
    "Pop top frame"
    (when (pair? *call-stack*)
      (set! *call-stack* (cdr *call-stack*))))

  (define (clear-stack!)
    "Clear call stack"
    (set! *call-stack* '()))

  (define (take-n lst n)
    (if (or (null? lst) (<= n 0)) '()
        (cons (car lst) (take-n (cdr lst) (- n 1)))))

  ;; Tracing macro - wrap function calls to record in our stack
  (define-syntax traced
    (syntax-rules ()
      ((_ name body ...)
       (begin
         (push-frame! 'name '() #f)
         (let ((result (begin body ...)))
           (pop-frame!)
           result)))))

  ;; ============================================================
  ;; Stack Frame Reconstruction
  ;; ============================================================
  ;;
  ;; Chicken's call-chain gives us CPS frames. We try to make
  ;; them readable by filtering noise and extracting source info.

  (define (fetch-call-chain)
    "Get current call chain, filtering CPS internals"
    (let ((chain (with-exception-handler
                   (lambda (e) '())
                   (lambda ()
                     (condition-property-accessor 'exn 'call-chain '())))))
      (if (procedure? chain) (chain) '())))

  (define (cps-noise? frame)
    "Is this frame CPS implementation noise?"
    (let ((name (frame-name frame)))
      (or (not name)
          (string-prefix? "##" (symbol->string name))
          (string-prefix? "chicken." (symbol->string name))
          (memq name '(call-with-values values apply)))))

  (define (frame-name frame)
    "Extract procedure name from frame"
    (and (pair? frame)
         (pair? (car frame))
         (caar frame)))

  (define (clean-frames raw-frames)
    "Filter CPS noise, keep meaningful frames"
    (filter (lambda (f) (not (cps-noise? f))) raw-frames))

  (define (current-frames)
    "Get current cleaned frame list"
    *current-frames*)

  (define (frame-ref n)
    "Get frame by index"
    (and (< n (length *current-frames*))
         (list-ref *current-frames* n)))

  (define (frame-locals frame)
    "Extract local variables from frame (if available)"
    ;; Chicken doesn't expose locals directly, but we can
    ;; extract what's in the frame structure
    (if (and (pair? frame) (pair? (cdr frame)))
        (cdr frame)
        '()))

  (define (frame-source frame)
    "Get source location for frame"
    ;; Would need debug info compiled in
    (and (pair? frame)
         (let ((props (cdr frame)))
           (and (pair? props)
                (assq 'source props)))))

  ;; ============================================================
  ;; Object Inspection
  ;; ============================================================

  (define (describe obj)
    "Describe an object's type and contents"
    (cond
      ((null? obj) (print "  null list"))
      ((pair? obj)
       (printf "  pair (list of ~a elements)~n" (safe-length obj))
       (describe-list obj))
      ((vector? obj)
       (printf "  vector of ~a elements~n" (vector-length obj))
       (describe-vector obj))
      ((string? obj)
       (printf "  string (~a chars): ~s~n" (string-length obj)
               (if (> (string-length obj) 60)
                   (string-append (substring obj 0 60) "...")
                   obj)))
      ((number? obj)
       (printf "  ~a: ~a~n" (number-type obj) obj))
      ((symbol? obj)
       (printf "  symbol: ~a~n" obj))
      ((procedure? obj)
       (printf "  procedure~n")
       (describe-procedure obj))
      ((hash-table? obj)
       (printf "  hash-table (~a entries)~n" (hash-table-size obj))
       (describe-hash-table obj))
      ((blob? obj)
       (printf "  blob (~a bytes)~n" (blob-size obj)))
      ((port? obj)
       (printf "  port: ~a~n" obj))
      ((boolean? obj)
       (printf "  boolean: ~a~n" obj))
      (else
       (printf "  ~a~n" obj))))

  (define (safe-length lst)
    "Length that handles improper lists"
    (let loop ((l lst) (n 0))
      (cond
        ((null? l) n)
        ((pair? l) (loop (cdr l) (+ n 1)))
        (else (sprintf "~a + dotted" n)))))

  (define (number-type n)
    (cond
      ((exact-integer? n) "exact integer")
      ((flonum? n) "flonum")
      ((ratnum? n) "rational")
      (else "number")))

  (define (describe-list lst)
    (let loop ((l lst) (i 0))
      (when (and (pair? l) (< i 10))
        (printf "    [~a] ~s~n" i (car l))
        (loop (cdr l) (+ i 1)))
      (when (and (pair? l) (>= i 10))
        (printf "    ... (~a more)~n" (- (length lst) 10)))))

  (define (describe-vector vec)
    (let ((len (vector-length vec)))
      (do ((i 0 (+ i 1)))
          ((or (>= i len) (>= i 10)))
        (printf "    [~a] ~s~n" i (vector-ref vec i)))
      (when (> len 10)
        (printf "    ... (~a more)~n" (- len 10)))))

  (define (describe-procedure proc)
    ;; Limited info available for procedures
    (printf "    ~a~n" proc))

  (define (describe-hash-table ht)
    (let ((keys (hash-table-keys ht))
          (shown 0))
      (for-each
        (lambda (k)
          (when (< shown 10)
            (printf "    ~s => ~s~n" k (hash-table-ref ht k))
            (set! shown (+ shown 1))))
        keys)
      (when (> (length keys) 10)
        (printf "    ... (~a more)~n" (- (length keys) 10)))))

  (define (slots obj)
    "Return alist of slot names and values"
    (cond
      ((pair? obj)
       `((car . ,(car obj)) (cdr . ,(cdr obj))))
      ((vector? obj)
       (map (lambda (i) (cons i (vector-ref obj i)))
            (iota (vector-length obj))))
      ((hash-table? obj)
       (hash-table->alist obj))
      (else '())))

  (define (slot-ref obj slot)
    "Get slot value from object"
    (cond
      ((and (pair? obj) (eq? slot 'car)) (car obj))
      ((and (pair? obj) (eq? slot 'cdr)) (cdr obj))
      ((and (vector? obj) (number? slot)) (vector-ref obj slot))
      ((hash-table? obj) (hash-table-ref/default obj slot #f))
      (else #f)))

  ;; ============================================================
  ;; Pretty Printing
  ;; ============================================================

  (define (pprint obj)
    "Pretty print object"
    (pretty-print obj)
    (newline))

  (define (pp-frame n)
    "Pretty print frame n"
    (let ((frame (frame-ref n)))
      (if frame
          (begin
            (printf "Frame ~a:~n" n)
            (let ((name (frame-name frame)))
              (when name (printf "  procedure: ~a~n" name)))
            (let ((locals (frame-locals frame)))
              (unless (null? locals)
                (printf "  context:~n")
                (for-each (lambda (l) (printf "    ~s~n" l)) locals))))
          (printf "No frame ~a~n" n))))

  ;; ============================================================
  ;; Restarts
  ;; ============================================================

  (define (define-restart name description thunk)
    "Register a restart option"
    (set! *restarts*
      (cons (list name description thunk) *restarts*)))

  (define (available-restarts)
    "List available restarts"
    *restarts*)

  (define (invoke-restart name)
    "Invoke a restart by name"
    (let ((r (assq name *restarts*)))
      (if r
          ((caddr r))
          (printf "No restart named ~a~n" name))))

  (define (clear-restarts!)
    (set! *restarts* '()))

  ;; ============================================================
  ;; Inspector REPL
  ;; ============================================================

  (define (inspector-repl condition)
    "Enter inspector REPL for condition"
    (set! *current-condition* condition)
    ;; Prefer our explicit stack, fall back to CPS chain
    (set! *current-frames*
      (if (pair? *call-stack*)
          *call-stack*
          (clean-frames
            (or ((condition-property-accessor 'exn 'call-chain #f) condition)
                '()))))
    (set! *current-frame-index* 0)
    (clear-restarts!)

    ;; Default restarts
    (define-restart 'abort "Return to top level"
      (lambda () (signal (make-property-condition 'user-abort))))
    (define-restart 'continue "Continue execution"
      (lambda () #f))

    (print "")
    (printf "~a~n" (or ((condition-property-accessor 'exn 'message #f) condition)
                       "Error"))
    (print "")

    ;; Show stack - format depends on source
    (let ((frames *current-frames*))
      (if (null? frames)
          (print "  (no stack frames available)")
          (let loop ((fs frames) (i 0))
            (when (and (pair? fs) (< i 10))
              (let ((f (car fs)))
                ;; Our frames: (name args source time)
                ;; CPS frames: ((name . stuff) ...)
                (if (and (pair? f) (symbol? (car f)))
                    (printf "  [~a] ~a~n" i (car f))  ; our frame
                    (printf "  [~a] ~a~n" i (or (frame-name f) "(anonymous)"))))
              (loop (cdr fs) (+ i 1)))
            (when (> (length frames) 10)
              (printf "  ... (~a more frames)~n" (- (length frames) 10))))))

    (print "")
    (print "(.) proceed  (?) help  (exit) quit  |  frame N  inspect EXPR  restarts")
    (print "")

    ;; Inspector loop
    (let loop ()
      (display "debug> ")
      (flush-output)
      (let ((input (read-line)))
        (cond
          ((or (eof-object? input)
               (member input '(":q" ":quit" ",q" "bye" "bye." "exit" "(exit)" "q" "quit")))
           (print "Returning to REPL.")
           #f)

          ;; Dylan-style: period means "do it" / proceed
          ((member input '("." "go" "proceed" "continue"))
           (print "Proceeding.")
           #f)

          ((member input '("?" ":?" ":h" ":help" "help"))
           (print "(.) proceed  (?) help  (exit) quit")
           (print "frame N  inspect EXPR  restarts")
           (loop))

          ;; Frame commands: :f N or frame N
          ((or (string-prefix? ":f " input)
               (string-prefix? "frame " input)
               (string-prefix? "f " input))
           (let* ((prefix-len (cond ((string-prefix? "frame " input) 6)
                                    ((string-prefix? ":f " input) 3)
                                    (else 2)))
                  (n (string->number (string-trim-both (substring input prefix-len)))))
             (if n (pp-frame n) (print "Usage: frame N")))
           (loop))

          ;; Inspect commands: :i EXPR or inspect EXPR
          ((or (string-prefix? ":i " input)
               (string-prefix? "inspect " input)
               (string-prefix? "i " input))
           (let* ((prefix-len (cond ((string-prefix? "inspect " input) 8)
                                    ((string-prefix? ":i " input) 3)
                                    (else 2)))
                  (expr (substring input prefix-len)))
             (handle-exceptions exn
               (printf "Error: ~a~n" ((condition-property-accessor 'exn 'message) exn))
               (describe (eval (read (open-input-string expr))))))
           (loop))

          ;; Restarts: :r or restarts
          ((member input '(":r" ":restarts" "r" "restarts"))
           (print "Available restarts:")
           (for-each
             (lambda (r)
               (printf "  ~a - ~a~n" (car r) (cadr r)))
             *restarts*)
           (loop))

          ((or (string-prefix? ":r " input)
               (string-prefix? "restart " input))
           (let* ((prefix-len (if (string-prefix? "restart " input) 8 3))
                  (name (string->symbol (substring input prefix-len))))
             (invoke-restart name)))

          ((string-prefix? ":" input)
           (printf "Unknown command: ~a~n" input)
           (loop))

          (else
           ;; Evaluate as Scheme
           (handle-exceptions exn
             (printf "Error: ~a~n" ((condition-property-accessor 'exn 'message) exn))
             (let ((result (eval (read (open-input-string input)))))
               (unless (eq? result (void))
                 (pprint result))))
           (loop))))))

  ;; ============================================================
  ;; Error Handler Installation
  ;; ============================================================

  (define (inspect-error exn)
    "Inspect an error condition"
    (when *inspector-enabled*
      (inspector-repl exn)))

  (define (install-inspector!)
    "Install inspector as default error handler"
    (set! *inspector-enabled* #t)
    (print "Inspector installed. Errors will drop into debug REPL."))

  (define (inspect obj)
    "Interactively inspect any object"
    (print "")
    (describe obj)
    (print "")
    (set! *inspect-history* (cons obj *inspect-history*))
    obj)

) ;; end module
