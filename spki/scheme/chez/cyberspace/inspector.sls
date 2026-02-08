;;; inspector.sls - Dylan/CCL-style Debugger for Cyberspace (Chez Port)
;;; Library of Cyberspace
;;;
;;; Integrated inspector that makes the REPL a debugger.
;;; When errors occur, drop into inspection context with:
;;;   - Object browser with navigation
;;;   - Frame navigation
;;;   - Restarts
;;;
;;; Heritage: Symbolics, LispWorks, Dylan, CCL, Mach ddb, NT kd
;;;
;;; Ported from inspector.scm.
;;; Copyright (c) 2026 Yoyodyne. See LICENSE.

(library (cyberspace inspector)
  (export
    ;; Entry points
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

    ;; Object inspector navigation (Memo-052 8.2)
    inspector-show
    inspector-descend
    inspector-up
    inspector-history
    inspector-bookmark
    inspector-type
    *inspector-current*
    *inspector-stack*
    *inspector-bookmarks*

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

  (import (rnrs)
          (only (chezscheme)
                printf format void
                pretty-print
                flush-output-port
                eval interaction-environment
                with-input-from-string with-output-to-string
                procedure-arity-mask)
          (cyberspace chicken-compatibility chicken)
          (cyberspace chicken-compatibility hashtable)
          (cyberspace os)
          (cyberspace tty-ffi))

  ;; ============================================================
  ;; State
  ;; ============================================================

  (define *inspector-enabled* #f)
  (define *current-condition* #f)
  (define *current-frames* '())
  (define *current-frame-index* 0)
  (define *restarts* '())
  (define *inspect-history* '())

  ;; Our own call stack - maintained explicitly
  (define *call-stack* '())
  (define *call-stack-max* 100)

  ;; Object inspector state (Memo-052 Section 8.2)
  (define *inspector-current* #f)
  (define *inspector-stack* '())
  (define *inspector-bookmarks* '())

  ;; ============================================================
  ;; Explicit Call Tracking
  ;; ============================================================

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

  ;; Tracing macro
  (define-syntax traced
    (syntax-rules ()
      ((_ name body ...)
       (begin
         (push-frame! 'name '() #f)
         (let ((result (begin body ...)))
           (pop-frame!)
           result)))))

  ;; ============================================================
  ;; Stack Frame Access
  ;; ============================================================

  (define (frame-name frame)
    "Extract procedure name from frame"
    (and (pair? frame)
         (if (symbol? (car frame))
             (car frame)
             (and (pair? (car frame))
                  (caar frame)))))

  (define (current-frames)
    *current-frames*)

  (define (frame-ref n)
    (and (< n (length *current-frames*))
         (list-ref *current-frames* n)))

  (define (frame-locals frame)
    (if (and (pair? frame) (pair? (cdr frame)))
        (cdr frame)
        '()))

  (define (frame-source frame)
    (and (pair? frame)
         (let ((props (cdr frame)))
           (and (pair? props) (assq 'source props)))))

  ;; ============================================================
  ;; Object Inspection - Type-Specific Display
  ;; ============================================================

  (define (insp-type-name obj)
    (cond
      ((null? obj) "null")
      ((pair? obj)
       (if (and (symbol? (car obj))
                (memq (car obj) '(cert signed-cert signature
                                  principal tag validity audit-entry)))
           (symbol->string (car obj))
           "pair"))
      ((vector? obj) "vector")
      ((bytevector? obj) "bytevector")
      ((string? obj) "string")
      ((symbol? obj) "symbol")
      ((number? obj) (insp-number-type obj))
      ((procedure? obj) "procedure")
      ((hash-table? obj) "hash-table")
      ((port? obj) "port")
      ((boolean? obj) "boolean")
      ((char? obj) "char")
      ((eof-object? obj) "eof-object")
      (else "object")))

  (define (insp-number-type n)
    (cond
      ((and (exact? n) (integer? n)) "integer")
      ((and (inexact? n) (real? n)) "flonum")
      ((rational? n) "rational")
      (else "number")))

  (define (insp-safe-length lst)
    (let loop ((l lst) (n 0))
      (cond
        ((null? l) n)
        ((pair? l) (loop (cdr l) (+ n 1)))
        (else (string-append (number->string n) " + dotted")))))

  (define (insp-format-value val . rest)
    (let ((max-len (if (null? rest) 40 (car rest))))
      (let ((s (with-output-to-string (lambda () (write val)))))
        (if (> (string-length s) max-len)
            (string-append (substring s 0 (- max-len 3)) "...")
            s))))

  (define (insp-hex-byte b)
    (let ((s (number->string b 16)))
      (if (< (string-length s) 2)
          (string-append "0" s)
          s)))

  (define (insp-get-slots obj)
    (cond
      ((pair? obj)
       (list (cons 0 (car obj)) (cons 1 (cdr obj))))
      ((vector? obj)
       (let ((len (min (vector-length obj) 20)))
         (let loop ((i 0) (acc '()))
           (if (= i len) (reverse acc)
               (loop (+ i 1) (cons (cons i (vector-ref obj i)) acc))))))
      ((bytevector? obj)
       (let ((len (min (bytevector-length obj) 32)))
         (let loop ((i 0) (acc '()))
           (if (= i len) (reverse acc)
               (loop (+ i 1) (cons (cons i (bytevector-u8-ref obj i)) acc))))))
      ((hash-table? obj)
       (take (hash-table->alist obj) (min (hash-table-size obj) 20)))
      ((string? obj)
       (let ((len (min (string-length obj) 20)))
         (let loop ((i 0) (acc '()))
           (if (= i len) (reverse acc)
               (loop (+ i 1) (cons (cons i (string-ref obj i)) acc))))))
      ((and (pair? obj) (symbol? (car obj)))
       (let loop ((items (cdr obj)) (i 0) (acc '()))
         (if (null? items) (reverse acc)
             (loop (cdr items) (+ i 1) (cons (cons i (car items)) acc)))))
      (else '())))

  ;; ============================================================
  ;; Display Functions
  ;; ============================================================

  (define (insp-display-pair obj box)
    (box-print box (format "Type: pair"))
    (let ((len (insp-safe-length obj)))
      (if (number? len)
          (box-print box (format "Length: ~a elements" len))
          (box-print box (format "Length: ~a" len))))
    (display (box-separator box)) (newline)
    (box-print box (format "[0] car: ~a ~a"
                            (insp-type-name (car obj))
                            (insp-format-value (car obj) 30)))
    (box-print box (format "[1] cdr: ~a ~a"
                            (insp-type-name (cdr obj))
                            (insp-format-value (cdr obj) 30))))

  (define (insp-display-vector obj box)
    (let ((len (vector-length obj)))
      (box-print box (format "Type: vector"))
      (box-print box (format "Length: ~a elements" len))
      (display (box-separator box)) (newline)
      (let ((show-count (min len 10)))
        (do ((i 0 (+ i 1)))
            ((>= i show-count))
          (box-print box (format "[~a] ~a ~a"
                                  i
                                  (insp-type-name (vector-ref obj i))
                                  (insp-format-value (vector-ref obj i) 30))))
        (when (> len 10)
          (box-print box (format "... (~a more)" (- len 10)))))))

  (define (insp-display-hash-table obj box)
    (let ((size (hash-table-size obj))
          (keys (hash-table-keys obj)))
      (box-print box (format "Type: hash-table"))
      (box-print box (format "Size: ~a entries" size))
      (display (box-separator box)) (newline)
      (let loop ((ks keys) (i 0))
        (when (and (pair? ks) (< i 10))
          (let ((k (car ks)))
            (box-print box (format "[~a] ~a => ~a"
                                    i
                                    (insp-format-value k 15)
                                    (insp-format-value (hash-table-ref obj k) 25))))
          (loop (cdr ks) (+ i 1))))
      (when (> size 10)
        (box-print box (format "... (~a more)" (- size 10))))))

  (define (insp-display-procedure obj box)
    (box-print box (format "Type: procedure"))
    (box-print box (format "Arity mask: ~a" (procedure-arity-mask obj))))

  (define (insp-display-bytevector obj box)
    (let* ((size (bytevector-length obj))
           (preview-size (min size 32)))
      (box-print box (format "Type: bytevector"))
      (box-print box (format "Size: ~a bytes" size))
      (display (box-separator box)) (newline)
      (box-print box "Hex preview (first 32 bytes):")
      (let loop ((i 0) (line ""))
        (cond
          ((>= i preview-size)
           (when (> (string-length line) 0)
             (box-print box (format "  ~a" line))))
          ((and (> i 0) (= (mod i 16) 0))
           (box-print box (format "  ~a" line))
           (loop i ""))
          (else
           (loop (+ i 1)
                 (string-append line
                                (if (> (string-length line) 0) " " "")
                                (insp-hex-byte (bytevector-u8-ref obj i)))))))))

  (define (insp-display-string obj box)
    (let ((len (string-length obj)))
      (box-print box (format "Type: string"))
      (box-print box (format "Length: ~a characters" len))
      (display (box-separator box)) (newline)
      (if (<= len 60)
          (box-print box (format "Value: ~s" obj))
          (begin
            (box-print box (format "Preview: ~s" (substring obj 0 60)))
            (box-print box (format "... (~a more chars)" (- len 60)))))))

  (define (insp-display-spki obj box)
    (let ((type (car obj)))
      (box-print box (format "Type: ~a" type))
      (display (box-separator box)) (newline)
      (let loop ((fields (cdr obj)) (i 0))
        (when (pair? fields)
          (let ((field (car fields)))
            (if (and (pair? field) (symbol? (car field)))
                (box-print box (format "[~a] ~a: ~a"
                                        i
                                        (car field)
                                        (insp-format-value (cdr field) 30)))
                (box-print box (format "[~a] ~a"
                                        i
                                        (insp-format-value field 35)))))
          (loop (cdr fields) (+ i 1))))))

  ;; ============================================================
  ;; Main Describe
  ;; ============================================================

  (define (describe obj)
    "Describe an object with type-specific display in a box."
    (let* ((type-name (insp-type-name obj))
           (box (make-box 42)))
      (display (box-top box (format "Inspecting: ~a" type-name)))
      (newline)
      (cond
        ((null? obj)
         (box-print box "Type: null (empty list)"))
        ((pair? obj)
         (if (and (symbol? (car obj))
                  (memq (car obj) '(cert signed-cert signature
                                   principal tag validity audit-entry)))
             (insp-display-spki obj box)
             (insp-display-pair obj box)))
        ((vector? obj)
         (insp-display-vector obj box))
        ((hash-table? obj)
         (insp-display-hash-table obj box))
        ((procedure? obj)
         (insp-display-procedure obj box))
        ((bytevector? obj)
         (insp-display-bytevector obj box))
        ((string? obj)
         (insp-display-string obj box))
        ((symbol? obj)
         (box-print box (format "Type: symbol"))
         (box-print box (format "Value: ~a" obj)))
        ((number? obj)
         (box-print box (format "Type: ~a" (insp-number-type obj)))
         (box-print box (format "Value: ~a" obj)))
        ((boolean? obj)
         (box-print box (format "Type: boolean"))
         (box-print box (format "Value: ~a" obj)))
        ((char? obj)
         (box-print box (format "Type: char"))
         (box-print box (format "Value: ~s (~a)" obj (char->integer obj))))
        ((port? obj)
         (box-print box (format "Type: port"))
         (box-print box (format "Value: ~a" obj)))
        (else
         (box-print box (format "Type: ~a" type-name))
         (box-print box (format "Value: ~a" obj))))

      ;; Show navigation hints if slots available
      (let ((slot-list (insp-get-slots obj)))
        (when (pair? slot-list)
          (display (box-separator box)) (newline)
          (let ((max-slots (min (length slot-list) 5)))
            (do ((i 0 (+ i 1)))
                ((>= i max-slots))
              (box-print box (format ":d ~a  - inspect slot ~a" i i))))
          (when (> (length slot-list) 5)
            (box-print box (format "... (~a more slots)" (- (length slot-list) 5))))
          (box-print box ":u    - go back")))
      (display (box-bottom box)) (newline)
      obj))

  (define (slots obj)
    "Return alist of slot names and values."
    (insp-get-slots obj))

  (define (slot-ref obj slot)
    "Get slot value from object by index."
    (cond
      ((and (pair? obj) (= slot 0)) (car obj))
      ((and (pair? obj) (= slot 1)) (cdr obj))
      ((and (vector? obj) (number? slot) (< slot (vector-length obj)))
       (vector-ref obj slot))
      ((and (bytevector? obj) (number? slot) (< slot (bytevector-length obj)))
       (bytevector-u8-ref obj slot))
      ((and (string? obj) (number? slot) (< slot (string-length obj)))
       (string-ref obj slot))
      ((hash-table? obj)
       (let ((keys (hash-table-keys obj)))
         (if (< slot (length keys))
             (hash-table-ref obj (list-ref keys slot))
             #f)))
      ((and (pair? obj) (symbol? (car obj)) (< slot (length (cdr obj))))
       (list-ref (cdr obj) slot))
      (else #f)))

  ;; ============================================================
  ;; Object Inspector Navigation (Memo-052 Section 8.2)
  ;; ============================================================

  (define (inspector-show)
    (if *inspector-current*
        (describe *inspector-current*)
        (display "No object being inspected. Use (inspect OBJ) or :i OBJ to start.\n")))

  (define (inspector-descend n)
    (if (not *inspector-current*)
        (display "No object being inspected. Use (inspect OBJ) first.\n")
        (let ((val (slot-ref *inspector-current* n)))
          (if val
              (begin
                (set! *inspector-stack* (cons *inspector-current* *inspector-stack*))
                (set! *inspector-current* val)
                (describe *inspector-current*))
              (printf "Slot ~a not found or empty.~%" n)))))

  (define (inspector-up)
    (if (null? *inspector-stack*)
        (display "At top level - no parent object.\n")
        (begin
          (set! *inspector-current* (car *inspector-stack*))
          (set! *inspector-stack* (cdr *inspector-stack*))
          (describe *inspector-current*))))

  (define (inspector-history)
    (display "\nInspector Navigation History:\n\n")
    (if (null? *inspector-stack*)
        (display "  (empty)\n")
        (let loop ((stack (reverse *inspector-stack*)) (i 0))
          (when (pair? stack)
            (printf "  [~a] ~a: ~a~%"
                    i
                    (insp-type-name (car stack))
                    (insp-format-value (car stack) 40))
            (loop (cdr stack) (+ i 1)))))
    (when *inspector-current*
      (printf "  --> ~a: ~a (current)~%"
              (insp-type-name *inspector-current*)
              (insp-format-value *inspector-current* 40)))
    (display "\n"))

  (define (inspector-bookmark)
    (if (not *inspector-current*)
        (display "No object to bookmark.\n")
        (let ((n (length *inspector-bookmarks*)))
          (set! *inspector-bookmarks*
                (cons (cons n *inspector-current*) *inspector-bookmarks*))
          (printf "Bookmarked as #~a: ~a~%"
                  n
                  (insp-format-value *inspector-current* 40)))))

  (define (inspector-type)
    (if (not *inspector-current*)
        (display "No object being inspected.\n")
        (let* ((obj *inspector-current*)
               (box (make-box 42)))
          (display (box-top box "Type Information")) (newline)
          (box-print box (format "Type: ~a" (insp-type-name obj)))
          (cond
            ((pair? obj)
             (box-print box (format "Proper list: ~a" (list? obj)))
             (box-print box (format "Length: ~a" (insp-safe-length obj))))
            ((vector? obj)
             (box-print box (format "Length: ~a" (vector-length obj))))
            ((string? obj)
             (box-print box (format "Length: ~a chars" (string-length obj))))
            ((hash-table? obj)
             (box-print box (format "Size: ~a entries" (hash-table-size obj))))
            ((bytevector? obj)
             (box-print box (format "Size: ~a bytes" (bytevector-length obj))))
            ((number? obj)
             (box-print box (format "Exact: ~a" (exact? obj)))
             (box-print box (format "Integer: ~a" (integer? obj)))))
          (display (box-bottom box)) (newline))))

  ;; ============================================================
  ;; Pretty Printing
  ;; ============================================================

  (define (pprint obj)
    (pretty-print obj)
    (newline))

  (define (pp-frame n)
    (let ((frame (frame-ref n)))
      (if frame
          (begin
            (printf "Frame ~a:~%" n)
            (let ((name (frame-name frame)))
              (when name (printf "  procedure: ~a~%" name)))
            (let ((locals (frame-locals frame)))
              (unless (null? locals)
                (printf "  context:~%")
                (for-each (lambda (l) (printf "    ~s~%" l)) locals))))
          (printf "No frame ~a~%" n))))

  ;; ============================================================
  ;; Restarts
  ;; ============================================================

  (define (define-restart name description thunk)
    (set! *restarts*
      (cons (list name description thunk) *restarts*)))

  (define (available-restarts)
    *restarts*)

  (define (invoke-restart name)
    (let ((r (assq name *restarts*)))
      (if r
          ((caddr r))
          (printf "No restart named ~a~%" name))))

  (define (clear-restarts!)
    (set! *restarts* '()))

  ;; ============================================================
  ;; Inspector REPL
  ;; ============================================================

  (define (debug-read-line prompt)
    "Read line with immediate shortcuts for inspector."
    (display prompt)
    (flush-output-port (current-output-port))
    (tty-set-raw)
    (let ((c (tty-raw-char)))
      (tty-set-cooked)
      (cond
        ((< c 0) #f)
        ((= c 46) (newline) ".")   ; .
        ((= c 63) (newline) "?")   ; ?
        ((= c 27) (get-line (current-input-port)))  ; ESC
        ((= c 4) #f)               ; Ctrl-D
        ((= c 3) (newline) "")     ; Ctrl-C
        (else
         (let ((first-char (string (integer->char c))))
           (display "\r")
           (display prompt)
           (display first-char)
           (flush-output-port (current-output-port))
           (let ((rest-line (get-line (current-input-port))))
             (if (eof-object? rest-line)
                 first-char
                 (string-append first-char rest-line))))))))

  (define (inspector-repl condition)
    "Enter inspector REPL for condition"
    (set! *current-condition* condition)
    (set! *current-frames*
      (if (pair? *call-stack*)
          *call-stack*
          '()))
    (set! *current-frame-index* 0)
    (clear-restarts!)

    ;; Default restarts
    (define-restart 'abort "Return to top level" (lambda () #f))
    (define-restart 'continue "Continue execution" (lambda () #f))

    (display "\n")
    (printf "~a~%"
            (if (message-condition? condition)
                (condition-message condition)
                "Error"))
    (display "\n")

    ;; Show stack
    (let ((frames *current-frames*))
      (if (null? frames)
          (display "  (no stack frames available)\n")
          (let loop ((fs frames) (i 0))
            (when (and (pair? fs) (< i 10))
              (let ((f (car fs)))
                (if (and (pair? f) (symbol? (car f)))
                    (printf "  [~a] ~a~%" i (car f))
                    (printf "  [~a] ~a~%" i (or (frame-name f) "(anonymous)"))))
              (loop (cdr fs) (+ i 1)))
            (when (> (length frames) 10)
              (printf "  ... (~a more frames)~%" (- (length frames) 10))))))

    (display "\n")
    (display "(.) proceed  (?) help  (exit) quit  |  frame N  inspect EXPR  restarts\n")
    (display "\n")

    ;; Inspector loop
    (let loop ()
      (let ((input (debug-read-line "debug> ")))
        (cond
          ((or (not input) (eof-object? input)
               (member input '(":q" ":quit" ",q" "bye" "bye." "exit" "(exit)" "q" "quit")))
           (display "Returning to REPL.\n")
           #f)

          ((member input '("." "go" "proceed" "continue"))
           (display "Proceeding.\n")
           #f)

          ((member input '("?" ":?" ":h" ":help" "help"))
           (display "\nCyberspace Scheme\n\n")
           (display "  (library)         - Enter the Library\n")
           (display "  (search 'topic)   - Search everything\n")
           (display "  (status)          - Node status\n")
           (display "  (inspect OBJ)     - Inspect anything\n\n")
           (display "  (.) proceed  (?) help  (exit) quit\n\n")
           (loop))

          ((or (string-prefix? ":f " input)
               (string-prefix? "frame " input)
               (string-prefix? "f " input))
           (let* ((prefix-len (cond ((string-prefix? "frame " input) 6)
                                    ((string-prefix? ":f " input) 3)
                                    (else 2)))
                  (n (string->number (string-trim-both
                                       (substring input prefix-len
                                                  (string-length input))))))
             (if n (pp-frame n) (display "Usage: frame N\n")))
           (loop))

          ((or (string-prefix? ":i " input)
               (string-prefix? "inspect " input)
               (string-prefix? "i " input))
           (let* ((prefix-len (cond ((string-prefix? "inspect " input) 8)
                                    ((string-prefix? ":i " input) 3)
                                    (else 2)))
                  (expr (substring input prefix-len (string-length input))))
             (guard (exn
               [#t (printf "Error: ~a~%"
                           (if (message-condition? exn)
                               (condition-message exn)
                               "unknown"))])
               (describe (eval (read (open-input-string expr))
                               (interaction-environment)))))
           (loop))

          ((member input '(":r" ":restarts" "r" "restarts"))
           (display "Available restarts:\n")
           (for-each
             (lambda (r)
               (printf "  ~a - ~a~%" (car r) (cadr r)))
             *restarts*)
           (loop))

          ((or (string-prefix? ":r " input)
               (string-prefix? "restart " input))
           (let* ((prefix-len (if (string-prefix? "restart " input) 8 3))
                  (name (string->symbol
                          (substring input prefix-len (string-length input)))))
             (invoke-restart name)))

          ((and (> (string-length input) 0)
                (char=? (string-ref input 0) #\:))
           (printf "Unknown command: ~a~%" input)
           (loop))

          (else
           (guard (exn
             [#t (printf "Error: ~a~%"
                         (if (message-condition? exn)
                             (condition-message exn)
                             "unknown"))])
             (let ((result (eval (read (open-input-string input))
                                 (interaction-environment))))
               (unless (eq? result (void))
                 (pprint result))))
           (loop))))))

  ;; ============================================================
  ;; Error Handler Installation
  ;; ============================================================

  (define (inspect-error exn)
    (when *inspector-enabled*
      (inspector-repl exn)))

  (define (install-inspector!)
    (set! *inspector-enabled* #t)
    (display "Inspector installed. Errors will drop into debug REPL.\n"))

  (define (inspect obj)
    "Interactively inspect any object."
    (set! *inspector-stack* '())
    (set! *inspector-current* obj)
    (set! *inspect-history* (cons obj *inspect-history*))
    (display "\n")
    (describe obj)
    (display "\n")
    (display "Navigation: :s show  :d N descend  :u up  :h history  :b bookmark  :t type\n")
    (display "\n")
    obj)

) ;; end library
