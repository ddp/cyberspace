;;; inspector.scm - Dylan/CCL-style debugger for Cyberspace Scheme
;;;
;;; Integrated inspector that makes the REPL a debugger.
;;; When errors occur, drop into inspection context with:
;;;   - Clean stack traces (not CPS noise)
;;;   - Object browser with navigation
;;;   - Frame navigation
;;;   - Restarts
;;;
;;; Object Inspector (Memo-052 Section 8.2):
;;;   :i obj  - Enter inspector mode for object
;;;   :s      - Show current object
;;;   :d N    - Descend into slot N
;;;   :u      - Go up to parent object
;;;   :h      - Show navigation history
;;;   :b      - Bookmark current object
;;;   :t      - Show object type info
;;;
;;; Heritage: Symbolics, LispWorks, Dylan, CCL, Mach ddb, NT kd

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

   ;; Object inspector navigation (Memo-052 8.2)
   inspector-show          ; :s - show current object
   inspector-descend       ; :d N - descend into slot
   inspector-up            ; :u - go up
   inspector-history       ; :h - show history
   inspector-bookmark      ; :b - bookmark current
   inspector-type          ; :t - show type info
   *inspector-current*     ; current object
   *inspector-stack*       ; navigation history
   *inspector-bookmarks*   ; bookmarked objects

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
          (only srfi-1 filter iota take)
          srfi-4             ; u8vector for blob inspection
          srfi-13
          srfi-69
          os                 ; box-drawing utilities
          tty-ffi)

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
  (define *inspector-current* #f)       ; current object being inspected
  (define *inspector-stack* '())        ; navigation history (list of previous objects)
  (define *inspector-bookmarks* '())    ; bookmarked objects

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
  ;; Object Inspection - Type-Specific Display (Memo-052 8.2)
  ;; ============================================================

  ;; Helper: get type name for display
  (define (insp-type-name obj)
    "Get human-readable type name for object."
    (cond
      ((null? obj) "null")
      ((pair? obj) "pair")
      ((vector? obj) "vector")
      ((u8vector? obj) "u8vector")
      ((string? obj) "string")
      ((symbol? obj) "symbol")
      ((number? obj) (insp-number-type obj))
      ((procedure? obj) "procedure")
      ((hash-table? obj) "hash-table")
      ((blob? obj) "blob")
      ((port? obj) "port")
      ((boolean? obj) "boolean")
      ((char? obj) "char")
      ((eof-object? obj) "eof-object")
      ;; Check for SPKI structures (s-expression based)
      ((and (pair? obj) (memq (car obj) '(cert signed-cert signature
                                          principal tag validity
                                          audit-entry)))
       (symbol->string (car obj)))
      (else "object")))

  (define (insp-number-type n)
    "Get specific number type."
    (cond
      ((exact-integer? n) "integer")
      ((flonum? n) "flonum")
      ((ratnum? n) "rational")
      (else "number")))

  (define (insp-safe-length lst)
    "Length that handles improper lists."
    (let loop ((l lst) (n 0))
      (cond
        ((null? l) n)
        ((pair? l) (loop (cdr l) (+ n 1)))
        (else (sprintf "~a + dotted" n)))))

  ;; Helper: format value for display (truncated)
  (define (insp-format-value val #!optional (max-len 40))
    "Format value for display, truncating if needed."
    (let ((s (with-output-to-string (lambda () (write val)))))
      (if (> (string-length s) max-len)
          (string-append (substring s 0 (- max-len 3)) "...")
          s)))

  ;; Helper: hex byte display
  (define (insp-hex-byte b)
    "Format byte as 2-digit hex."
    (let ((s (number->string b 16)))
      (if (< (string-length s) 2)
          (string-append "0" s)
          s)))

  ;; Helper: get slots for an object (returns list of (index . value) or (name . value))
  (define (insp-get-slots obj)
    "Get inspectable slots for object."
    (cond
      ((pair? obj)
       (list (cons 0 (car obj)) (cons 1 (cdr obj))))
      ((vector? obj)
       (map (lambda (i) (cons i (vector-ref obj i)))
            (iota (min (vector-length obj) 20))))  ; limit to 20 slots
      ((u8vector? obj)
       (map (lambda (i) (cons i (u8vector-ref obj i)))
            (iota (min (u8vector-length obj) 32))))
      ((hash-table? obj)
       (take (hash-table->alist obj) (min (hash-table-size obj) 20)))
      ((string? obj)
       (map (lambda (i) (cons i (string-ref obj i)))
            (iota (min (string-length obj) 20))))
      ;; SPKI s-expression structures
      ((and (pair? obj) (symbol? (car obj)))
       (map (lambda (item i)
              (cons i item))
            (cdr obj)
            (iota (length (cdr obj)))))
      (else '())))

  ;; Display function for pairs
  (define (insp-display-pair obj box)
    (box-print box (sprintf "Type: pair"))
    (let ((len (insp-safe-length obj)))
      (if (number? len)
          (box-print box (sprintf "Length: ~a elements" len))
          (box-print box (sprintf "Length: ~a" len))))
    (print (box-separator box))
    (box-print box (sprintf "[0] car: ~a ~a"
                            (insp-type-name (car obj))
                            (insp-format-value (car obj) 30)))
    (box-print box (sprintf "[1] cdr: ~a ~a"
                            (insp-type-name (cdr obj))
                            (insp-format-value (cdr obj) 30))))

  ;; Display function for vectors
  (define (insp-display-vector obj box)
    (let ((len (vector-length obj)))
      (box-print box (sprintf "Type: vector"))
      (box-print box (sprintf "Length: ~a elements" len))
      (print (box-separator box))
      (let ((show-count (min len 10)))
        (do ((i 0 (+ i 1)))
            ((>= i show-count))
          (box-print box (sprintf "[~a] ~a ~a"
                                  i
                                  (insp-type-name (vector-ref obj i))
                                  (insp-format-value (vector-ref obj i) 30))))
        (when (> len 10)
          (box-print box (sprintf "... (~a more)" (- len 10)))))))

  ;; Display function for hash-tables
  (define (insp-display-hash-table obj box)
    (let ((size (hash-table-size obj))
          (keys (hash-table-keys obj)))
      (box-print box (sprintf "Type: hash-table"))
      (box-print box (sprintf "Size: ~a entries" size))
      (print (box-separator box))
      (let loop ((ks keys) (i 0))
        (when (and (pair? ks) (< i 10))
          (let ((k (car ks)))
            (box-print box (sprintf "[~a] ~a => ~a"
                                    i
                                    (insp-format-value k 15)
                                    (insp-format-value (hash-table-ref obj k) 25))))
          (loop (cdr ks) (+ i 1))))
      (when (> size 10)
        (box-print box (sprintf "... (~a more)" (- size 10))))))

  ;; Display function for procedures
  (define (insp-display-procedure obj box)
    (box-print box (sprintf "Type: procedure"))
    ;; Try to get procedure info
    (let ((info (procedure-information obj)))
      (if info
          (begin
            (when (and (pair? info) (symbol? (car info)))
              (box-print box (sprintf "Name: ~a" (car info))))
            (when (and (pair? info) (pair? (cdr info)))
              (box-print box (sprintf "Arity: ~a"
                                      (if (list? (cdr info))
                                          (length (cdr info))
                                          "variable")))))
          (box-print box (sprintf "Info: ~a" obj)))))

  ;; Display function for blobs
  (define (insp-display-blob obj box)
    (let* ((size (blob-size obj))
           (preview-size (min size 32))
           (bytes (blob->u8vector/shared obj)))
      (box-print box (sprintf "Type: blob"))
      (box-print box (sprintf "Size: ~a bytes" size))
      (print (box-separator box))
      ;; Hex preview
      (box-print box "Hex preview (first 32 bytes):")
      (let loop ((i 0) (line ""))
        (cond
          ((>= i preview-size)
           (when (> (string-length line) 0)
             (box-print box (sprintf "  ~a" line))))
          ((and (> i 0) (= (modulo i 16) 0))
           (box-print box (sprintf "  ~a" line))
           (loop i ""))
          (else
           (loop (+ i 1)
                 (string-append line
                                (if (> (string-length line) 0) " " "")
                                (insp-hex-byte (u8vector-ref bytes i)))))))))

  ;; Display function for strings
  (define (insp-display-string obj box)
    (let ((len (string-length obj)))
      (box-print box (sprintf "Type: string"))
      (box-print box (sprintf "Length: ~a characters" len))
      (print (box-separator box))
      (if (<= len 60)
          (box-print box (sprintf "Value: ~s" obj))
          (begin
            (box-print box (sprintf "Preview: ~s" (substring obj 0 60)))
            (box-print box (sprintf "... (~a more chars)" (- len 60)))))))

  ;; Display function for SPKI certificates
  (define (insp-display-spki obj box)
    (let ((type (car obj)))
      (box-print box (sprintf "Type: ~a" type))
      (print (box-separator box))
      (let loop ((fields (cdr obj)) (i 0))
        (when (pair? fields)
          (let ((field (car fields)))
            (if (and (pair? field) (symbol? (car field)))
                (box-print box (sprintf "[~a] ~a: ~a"
                                        i
                                        (car field)
                                        (insp-format-value (cdr field) 30)))
                (box-print box (sprintf "[~a] ~a"
                                        i
                                        (insp-format-value field 35)))))
          (loop (cdr fields) (+ i 1))))))

  ;; Main describe function with box display
  (define (describe obj)
    "Describe an object with type-specific display in a box."
    (let* ((type-name (insp-type-name obj))
           (box (make-box 42)))
      (print (box-top box (sprintf "Inspecting: ~a" type-name)))
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
        ((blob? obj)
         (insp-display-blob obj box))
        ((string? obj)
         (insp-display-string obj box))
        ((symbol? obj)
         (box-print box (sprintf "Type: symbol"))
         (box-print box (sprintf "Value: ~a" obj)))
        ((number? obj)
         (box-print box (sprintf "Type: ~a" (insp-number-type obj)))
         (box-print box (sprintf "Value: ~a" obj)))
        ((boolean? obj)
         (box-print box (sprintf "Type: boolean"))
         (box-print box (sprintf "Value: ~a" obj)))
        ((char? obj)
         (box-print box (sprintf "Type: char"))
         (box-print box (sprintf "Value: ~s (~a)" obj (char->integer obj))))
        ((port? obj)
         (box-print box (sprintf "Type: port"))
         (box-print box (sprintf "Value: ~a" obj)))
        (else
         (box-print box (sprintf "Type: ~a" type-name))
         (box-print box (sprintf "Value: ~a" obj))))

      ;; Show navigation hints if slots available
      (let ((slot-list (insp-get-slots obj)))
        (when (pair? slot-list)
          (print (box-separator box))
          (let ((max-slots (min (length slot-list) 5)))
            (do ((i 0 (+ i 1)))
                ((>= i max-slots))
              (box-print box (sprintf ":d ~a  - inspect slot ~a" i i))))
          (when (> (length slot-list) 5)
            (box-print box (sprintf "... (~a more slots)" (- (length slot-list) 5))))
          (box-print box ":u    - go back")))
      (print (box-bottom box))
      obj))

  ;; Slots access (for navigation)
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
      ((and (u8vector? obj) (number? slot) (< slot (u8vector-length obj)))
       (u8vector-ref obj slot))
      ((and (string? obj) (number? slot) (< slot (string-length obj)))
       (string-ref obj slot))
      ((hash-table? obj)
       (let ((keys (hash-table-keys obj)))
         (if (< slot (length keys))
             (hash-table-ref obj (list-ref keys slot))
             #f)))
      ;; SPKI s-expression structures
      ((and (pair? obj) (symbol? (car obj)) (< slot (length (cdr obj))))
       (list-ref (cdr obj) slot))
      (else #f)))

  ;; ============================================================
  ;; Object Inspector Navigation (Memo-052 Section 8.2)
  ;; ============================================================

  (define (inspector-show)
    "Show current inspected object (:s command)."
    (if *inspector-current*
        (describe *inspector-current*)
        (print "No object being inspected. Use (inspect OBJ) or :i OBJ to start.")))

  (define (inspector-descend n)
    "Descend into slot N of current object (:d N command)."
    (if (not *inspector-current*)
        (print "No object being inspected. Use (inspect OBJ) first.")
        (let ((val (slot-ref *inspector-current* n)))
          (if val
              (begin
                ;; Push current onto stack
                (set! *inspector-stack* (cons *inspector-current* *inspector-stack*))
                ;; Descend into slot
                (set! *inspector-current* val)
                (describe *inspector-current*))
              (printf "Slot ~a not found or empty.~n" n)))))

  (define (inspector-up)
    "Go up to parent object (:u command)."
    (if (null? *inspector-stack*)
        (print "At top level - no parent object.")
        (begin
          (set! *inspector-current* (car *inspector-stack*))
          (set! *inspector-stack* (cdr *inspector-stack*))
          (describe *inspector-current*))))

  (define (inspector-history)
    "Show navigation history (:h command)."
    (print "")
    (print "Inspector Navigation History:")
    (print "")
    (if (null? *inspector-stack*)
        (print "  (empty)")
        (let loop ((stack (reverse *inspector-stack*)) (i 0))
          (when (pair? stack)
            (printf "  [~a] ~a: ~a~n"
                    i
                    (insp-type-name (car stack))
                    (insp-format-value (car stack) 40))
            (loop (cdr stack) (+ i 1)))))
    (when *inspector-current*
      (printf "  --> ~a: ~a (current)~n"
              (insp-type-name *inspector-current*)
              (insp-format-value *inspector-current* 40)))
    (print ""))

  (define (inspector-bookmark)
    "Bookmark current object (:b command)."
    (if (not *inspector-current*)
        (print "No object to bookmark.")
        (let ((n (length *inspector-bookmarks*)))
          (set! *inspector-bookmarks*
                (cons (cons n *inspector-current*) *inspector-bookmarks*))
          (printf "Bookmarked as #~a: ~a~n"
                  n
                  (insp-format-value *inspector-current* 40)))))

  (define (inspector-type)
    "Show detailed type info for current object (:t command)."
    (if (not *inspector-current*)
        (print "No object being inspected.")
        (let* ((obj *inspector-current*)
               (box (make-box 42)))
          (print (box-top box "Type Information"))
          (box-print box (sprintf "Type: ~a" (insp-type-name obj)))
          (cond
            ((pair? obj)
             (box-print box (sprintf "Proper list: ~a" (list? obj)))
             (box-print box (sprintf "Length: ~a" (insp-safe-length obj))))
            ((vector? obj)
             (box-print box (sprintf "Length: ~a" (vector-length obj))))
            ((string? obj)
             (box-print box (sprintf "Length: ~a chars" (string-length obj))))
            ((procedure? obj)
             (let ((info (procedure-information obj)))
               (when info
                 (box-print box (sprintf "Info: ~a" info)))))
            ((hash-table? obj)
             (box-print box (sprintf "Size: ~a entries" (hash-table-size obj))))
            ((blob? obj)
             (box-print box (sprintf "Size: ~a bytes" (blob-size obj))))
            ((number? obj)
             (box-print box (sprintf "Exact: ~a" (exact? obj)))
             (box-print box (sprintf "Integer: ~a" (integer? obj)))))
          (print (box-bottom box)))))

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

  (define (debug-read-line prompt)
    "Read line with immediate shortcuts (. ?) for inspector.
     ESC defers to regular read-line for special keys."
    (display prompt)
    (flush-output)
    (tty-set-raw)
    (let ((c (tty-raw-char)))
      (tty-set-cooked)
      (cond
        ((< c 0) #f)              ; EOF
        ((= c 46) (newline) ".")  ; . immediate
        ((= c 63) (newline) "?")  ; ? immediate
        ((= c 27) (read-line))    ; ESC - let read-line handle
        ((= c 4) #f)              ; Ctrl-D
        ((= c 3) (newline) "")    ; Ctrl-C
        (else
         ;; Regular char - redisplay prompt+char so backspace is safe
         (let ((first-char (string (integer->char c))))
           ;; Clear line and redisplay with first char as part of "prompt"
           (display "\r")
           (display prompt)
           (display first-char)
           (flush-output)
           (let ((rest (read-line)))
             (if (eof-object? rest)
                 first-char
                 (string-append first-char rest))))))))

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
      (let ((input (debug-read-line "debug> ")))
        (cond
          ((or (not input) (eof-object? input)
               (member input '(":q" ":quit" ",q" "bye" "bye." "exit" "(exit)" "q" "quit")))
           (print "Returning to REPL.")
           #f)

          ;; Dylan-style: period means "do it" / proceed
          ((member input '("." "go" "proceed" "continue"))
           (print "Proceeding.")
           #f)

          ((member input '("?" ":?" ":h" ":help" "help"))
           (print "")
           (print "Cyberspace Scheme")
           (print "")
           (print "  (library)         - Enter the Library")
           (print "  (search 'topic)   - Search everything")
           (print "  (status)          - Node status")
           (print "  (inspect OBJ)     - Inspect anything")
           (print "")
           (print "  (help 'topics)    - All help topics")
           (print "  (.) proceed  (?) help  (exit) quit")
           (print "")
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
    "Interactively inspect any object. Sets inspector state for navigation."
    ;; Clear previous navigation
    (set! *inspector-stack* '())
    ;; Set current object
    (set! *inspector-current* obj)
    ;; Add to history
    (set! *inspect-history* (cons obj *inspect-history*))
    ;; Display
    (print "")
    (describe obj)
    (print "")
    (print "Navigation: :s show  :d N descend  :u up  :h history  :b bookmark  :t type")
    (print "")
    obj)

) ;; end module
