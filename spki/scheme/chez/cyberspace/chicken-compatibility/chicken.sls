;;; Chicken Scheme Compatibility Library
;;; Library of Cyberspace - Chez Port
;;;
;;; Maps common Chicken-isms to Chez equivalents:
;;;   - print (multi-arg display with newline)
;;;   - sprintf (format to string)
;;;   - conc (string concatenation of arbitrary values)
;;;   - string-intersperse (join strings with separator)
;;;   - alist-ref, alist-update (association list operations)
;;;   - handle-exceptions (-> guard)
;;;   - get-condition-property (condition accessor)
;;;   - optional argument helpers
;;;   - current-seconds (epoch time)
;;;   - SRFI-1 list utilities (filter-map, take, drop, any, every)
;;;   - SRFI-13 string utilities (string-contains, string-prefix?)

(library (cyberspace chicken-compatibility chicken)
  (export
    ;; Output
    print
    ;; String operations
    conc string-intersperse string-split
    string-contains string-prefix? string-suffix?
    string-trim-both string-take-right string-drop-right
    string-concatenate
    ;; Association lists
    alist-ref alist-update alist-delete
    ;; Condition handling
    handle-exceptions get-condition-property
    ;; Optional/keyword argument helpers
    get-opt get-key
    ;; Time
    current-seconds
    ;; SRFI-1 list utilities
    filter-map take drop any every find
    ;; String join (Chicken's string-join)
    string-join
    ;; Arithmetic (Chicken uses modulo/quotient/remainder)
    modulo quotient remainder
    ;; File system (Chez 9.5 compat)
    directory-exists?)

  (import (except (rnrs) find file-exists?)
          (only (chezscheme) printf format void
                with-output-to-string
                file-exists? system
                open-process-ports native-transcoder
                current-time time-second))

  ;; ============================================================
  ;; Output
  ;; ============================================================

  ;; Chicken's print: display each arg, then newline
  (define (print . args)
    (for-each display args)
    (newline))

  ;; ============================================================
  ;; String Operations
  ;; ============================================================

  ;; Chicken's conc: like string-append but converts non-strings
  (define (conc . args)
    (apply string-append
           (map (lambda (x)
                  (if (string? x)
                      x
                      (with-output-to-string (lambda () (display x)))))
                args)))

  ;; Chicken's string-intersperse: join list of strings with separator
  (define (string-intersperse lst . rest)
    (let ((sep (if (null? rest) " " (car rest))))
      (cond
        ((null? lst) "")
        ((null? (cdr lst)) (car lst))
        (else
         (let loop ((rest (cdr lst))
                    (acc (car lst)))
           (if (null? rest)
               acc
               (loop (cdr rest)
                     (string-append acc sep (car rest)))))))))

  ;; Simple string-split on a character
  (define (string-split str . rest)
    (let ((sep (if (null? rest) #\space (string-ref (car rest) 0))))
      (let loop ((i 0) (start 0) (acc '()))
        (cond
          ((= i (string-length str))
           (reverse (if (= start i)
                        acc
                        (cons (substring str start i) acc))))
          ((char=? (string-ref str i) sep)
           (loop (+ i 1) (+ i 1)
                 (if (= start i)
                     acc
                     (cons (substring str start i) acc))))
          (else
           (loop (+ i 1) start acc))))))

  ;; ============================================================
  ;; Association Lists
  ;; ============================================================

  ;; Chicken's alist-ref: look up key, return value or default
  (define (alist-ref key alist . rest)
    (let ((compare (if (null? rest) equal? (car rest)))
          (default (if (or (null? rest) (null? (cdr rest))) #f (cadr rest))))
      (let loop ((al alist))
        (cond
          ((null? al) default)
          ((compare key (caar al)) (cdar al))
          (else (loop (cdr al)))))))

  ;; Chicken's alist-update: set key to value, replacing if exists
  (define (alist-update key value alist . rest)
    (let ((compare (if (null? rest) equal? (car rest))))
      (cons (cons key value)
            (alist-delete key alist compare))))

  ;; Chicken's alist-delete: remove key from alist
  (define (alist-delete key alist . rest)
    (let ((compare (if (null? rest) equal? (car rest))))
      (filter (lambda (pair)
                (not (compare key (car pair))))
              alist)))

  ;; ============================================================
  ;; Condition Handling
  ;; ============================================================

  ;; Chicken's handle-exceptions: (handle-exceptions exn handler body ...)
  ;; Maps to R6RS guard.
  ;; NOTE: This is a syntax form.  Usage:
  ;;   (handle-exceptions exn fallback-expr body-expr)
  (define-syntax handle-exceptions
    (syntax-rules ()
      [(_ exn handler body ...)
       (guard (exn [#t handler])
         body ...)]))

  ;; Chicken's get-condition-property: extract from condition object
  ;; (get-condition-property exn 'exn 'message "default")
  (define (get-condition-property exn kind prop . rest)
    (let ((default (if (null? rest) #f (car rest))))
      (cond
        ;; R6RS message condition
        ((and (eq? prop 'message) (message-condition? exn))
         (condition-message exn))
        ;; R6RS who condition
        ((and (eq? prop 'who) (who-condition? exn))
         (condition-who exn))
        ;; Irritants
        ((and (eq? prop 'arguments) (irritants-condition? exn))
         (condition-irritants exn))
        (else default))))

  ;; ============================================================
  ;; Optional/Keyword Argument Helpers
  ;;
  ;; Since Chez has no #!optional or #!key, use rest args + helpers.
  ;;
  ;; Pattern:
  ;;   Chicken: (define (foo x #!optional (y 10)) ...)
  ;;   Chez:    (define (foo x . rest)
  ;;              (let ((y (get-opt rest 0 10))) ...))
  ;;
  ;;   Chicken: (define (foo #!key (n 3) (p 0.01)) ...)
  ;;   Chez:    (define (foo . opts)
  ;;              (let ((n (get-key opts 'n 3))
  ;;                    (p (get-key opts 'p 0.01))) ...))
  ;; ============================================================

  ;; Get positional optional argument from rest list
  (define (get-opt rest index default)
    (if (> (length rest) index)
        (list-ref rest index)
        default))

  ;; Get keyword argument from flat key-value rest list
  ;; (get-key '(threshold: 3 total: 5) 'threshold: 3)
  (define (get-key opts key default)
    (let loop ((rest opts))
      (cond
        ((null? rest) default)
        ((null? (cdr rest)) default)
        ((eq? (car rest) key) (cadr rest))
        (else (loop (cddr rest))))))

  ;; ============================================================
  ;; String Utilities (SRFI-13 subset + Chicken extras)
  ;; ============================================================

  ;; string-contains: find substring, return starting index or #f
  (define (string-contains haystack needle)
    (let ((hlen (string-length haystack))
          (nlen (string-length needle)))
      (if (> nlen hlen)
          #f
          (let loop ((i 0))
            (cond
              ((> (+ i nlen) hlen) #f)
              ((string=? (substring haystack i (+ i nlen)) needle) i)
              (else (loop (+ i 1))))))))

  ;; string-prefix?: check if str starts with prefix
  (define (string-prefix? prefix str)
    (let ((plen (string-length prefix))
          (slen (string-length str)))
      (and (<= plen slen)
           (string=? (substring str 0 plen) prefix))))

  ;; string-trim-both: strip leading/trailing whitespace
  (define (string-trim-both str)
    (let* ((len (string-length str))
           (start (let loop ((i 0))
                    (if (and (< i len) (char-whitespace? (string-ref str i)))
                        (loop (+ i 1))
                        i)))
           (end (let loop ((i (- len 1)))
                  (if (and (>= i start) (char-whitespace? (string-ref str i)))
                      (loop (- i 1))
                      (+ i 1)))))
      (if (>= start end)
          ""
          (substring str start end))))

  ;; string-suffix?: check if str ends with suffix
  (define (string-suffix? suffix str)
    (let ((xlen (string-length suffix))
          (slen (string-length str)))
      (and (<= xlen slen)
           (string=? (substring str (- slen xlen) slen) suffix))))

  ;; string-take-right: return last n characters
  (define (string-take-right str n)
    (let ((len (string-length str)))
      (if (>= n len) str (substring str (- len n) len))))

  ;; string-drop-right: remove last n characters
  (define (string-drop-right str n)
    (let ((len (string-length str)))
      (if (>= n len) "" (substring str 0 (- len n)))))

  ;; string-concatenate: concatenate list of strings (SRFI-13)
  (define (string-concatenate lst)
    (apply string-append lst))

  ;; ============================================================
  ;; Time
  ;; ============================================================

  ;; Chicken's (current-seconds): POSIX epoch seconds
  (define (current-seconds)
    (time-second (current-time)))

  ;; ============================================================
  ;; SRFI-1 List Utilities
  ;; ============================================================

  ;; filter-map: map + filter in one pass (drop #f results)
  (define (filter-map proc lst)
    (let loop ((rest lst) (acc '()))
      (if (null? rest)
          (reverse acc)
          (let ((result (proc (car rest))))
            (loop (cdr rest)
                  (if result (cons result acc) acc))))))

  ;; take: return first n elements
  (define (take lst n)
    (let loop ((rest lst) (k n) (acc '()))
      (if (or (zero? k) (null? rest))
          (reverse acc)
          (loop (cdr rest) (- k 1) (cons (car rest) acc)))))

  ;; drop: skip first n elements
  (define (drop lst n)
    (let loop ((rest lst) (k n))
      (if (or (zero? k) (null? rest))
          rest
          (loop (cdr rest) (- k 1)))))

  ;; any: return first truthy result of applying pred
  (define (any pred lst)
    (let loop ((rest lst))
      (cond
        ((null? rest) #f)
        ((pred (car rest)) => (lambda (x) x))
        (else (loop (cdr rest))))))

  ;; every: return #f if any element fails pred
  (define (every pred lst)
    (let loop ((rest lst) (last #t))
      (cond
        ((null? rest) last)
        ((pred (car rest)) => (lambda (x) (loop (cdr rest) x)))
        (else #f))))

  ;; find: return first element satisfying pred, or #f
  (define (find pred lst)
    (let loop ((rest lst))
      (cond
        ((null? rest) #f)
        ((pred (car rest)) (car rest))
        (else (loop (cdr rest))))))

  ;; ============================================================
  ;; String Join (Chicken's string-join)
  ;; ============================================================

  ;; string-join: join list of strings with separator (default " ")
  (define (string-join lst . rest)
    (let ((sep (if (null? rest) " " (car rest))))
      (cond
        ((null? lst) "")
        ((null? (cdr lst)) (car lst))
        (else
         (let loop ((rest (cdr lst))
                    (acc (car lst)))
           (if (null? rest)
               acc
               (loop (cdr rest)
                     (string-append acc sep (car rest)))))))))

  ;; ============================================================
  ;; Arithmetic
  ;; ============================================================

  ;; Chicken's modulo/quotient/remainder: R5RS names not in (rnrs)
  (define modulo mod)
  (define (quotient a b) (div a b))
  (define (remainder a b) (mod a b))

  ;; ============================================================
  ;; File System (Chez 9.5 compatibility)
  ;; ============================================================

  ;; directory-exists? is not in Chez 9.5.8;
  ;; available in newer versions.  Use file-exists? + stat.
  (define (directory-exists? path)
    (and (file-exists? path)
         (guard (exn [#t #f])
           (let-values (((to-stdin from-stdout from-stderr)
                         (open-process-ports
                           (string-append "test -d " path " && echo y")
                           'line (native-transcoder))))
             (let ((result (get-line from-stdout)))
               (close-port to-stdin)
               (close-port from-stdout)
               (close-port from-stderr)
               (and (string? result) (string=? result "y")))))))

) ;; end library
