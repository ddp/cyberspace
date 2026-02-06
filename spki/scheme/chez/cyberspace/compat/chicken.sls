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

(library (cyberspace compat chicken)
  (export
    ;; Output
    print
    ;; String operations
    conc string-intersperse string-split
    ;; Association lists
    alist-ref alist-update alist-delete
    ;; Condition handling
    handle-exceptions get-condition-property
    ;; Optional/keyword argument helpers
    get-opt get-key)

  (import (rnrs)
          (only (chezscheme) printf format void
                with-output-to-string display))

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

) ;; end library
