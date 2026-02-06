;;; SPKI Scheme - S-expression Parser
;;; Library of Cyberspace - Chez Port
;;;
;;; S-expressions are the foundation of SPKI certificates.
;;; This module provides parsing, printing, and manipulation.
;;;
;;; Syntax:
;;;   (cert (issuer |base64...|) (subject |base64...|))
;;;
;;; Three types:
;;;   - Atom: identifier or keyword
;;;   - List: (...)
;;;   - Bytes: |base64| for binary data (keys, signatures)
;;;
;;; Ported from Chicken's sexp.scm.
;;; Changes: module -> library, (chicken *) -> (rnrs), blob -> bytevector,
;;;          base64 egg -> cyberspace compat base64.

(library (cyberspace sexp)
  (export
    sexp-atom sexp-list sexp-bytes
    sexp-atom? sexp-list? sexp-bytes?
    atom-value list-items bytes-value
    parse-sexp
    sexp->string
    sexp->string-indent
    find-tag
    get-tag-value)

  (import (rnrs)
          (only (chezscheme) printf format)
          (cyberspace compat blob)
          (prefix (cyberspace compat base64) b64:))

  ;; S-expression types (tagged records)
  (define-record-type (<sexp-atom> make-atom sexp-atom?)
    (fields (immutable value atom-value)))

  (define-record-type (<sexp-list> make-sexp-list sexp-list?)
    (fields (immutable items list-items)))

  (define-record-type (<sexp-bytes> make-bytes sexp-bytes?)
    (fields (immutable value bytes-value)))

  ;; Constructors (exported names)
  (define (sexp-atom s) (make-atom s))
  (define (sexp-list xs) (make-sexp-list xs))
  (define (sexp-bytes b) (make-bytes b))

  ;;; Base64 encoding/decoding (using compat library)

  (define (base64-encode bytes)
    "Encode bytevector to base64 string."
    (if (bytevector? bytes)
        (b64:base64-encode (blob->string bytes))
        ""))

  (define (base64-decode str)
    "Decode base64 string to bytevector."
    (string->blob (b64:base64-decode str)))

  ;;; Tokenizer

  (define-record-type (token make-token token?)
    (fields (immutable type token-type)
            (immutable value token-value)))

  (define (lparen) (make-token 'lparen #f))
  (define (rparen) (make-token 'rparen #f))
  (define (tatom s) (make-token 'atom s))
  (define (tbytes b) (make-token 'bytes b))

  (define (tokenize str)
    (let ((len (string-length str)))
      (let loop ((i 0) (acc '()))
        (if (>= i len)
            (reverse acc)
            (let ((c (string-ref str i)))
              (cond
               ;; Whitespace - skip
               ((char-whitespace? c)
                (loop (+ i 1) acc))

               ;; Left paren
               ((char=? c #\()
                (loop (+ i 1) (cons (lparen) acc)))

               ;; Right paren
               ((char=? c #\))
                (loop (+ i 1) (cons (rparen) acc)))

               ;; Bytes literal: |base64|
               ((char=? c #\|)
                (let find-end ((j (+ i 1)))
                  (cond
                   ((>= j len)
                    (error 'tokenize "Unterminated bytes literal"))
                   ((char=? (string-ref str j) #\|)
                    (let* ((b64-str (substring str (+ i 1) j))
                           (bytes (base64-decode b64-str)))
                      (loop (+ j 1) (cons (tbytes bytes) acc))))
                   (else
                    (find-end (+ j 1))))))

               ;; Atom: read until whitespace or paren
               (else
                (let read-atom ((j i))
                  (cond
                   ((>= j len)
                    (let ((atom (substring str i j)))
                      (loop j (cons (tatom atom) acc))))
                   (else
                    (let ((c (string-ref str j)))
                      (if (or (char-whitespace? c)
                              (char=? c #\()
                              (char=? c #\)))
                          (let ((atom (substring str i j)))
                            (loop j (cons (tatom atom) acc)))
                          (read-atom (+ j 1))))))))))))))

  ;;; Parser

  (define (parse-tokens tokens)
    (define (parse-list acc tokens)
      (cond
       ((null? tokens)
        (error 'parse-sexp "Unexpected end of input"))

       ((eq? (token-type (car tokens)) 'rparen)
        (values (reverse acc) (cdr tokens)))

       ((eq? (token-type (car tokens)) 'lparen)
        (let-values (((inner rest) (parse-list '() (cdr tokens))))
          (parse-list (cons (sexp-list inner) acc) rest)))

       ((eq? (token-type (car tokens)) 'atom)
        (parse-list (cons (sexp-atom (token-value (car tokens))) acc)
                    (cdr tokens)))

       ((eq? (token-type (car tokens)) 'bytes)
        (parse-list (cons (sexp-bytes (token-value (car tokens))) acc)
                    (cdr tokens)))

       (else
        (error 'parse-sexp "Unexpected token" (car tokens)))))

    (cond
     ((null? tokens)
      (error 'parse-sexp "Empty input"))

     ((eq? (token-type (car tokens)) 'lparen)
      (let-values (((sexp rest) (parse-list '() (cdr tokens))))
        (if (null? rest)
            (sexp-list sexp)
            (error 'parse-sexp "Unexpected tokens after s-expression"))))

     ((eq? (token-type (car tokens)) 'atom)
      (if (null? (cdr tokens))
          (sexp-atom (token-value (car tokens)))
          (error 'parse-sexp "Unexpected tokens after s-expression")))

     ((eq? (token-type (car tokens)) 'bytes)
      (if (null? (cdr tokens))
          (sexp-bytes (token-value (car tokens)))
          (error 'parse-sexp "Unexpected tokens after s-expression")))

     ((eq? (token-type (car tokens)) 'rparen)
      (error 'parse-sexp "Unexpected closing paren"))

     (else
      (error 'parse-sexp "Unexpected token" (car tokens)))))

  ;;; Main parse function

  (define (parse-sexp str)
    (parse-tokens (tokenize str)))

  ;;; Pretty-printing

  ;; SRFI-13 string-join equivalent
  (define (string-join lst sep)
    (cond
      ((null? lst) "")
      ((null? (cdr lst)) (car lst))
      (else
       (let loop ((rest (cdr lst)) (acc (car lst)))
         (if (null? rest)
             acc
             (loop (cdr rest)
                   (string-append acc sep (car rest))))))))

  (define (sexp->string sexp)
    (cond
     ((sexp-atom? sexp)
      (atom-value sexp))

     ((sexp-bytes? sexp)
      (string-append "|" (base64-encode (bytes-value sexp)) "|"))

     ((sexp-list? sexp)
      (let ((items (list-items sexp)))
        (if (null? items)
            "()"
            (string-append "("
                          (string-join (map sexp->string items) " ")
                          ")"))))))

  (define (sexp->string-indent sexp indent)
    (cond
     ((sexp-atom? sexp)
      (atom-value sexp))

     ((sexp-bytes? sexp)
      (string-append "|" (base64-encode (bytes-value sexp)) "|"))

     ((sexp-list? sexp)
      (let ((items (list-items sexp)))
        (cond
         ((null? items)
          "()")

         ;; Special case: (atom ...) - one line if short
         ((sexp-atom? (car items))
          (let* ((one-line (string-append "("
                                         (atom-value (car items))
                                         " "
                                         (string-join (map sexp->string (cdr items)) " ")
                                         ")")))
            (if (< (string-length one-line) 60)
                one-line
                ;; Multi-line
                (let ((new-indent (string-append indent "  ")))
                  (string-append "("
                                (atom-value (car items))
                                "\n"
                                (string-join
                                 (map (lambda (x)
                                        (string-append new-indent
                                                      (sexp->string-indent x new-indent)))
                                      (cdr items))
                                 "\n")
                                ")")))))

         ;; Generic list
         (else
          (let ((new-indent (string-append indent "  ")))
            (string-append "(\n"
                          (string-join
                           (map (lambda (x)
                                  (string-append new-indent
                                                (sexp->string-indent x new-indent)))
                                items)
                           "\n")
                          "\n"
                          indent
                          ")"))))))))

  ;;; Helpers

  (define (find-tag tag sexp)
    "Find a tagged item in a list: (tag ...) -> Some (tag ...) | None"
    (and (sexp-list? sexp)
         (let ((items (list-items sexp)))
           (find (lambda (item)
                   (and (sexp-list? item)
                        (let ((inner (list-items item)))
                          (and (not (null? inner))
                               (sexp-atom? (car inner))
                               (string=? (atom-value (car inner)) tag)))))
                 items))))

  (define (get-tag-value tag sexp)
    "Extract value after tag: (tag value ...) -> Some value | None"
    (let ((tagged (find-tag tag sexp)))
      (and tagged
           (let ((items (list-items tagged)))
             (and (>= (length items) 2)
                  (cadr items))))))

) ;; end library
