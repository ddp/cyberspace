;;; SPKI Scheme - S-expression Parser
;;;
;;; S-expressions are the foundation of SPKI certificates.
;;; This module provides parsing, printing, and manipulation of s-expressions.
;;;
;;; Syntax:
;;;   (cert (issuer |base64...|) (subject |base64...|))
;;;
;;; Three types:
;;;   - Atom: identifier or keyword
;;;   - List: (...)
;;;   - Bytes: |base64| for binary data (keys, signatures)

(module sexp
  (;; Exports
   sexp-atom sexp-list sexp-bytes
   sexp-atom? sexp-list? sexp-bytes?
   atom-value list-items bytes-value
   parse-sexp
   sexp->string
   sexp->string-indent
   find-tag
   get-tag-value)

  (import scheme
          (chicken base)
          (chicken string)
          (chicken format)
          (chicken condition)
          (chicken blob)
          (chicken memory representation)
          srfi-1   ; list utilities
          srfi-4   ; u8vectors
          srfi-13  ; string utilities
          srfi-14) ; character sets

  ;; S-expression types (tagged)
  (define-record-type <sexp-atom>
    (make-atom value)
    sexp-atom?
    (value atom-value))

  (define-record-type <sexp-list>
    (make-sexp-list items)
    sexp-list?
    (items list-items))

  (define-record-type <sexp-bytes>
    (make-bytes value)
    sexp-bytes?
    (value bytes-value))

  ;; Constructors (exported as sexp-atom, sexp-list, sexp-bytes)
  (define (sexp-atom s) (make-atom s))
  (define (sexp-list xs) (make-sexp-list xs))
  (define (sexp-bytes b) (make-bytes b))

  ;;; Base64 encoding/decoding (simplified - will use library later)

  (define base64-alphabet
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/")

  (define (base64-encode bytes)
    ;; Simple base64 encoder for blobs
    ;; TODO: Replace with proper library (base64 egg)
    ;; For now, use hex encoding as a placeholder
    (if (blob? bytes)
        (let* ((vec (blob->u8vector/shared bytes))
               (len (u8vector-length vec)))
          (let loop ((i 0) (acc ""))
            (if (>= i len)
                acc
                (let ((byte (u8vector-ref vec i)))
                  (loop (+ i 1)
                        (string-append acc
                                       (if (< byte 16)
                                           (string-append "0" (number->string byte 16))
                                           (number->string byte 16))))))))
        ""))

  (define (base64-decode str)
    ;; Simple base64 decoder (currently decodes hex)
    ;; TODO: Replace with proper library (base64 egg)
    (let* ((len (string-length str))
           (blob (make-blob (quotient len 2)))
           (vec (blob->u8vector/shared blob)))
      (let loop ((i 0))
        (if (>= i (quotient len 2))
            blob
            (let ((hex-str (substring str (* i 2) (+ (* i 2) 2))))
              (u8vector-set! vec i (string->number hex-str 16))
              (loop (+ i 1)))))))

  ;;; Tokenizer

  (define-record-type token
    (make-token type value)
    token?
    (type token-type)
    (value token-value))

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
                    (error "Unterminated bytes literal"))
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
        (error "Unexpected end of input"))

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
        (error "Unexpected token" (car tokens)))))

    (cond
     ((null? tokens)
      (error "Empty input"))

     ((eq? (token-type (car tokens)) 'lparen)
      (let-values (((sexp rest) (parse-list '() (cdr tokens))))
        (if (null? rest)
            (sexp-list sexp)
            (error "Unexpected tokens after s-expression"))))

     ((eq? (token-type (car tokens)) 'atom)
      (if (null? (cdr tokens))
          (sexp-atom (token-value (car tokens)))
          (error "Unexpected tokens after s-expression")))

     ((eq? (token-type (car tokens)) 'bytes)
      (if (null? (cdr tokens))
          (sexp-bytes (token-value (car tokens)))
          (error "Unexpected tokens after s-expression")))

     ((eq? (token-type (car tokens)) 'rparen)
      (error "Unexpected closing paren"))

     (else
      (error "Unexpected token" (car tokens)))))

  ;;; Main parse function

  (define (parse-sexp str)
    (parse-tokens (tokenize str)))

  ;;; Pretty-printing

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

  ) ;; end module

;;;
;;; Example usage:
;;;
;;; (import sexp)
;;;
;;; ;; Parse
;;; (define cert (parse-sexp "(cert (issuer alice) (subject bob))"))
;;;
;;; ;; Query
;;; (define issuer (get-tag-value "issuer" cert))
;;; ;; => (sexp-atom "alice")
;;;
;;; ;; Print
;;; (sexp->string cert)
;;; ;; => "(cert (issuer alice) (subject bob))"
;;;
