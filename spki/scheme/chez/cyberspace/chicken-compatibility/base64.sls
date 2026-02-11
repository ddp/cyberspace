;;; Base64 Encoding/Decoding
;;; Library of Cyberspace - Chez Port
;;;
;;; Replaces Chicken's base64 egg.
;;; Used by sexp.scm for SPKI certificate binary data (|base64...|).
;;;
;;; API: bytevector in, string out (encode); string in, bytevector out (decode).
;;; RFC 4648 compliant.

(library (cyberspace chicken-compatibility base64)
  (export base64-encode base64-decode)

  (import (rnrs)
          (only (chezscheme) open-output-string get-output-string))

  (define *encode-table*
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/")

  ;; Decode table: char -> 6-bit value (or #f for invalid)
  (define *decode-table*
    (let ((tbl (make-vector 128 #f)))
      (do ((i 0 (+ i 1)))
          ((= i 64) tbl)
        (vector-set! tbl (char->integer (string-ref *encode-table* i)) i))))

  ;; Encode a bytevector to base64 string.
  (define (base64-encode bv)
    (let* ((len (bytevector-length bv))
           (out (open-output-string)))
      (let loop ((i 0))
        (when (< i len)
          (let* ((b0 (bytevector-u8-ref bv i))
                 (b1 (if (< (+ i 1) len) (bytevector-u8-ref bv (+ i 1)) 0))
                 (b2 (if (< (+ i 2) len) (bytevector-u8-ref bv (+ i 2)) 0))
                 (remaining (- len i)))
            ;; Encode 3 bytes -> 4 base64 chars
            (put-char out (string-ref *encode-table* (bitwise-arithmetic-shift-right b0 2)))
            (put-char out (string-ref *encode-table*
                                      (bitwise-ior
                                       (bitwise-arithmetic-shift-left (bitwise-and b0 #x03) 4)
                                       (bitwise-arithmetic-shift-right b1 4))))
            (if (>= remaining 2)
                (put-char out (string-ref *encode-table*
                                          (bitwise-ior
                                           (bitwise-arithmetic-shift-left (bitwise-and b1 #x0F) 2)
                                           (bitwise-arithmetic-shift-right b2 6))))
                (put-char out #\=))
            (if (>= remaining 3)
                (put-char out (string-ref *encode-table* (bitwise-and b2 #x3F)))
                (put-char out #\=))
            (loop (+ i 3)))))
      (get-output-string out)))

  ;; Decode a base64 string to bytevector.
  (define (base64-decode str)
    (let* ((len (string-length str))
           (bytes '()))
      (let loop ((i 0))
        (when (< i len)
          (let skip-ws ((j i))
            (if (and (< j len)
                     (let ((c (string-ref str j)))
                       (or (char-whitespace? c) (char=? c #\=))))
                (skip-ws (+ j 1))
                (when (< j len)
                  (let* ((c0 (vector-ref *decode-table* (char->integer (string-ref str j))))
                         (c1 (and (< (+ j 1) len)
                                  (vector-ref *decode-table* (char->integer (string-ref str (+ j 1))))))
                         (c2 (and (< (+ j 2) len)
                                  (not (char=? (string-ref str (+ j 2)) #\=))
                                  (vector-ref *decode-table* (char->integer (string-ref str (+ j 2))))))
                         (c3 (and (< (+ j 3) len)
                                  (not (char=? (string-ref str (+ j 3)) #\=))
                                  (vector-ref *decode-table* (char->integer (string-ref str (+ j 3)))))))
                    (when (and c0 c1)
                      (set! bytes (cons (bitwise-ior
                                         (bitwise-arithmetic-shift-left c0 2)
                                         (bitwise-arithmetic-shift-right c1 4))
                                        bytes))
                      (when c2
                        (set! bytes (cons (bitwise-and
                                           #xFF
                                           (bitwise-ior
                                            (bitwise-arithmetic-shift-left (bitwise-and c1 #x0F) 4)
                                            (bitwise-arithmetic-shift-right c2 2)))
                                          bytes))
                        (when c3
                          (set! bytes (cons (bitwise-and
                                             #xFF
                                             (bitwise-ior
                                              (bitwise-arithmetic-shift-left (bitwise-and c2 #x03) 6)
                                              c3))
                                            bytes))))))
                  (loop (+ j 4)))))))
      ;; Convert accumulated bytes to bytevector
      (let* ((byte-list (reverse bytes))
             (bv (make-bytevector (length byte-list))))
        (let fill ((i 0) (rest byte-list))
          (if (null? rest)
              bv
              (begin
                (bytevector-u8-set! bv i (car rest))
                (fill (+ i 1) (cdr rest))))))))

) ;; end library
