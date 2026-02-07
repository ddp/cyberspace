;;; Base64 Encoding/Decoding
;;; Library of Cyberspace - Chez Port
;;;
;;; Replaces Chicken's base64 egg.
;;; Used by sexp.scm for SPKI certificate binary data (|base64...|).
;;;
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

  (define (base64-encode str)
    "Encode a string to base64.  Input is raw bytes (Latin-1)."
    (let* ((len (string-length str))
           (out (open-output-string)))
      (let loop ((i 0))
        (when (< i len)
          (let* ((b0 (char->integer (string-ref str i)))
                 (b1 (if (< (+ i 1) len) (char->integer (string-ref str (+ i 1))) 0))
                 (b2 (if (< (+ i 2) len) (char->integer (string-ref str (+ i 2))) 0))
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

  (define (base64-decode str)
    "Decode a base64 string to raw bytes (Latin-1 string)."
    (let* ((len (string-length str))
           (out (open-output-string)))
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
                      (put-char out (integer->char
                                     (bitwise-ior
                                      (bitwise-arithmetic-shift-left c0 2)
                                      (bitwise-arithmetic-shift-right c1 4))))
                      (when c2
                        (put-char out (integer->char
                                       (bitwise-and
                                        #xFF
                                        (bitwise-ior
                                         (bitwise-arithmetic-shift-left (bitwise-and c1 #x0F) 4)
                                         (bitwise-arithmetic-shift-right c2 2)))))
                        (when c3
                          (put-char out (integer->char
                                         (bitwise-and
                                          #xFF
                                          (bitwise-ior
                                           (bitwise-arithmetic-shift-left (bitwise-and c2 #x03) 6)
                                           c3)))))))
                    (loop (+ j 4))))))))
      (get-output-string out)))

) ;; end library
