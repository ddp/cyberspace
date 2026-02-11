;;; Blob Compatibility Library
;;; Library of Cyberspace - Chez Port
;;;
;;; Chicken Scheme has two binary types: blob (opaque bytes) and
;;; u8vector (SRFI-4 numeric vector).  Chez has one: bytevector.
;;; This library maps Chicken's blob API onto Chez bytevectors.
;;;
;;; In Chicken, blobs and u8vectors share storage but have
;;; different types.  Here they're the same thing.
;;;
;;; Used by: crypto-ffi, cert, vault, audit, sexp, merkle, bloom,
;;;          keyring, security, gossip -- basically everything.

(library (cyberspace chicken-compatibility blob)
  (export
    ;; Core blob operations
    make-blob blob-size blob? blob=?
    ;; Blob <-> u8vector (identity in Chez)
    blob->u8vector u8vector->blob
    blob->u8vector/shared u8vector->blob/shared
    ;; Blob <-> string
    string->blob blob->string
    ;; Memory operations
    move-memory! blob-append
    ;; SRFI-4 u8vector operations (re-export for convenience)
    make-u8vector u8vector-ref u8vector-set! u8vector-length u8vector?
    u8vector->list list->u8vector
    ;; String helpers
    string->u8vector u8vector->string)

  (import (rnrs))

  ;; ============================================================
  ;; Core Blob Operations
  ;;
  ;; In Chez, blob = bytevector.  No conversion needed.
  ;; ============================================================

  (define make-blob make-bytevector)
  (define blob-size bytevector-length)
  (define blob? bytevector?)
  (define blob=? bytevector=?)

  ;; ============================================================
  ;; Blob <-> U8Vector
  ;;
  ;; In Chicken these are different types sharing storage.
  ;; In Chez they're identical -- these are identity functions.
  ;; The /shared variants in Chicken return a view of the same
  ;; memory.  Here everything is the same bytevector.
  ;; ============================================================

  (define (blob->u8vector b) b)       ; identity
  (define (u8vector->blob v) v)       ; identity
  (define (blob->u8vector/shared b) b) ; identity (was zero-copy in Chicken)
  (define (u8vector->blob/shared v) v) ; identity

  ;; ============================================================
  ;; Blob <-> String
  ;;
  ;; string->blob: UTF-8 encode (for text)
  ;; blob->string: Latin-1 decode (byte-for-byte, for binary data
  ;;               passed to base64 encoding)
  ;; ============================================================

  (define (string->blob s)
    "Convert string to bytevector (Latin-1, byte-for-byte).
     For text input (ASCII subset), equivalent to string->utf8."
    (let* ((len (string-length s))
           (bv (make-bytevector len)))
      (let loop ((i 0))
        (if (= i len) bv
            (begin
              (bytevector-u8-set! bv i (char->integer (string-ref s i)))
              (loop (+ i 1)))))))

  (define (blob->string b)
    "Convert bytevector to Latin-1 string (byte-for-byte).
     Required for base64 encoding of binary data (keys, signatures)."
    (let* ((len (bytevector-length b))
           (chars (let loop ((i 0) (acc '()))
                    (if (= i len) (reverse acc)
                        (loop (+ i 1)
                              (cons (integer->char (bytevector-u8-ref b i)) acc))))))
      (list->string chars)))

  ;; ============================================================
  ;; U8Vector Operations (SRFI-4 compatible names)
  ;;
  ;; Chez uses bytevector-* names.  Chicken uses u8vector-*.
  ;; Map SRFI-4 names to Chez bytevector operations.
  ;; ============================================================

  (define make-u8vector make-bytevector)
  (define u8vector-ref  bytevector-u8-ref)
  (define u8vector-set! bytevector-u8-set!)
  (define u8vector-length bytevector-length)
  (define u8vector? bytevector?)

  (define (u8vector->list v)
    (let ((len (bytevector-length v)))
      (let loop ((i (- len 1)) (acc '()))
        (if (< i 0)
            acc
            (loop (- i 1) (cons (bytevector-u8-ref v i) acc))))))

  (define (list->u8vector lst)
    (let* ((len (length lst))
           (v (make-bytevector len)))
      (let loop ((i 0) (rest lst))
        (if (null? rest)
            v
            (begin
              (bytevector-u8-set! v i (car rest))
              (loop (+ i 1) (cdr rest)))))))

  ;; ============================================================
  ;; String <-> U8Vector
  ;; ============================================================

  (define (string->u8vector s) (string->utf8 s))
  (define (u8vector->string v) (utf8->string v))

  ;; ============================================================
  ;; move-memory!
  ;;
  ;; Chicken: (move-memory! src dst len src-offset dst-offset)
  ;; Copies len bytes from src at src-offset to dst at dst-offset.
  ;; ============================================================

  (define (move-memory! src dst len src-offset dst-offset)
    (bytevector-copy! src src-offset dst dst-offset len))

  ;; ============================================================
  ;; blob-append
  ;;
  ;; Concatenate multiple blobs into a new one.
  ;; Used heavily in Merkle tree hashing and crypto operations.
  ;; ============================================================

  (define (blob-append . blobs)
    (if (null? blobs)
        (make-bytevector 0)
        (let* ((sizes (map bytevector-length blobs))
               (total (apply + sizes))
               (result (make-bytevector total)))
          (let loop ((rest blobs) (offset 0))
            (if (null? rest)
                result
                (let ((b (car rest))
                      (len (bytevector-length (car rest))))
                  (bytevector-copy! b 0 result offset len)
                  (loop (cdr rest) (+ offset len))))))))

) ;; end library
