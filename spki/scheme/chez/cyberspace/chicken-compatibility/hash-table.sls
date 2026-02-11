;;; SRFI-69 Hash Table Compatibility Library
;;; Library of Cyberspace - Chez Port
;;;
;;; Maps Chicken's SRFI-69 hash table API onto Chez Scheme's
;;; native hashtable operations.
;;;
;;; SRFI-69 defaults to equal? comparison; Chez requires explicit
;;; hash function and comparator.  We use equal-hash + equal?.
;;;
;;; Used by: os (session stats, cleanup hooks), and anything
;;;          that used srfi-69 in the Chicken codebase.

(library (cyberspace chicken-compatibility hash-table)
  (export
    make-hash-table
    hash-table-set!
    hash-table-ref
    hash-table-ref/default
    hash-table-keys
    hash-table-values
    hash-table-size
    hash-table-map
    hash-table-walk
    hash-table-delete!
    hash-table-exists?)

  (import (except (rnrs)
                  make-hashtable hashtable-set! hashtable-ref
                  hashtable-delete! hashtable-contains? hashtable-keys
                  hashtable-entries hashtable-size
                  equal-hash string-hash)
          (only (chezscheme)
                make-hashtable hashtable-set! hashtable-ref
                hashtable-delete! hashtable-contains? hashtable-keys
                hashtable-entries hashtable-size
                equal-hash string-hash))

  ;; SRFI-69 make-hash-table: optional comparator argument
  ;; (make-hash-table) → equal? comparison
  ;; (make-hash-table string=?) → string comparison with string-hash
  (define make-hash-table
    (case-lambda
      [() (make-hashtable equal-hash equal?)]
      [(compare)
       (cond
         [(eq? compare string=?) (make-hashtable string-hash string=?)]
         [else (make-hashtable equal-hash compare)])]))

  ;; Direct mapping
  (define hash-table-set! hashtable-set!)

  ;; SRFI-69 hash-table-ref with no default raises error on missing key
  (define hash-table-ref
    (let ((sentinel (list 'missing)))
      (lambda (ht key)
        (let ((v (hashtable-ref ht key sentinel)))
          (if (eq? v sentinel)
              (assertion-violation 'hash-table-ref
                "no value associated with key" key)
              v)))))

  ;; SRFI-69 hash-table-ref/default always takes a default
  (define hash-table-ref/default hashtable-ref)

  ;; Chez hashtable-keys returns a vector; SRFI-69 returns a list
  (define (hash-table-keys ht)
    (vector->list (hashtable-keys ht)))

  ;; Direct mapping
  (define hash-table-delete! hashtable-delete!)

  ;; Return all values as a list
  (define (hash-table-values ht)
    (let-values (((keys vals) (hashtable-entries ht)))
      (vector->list vals)))

  ;; Return number of entries
  (define hash-table-size hashtable-size)

  ;; Apply proc to each (key value) pair, return list of results
  (define (hash-table-map ht proc)
    (let-values (((keys vals) (hashtable-entries ht)))
      (let ((len (vector-length keys)))
        (let loop ((i 0) (acc '()))
          (if (= i len)
              (reverse acc)
              (loop (+ i 1)
                    (cons (proc (vector-ref keys i) (vector-ref vals i))
                          acc)))))))

  ;; Apply proc to each (key value) pair for side effects
  (define (hash-table-walk ht proc)
    (let-values (((keys vals) (hashtable-entries ht)))
      (let ((len (vector-length keys)))
        (do ((i 0 (+ i 1)))
            ((= i len))
          (proc (vector-ref keys i) (vector-ref vals i))))))

  ;; Name mapping: SRFI-69 hash-table-exists? -> Chez hashtable-contains?
  (define hash-table-exists? hashtable-contains?)

) ;; end library
