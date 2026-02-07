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
    hash-table-delete!
    hash-table-exists?)

  (import (rnrs)
          (only (chezscheme)
                make-hashtable hashtable-set! hashtable-ref
                hashtable-delete! hashtable-contains? hashtable-keys
                equal-hash))

  ;; SRFI-69 make-hash-table defaults to equal? comparison
  (define (make-hash-table)
    (make-hashtable equal-hash equal?))

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

  ;; Name mapping: SRFI-69 hash-table-exists? -> Chez hashtable-contains?
  (define hash-table-exists? hashtable-contains?)

) ;; end library
