;;; SRFI-69 Hash Table Compatibility Library
;;; Library of Cyberspace - Chez Port
;;;
;;; Maps Chicken's SRFI-69 hash table API to R6RS hashtables.
;;;
;;; SRFI-69: make-hash-table, hash-table-ref, hash-table-set!, etc.
;;; R6RS:    make-hashtable, hashtable-ref, hashtable-set!, etc.
;;;
;;; Used by: os, catalog, gossip, vault, audit -- basically everything.

(library (cyberspace chicken-compatibility hashtable)
  (export
    make-hash-table
    hash-table?
    hash-table-ref
    hash-table-ref/default
    hash-table-set!
    hash-table-delete!
    hash-table-exists?
    hash-table-keys
    hash-table-values
    hash-table-walk
    hash-table-fold
    hash-table-size
    hash-table->alist
    alist->hash-table)

  (import (rnrs)
          (only (chezscheme) void))

  ;; ============================================================
  ;; Constructor
  ;;
  ;; SRFI-69: (make-hash-table)
  ;;          (make-hash-table equal?)
  ;;          (make-hash-table string=?)
  ;; R6RS:   (make-hashtable hash-fn equiv? size)
  ;; ============================================================

  (define (make-hash-table . rest)
    "Create a hash table. Optional comparator (default: equal?)."
    (let ((equiv? (if (null? rest) equal? (car rest))))
      (cond
        ((eq? equiv? eq?)
          (make-eq-hashtable))
        ((eq? equiv? eqv?)
          (make-eqv-hashtable))
        ((eq? equiv? string=?)
          (make-hashtable string-hash string=?))
        ((eq? equiv? equal?)
          (make-hashtable equal-hash equal?))
        (else
          ;; Custom comparator -- use equal-hash as default
          (make-hashtable equal-hash equiv?)))))

  (define (hash-table? x)
    (hashtable? x))

  ;; ============================================================
  ;; Lookup
  ;; ============================================================

  (define (hash-table-ref ht key . rest)
    "Look up key.  Optional failure thunk (default: error)."
    (let ((found (hashtable-ref ht key (void))))
      (if (eq? found (void))
          (if (null? rest)
              (error 'hash-table-ref "Key not found" key)
              ((car rest)))  ; call failure thunk
          found)))

  (define (hash-table-ref/default ht key default)
    "Look up key with default value."
    (hashtable-ref ht key default))

  ;; ============================================================
  ;; Mutation
  ;; ============================================================

  (define (hash-table-set! ht key value)
    (hashtable-set! ht key value))

  (define (hash-table-delete! ht key)
    (hashtable-delete! ht key))

  (define (hash-table-exists? ht key)
    (hashtable-contains? ht key))

  ;; ============================================================
  ;; Iteration
  ;; ============================================================

  (define (hash-table-keys ht)
    "Return list of keys."
    (vector->list (hashtable-keys ht)))

  (define (hash-table-values ht)
    "Return list of values."
    (let-values (((keys vals) (hashtable-entries ht)))
      (vector->list vals)))

  (define (hash-table-walk ht proc)
    "Call (proc key value) for each entry."
    (let-values (((keys vals) (hashtable-entries ht)))
      (do ((i 0 (+ i 1)))
          ((= i (vector-length keys)))
        (proc (vector-ref keys i) (vector-ref vals i)))))

  (define (hash-table-fold ht f init)
    "Fold over hash table entries."
    (let-values (((keys vals) (hashtable-entries ht)))
      (let loop ((i 0) (acc init))
        (if (= i (vector-length keys))
            acc
            (loop (+ i 1)
                  (f (vector-ref keys i) (vector-ref vals i) acc))))))

  (define (hash-table-size ht)
    (hashtable-size ht))

  ;; ============================================================
  ;; Conversion
  ;; ============================================================

  (define (hash-table->alist ht)
    "Convert hash table to association list."
    (let-values (((keys vals) (hashtable-entries ht)))
      (let loop ((i 0) (acc '()))
        (if (= i (vector-length keys))
            (reverse acc)
            (loop (+ i 1)
                  (cons (cons (vector-ref keys i) (vector-ref vals i)) acc))))))

  (define (alist->hash-table alist . rest)
    "Create hash table from association list."
    (let ((ht (apply make-hash-table rest)))
      (for-each (lambda (pair)
                  (hash-table-set! ht (car pair) (cdr pair)))
                alist)
      ht))

) ;; end library
