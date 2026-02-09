;;; query.scm - Lazy Query Cursors for the Soup (Memo-027 Phase 1)
;;;
;;; Provides cursors, sorting, pagination, and aggregation over
;;; soup-query results. Phase 1: materialized cursors over the
;;; existing four-tuple model (type name size info).
;;;
;;; Phase 2 (deferred): indexes, cost optimization, federation, full-text.

(module query
  (;; Cursor creation
   soup-cursor
   cursor?
   cursor-next
   cursor-peek
   cursor-reset
   cursor-count
   cursor->list

   ;; Sorting
   order-by

   ;; Pagination
   cursor-limit
   cursor-offset
   cursor-page

   ;; Aggregation
   cursor-aggregate

   ;; Convenience
   soup-select)

  (import scheme
          (chicken base)
          (chicken format)
          (chicken sort)
          srfi-1    ; list utilities
          srfi-69   ; hash tables (for distinct)
          vault)

  ;; ============================================================
  ;; Cursor Type
  ;; ============================================================
  ;;
  ;; A cursor wraps a materialized result vector with a position
  ;; pointer. Results are four-tuples: (type name size info).

  (define-record-type <cursor>
    (make-cursor-internal results position)
    cursor?
    (results  cursor-results)
    (position cursor-position cursor-position-set!))

  (define (soup-cursor query)
    "Create cursor from s-expression query.
     Query syntax is the same as soup-query."
    (let ((results (soup-query query #t)))  ; #t = silent
      (make-cursor-internal (list->vector results) 0)))

  (define (cursor-next cursor)
    "Return next result and advance cursor. Returns #f at end."
    (let ((pos (cursor-position cursor))
          (vec (cursor-results cursor)))
      (if (>= pos (vector-length vec))
          #f
          (let ((result (vector-ref vec pos)))
            (cursor-position-set! cursor (+ pos 1))
            result))))

  (define (cursor-peek cursor)
    "Return next result without advancing. Returns #f at end."
    (let ((pos (cursor-position cursor))
          (vec (cursor-results cursor)))
      (if (>= pos (vector-length vec))
          #f
          (vector-ref vec pos))))

  (define (cursor-reset cursor)
    "Reset cursor to beginning."
    (cursor-position-set! cursor 0)
    cursor)

  (define (cursor-count cursor)
    "Return total number of results."
    (vector-length (cursor-results cursor)))

  (define (cursor->list cursor)
    "Materialize remaining results as a list."
    (let ((vec (cursor-results cursor))
          (pos (cursor-position cursor)))
      (let loop ((i pos) (acc '()))
        (if (>= i (vector-length vec))
            (reverse acc)
            (loop (+ i 1) (cons (vector-ref vec i) acc))))))

  ;; ============================================================
  ;; Sorting
  ;; ============================================================

  (define (field-accessor field)
    "Return accessor for a four-tuple field."
    (case field
      ((type)  car)
      ((name)  cadr)
      ((size)  caddr)
      (else (error "order-by: unknown field" field))))

  (define (order-by cursor field direction)
    "Sort cursor results by field (name/size/type), direction (asc/desc).
     Returns a new cursor."
    (let* ((accessor (field-accessor field))
           (items (vector->list (cursor-results cursor)))
           (cmp (case field
                  ((size)
                   (if (eq? direction 'asc)
                       (lambda (a b) (< (accessor a) (accessor b)))
                       (lambda (a b) (> (accessor a) (accessor b)))))
                  (else
                   (let ((str-accessor (lambda (x) (let ((v (accessor x)))
                                                     (if (symbol? v)
                                                         (symbol->string v)
                                                         (format "~a" v))))))
                     (if (eq? direction 'asc)
                         (lambda (a b) (string<? (str-accessor a) (str-accessor b)))
                         (lambda (a b) (string>? (str-accessor a) (str-accessor b))))))))
           (sorted (sort items cmp)))
      (make-cursor-internal (list->vector sorted) 0)))

  ;; ============================================================
  ;; Pagination
  ;; ============================================================

  (define (cursor-limit cursor n)
    "Return a new cursor with at most n results."
    (let* ((vec (cursor-results cursor))
           (len (min n (vector-length vec)))
           (new-vec (make-vector len)))
      (do ((i 0 (+ i 1)))
          ((= i len))
        (vector-set! new-vec i (vector-ref vec i)))
      (make-cursor-internal new-vec 0)))

  (define (cursor-offset cursor n)
    "Return a new cursor skipping the first n results."
    (let* ((vec (cursor-results cursor))
           (total (vector-length vec))
           (start (min n total))
           (new-len (- total start))
           (new-vec (make-vector new-len)))
      (do ((i 0 (+ i 1)))
          ((= i new-len))
        (vector-set! new-vec i (vector-ref vec (+ start i))))
      (make-cursor-internal new-vec 0)))

  (define (cursor-page cursor page-num page-size)
    "Return a new cursor for a specific page (1-based page numbers)."
    (let ((offset (* (- page-num 1) page-size)))
      (cursor-limit (cursor-offset cursor offset) page-size)))

  ;; ============================================================
  ;; Aggregation
  ;; ============================================================

  (define (cursor-aggregate cursor op)
    "Aggregate cursor results.
     op: count | distinct-types | total-size | distinct-names"
    (let ((vec (cursor-results cursor)))
      (case op
        ((count) (vector-length vec))

        ((total-size)
         (let loop ((i 0) (total 0))
           (if (>= i (vector-length vec))
               total
               (loop (+ i 1) (+ total (caddr (vector-ref vec i)))))))

        ((distinct-types)
         (let ((seen (make-hash-table eq?)))
           (do ((i 0 (+ i 1)))
               ((= i (vector-length vec))
                (hash-table-keys seen))
             (hash-table-set! seen (car (vector-ref vec i)) #t))))

        ((distinct-names)
         (let ((seen (make-hash-table string=?)))
           (do ((i 0 (+ i 1)))
               ((= i (vector-length vec))
                (hash-table-keys seen))
             (hash-table-set! seen (cadr (vector-ref vec i)) #t))))

        (else (error "cursor-aggregate: unknown op" op)))))

  ;; ============================================================
  ;; Convenience: soup-select
  ;; ============================================================

  (define (soup-select query #!key (sort-by #f) (limit #f) (offset #f) (aggregate #f))
    "One-call query + sort + paginate + aggregate.

     (soup-select '(type archives) sort-by: '(size desc) limit: 10)
     (soup-select '(type releases) aggregate: 'count)
     (soup-select '(signed) sort-by: '(name asc) limit: 5 offset: 10)"
    (let* ((c (soup-cursor query))
           ;; Sort if requested
           (c (if sort-by
                  (order-by c (car sort-by) (cadr sort-by))
                  c))
           ;; Offset if requested
           (c (if offset
                  (cursor-offset c offset)
                  c))
           ;; Limit if requested
           (c (if limit
                  (cursor-limit c limit)
                  c)))
      ;; Aggregate or return list
      (if aggregate
          (cursor-aggregate c aggregate)
          (cursor->list c))))

) ; end module query
