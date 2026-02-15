;;; piece-table.sls - Piece Table Data Structure for Collaborative Editing
;;; Library of Cyberspace - Chez Port
;;;
;;; A piece table represents text as a sequence of "pieces" that reference
;;; either the original file or an append-only "add buffer" of changes.
;;;
;;; Structure:
;;;   - Original buffer: read-only copy of original file
;;;   - Add buffer: append-only buffer of all insertions
;;;   - Piece table: list of (buffer, start, length) descriptors
;;;
;;; Example: Original "Hello World", insert "beautiful " at position 6:
;;;
;;;   Original: "Hello World"
;;;   Add:      "beautiful "
;;;   Pieces:   [(orig, 0, 6), (add, 0, 10), (orig, 6, 5)]
;;;   Result:   "Hello beautiful World"
;;;
;;; See Memo-0058 (Text Objects) for context.
;;;
;;; Ported from Chicken's piece-table.scm.
;;; Changes: module -> library, SRFI-9 -> R6RS records (mutable fields),
;;;          read-string -> get-string-all, Chicken sort -> Chez sort.

(library (cyberspace piece-table)
  (export
    ;; Construction
    pt-new
    pt-from-string
    pt-from-file

    ;; Query
    pt-length
    pt-char-at
    pt->string
    pt-piece-count

    ;; Operations
    pt-insert!
    pt-delete!
    pt-substring

    ;; History
    pt-checkpoint!
    pt-undo!
    pt-redo!
    pt-can-undo?
    pt-can-redo?

    ;; Collaboration hooks
    pt-get-operations
    pt-apply-operation
    pt-merge-operations)

  (import (rnrs)
          (only (chezscheme) sort))

  ;; ============================================================
  ;; Piece Structure
  ;; ============================================================

  (define-record-type <piece>
    (fields (immutable buffer piece-buffer)
            (immutable start piece-start)
            (immutable length piece-length)))

  (define (make-piece buffer start length)
    (make-<piece> buffer start length))
  (define (piece? x) (<piece>? x))

  (define-record-type <piece-table>
    (fields (immutable original pt-original)
            (mutable add pt-add pt-add-set!)
            (mutable pieces pt-pieces pt-pieces-set!)
            (mutable history pt-history pt-history-set!)
            (mutable future pt-future pt-future-set!)
            (mutable length pt-length pt-length-set!)))

  (define (make-piece-table original add pieces history future length)
    (make-<piece-table> original add pieces history future length))

  ;; ============================================================
  ;; Construction
  ;; ============================================================

  (define (pt-new)
    (make-piece-table "" "" '() '() '() 0))

  (define (pt-from-string str)
    (if (= (string-length str) 0)
        (pt-new)
        (make-piece-table
         str
         ""
         (list (make-piece 'original 0 (string-length str)))
         '()
         '()
         (string-length str))))

  (define (pt-from-file filename)
    (if (file-exists? filename)
        (pt-from-string
         (with-input-from-file filename
           (lambda () (get-string-all (current-input-port)))))
        (pt-new)))

  ;; ============================================================
  ;; Query
  ;; ============================================================

  (define (pt-piece-count pt)
    (length (pt-pieces pt)))

  (define (piece-text pt p)
    (let ((buf (if (eq? (piece-buffer p) 'original)
                   (pt-original pt)
                   (pt-add pt))))
      (substring buf (piece-start p) (+ (piece-start p) (piece-length p)))))

  (define (pt-char-at pt pos)
    (if (or (< pos 0) (>= pos (pt-length pt)))
        #f
        (let loop ((pieces (pt-pieces pt))
                   (offset 0))
          (if (null? pieces)
              #f
              (let* ((p (car pieces))
                     (plen (piece-length p)))
                (if (< pos (+ offset plen))
                    (let ((buf (if (eq? (piece-buffer p) 'original)
                                   (pt-original pt)
                                   (pt-add pt))))
                      (string-ref buf (+ (piece-start p) (- pos offset))))
                    (loop (cdr pieces) (+ offset plen))))))))

  (define (pt->string pt)
    (apply string-append
           (map (lambda (p) (piece-text pt p))
                (pt-pieces pt))))

  ;; ============================================================
  ;; Operations
  ;; ============================================================

  (define (find-piece-at pt pos)
    (let loop ((pieces (pt-pieces pt))
               (idx 0)
               (offset 0)
               (prefix '()))
      (if (null? pieces)
          (values idx 0 (reverse prefix))
          (let* ((p (car pieces))
                 (plen (piece-length p)))
            (if (< pos (+ offset plen))
                (values idx (- pos offset) (reverse prefix))
                (loop (cdr pieces)
                      (+ idx 1)
                      (+ offset plen)
                      (cons p prefix)))))))

  (define (pt-insert! pt pos str)
    (when (> (string-length str) 0)
      ;; Save state for undo
      (pt-history-set! pt (cons (pt-pieces pt) (pt-history pt)))
      (pt-future-set! pt '())

      ;; Append to add buffer
      (let ((add-start (string-length (pt-add pt))))
        (pt-add-set! pt (string-append (pt-add pt) str))

        ;; Create new piece for inserted text
        (let ((new-piece (make-piece 'add add-start (string-length str))))

          (if (null? (pt-pieces pt))
              ;; Empty table
              (pt-pieces-set! pt (list new-piece))
              ;; Find where to insert
              (let-values (((idx offset prefix) (find-piece-at pt pos)))
                (let ((pieces (pt-pieces pt)))
                  (if (>= idx (length pieces))
                      ;; Insert at end
                      (pt-pieces-set! pt (append pieces (list new-piece)))
                      ;; Split existing piece
                      (let* ((p (list-ref pieces idx))
                             (suffix (list-tail pieces (+ idx 1))))
                        (if (= offset 0)
                            ;; Insert before this piece
                            (pt-pieces-set! pt
                              (append prefix (list new-piece) (list p) suffix))
                            (if (= offset (piece-length p))
                                ;; Insert after this piece
                                (pt-pieces-set! pt
                                  (append prefix (list p new-piece) suffix))
                                ;; Split the piece
                                (let ((p1 (make-piece (piece-buffer p)
                                                      (piece-start p)
                                                      offset))
                                      (p2 (make-piece (piece-buffer p)
                                                      (+ (piece-start p) offset)
                                                      (- (piece-length p) offset))))
                                  (pt-pieces-set! pt
                                    (append prefix
                                            (list p1 new-piece p2)
                                            suffix))))))))))

          ;; Update length
          (pt-length-set! pt (+ (pt-length pt) (string-length str)))))))

  (define (pt-delete! pt start len)
    (when (and (> len 0) (> (pt-length pt) 0))
      ;; Save state for undo
      (pt-history-set! pt (cons (pt-pieces pt) (pt-history pt)))
      (pt-future-set! pt '())

      ;; Clamp range
      (let* ((actual-len (min len (- (pt-length pt) start)))
             (end (+ start actual-len)))

        ;; Rebuild piece list, skipping deleted range
        (let loop ((pieces (pt-pieces pt))
                   (offset 0)
                   (result '()))
          (if (null? pieces)
              (begin
                (pt-pieces-set! pt (reverse result))
                (pt-length-set! pt (- (pt-length pt) actual-len)))
              (let* ((p (car pieces))
                     (plen (piece-length p))
                     (piece-end (+ offset plen)))

                (cond
                 ;; Piece entirely before deletion
                 ((< piece-end start)
                  (loop (cdr pieces) piece-end (cons p result)))

                 ;; Piece entirely after deletion
                 ((>= offset end)
                  (loop (cdr pieces) piece-end (cons p result)))

                 ;; Piece entirely within deletion - skip it
                 ((and (>= offset start) (< piece-end end))
                  (loop (cdr pieces) piece-end result))

                 ;; Deletion starts in this piece
                 ((and (< offset start) (>= piece-end start))
                  (if (< piece-end end)
                      ;; Piece extends into deletion - truncate
                      (let ((new-p (make-piece (piece-buffer p)
                                               (piece-start p)
                                               (- start offset))))
                        (loop (cdr pieces) piece-end (cons new-p result)))
                      ;; Deletion entirely within piece - split
                      (let ((p1 (make-piece (piece-buffer p)
                                            (piece-start p)
                                            (- start offset)))
                            (p2 (make-piece (piece-buffer p)
                                            (+ (piece-start p) (- end offset))
                                            (- piece-end end))))
                        (loop (cdr pieces) piece-end
                              (if (> (piece-length p2) 0)
                                  (cons p2 (cons p1 result))
                                  (cons p1 result))))))

                 ;; Deletion ends in this piece
                 ((and (> offset start) (< offset end) (<= piece-end end))
                  (loop (cdr pieces) piece-end result))

                 ((and (< offset end) (> piece-end end))
                  ;; Trim beginning of piece
                  (let ((trim (- end offset)))
                    (let ((new-p (make-piece (piece-buffer p)
                                             (+ (piece-start p) trim)
                                             (- plen trim))))
                      (loop (cdr pieces) piece-end (cons new-p result)))))

                 (else
                  (loop (cdr pieces) piece-end (cons p result))))))))))

  (define (pt-substring pt start len)
    (let ((actual-len (min len (- (pt-length pt) start))))
      (if (<= actual-len 0)
          ""
          (let ((end (+ start actual-len)))
            (let loop ((pieces (pt-pieces pt))
                       (offset 0)
                       (result '()))
              (if (or (null? pieces) (>= offset end))
                  (apply string-append (reverse result))
                  (let* ((p (car pieces))
                         (plen (piece-length p))
                         (piece-end (+ offset plen)))
                    (cond
                     ((<= piece-end start)
                      (loop (cdr pieces) piece-end result))
                     ((>= offset end)
                      (apply string-append (reverse result)))
                     (else
                      (let* ((rel-start (max 0 (- start offset)))
                             (rel-end (min plen (- end offset)))
                             (buf (if (eq? (piece-buffer p) 'original)
                                      (pt-original pt)
                                      (pt-add pt)))
                             (chunk (substring buf
                                              (+ (piece-start p) rel-start)
                                              (+ (piece-start p) rel-end))))
                        (loop (cdr pieces) piece-end (cons chunk result))))))))))))

  ;; ============================================================
  ;; History (Undo/Redo)
  ;; ============================================================

  (define (pt-checkpoint! pt)
    (pt-history-set! pt (cons (pt-pieces pt) (pt-history pt)))
    (pt-future-set! pt '()))

  (define (pt-can-undo? pt)
    (not (null? (pt-history pt))))

  (define (pt-can-redo? pt)
    (not (null? (pt-future pt))))

  (define (pt-undo! pt)
    (when (pt-can-undo? pt)
      (pt-future-set! pt (cons (pt-pieces pt) (pt-future pt)))
      (pt-pieces-set! pt (car (pt-history pt)))
      (pt-history-set! pt (cdr (pt-history pt)))
      (pt-length-set! pt
        (apply + (map piece-length (pt-pieces pt))))))

  (define (pt-redo! pt)
    (when (pt-can-redo? pt)
      (pt-history-set! pt (cons (pt-pieces pt) (pt-history pt)))
      (pt-pieces-set! pt (car (pt-future pt)))
      (pt-future-set! pt (cdr (pt-future pt)))
      (pt-length-set! pt
        (apply + (map piece-length (pt-pieces pt))))))

  ;; ============================================================
  ;; Collaboration Hooks
  ;; ============================================================

  (define-record-type <pt-operation>
    (fields (immutable type pt-op-type)
            (immutable pos pt-op-pos)
            (immutable data pt-op-data)
            (immutable timestamp pt-op-timestamp)))

  (define (make-pt-operation type pos data timestamp)
    (make-<pt-operation> type pos data timestamp))

  (define *operation-log* '())
  (define *logical-clock* 0)

  (define (pt-get-operations)
    (let ((ops *operation-log*))
      (set! *operation-log* '())
      ops))

  (define (pt-apply-operation pt op)
    (case (pt-op-type op)
      ((insert)
       (pt-insert! pt (pt-op-pos op) (pt-op-data op)))
      ((delete)
       (pt-delete! pt (pt-op-pos op) (pt-op-data op)))))

  (define (pt-merge-operations ops1 ops2)
    ;; Chez sort: (sort predicate list) — swapped from Chicken
    (sort (lambda (a b)
            (< (pt-op-timestamp a) (pt-op-timestamp b)))
          (append ops1 ops2)))

) ;; end library
