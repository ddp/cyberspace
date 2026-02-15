;;; rope.scm - Rope Data Structure for Large Texts
;;;
;;; A rope is a binary tree of strings, enabling efficient operations
;;; on very large texts where gap buffers become expensive.
;;;
;;; Structure:
;;;   - Leaf: contains a string chunk (max 1KB)
;;;   - Node: contains left child, right child, and cached weight (left subtree length)
;;;
;;;            [weight=11]
;;;            /         \
;;;     [weight=5]    "world!"
;;;      /      \
;;;   "Hello"   " "
;;;
;;; Complexity:
;;;   - Index lookup: O(log n)
;;;   - Insert: O(log n)
;;;   - Delete: O(log n)
;;;   - Concatenate: O(1)
;;;   - Split: O(log n)
;;;
;;; See Memo-0058 (Text Objects) for context.

(module rope
  (;; Construction
   rope-new
   rope-from-string
   rope-from-text

   ;; Query
   rope-length
   rope-char-at
   rope->string
   rope-depth

   ;; Operations
   rope-concat
   rope-split
   rope-insert
   rope-delete
   rope-substring

   ;; Conversion
   rope->text

   ;; Predicates
   rope?
   rope-leaf?
   rope-node?)

  (import scheme
          (chicken base)
          (chicken string))

;;; ============================================================
;;; Rope Structure
;;; ============================================================

(define *max-leaf-size* 1024)  ; Max chars in a leaf
(define *min-leaf-size* 512)   ; Min chars before merging

;; Leaf node: just a string
(define-record-type <rope-leaf>
  (make-rope-leaf str)
  rope-leaf?
  (str rope-leaf-string))

;; Internal node: left, right, weight (length of left subtree)
(define-record-type <rope-node>
  (make-rope-node left right weight len)
  rope-node?
  (left rope-node-left)
  (right rope-node-right)
  (weight rope-node-weight)    ; chars in left subtree
  (len rope-node-length))      ; total chars (cached)

(define (rope? x)
  (or (rope-leaf? x) (rope-node? x)))

;;; ============================================================
;;; Construction
;;; ============================================================

(define (rope-new)
  "Create empty rope"
  (make-rope-leaf ""))

(define (rope-from-string str)
  "Create rope from string, splitting into balanced tree"
  (let ((len (string-length str)))
    (if (<= len *max-leaf-size*)
        (make-rope-leaf str)
        ;; Split in half and recurse
        (let* ((mid (quotient len 2))
               (left (rope-from-string (substring str 0 mid)))
               (right (rope-from-string (substring str mid len))))
          (make-rope-node left right mid len)))))

(define (rope-from-text t)
  "Create rope from text object"
  ;; Import dynamically to avoid circular dependency
  (let ((str ((eval 'text->string) t)))
    (rope-from-string str)))

;;; ============================================================
;;; Query
;;; ============================================================

(define (rope-length r)
  "Total characters in rope"
  (cond
   ((rope-leaf? r) (string-length (rope-leaf-string r)))
   ((rope-node? r) (rope-node-length r))
   (else 0)))

(define (rope-char-at r pos)
  "Get character at position"
  (cond
   ((rope-leaf? r)
    (let ((str (rope-leaf-string r)))
      (if (and (>= pos 0) (< pos (string-length str)))
          (string-ref str pos)
          #f)))
   ((rope-node? r)
    (let ((w (rope-node-weight r)))
      (if (< pos w)
          (rope-char-at (rope-node-left r) pos)
          (rope-char-at (rope-node-right r) (- pos w)))))
   (else #f)))

(define (rope->string r)
  "Convert rope to string"
  (cond
   ((rope-leaf? r) (rope-leaf-string r))
   ((rope-node? r)
    (string-append (rope->string (rope-node-left r))
                   (rope->string (rope-node-right r))))
   (else "")))

(define (rope-depth r)
  "Depth of rope tree (for balancing analysis)"
  (cond
   ((rope-leaf? r) 0)
   ((rope-node? r)
    (+ 1 (max (rope-depth (rope-node-left r))
              (rope-depth (rope-node-right r)))))
   (else 0)))

;;; ============================================================
;;; Core Operations
;;; ============================================================

(define (rope-concat r1 r2)
  "Concatenate two ropes - O(1)"
  (cond
   ((= (rope-length r1) 0) r2)
   ((= (rope-length r2) 0) r1)
   (else
    (let ((len1 (rope-length r1))
          (len2 (rope-length r2)))
      ;; Check if we should merge small leaves
      (if (and (rope-leaf? r1) (rope-leaf? r2)
               (< (+ len1 len2) *max-leaf-size*))
          (make-rope-leaf (string-append (rope-leaf-string r1)
                                         (rope-leaf-string r2)))
          (make-rope-node r1 r2 len1 (+ len1 len2)))))))

(define (rope-split r pos)
  "Split rope at position, returns (left . right)"
  (cond
   ((rope-leaf? r)
    (let ((str (rope-leaf-string r))
          (len (string-length (rope-leaf-string r))))
      (cond
       ((<= pos 0) (cons (rope-new) r))
       ((>= pos len) (cons r (rope-new)))
       (else
        (cons (make-rope-leaf (substring str 0 pos))
              (make-rope-leaf (substring str pos len)))))))
   ((rope-node? r)
    (let ((w (rope-node-weight r)))
      (cond
       ((<= pos 0)
        (cons (rope-new) r))
       ((>= pos (rope-length r))
        (cons r (rope-new)))
       ((= pos w)
        ;; Split exactly at boundary
        (cons (rope-node-left r) (rope-node-right r)))
       ((< pos w)
        ;; Split in left subtree
        (let ((split-left (rope-split (rope-node-left r) pos)))
          (cons (car split-left)
                (rope-concat (cdr split-left) (rope-node-right r)))))
       (else
        ;; Split in right subtree
        (let ((split-right (rope-split (rope-node-right r) (- pos w))))
          (cons (rope-concat (rope-node-left r) (car split-right))
                (cdr split-right)))))))
   (else (cons (rope-new) (rope-new)))))

(define (rope-insert r pos str)
  "Insert string at position"
  (if (= (string-length str) 0)
      r
      (let ((split (rope-split r pos))
            (new-rope (rope-from-string str)))
        (rope-concat (rope-concat (car split) new-rope) (cdr split)))))

(define (rope-delete r start len)
  "Delete len characters starting at start"
  (if (<= len 0)
      r
      (let* ((split1 (rope-split r start))
             (split2 (rope-split (cdr split1) len)))
        (rope-concat (car split1) (cdr split2)))))

(define (rope-substring r start end)
  "Extract substring from rope"
  (let* ((split1 (rope-split r start))
         (right-part (cdr split1))
         (split2 (rope-split right-part (- end start))))
    (rope->string (car split2))))

;;; ============================================================
;;; Conversion
;;; ============================================================

(define (rope->text r)
  "Convert rope back to text object"
  ;; Import dynamically to avoid circular dependency
  ((eval 'text-from-string) (rope->string r)))

;;; ============================================================
;;; Rebalancing (optional, for pathological cases)
;;; ============================================================

(define *max-depth-ratio* 2)  ; Rebalance if depth > log2(n) * ratio

(define (rope-needs-rebalance? r)
  "Check if rope is too unbalanced"
  (let ((len (rope-length r))
        (depth (rope-depth r)))
    (and (> len 0)
         (> depth (* *max-depth-ratio* (integer-length len))))))

(define (rope-rebalance r)
  "Rebalance rope by rebuilding from string"
  (if (rope-needs-rebalance? r)
      (rope-from-string (rope->string r))
      r))

(define (integer-length n)
  "Number of bits needed to represent n"
  (let loop ((n n) (bits 0))
    (if (<= n 0)
        bits
        (loop (quotient n 2) (+ bits 1)))))

) ; end module
