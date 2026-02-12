;;; rope.sls - Rope Data Structure for Large Texts
;;; Library of Cyberspace - Chez Port
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
;;;
;;; Ported from Chicken's rope.scm.
;;; Changes: module -> library, SRFI-9 -> R6RS records,
;;;          quotient -> div, custom integer-length -> bitwise-length,
;;;          eval -> Chez eval (for text interop).

(library (cyberspace rope)
  (export
    ;; Construction
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

  (import (rnrs)
          (only (chezscheme) eval))

  ;; ============================================================
  ;; Rope Structure
  ;; ============================================================

  (define *max-leaf-size* 1024)
  (define *min-leaf-size* 512)

  (define-record-type <rope-leaf>
    (fields (immutable str rope-leaf-string)))

  (define (make-rope-leaf str) (make-<rope-leaf> str))
  (define (rope-leaf? x) (<rope-leaf>? x))

  (define-record-type <rope-node>
    (fields (immutable left rope-node-left)
            (immutable right rope-node-right)
            (immutable weight rope-node-weight)
            (immutable len rope-node-length)))

  (define (make-rope-node left right weight len)
    (make-<rope-node> left right weight len))
  (define (rope-node? x) (<rope-node>? x))

  (define (rope? x) (or (rope-leaf? x) (rope-node? x)))

  ;; ============================================================
  ;; Construction
  ;; ============================================================

  (define (rope-new)
    (make-rope-leaf ""))

  (define (rope-from-string str)
    (let ((len (string-length str)))
      (if (<= len *max-leaf-size*)
          (make-rope-leaf str)
          (let* ((mid (div len 2))
                 (left (rope-from-string (substring str 0 mid)))
                 (right (rope-from-string (substring str mid len))))
            (make-rope-node left right mid len)))))

  (define (rope-from-text t)
    ;; Dynamic lookup to avoid circular dependency with text module
    (let ((str ((eval 'text->string) t)))
      (rope-from-string str)))

  ;; ============================================================
  ;; Query
  ;; ============================================================

  (define (rope-length r)
    (cond
     ((rope-leaf? r) (string-length (rope-leaf-string r)))
     ((rope-node? r) (rope-node-length r))
     (else 0)))

  (define (rope-char-at r pos)
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
    (cond
     ((rope-leaf? r) (rope-leaf-string r))
     ((rope-node? r)
      (string-append (rope->string (rope-node-left r))
                     (rope->string (rope-node-right r))))
     (else "")))

  (define (rope-depth r)
    (cond
     ((rope-leaf? r) 0)
     ((rope-node? r)
      (+ 1 (max (rope-depth (rope-node-left r))
                (rope-depth (rope-node-right r)))))
     (else 0)))

  ;; ============================================================
  ;; Core Operations
  ;; ============================================================

  (define (rope-concat r1 r2)
    (cond
     ((= (rope-length r1) 0) r2)
     ((= (rope-length r2) 0) r1)
     (else
      (let ((len1 (rope-length r1))
            (len2 (rope-length r2)))
        (if (and (rope-leaf? r1) (rope-leaf? r2)
                 (< (+ len1 len2) *max-leaf-size*))
            (make-rope-leaf (string-append (rope-leaf-string r1)
                                           (rope-leaf-string r2)))
            (make-rope-node r1 r2 len1 (+ len1 len2)))))))

  (define (rope-split r pos)
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
          (cons (rope-node-left r) (rope-node-right r)))
         ((< pos w)
          (let ((split-left (rope-split (rope-node-left r) pos)))
            (cons (car split-left)
                  (rope-concat (cdr split-left) (rope-node-right r)))))
         (else
          (let ((split-right (rope-split (rope-node-right r) (- pos w))))
            (cons (rope-concat (rope-node-left r) (car split-right))
                  (cdr split-right)))))))
     (else (cons (rope-new) (rope-new)))))

  (define (rope-insert r pos str)
    (if (= (string-length str) 0)
        r
        (let ((split (rope-split r pos))
              (new-rope (rope-from-string str)))
          (rope-concat (rope-concat (car split) new-rope) (cdr split)))))

  (define (rope-delete r start len)
    (if (<= len 0)
        r
        (let* ((split1 (rope-split r start))
               (split2 (rope-split (cdr split1) len)))
          (rope-concat (car split1) (cdr split2)))))

  (define (rope-substring r start end)
    (let* ((split1 (rope-split r start))
           (right-part (cdr split1))
           (split2 (rope-split right-part (- end start))))
      (rope->string (car split2))))

  ;; ============================================================
  ;; Conversion
  ;; ============================================================

  (define (rope->text r)
    ;; Dynamic lookup to avoid circular dependency with text module
    ((eval 'text-from-string) (rope->string r)))

  ;; ============================================================
  ;; Rebalancing (optional, for pathological cases)
  ;; ============================================================

  (define *max-depth-ratio* 2)

  (define (rope-needs-rebalance? r)
    (let ((len (rope-length r))
          (depth (rope-depth r)))
      (and (> len 0)
           (> depth (* *max-depth-ratio* (bitwise-length len))))))

  (define (rope-rebalance r)
    (if (rope-needs-rebalance? r)
        (rope-from-string (rope->string r))
        r))

) ;; end library
