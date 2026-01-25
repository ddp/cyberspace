;;; text.scm - Text Objects for Cyberspace
;;;
;;; Gap buffer implementation for efficient text editing.
;;; Shared substrate for Electric Pencil, TECO, and Schemacs.
;;;
;;; See Memo-0058 (Text Objects) for specification.
;;;
;;; Gap Buffer:
;;;   [text before cursor][    gap    ][text after cursor]
;;;
;;; Operations at cursor are O(1), moving gap is O(n).
;;; Line index provides O(1) line access.

(module text
  (;; Construction
   text-new
   text-from-string
   text-from-file

   ;; Query
   text-length
   text-cursor
   text-char-at
   text->string
   text-modified?
   text-line-count
   text-line-number
   text-column

   ;; Movement
   text-goto!
   text-move!
   text-beginning!
   text-end!
   text-line-start!
   text-line-end!

   ;; Editing
   text-insert!
   text-insert-char!
   text-delete!
   text-delete-backward!
   text-kill-line!
   text-set-char!
   text-clear-modified!

   ;; Line operations
   text-extract-line
   text-line-at
   text-substring
   text-next-line!
   text-prev-line!
   text-find-line-start
   text-find-line-end

   ;; Search
   text-search
   text-search-backward

   ;; Soup integration (stubs for now)
   text-seal
   text-unseal
   text-hash)

  (import scheme
          (chicken base)
          (chicken format)
          (chicken string)
          (chicken io)
          (chicken file))

;;; ============================================================
;;; Gap Buffer Data Structure
;;; ============================================================

(define-record-type <text>
  (make-text-internal vec gap-start gap-end size modified line-index)
  text?
  (vec text-vec set-text-vec!)
  (gap-start text-gap-start set-text-gap-start!)
  (gap-end text-gap-end set-text-gap-end!)
  (size text-size set-text-size!)
  (modified text-modified? set-text-modified!)
  (line-index text-line-index set-text-line-index!))  ; vector of line starts

(define *default-gap-size* 256)
(define *initial-size* 1024)

;;; ============================================================
;;; Line Index
;;; ============================================================
;;;
;;; The line index is a vector where entry i contains the position
;;; of the start of line i (0-indexed). This gives O(1) line access.
;;;
;;; The index is rebuilt on structural changes (insert/delete newlines).
;;; For most editing (within a line), no rebuild is needed.

(define (build-line-index t)
  "Build line index from buffer contents"
  (let* ((len (text-length-internal t))
         (lines (list 0)))  ; line 0 starts at position 0
    ;; Scan for newlines
    (do ((i 0 (+ i 1)))
        ((>= i len))
      (when (char=? (text-char-at-internal t i) #\newline)
        (set! lines (cons (+ i 1) lines))))
    ;; Convert to vector (reversed)
    (let ((vec (list->vector (reverse lines))))
      (set-text-line-index! t vec)
      vec)))

(define (text-line-count t)
  "Number of lines in text (1 if empty)"
  (let ((idx (text-line-index t)))
    (if idx
        (vector-length idx)
        (begin (build-line-index t)
               (vector-length (text-line-index t))))))

(define (invalidate-line-index! t)
  "Mark line index as needing rebuild"
  (set-text-line-index! t #f))

;;; ============================================================
;;; Internal helpers (don't account for gap)
;;; ============================================================

(define (text-length-internal t)
  "Number of characters (excluding gap)"
  (- (text-size t) (- (text-gap-end t) (text-gap-start t))))

(define (text-char-at-internal t pos)
  "Get character at position (internal, no bounds check)"
  (let ((gap-start (text-gap-start t))
        (gap-end (text-gap-end t))
        (vec (text-vec t)))
    (if (< pos gap-start)
        (vector-ref vec pos)
        (vector-ref vec (+ gap-end (- pos gap-start))))))

;;; ============================================================
;;; Construction
;;; ============================================================

(define (text-new #!optional (initial-size *initial-size*))
  "Create new empty text object"
  (let ((t (make-text-internal
            (make-vector initial-size #\space)
            0                    ; gap-start = cursor at beginning
            initial-size         ; gap-end = whole buffer is gap
            initial-size
            #f                   ; not modified
            #f)))                ; line index not built
    (build-line-index t)
    t))

(define (text-from-string str)
  "Create text object from string"
  (let* ((len (string-length str))
         (t (text-new (max *initial-size* (* 2 len)))))
    (text-insert! t str)
    (text-beginning! t)
    (set-text-modified! t #f)
    t))

(define (text-from-file path)
  "Create text object from file"
  (if (file-exists? path)
      (text-from-string (with-input-from-file path read-string))
      (text-new)))

;;; ============================================================
;;; Query
;;; ============================================================

(define (text-length t)
  "Number of characters in text"
  (text-length-internal t))

(define (text-cursor t)
  "Current cursor position (0-indexed)"
  (text-gap-start t))

(define (text-char-at t pos)
  "Get character at position"
  (if (and (>= pos 0) (< pos (text-length t)))
      (text-char-at-internal t pos)
      #f))

(define (text->string t)
  "Extract text contents as string"
  (let ((len (text-length t)))
    (let ((result (make-string len)))
      (do ((i 0 (+ i 1)))
          ((>= i len) result)
        (string-set! result i (text-char-at-internal t i))))))

(define (text-line-number t #!optional (pos (text-cursor t)))
  "Get line number (1-indexed) for position"
  (let ((idx (or (text-line-index t) (build-line-index t))))
    ;; Binary search for line containing pos
    (let ((n (vector-length idx)))
      (let loop ((lo 0) (hi (- n 1)))
        (if (>= lo hi)
            (+ lo 1)  ; 1-indexed
            (let ((mid (quotient (+ lo hi 1) 2)))
              (if (> (vector-ref idx mid) pos)
                  (loop lo (- mid 1))
                  (loop mid hi))))))))

(define (text-column t #!optional (pos (text-cursor t)))
  "Get column (1-indexed) for position"
  (let* ((line (text-line-number t pos))
         (idx (text-line-index t))
         (line-start (vector-ref idx (- line 1))))
    (+ 1 (- pos line-start))))

;;; ============================================================
;;; Movement
;;; ============================================================

(define (text-gap-size t)
  "Size of gap"
  (- (text-gap-end t) (text-gap-start t)))

(define (text-grow! t #!optional (min-gap *default-gap-size*))
  "Expand buffer to ensure gap >= min-gap"
  (when (< (text-gap-size t) min-gap)
    (let* ((old-vec (text-vec t))
           (old-size (text-size t))
           (new-size (* 2 (+ old-size min-gap)))
           (new-vec (make-vector new-size #\space))
           (gap-start (text-gap-start t))
           (gap-end (text-gap-end t))
           (after-gap (- old-size gap-end))
           (new-gap-end (- new-size after-gap)))
      ;; Copy before gap
      (do ((i 0 (+ i 1)))
          ((>= i gap-start))
        (vector-set! new-vec i (vector-ref old-vec i)))
      ;; Copy after gap to end of new buffer
      (do ((i 0 (+ i 1)))
          ((>= i after-gap))
        (vector-set! new-vec (+ new-gap-end i) (vector-ref old-vec (+ gap-end i))))
      (set-text-vec! t new-vec)
      (set-text-gap-end! t new-gap-end)
      (set-text-size! t new-size))))

(define (text-move-gap! t pos)
  "Move gap to position (0 to length)"
  (let ((gap-start (text-gap-start t))
        (gap-end (text-gap-end t))
        (vec (text-vec t)))
    (cond
     ((= pos gap-start) #t)             ; already there
     ((< pos gap-start)
      ;; Move gap left: shift chars [pos, gap-start) to right
      (let ((shift (- gap-start pos)))
        (do ((i (- gap-start 1) (- i 1))
             (j (- gap-end 1) (- j 1)))
            ((< i pos))
          (vector-set! vec j (vector-ref vec i)))
        (set-text-gap-start! t pos)
        (set-text-gap-end! t (- gap-end shift))))
     (else
      ;; Move gap right: shift chars [gap-end, gap-end + delta) to left
      (let ((delta (- pos gap-start)))
        (do ((i 0 (+ i 1)))
            ((>= i delta))
          (vector-set! vec (+ gap-start i) (vector-ref vec (+ gap-end i))))
        (set-text-gap-start! t pos)
        (set-text-gap-end! t (+ gap-end delta)))))))

(define (text-goto! t pos)
  "Move cursor to absolute position"
  (let ((len (text-length t)))
    (text-move-gap! t (max 0 (min pos len)))))

(define (text-move! t delta)
  "Move cursor by relative amount"
  (text-goto! t (+ (text-cursor t) delta)))

(define (text-beginning! t)
  "Move cursor to start of text"
  (text-goto! t 0))

(define (text-end! t)
  "Move cursor to end of text"
  (text-goto! t (text-length t)))

(define (text-line-start! t)
  "Move cursor to start of current line"
  (let* ((pos (text-cursor t))
         (line (text-line-number t pos))
         (idx (text-line-index t))
         (start (vector-ref idx (- line 1))))
    (text-goto! t start)))

(define (text-line-end! t)
  "Move cursor to end of current line"
  (let ((len (text-length t))
        (pos (text-cursor t)))
    (let loop ((p pos))
      (cond
       ((>= p len) (text-goto! t len))
       ((char=? (text-char-at-internal t p) #\newline)
        (text-goto! t p))
       (else (loop (+ p 1)))))))

;;; ============================================================
;;; Editing
;;; ============================================================

(define (text-insert-char! t char)
  "Insert single character at cursor"
  (text-grow! t 1)
  (let ((gap-start (text-gap-start t)))
    (vector-set! (text-vec t) gap-start char)
    (set-text-gap-start! t (+ gap-start 1)))
  (set-text-modified! t #t)
  ;; Invalidate line index if newline
  (when (char=? char #\newline)
    (invalidate-line-index! t)))

(define (text-insert! t str)
  "Insert string at cursor"
  (let ((has-newline #f))
    (for-each (lambda (c)
                (when (char=? c #\newline) (set! has-newline #t))
                (text-grow! t 1)
                (let ((gap-start (text-gap-start t)))
                  (vector-set! (text-vec t) gap-start c)
                  (set-text-gap-start! t (+ gap-start 1))))
              (string->list str))
    (set-text-modified! t #t)
    (when has-newline
      (invalidate-line-index! t))))

(define (text-delete! t n)
  "Delete n characters forward from cursor"
  (let ((gap-end (text-gap-end t))
        (size (text-size t)))
    (let ((actual (min n (- size gap-end))))
      ;; Check if deleting newlines
      (let ((has-newline #f))
        (do ((i 0 (+ i 1)))
            ((>= i actual))
          (when (char=? (vector-ref (text-vec t) (+ gap-end i)) #\newline)
            (set! has-newline #t)))
        (set-text-gap-end! t (+ gap-end actual))
        (set-text-modified! t #t)
        (when has-newline
          (invalidate-line-index! t))))))

(define (text-delete-backward! t #!optional (n 1))
  "Delete n characters backward from cursor"
  (let ((gap-start (text-gap-start t)))
    (let ((actual (min n gap-start)))
      ;; Check if deleting newlines
      (let ((has-newline #f))
        (do ((i 1 (+ i 1)))
            ((> i actual))
          (when (char=? (vector-ref (text-vec t) (- gap-start i)) #\newline)
            (set! has-newline #t)))
        (set-text-gap-start! t (- gap-start actual))
        (set-text-modified! t #t)
        (when has-newline
          (invalidate-line-index! t))))))

(define (text-kill-line! t)
  "Delete from cursor to end of line"
  (let ((len (text-length t))
        (pos (text-cursor t)))
    (let loop ((p pos))
      (cond
       ((>= p len)
        (text-delete! t (- p pos)))
       ((char=? (text-char-at-internal t p) #\newline)
        ;; Delete including newline
        (text-delete! t (+ 1 (- p pos))))
       (else (loop (+ p 1)))))))

(define (text-set-char! t pos char)
  "Set character at position (overwrite)"
  (let ((gap-start (text-gap-start t))
        (gap-end (text-gap-end t))
        (vec (text-vec t)))
    (when (and (>= pos 0) (< pos (text-length t)))
      (let ((old-char (text-char-at-internal t pos)))
        (if (< pos gap-start)
            (vector-set! vec pos char)
            (vector-set! vec (+ gap-end (- pos gap-start)) char))
        (set-text-modified! t #t)
        ;; Invalidate if newline status changed
        (when (or (char=? old-char #\newline) (char=? char #\newline))
          (invalidate-line-index! t))))))

(define (text-clear-modified! t)
  "Clear modified flag"
  (set-text-modified! t #f))

;;; ============================================================
;;; Line Operations
;;; ============================================================

(define (text-line-at t line-num)
  "Get position of start of line-num (1-indexed)"
  (let ((idx (or (text-line-index t) (build-line-index t))))
    (if (and (>= line-num 1) (<= line-num (vector-length idx)))
        (vector-ref idx (- line-num 1))
        #f)))

(define (text-extract-line t #!optional (pos (text-cursor t)))
  "Extract line containing pos as string"
  (let* ((len (text-length t))
         (line (text-line-number t pos))
         (start (text-line-at t line)))
    (if start
        (let loop ((end start))
          (cond
           ((>= end len)
            (let ((result (make-string (- end start))))
              (do ((i start (+ i 1)) (j 0 (+ j 1)))
                  ((>= i end) result)
                (string-set! result j (text-char-at-internal t i)))))
           ((char=? (text-char-at-internal t end) #\newline)
            (let ((result (make-string (- end start))))
              (do ((i start (+ i 1)) (j 0 (+ j 1)))
                  ((>= i end) result)
                (string-set! result j (text-char-at-internal t i)))))
           (else (loop (+ end 1)))))
        "")))

(define (text-substring t start end)
  "Extract substring from start to end"
  (let* ((len (text-length t))
         (actual-start (max 0 (min start len)))
         (actual-end (max actual-start (min end len)))
         (result-len (- actual-end actual-start)))
    (let ((result (make-string result-len)))
      (do ((i actual-start (+ i 1))
           (j 0 (+ j 1)))
          ((>= i actual-end) result)
        (string-set! result j (text-char-at-internal t i))))))

(define (text-next-line! t)
  "Move cursor to start of next line"
  (let ((len (text-length t))
        (pos (text-cursor t)))
    ;; Find next newline
    (let loop ((p pos))
      (cond
       ((>= p len) (text-goto! t len))  ; at end
       ((char=? (text-char-at-internal t p) #\newline)
        (text-goto! t (+ p 1)))         ; move past newline
       (else (loop (+ p 1)))))))

(define (text-prev-line! t)
  "Move cursor to start of previous line"
  (let ((pos (text-cursor t)))
    (if (<= pos 0)
        (text-goto! t 0)
        ;; First, move back past any newline we're at
        (let* ((p (if (and (> pos 0)
                           (char=? (text-char-at-internal t (- pos 1)) #\newline))
                      (- pos 1)
                      pos))
               ;; Find start of current line
               (current-start
                (let find-start ((q (- p 1)))
                  (cond
                   ((< q 0) 0)
                   ((char=? (text-char-at-internal t q) #\newline) (+ q 1))
                   (else (find-start (- q 1)))))))
          ;; Now find start of previous line
          (if (<= current-start 0)
              (text-goto! t 0)
              (let find-prev ((q (- current-start 2)))
                (cond
                 ((< q 0) (text-goto! t 0))
                 ((char=? (text-char-at-internal t q) #\newline)
                  (text-goto! t (+ q 1)))
                 (else (find-prev (- q 1))))))))))

(define (text-find-line-start t pos)
  "Find start position of line containing pos (doesn't move cursor)"
  (let loop ((p pos))
    (cond
     ((<= p 0) 0)
     ((char=? (text-char-at-internal t (- p 1)) #\newline) p)
     (else (loop (- p 1))))))

(define (text-find-line-end t pos)
  "Find end position of line containing pos (before newline, doesn't move cursor)"
  (let ((len (text-length t)))
    (let loop ((p pos))
      (cond
       ((>= p len) len)
       ((char=? (text-char-at-internal t p) #\newline) p)
       (else (loop (+ p 1)))))))

;;; ============================================================
;;; Search
;;; ============================================================

(define (text-search t pattern)
  "Find pattern forward from cursor. Returns position or #f"
  (let ((plen (string-length pattern))
        (len (text-length t))
        (start (+ (text-cursor t) 1)))
    (if (= plen 0)
        #f
        (let search ((pos start))
          (cond
           ((> pos (- len plen))
            ;; Wrap around to beginning
            (let wrap ((pos 0))
              (cond
               ((>= pos start) #f)
               ((string-match-at? t pos pattern plen) pos)
               (else (wrap (+ pos 1))))))
           ((string-match-at? t pos pattern plen) pos)
           (else (search (+ pos 1))))))))

(define (text-search-backward t pattern)
  "Find pattern backward from cursor. Returns position or #f"
  (let ((plen (string-length pattern))
        (len (text-length t))
        (start (- (text-cursor t) 1)))
    (if (= plen 0)
        #f
        (let search ((pos start))
          (cond
           ((< pos 0)
            ;; Wrap around to end
            (let wrap ((pos (- len plen)))
              (cond
               ((<= pos start) #f)
               ((string-match-at? t pos pattern plen) pos)
               (else (wrap (- pos 1))))))
           ((string-match-at? t pos pattern plen) pos)
           (else (search (- pos 1))))))))

(define (string-match-at? t pos pattern plen)
  "Check if pattern matches at position"
  (let ((len (text-length t)))
    (and (<= (+ pos plen) len)
         (let loop ((i 0))
           (cond
            ((>= i plen) #t)
            ((char=? (text-char-at-internal t (+ pos i)) (string-ref pattern i))
             (loop (+ i 1)))
            (else #f))))))

;;; ============================================================
;;; Soup Integration (stubs)
;;; ============================================================
;;;
;;; These will be implemented when merkle chunks are added.

(define (text-seal t)
  "Seal text to soup, return content hash"
  ;; TODO: implement with merkle chunks
  #f)

(define (text-unseal hash)
  "Load text from soup by hash"
  ;; TODO: implement with merkle chunks
  #f)

(define (text-hash t)
  "Get content address of text (requires seal)"
  ;; TODO: implement with merkle chunks
  #f)

) ; end module
