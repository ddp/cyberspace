;;; lazy-chunks.sls - Lazy Merkle Chunk Loading for Huge Objects
;;; Library of Cyberspace - Chez Port
;;;
;;; For very large texts (multi-megabyte files), we don't want to load
;;; the entire content into memory. Instead, we store the text as a
;;; sequence of content-addressed chunks and load them on demand.
;;;
;;; See Memo-058 (Text Objects) for context.
;;;
;;; Ported from Chicken's lazy-chunks.scm.
;;; Changes: module -> library, SRFI-9 -> R6RS records (mutable cache/lru),
;;;          srfi-69 -> hash-table compat, bitwise -> rnrs arithmetic,
;;;          quotient -> div, remove -> remp.

(library (cyberspace lazy-chunks)
  (export
    ;; Construction
    lazy-text-new
    lazy-text-from-string
    lazy-text-from-file
    lazy-text-from-manifest

    ;; Query
    lazy-text-length
    lazy-text-char-at
    lazy-text-chunk-count
    lazy-text-loaded-count

    ;; Extraction
    lazy-text-substring
    lazy-text-line-at

    ;; Manifest
    lazy-text-manifest
    lazy-text-manifest-hash

    ;; Cache control
    lazy-text-preload!
    lazy-text-evict!
    lazy-text-cache-stats

    ;; Predicates
    lazy-text?)

  (import (rnrs)
          (only (chezscheme) format)
          (cyberspace chicken-compatibility hash-table))

  ;; ============================================================
  ;; Configuration
  ;; ============================================================

  (define *chunk-size* 65536)        ; 64KB chunks
  (define *cache-limit* 16)          ; Max chunks in memory
  (define *hash-function* #f)        ; Set by vault integration

  ;; ============================================================
  ;; Chunk Structure
  ;; ============================================================

  (define-record-type <chunk-ref>
    (fields (immutable hash chunk-ref-hash)
            (immutable offset chunk-ref-offset)
            (immutable length chunk-ref-length)))

  (define (make-chunk-ref hash offset length)
    (make-<chunk-ref> hash offset length))

  (define (chunk-ref? x) (<chunk-ref>? x))

  (define-record-type <lazy-text>
    (fields (immutable length lazy-text-length)
            (immutable chunk-size lt-chunk-size)
            (immutable chunks lt-chunks)
            (mutable cache lt-cache lt-cache-set!)
            (mutable lru lt-lru lt-lru-set!)))

  (define (make-lazy-text length chunk-size chunks cache lru)
    (make-<lazy-text> length chunk-size chunks cache lru))

  (define (lazy-text? x) (<lazy-text>? x))

  ;; ============================================================
  ;; Hashing (placeholder - vault.scm provides real implementation)
  ;; ============================================================

  (define (compute-hash data)
    (if *hash-function*
        (*hash-function* data)
        ;; Simple placeholder hash for testing
        (let ((h 0))
          (let loop ((i 0))
            (if (>= i (string-length data))
                (number->string h 16)
                (begin
                  (set! h (bitwise-xor (bitwise-arithmetic-shift h 5)
                                       (char->integer (string-ref data i))))
                  (loop (+ i 1))))))))

  ;; ============================================================
  ;; Chunk Storage (placeholder - vault.scm provides real storage)
  ;; ============================================================

  (define *chunk-store* (make-hash-table string=?))

  (define store-chunk!
    (lambda (hash data)
      (hash-table-set! *chunk-store* hash data)))

  (define fetch-chunk
    (lambda (hash)
      (hash-table-ref/default *chunk-store* hash #f)))

  ;; ============================================================
  ;; Construction
  ;; ============================================================

  (define (lazy-text-new)
    (make-lazy-text 0 *chunk-size* '#() (make-hash-table string=?) '()))

  (define (lazy-text-from-string str)
    (let* ((len (string-length str))
           (num-chunks (div (+ len *chunk-size* -1) *chunk-size*))
           (chunks (make-vector num-chunks)))
      (let loop ((i 0) (offset 0))
        (when (< i num-chunks)
          (let* ((chunk-len (min *chunk-size* (- len offset)))
                 (data (substring str offset (+ offset chunk-len)))
                 (hash (compute-hash data)))
            (store-chunk! hash data)
            (vector-set! chunks i (make-chunk-ref hash offset chunk-len))
            (loop (+ i 1) (+ offset chunk-len)))))
      (make-lazy-text len *chunk-size* chunks
                      (make-hash-table string=?) '())))

  (define (lazy-text-from-file filename)
    (if (file-exists? filename)
        (lazy-text-from-string
         (with-input-from-file filename
           (lambda () (get-string-all (current-input-port)))))
        (lazy-text-new)))

  (define (lazy-text-from-manifest manifest-data)
    ;; manifest-data: ((total-length . n) (chunk-size . s) (chunks . ((hash len) ...)))
    (let* ((total-len (cdr (assq 'total-length manifest-data)))
           (chunk-size (cdr (assq 'chunk-size manifest-data)))
           (chunk-list (cdr (assq 'chunks manifest-data)))
           (chunks (list->vector
                    (let loop ((refs chunk-list) (offset 0) (result '()))
                      (if (null? refs)
                          (reverse result)
                          (let ((ref (car refs)))
                            (loop (cdr refs)
                                  (+ offset (cadr ref))
                                  (cons (make-chunk-ref (car ref) offset (cadr ref))
                                        result))))))))
      (make-lazy-text total-len chunk-size chunks
                      (make-hash-table string=?) '())))

  ;; ============================================================
  ;; Query
  ;; ============================================================

  (define (lazy-text-chunk-count lt)
    (vector-length (lt-chunks lt)))

  (define (lazy-text-loaded-count lt)
    (hash-table-size (lt-cache lt)))

  (define (position->chunk-index lt pos)
    (div pos (lt-chunk-size lt)))

  (define (load-chunk! lt idx)
    (let* ((chunks (lt-chunks lt))
           (ref (vector-ref chunks idx))
           (hash (chunk-ref-hash ref))
           (cache (lt-cache lt)))

      (unless (hash-table-exists? cache hash)
        ;; Evict oldest if at limit
        (when (>= (hash-table-size cache) *cache-limit*)
          (let ((oldest (car (reverse (lt-lru lt)))))
            (hash-table-delete! cache oldest)
            (lt-lru-set! lt (reverse (cdr (reverse (lt-lru lt)))))))

        ;; Load chunk
        (let ((data (fetch-chunk hash)))
          (when data
            (hash-table-set! cache hash data)
            (lt-lru-set! lt (cons hash (lt-lru lt))))))

      ;; Update LRU (move to front)
      (lt-lru-set! lt (cons hash (remp (lambda (h) (string=? h hash))
                                       (lt-lru lt))))

      (hash-table-ref/default cache hash #f)))

  (define (lazy-text-char-at lt pos)
    (if (or (< pos 0) (>= pos (lazy-text-length lt)))
        #f
        (let* ((idx (position->chunk-index lt pos))
               (ref (vector-ref (lt-chunks lt) idx))
               (data (load-chunk! lt idx)))
          (if data
              (string-ref data (- pos (chunk-ref-offset ref)))
              #f))))

  ;; ============================================================
  ;; Extraction
  ;; ============================================================

  (define (lazy-text-substring lt start len)
    (if (<= len 0)
        ""
        (let ((end (min (+ start len) (lazy-text-length lt))))
          (let loop ((pos start) (result '()))
            (if (>= pos end)
                (apply string-append (reverse result))
                (let* ((idx (position->chunk-index lt pos))
                       (ref (vector-ref (lt-chunks lt) idx))
                       (data (load-chunk! lt idx))
                       (chunk-start (chunk-ref-offset ref))
                       (rel-start (- pos chunk-start))
                       (rel-end (min (chunk-ref-length ref) (- end chunk-start)))
                       (chunk (if data
                                 (substring data rel-start rel-end)
                                 "")))
                  (loop (+ chunk-start rel-end)
                        (cons chunk result))))))))

  (define (lazy-text-line-at lt line-num)
    ;; Get specific line (0-indexed). Scans to find line boundaries.
    (let ((len (lazy-text-length lt)))
      (let loop ((pos 0) (line 0) (line-start 0))
        (cond
         ((>= pos len)
          (if (= line line-num)
              (lazy-text-substring lt line-start (- pos line-start))
              #f))
         ((char=? (lazy-text-char-at lt pos) #\newline)
          (if (= line line-num)
              (lazy-text-substring lt line-start (- pos line-start))
              (loop (+ pos 1) (+ line 1) (+ pos 1))))
         (else
          (loop (+ pos 1) line line-start))))))

  ;; ============================================================
  ;; Manifest
  ;; ============================================================

  (define (lazy-text-manifest lt)
    `((total-length . ,(lazy-text-length lt))
      (chunk-size . ,(lt-chunk-size lt))
      (chunks . ,(map (lambda (ref)
                        (list (chunk-ref-hash ref)
                              (chunk-ref-length ref)))
                      (vector->list (lt-chunks lt))))))

  (define (lazy-text-manifest-hash lt)
    (compute-hash (format #f "~a" (lazy-text-manifest lt))))

  ;; ============================================================
  ;; Cache Control
  ;; ============================================================

  (define (lazy-text-preload! lt start-chunk end-chunk)
    (let ((max-idx (- (vector-length (lt-chunks lt)) 1)))
      (let loop ((i (max 0 start-chunk)))
        (when (<= i (min max-idx end-chunk))
          (load-chunk! lt i)
          (loop (+ i 1))))))

  (define (lazy-text-evict! lt)
    (lt-cache-set! lt (make-hash-table string=?))
    (lt-lru-set! lt '()))

  (define (lazy-text-cache-stats lt)
    `((loaded . ,(hash-table-size (lt-cache lt)))
      (total . ,(vector-length (lt-chunks lt)))
      (limit . ,*cache-limit*)
      (chunk-size . ,(lt-chunk-size lt))))

  ;; ============================================================
  ;; Vault Integration Hooks
  ;; ============================================================

  (define (set-chunk-hash-function! fn)
    (set! *hash-function* fn))

  (define (set-chunk-store-functions! store-fn fetch-fn)
    (set! store-chunk! store-fn)
    (set! fetch-chunk fetch-fn))

) ;; end library
