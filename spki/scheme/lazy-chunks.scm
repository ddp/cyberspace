;;; lazy-chunks.scm - Lazy Merkle Chunk Loading for Huge Objects
;;;
;;; For very large texts (multi-megabyte files), we don't want to load
;;; the entire content into memory. Instead, we store the text as a
;;; sequence of content-addressed chunks and load them on demand.
;;;
;;; Structure:
;;;   - Chunk: 64KB block with hash (content address)
;;;   - Chunk manifest: ordered list of chunk hashes + metadata
;;;   - Lazy text: manifest + cache of loaded chunks
;;;
;;;   Manifest:
;;;   +------------------------+
;;;   | total-length: 15728640 |  (15MB)
;;;   | chunk-size: 65536      |  (64KB)
;;;   | chunks:                |
;;;   |   0: (hash1 65536)     |
;;;   |   1: (hash2 65536)     |
;;;   |   ...                  |
;;;   |   239: (hash240 32768) |  (last chunk, partial)
;;;   +------------------------+
;;;
;;; Operations:
;;;   - Chunk lookup: O(1) via position / chunk-size
;;;   - Character access: O(1) with loaded chunk
;;;   - Chunk load: O(1) hash lookup in vault
;;;   - Memory: O(cache-size) not O(file-size)
;;;
;;; Integration:
;;;   - Works with vault.scm for content-addressed storage
;;;   - Chunks are shared across identical content (dedup)
;;;   - Manifest itself is content-addressed
;;;
;;; See Memo-0058 (Text Objects) for context.

(module lazy-chunks
  (;; Construction
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

  (import scheme
          (chicken base)
          (chicken string)
          (chicken io)
          (chicken file)
          (chicken bitwise)
          (chicken format)
          srfi-1      ; filter
          srfi-69)    ; hash-tables

;;; ============================================================
;;; Configuration
;;; ============================================================

(define *chunk-size* 65536)        ; 64KB chunks
(define *cache-limit* 16)          ; Max chunks in memory
(define *hash-function* #f)        ; Set by vault integration

;;; ============================================================
;;; Chunk Structure
;;; ============================================================

(define-record-type <chunk-ref>
  (make-chunk-ref hash offset length)
  chunk-ref?
  (hash chunk-ref-hash)            ; content hash (string)
  (offset chunk-ref-offset)        ; byte offset in original
  (length chunk-ref-length))       ; bytes in this chunk

(define-record-type <lazy-text>
  (make-lazy-text length chunk-size chunks cache lru)
  lazy-text?
  (length lazy-text-length)        ; total characters
  (chunk-size lt-chunk-size)       ; bytes per chunk
  (chunks lt-chunks)               ; vector of chunk-refs
  (cache lt-cache lt-cache-set!)   ; hash-table: hash -> string
  (lru lt-lru lt-lru-set!))        ; LRU list of loaded hashes

;;; ============================================================
;;; Hashing (placeholder - vault.scm provides real implementation)
;;; ============================================================

(define (compute-hash data)
  "Compute content hash. Placeholder using simple hash."
  (if *hash-function*
      (*hash-function* data)
      ;; Simple placeholder hash for testing
      (let ((h 0))
        (let loop ((i 0))
          (if (>= i (string-length data))
              (number->string h 16)
              (begin
                (set! h (bitwise-xor (arithmetic-shift h 5)
                                     (char->integer (string-ref data i))))
                (loop (+ i 1))))))))

;;; ============================================================
;;; Chunk Storage (placeholder - vault.scm provides real storage)
;;; ============================================================

(define *chunk-store* (make-hash-table string=?))

(define (store-chunk! hash data)
  "Store chunk by hash"
  (hash-table-set! *chunk-store* hash data))

(define (fetch-chunk hash)
  "Fetch chunk by hash"
  (hash-table-ref/default *chunk-store* hash #f))

;;; ============================================================
;;; Construction
;;; ============================================================

(define (lazy-text-new)
  "Create empty lazy text"
  (make-lazy-text 0 *chunk-size* '#() (make-hash-table string=?) '()))

(define (lazy-text-from-string str)
  "Create lazy text from string, chunking it"
  (let* ((len (string-length str))
         (num-chunks (quotient (+ len *chunk-size* -1) *chunk-size*))
         (chunks (make-vector num-chunks)))

    ;; Create and store chunks
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
  "Create lazy text from file"
  (if (file-exists? filename)
      (lazy-text-from-string
       (with-input-from-file filename read-string))
      (lazy-text-new)))

(define (lazy-text-from-manifest manifest-data)
  "Reconstruct lazy text from manifest.
   manifest-data: ((total-length . n) (chunk-size . s) (chunks . ((hash len) ...)))"
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

;;; ============================================================
;;; Query
;;; ============================================================

(define (lazy-text-chunk-count lt)
  "Number of chunks"
  (vector-length (lt-chunks lt)))

(define (lazy-text-loaded-count lt)
  "Number of currently loaded chunks"
  (hash-table-size (lt-cache lt)))

(define (position->chunk-index lt pos)
  "Get chunk index for position"
  (quotient pos (lt-chunk-size lt)))

(define (load-chunk! lt idx)
  "Load chunk into cache, evicting if necessary"
  (let* ((chunks (lt-chunks lt))
         (ref (vector-ref chunks idx))
         (hash (chunk-ref-hash ref))
         (cache (lt-cache lt)))

    (unless (hash-table-exists? cache hash)
      ;; Evict if at limit
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
    (lt-lru-set! lt (cons hash (remove (lambda (h) (string=? h hash))
                                       (lt-lru lt))))

    (hash-table-ref/default cache hash #f)))

(define (lazy-text-char-at lt pos)
  "Get character at position"
  (if (or (< pos 0) (>= pos (lazy-text-length lt)))
      #f
      (let* ((idx (position->chunk-index lt pos))
             (ref (vector-ref (lt-chunks lt) idx))
             (data (load-chunk! lt idx)))
        (if data
            (string-ref data (- pos (chunk-ref-offset ref)))
            #f))))

;;; ============================================================
;;; Extraction
;;; ============================================================

(define (lazy-text-substring lt start len)
  "Extract substring, loading chunks as needed"
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
                     (chunk-end (+ chunk-start (chunk-ref-length ref)))
                     (rel-start (- pos chunk-start))
                     (rel-end (min (chunk-ref-length ref) (- end chunk-start)))
                     (chunk (if data
                               (substring data rel-start rel-end)
                               "")))
                (loop (+ chunk-start rel-end)
                      (cons chunk result))))))))

(define (lazy-text-line-at lt line-num)
  "Get specific line (0-indexed). Scans to find line boundaries."
  ;; Simple implementation - scans forward
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

;;; ============================================================
;;; Manifest
;;; ============================================================

(define (lazy-text-manifest lt)
  "Generate manifest for storage/transmission"
  `((total-length . ,(lazy-text-length lt))
    (chunk-size . ,(lt-chunk-size lt))
    (chunks . ,(map (lambda (ref)
                      (list (chunk-ref-hash ref)
                            (chunk-ref-length ref)))
                    (vector->list (lt-chunks lt))))))

(define (lazy-text-manifest-hash lt)
  "Hash of manifest for content addressing"
  (compute-hash (format #f "~a" (lazy-text-manifest lt))))

;;; ============================================================
;;; Cache Control
;;; ============================================================

(define (lazy-text-preload! lt start-chunk end-chunk)
  "Preload range of chunks"
  (let ((max-idx (- (vector-length (lt-chunks lt)) 1)))
    (let loop ((i (max 0 start-chunk)))
      (when (<= i (min max-idx end-chunk))
        (load-chunk! lt i)
        (loop (+ i 1))))))

(define (lazy-text-evict! lt)
  "Evict all cached chunks"
  (lt-cache-set! lt (make-hash-table string=?))
  (lt-lru-set! lt '()))

(define (lazy-text-cache-stats lt)
  "Return cache statistics"
  `((loaded . ,(hash-table-size (lt-cache lt)))
    (total . ,(vector-length (lt-chunks lt)))
    (limit . ,*cache-limit*)
    (chunk-size . ,(lt-chunk-size lt))))

;;; ============================================================
;;; Vault Integration Hooks
;;; ============================================================

(define (set-chunk-hash-function! fn)
  "Set hash function from vault module"
  (set! *hash-function* fn))

(define (set-chunk-store-functions! store-fn fetch-fn)
  "Set storage functions from vault module"
  (set! store-chunk! store-fn)
  (set! fetch-chunk fetch-fn))

) ; end module
