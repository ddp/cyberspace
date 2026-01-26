;;; text.scm - Text objects for the soup
;;;
;;; A text object is the native representation of editable content.
;;; Gap buffer for editing, chunked merkle for storage.
;;;
;;; Both Electric Pencil and TECO use this - one representation,
;;; multiple interfaces. The buffer is the truth; editors are views.
;;;
;;; Copyright (c) 2026 ddp@eludom.net
;;; MIT License - see LICENSE file

(module text
  (;; Construction
   text-new
   text-from-string
   text-from-file

   ;; Query
   text-length
   text-cursor
   text-char-at
   text-substring
   text->string
   text-line-count
   text-line-at
   text-modified?

   ;; Movement
   text-goto!
   text-move!
   text-beginning!
   text-end!
   text-line-start!
   text-line-end!
   text-next-line!
   text-prev-line!

   ;; Editing
   text-insert!
   text-delete!
   text-delete-forward!
   text-kill-line!
   text-replace!

   ;; Search
   text-search
   text-search-backward

   ;; Provenance
   text-source-hash
   text-parent-hash

   ;; Soup integration
   text-seal
   text-unseal
   text-hash
   set-vault-path!
   content-exists?   ; check if hash exists in vault
   load-content      ; low-level: load by hash (any format)

   ;; For editors
   text-gap-buffer  ; expose internal for low-level access
   text-clear-modified!  ; mark as saved (for file operations)
   )

  (import scheme
          (chicken base)
          (chicken format)
          (chicken string)
          (chicken io)
          (chicken port)
          (chicken file)
          (chicken pathname)
          (chicken blob)
          (chicken bitwise)
          (chicken condition)
          srfi-4   ; u8vectors
          srfi-13
          crypto-ffi)

;;; ============================================================
;;; Gap Buffer - efficient editing data structure
;;; ============================================================
;;;
;;; [text before cursor][  gap  ][text after cursor]
;;;
;;; Insert at cursor = fill gap from left (O(1))
;;; Delete at cursor = grow gap (O(1))
;;; Move cursor = shift text across gap (O(n) for distance n)
;;;
;;; This is what Emacs uses. Good enough for 50 years.

(define-record-type <gap-buffer>
  (make-gap-buffer-raw vec gap-start gap-end size)
  gap-buffer?
  (vec gb-vec set-gb-vec!)
  (gap-start gb-gap-start set-gb-gap-start!)
  (gap-end gb-gap-end set-gb-gap-end!)
  (size gb-size set-gb-size!))

(define *default-gap* 256)
(define *initial-size* 1024)

(define (gap-buffer-new #!optional (size *initial-size*))
  "Create empty gap buffer"
  (make-gap-buffer-raw
   (make-vector size #\nul)
   0 size size))

(define (gap-buffer-length gb)
  "Characters in buffer (excluding gap)"
  (- (gb-size gb) (- (gb-gap-end gb) (gb-gap-start gb))))

(define (gap-buffer-cursor gb)
  "Cursor position"
  (gb-gap-start gb))

(define (gap-buffer-grow! gb min-gap)
  "Ensure gap >= min-gap"
  (when (< (- (gb-gap-end gb) (gb-gap-start gb)) min-gap)
    (let* ((old-vec (gb-vec gb))
           (old-size (gb-size gb))
           (new-size (* 2 (+ old-size min-gap)))
           (new-vec (make-vector new-size #\nul))
           (gap-start (gb-gap-start gb))
           (gap-end (gb-gap-end gb))
           (after-gap (- old-size gap-end))
           (new-gap-end (- new-size after-gap)))
      ;; Copy before gap
      (do ((i 0 (+ i 1))) ((>= i gap-start))
        (vector-set! new-vec i (vector-ref old-vec i)))
      ;; Copy after gap
      (do ((i 0 (+ i 1))) ((>= i after-gap))
        (vector-set! new-vec (+ new-gap-end i)
                     (vector-ref old-vec (+ gap-end i))))
      (set-gb-vec! gb new-vec)
      (set-gb-gap-end! gb new-gap-end)
      (set-gb-size! gb new-size))))

(define (gap-buffer-move-gap! gb pos)
  "Move gap to position"
  (let ((gap-start (gb-gap-start gb))
        (gap-end (gb-gap-end gb))
        (vec (gb-vec gb)))
    (cond
     ((= pos gap-start) #t)  ; already there
     ((< pos gap-start)
      ;; Move gap left: shift text right into gap
      (let ((shift (- gap-start pos)))
        (do ((i 0 (+ i 1))) ((>= i shift))
          (vector-set! vec (- gap-end 1 i)
                       (vector-ref vec (- gap-start 1 i))))
        (set-gb-gap-start! gb pos)
        (set-gb-gap-end! gb (- gap-end shift))))
     (else
      ;; Move gap right: shift text left into gap
      (let ((shift (- pos gap-start)))
        (do ((i 0 (+ i 1))) ((>= i shift))
          (vector-set! vec (+ gap-start i)
                       (vector-ref vec (+ gap-end i))))
        (set-gb-gap-start! gb pos)
        (set-gb-gap-end! gb (+ gap-end shift)))))))

(define (gap-buffer-insert! gb char)
  "Insert character at cursor"
  (gap-buffer-grow! gb 1)
  (vector-set! (gb-vec gb) (gb-gap-start gb) char)
  (set-gb-gap-start! gb (+ (gb-gap-start gb) 1)))

(define (gap-buffer-insert-string! gb str)
  "Insert string at cursor"
  (let ((len (string-length str)))
    (gap-buffer-grow! gb len)
    (do ((i 0 (+ i 1))) ((>= i len))
      (vector-set! (gb-vec gb) (+ (gb-gap-start gb) i)
                   (string-ref str i)))
    (set-gb-gap-start! gb (+ (gb-gap-start gb) len))))

(define (gap-buffer-delete! gb n)
  "Delete n characters after cursor"
  (let ((gap-end (gb-gap-end gb))
        (size (gb-size gb)))
    (set-gb-gap-end! gb (min size (+ gap-end n)))))

(define (gap-buffer-delete-backward! gb n)
  "Delete n characters before cursor"
  (let ((gap-start (gb-gap-start gb)))
    (set-gb-gap-start! gb (max 0 (- gap-start n)))))

(define (gap-buffer-char-at gb pos)
  "Character at position"
  (let ((gap-start (gb-gap-start gb))
        (gap-end (gb-gap-end gb)))
    (cond
     ((< pos gap-start)
      (vector-ref (gb-vec gb) pos))
     (else
      (vector-ref (gb-vec gb) (+ gap-end (- pos gap-start)))))))

(define (gap-buffer->string gb)
  "Extract buffer contents as string"
  (let* ((len (gap-buffer-length gb))
         (str (make-string len)))
    (do ((i 0 (+ i 1))) ((>= i len) str)
      (string-set! str i (gap-buffer-char-at gb i)))))

(define (string->gap-buffer str)
  "Create gap buffer from string"
  (let* ((len (string-length str))
         (size (max *initial-size* (* 2 len)))
         (gb (gap-buffer-new size)))
    (gap-buffer-insert-string! gb str)
    gb))

;;; ============================================================
;;; Text Object - the soup-native text type
;;; ============================================================

(define-record-type <text>
  (make-text-raw buffer modified source-hash parent-hash)
  text?
  (buffer text-buffer)
  (modified text-modified set-text-modified!)
  (source-hash text-source-hash set-text-source-hash!)  ; where it came from
  (parent-hash text-parent-hash set-text-parent-hash!)) ; previous version

(define (text-new)
  "Create empty text object"
  (make-text-raw (gap-buffer-new) #f #f #f))

(define (text-from-string str)
  "Create text from string"
  (make-text-raw (string->gap-buffer str) #f #f #f))

(define (text-from-file filename)
  "Load text from file (bootstrap only - files are not native)"
  (let ((content (with-input-from-file filename read-string)))
    (make-text-raw (string->gap-buffer content) #f #f #f)))

;; Query
(define (text-length t) (gap-buffer-length (text-buffer t)))
(define (text-cursor t) (gap-buffer-cursor (text-buffer t)))
(define (text-char-at t pos) (gap-buffer-char-at (text-buffer t) pos))
(define (text->string t) (gap-buffer->string (text-buffer t)))
(define (text-modified? t) (text-modified t))
(define (text-gap-buffer t) (text-buffer t))  ; for editors
(define (text-clear-modified! t) (set-text-modified! t #f))  ; for save operations

(define (text-substring t start end)
  "Extract substring"
  (let* ((len (text-length t))
         (s (max 0 (min start len)))
         (e (max s (min end len)))
         (result (make-string (- e s))))
    (do ((i s (+ i 1))) ((>= i e) result)
      (string-set! result (- i s) (text-char-at t i)))))

(define (text-line-count t)
  "Count lines"
  (let ((len (text-length t)))
    (let loop ((i 0) (count 1))
      (if (>= i len) count
          (loop (+ i 1)
                (if (char=? (text-char-at t i) #\newline)
                    (+ count 1) count))))))

(define (text-line-at t line-num)
  "Get line by number (0-indexed)"
  (let ((len (text-length t)))
    (let loop ((i 0) (line 0) (start 0))
      (cond
       ((>= i len)
        (if (= line line-num)
            (text-substring t start i)
            ""))
       ((char=? (text-char-at t i) #\newline)
        (if (= line line-num)
            (text-substring t start i)
            (loop (+ i 1) (+ line 1) (+ i 1))))
       (else (loop (+ i 1) line start))))))

;; Movement
(define (text-goto! t pos)
  "Move cursor to position"
  (gap-buffer-move-gap! (text-buffer t)
                        (max 0 (min pos (text-length t)))))

(define (text-move! t delta)
  "Move cursor by delta"
  (text-goto! t (+ (text-cursor t) delta)))

(define (text-beginning! t) (text-goto! t 0))
(define (text-end! t) (text-goto! t (text-length t)))

(define (text-line-start! t)
  "Move to start of current line"
  (let loop ((pos (text-cursor t)))
    (cond
     ((<= pos 0) (text-goto! t 0))
     ((char=? (text-char-at t (- pos 1)) #\newline)
      (text-goto! t pos))
     (else (loop (- pos 1))))))

(define (text-line-end! t)
  "Move to end of current line"
  (let ((len (text-length t)))
    (let loop ((pos (text-cursor t)))
      (cond
       ((>= pos len) (text-goto! t len))
       ((char=? (text-char-at t pos) #\newline)
        (text-goto! t pos))
       (else (loop (+ pos 1)))))))

(define (text-next-line! t)
  "Move to next line"
  (text-line-end! t)
  (when (< (text-cursor t) (text-length t))
    (text-move! t 1)))

(define (text-prev-line! t)
  "Move to previous line"
  (text-line-start! t)
  (when (> (text-cursor t) 0)
    (text-move! t -1)
    (text-line-start! t)))

;; Editing
(define (text-insert! t str)
  "Insert string at cursor"
  (gap-buffer-insert-string! (text-buffer t) str)
  (set-text-modified! t #t))

(define (text-delete! t n)
  "Delete n characters after cursor"
  (gap-buffer-delete! (text-buffer t) n)
  (set-text-modified! t #t))

(define (text-delete-forward! t)
  "Delete character at cursor"
  (text-delete! t 1))

(define (text-kill-line! t)
  "Delete to end of line"
  (let ((start (text-cursor t))
        (len (text-length t)))
    (let loop ((pos start))
      (cond
       ((>= pos len) (text-delete! t (- pos start)))
       ((char=? (text-char-at t pos) #\newline)
        (text-delete! t (- pos start -1)))  ; include newline
       (else (loop (+ pos 1)))))))

(define (text-replace! t start end new-text)
  "Replace region with new text"
  (text-goto! t start)
  (text-delete! t (- end start))
  (text-insert! t new-text))

;; Search
(define (text-search t pattern #!optional (from #f))
  "Search forward from position, return position or #f"
  (let* ((start (or from (text-cursor t)))
         (text-str (text->string t))
         (pos (string-contains text-str pattern start)))
    pos))

(define (text-search-backward t pattern #!optional (from #f))
  "Search backward from position, return position or #f"
  (let* ((end (or from (text-cursor t)))
         (text-str (substring (text->string t) 0 end)))
    (let loop ((pos (- end (string-length pattern))))
      (cond
       ((< pos 0) #f)
       ((string-prefix? pattern (substring text-str pos))
        pos)
       (else (loop (- pos 1)))))))

;;; ============================================================
;;; Soup Integration - seal/unseal to content-addressed storage
;;; ============================================================
;;;
;;; Three storage strategies for space efficiency:
;;;
;;; 1. CHUNKED - Content-defined chunking with rolling hash
;;;    Splits text at natural boundaries, deduplicates chunks.
;;;    Good for large files with localized edits.
;;;
;;; 2. DELTA - Stores diff from parent version
;;;    Good for small edits to any size file.
;;;    Chain depth limited to prevent reconstruction explosion.
;;;
;;; 3. FULL - Complete content (current default)
;;;    Simple, fast, always works. Used as base for deltas.
;;;
;;; text-seal auto-selects based on content and parent availability.

;; Configurable vault path (default: .vault in current directory)
(define *vault-path* ".vault")

(define (set-vault-path! path)
  "Set the vault directory path"
  (set! *vault-path* path))

(define (vault-objects-path)
  "Path to objects directory"
  (make-pathname *vault-path* "objects"))

(define (vault-chunks-path)
  "Path to chunks directory"
  (make-pathname *vault-path* "chunks"))

(define (vault-deltas-path)
  "Path to deltas directory"
  (make-pathname *vault-path* "deltas"))

(define (ensure-vault-dirs!)
  "Create vault directories if needed"
  (for-each (lambda (dir)
              (unless (directory-exists? dir)
                (create-directory dir #t)))
            (list (vault-objects-path)
                  (vault-chunks-path)
                  (vault-deltas-path))))

(define (blob->hex b)
  "Convert blob to hex string"
  (define (byte->hex n)
    (let ((s (number->string n 16)))
      (if (= (string-length s) 1)
          (string-append "0" s)
          s)))
  (let* ((len (blob-size b))
         (parts '()))
    (do ((i 0 (+ i 1))) ((>= i len) (apply string-append (reverse parts)))
      (set! parts (cons (byte->hex (u8vector-ref (blob->u8vector b) i)) parts)))))

(define (content-hash str)
  "Blake2b hash of string content"
  (string-append "blake2b:" (blob->hex (blake2b-hash str))))

(define (text-hash t)
  "Content hash of text using blake2b (32 bytes = 64 hex chars)"
  (content-hash (text->string t)))

(define (hash->path hash)
  "Convert hash to storage path (objects)"
  (make-pathname (vault-objects-path) hash))

(define (chunk-hash->path hash)
  "Convert hash to chunk storage path"
  (make-pathname (vault-chunks-path) hash))

(define (delta-hash->path hash)
  "Convert hash to delta storage path"
  (make-pathname (vault-deltas-path) hash))

;;; ============================================================
;;; Chunked Storage - Content-Defined Chunking
;;; ============================================================
;;;
;;; Rolling hash (Rabin-style) splits at natural boundaries.
;;; Average chunk ~4KB, min 1KB, max 16KB.
;;; Only new chunks are stored; existing chunks deduplicated.

(define *chunk-min* 1024)      ; minimum chunk size
(define *chunk-avg* 4096)      ; target average (mask determines this)
(define *chunk-max* 16384)     ; maximum chunk size
(define *chunk-mask* #xFFF)    ; split when (hash & mask) == 0 (~4KB avg)

(define (rolling-hash-init)
  "Initialize rolling hash state"
  0)

(define (rolling-hash-update h byte)
  "Update rolling hash with new byte (simple polynomial)"
  ;; h = h * 31 + byte, keeping low 32 bits
  (bitwise-and (+ (* h 31) byte) #xFFFFFFFF))

(define (chunk-boundary? hash pos)
  "Check if this is a chunk boundary"
  (and (>= pos *chunk-min*)
       (or (>= pos *chunk-max*)
           (= (bitwise-and hash *chunk-mask*) 0))))

(define (string->chunks str)
  "Split string into content-defined chunks. Returns list of strings."
  (let ((len (string-length str)))
    (if (<= len *chunk-min*)
        (list str)  ; too small to chunk
        (let loop ((pos 0) (chunk-start 0) (h (rolling-hash-init)) (chunks '()))
          (cond
           ((>= pos len)
            ;; Final chunk
            (reverse (cons (substring str chunk-start len) chunks)))
           (else
            (let* ((byte (char->integer (string-ref str pos)))
                   (new-h (rolling-hash-update h byte))
                   (chunk-len (- pos chunk-start)))
              (if (chunk-boundary? new-h chunk-len)
                  ;; Split here
                  (loop (+ pos 1) (+ pos 1) (rolling-hash-init)
                        (cons (substring str chunk-start (+ pos 1)) chunks))
                  ;; Continue
                  (loop (+ pos 1) chunk-start new-h chunks)))))))))

(define (store-chunk! chunk)
  "Store chunk, return its hash. Idempotent."
  (let* ((hash (content-hash chunk))
         (path (chunk-hash->path hash)))
    (unless (file-exists? path)
      (with-output-to-file path
        (lambda () (display chunk))))
    hash))

(define (load-chunk hash)
  "Load chunk by hash"
  (let ((path (chunk-hash->path hash)))
    (if (file-exists? path)
        (with-input-from-file path read-string)
        (error "Chunk not found" hash))))

(define (store-chunked! content)
  "Store content as chunks, return content hash.
   Manifest stored at content hash path.
   Manifest format: (chunked (chunks hash1 hash2 ...))"
  (let* ((content-h (content-hash content))
         (chunks (string->chunks content))
         (chunk-hashes (map store-chunk! chunks))
         (manifest `(chunked (chunks ,@chunk-hashes)
                            (content-hash ,content-h)
                            (total-size ,(string-length content))
                            (chunk-count ,(length chunks))))
         (manifest-str (format #f "~s" manifest))
         (manifest-path (hash->path content-h)))
    (unless (file-exists? manifest-path)
      (with-output-to-file manifest-path
        (lambda () (display manifest-str))))
    content-h))

(define (load-chunked manifest-hash)
  "Load content from chunked manifest"
  (let* ((path (hash->path manifest-hash))
         (manifest-str (with-input-from-file path read-string))
         (manifest (with-input-from-string manifest-str read)))
    (if (and (pair? manifest) (eq? (car manifest) 'chunked))
        (let ((chunk-hashes (cdr (assq 'chunks (cdr manifest)))))
          (apply string-append (map load-chunk chunk-hashes)))
        (error "Invalid chunked manifest" manifest-hash))))

;;; ============================================================
;;; Delta Storage - Edit Script Compression
;;; ============================================================
;;;
;;; Stores difference from parent version.
;;; Simple edit script: (delta base-hash ops...)
;;; ops: (copy start len) | (insert "text")
;;;
;;; Chain depth limited to 10 to bound reconstruction time.

(define *max-delta-depth* 10)

(define (compute-delta old-str new-str)
  "Compute edit script from old to new. Returns list of ops.
   Simple algorithm: find common prefix/suffix, insert middle."
  (let* ((old-len (string-length old-str))
         (new-len (string-length new-str))
         ;; Common prefix
         (prefix-len
          (let loop ((i 0))
            (if (and (< i old-len) (< i new-len)
                     (char=? (string-ref old-str i) (string-ref new-str i)))
                (loop (+ i 1))
                i)))
         ;; Common suffix (after prefix)
         (suffix-len
          (let loop ((i 0))
            (let ((old-pos (- old-len 1 i))
                  (new-pos (- new-len 1 i)))
              (if (and (>= old-pos prefix-len) (>= new-pos prefix-len)
                       (char=? (string-ref old-str old-pos)
                               (string-ref new-str new-pos)))
                  (loop (+ i 1))
                  i))))
         (old-middle-end (- old-len suffix-len))
         (new-middle-start prefix-len)
         (new-middle-end (- new-len suffix-len)))
    ;; Build ops
    (let ((ops '()))
      ;; Copy prefix from old
      (when (> prefix-len 0)
        (set! ops (cons `(copy 0 ,prefix-len) ops)))
      ;; Insert new middle (if any)
      (when (> new-middle-end new-middle-start)
        (set! ops (cons `(insert ,(substring new-str new-middle-start new-middle-end)) ops)))
      ;; Copy suffix from old
      (when (> suffix-len 0)
        (set! ops (cons `(copy ,old-middle-end ,suffix-len) ops)))
      (reverse ops))))

(define (apply-delta base-str ops)
  "Apply edit script to base string"
  (apply string-append
         (map (lambda (op)
                (case (car op)
                  ((copy)
                   (let ((start (cadr op))
                         (len (caddr op)))
                     (substring base-str start (+ start len))))
                  ((insert)
                   (cadr op))
                  (else (error "Unknown delta op" op))))
              ops)))

(define (delta-size ops)
  "Estimate serialized size of delta ops"
  (let loop ((ops ops) (size 20))  ; base overhead
    (if (null? ops)
        size
        (loop (cdr ops)
              (+ size
                 (case (caar ops)
                   ((copy) 20)  ; (copy N N) ~20 chars
                   ((insert) (+ 12 (string-length (cadar ops))))
                   (else 10)))))))

(define (get-delta-depth hash)
  "Get depth of delta chain (0 for full content).
   Recursively follows base-hash to count chain length."
  (let ((delta-path (delta-hash->path hash)))
    (if (file-exists? delta-path)
        (let* ((delta-str (with-input-from-file delta-path read-string))
               (delta (with-input-from-string delta-str read)))
          (if (and (pair? delta) (eq? (car delta) 'delta))
              (+ 1 (get-delta-depth (cadr delta)))  ; recurse on base-hash
              0))
        0)))

(define (store-delta! base-hash ops target-hash)
  "Store delta at target-hash path in deltas/.
   Format: (delta base-hash target-hash ops...)"
  (let* ((delta `(delta ,base-hash ,target-hash ,@ops))
         (delta-str (format #f "~s" delta))
         (path (delta-hash->path target-hash)))  ; Store at content hash
    (unless (file-exists? path)
      (with-output-to-file path
        (lambda () (display delta-str))))
    target-hash))

(define (load-via-delta target-hash)
  "Reconstruct content from delta chain.
   target-hash is the content hash, delta stored at deltas/target-hash"
  (let* ((path (delta-hash->path target-hash))
         (delta-str (with-input-from-file path read-string))
         (delta (with-input-from-string delta-str read)))
    (if (and (pair? delta) (eq? (car delta) 'delta))
        (let ((base-hash (cadr delta))
              (expected-hash (caddr delta))
              (ops (cdddr delta)))
          ;; Load base (might be another delta, or full content)
          (let* ((base-content (load-content base-hash))
                 (result (apply-delta base-content ops)))
            ;; Verify
            (unless (string=? (content-hash result) expected-hash)
              (error "Delta reconstruction failed" target-hash))
            result))
        (error "Invalid delta format" target-hash))))

;;; ============================================================
;;; Unified Storage - Smart Selection
;;; ============================================================

(define (content-exists? hash)
  "Check if content exists in any form"
  (or (file-exists? (hash->path hash))
      (file-exists? (delta-hash->path hash))))

(define (load-content hash)
  "Load content by hash, handling full/chunked/delta formats"
  (let ((obj-path (hash->path hash))
        (delta-path (delta-hash->path hash)))
    (cond
     ;; Full or chunked object
     ((file-exists? obj-path)
      (let* ((content (with-input-from-file obj-path read-string))
             (parsed (condition-case
                      (with-input-from-string content read)
                      ((exn) #f))))
        (if (and (pair? parsed) (eq? (car parsed) 'chunked))
            ;; Chunked manifest
            (load-chunked hash)
            ;; Full content
            content)))
     ;; Delta reference
     ((file-exists? delta-path)
      (load-via-delta hash))
     (else
      (error "Content not found" hash)))))

(define (store-smart! content parent-hash)
  "Store content using best strategy. Returns (type . hash).
   Strategies:
   - If small (< 4KB): always store full
   - If parent available and delta < 50% size: store delta
   - If large (> 16KB): store chunked
   - Otherwise: store full"
  (ensure-vault-dirs!)
  (let* ((size (string-length content))
         (content-h (content-hash content))
         (path (hash->path content-h)))
    (cond
     ;; Already exists
     ((content-exists? content-h)
      (cons 'existing content-h))

     ;; Small content: always full
     ((< size *chunk-min*)
      (with-output-to-file path (lambda () (display content)))
      (cons 'full content-h))

     ;; Has parent: try delta
     ((and parent-hash
           (content-exists? parent-hash)
           (< (get-delta-depth parent-hash) *max-delta-depth*))
      (let* ((parent-content (load-content parent-hash))
             (ops (compute-delta parent-content content))
             (delta-sz (delta-size ops)))
        (if (< delta-sz (quotient size 2))
            ;; Delta is worth it
            (let ((delta-h (store-delta! parent-hash ops content-h)))
              (cons 'delta content-h))
            ;; Delta too big, try chunked or full
            (if (> size *chunk-max*)
                (cons 'chunked (store-chunked! content))
                (begin
                  (with-output-to-file path (lambda () (display content)))
                  (cons 'full content-h))))))

     ;; Large content: chunked
     ((> size *chunk-max*)
      (cons 'chunked (store-chunked! content)))

     ;; Default: full
     (else
      (with-output-to-file path (lambda () (display content)))
      (cons 'full content-h)))))

;;; ============================================================
;;; Public API
;;; ============================================================

(define (text-seal t)
  "Seal text to vault using smart storage strategy.
   Returns content hash. Updates provenance chain."
  (let* ((old-hash (text-source-hash t))
         (content (text->string t))
         (result (store-smart! content old-hash))
         (storage-type (car result))
         (new-hash (cdr result)))
    ;; Update provenance
    (set-text-parent-hash! t old-hash)
    (set-text-source-hash! t new-hash)
    (set-text-modified! t #f)
    new-hash))

(define (text-unseal hash)
  "Load text from vault by hash. Handles full/chunked/delta.
   Verifies integrity. Sets source-hash for provenance."
  (let* ((content (load-content hash))
         (t (text-from-string content))
         (computed-hash (text-hash t)))
    ;; Verify integrity
    (unless (string=? hash computed-hash)
      (error "Content integrity failure" hash computed-hash))
    (set-text-source-hash! t hash)
    t))

) ; end module
