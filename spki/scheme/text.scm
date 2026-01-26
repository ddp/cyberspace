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

   ;; For editors
   text-gap-buffer  ; expose internal for low-level access
   text-clear-modified!  ; mark as saved (for file operations)
   )

  (import scheme
          (chicken base)
          (chicken format)
          (chicken string)
          (chicken io)
          (chicken file)
          (chicken pathname)
          (chicken blob)
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
;;; Content-addressed storage using blake2b.
;;; Objects stored in .vault/objects/{hash}
;;; For now, simple single-chunk. Future: merkle tree of chunks.

;; Configurable vault path (default: .vault in current directory)
(define *vault-path* ".vault")

(define (set-vault-path! path)
  "Set the vault directory path"
  (set! *vault-path* path))

(define (vault-objects-path)
  "Path to objects directory"
  (make-pathname *vault-path* "objects"))

(define (ensure-objects-dir!)
  "Create objects directory if needed"
  (let ((dir (vault-objects-path)))
    (unless (directory-exists? dir)
      (create-directory dir #t))))

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

(define (text-hash t)
  "Content hash of text using blake2b (32 bytes = 64 hex chars)"
  (let* ((content (text->string t))
         (hash-blob (blake2b-hash content)))
    (string-append "blake2b:" (blob->hex hash-blob))))

(define (hash->path hash)
  "Convert hash to storage path"
  (make-pathname (vault-objects-path) hash))

(define (text-seal t)
  "Seal text to vault, return hash. Captures parent for undo chain.
   Stores content at .vault/objects/{hash}"
  (ensure-objects-dir!)
  (let* ((old-hash (text-source-hash t))
         (content (text->string t))
         (new-hash (text-hash t))
         (path (hash->path new-hash)))
    ;; Store content (idempotent - same content = same hash = same file)
    (unless (file-exists? path)
      (with-output-to-file path
        (lambda () (display content))))
    ;; Update provenance
    (set-text-parent-hash! t old-hash)  ; previous version
    (set-text-source-hash! t new-hash)  ; now points to self
    (set-text-modified! t #f)
    new-hash))

(define (text-unseal hash)
  "Load text from vault by hash. Sets source-hash for provenance.
   Verifies content integrity against hash."
  (let ((path (hash->path hash)))
    (unless (file-exists? path)
      (error "Object not found in vault" hash))
    (let* ((content (with-input-from-file path read-string))
           (t (text-from-string content))
           ;; Verify integrity
           (computed-hash (text-hash t)))
      (unless (string=? hash computed-hash)
        (error "Content integrity failure" hash computed-hash))
      (set-text-source-hash! t hash)
      t)))

) ; end module
