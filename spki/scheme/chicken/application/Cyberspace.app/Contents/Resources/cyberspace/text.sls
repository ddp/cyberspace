;;; text.sls - Text objects for the soup
;;;
;;; Gap buffer for editing, chunked merkle for storage.
;;; Both Electric Pencil and TECO use this - one representation,
;;; multiple interfaces. The buffer is the truth; editors are views.

(library (cyberspace text)
  (export
    ;; Construction
    text-new text-from-string text-from-file
    ;; Query
    text-length text-cursor text-char-at text-substring
    text->string text-line-count text-line-at text-modified?
    ;; Movement
    text-goto! text-move! text-beginning! text-end!
    text-line-start! text-line-end! text-next-line! text-prev-line!
    ;; Editing
    text-insert! text-delete! text-delete-forward!
    text-kill-line! text-replace!
    ;; Search
    text-search text-search-backward
    ;; Provenance
    text-source-hash text-parent-hash
    ;; Soup integration
    text-seal text-unseal text-hash
    set-vault-path! content-exists? load-content
    ;; Named refs
    seal-as unseal-named ref-list ref-history
    ref-current ref-delete!
    ;; For editors
    text-gap-buffer text-clear-modified!)

  (import (rnrs)
          (rnrs mutable-strings)
          (only (chezscheme)
                printf format
                with-input-from-string with-output-to-string
                file-directory? directory-list
                mkdir)
          (only (cyberspace crypto-ffi) blake2b-hash))

  ;; ============================================================
  ;; Inlined helpers
  ;; ============================================================

  (define (string-contains s1 s2 . rest)
    (let ((start (if (null? rest) 0 (car rest)))
          (len1 (string-length s1))
          (len2 (string-length s2)))
      (if (> len2 (- len1 start)) #f
          (let loop ((i start))
            (cond ((> (+ i len2) len1) #f)
                  ((string=? s2 (substring s1 i (+ i len2))) i)
                  (else (loop (+ i 1))))))))

  (define (string-prefix? prefix s)
    (and (>= (string-length s) (string-length prefix))
         (string=? prefix (substring s 0 (string-length prefix)))))

  (define (string-index s ch)
    (let ((len (string-length s)))
      (let loop ((i 0))
        (cond ((= i len) #f)
              ((char=? (string-ref s i) ch) i)
              (else (loop (+ i 1)))))))

  (define (make-pathname dir file)
    (string-append dir "/" file))

  (define (directory-exists? path)
    (and (file-exists? path) (file-directory? path)))

  (define (create-directory path . rest)
    (let ((recursive (if (null? rest) #f (car rest))))
      (if recursive
          (let loop ((parts (path-split path)) (current ""))
            (unless (null? parts)
              (let ((next (if (string=? current "")
                              (car parts) (string-append current "/" (car parts)))))
                (unless (or (string=? next "") (directory-exists? next))
                  (guard (exn [#t #f]) (mkdir next #o755)))
                (loop (cdr parts) next))))
          (unless (directory-exists? path) (mkdir path #o755)))))

  (define (path-split str)
    (let loop ((i 0) (start 0) (acc '()))
      (cond
        ((= i (string-length str))
         (reverse (if (= start i) acc (cons (substring str start i) acc))))
        ((char=? (string-ref str i) #\/)
         (loop (+ i 1) (+ i 1)
               (if (= start i) acc (cons (substring str start i) acc))))
        (else (loop (+ i 1) start acc)))))

  (define (every pred lst)
    (or (null? lst) (and (pred (car lst)) (every pred (cdr lst)))))

  (define (bytevector->hex bv)
    (let* ((len (bytevector-length bv))
           (parts '()))
      (do ((i 0 (+ i 1)))
          ((>= i len) (apply string-append (reverse parts)))
        (let ((s (number->string (bytevector-u8-ref bv i) 16)))
          (set! parts (cons (if (< (bytevector-u8-ref bv i) 16)
                                (string-append "0" s) s)
                            parts))))))

  ;; ============================================================
  ;; Gap Buffer
  ;; ============================================================

  (define-record-type (gap-buffer make-gap-buffer-raw gap-buffer?)
    (fields (mutable vec gb-vec set-gb-vec!)
            (mutable gap-start gb-gap-start set-gb-gap-start!)
            (mutable gap-end gb-gap-end set-gb-gap-end!)
            (mutable size gb-size set-gb-size!)))

  (define *default-gap* 256)
  (define *initial-size* 1024)

  (define (gap-buffer-new . rest)
    (let ((size (if (null? rest) *initial-size* (car rest))))
      (make-gap-buffer-raw (make-vector size #\nul) 0 size size)))

  (define (gap-buffer-length gb)
    (- (gb-size gb) (- (gb-gap-end gb) (gb-gap-start gb))))

  (define (gap-buffer-cursor gb) (gb-gap-start gb))

  (define (gap-buffer-grow! gb min-gap)
    (when (< (- (gb-gap-end gb) (gb-gap-start gb)) min-gap)
      (let* ((old-vec (gb-vec gb))
             (old-size (gb-size gb))
             (new-size (* 2 (+ old-size min-gap)))
             (new-vec (make-vector new-size #\nul))
             (gap-start (gb-gap-start gb))
             (gap-end (gb-gap-end gb))
             (after-gap (- old-size gap-end))
             (new-gap-end (- new-size after-gap)))
        (do ((i 0 (+ i 1))) ((>= i gap-start))
          (vector-set! new-vec i (vector-ref old-vec i)))
        (do ((i 0 (+ i 1))) ((>= i after-gap))
          (vector-set! new-vec (+ new-gap-end i) (vector-ref old-vec (+ gap-end i))))
        (set-gb-vec! gb new-vec)
        (set-gb-gap-end! gb new-gap-end)
        (set-gb-size! gb new-size))))

  (define (gap-buffer-move-gap! gb pos)
    (let ((gap-start (gb-gap-start gb))
          (gap-end (gb-gap-end gb))
          (vec (gb-vec gb)))
      (cond
        ((= pos gap-start) #t)
        ((< pos gap-start)
         (let ((shift (- gap-start pos)))
           (do ((i 0 (+ i 1))) ((>= i shift))
             (vector-set! vec (- gap-end 1 i) (vector-ref vec (- gap-start 1 i))))
           (set-gb-gap-start! gb pos)
           (set-gb-gap-end! gb (- gap-end shift))))
        (else
         (let ((shift (- pos gap-start)))
           (do ((i 0 (+ i 1))) ((>= i shift))
             (vector-set! vec (+ gap-start i) (vector-ref vec (+ gap-end i))))
           (set-gb-gap-start! gb pos)
           (set-gb-gap-end! gb (+ gap-end shift)))))))

  (define (gap-buffer-insert! gb char)
    (gap-buffer-grow! gb 1)
    (vector-set! (gb-vec gb) (gb-gap-start gb) char)
    (set-gb-gap-start! gb (+ (gb-gap-start gb) 1)))

  (define (gap-buffer-insert-string! gb str)
    (let ((len (string-length str)))
      (gap-buffer-grow! gb len)
      (do ((i 0 (+ i 1))) ((>= i len))
        (vector-set! (gb-vec gb) (+ (gb-gap-start gb) i) (string-ref str i)))
      (set-gb-gap-start! gb (+ (gb-gap-start gb) len))))

  (define (gap-buffer-delete! gb n)
    (set-gb-gap-end! gb (min (gb-size gb) (+ (gb-gap-end gb) n))))

  (define (gap-buffer-delete-backward! gb n)
    (set-gb-gap-start! gb (max 0 (- (gb-gap-start gb) n))))

  (define (gap-buffer-char-at gb pos)
    (let ((gap-start (gb-gap-start gb))
          (gap-end (gb-gap-end gb)))
      (if (< pos gap-start)
          (vector-ref (gb-vec gb) pos)
          (vector-ref (gb-vec gb) (+ gap-end (- pos gap-start))))))

  (define (gap-buffer->string gb)
    (let* ((len (gap-buffer-length gb))
           (str (make-string len)))
      (do ((i 0 (+ i 1))) ((>= i len) str)
        (string-set! str i (gap-buffer-char-at gb i)))))

  (define (string->gap-buffer str)
    (let* ((len (string-length str))
           (size (max *initial-size* (* 2 len)))
           (gb (gap-buffer-new size)))
      (gap-buffer-insert-string! gb str)
      gb))

  ;; ============================================================
  ;; Text Object
  ;; ============================================================

  (define-record-type (text-obj make-text-raw text-obj?)
    (fields (immutable buffer text-buffer)
            (mutable modified text-modified set-text-modified!)
            (mutable source-hash text-source-hash set-text-source-hash!)
            (mutable parent-hash text-parent-hash set-text-parent-hash!)))

  (define (text-new) (make-text-raw (gap-buffer-new) #f #f #f))

  (define (text-from-string str)
    (make-text-raw (string->gap-buffer str) #f #f #f))

  (define (text-from-file filename)
    (let ((content (with-input-from-file filename
                     (lambda () (get-string-all (current-input-port))))))
      (make-text-raw (string->gap-buffer content) #f #f #f)))

  (define (text-length t) (gap-buffer-length (text-buffer t)))
  (define (text-cursor t) (gap-buffer-cursor (text-buffer t)))
  (define (text-char-at t pos) (gap-buffer-char-at (text-buffer t) pos))
  (define (text->string t) (gap-buffer->string (text-buffer t)))
  (define (text-modified? t) (text-modified t))
  (define (text-gap-buffer t) (text-buffer t))
  (define (text-clear-modified! t) (set-text-modified! t #f))

  (define (text-substring t start end)
    (let* ((len (text-length t))
           (s (max 0 (min start len)))
           (e (max s (min end len)))
           (result (make-string (- e s))))
      (do ((i s (+ i 1))) ((>= i e) result)
        (string-set! result (- i s) (text-char-at t i)))))

  (define (text-line-count t)
    (let ((len (text-length t)))
      (let loop ((i 0) (count 1))
        (if (>= i len) count
            (loop (+ i 1) (if (char=? (text-char-at t i) #\newline) (+ count 1) count))))))

  (define (text-line-at t line-num)
    (let ((len (text-length t)))
      (let loop ((i 0) (line 0) (start 0))
        (cond
          ((>= i len) (if (= line line-num) (text-substring t start i) ""))
          ((char=? (text-char-at t i) #\newline)
           (if (= line line-num) (text-substring t start i)
               (loop (+ i 1) (+ line 1) (+ i 1))))
          (else (loop (+ i 1) line start))))))

  ;; Movement
  (define (text-goto! t pos)
    (gap-buffer-move-gap! (text-buffer t) (max 0 (min pos (text-length t)))))
  (define (text-move! t delta)
    (text-goto! t (+ (text-cursor t) delta)))
  (define (text-beginning! t) (text-goto! t 0))
  (define (text-end! t) (text-goto! t (text-length t)))

  (define (text-line-start! t)
    (let loop ((pos (text-cursor t)))
      (cond ((<= pos 0) (text-goto! t 0))
            ((char=? (text-char-at t (- pos 1)) #\newline) (text-goto! t pos))
            (else (loop (- pos 1))))))

  (define (text-line-end! t)
    (let ((len (text-length t)))
      (let loop ((pos (text-cursor t)))
        (cond ((>= pos len) (text-goto! t len))
              ((char=? (text-char-at t pos) #\newline) (text-goto! t pos))
              (else (loop (+ pos 1)))))))

  (define (text-next-line! t)
    (text-line-end! t)
    (when (< (text-cursor t) (text-length t)) (text-move! t 1)))

  (define (text-prev-line! t)
    (text-line-start! t)
    (when (> (text-cursor t) 0) (text-move! t -1) (text-line-start! t)))

  ;; Editing
  (define (text-insert! t str)
    (gap-buffer-insert-string! (text-buffer t) str)
    (set-text-modified! t #t))

  (define (text-delete! t n)
    (gap-buffer-delete! (text-buffer t) n)
    (set-text-modified! t #t))

  (define (text-delete-forward! t) (text-delete! t 1))

  (define (text-kill-line! t)
    (let ((start (text-cursor t)) (len (text-length t)))
      (let loop ((pos start))
        (cond ((>= pos len) (text-delete! t (- pos start)))
              ((char=? (text-char-at t pos) #\newline) (text-delete! t (- pos start -1)))
              (else (loop (+ pos 1)))))))

  (define (text-replace! t start end new-text)
    (text-goto! t start)
    (text-delete! t (- end start))
    (text-insert! t new-text))

  ;; Search
  (define (text-search t pattern . rest)
    (let* ((from (if (null? rest) #f (car rest)))
           (start (or from (text-cursor t))))
      (string-contains (text->string t) pattern start)))

  (define (text-search-backward t pattern . rest)
    (let* ((from (if (null? rest) #f (car rest)))
           (end (or from (text-cursor t)))
           (text-str (substring (text->string t) 0 end)))
      (let loop ((pos (- end (string-length pattern))))
        (cond ((< pos 0) #f)
              ((string-prefix? pattern (substring text-str pos (string-length text-str))) pos)
              (else (loop (- pos 1)))))))

  ;; ============================================================
  ;; Soup Integration
  ;; ============================================================

  (define *vault-path* ".vault")
  (define (set-vault-path! path) (set! *vault-path* path))
  (define (vault-objects-path) (make-pathname *vault-path* "objects"))
  (define (vault-chunks-path) (make-pathname *vault-path* "chunks"))
  (define (vault-deltas-path) (make-pathname *vault-path* "deltas"))

  (define (ensure-vault-dirs!)
    (for-each (lambda (dir) (unless (directory-exists? dir) (create-directory dir #t)))
              (list (vault-objects-path) (vault-chunks-path) (vault-deltas-path))))

  (define (content-hash str)
    (string-append "blake2b:" (bytevector->hex (blake2b-hash str))))

  (define (text-hash t) (content-hash (text->string t)))
  (define (hash->path hash) (make-pathname (vault-objects-path) hash))
  (define (chunk-hash->path hash) (make-pathname (vault-chunks-path) hash))
  (define (delta-hash->path hash) (make-pathname (vault-deltas-path) hash))

  ;; Chunked storage
  (define *chunk-min* 1024)
  (define *chunk-max* 16384)
  (define *chunk-mask* #xFFF)

  (define (rolling-hash-update h byte)
    (bitwise-and (+ (* h 31) byte) #xFFFFFFFF))

  (define (chunk-boundary? hash pos)
    (and (>= pos *chunk-min*)
         (or (>= pos *chunk-max*)
             (= (bitwise-and hash *chunk-mask*) 0))))

  (define (string->chunks str)
    (let ((len (string-length str)))
      (if (<= len *chunk-min*) (list str)
          (let loop ((pos 0) (chunk-start 0) (h 0) (chunks '()))
            (cond
              ((>= pos len) (reverse (cons (substring str chunk-start len) chunks)))
              (else
               (let* ((byte (char->integer (string-ref str pos)))
                      (new-h (rolling-hash-update h byte))
                      (chunk-len (- pos chunk-start)))
                 (if (chunk-boundary? new-h chunk-len)
                     (loop (+ pos 1) (+ pos 1) 0
                           (cons (substring str chunk-start (+ pos 1)) chunks))
                     (loop (+ pos 1) chunk-start new-h chunks)))))))))

  (define (store-chunk! chunk)
    (let* ((hash (content-hash chunk))
           (path (chunk-hash->path hash)))
      (unless (file-exists? path)
        (with-output-to-file path (lambda () (display chunk))))
      hash))

  (define (load-chunk hash)
    (let ((path (chunk-hash->path hash)))
      (if (file-exists? path)
          (with-input-from-file path (lambda () (get-string-all (current-input-port))))
          (error 'load-chunk "Chunk not found" hash))))

  (define (store-chunked! content)
    (let* ((content-h (content-hash content))
           (chunks (string->chunks content))
           (chunk-hashes (map store-chunk! chunks))
           (manifest `(chunked (chunks ,@chunk-hashes)
                               (content-hash ,content-h)
                               (total-size ,(string-length content))
                               (chunk-count ,(length chunks))))
           (manifest-str (format "~s" manifest))
           (manifest-path (hash->path content-h)))
      (unless (file-exists? manifest-path)
        (with-output-to-file manifest-path (lambda () (display manifest-str))))
      content-h))

  (define (load-chunked manifest-hash)
    (let* ((path (hash->path manifest-hash))
           (manifest-str (with-input-from-file path
                           (lambda () (get-string-all (current-input-port)))))
           (manifest (with-input-from-string manifest-str read)))
      (if (and (pair? manifest) (eq? (car manifest) 'chunked))
          (let ((chunk-hashes (cdr (assq 'chunks (cdr manifest)))))
            (apply string-append (map load-chunk chunk-hashes)))
          (error 'load-chunked "Invalid chunked manifest" manifest-hash))))

  ;; Delta storage
  (define *max-delta-depth* 10)

  (define (compute-delta old-str new-str)
    (let* ((old-len (string-length old-str))
           (new-len (string-length new-str))
           (prefix-len (let loop ((i 0))
                         (if (and (< i old-len) (< i new-len)
                                  (char=? (string-ref old-str i) (string-ref new-str i)))
                             (loop (+ i 1)) i)))
           (suffix-len (let loop ((i 0))
                         (let ((old-pos (- old-len 1 i)) (new-pos (- new-len 1 i)))
                           (if (and (>= old-pos prefix-len) (>= new-pos prefix-len)
                                    (char=? (string-ref old-str old-pos)
                                            (string-ref new-str new-pos)))
                               (loop (+ i 1)) i))))
           (old-middle-end (- old-len suffix-len))
           (new-middle-start prefix-len)
           (new-middle-end (- new-len suffix-len)))
      (let ((ops '()))
        (when (> prefix-len 0) (set! ops (cons `(copy 0 ,prefix-len) ops)))
        (when (> new-middle-end new-middle-start)
          (set! ops (cons `(insert ,(substring new-str new-middle-start new-middle-end)) ops)))
        (when (> suffix-len 0)
          (set! ops (cons `(copy ,old-middle-end ,suffix-len) ops)))
        (reverse ops))))

  (define (apply-delta base-str ops)
    (apply string-append
           (map (lambda (op)
                  (case (car op)
                    ((copy) (substring base-str (cadr op) (+ (cadr op) (caddr op))))
                    ((insert) (cadr op))
                    (else (error 'apply-delta "Unknown delta op" op))))
                ops)))

  (define (delta-size ops)
    (let loop ((ops ops) (size 20))
      (if (null? ops) size
          (loop (cdr ops)
                (+ size (case (caar ops)
                          ((copy) 20)
                          ((insert) (+ 12 (string-length (cadar ops))))
                          (else 10)))))))

  (define (get-delta-depth hash)
    (let ((delta-path (delta-hash->path hash)))
      (if (file-exists? delta-path)
          (let* ((delta-str (with-input-from-file delta-path
                              (lambda () (get-string-all (current-input-port)))))
                 (delta (with-input-from-string delta-str read)))
            (if (and (pair? delta) (eq? (car delta) 'delta))
                (+ 1 (get-delta-depth (cadr delta))) 0))
          0)))

  (define (store-delta! base-hash ops target-hash)
    (let* ((delta `(delta ,base-hash ,target-hash ,@ops))
           (delta-str (format "~s" delta))
           (path (delta-hash->path target-hash)))
      (unless (file-exists? path) (with-output-to-file path (lambda () (display delta-str))))
      target-hash))

  (define (load-via-delta target-hash)
    (let* ((path (delta-hash->path target-hash))
           (delta-str (with-input-from-file path
                        (lambda () (get-string-all (current-input-port)))))
           (delta (with-input-from-string delta-str read)))
      (if (and (pair? delta) (eq? (car delta) 'delta))
          (let ((base-hash (cadr delta)) (ops (cdddr delta)))
            (let* ((base-content (load-content base-hash))
                   (result (apply-delta base-content ops)))
              (unless (string=? (content-hash result) (caddr delta))
                (error 'load-via-delta "Delta reconstruction failed" target-hash))
              result))
          (error 'load-via-delta "Invalid delta format" target-hash))))

  ;; Unified storage
  (define (content-exists? hash)
    (or (file-exists? (hash->path hash)) (file-exists? (delta-hash->path hash))))

  (define (load-content hash)
    (let ((obj-path (hash->path hash)) (delta-path (delta-hash->path hash)))
      (cond
        ((file-exists? obj-path)
         (let ((content (with-input-from-file obj-path
                          (lambda () (get-string-all (current-input-port))))))
           (let ((parsed (guard (exn [#t #f]) (with-input-from-string content read))))
             (if (and (pair? parsed) (eq? (car parsed) 'chunked))
                 (load-chunked hash) content))))
        ((file-exists? delta-path) (load-via-delta hash))
        (else (error 'load-content "Content not found" hash)))))

  (define (store-smart! content parent-hash)
    (ensure-vault-dirs!)
    (let* ((size (string-length content))
           (content-h (content-hash content))
           (path (hash->path content-h)))
      (cond
        ((content-exists? content-h) (cons 'existing content-h))
        ((< size *chunk-min*)
         (with-output-to-file path (lambda () (display content)))
         (cons 'full content-h))
        ((and parent-hash (content-exists? parent-hash)
              (< (get-delta-depth parent-hash) *max-delta-depth*))
         (let* ((parent-content (load-content parent-hash))
                (ops (compute-delta parent-content content))
                (delta-sz (delta-size ops)))
           (if (< delta-sz (div size 2))
               (begin (store-delta! parent-hash ops content-h) (cons 'delta content-h))
               (if (> size *chunk-max*)
                   (cons 'chunked (store-chunked! content))
                   (begin (with-output-to-file path (lambda () (display content)))
                          (cons 'full content-h))))))
        ((> size *chunk-max*) (cons 'chunked (store-chunked! content)))
        (else
         (with-output-to-file path (lambda () (display content)))
         (cons 'full content-h)))))

  ;; Public API
  (define (text-seal t)
    (let* ((old-hash (text-source-hash t))
           (content (text->string t))
           (result (store-smart! content old-hash))
           (new-hash (cdr result)))
      (set-text-parent-hash! t old-hash)
      (set-text-source-hash! t new-hash)
      (set-text-modified! t #f)
      new-hash))

  (define (text-unseal hash)
    (let* ((content (load-content hash))
           (t (text-from-string content))
           (computed-hash (text-hash t)))
      (unless (string=? hash computed-hash)
        (error 'text-unseal "Content integrity failure" hash computed-hash))
      (set-text-source-hash! t hash)
      t))

  ;; ============================================================
  ;; Named Refs
  ;; ============================================================

  (define (refs-path) (make-pathname *vault-path* "refs"))
  (define (ref-file name) (make-pathname (refs-path) name))

  (define (ensure-refs-dir!)
    (let ((path (refs-path)))
      (unless (directory-exists? path) (create-directory path #t))))

  (define (ref-load name)
    (let ((path (ref-file name)))
      (if (file-exists? path)
          (let ((data (with-input-from-file path read)))
            (if (and (list? data) (every string? data)) data '()))
          '())))

  (define (ref-save! name history)
    (ensure-refs-dir!)
    (with-output-to-file (ref-file name)
      (lambda () (write history) (newline))))

  (define (ref-current name)
    (let ((history (ref-load name)))
      (and (pair? history) (car history))))

  (define (ref-delete! name)
    (let ((path (ref-file name)))
      (when (file-exists? path) (delete-file path))))

  (define (ref-list)
    (let ((path (refs-path)))
      (if (directory-exists? path)
          (let loop ((names (directory-list path)) (result '()))
            (if (null? names) (reverse result)
                (let* ((name (car names)) (hash (ref-current name)))
                  (loop (cdr names) (if hash (cons (cons name hash) result) result)))))
          '())))

  (define (ref-history name) (ref-load name))

  (define (parse-ref-spec spec)
    (let ((semi-pos (string-index spec #\;)))
      (if semi-pos
          (let ((ver-str (substring spec (+ semi-pos 1) (string-length spec))))
            (cons (substring spec 0 semi-pos)
                  (if (string=? ver-str "") #f (string->number ver-str))))
          (cons spec #f))))

  (define (seal-as t name)
    (let* ((hash (text-seal t))
           (history (ref-load name))
           (new-history (if (and (pair? history) (string=? hash (car history)))
                            history (cons hash history))))
      (ref-save! name new-history)
      hash))

  (define (unseal-named spec)
    (let* ((parsed (parse-ref-spec spec))
           (name (car parsed))
           (version (cdr parsed))
           (history (ref-history name)))
      (cond
        ((null? history) (error 'unseal-named "Ref not found" name))
        ((not version) (text-unseal (car history)))
        ((< version 0)
         (let ((idx (abs version)))
           (if (< idx (length history)) (text-unseal (list-ref history idx))
               (error 'unseal-named "Version not found" spec))))
        (else
         (let ((idx (- (length history) version)))
           (if (and (>= idx 0) (< idx (length history)))
               (text-unseal (list-ref history idx))
               (error 'unseal-named "Version not found" spec)))))))

) ;; end library
