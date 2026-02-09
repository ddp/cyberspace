;;; filetype.sls - File Type Inspector
;;; Library of Cyberspace - Chez Port
;;;
;;; Comprehensive file type detection using magic bytes and the
;;; system file(1) command. Provides both fast pure-Scheme checks
;;; for common types and fallback to libmagic for everything else.
;;;
;;; Design: Two-tier detection
;;;   1. Fast path: Pure Scheme magic byte checks (no fork)
;;;   2. Full path: Shell to file(1) for comprehensive detection

(library (cyberspace filetype)
  (export
    file-type file-mime file-description
    magic-type magic-mime
    pdf? gzip? zip? png? jpeg? gif? webp? tiff? bmp?
    mp3? mp4? wav? ogg? flac?
    elf? mach-o? pe? sqlite?
    xml? html? json?
    tar? bz2? xz? zstd? rar? sevenz? wasm?
    pdf-magic? gzip-magic?
    image? audio? video? archive? executable? document?
    *magic-patterns*)

  (import (rnrs)
          (only (chezscheme)
                file-exists? open-file-input-port
                with-output-to-string)
          (cyberspace chicken-compatibility blob)
          (cyberspace chicken-compatibility chicken)
          (cyberspace chicken-compatibility process))

  ;; ============================================================
  ;; String helpers
  ;; ============================================================

  (define (string-prefix? prefix str)
    (and (>= (string-length str) (string-length prefix))
         (string=? (substring str 0 (string-length prefix)) prefix)))

  (define (string-upcase str)
    (let ((len (string-length str)))
      (let loop ((i 0) (acc '()))
        (if (= i len)
            (list->string (reverse acc))
            (loop (+ i 1) (cons (char-upcase (string-ref str i)) acc))))))

  (define (string-contains-ci haystack needle)
    (let ((h (string-upcase haystack))
          (n (string-upcase needle)))
      (let loop ((i 0))
        (cond
          ((> (+ i (string-length n)) (string-length h)) #f)
          ((string=? (substring h i (+ i (string-length n))) n) i)
          (else (loop (+ i 1)))))))

  ;; ============================================================
  ;; Magic Byte Patterns
  ;; ============================================================

  (define *magic-patterns*
    '(;; Documents
      (pdf      "application/pdf"           0 #x25 #x50 #x44 #x46)
      (ps       "application/postscript"    0 #x25 #x21)
      (rtf      "application/rtf"           0 #x7b #x5c #x72 #x74 #x66)
      ;; Images
      (png      "image/png"                 0 #x89 #x50 #x4e #x47 #x0d #x0a #x1a #x0a)
      (jpeg     "image/jpeg"                0 #xff #xd8 #xff)
      (gif      "image/gif"                 0 #x47 #x49 #x46 #x38)
      (webp     "image/webp"                0 #x52 #x49 #x46 #x46)
      (tiff-le  "image/tiff"                0 #x49 #x49 #x2a #x00)
      (tiff-be  "image/tiff"                0 #x4d #x4d #x00 #x2a)
      (bmp      "image/bmp"                 0 #x42 #x4d)
      ;; Audio
      (mp3-id3  "audio/mpeg"                0 #x49 #x44 #x33)
      (mp3-sync "audio/mpeg"                0 #xff #xfb)
      (ogg      "audio/ogg"                 0 #x4f #x67 #x67 #x53)
      (flac     "audio/flac"                0 #x66 #x4c #x61 #x43)
      (wav      "audio/wav"                 0 #x52 #x49 #x46 #x46)
      (m4a      "audio/mp4"                 4 #x66 #x74 #x79 #x70)
      ;; Video
      (mp4      "video/mp4"                 4 #x66 #x74 #x79 #x70)
      (webm     "video/webm"                0 #x1a #x45 #xdf #xa3)
      ;; Archives
      (gzip     "application/gzip"          0 #x1f #x8b)
      (zip      "application/zip"           0 #x50 #x4b #x03 #x04)
      (rar      "application/vnd.rar"       0 #x52 #x61 #x72 #x21 #x1a #x07)
      (sevenz   "application/x-7z-compressed" 0 #x37 #x7a #xbc #xaf #x27 #x1c)
      (xz       "application/x-xz"          0 #xfd #x37 #x7a #x58 #x5a #x00)
      (bz2      "application/x-bzip2"       0 #x42 #x5a #x68)
      (zstd     "application/zstd"          0 #x28 #xb5 #x2f #xfd)
      (tar      "application/x-tar"         257 #x75 #x73 #x74 #x61 #x72)
      ;; Executables
      (elf      "application/x-executable"  0 #x7f #x45 #x4c #x46)
      (mach-o   "application/x-mach-binary" 0 #xfe #xed #xfa #xce)
      (mach-o64 "application/x-mach-binary" 0 #xfe #xed #xfa #xcf)
      (mach-fat "application/x-mach-binary" 0 #xca #xfe #xba #xbe)
      (pe       "application/x-dosexec"     0 #x4d #x5a)
      (wasm     "application/wasm"          0 #x00 #x61 #x73 #x6d)
      ;; Databases
      (sqlite   "application/x-sqlite3"     0 #x53 #x51 #x4c #x69 #x74 #x65)))

  ;; ============================================================
  ;; Magic Byte Detection
  ;; ============================================================

  (define (read-magic-bytes source n)
    "Read first n bytes from source (path, blob, or string)."
    (guard (exn [#t #f])
      (cond
        ((and (string? source) (file-exists? source))
         (let ((port (open-file-input-port source)))
           (let ((buf (make-bytevector n 0)))
             (let loop ((i 0))
               (if (>= i n)
                   (begin (close-port port) buf)
                   (let ((b (get-u8 port)))
                     (if (eof-object? b)
                         (begin (close-port port) buf)
                         (begin
                           (bytevector-u8-set! buf i b)
                           (loop (+ i 1))))))))))
        ((bytevector? source)
         (let* ((len (min n (bytevector-length source)))
                (buf (make-bytevector len 0)))
           (bytevector-copy! source 0 buf 0 len)
           buf))
        (else #f))))

  (define (match-pattern bytes pattern)
    (let ((offset (caddr pattern))
          (magic (cdddr pattern))
          (len (bytevector-length bytes)))
      (let loop ((i 0) (m magic))
        (cond
          ((null? m) #t)
          ((>= (+ offset i) len) #f)
          ((not (= (bytevector-u8-ref bytes (+ offset i)) (car m))) #f)
          (else (loop (+ i 1) (cdr m)))))))

  (define (magic-type source)
    (let ((bytes (read-magic-bytes source 300)))
      (and bytes
           (let loop ((patterns *magic-patterns*))
             (cond
               ((null? patterns) #f)
               ((match-pattern bytes (car patterns)) (caar patterns))
               (else (loop (cdr patterns))))))))

  (define (magic-mime source)
    (let ((bytes (read-magic-bytes source 300)))
      (and bytes
           (let loop ((patterns *magic-patterns*))
             (cond
               ((null? patterns) #f)
               ((match-pattern bytes (car patterns)) (cadar patterns))
               (else (loop (cdr patterns))))))))

  ;; ============================================================
  ;; Type Predicates
  ;; ============================================================

  (define (make-type-predicate type)
    (lambda (source) (eq? (magic-type source) type)))

  (define pdf?     (make-type-predicate 'pdf))
  (define gzip?    (make-type-predicate 'gzip))
  (define zip?     (make-type-predicate 'zip))
  (define png?     (make-type-predicate 'png))
  (define jpeg?    (make-type-predicate 'jpeg))
  (define gif?     (make-type-predicate 'gif))
  (define webp?    (make-type-predicate 'webp))
  (define bmp?     (make-type-predicate 'bmp))
  (define ogg?     (make-type-predicate 'ogg))
  (define flac?    (make-type-predicate 'flac))
  (define elf?     (make-type-predicate 'elf))
  (define pe?      (make-type-predicate 'pe))
  (define sqlite?  (make-type-predicate 'sqlite))
  (define tar?     (make-type-predicate 'tar))
  (define bz2?     (make-type-predicate 'bz2))
  (define xz?      (make-type-predicate 'xz))
  (define zstd?    (make-type-predicate 'zstd))
  (define rar?     (make-type-predicate 'rar))
  (define sevenz?  (make-type-predicate 'sevenz))
  (define wasm?    (make-type-predicate 'wasm))

  (define (tiff? source)
    (let ((t (magic-type source)))
      (or (eq? t 'tiff-le) (eq? t 'tiff-be))))

  (define (mp3? source)
    (let ((t (magic-type source)))
      (or (eq? t 'mp3-id3) (eq? t 'mp3-sync))))

  (define (mp4? source) (eq? (magic-type source) 'mp4))

  (define (wav? source)
    (let ((bytes (read-magic-bytes source 12)))
      (and bytes
           (>= (bytevector-length bytes) 12)
           (= (bytevector-u8-ref bytes 0) #x52)
           (= (bytevector-u8-ref bytes 1) #x49)
           (= (bytevector-u8-ref bytes 2) #x46)
           (= (bytevector-u8-ref bytes 3) #x46)
           (= (bytevector-u8-ref bytes 8) #x57)
           (= (bytevector-u8-ref bytes 9) #x41)
           (= (bytevector-u8-ref bytes 10) #x56)
           (= (bytevector-u8-ref bytes 11) #x45))))

  (define (mach-o? source)
    (let ((t (magic-type source)))
      (or (eq? t 'mach-o) (eq? t 'mach-o64) (eq? t 'mach-fat))))

  (define pdf-magic? pdf?)
  (define gzip-magic? gzip?)

  ;; ============================================================
  ;; Category Predicates
  ;; ============================================================

  (define (image? source)
    (memq (magic-type source) '(png jpeg gif webp tiff-le tiff-be bmp)))

  (define (audio? source)
    (memq (magic-type source) '(mp3-id3 mp3-sync ogg flac wav m4a)))

  (define (video? source)
    (memq (magic-type source) '(mp4 webm)))

  (define (archive? source)
    (memq (magic-type source) '(gzip zip rar sevenz xz bz2 zstd tar)))

  (define (executable? source)
    (memq (magic-type source) '(elf mach-o mach-o64 mach-fat pe wasm)))

  (define (document? source)
    (memq (magic-type source) '(pdf ps rtf)))

  ;; ============================================================
  ;; Text-Based Detection
  ;; ============================================================

  (define (looks-like-text? bytes)
    (let ((len (bytevector-length bytes)))
      (let loop ((i 0) (text-chars 0) (binary-chars 0))
        (cond
          ((>= i len)
           (and (> text-chars 0)
                (< binary-chars (* text-chars 0.1))))
          (else
           (let ((b (bytevector-u8-ref bytes i)))
             (cond
               ((or (and (>= b 32) (<= b 126))
                    (= b 9) (= b 10) (= b 13))
                (loop (+ i 1) (+ text-chars 1) binary-chars))
               ((and (>= b #x80) (<= b #xbf))
                (loop (+ i 1) text-chars binary-chars))
               ((and (>= b #xc0) (<= b #xf7))
                (loop (+ i 1) text-chars binary-chars))
               (else
                (loop (+ i 1) text-chars (+ binary-chars 1))))))))))

  (define (xml? source)
    (let ((bytes (read-magic-bytes source 50)))
      (and bytes
           (>= (bytevector-length bytes) 5)
           (= (bytevector-u8-ref bytes 0) #x3c)
           (= (bytevector-u8-ref bytes 1) #x3f)
           (= (bytevector-u8-ref bytes 2) #x78)
           (= (bytevector-u8-ref bytes 3) #x6d)
           (= (bytevector-u8-ref bytes 4) #x6c))))

  (define (html? source)
    (let ((bytes (read-magic-bytes source 100)))
      (and bytes
           (looks-like-text? bytes)
           (let ((s (utf8->string bytes)))
             (or (string-prefix? "<!DOCTYPE" (string-upcase s))
                 (string-prefix? "<HTML" (string-upcase s))
                 (string-contains-ci s "<html"))))))

  (define (json? source)
    (let ((bytes (read-magic-bytes source 100)))
      (and bytes
           (> (bytevector-length bytes) 0)
           (looks-like-text? bytes)
           (let ((first (bytevector-u8-ref bytes 0)))
             (or (= first #x7b) (= first #x5b))))))

  ;; ============================================================
  ;; Full Detection (Shell to file(1))
  ;; ============================================================

  (define (file-command path flag)
    (guard (exn [#t #f])
      (with-input-from-pipe
       (string-append "file " flag " '" path "' 2>/dev/null")
       (lambda () (let ((line (read-line))) (if (eof-object? line) #f line))))))

  (define (file-mime path)
    (or (magic-mime path)
        (file-command path "-b --mime-type")
        "application/octet-stream"))

  (define (file-description path)
    (or (file-command path "-b")
        "data"))

  (define (file-type path)
    (cons (file-mime path) (file-description path)))

) ;; end library
