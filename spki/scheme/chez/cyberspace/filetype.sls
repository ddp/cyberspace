;;; filetype.sls - File Type Inspector (Chez Port)
;;; Library of Cyberspace
;;;
;;; Comprehensive file type detection using magic bytes and the
;;; system file(1) command. Provides both fast pure-Scheme checks
;;; for common types and fallback to libmagic for everything else.
;;;
;;; Design: Two-tier detection
;;;   1. Fast path: Pure Scheme magic byte checks (no fork)
;;;   2. Full path: Shell to file(1) for comprehensive detection
;;;
;;; Ported from filetype.scm.
;;; Copyright (c) 2026 Yoyodyne. See LICENSE.

(library (cyberspace filetype)
  (export
    ;; Primary interface
    file-type          ; path -> (mime . description)
    file-mime          ; path -> mime-type string
    file-description   ; path -> human description

    ;; Fast pure-Scheme checks
    magic-type         ; bytevector/string -> symbol or #f
    magic-mime         ; bytevector/string -> mime-type or #f

    ;; Type predicates
    pdf?
    gzip?
    zip?
    png?
    jpeg?
    gif?
    webp?
    tiff?
    bmp?
    mp3?
    mp4?
    wav?
    ogg?
    flac?
    elf?
    mach-o?
    pe?
    sqlite?
    xml?
    html?
    json?
    tar?
    bz2?
    xz?
    zstd?
    rar?
    sevenz?
    wasm?
    pdf-magic?    ; legacy alias
    gzip-magic?   ; legacy alias

    ;; Categories
    image?
    audio?
    video?
    archive?
    executable?
    document?

    ;; Known types registry
    *magic-patterns*)

  (import (except (rnrs) file-exists? find string-upcase string-downcase)
          (only (chezscheme)
                printf format void
                file-exists? open-file-input-port)
          (cyberspace chicken-compatibility chicken)
          (cyberspace os))

  ;; ============================================================
  ;; Magic Byte Patterns
  ;; ============================================================
  ;;
  ;; Each pattern: (symbol mime-type offset bytes ...)
  ;; Offset can be 0 for start-of-file or a number for other positions.

  (define *magic-patterns*
    '(;; Documents
      (pdf      "application/pdf"           0 #x25 #x50 #x44 #x46)  ; %PDF
      (ps       "application/postscript"    0 #x25 #x21)            ; %!
      (rtf      "application/rtf"           0 #x7b #x5c #x72 #x74 #x66)  ; {\rtf

      ;; Images
      (png      "image/png"                 0 #x89 #x50 #x4e #x47 #x0d #x0a #x1a #x0a)
      (jpeg     "image/jpeg"                0 #xff #xd8 #xff)
      (gif      "image/gif"                 0 #x47 #x49 #x46 #x38)  ; GIF8
      (webp     "image/webp"                0 #x52 #x49 #x46 #x46)  ; RIFF (+ WEBP at 8)
      (tiff-le  "image/tiff"                0 #x49 #x49 #x2a #x00)  ; II*\0
      (tiff-be  "image/tiff"                0 #x4d #x4d #x00 #x2a)  ; MM\0*
      (bmp      "image/bmp"                 0 #x42 #x4d)            ; BM
      (ico      "image/x-icon"              0 #x00 #x00 #x01 #x00)
      (psd      "image/vnd.adobe.photoshop" 0 #x38 #x42 #x50 #x53)  ; 8BPS
      (svg      "image/svg+xml"             0 #x3c #x73 #x76 #x67)  ; <svg (simplified)

      ;; Audio
      (mp3-id3  "audio/mpeg"                0 #x49 #x44 #x33)       ; ID3
      (mp3-sync "audio/mpeg"                0 #xff #xfb)            ; MPEG sync
      (ogg      "audio/ogg"                 0 #x4f #x67 #x67 #x53)  ; OggS
      (flac     "audio/flac"                0 #x66 #x4c #x61 #x43)  ; fLaC
      (wav      "audio/wav"                 0 #x52 #x49 #x46 #x46)  ; RIFF (+ WAVE at 8)
      (aiff     "audio/aiff"                0 #x46 #x4f #x52 #x4d)  ; FORM
      (midi     "audio/midi"                0 #x4d #x54 #x68 #x64)  ; MThd
      (m4a      "audio/mp4"                 4 #x66 #x74 #x79 #x70)  ; ftyp at offset 4

      ;; Video
      (mp4      "video/mp4"                 4 #x66 #x74 #x79 #x70)  ; ftyp
      (webm     "video/webm"                0 #x1a #x45 #xdf #xa3)  ; EBML
      (mkv      "video/x-matroska"          0 #x1a #x45 #xdf #xa3)  ; EBML
      (avi      "video/avi"                 0 #x52 #x49 #x46 #x46)  ; RIFF (+ AVI at 8)
      (mov      "video/quicktime"           4 #x66 #x74 #x79 #x70)  ; ftyp (qt brand)
      (flv      "video/x-flv"               0 #x46 #x4c #x56 #x01)  ; FLV\1

      ;; Archives
      (gzip     "application/gzip"          0 #x1f #x8b)
      (zip      "application/zip"           0 #x50 #x4b #x03 #x04)  ; PK\3\4
      (rar      "application/vnd.rar"       0 #x52 #x61 #x72 #x21 #x1a #x07)  ; Rar!
      (sevenz   "application/x-7z-compressed" 0 #x37 #x7a #xbc #xaf #x27 #x1c)  ; 7z
      (xz       "application/x-xz"          0 #xfd #x37 #x7a #x58 #x5a #x00)  ; .7zXZ
      (bz2      "application/x-bzip2"       0 #x42 #x5a #x68)       ; BZh
      (zstd     "application/zstd"          0 #x28 #xb5 #x2f #xfd)
      (lz4      "application/x-lz4"         0 #x04 #x22 #x4d #x18)
      (tar      "application/x-tar"         257 #x75 #x73 #x74 #x61 #x72)  ; ustar at 257
      (ar       "application/x-archive"     0 #x21 #x3c #x61 #x72 #x63 #x68 #x3e)  ; !<arch>
      (cab      "application/vnd.ms-cab-compressed" 0 #x4d #x53 #x43 #x46)  ; MSCF
      (dmg      "application/x-apple-diskimage" 0 #x78 #x01 #x73 #x0d #x62 #x62 #x60)

      ;; Executables
      (elf      "application/x-executable"  0 #x7f #x45 #x4c #x46)  ; .ELF
      (mach-o   "application/x-mach-binary" 0 #xfe #xed #xfa #xce)  ; 32-bit
      (mach-o64 "application/x-mach-binary" 0 #xfe #xed #xfa #xcf)  ; 64-bit
      (mach-fat "application/x-mach-binary" 0 #xca #xfe #xba #xbe)  ; universal
      (pe       "application/x-dosexec"     0 #x4d #x5a)            ; MZ
      (shebang  "text/x-script"             0 #x23 #x21)            ; #!
      (wasm     "application/wasm"          0 #x00 #x61 #x73 #x6d)  ; \0asm
      (class    "application/java-vm"       0 #xca #xfe #xba #xbe)  ; Java
      (dex      "application/vnd.android.dex" 0 #x64 #x65 #x78 #x0a) ; dex\n

      ;; Databases
      (sqlite   "application/x-sqlite3"     0 #x53 #x51 #x4c #x69 #x74 #x65)  ; SQLite

      ;; Fonts
      (ttf      "font/sfnt"                 0 #x00 #x01 #x00 #x00)
      (otf      "font/otf"                  0 #x4f #x54 #x54 #x4f)  ; OTTO
      (woff     "font/woff"                 0 #x77 #x4f #x46 #x46)  ; wOFF
      (woff2    "font/woff2"                0 #x77 #x4f #x46 #x32)  ; wOF2

      ;; Crypto / Certificates
      (gpg      "application/pgp-encrypted" 0 #x85 #x01)            ; old format
      (gpg2     "application/pgp-encrypted" 0 #x85 #x02)            ; new format
      (ssh-key  "application/x-ssh-key"     0 #x73 #x73 #x68 #x2d)  ; ssh-
      ))

  ;; ============================================================
  ;; Magic Byte Detection (Pure Scheme - Fast Path)
  ;; ============================================================

  (define (read-magic-bytes source n)
    "Read first n bytes from source (path or bytevector).
     Returns bytevector or #f on error."
    (guard (exn [#t #f])
      (cond
        ((bytevector? source)
         ;; Already raw bytes
         (if (<= (bytevector-length source) n)
             source
             (let ((buf (make-bytevector n 0)))
               (bytevector-copy! source 0 buf 0 n)
               buf)))
        ((string? source)
         (if (file-exists? source)
             ;; It's a file path - read binary
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
                               (loop (+ i 1)))))))))
             ;; It's raw bytes as a string (Latin-1)
             (let* ((len (min n (string-length source)))
                    (buf (make-bytevector len 0)))
               (let loop ((i 0))
                 (if (>= i len) buf
                     (begin
                       (bytevector-u8-set! buf i (char->integer (string-ref source i)))
                       (loop (+ i 1))))))))
        (else #f))))

  (define (match-pattern bytes pattern)
    "Check if bytes match pattern at specified offset.
     Pattern format: (symbol mime offset byte1 byte2 ...)"
    (let ((offset (caddr pattern))
          (magic (cdddr pattern))
          (len (bytevector-length bytes)))
      (let loop ((i 0) (m magic))
        (cond
          ((null? m) #t)  ; all bytes matched
          ((>= (+ offset i) len) #f)  ; not enough bytes
          ((not (= (bytevector-u8-ref bytes (+ offset i)) (car m))) #f)
          (else (loop (+ i 1) (cdr m)))))))

  (define (magic-type source)
    "Detect type from magic bytes. Returns symbol or #f."
    (let ((bytes (read-magic-bytes source 300)))  ; enough for tar at 257
      (and bytes
           (let loop ((patterns *magic-patterns*))
             (cond
               ((null? patterns) #f)
               ((match-pattern bytes (car patterns))
                (caar patterns))
               (else (loop (cdr patterns))))))))

  (define (magic-mime source)
    "Detect MIME type from magic bytes. Returns string or #f."
    (let ((bytes (read-magic-bytes source 300)))
      (and bytes
           (let loop ((patterns *magic-patterns*))
             (cond
               ((null? patterns) #f)
               ((match-pattern bytes (car patterns))
                (cadar patterns))
               (else (loop (cdr patterns))))))))

  ;; ============================================================
  ;; Type Predicates
  ;; ============================================================

  (define (make-type-predicate type)
    (lambda (source)
      (eq? (magic-type source) type)))

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

  ;; Multi-pattern predicates
  (define (tiff? source)
    (let ((t (magic-type source)))
      (or (eq? t 'tiff-le) (eq? t 'tiff-be))))

  (define (mp3? source)
    (let ((t (magic-type source)))
      (or (eq? t 'mp3-id3) (eq? t 'mp3-sync))))

  (define (mp4? source)
    (eq? (magic-type source) 'mp4))

  (define (wav? source)
    ;; RIFF + check for WAVE at offset 8
    (let ((bytes (read-magic-bytes source 12)))
      (and bytes
           (>= (bytevector-length bytes) 12)
           (= (bytevector-u8-ref bytes 0) #x52)   ; R
           (= (bytevector-u8-ref bytes 1) #x49)   ; I
           (= (bytevector-u8-ref bytes 2) #x46)   ; F
           (= (bytevector-u8-ref bytes 3) #x46)   ; F
           (= (bytevector-u8-ref bytes 8) #x57)   ; W
           (= (bytevector-u8-ref bytes 9) #x41)   ; A
           (= (bytevector-u8-ref bytes 10) #x56)  ; V
           (= (bytevector-u8-ref bytes 11) #x45)))) ; E

  (define (mach-o? source)
    (let ((t (magic-type source)))
      (or (eq? t 'mach-o) (eq? t 'mach-o64) (eq? t 'mach-fat))))

  ;; Legacy aliases
  (define pdf-magic? pdf?)
  (define gzip-magic? gzip?)

  ;; ============================================================
  ;; Category Predicates
  ;; ============================================================

  (define (image? source)
    (let ((t (magic-type source)))
      (memq t '(png jpeg gif webp tiff-le tiff-be bmp ico psd svg))))

  (define (audio? source)
    (let ((t (magic-type source)))
      (memq t '(mp3-id3 mp3-sync ogg flac wav aiff midi m4a))))

  (define (video? source)
    (let ((t (magic-type source)))
      (memq t '(mp4 webm mkv avi mov flv))))

  (define (archive? source)
    (let ((t (magic-type source)))
      (memq t '(gzip zip rar sevenz xz bz2 zstd lz4 tar ar cab dmg))))

  (define (executable? source)
    (let ((t (magic-type source)))
      (memq t '(elf mach-o mach-o64 mach-fat pe shebang wasm class dex))))

  (define (document? source)
    (let ((t (magic-type source)))
      (memq t '(pdf ps rtf))))

  ;; ============================================================
  ;; Text-Based Detection (Heuristics)
  ;; ============================================================

  (define (looks-like-text? bytes)
    "Check if bytes look like text (UTF-8 or ASCII)."
    (let ((len (bytevector-length bytes)))
      (let loop ((i 0) (text-chars 0) (binary-chars 0))
        (cond
          ((>= i len)
           (and (> text-chars 0)
                (< binary-chars (* text-chars 0.1))))  ; <10% binary
          (else
           (let ((b (bytevector-u8-ref bytes i)))
             (cond
               ;; Common text bytes
               ((or (and (>= b 32) (<= b 126))  ; printable ASCII
                    (= b 9) (= b 10) (= b 13))   ; tab, LF, CR
                (loop (+ i 1) (+ text-chars 1) binary-chars))
               ;; UTF-8 continuation bytes (10xxxxxx) are ok
               ((and (>= b #x80) (<= b #xbf))
                (loop (+ i 1) text-chars binary-chars))
               ;; UTF-8 lead bytes
               ((and (>= b #xc0) (<= b #xf7))
                (loop (+ i 1) text-chars binary-chars))
               ;; Binary
               (else
                (loop (+ i 1) text-chars (+ binary-chars 1))))))))))

  (define (xml? source)
    "Check for XML (starts with <?xml or BOM + <?xml)."
    (let ((bytes (read-magic-bytes source 50)))
      (and bytes
           (>= (bytevector-length bytes) 5)
           (or ;; <?xml
               (and (= (bytevector-u8-ref bytes 0) #x3c)
                    (= (bytevector-u8-ref bytes 1) #x3f)
                    (= (bytevector-u8-ref bytes 2) #x78)
                    (= (bytevector-u8-ref bytes 3) #x6d)
                    (= (bytevector-u8-ref bytes 4) #x6c))
               ;; UTF-8 BOM + <?xml
               (and (>= (bytevector-length bytes) 8)
                    (= (bytevector-u8-ref bytes 0) #xef)
                    (= (bytevector-u8-ref bytes 1) #xbb)
                    (= (bytevector-u8-ref bytes 2) #xbf)
                    (= (bytevector-u8-ref bytes 3) #x3c)
                    (= (bytevector-u8-ref bytes 4) #x3f))))))

  (define (bv->ascii-string bytes)
    "Convert bytevector to ASCII string (for text detection)."
    (let ((len (bytevector-length bytes)))
      (let loop ((i 0) (chars '()))
        (if (>= i len)
            (list->string (reverse chars))
            (loop (+ i 1)
                  (cons (integer->char (bytevector-u8-ref bytes i)) chars))))))

  (define (string-upcase str)
    (list->string (map char-upcase (string->list str))))

  (define (string-contains-ci haystack needle)
    (string-contains (string-downcase haystack) (string-downcase needle)))

  (define (string-downcase str)
    (list->string (map char-downcase (string->list str))))

  (define (html? source)
    "Check for HTML (starts with <!DOCTYPE or <html)."
    (let ((bytes (read-magic-bytes source 100)))
      (and bytes
           (looks-like-text? bytes)
           (let ((s (bv->ascii-string bytes)))
             (or (string-prefix? "<!DOCTYPE" (string-upcase s))
                 (string-prefix? "<HTML" (string-upcase s))
                 (string-contains-ci s "<html"))))))

  (define (json? source)
    "Check for JSON (starts with { or [, text content)."
    (let ((bytes (read-magic-bytes source 100)))
      (and bytes
           (> (bytevector-length bytes) 0)
           (looks-like-text? bytes)
           (let ((first (bytevector-u8-ref bytes 0)))
             (or (= first #x7b)    ; {
                 (= first #x5b)))))) ; [

  ;; ============================================================
  ;; Full Detection (Shell to file(1))
  ;; ============================================================

  (define (file-command path flag)
    "Run file command and return trimmed output."
    (let ((result (shell-command
                   (string-append "file " flag " '"
                                  path "' 2>/dev/null"))))
      (and result (string-trim-both result))))

  (define (file-mime path)
    "Get MIME type using file command."
    (or (magic-mime path)  ; try fast path first
        (file-command path "-b --mime-type")
        "application/octet-stream"))

  (define (file-description path)
    "Get human-readable description using file command."
    (or (file-command path "-b")
        "data"))

  (define (file-type path)
    "Get both MIME type and description.
     Returns (mime . description) pair."
    (let ((mime (file-mime path))
          (desc (file-description path)))
      (cons mime desc)))

) ;; end library
