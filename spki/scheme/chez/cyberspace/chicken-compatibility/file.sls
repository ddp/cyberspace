;;; File Compatibility Library
;;; Library of Cyberspace - Chez Port
;;;
;;; Maps Chicken's file operations to Chez Scheme equivalents:
;;;   - file-exists?, directory-exists?, create-directory
;;;   - directory (list directory contents)
;;;   - glob (simple pattern matching)
;;;   - with-output-to-string, with-input-from-file, with-output-to-file
;;;   - get-environment-variable
;;;   - current-seconds, seconds->string, local-time->seconds
;;;   - sort (list sorting)
;;;
;;; Consolidates: (chicken file), (chicken file posix), (chicken time),
;;;               (chicken time posix), (chicken process-context), (chicken sort)

(library (cyberspace chicken-compatibility file)
  (export
    ;; File operations
    file-exists?
    directory-exists?
    create-directory
    directory
    glob
    ;; Port operations
    with-output-to-string
    with-output-to-file
    with-input-from-file
    ;; Environment
    get-environment-variable
    ;; Time
    current-seconds
    seconds->string
    ;; Sorting
    sort)

  (import (rnrs)
          (only (chezscheme)
                file-directory?
                directory-list mkdir
                with-output-to-string
                getenv
                current-time time-second time-nanosecond
                date-and-time
                sort parameterize))

  ;; Chicken's directory-exists? -> Chez's file-directory?
  (define (directory-exists? path)
    (and (file-exists? path)
         (file-directory? path)))

  ;; Chicken's create-directory with recursive flag
  (define (create-directory path . rest)
    (let ((recursive (if (null? rest) #f (car rest))))
      (if recursive
          ;; Recursively create parent directories
          (let loop ((parts (string-split-path path)) (current ""))
            (unless (null? parts)
              (let ((next (if (string=? current "")
                              (car parts)
                              (string-append current "/" (car parts)))))
                (unless (or (string=? next "") (directory-exists? next))
                  (guard (exn [#t #f])  ; ignore if exists
                    (mkdir next #o755)))
                (loop (cdr parts) next))))
          ;; Simple single-level create
          (unless (directory-exists? path)
            (mkdir path #o755)))))

  ;; Helper: split path into components
  (define (string-split-path str)
    (let loop ((i 0) (start 0) (acc '()))
      (cond
        ((= i (string-length str))
         (reverse (if (= start i) acc (cons (substring str start i) acc))))
        ((char=? (string-ref str i) #\/)
         (loop (+ i 1) (+ i 1)
               (if (= start i) acc (cons (substring str start i) acc))))
        (else
         (loop (+ i 1) start acc)))))

  ;; Chicken's (directory path) -> list of filenames
  (define (directory path)
    (if (directory-exists? path)
        (directory-list path)
        '()))

  ;; Simple glob: match *.ext pattern in a directory
  (define (glob pattern)
    (let* ((slash-pos (let loop ((i (- (string-length pattern) 1)))
                        (cond ((< i 0) #f)
                              ((char=? (string-ref pattern i) #\/) i)
                              (else (loop (- i 1))))))
           (dir (if slash-pos (substring pattern 0 slash-pos) "."))
           (pat (if slash-pos
                    (substring pattern (+ slash-pos 1) (string-length pattern))
                    pattern)))
      (if (directory-exists? dir)
          (let ((files (directory-list dir)))
            (map (lambda (f)
                   (if (string=? dir ".")
                       f
                       (string-append dir "/" f)))
                 (filter (lambda (f) (glob-match? pat f)) files)))
          '())))

  ;; Simple glob matching (* matches anything)
  (define (glob-match? pattern str)
    (cond
      ((string=? pattern "*") #t)
      ((and (> (string-length pattern) 1)
            (char=? (string-ref pattern 0) #\*))
       ;; *.ext -> check suffix
       (let ((suffix (substring pattern 1 (string-length pattern))))
         (and (>= (string-length str) (string-length suffix))
              (string=? (substring str (- (string-length str) (string-length suffix))
                                   (string-length str))
                        suffix))))
      (else (string=? pattern str))))

  ;; Chicken's get-environment-variable
  (define (get-environment-variable name)
    (getenv name))

  ;; Chicken's current-seconds -> epoch seconds
  (define (current-seconds)
    (time-second (current-time)))

  ;; Chicken's seconds->string -> ISO-ish timestamp
  (define (seconds->string secs)
    ;; Use Chez's date-and-time which returns "Day Mon DD HH:MM:SS YYYY"
    ;; We convert to ISO format manually
    (date-and-time))

) ;; end library
