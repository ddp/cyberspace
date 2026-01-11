#!/usr/bin/env csi -q
;;; generate-all.scm - Generate all RFC formats from S-expression sources
;;;
;;; Usage: csi -q generate-all.scm
;;;
;;; Processes all rfc-*.scm files and generates .txt, .html, .ps

(import scheme
        (chicken base)
        (chicken io)
        (chicken file)
        (chicken file posix)
        (chicken pathname)
        (chicken sort)
        (chicken string)
        (chicken irregex)
        (chicken condition)
        (chicken time)
        srfi-1
        srfi-13)

(load "rfc-format.scm")

(define (discover-rfcs)
  "Find all RFC S-expression source files."
  (let ((files (glob "rfc-*.scm")))
    (sort (filter (lambda (f)
                    (and (not (string=? f "rfc-format.scm"))
                         (not (string=? f "md2scm.scm"))
                         (not (string=? f "generate-all.scm"))))
                  files)
          string<?)))

(define (rfc-number filename)
  "Extract RFC number from filename for sorting."
  (let ((m (irregex-match "rfc-([0-9]+)" filename)))
    (if m
        (string->number (irregex-match-substring m 1))
        999)))

(define (file-newer? source target)
  "Check if source is newer than target."
  (or (not (file-exists? target))
      (> (file-modification-time source)
         (file-modification-time target))))

(define (generate-rfc rfc-file)
  "Generate all formats for one RFC."
  (let* ((base (pathname-strip-extension rfc-file))
         (txt-file (string-append base ".txt"))
         (html-file (string-append base ".html"))
         (ps-file (string-append base ".ps")))

    ;; Check if regeneration needed
    (when (or (file-newer? rfc-file txt-file)
              (file-newer? rfc-file html-file)
              (file-newer? rfc-file ps-file))

      (condition-case
        (let ((doc (read-rfc rfc-file)))
          (rfc->txt doc txt-file)
          (rfc->html doc html-file)
          (rfc->ps doc ps-file)
          (print "  " base ": txt html ps"))
        (e ()
          (print "  " base ": FAILED - " (get-condition-property e 'exn 'message "")))))))

(define (discover-docs)
  "Find non-RFC document files."
  (filter file-exists? '("README.scm")))

;;; Validation checks
(define (validate-txt-file txt-file)
  "Validate a generated txt file for common issues."
  (let ((content (with-input-from-file txt-file read-string))
        (errors '()))
    ;; Check for embedded markdown list syntax
    (when (irregex-search "\\(p \"- [^\"]+\"\\)" content)
      (set! errors (cons "embedded markdown list syntax" errors)))
    ;; Check for truncated table cells (20 char fixed width artifact)
    (when (irregex-search "  [^ ]{20} [^ ]{20} [^ ]{18,20}$" content)
      (set! errors (cons "possible truncated table cells" errors)))
    ;; Check for minimum content length
    (when (< (string-length content) 500)
      (set! errors (cons "suspiciously short content" errors)))
    errors))

(define (validate-outputs base)
  "Validate all output files for an RFC."
  (let* ((txt-file (string-append base ".txt"))
         (errors (if (file-exists? txt-file)
                     (validate-txt-file txt-file)
                     '("txt file missing"))))
    (when (not (null? errors))
      (print "  [WARN] " base ": " (string-intersperse errors ", ")))
    (null? errors)))

(define (main)
  (print "=== RFC Generation (S-expression Pipeline) ===")
  (print "")

  (let* ((start-time (current-milliseconds))
         (rfcs (discover-rfcs))
         (docs (discover-docs))
         (all-files (append rfcs docs)))
    (print "Found " (length rfcs) " RFCs, " (length docs) " docs")
    (print "")

    (for-each generate-rfc all-files)

    ;; Validation pass
    (print "")
    (print "=== Validation ===")
    (let* ((bases (map pathname-strip-extension all-files))
           (results (map validate-outputs bases))
           (passed (length (filter identity results)))
           (failed (- (length results) passed)))
      (if (= failed 0)
          (print "  All " passed " files passed validation")
          (print "  " failed " file(s) have warnings")))

    (let* ((end-time (current-milliseconds))
           (elapsed-ms (- end-time start-time))
           (elapsed-sec (/ elapsed-ms 1000.0)))
      (print "")
      (print "Done in " (if (< elapsed-sec 1)
                            (string-append (number->string elapsed-ms) "ms")
                            (string-append (number->string elapsed-sec) "s")))
      (print "  TXT:  " (length (glob "rfc-*.txt")))
      (print "  HTML: " (length (glob "rfc-*.html")))
      (print "  PS:   " (length (glob "rfc-*.ps"))))))

(main)
