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

(define (main)
  (print "=== RFC Generation (S-expression Pipeline) ===")
  (print "")

  (let* ((start-time (current-milliseconds))
         (rfcs (discover-rfcs))
         (docs (discover-docs)))
    (print "Found " (length rfcs) " RFCs, " (length docs) " docs")
    (print "")

    (for-each generate-rfc rfcs)
    (for-each generate-rfc docs)

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
