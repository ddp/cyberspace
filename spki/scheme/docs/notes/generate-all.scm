#!/usr/bin/env csi -q
;;; generate-all.scm - Generate all Memo formats from S-expression sources
;;;
;;; Usage: csi -q generate-all.scm
;;;
;;; Processes all memo-*.scm files and generates .txt, .html, .ps

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

(load "memo-format.scm")

(define (discover-memos)
  "Find all Memo S-expression source files."
  (let ((files (glob "memo-*.scm")))
    (sort (filter (lambda (f)
                    (and (not (string=? f "memo-format.scm"))
                         (not (string=? f "md2scm.scm"))
                         (not (string=? f "generate-all.scm"))))
                  files)
          string<?)))

(define (memo-number filename)
  "Extract Memo number from filename for sorting."
  (let ((m (irregex-match "memo-([0-9]+)" filename)))
    (if m
        (string->number (irregex-match-substring m 1))
        999)))

(define (file-newer? source target)
  "Check if source is newer than target."
  (or (not (file-exists? target))
      (> (file-modification-time source)
         (file-modification-time target))))

(define (generate-memo memo-file)
  "Generate all formats for one Memo."
  (let* ((base (pathname-strip-extension memo-file))
         (txt-file (string-append base ".txt"))
         (html-file (string-append base ".html"))
         (ps-file (string-append base ".ps")))

    ;; Check if regeneration needed (also check formatter itself)
    (when (or (file-newer? memo-file txt-file)
              (file-newer? memo-file html-file)
              (file-newer? memo-file ps-file)
              (file-newer? "memo-format.scm" txt-file))

      (condition-case
        (let ((doc (read-memo memo-file)))
          (if (assq 'reserved (cdr doc))
              (print "  " base ": <reserved>")
              (begin
                (let ((title-warnings (validate-memo doc memo-file)))
                  (for-each (lambda (w) (print "  [TITLE] " w)) title-warnings))
                (memo->txt doc txt-file)
                (memo->html doc html-file)
                (memo->ps doc ps-file)
                (print "  " base ": txt html ps"))))
        (e ()
          (print "  " base ": FAILED - " (get-condition-property e 'exn 'message "")))))))

(define (discover-docs)
  "Find non-Memo document files."
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

(define (is-eluded? base)
  (let ((scm-file (string-append base ".scm")))
    (and (file-exists? scm-file)
         (let ((doc (with-input-from-file scm-file read)))
           (and (pair? doc) (assq 'reserved (cdr doc)))))))

(define (validate-outputs base)
  "Validate all output files for a Memo."
  (cond
    ((is-eluded? base) #t)
    (else
     (let* ((txt-file (string-append base ".txt"))
            (errors (if (file-exists? txt-file)
                        (validate-txt-file txt-file)
                        '("txt file missing"))))
       (when (not (null? errors))
         (print "  [WARN] " base ": " (string-intersperse errors ", ")))
       (null? errors)))))

(define (check-duplicate-numbers memos)
  "Fail fast if any memo numbers are duplicated."
  (let* ((numbers (map memo-number memos))
         (seen '())
         (dupes '()))
    (for-each (lambda (n f)
                (if (member n seen)
                    (set! dupes (cons n dupes))
                    (set! seen (cons n seen))))
              numbers memos)
    (when (not (null? dupes))
      (print "")
      (print "*** ERROR: Duplicate memo numbers detected! ***")
      (for-each (lambda (n)
                  (print "  " (string-pad (number->string n) 4 #\0) ": "
                         (string-intersperse
                           (filter (lambda (f) (= (memo-number f) n)) memos)
                           ", ")))
                (delete-duplicates (reverse dupes)))
      (print "")
      (print "The Ten Commandments (0000-0009) are fixed:")
      (print "  0000 Declaration")
      (print "  0001 Conventions")
      (print "  0002 Architecture")
      (print "  0003 Public Key Authorization")
      (print "  0004 Shamir Sharing")
      (print "  0005 Audit Trail")
      (print "  0006 Vault Architecture")
      (print "  0007 Replication Layer")
      (print "  0008 Threshold Governance")
      (print "  0009 Designer Notes")
      (print "")
      (print "Fix duplicates before regenerating.")
      (exit 1))))

(define (main)
  (print "=== Memo Generation (S-expression Pipeline) ===")
  (print "")

  (let* ((start-time (current-milliseconds))
         (memos (discover-memos))
         (docs (discover-docs))
         (all-files (append memos docs)))

    ;; Fail fast on duplicate numbers
    (check-duplicate-numbers memos)

    (print "Found " (length memos) " Memos, " (length docs) " docs")
    (print "")

    (for-each generate-memo all-files)

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
      (print "  TXT:  " (length (glob "memo-*.txt")))
      (print "  HTML: " (length (glob "memo-*.html")))
      (print "  PS:   " (length (glob "memo-*.ps"))))))

(main)
