#!/usr/bin/env csi -s
;;; sanity.scm - Library coherence checks
;;;
;;; Run during build to verify self-referential consistency:
;;; - Memo numbering (no gaps, internal matches filename)
;;; - Cross-references (no dangling refs)
;;; - Module exports (all defined and accessible)
;;;
;;; Usage: ./sanity.scm

(import scheme
        (chicken base)
        (chicken io)
        (chicken file)
        (chicken pathname)
        (chicken string)
        (chicken format)
        (chicken sort)
        (chicken process)
        (chicken irregex)
        srfi-1
        srfi-13)

(define *errors* 0)
(define *warnings* 0)
(define *max-memo* 9999)  ; memo namespace: 0-9999

(define (error! msg)
  (set! *errors* (+ *errors* 1))
  (printf "  ERROR: ~a~n" msg))

(define (warn! msg)
  (set! *warnings* (+ *warnings* 1))
  (printf "  WARN:  ~a~n" msg))

(define (ok! msg)
  (printf "  OK:    ~a~n" msg))

;;; ============================================================
;;; Memo Checks
;;; ============================================================

(define (memo-files)
  "List all memo-NNN-*.scm files sorted"
  (let ((dir "docs/notes"))
    (if (directory-exists? dir)
        (sort
          (filter (lambda (f)
                    (irregex-match "^memo-[0-9]{4}-.*\\.scm$" f))
                  (directory dir))
          string<?)
        '())))

(define (extract-number-from-filename f)
  "memo-042-foo.scm -> 42"
  (let ((m (irregex-search "memo-([0-9]{4})-" f)))
    (and m (string->number (irregex-match-substring m 1)))))

(define (extract-number-from-content path)
  "Read (number N) from memo file"
  (let ((content (with-input-from-file path read-string)))
    (let ((m (irregex-search "\\(number ([0-9]+)\\)" content)))
      (and m (string->number (irregex-match-substring m 1))))))

(define (check-memo-numbering)
  (print "\n=== Memo Numbering ===")
  (let ((files (memo-files)))
    (printf "  Found ~a memo files~n" (length files))

    ;; Check each file: internal number should match filename
    (for-each
      (lambda (f)
        (let* ((path (make-pathname "docs/notes" f))
               (fn-num (extract-number-from-filename f))
               (internal (extract-number-from-content path)))
          (when (and fn-num internal (not (= fn-num internal)))
            (error! (sprintf "~a: (number ~a) != filename ~a" f internal fn-num)))))
      files)

    ;; Check for gaps in sequence
    (let ((nums (filter-map extract-number-from-filename files)))
      (when (pair? nums)
        (let ((min-n (apply min nums))
              (max-n (apply max nums)))
          (let loop ((i min-n))
            (when (<= i max-n)
              (unless (member i nums)
                (warn! (sprintf "Gap in sequence: memo ~a missing" i)))
              (loop (+ i 1)))))))

    (if (zero? *errors*)
        (ok! "All memo numbers consistent")
        (printf "  ~a numbering errors~n" *errors*))))

(define (check-cross-references)
  (print "\n=== Cross-References ===")
  (let ((existing (filter-map extract-number-from-filename (memo-files)))
        (refs '()))

    ;; Collect all Memo-NNN references (1-4 digits)
    (for-each
      (lambda (f)
        (let* ((path (make-pathname "docs/notes" f))
               (content (with-input-from-file path read-string)))
          (irregex-fold
            "Memo-([0-9]{1,4})"
            (lambda (i m acc)
              (set! refs (cons (string->number (irregex-match-substring m 1)) refs)))
            #f content)))
      (memo-files))

    ;; Check refs against existing (only in cyberspace range, not IETF RFCs)
    (let ((cyberspace-refs (filter (lambda (n) (<= n 100)) (delete-duplicates refs))))
      (for-each
        (lambda (n)
          (unless (member n existing)
            (warn! (sprintf "Reference to Memo-~a but file doesn't exist" n))))
        cyberspace-refs))

    (ok! (sprintf "Checked ~a cross-references" (length refs)))))

;;; ============================================================
;;; Module Checks
;;; ============================================================

(define (check-module-exports)
  (print "\n=== Module Exports ===")

  ;; Test os module exports
  (let ((result (with-input-from-pipe
                  "csi -q -e \"(import os) (print (and (procedure? open-keychain) (procedure? open-tickets) (procedure? open-console) (procedure? open-monitor) (procedure? open-finder)))\" 2>&1 | tail -1"
                  read-line)))
    (if (equal? result "#t")
        (ok! "os: system utilities exported")
        (error! (sprintf "os: export check failed (~a)" result))))

  ;; Test core modules load
  (for-each
    (lambda (mod)
      (let* ((cmd (sprintf "csi -q -e \"(import ~a) (print 'ok)\" 2>&1 | tail -1" mod))
             (result (with-input-from-pipe cmd read-line)))
        (if (equal? result "ok")
            (ok! (sprintf "~a: loads" mod))
            (error! (sprintf "~a: failed" mod)))))
    '(sexp crypto-ffi vault audit cert)))

;;; ============================================================
;;; Boot Regression Tests
;;; ============================================================
;;; These catch errors like missing imports that only surface at runtime.

(define (check-repl-boot)
  (print "\n=== REPL Boot Test ===")

  ;; Test 1: REPL can reach prompt without error (shadow mode, immediate exit)
  (let* ((cmd "echo '(exit 0)' | ./repl shadow 2>&1")
         (output (with-input-from-pipe cmd read-string)))
    (if (string-contains output "Error:")
        (error! "REPL boot failed - check for unbound symbols")
        (ok! "REPL boots without error")))

  ;; Test 2: os module exports hostname (caught the hostname bug)
  (let* ((cmd "csi -q -e \"(import os) (print (hostname))\" 2>&1")
         (output (with-input-from-pipe cmd read-string)))
    (if (string-contains output "Error")
        (error! "os: hostname not exported")
        (ok! "os: hostname available")))

  ;; Test 3: No deprecated API warnings in compile
  (let* ((cmd "csc -check-syntax repl.scm 2>&1 | grep -c 'deprecated' || echo 0")
         (result (with-input-from-pipe cmd read-line)))
    (if (equal? result "0")
        (ok! "No deprecated API usage")
        (warn! (sprintf "~a deprecated API warnings" result)))))

;;; ============================================================
;;; Main
;;; ============================================================

(define (main)
  (print "\n==============================")
  (print "   Library Sanity Check")
  (print "==============================")

  (check-memo-numbering)
  (check-cross-references)
  (check-module-exports)
  (check-repl-boot)

  (print "\n=== Summary ===")
  (printf "  Errors:   ~a~n" *errors*)
  (printf "  Warnings: ~a~n" *warnings*)

  (if (zero? *errors*)
      (begin
        (print "\n  Library is coherent.")
        (exit 0))
      (begin
        (print "\n  Library has issues.")
        (exit 1))))

(main)
