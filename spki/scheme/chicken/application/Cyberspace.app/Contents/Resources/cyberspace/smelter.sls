;;; smelter.sls - Compile word lists into Forge digraph databases
;;;
;;; Heritage: VAX/VMS TPU smelter (Jon Callas, circa 1991)
;;; Rewritten in pure Scheme for Cyberspace.
;;;
;;; Usage:
;;;   (smelt "english.txt" "english.db")
;;;   (smelt-preview "english.txt" 10)

(library (cyberspace smelter)
  (export
    smelt
    smelt-preview
    word->digraphs
    valid-word?)

  (import (rnrs)
          (only (chezscheme) printf format sort)
          (cyberspace chicken-compatibility hash-table))

  ;; ============================================================
  ;; Inlined helpers
  ;; ============================================================

  (define (every pred lst)
    (or (null? lst)
        (and (pred (car lst))
             (every pred (cdr lst)))))

  (define (count pred lst)
    (let loop ((l lst) (n 0))
      (if (null? l) n
          (loop (cdr l) (if (pred (car l)) (+ n 1) n)))))

  (define (take lst n)
    (if (or (zero? n) (null? lst)) '()
        (cons (car lst) (take (cdr lst) (- n 1)))))

  (define (string-null? s) (string=? s ""))

  (define (string-trim-both s)
    (let* ((len (string-length s))
           (start (let loop ((i 0))
                    (if (or (= i len) (not (char-whitespace? (string-ref s i)))) i
                        (loop (+ i 1)))))
           (end (let loop ((i (- len 1)))
                  (if (or (< i start) (not (char-whitespace? (string-ref s i)))) (+ i 1)
                      (loop (- i 1))))))
      (substring s start end)))

  (define (string-prefix? prefix s)
    (and (>= (string-length s) (string-length prefix))
         (string=? prefix (substring s 0 (string-length prefix)))))

  (define (string-suffix? suffix s)
    (let ((slen (string-length s))
          (plen (string-length suffix)))
      (and (>= slen plen)
           (string=? suffix (substring s (- slen plen) slen)))))

  ;; Simple string-pad: right-pad a string to width
  (define (string-pad s width)
    (let ((len (string-length s)))
      (if (>= len width) s
          (string-append (make-string (- width len) #\space) s))))

  ;; string-tokenize: split on whitespace
  (define (string-tokenize s)
    (let ((len (string-length s)))
      (let loop ((i 0) (start #f) (acc '()))
        (cond
          ((= i len)
           (reverse (if start (cons (substring s start i) acc) acc)))
          ((char-whitespace? (string-ref s i))
           (loop (+ i 1) #f
                 (if start (cons (substring s start i) acc) acc)))
          (else
           (loop (+ i 1) (or start i) acc))))))

  ;; ============================================================
  ;; Configuration
  ;; ============================================================

  (define *min-word-length* 3)

  (define *legit-chars*
    (string-append
      "abcdefghijklmnopqrstuvwxyz'-"
      "\x00e0;\x00e1;\x00e2;\x00e3;\x00e4;\x00e5;\x00e6;\x00e7;"
      "\x00e8;\x00e9;\x00ea;\x00eb;\x00ec;\x00ed;\x00ee;\x00ef;"
      "\x00f0;\x00f1;\x00f2;\x00f3;\x00f4;\x00f5;\x00f6;\x00f8;"
      "\x00f9;\x00fa;\x00fb;\x00fc;\x00fd;\x00fe;\x00ff;"
      "\x0153;"
      "\x0101;\x0113;\x012b;\x014d;\x016b;\x0103;\x0115;\x012d;\x014f;\x016d;"
      "\x0177;\x0175;"
      "\x00f1;"))

  ;; ============================================================
  ;; Word Validation
  ;; ============================================================

  (define (valid-char? c)
    (let ((cp (char->integer c)))
      (or (char-alphabetic? c)
          (char=? c #\')
          (char=? c #\-)
          (and (>= cp #x00C0) (<= cp #x024F))
          (and (>= cp #x0370) (<= cp #x03FF))
          (and (>= cp #x0400) (<= cp #x04FF))
          (and (>= cp #x0530) (<= cp #x058F))
          (and (>= cp #x0E00) (<= cp #x0E7F))
          (and (>= cp #x0E80) (<= cp #x0EFF))
          (and (>= cp #x0900) (<= cp #x097F))
          (and (>= cp #xAC00) (<= cp #xD7AF))
          (and (>= cp #x1100) (<= cp #x11FF))
          (and (>= cp #x1E00) (<= cp #x1EFF)))))

  (define (valid-word? word)
    (guard (exn [#t #f])
      (and (>= (string-length word) *min-word-length*)
           (every valid-char? (string->list (string-downcase word))))))

  ;; ============================================================
  ;; Digraph Extraction
  ;; ============================================================

  (define (word->digraphs word)
    (guard (exn [#t '()])
      (let* ((w (string-downcase word))
             (len (string-length w)))
        (if (< len 2)
            '()
            (let loop ((i 0) (acc '()))
              (if (>= i (- len 1))
                  (reverse (cons (string (string-ref w (- len 1)) #\.) acc))
                  (loop (+ i 1)
                        (cons (string (string-ref w i) (string-ref w (+ i 1)))
                              acc))))))))

  (define (starting-digraph word)
    (guard (exn [#t #f])
      (let ((w (string-downcase word)))
        (if (< (string-length w) 2) #f
            (string (string-ref w 0) (string-ref w 1))))))

  ;; ============================================================
  ;; Statistics Collection
  ;; ============================================================

  (define (collect-stats words)
    (let ((pairs (make-hash-table string=?))
          (nstart 0))
      (for-each
        (lambda (word)
          (when (valid-word? word)
            (let ((start (starting-digraph word)))
              (when start
                (set! nstart (+ nstart 1))
                (let ((entry (hash-table-ref/default pairs start #f)))
                  (if entry
                      (vector-set! entry 1 (+ (vector-ref entry 1) 1))
                      (hash-table-set! pairs start
                                       (vector 0 1 (make-hash-table)))))))
            (let ((digraphs (word->digraphs word)))
              (let loop ((dgs digraphs))
                (when (pair? dgs)
                  (let* ((dg (car dgs))
                         (next-char (if (null? (cdr dgs))
                                        #\.
                                        (string-ref (cadr dgs) 1))))
                    (unless (hash-table-exists? pairs dg)
                      (hash-table-set! pairs dg (vector 0 0 (make-hash-table))))
                    (let* ((entry (hash-table-ref pairs dg))
                           (entries (vector-ref entry 2))
                           (old-count (hash-table-ref/default entries next-char 0)))
                      (vector-set! entry 0 (+ (vector-ref entry 0) 1))
                      (hash-table-set! entries next-char (+ old-count 1))))
                  (loop (cdr dgs)))))))
        words)
      (values nstart pairs)))

  ;; ============================================================
  ;; Database Output
  ;; ============================================================

  (define (write-db-header port nstart npairs minword)
    (format port "; Number of start pairs is ~a.~n" nstart)
    (format port "; Number of pair entries is ~a.~n" npairs)
    (format port "; Number of allocated pairs is ~a.~n" (+ npairs 100))
    (format port "; Min word size is ~a.~n" minword)
    (format port "; Legit characters are ~s.~n" *legit-chars*)
    (format port "; Num-Start Num-Pairs Allocated-Pairs Min-Word-Size Legit-Chars~n")
    (format port "~a ~a ~a ~a ~s" nstart npairs (+ npairs 100) minword *legit-chars*)
    (format port "; Pairs:~n")
    (format port "; text npairs nstart nentry (e-char e-count...)~n"))

  (define (write-pair-entry port digraph entry)
    (let* ((npairs (vector-ref entry 0))
           (nstart (vector-ref entry 1))
           (entries-hash (vector-ref entry 2))
           (entries (hash-table-map entries-hash cons))
           (sorted-entries (sort (lambda (a b) (> (cdr a) (cdr b))) entries)))
      (write (list digraph npairs nstart
                   (map (lambda (e) (cons (string (car e)) (cdr e)))
                        sorted-entries))
             port)
      (newline port)))

  ;; ============================================================
  ;; Main Entry Points
  ;; ============================================================

  (define (load-words filename)
    (with-input-from-file filename
      (lambda ()
        (let loop ((acc '()))
          (let ((line (get-line (current-input-port))))
            (if (eof-object? line)
                (reverse acc)
                (let ((word (string-trim-both line)))
                  (if (string-null? word)
                      (loop acc)
                      (loop (cons word acc))))))))))

  (define (smelt input-file output-file)
    (printf "Loading ~a...~n" input-file)
    (let ((words (load-words input-file)))
      (printf "  ~a words loaded~n" (length words))
      (let ((valid-count (count valid-word? words)))
        (printf "  ~a valid words (length >= ~a)~n" valid-count *min-word-length*))
      (printf "Collecting statistics...~n")
      (let-values (((nstart pairs) (collect-stats words)))
        (let ((npairs (hash-table-size pairs)))
          (printf "  ~a starting words~n" nstart)
          (printf "  ~a unique digraphs~n" npairs)
          (printf "Writing ~a...~n" output-file)
          (with-output-to-file output-file
            (lambda ()
              (write-db-header (current-output-port) nstart npairs *min-word-length*)
              (for-each
                (lambda (dg)
                  (write-pair-entry (current-output-port) dg (hash-table-ref pairs dg)))
                (sort string<? (hash-table-keys pairs)))))
          (printf "Done.~n")
          (list nstart npairs)))))

  (define (smelt-preview input-file n)
    (let ((words (load-words input-file)))
      (printf "~a words, ~a valid~n"
              (length words) (count valid-word? words))
      (let-values (((nstart pairs) (collect-stats words)))
        (printf "~a start, ~a digraphs~n" nstart (hash-table-size pairs))
        (printf "~nFirst ~a digraphs:~n" n)
        (let ((sorted (sort string<? (hash-table-keys pairs))))
          (for-each
            (lambda (dg)
              (let ((e (hash-table-ref pairs dg)))
                (printf "  ~a: ~a pairs, ~a starts~n"
                        dg (vector-ref e 0) (vector-ref e 1))))
            (take sorted (min n (length sorted))))))))

) ;; end library
