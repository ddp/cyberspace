;;; smelter.scm - Compile word lists into Forge digraph databases
;;;
;;; The smelter reads dictionaries and extracts digraph statistics
;;; for the Forge pronounceable password generator.
;;;
;;; Heritage: VAX/VMS TPU smelter (Jon Callas, circa 1991)
;;; Rewritten in pure Scheme for Cyberspace.
;;;
;;; Usage:
;;;   (smelt "english.txt" "english.db")
;;;   (smelt-preview "english.txt" 10)  ; preview first 10 entries
;;;

(module smelter
  (;; Main entry point
   smelt
   smelt-preview

   ;; Utilities
   word->digraphs
   valid-word?)

  (import scheme
          (chicken base)
          (chicken io)
          (chicken format)
          (chicken string)
          (chicken file)
          (chicken sort)
          srfi-1
          srfi-13
          srfi-69)

  ;; ============================================================
  ;; Configuration
  ;; ============================================================

  (define *min-word-length* 3)
  ;; Extended character set: ASCII + common diacriticals (UTF-8)
  ;; Covers: Latin-1 Supplement, Latin Extended-A (subset)
  (define *legit-chars*
    (string-append
      "abcdefghijklmnopqrstuvwxyz'-"
      "àáâãäåæçèéêëìíîïðñòóôõöøùúûüýþÿ"  ; Latin-1 lower
      "œ"                                   ; Latin Extended
      "āēīōūăĕĭŏŭ"                         ; macrons/breves for Latin
      "ŷŵ"                                  ; Welsh
      "ñ"))

  ;; ============================================================
  ;; Word Validation
  ;; ============================================================

  (define (valid-char? c)
    "Check if character/byte is valid for digraph analysis"
    ;; CHICKEN treats UTF-8 as bytes, so we accept:
    ;; - ASCII letters (a-z, A-Z)
    ;; - UTF-8 lead bytes (0xC0-0xF4) and continuation bytes (0x80-0xBF)
    ;; - apostrophe and hyphen
    (let ((b (char->integer c)))
      (or (and (>= b #x41) (<= b #x5A))    ; A-Z
          (and (>= b #x61) (<= b #x7A))    ; a-z
          (and (>= b #x80) (<= b #xBF))    ; UTF-8 continuation bytes
          (and (>= b #xC0) (<= b #xF4))    ; UTF-8 lead bytes
          (char=? c #\')
          (char=? c #\-))))

  (define (valid-word? word)
    "Check if word is suitable for analysis"
    (and (>= (string-length word) *min-word-length*)
         (every valid-char? (string->list (string-downcase word)))))

  ;; ============================================================
  ;; Digraph Extraction
  ;; ============================================================

  (define (word->digraphs word)
    "Extract digraphs from word, including terminal marker"
    (let* ((w (string-downcase word))
           (len (string-length w)))
      (if (< len 2)
          '()
          (let loop ((i 0) (acc '()))
            (if (>= i (- len 1))
                ;; Add terminal digraph (last char + period)
                (reverse (cons (string (string-ref w (- len 1)) #\.) acc))
                (loop (+ i 1)
                      (cons (string (string-ref w i) (string-ref w (+ i 1)))
                            acc)))))))

  (define (starting-digraph word)
    "Get the starting digraph of a word"
    (let ((w (string-downcase word)))
      (if (< (string-length w) 2)
          #f
          (string (string-ref w 0) (string-ref w 1)))))

  ;; ============================================================
  ;; Statistics Collection
  ;; ============================================================

  (define (collect-stats words)
    "Collect digraph statistics from word list.
     Returns: (nstart pairs-table)
     pairs-table: digraph -> (npairs nstart entries)
     entries: hash-table char -> count"
    (let ((pairs (make-hash-table string=?))
          (nstart 0))

      (for-each
        (lambda (word)
          (when (valid-word? word)
            ;; Count starting digraph
            (let ((start (starting-digraph word)))
              (when start
                (set! nstart (+ nstart 1))
                (let ((entry (hash-table-ref/default pairs start #f)))
                  (if entry
                      ;; Increment nstart count
                      (vector-set! entry 1 (+ (vector-ref entry 1) 1))
                      ;; Create new entry: #(npairs nstart entries-hash)
                      (hash-table-set! pairs start
                                       (vector 0 1 (make-hash-table equal?)))))))

            ;; Count all digraphs and their following characters
            (let* ((digraphs (word->digraphs word)))
              (let loop ((dgs digraphs))
                (when (pair? dgs)
                  (let* ((dg (car dgs))
                         (next-char (if (null? (cdr dgs))
                                        #\.  ; terminal
                                        (string-ref (cadr dgs) 1))))
                    ;; Ensure entry exists
                    (unless (hash-table-exists? pairs dg)
                      (hash-table-set! pairs dg (vector 0 0 (make-hash-table equal?))))
                    ;; Update counts
                    (let* ((entry (hash-table-ref pairs dg))
                           (entries (vector-ref entry 2))
                           (old-count (hash-table-ref/default entries next-char 0)))
                      (vector-set! entry 0 (+ (vector-ref entry 0) 1))  ; npairs
                      (hash-table-set! entries next-char (+ old-count 1))))
                  (loop (cdr dgs)))))))
        words)

      (values nstart pairs)))

  ;; ============================================================
  ;; Database Output
  ;; ============================================================

  (define (write-db-header port nstart npairs minword)
    "Write database header"
    (fprintf port "; Number of start pairs is ~a.~n" nstart)
    (fprintf port "; Number of pair entries is ~a.~n" npairs)
    (fprintf port "; Number of allocated pairs is ~a.~n" (+ npairs 100))
    (fprintf port "; Min word size is ~a.~n" minword)
    (fprintf port "; Legit characters are ~s.~n" *legit-chars*)
    (fprintf port "; Num-Start Num-Pairs Allocated-Pairs Min-Word-Size Legit-Chars~n")
    (fprintf port "~a ~a ~a ~a ~s" nstart npairs (+ npairs 100) minword *legit-chars*)
    (fprintf port "; Pairs:~n")
    (fprintf port "; text npairs nstart nentry (e-char e-count...)~n"))

  (define (pad-num n width)
    "Right-pad number to width"
    (string-pad (number->string n) width))

  (define (write-pair-entry port digraph entry)
    "Write a single pair entry line"
    (let* ((npairs (vector-ref entry 0))
           (nstart (vector-ref entry 1))
           (entries-hash (vector-ref entry 2))
           (entries (hash-table->alist entries-hash))
           (nentry (length entries)))
      ;; Format: XX npairs nstart nentry char count char count ...
      (fprintf port "~a ~a ~a ~a"
               digraph (pad-num npairs 8) (pad-num nstart 9) (pad-num nentry 9))
      (for-each
        (lambda (e)
          (fprintf port " ~a ~a" (car e) (cdr e)))
        (sort entries (lambda (a b) (> (cdr a) (cdr b)))))  ; sort by count desc
      (fprintf port " ~n")))

  ;; ============================================================
  ;; Main Entry Points
  ;; ============================================================

  (define (load-words filename)
    "Load words from file (one per line)"
    (call-with-input-file filename
      (lambda (port)
        (let loop ((acc '()))
          (let ((line (read-line port)))
            (if (eof-object? line)
                (reverse acc)
                (let ((word (string-trim-both line)))
                  (if (string-null? word)
                      (loop acc)
                      (loop (cons word acc))))))))))

  (define (smelt input-file output-file)
    "Compile word list into forge database"
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
          (call-with-output-file output-file
            (lambda (port)
              (write-db-header port nstart npairs *min-word-length*)
              (for-each
                (lambda (dg)
                  (write-pair-entry port dg (hash-table-ref pairs dg)))
                (sort (hash-table-keys pairs) string<?))))

          (printf "Done.~n")
          (list nstart npairs)))))

  (define (smelt-preview input-file n)
    "Preview digraph statistics without writing"
    (let ((words (load-words input-file)))
      (printf "~a words, ~a valid~n"
              (length words)
              (count valid-word? words))
      (let-values (((nstart pairs) (collect-stats words)))
        (printf "~a start, ~a digraphs~n" nstart (hash-table-size pairs))
        (printf "~nFirst ~a digraphs:~n" n)
        (let ((sorted (sort (hash-table-keys pairs) string<?)))
          (for-each
            (lambda (dg)
              (let ((e (hash-table-ref pairs dg)))
                (printf "  ~a: ~a pairs, ~a starts~n"
                        dg (vector-ref e 0) (vector-ref e 1))))
            (take sorted (min n (length sorted))))))))

) ;; end module
