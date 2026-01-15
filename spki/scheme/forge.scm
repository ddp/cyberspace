;;; forge.scm - Multilingual Password Generator
;;;
;;; Markov chain word generator using digraph statistics.
;;; Produces pronounceable passwords from language models.
;;;
;;; Design: Derrell Piper & Jon Callas (VAX/VMS 6.0, circa 1991)
;;; US/EU DEC patents (expired)
;;;
;;; The "smelter" compiles dictionaries into digraph databases.
;;; The "forge" generates words following those patterns.
;;; Entropy tracked in "decibits" (tenths of bits).

(module forge
  (;; Database operations
   forge-load-db
   forge-db-info

   ;; Word generation
   forge-word
   forge-words
   forge-passphrase

   ;; Easter egg
   forge

   ;; Available languages
   *forge-languages*
   *forge-db-path*)

  (import scheme
          (chicken base)
          (chicken io)
          (chicken format)
          (chicken string)
          (chicken pathname)
          (chicken process-context)
          (chicken file)
          srfi-1
          srfi-13
          srfi-69)

  ;; ============================================================
  ;; Configuration
  ;; ============================================================

  (define *forge-db-path*
    (make-parameter
      (or (get-environment-variable "FORGE_DB_PATH")
          (make-pathname (get-environment-variable "HOME")
                         "src/lisp/forge"))))

  (define *forge-languages*
    '(;; DEC heritage (VMS 1991)
      english latin italian dutch sindarin webster
      ;; Western Europe
      french german spanish portuguese
      ;; Iberia
      catalan galician basque
      ;; Alpine (Bern station)
      ;; Nordic (resistance networks)
      swedish norwegian danish finnish
      ;; Atlantic fringe
      irish welsh scottish breton
      ;; Balkans (partisan country)
      greek albanian serbian croatian slovenian macedonian
      ;; Eastern front
      polish czech slovak hungarian romanian
      ;; Baltic
      lithuanian latvian estonian
      ;; Soviet theater
      russian ukrainian bulgarian
      ;; Near East
      turkish armenian
      ;; Mediterranean (George Cross island)
      maltese
      ;; Detachment 101
      vietnamese thai lao korean
      ;; Literary
      dante))

  ;; ============================================================
  ;; Cryptographic Random Number Generator
  ;; ============================================================
  ;;
  ;; Uses /dev/urandom for cryptographically secure randomness.
  ;; Boot-time verification ensures the entropy source is sane.

  (define *urandom-path* "/dev/urandom")

  (define (read-random-bytes n)
    "Read n bytes from /dev/urandom"
    (call-with-input-file *urandom-path*
      (lambda (port)
        (let ((buf (make-string n)))
          (read-string! n buf port)
          buf))))

  (define (bytes->integer bytes)
    "Convert byte string to unsigned integer (big-endian)"
    (let loop ((i 0) (acc 0))
      (if (>= i (string-length bytes))
          acc
          (loop (+ i 1)
                (+ (* acc 256) (char->integer (string-ref bytes i)))))))

  (define (crypto-random-integer limit)
    "Generate cryptographically secure random integer in [0, limit)"
    (if (<= limit 0)
        0
        (let* ((bytes-needed (max 1 (inexact->exact (ceiling (/ (log (+ limit 1)) (log 256))))))
               (raw (bytes->integer (read-random-bytes bytes-needed))))
          (modulo raw limit))))

  (define (verify-entropy-source)
    "Boot-time verification of cryptographic entropy source.
     Returns #t if source passes sanity checks, signals error otherwise."
    (unless (file-exists? *urandom-path*)
      (error "Cryptographic entropy source not available" *urandom-path*))

    ;; Read test bytes and verify basic properties
    (let* ((test-bytes (read-random-bytes 256))
           (byte-counts (make-vector 256 0)))

      ;; Count byte frequencies
      (string-for-each
        (lambda (c)
          (let ((b (char->integer c)))
            (vector-set! byte-counts b (+ 1 (vector-ref byte-counts b)))))
        test-bytes)

      ;; Sanity check: no single byte should appear more than ~10% of the time
      ;; For 256 bytes, expected is 1 per value, max reasonable is ~25
      (let ((max-count (apply max (vector->list byte-counts))))
        (when (> max-count 25)
          (error "Entropy source failed distribution check - possible bias")))

      ;; Sanity check: should have at least 100 distinct byte values
      (let ((distinct (count positive? (vector->list byte-counts))))
        (when (< distinct 100)
          (error "Entropy source failed diversity check" distinct)))

      #t))

  ;; Verify entropy source on module load
  (verify-entropy-source)

  ;; ============================================================
  ;; Database Structure
  ;; ============================================================
  ;;
  ;; A smelter database contains:
  ;;   nstart     - total starting pairs (= words in source)
  ;;   npairs     - number of unique digraphs
  ;;   pairs      - hash table: "ab" -> (npairs nstart nentry entries)
  ;;   entries    - alist: ((#\c . count) ...)

  (define-record-type <forge-db>
    (make-forge-db-internal nstart npairs minword language pairs)
    forge-db?
    (nstart   forge-db-nstart)
    (npairs   forge-db-npairs)
    (minword  forge-db-minword)
    (language forge-db-language)
    (pairs    forge-db-pairs))

  (define (make-forge-db)
    (make-forge-db-internal 0 0 3 'unknown (make-hash-table string=?)))

  ;; ============================================================
  ;; Database Parser
  ;; ============================================================

  (define (forge-load-db language)
    "Load a smelter database file"
    (let* ((filename (sprintf "~a.db" language))
           (path (make-pathname (*forge-db-path*) filename)))
      (call-with-input-file path
        (lambda (port)
          (parse-db-file port language)))))

  (define (parse-db-file port language)
    "Parse smelter .db format"
    (let ((db (make-forge-db))
          (pairs (make-hash-table string=?)))

      ;; Skip comment lines, read header
      (let loop ()
        (let ((line (read-line port)))
          (cond
            ((eof-object? line) db)
            ((string-prefix? ";" line) (loop))
            (else
             ;; Header: nstart npairs alloc minword "legitchars"
             (let ((tokens (string-tokenize line)))
               (when (>= (length tokens) 4)
                 (set! db (make-forge-db-internal
                            (string->number (car tokens))
                            (string->number (cadr tokens))
                            (string->number (cadddr tokens))
                            language
                            pairs))))))))

      ;; Read pair entries
      (let loop ()
        (let ((line (read-line port)))
          (unless (eof-object? line)
            (unless (or (string-prefix? ";" line)
                        (string-null? (string-trim-both line)))
              (parse-pair-line line pairs))
            (loop))))

      db))

  (define (parse-pair-line line pairs)
    "Parse: XX npairs nstart nentry char1 count1 char2 count2 ..."
    (let ((tokens (string-tokenize line)))
      (when (>= (length tokens) 4)
        (let* ((digraph (car tokens))
               (npairs (string->number (cadr tokens)))
               (nstart (string->number (caddr tokens)))
               (nentry (string->number (cadddr tokens)))
               (rest (list-tail-4 tokens))
               (entries (parse-entries rest)))
          (hash-table-set! pairs digraph
                           (list npairs nstart nentry entries))))))

  (define (parse-entries tokens)
    "Parse char count char count ... into alist"
    (let loop ((toks tokens) (acc '()))
      (if (or (null? toks) (null? (cdr toks)))
          (reverse acc)
          (let ((char (string-ref (car toks) 0))
                (count (string->number (cadr toks))))
            (loop (cddr toks)
                  (cons (cons char count) acc))))))

  (define (list-tail-4 lst)
    "Return tail starting at 5th element (drop first 4)"
    (cdr (cdddr lst)))

  ;; ============================================================
  ;; Database Info
  ;; ============================================================

  (define (forge-db-info db)
    "Return database statistics"
    `((language ,(forge-db-language db))
      (words ,(forge-db-nstart db))
      (digraphs ,(hash-table-size (forge-db-pairs db)))
      (minword ,(forge-db-minword db))))

  ;; ============================================================
  ;; Random Selection (weighted)
  ;; ============================================================

  (define (weighted-choice items total)
    "Choose from ((item . weight) ...) weighted by counts"
    (if (or (null? items) (not (number? total)) (<= total 0))
        #f
        (let ((die (crypto-random-integer total)))
          (let loop ((items items) (sum 0) (first-item (and (pair? items) (pair? (car items)) (caar items))))
            (cond
              ((null? items) first-item)
              ((not (pair? (car items))) first-item)  ; malformed entry
              (else
               (let* ((item (car items))
                      (weight (cdr item)))
                 (if (not (number? weight))
                     first-item  ; bad weight, use fallback
                     (let ((newsum (+ sum weight)))
                       (if (> newsum die)
                           (car item)
                           (loop (cdr items) newsum first-item)))))))))))

  ;; ============================================================
  ;; Word Generation
  ;; ============================================================

  (define (conjure-start-pair db)
    "Pick a random starting digraph (weighted by nstart)"
    (let* ((pairs (forge-db-pairs db))
           (nstart (forge-db-nstart db))
           (candidates '()))
      ;; Build list of (digraph . nstart-weight)
      (hash-table-walk pairs
        (lambda (digraph entry)
          (let ((weight (cadr entry)))  ; nstart is second element
            (when (> weight 0)
              (set! candidates (cons (cons digraph weight) candidates))))))
      (weighted-choice candidates nstart)))

  (define (conjure-next-char db digraph)
    "Pick next character given current digraph (weighted)"
    (let* ((pairs (forge-db-pairs db))
           (entry (hash-table-ref/default pairs digraph #f)))
      (if (not entry)
          #\.  ; end if unknown digraph
          (let* ((npairs (car entry))
                 (entries (cadddr entry)))  ; ((char . count) ...)
            (or (weighted-choice entries npairs)
                #\.)))))

  (define (forge-word db)
    "Generate one pronounceable word, return (word . decibits)"
    (let* ((start (conjure-start-pair db))
           (word (list (string-ref start 1) (string-ref start 0)))
           (decibits 0)
           (pairs (forge-db-pairs db)))

      ;; Calculate entropy for start pair
      (let* ((entry (hash-table-ref/default pairs start #f))
             (nstart-pair (if entry (cadr entry) 1))
             (nstart-total (forge-db-nstart db))
             (start-entropy (entropy-decibits nstart-pair nstart-total)))
        (set! decibits (if (number? start-entropy) start-entropy 0)))

      ;; Generate rest of word
      (let loop ((digraph start))
        (let ((next (conjure-next-char db digraph)))
          (if (char=? next #\.)
              (cons (list->string (reverse word)) decibits)
              (let* ((entry (hash-table-ref/default pairs digraph #f))
                     (npairs (if entry (car entry) 1))
                     (entries (if entry (cadddr entry) '()))
                     (char-count (or (assoc-ref entries next) 1))
                     (entropy (entropy-decibits char-count npairs)))
                (set! decibits (+ decibits (if (number? entropy) entropy 0)))
                (set! word (cons next word))
                (if (> (length word) 40)
                    (cons (list->string (reverse word)) decibits)
                    (loop (string (string-ref digraph 1) next)))))))))

  (define (assoc-ref alist key)
    "Get value from alist by key (uses equal? for UTF-8 compatibility)"
    (let ((pair (assoc key alist)))
      (and pair (cdr pair))))

  (define (entropy-decibits count total)
    "Calculate entropy contribution in deci-bits"
    (if (or (not (number? count)) (not (number? total))
            (<= count 0) (<= total 0))
        0
        (let ((p (/ count total)))
          (inexact->exact (round (* -10 (/ (log p) (log 2))))))))

  (define (format-bits n)
    "Format floating point to 1 decimal place"
    (let* ((scaled (round (* n 10)))
           (whole (quotient (inexact->exact scaled) 10))
           (frac (modulo (abs (inexact->exact scaled)) 10)))
      (string-append (number->string whole) "." (number->string frac))))

  ;; ============================================================
  ;; Multi-word Generation
  ;; ============================================================

  (define (forge-words db n)
    "Generate n words, return ((word . decibits) ...)"
    (let loop ((i 0) (acc '()))
      (if (>= i n)
          (reverse acc)
          (loop (+ i 1) (cons (forge-word db) acc)))))

  (define (forge-passphrase db n)
    "Generate passphrase of n words"
    (let* ((words (forge-words db n))
           (phrase (string-join (map car words) "-"))
           (total-decibits (apply + (map cdr words))))
      (cons phrase total-decibits)))

  ;; ============================================================
  ;; Easter Egg Interface
  ;; ============================================================

  (define *loaded-dbs* (make-hash-table eq?))

  (define (get-db language)
    "Get or load database for language"
    (or (hash-table-ref/default *loaded-dbs* language #f)
        (let ((db (forge-load-db language)))
          (hash-table-set! *loaded-dbs* language db)
          db)))

  (define (forge . args)
    "Generate pronounceable passwords

     (forge)              - one English word
     (forge 5)            - five English words
     (forge 'sindarin)    - one Sindarin (Elvish) word
     (forge 'latin 3)     - three Latin words
     (forge 'passphrase)  - 4-word passphrase
     (forge 'passphrase 6) - 6-word passphrase"

    (let* ((lang 'english)
           (count 1)
           (mode 'words))

      ;; Parse arguments
      (for-each
        (lambda (arg)
          (cond
            ((number? arg) (set! count arg))
            ((eq? arg 'passphrase) (set! mode 'passphrase))
            ((memq arg *forge-languages*) (set! lang arg))))
        args)

      (let ((db (get-db lang)))
        (case mode
          ((passphrase)
           (let* ((result (forge-passphrase db (if (= count 1) 4 count)))
                  (phrase (car result))
                  (bits (/ (cdr result) 10.0)))
             (printf "~a~n" phrase)
             (printf "  (~a, ~a bits)~n" lang (format-bits bits))
             phrase))

          (else
           (let ((results (forge-words db count)))
             (for-each
               (lambda (r)
                 (printf "~a  (~a bits)~n" (car r) (format-bits (/ (cdr r) 10.0))))
               results)
             (if (= count 1)
                 (caar results)
                 (map car results))))))))

) ;; end module
