;;; forge.sls - Multilingual Password Generator
;;;
;;; Markov chain word generator using digraph statistics.
;;; Produces pronounceable passwords from language models.
;;;
;;; Design: Derrell Piper & Jon Callas (VAX/VMS 6.0, circa 1991)
;;; US/EU DEC patents (expired)

(library (cyberspace forge)
  (export
    forge-load-db
    forge-db-info
    forge-word
    forge-words
    forge-passphrase
    forge
    forge-languages
    forge-db-path
    set-forge-db-path!)

  (import (rnrs)
          (only (chezscheme)
                printf format sort
                getenv parameterize)
          (only (cyberspace crypto-ffi) random-uniform)
          (only (cyberspace fips) test-randomness)
          (cyberspace chicken-compatibility hash-table))

  ;; ============================================================
  ;; Inlined helpers
  ;; ============================================================

  (define (string-prefix? prefix s)
    (and (>= (string-length s) (string-length prefix))
         (string=? prefix (substring s 0 (string-length prefix)))))

  (define (string-tokenize s)
    (let ((len (string-length s)))
      (let loop ((i 0) (start #f) (acc '()))
        (cond
          ((= i len)
           (reverse (if start (cons (substring s start i) acc) acc)))
          ((char-whitespace? (string-ref s i))
           (loop (+ i 1) #f (if start (cons (substring s start i) acc) acc)))
          (else
           (loop (+ i 1) (or start i) acc))))))

  (define (string-join lst sep)
    (cond
      ((null? lst) "")
      ((null? (cdr lst)) (car lst))
      (else (let loop ((rest (cdr lst)) (acc (car lst)))
              (if (null? rest) acc
                  (loop (cdr rest) (string-append acc sep (car rest))))))))

  (define (make-pathname dir file)
    (string-append dir "/" file))

  ;; ============================================================
  ;; Configuration
  ;; ============================================================

  (define *forge-db-path*
    (or (getenv "FORGE_DB_PATH")
        (let ((home (getenv "HOME")))
          (and home (string-append home "/src/lisp/forge")))))

  (define (forge-db-path) *forge-db-path*)
  (define (set-forge-db-path! path) (set! *forge-db-path* path))

  (define forge-languages
    '(english latin italian dutch sindarin webster
      french german spanish portuguese
      catalan galician basque
      swedish norwegian danish finnish
      irish welsh scottish breton
      greek albanian serbian croatian slovenian macedonian
      polish czech slovak hungarian romanian
      lithuanian latvian estonian
      russian ukrainian bulgarian
      turkish armenian maltese
      vietnamese thai lao korean
      sanskrit dante))

  ;; ============================================================
  ;; Cryptographic Random
  ;; ============================================================

  (define (crypto-random-integer limit)
    (if (<= limit 0) 0 (random-uniform limit)))

  (define (verify-entropy-source)
    (unless (test-randomness)
      (error 'forge "Entropy source failed FIPS 140-2 statistical tests")))

  ;; ============================================================
  ;; Database Structure (R6RS record)
  ;; ============================================================

  (define-record-type forge-db
    (fields nstart npairs minword language pairs))

  (define (make-empty-forge-db)
    (make-forge-db 0 0 3 'unknown (make-hash-table string=?)))

  ;; ============================================================
  ;; Database Parser
  ;; ============================================================

  (define (forge-load-db language)
    (let* ((filename (format "~a.db" language))
           (path (make-pathname *forge-db-path* filename)))
      (with-input-from-file path
        (lambda () (parse-db-file (current-input-port) language)))))

  (define (parse-db-file port language)
    (let ((pairs (make-hash-table string=?))
          (db-nstart 0)
          (db-npairs 0)
          (db-minword 3))
      ;; Skip comment lines, read header
      (let loop ()
        (let ((line (get-line port)))
          (cond
            ((eof-object? line) #f)
            ((string-prefix? ";" line) (loop))
            (else
             (let ((tokens (string-tokenize line)))
               (when (>= (length tokens) 4)
                 (set! db-nstart (string->number (car tokens)))
                 (set! db-npairs (string->number (cadr tokens)))
                 (set! db-minword (string->number (cadddr tokens)))))))))
      ;; Read pair entries as S-expressions
      (let loop ()
        (let ((entry (read port)))
          (unless (eof-object? entry)
            (when (and (list? entry) (>= (length entry) 4))
              (parse-sexp-entry entry pairs))
            (loop))))
      (make-forge-db db-nstart db-npairs db-minword language pairs)))

  (define (parse-sexp-entry entry pairs)
    (let* ((digraph (car entry))
           (npairs (cadr entry))
           (nstart (caddr entry))
           (char-entries (cadddr entry))
           (entries (map (lambda (e)
                           (cons (string-ref (car e) 0) (cdr e)))
                         char-entries)))
      (hash-table-set! pairs digraph
                       (list npairs nstart (length entries) entries))))

  ;; ============================================================
  ;; Database Info
  ;; ============================================================

  (define (forge-db-info db)
    `((language ,(forge-db-language db))
      (words ,(forge-db-nstart db))
      (digraphs ,(hash-table-size (forge-db-pairs db)))
      (minword ,(forge-db-minword db))))

  ;; ============================================================
  ;; Random Selection (weighted)
  ;; ============================================================

  (define (weighted-choice items total)
    (if (or (null? items) (not (number? total)) (<= total 0))
        #f
        (let ((die (crypto-random-integer total)))
          (let loop ((items items) (sum 0)
                     (first-item (and (pair? items) (pair? (car items)) (caar items))))
            (cond
              ((null? items) first-item)
              ((not (pair? (car items))) first-item)
              (else
               (let* ((item (car items))
                      (weight (cdr item)))
                 (if (not (number? weight))
                     first-item
                     (let ((newsum (+ sum weight)))
                       (if (> newsum die)
                           (car item)
                           (loop (cdr items) newsum first-item)))))))))))

  ;; ============================================================
  ;; Word Generation
  ;; ============================================================

  (define (conjure-start-pair db)
    (let* ((pairs (forge-db-pairs db))
           (nstart (forge-db-nstart db))
           (candidates '()))
      (hash-table-walk pairs
        (lambda (digraph entry)
          (let ((weight (cadr entry)))
            (when (> weight 0)
              (set! candidates (cons (cons digraph weight) candidates))))))
      (weighted-choice candidates nstart)))

  (define (conjure-next-char db digraph)
    (let* ((pairs (forge-db-pairs db))
           (entry (hash-table-ref/default pairs digraph #f)))
      (if (not entry)
          #\.
          (let* ((npairs (car entry))
                 (entries (cadddr entry)))
            (or (weighted-choice entries npairs)
                #\.)))))

  (define (forge-word db)
    (let* ((start (conjure-start-pair db))
           (word (list (string-ref start 1) (string-ref start 0)))
           (decibits 0)
           (pairs (forge-db-pairs db)))
      ;; Entropy for start pair
      (let* ((entry (hash-table-ref/default pairs start #f))
             (nstart-pair (if entry (cadr entry) 1))
             (nstart-total (forge-db-nstart db))
             (start-entropy (entropy-decibits nstart-pair nstart-total)))
        (set! decibits (if (number? start-entropy) start-entropy 0)))
      ;; Generate rest
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
    (let ((pair (assoc key alist)))
      (and pair (cdr pair))))

  (define (entropy-decibits count total)
    (if (or (not (number? count)) (not (number? total))
            (<= count 0) (<= total 0))
        0
        (let ((p (/ count total)))
          (exact (round (* -10 (/ (log p) (log 2))))))))

  (define (format-bits n)
    (let* ((scaled (round (* n 10)))
           (whole (div (exact (abs scaled)) 10))
           (frac (mod (exact (abs scaled)) 10)))
      (string-append (number->string whole) "." (number->string frac))))

  ;; ============================================================
  ;; Multi-word Generation
  ;; ============================================================

  (define (forge-words db n)
    (let loop ((i 0) (acc '()))
      (if (>= i n) (reverse acc)
          (loop (+ i 1) (cons (forge-word db) acc)))))

  (define (forge-passphrase db n)
    (let* ((words (forge-words db n))
           (phrase (string-join (map car words) "-"))
           (total-decibits (apply + (map cdr words))))
      (cons phrase total-decibits)))

  ;; ============================================================
  ;; Easter Egg Interface
  ;; ============================================================

  (define *loaded-dbs* (make-hash-table))

  (define (get-db language)
    (or (hash-table-ref/default *loaded-dbs* language #f)
        (let ((db (forge-load-db language)))
          (hash-table-set! *loaded-dbs* language db)
          db)))

  (define (forge-word-min-bits db min-decibits)
    (let loop ((attempts 0))
      (if (>= attempts 100)
          (let ((result (forge-word db)))
            (format (current-error-port)
                    "Warning: could not meet ~a bit target after 100 attempts~n"
                    (/ min-decibits 10.0))
            result)
          (let ((result (forge-word db)))
            (if (>= (cdr result) min-decibits)
                result
                (loop (+ attempts 1)))))))

  (define (forge . args)
    (let ((lang 'english)
          (count 1)
          (mode 'words)
          (min-bits #f))
      ;; Parse arguments
      (let loop ((remaining args) (expect-bits #f))
        (when (pair? remaining)
          (let ((arg (car remaining)))
            (cond
              (expect-bits
               (when (number? arg) (set! min-bits arg))
               (loop (cdr remaining) #f))
              ((eq? arg 'bits)
               (loop (cdr remaining) #t))
              ((number? arg)
               (set! count arg)
               (loop (cdr remaining) #f))
              ((eq? arg 'passphrase)
               (set! mode 'passphrase)
               (loop (cdr remaining) #f))
              ((memq arg forge-languages)
               (set! lang arg)
               (loop (cdr remaining) #f))
              (else
               (loop (cdr remaining) #f))))))
      (let ((db (get-db lang))
            (min-decibits (and min-bits (* min-bits 10))))
        (case mode
          ((passphrase)
           (let* ((result (forge-passphrase db (if (= count 1) 4 count)))
                  (phrase (car result))
                  (bits (/ (cdr result) 10.0)))
             (printf "~a~n" phrase)
             (printf "  (~a, ~a bits)~n" lang (format-bits bits))
             phrase))
          (else
           (let ((results (if min-decibits
                              (let loop ((i 0) (acc '()))
                                (if (>= i count) (reverse acc)
                                    (loop (+ i 1)
                                          (cons (forge-word-min-bits db min-decibits) acc))))
                              (forge-words db count))))
             (for-each
               (lambda (r)
                 (printf "~a  (~a bits)~n" (car r) (format-bits (/ (cdr r) 10.0))))
               results)
             (if (= count 1)
                 (caar results)
                 (map car results))))))))

  ;; Verify entropy on load (FIPS)
  (verify-entropy-source)

) ;; end library
