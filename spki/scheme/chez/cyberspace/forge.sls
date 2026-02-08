;;; forge.scm - Multilingual Password Generator
;;; Library of Cyberspace - Chez Port
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

(library (cyberspace forge)
  (export
    ;; Database operations
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

  (import (except (rnrs) with-input-from-file with-output-to-file flush-output-port find current-error-port)
          (only (chezscheme)
                printf format void
                make-parameter
                with-input-from-file with-output-to-file
                flush-output-port
                current-error-port
                getenv)
          (cyberspace chicken-compatibility chicken)
          (cyberspace chicken-compatibility hashtable)
          (cyberspace crypto-ffi)
          (cyberspace fips))

  ;; ============================================================
  ;; Configuration
  ;; ============================================================

  (define *forge-db-path*
    (make-parameter
      (or (getenv "FORGE_DB_PATH")
          (let ((home (getenv "HOME")))
            (if home
                (string-append home "/src/lisp/forge")
                "forge")))))

  (define *forge-languages*
    '(;; DEC heritage (VMS 1991)
      english latin italian dutch sindarin webster
      ;; Western Europe
      french german spanish portuguese
      ;; Iberia
      catalan galician basque
      ;; Nordic
      swedish norwegian danish finnish
      ;; Atlantic fringe
      irish welsh scottish breton
      ;; Balkans
      greek albanian serbian croatian slovenian macedonian
      ;; Eastern front
      polish czech slovak hungarian romanian
      ;; Baltic
      lithuanian latvian estonian
      ;; Soviet theater
      russian ukrainian bulgarian
      ;; Near East
      turkish armenian
      ;; Mediterranean
      maltese
      ;; Detachment 101
      vietnamese thai lao korean
      ;; Indic
      sanskrit
      ;; Literary
      dante))

  ;; ============================================================
  ;; Cryptographic Random Number Generator
  ;; ============================================================
  ;;
  ;; All randomness flows through libsodium's randombytes_buf():
  ;;   Linux: getrandom(2) syscall
  ;;   macOS: arc4random_buf()
  ;;   OpenBSD: getentropy(2)
  ;; Hardware entropy (RDRAND/RDSEED) feeds the OS pool.

  (define (crypto-random-integer limit)
    "Generate cryptographically secure random integer in [0, limit).
     Uses libsodium's rejection sampling to avoid modulo bias."
    (if (<= limit 0)
        0
        (random-uniform limit)))

  (define (verify-entropy-source)
    "Boot-time FIPS 140-2 verification of cryptographic entropy source.
     Tests: Monobit, Poker, Runs, Long Run on 20,000 bits.
     Signals error if any test fails."
    (unless (test-randomness)
      (error 'verify-entropy-source
             "Entropy source failed FIPS 140-2 statistical tests")))

  ;; Verify entropy source on module load
  (define _entropy-verified (begin (verify-entropy-source) (void)))

  ;; ============================================================
  ;; Database Structure
  ;; ============================================================
  ;;
  ;; A smelter database contains:
  ;;   nstart     - total starting pairs (= words in source)
  ;;   npairs     - number of unique digraphs
  ;;   pairs      - hash table: "ab" -> (npairs nstart nentry entries)
  ;;   entries    - alist: ((#\c . count) ...)

  ;; Tagged vector: #(*forge-db-tag* nstart npairs minword language pairs)
  (define *forge-db-tag* (list 'forge-db))

  (define (make-forge-db)
    (vector *forge-db-tag* 0 0 3 'unknown (make-hash-table string=?)))

  (define (make-forge-db* nstart npairs minword language pairs)
    (vector *forge-db-tag* nstart npairs minword language pairs))

  (define (forge-db? x)
    (and (vector? x)
         (>= (vector-length x) 6)
         (eq? (vector-ref x 0) *forge-db-tag*)))

  (define (forge-db-nstart db)  (vector-ref db 1))
  (define (forge-db-npairs db)  (vector-ref db 2))
  (define (forge-db-minword db) (vector-ref db 3))
  (define (forge-db-language db)(vector-ref db 4))
  (define (forge-db-pairs db)   (vector-ref db 5))

  ;; ============================================================
  ;; String tokenization (replaces Chicken's string-tokenize)
  ;; ============================================================

  (define (string-tokenize str)
    "Split string on whitespace into list of tokens"
    (string-split str))

  ;; ============================================================
  ;; Database Parser
  ;; ============================================================

  (define (forge-load-db language)
    "Load a smelter database file"
    (let* ((filename (string-append (symbol->string language) ".db"))
           (path (string-append (*forge-db-path*) "/" filename)))
      (call-with-input-file path
        (lambda (port)
          (parse-db-file port language)))))

  (define (parse-db-file port language)
    "Parse smelter .db format (S-expression based)"
    (let ((pairs (make-hash-table string=?))
          (nstart 0)
          (npairs 0)
          (minword 3))

      ;; Skip comment lines, read header
      (let loop ()
        (let ((line (get-line port)))
          (cond
            ((eof-object? line) (void))
            ((and (> (string-length line) 0)
                  (char=? (string-ref line 0) #\;))
             (loop))
            (else
             ;; Header: nstart npairs alloc minword "legitchars"
             (let ((tokens (string-tokenize line)))
               (when (>= (length tokens) 4)
                 (set! nstart (string->number (car tokens)))
                 (set! npairs (string->number (cadr tokens)))
                 (set! minword (string->number (list-ref tokens 3)))))))))

      ;; Read pair entries as S-expressions
      (let loop ()
        (let ((entry (read port)))
          (unless (eof-object? entry)
            (when (and (list? entry) (>= (length entry) 4))
              (parse-sexp-entry entry pairs))
            (loop))))

      (make-forge-db* nstart npairs minword language pairs)))

  (define (parse-sexp-entry entry pairs)
    "Parse S-expression: (digraph npairs nstart ((char . count) ...))"
    (let* ((digraph (car entry))
           (npairs (cadr entry))
           (nstart (caddr entry))
           (char-entries (list-ref entry 3))
           ;; Convert string chars back to actual chars
           (entries (map (lambda (e)
                           (cons (string-ref (car e) 0) (cdr e)))
                         char-entries)))
      (hash-table-set! pairs digraph
                       (list npairs nstart (length entries) entries))))

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
                 (entries (list-ref entry 3)))  ; ((char . count) ...)
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
                     (entries (if entry (list-ref entry 3) '()))
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
          (exact (round (* -10 (/ (log p) (log 2))))))))

  (define (format-bits n)
    "Format floating point to 1 decimal place"
    (let* ((scaled (round (* n 10)))
           (whole (quotient (exact scaled) 10))
           (frac (modulo (abs (exact scaled)) 10)))
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

  (define (forge-word-min-bits db min-decibits)
    "Generate word with at least min-decibits entropy (max 100 attempts)"
    (let loop ((attempts 0))
      (if (>= attempts 100)
          (let ((result (forge-word db)))
            (printf "Warning: could not meet ~a bit target after 100 attempts~%"
                    (/ min-decibits 10.0))
            result)
          (let ((result (forge-word db)))
            (if (>= (cdr result) min-decibits)
                result
                (loop (+ attempts 1)))))))

  (define (forge . args)
    "Generate pronounceable passwords

     (forge)              - one English word
     (forge 5)            - five English words
     (forge 'sindarin)    - one Sindarin (Elvish) word
     (forge 'latin 3)     - three Latin words
     (forge 'passphrase)  - 4-word passphrase
     (forge 'passphrase 6) - 6-word passphrase
     (forge 'bits 40)     - one word with >= 40 bits entropy
     (forge 'sanskrit 'bits 30 3) - three Sanskrit words >= 30 bits each"

    (let* ((lang 'english)
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
              ((memq arg *forge-languages*)
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
             (printf "~a~%" phrase)
             (printf "  (~a, ~a bits)~%" lang (format-bits bits))
             phrase))

          (else
           (let ((results (if min-decibits
                              (let loop ((i 0) (acc '()))
                                (if (>= i count)
                                    (reverse acc)
                                    (loop (+ i 1)
                                          (cons (forge-word-min-bits db min-decibits) acc))))
                              (forge-words db count))))
             (for-each
               (lambda (r)
                 (printf "~a  (~a bits)~%" (car r) (format-bits (/ (cdr r) 10.0))))
               results)
             (if (= count 1)
                 (caar results)
                 (map car results))))))))

) ;; end library
