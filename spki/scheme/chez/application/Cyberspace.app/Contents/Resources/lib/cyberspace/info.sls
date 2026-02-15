;;; info.sls - Hypertext documentation browser for Cyberspace
;;;
;;; Like info(1), but native to the REPL and the weave.
;;; Browses memos, API docs, and help topics.
;;; Buffered pager with top/bottom status lines.

(library (cyberspace info)
  (export
    info info? info-hierarchical
    info-search info-index
    info-next info-prev info-up
    info-page info-pager
    info-node info-history)

  (import (rnrs)
          (only (chezscheme)
                printf format void
                file-directory? directory-list
                getenv sort))

  ;; ============================================================
  ;; Inlined helpers
  ;; ============================================================

  (define (take lst n)
    (if (or (zero? n) (null? lst)) '()
        (cons (car lst) (take (cdr lst) (- n 1)))))

  (define (drop lst n)
    (if (or (zero? n) (null? lst)) lst
        (drop (cdr lst) (- n 1))))

  (define (drop-right lst n)
    (take lst (max 0 (- (length lst) n))))

  (define (string-pad-right s width)
    (let ((len (string-length s)))
      (if (>= len width) (substring s 0 width)
          (string-append s (make-string (- width len) #\space)))))

  (define (string-contains s1 s2)
    (let ((len1 (string-length s1))
          (len2 (string-length s2)))
      (if (> len2 len1) #f
          (let loop ((i 0))
            (cond ((> (+ i len2) len1) #f)
                  ((string=? s2 (substring s1 i (+ i len2))) i)
                  (else (loop (+ i 1))))))))

  (define (string-downcase-simple s)
    (list->string (map char-downcase (string->list s))))

  (define (make-pathname dir file)
    (string-append dir "/" file))

  (define (pathname-strip-directory path)
    (let loop ((i (- (string-length path) 1)))
      (cond ((< i 0) path)
            ((char=? (string-ref path i) #\/) (substring path (+ i 1) (string-length path)))
            (else (loop (- i 1))))))

  (define (directory-exists? path)
    (and (file-exists? path) (file-directory? path)))

  (define (read-lines port)
    (let loop ((acc '()))
      (let ((line (get-line port)))
        (if (eof-object? line) (reverse acc)
            (loop (cons line acc))))))

  ;; ============================================================
  ;; Terminal
  ;; ============================================================

  (define (term-height)
    (let ((h (getenv "LINES")))
      (if h (or (string->number h) 24) 24)))

  (define (term-width)
    (let ((w (getenv "COLUMNS")))
      (if w (or (string->number w) 80) 80)))

  (define (ansi-reverse s)
    (string-append "\x1b;[7m" s "\x1b;[0m"))

  (define (ansi-clear-screen)
    (display "\x1b;[2J\x1b;[H"))

  (define (ansi-goto row col)
    (printf "\x1b;[~a;~aH" row col))

  ;; ============================================================
  ;; Pager
  ;; ============================================================

  (define *pager-buffer* '())
  (define *pager-offset* 0)
  (define *pager-title* "")

  (define (pager-content-height)
    (- (term-height) 2))

  (define (pager-display)
    (let* ((height (pager-content-height))
           (total (length *pager-buffer*))
           (width (term-width))
           (end (min (+ *pager-offset* height) total))
           (visible (take (drop *pager-buffer* *pager-offset*)
                          (- end *pager-offset*))))
      (ansi-clear-screen)
      ;; Top status
      (display (ansi-reverse (string-pad-right (string-append " " *pager-title*) width)))
      (newline)
      ;; Content
      (for-each
        (lambda (line)
          (display (if (> (string-length line) width)
                       (substring line 0 width)
                       line))
          (newline))
        visible)
      ;; Pad
      (let ((pad (- height (length visible))))
        (when (> pad 0)
          (do ((i 0 (+ i 1))) ((= i pad)) (newline))))
      ;; Bottom status
      (ansi-goto (term-height) 1)
      (display (ansi-reverse
                 (string-pad-right
                   (format " Line ~a-~a of ~a  [j/k:scroll  q:quit  /:search]"
                           (+ *pager-offset* 1) end total)
                   width)))))

  (define (pager-down . rest)
    (let ((n (if (null? rest) 1 (car rest)))
          (max-offset (max 0 (- (length *pager-buffer*) (pager-content-height)))))
      (set! *pager-offset* (min max-offset (+ *pager-offset* n)))
      (pager-display)))

  (define (pager-up . rest)
    (let ((n (if (null? rest) 1 (car rest))))
      (set! *pager-offset* (max 0 (- *pager-offset* n)))
      (pager-display)))

  (define (pager-page-down) (pager-down (pager-content-height)))
  (define (pager-page-up) (pager-up (pager-content-height)))

  (define (pager-top)
    (set! *pager-offset* 0) (pager-display))

  (define (pager-bottom)
    (set! *pager-offset* (max 0 (- (length *pager-buffer*) (pager-content-height))))
    (pager-display))

  (define (info-pager lines title)
    (set! *pager-buffer* lines)
    (set! *pager-offset* 0)
    (set! *pager-title* title)
    (pager-display)
    (let loop ()
      (let ((c (read-char)))
        (cond
          ((or (eof-object? c) (char=? c #\q)) (void))
          ((or (char=? c #\j) (char=? c #\newline))
           (pager-down) (loop))
          ((char=? c #\k) (pager-up) (loop))
          ((char=? c #\space) (pager-page-down) (loop))
          ((char=? c #\b) (pager-page-up) (loop))
          ((char=? c #\g) (pager-top) (loop))
          ((char=? c #\G) (pager-bottom) (loop))
          (else (loop))))))

  (define (info-page file)
    (when (file-exists? file)
      (let ((lines (with-input-from-file file
                     (lambda () (read-lines (current-input-port))))))
        (info-pager lines (pathname-strip-directory file)))))

  ;; ============================================================
  ;; Navigation State
  ;; ============================================================

  (define *info-node* '(top))
  (define *info-history* '())
  (define *info-path* #f)

  (define (info-node) *info-node*)
  (define (info-history) *info-history*)

  (define (info-init!)
    (let ((paths '("./docs/notes"
                    "../docs/notes"
                    "~/cyberspace/spki/scheme/docs/notes")))
      (set! *info-path* (find directory-exists? paths))))

  ;; ============================================================
  ;; Topic Tree
  ;; ============================================================

  (define *info-tree*
    '((top "Library of Cyberspace"
        (architecture "System Architecture"
          (overview "Architecture Overview" memo-0002)
          (replication "Replication Layer" memo-0007)
          (federation "Federation Protocol" memo-0012))
        (vault "Vault & Storage"
          (architecture "Vault Architecture" memo-0006)
          (soup "Object Store (Soup)")
          (audit "Audit Trail" memo-0005)
          (migration "Vault Migration" memo-0029))
        (crypto "Cryptography"
          (spki "SPKI Authorization" memo-0003)
          (shamir "Secret Sharing" memo-0004)
          (threshold "Threshold Signatures" memo-0008)
          (entropy "Entropy Sources" memo-0043))
        (network "Network"
          (gossip "Gossip Protocol")
          (mdns "Local Discovery")
          (enrollment "Node Enrollment"))
        (consensus "Consensus"
          (lamport "Lamport Clocks" memo-0014)
          (byzantine "Byzantine Consensus" memo-0013))
        (interface "Interface"
          (terminal "Terminal Conventions" memo-0051)
          (compilation "Building & Debugging" memo-0052)))))

  (define (info-find-node path)
    (let loop ((tree *info-tree*) (path path))
      (cond
        ((null? path) tree)
        ((null? tree) #f)
        ((and (pair? tree) (eq? (car tree) (car path)))
         (if (null? (cdr path))
             tree
             (let ((children (if (> (length tree) 2) (cdddr tree) '())))
               (find (lambda (child)
                       (and (pair? child)
                            (eq? (car child) (cadr path))))
                     children))))
        (else #f))))

  (define (info-display-node node)
    (when (pair? node)
      (let ((name (car node))
            (title (if (> (length node) 1) (cadr node) ""))
            (memo (if (> (length node) 2)
                      (find symbol? (cddr node))
                      #f))
            (children (filter pair? (if (> (length node) 2) (cddr node) '()))))
        (newline)
        (display "=======================================================") (newline)
        (printf "  ~a~n" title)
        (display "=======================================================") (newline)
        (newline)
        (when memo (info-show-memo memo))
        (when (not (null? children))
          (display "Subtopics:") (newline) (newline)
          (for-each
            (lambda (child)
              (printf "  * ~a - ~a~n"
                      (car child)
                      (if (> (length child) 1) (cadr child) "")))
            children)
          (newline))
        (display "-------------------------------------------------------") (newline)
        (display "  (info 'topic)  Navigate    (info-search \"term\")  Search") (newline)
        (display "  (info-up)      Go up       (info-index)          Index") (newline)
        (newline))))

  (define (info-show-memo memo-sym)
    (when *info-path*
      (let ((file (make-pathname *info-path*
                    (string-append (symbol->string memo-sym) ".txt"))))
        (when (file-exists? file)
          (let ((lines (with-input-from-file file
                         (lambda () (read-lines (current-input-port))))))
            (let loop ((lines lines) (count 0))
              (when (and (not (null? lines)) (< count 20))
                (let ((line (car lines)))
                  (unless (string=? line "")
                    (display line) (newline))
                  (loop (cdr lines) (+ count 1))))))
          (newline)
          (printf "[Full text: ~a]~n" file)
          (newline)))))

  ;; ============================================================
  ;; Public Interface
  ;; ============================================================

  (define (info . args)
    (info-init!)
    (let ((path (if (null? args) '(top) (cons 'top args))))
      (set! *info-history* (cons *info-node* *info-history*))
      (set! *info-node* path)
      (let ((node (info-find-node path)))
        (if node
            (info-display-node node)
            (printf "Node not found: ~a~n" args)))))

  (define (info?)
    (printf "Current: ~a~n" *info-node*)
    (printf "History: ~a items~n" (length *info-history*))
    (newline)
    (display "Navigation:") (newline)
    (display "  (info 'topic)      Go to topic") (newline)
    (display "  (info-up)          Go up one level") (newline)
    (display "  (info-prev)        Go back in history") (newline)
    (display "  (info-search STR)  Search all docs") (newline)
    (display "  (info-index)       Show full index") (newline))

  (define (info-up)
    (when (> (length *info-node*) 1)
      (set! *info-node* (drop-right *info-node* 1))
      (info-display-node (info-find-node *info-node*))))

  (define (info-prev)
    (when (not (null? *info-history*))
      (set! *info-node* (car *info-history*))
      (set! *info-history* (cdr *info-history*))
      (info-display-node (info-find-node *info-node*))))

  (define (info-next)
    (display "Not yet implemented") (newline))

  (define (info-search pattern)
    (info-init!)
    (newline)
    (printf "Searching for: ~a~n" pattern)
    (newline)
    (when *info-path*
      (let ((files (let ((all (directory-list *info-path*)))
                     (map (lambda (f) (make-pathname *info-path* f))
                          (filter (lambda (f)
                                    (let ((len (string-length f)))
                                      (and (> len 4)
                                           (string=? ".txt" (substring f (- len 4) len)))))
                                  all)))))
        (for-each
          (lambda (file)
            (let ((matches (info-grep-file file pattern)))
              (when (not (null? matches))
                (printf "~a:~n" (pathname-strip-directory file))
                (for-each (lambda (m) (printf "  ~a~n" m))
                          (take matches (min 3 (length matches))))
                (newline))))
          files))))

  (define (info-grep-file file pattern)
    (let ((pat-lower (string-downcase-simple pattern)))
      (with-input-from-file file
        (lambda ()
          (let loop ((lines '()))
            (let ((line (get-line (current-input-port))))
              (if (eof-object? line)
                  (reverse lines)
                  (loop (if (string-contains (string-downcase-simple line) pat-lower)
                            (cons line lines)
                            lines)))))))))

  (define (info-index)
    (newline)
    (display "Library of Cyberspace - Documentation Index") (newline)
    (display "============================================") (newline)
    (newline)
    (info-print-tree *info-tree* 0))

  (define (info-print-tree tree depth)
    (when (pair? tree)
      (let ((name (car tree))
            (title (if (> (length tree) 1) (cadr tree) ""))
            (children (filter pair? (if (> (length tree) 2) (cddr tree) '()))))
        (printf "~a~a - ~a~n"
                (make-string (* depth 2) #\space) name title)
        (for-each
          (lambda (child) (info-print-tree child (+ depth 1)))
          children))))

  (define (info-hierarchical node)
    (info-print-tree (info-find-node node) 0))

) ;; end library
