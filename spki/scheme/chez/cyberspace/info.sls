;;; info.sls - Hypertext Documentation Browser (Chez Port)
;;; Library of Cyberspace
;;;
;;; Like info(1), but native to the REPL and the weave.
;;; Browses memos, API docs, and help topics.
;;; Buffered pager with top/bottom status lines.
;;;
;;; Ported from info.scm.
;;; Copyright (c) 2026 Yoyodyne. See LICENSE.

(library (cyberspace info)
  (export info info? info-hierarchical
          info-search info-index
          info-next info-prev info-up
          info-page info-pager
          *info-node* *info-history*)

  (import (except (rnrs) file-exists? with-input-from-file flush-output-port find)
          (only (chezscheme)
                printf format void
                file-exists?
                directory-list
                with-input-from-file
                flush-output-port
                getenv
                open-process-ports native-transcoder
                with-output-to-string)
          (cyberspace chicken-compatibility chicken))

  ;; ============================================================
  ;; Local Helpers
  ;; ============================================================

  (define (pathname-strip-directory path)
    (let loop ((i (- (string-length path) 1)))
      (cond ((< i 0) path)
            ((char=? (string-ref path i) #\/)
             (substring path (+ i 1) (string-length path)))
            (else (loop (- i 1))))))

  (define (make-pathname dir file)
    (if (or (not dir) (string=? dir ""))
        file
        (if (char=? (string-ref dir (- (string-length dir) 1)) #\/)
            (string-append dir file)
            (string-append dir "/" file))))

  (define (string-pad-right str n)
    (if (>= (string-length str) n)
        (substring str 0 n)
        (string-append str (make-string (- n (string-length str)) #\space))))

  (define (read-lines port)
    "Read all lines from port."
    (let loop ((lines '()))
      (let ((line (get-line port)))
        (if (eof-object? line)
            (reverse lines)
            (loop (cons line lines))))))

  (define (read-file-lines path)
    "Read all lines from file."
    (with-input-from-file path
      (lambda () (read-lines (current-input-port)))))

  (define (glob-files dir pattern)
    "List files matching a simple *.ext pattern in dir."
    (guard (exn [#t '()])
      (if (and dir (directory-exists? dir))
          (let ((ext (and (> (string-length pattern) 1)
                          (char=? (string-ref pattern 0) #\*)
                          (substring pattern 1 (string-length pattern)))))
            (if ext
                (map (lambda (f) (make-pathname dir f))
                     (filter (lambda (f)
                               (and (>= (string-length f) (string-length ext))
                                    (string=? (substring f (- (string-length f)
                                                              (string-length ext))
                                                         (string-length f))
                                              ext)))
                             (directory-list dir)))
                '()))
          '())))

  ;; ============================================================
  ;; Terminal Helpers
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

      ;; Top status line
      (display (ansi-reverse
                 (string-pad-right
                   (string-append " " *pager-title*)
                   width)))
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

      ;; Bottom status line
      (ansi-goto (term-height) 1)
      (display (ansi-reverse
                 (string-pad-right
                   (format " Line ~a-~a of ~a  [j/k:scroll  q:quit  /:search]"
                           (+ *pager-offset* 1)
                           end
                           total)
                   width)))))

  (define (pager-down . rest)
    (let ((n (if (null? rest) 1 (car rest))))
      (let ((max-offset (max 0 (- (length *pager-buffer*) (pager-content-height)))))
        (set! *pager-offset* (min max-offset (+ *pager-offset* n)))
        (pager-display))))

  (define (pager-up . rest)
    (let ((n (if (null? rest) 1 (car rest))))
      (set! *pager-offset* (max 0 (- *pager-offset* n)))
      (pager-display)))

  (define (pager-page-down)
    (pager-down (pager-content-height)))

  (define (pager-page-up)
    (pager-up (pager-content-height)))

  (define (pager-top)
    (set! *pager-offset* 0)
    (pager-display))

  (define (pager-bottom)
    (set! *pager-offset* (max 0 (- (length *pager-buffer*) (pager-content-height))))
    (pager-display))

  (define (info-pager lines title)
    "Display lines in pager with title"
    (set! *pager-buffer* lines)
    (set! *pager-offset* 0)
    (set! *pager-title* title)
    (pager-display)

    (let loop ()
      (let ((c (read-char)))
        (cond
          ((or (eof-object? c) (char=? c #\q))
           (display "")
           (newline)
           (void))
          ((or (char=? c #\j) (char=? c #\newline))
           (pager-down) (loop))
          ((char=? c #\k)
           (pager-up) (loop))
          ((char=? c #\space)
           (pager-page-down) (loop))
          ((char=? c #\b)
           (pager-page-up) (loop))
          ((char=? c #\g)
           (pager-top) (loop))
          ((char=? c #\G)
           (pager-bottom) (loop))
          (else (loop))))))

  (define (info-page file)
    "Page through a file"
    (when (file-exists? file)
      (let ((lines (read-file-lines file)))
        (info-pager lines (pathname-strip-directory file)))))

  ;; ============================================================
  ;; Info Tree
  ;; ============================================================

  (define *info-node-box* (vector '(top)))
  (define-syntax *info-node*
    (identifier-syntax
      [id (vector-ref *info-node-box* 0)]
      [(set! id val) (vector-set! *info-node-box* 0 val)]))
  (define *info-history-box* (vector '()))
  (define-syntax *info-history*
    (identifier-syntax
      [id (vector-ref *info-history-box* 0)]
      [(set! id val) (vector-set! *info-history-box* 0 val)]))
  (define *info-path* #f)

  (define (info-init!)
    (let ((paths (list
                   "./docs/notes"
                   "../docs/notes"
                   "~/cyberspace/spki/scheme/docs/notes")))
      (set! *info-path*
        (find (lambda (p) (directory-exists? p)) paths))))

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
    "Find node in tree by path"
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
    "Display a node's content"
    (when (pair? node)
      (let ((name (car node))
            (title (if (> (length node) 1) (cadr node) ""))
            (memo (if (> (length node) 2)
                      (find symbol? (cddr node))
                      #f))
            (children (filter pair? (if (> (length node) 2) (cddr node) '()))))

        (display "\n")
        (display "═══════════════════════════════════════════════════════\n")
        (printf "  ~a~%" title)
        (display "═══════════════════════════════════════════════════════\n")
        (display "\n")

        (when memo
          (info-show-memo memo))

        (when (not (null? children))
          (display "Subtopics:\n")
          (display "\n")
          (for-each
            (lambda (child)
              (printf "  * ~a -~a~%"
                      (car child)
                      (if (> (length child) 1) (cadr child) "")))
            children)
          (display "\n"))

        (display "───────────────────────────────────────────────────────\n")
        (display "  (info 'topic)  Navigate    (info-search \"term\")  Search\n")
        (display "  (info-up)      Go up       (info-index)          Index\n")
        (display "\n"))))

  (define (info-show-memo memo-sym)
    "Display memo abstract/intro"
    (when *info-path*
      (let ((file (make-pathname *info-path*
                    (string-append (symbol->string memo-sym) ".txt"))))
        (when (file-exists? file)
          (let ((lines (read-file-lines file)))
            (let loop ((lines lines) (count 0))
              (when (and (not (null? lines)) (< count 20))
                (let ((line (car lines)))
                  (unless (string=? line "")
                    (display line)
                    (newline))
                  (loop (cdr lines) (+ count 1))))))
          (display "\n")
          (printf "[Full text: ~a]~%" file)
          (display "\n")))))

  (define (info . args)
    "Browse documentation"
    (info-init!)
    (let ((path (if (null? args) '(top) (cons 'top args))))
      (set! *info-history* (cons *info-node* *info-history*))
      (set! *info-node* path)
      (let ((node (info-find-node path)))
        (if node
            (info-display-node node)
            (printf "Node not found: ~a~%" args)))))

  (define (info?)
    "Show current location and navigation help"
    (printf "Current: ~a~%" *info-node*)
    (printf "History: ~a items~%" (length *info-history*))
    (display "\n")
    (display "Navigation:\n")
    (display "  (info 'topic)      Go to topic\n")
    (display "  (info-up)          Go up one level\n")
    (display "  (info-prev)        Go back in history\n")
    (display "  (info-search STR)  Search all docs\n")
    (display "  (info-index)       Show full index\n"))

  (define (info-up)
    "Go up one level"
    (when (> (length *info-node*) 1)
      (set! *info-node* (reverse (cdr (reverse *info-node*))))
      (info-display-node (info-find-node *info-node*))))

  (define (info-prev)
    "Go back in history"
    (when (not (null? *info-history*))
      (set! *info-node* (car *info-history*))
      (set! *info-history* (cdr *info-history*))
      (info-display-node (info-find-node *info-node*))))

  (define (info-next)
    "Go to next sibling (placeholder)"
    (display "Not yet implemented\n"))

  (define (info-search pattern)
    "Search all documentation for pattern"
    (info-init!)
    (display "\n")
    (printf "Searching for: ~a~%" pattern)
    (display "\n")
    (when *info-path*
      (let ((files (glob-files *info-path* "*.txt")))
        (for-each
          (lambda (file)
            (let ((matches (info-grep-file file pattern)))
              (when (not (null? matches))
                (printf "~a:~%" (pathname-strip-directory file))
                (for-each (lambda (m) (printf "  ~a~%" m))
                          (take matches (min 3 (length matches))))
                (display "\n"))))
          files))))

  (define (info-grep-file file pattern)
    "Search file for pattern, return matching lines (case-insensitive)"
    (guard (exn [#t '()])
      (let ((pattern-lower (string-downcase pattern)))
        (with-input-from-file file
          (lambda ()
            (let loop ((lines '()))
              (let ((line (get-line (current-input-port))))
                (if (eof-object? line)
                    (reverse lines)
                    (loop (if (string-contains (string-downcase line) pattern-lower)
                              (cons line lines)
                              lines))))))))))

  ;; string-downcase is provided by (rnrs unicode)

  (define (info-index)
    "Show complete index of all topics"
    (display "\n")
    (display "Library of Cyberspace - Documentation Index\n")
    (display "════════════════════════════════════════════\n")
    (display "\n")
    (info-print-tree *info-tree* 0))

  (define (info-print-tree tree depth)
    "Recursively print tree"
    (when (pair? tree)
      (let ((name (car tree))
            (title (if (> (length tree) 1) (cadr tree) ""))
            (children (filter pair? (if (> (length tree) 2) (cddr tree) '()))))
        (printf "~a~a -~a~%"
                (make-string (* depth 2) #\space)
                name
                title)
        (for-each
          (lambda (child)
            (info-print-tree child (+ depth 1)))
          children))))

  (define (info-hierarchical node)
    "Display node in hierarchical outline format"
    (info-print-tree (info-find-node node) 0))

) ;; end library
