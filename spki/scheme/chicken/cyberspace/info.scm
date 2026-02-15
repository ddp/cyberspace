;;; info.scm - Hypertext documentation browser for Cyberspace
;;;
;;; Like info(1), but native to the REPL and the weave.
;;; Browses memos, API docs, and help topics.
;;; Buffered pager with top/bottom status lines.
;;;
;;; Copyright (c) 2026 Yoyodyne. See LICENSE.

(module info
  (info info? info-hierarchical
   info-search info-index
   info-next info-prev info-up
   info-page info-pager
   *info-node* *info-history*)

(import scheme)
(import (chicken base))
(import (chicken format))
(import (chicken string))
(import (chicken io))
(import (chicken file))
(import (chicken pathname))
(import (chicken irregex))
(import (chicken process-context))
(import srfi-1)
(import srfi-13)  ; string-pad-right

;; Terminal dimensions
(define (term-height)
  (let ((h (get-environment-variable "LINES")))
    (if h (string->number h) 24)))

(define (term-width)
  (let ((w (get-environment-variable "COLUMNS")))
    (if w (string->number w) 80)))

;; ANSI escape codes
(define (ansi-reverse s)
  (string-append "\x1b[7m" s "\x1b[0m"))

(define (ansi-clear-screen)
  (display "\x1b[2J\x1b[H"))

(define (ansi-goto row col)
  (printf "\x1b[~a;~aH" row col))

;; Pager state
(define *pager-buffer* '())     ; list of lines
(define *pager-offset* 0)       ; current scroll position
(define *pager-title* "")       ; top banner

(define (pager-content-height)
  "Height available for content (total - 2 status lines)"
  (- (term-height) 2))

(define (pager-display)
  "Display current page with status lines"
  (let* ((height (pager-content-height))
         (total (length *pager-buffer*))
         (width (term-width))
         (end (min (+ *pager-offset* height) total))
         (visible (take (drop *pager-buffer* *pager-offset*)
                        (- end *pager-offset*))))

    ;; Clear and position
    (ansi-clear-screen)

    ;; Top status line (reversed)
    (display (ansi-reverse
               (string-pad-right
                 (string-append " " *pager-title*)
                 width)))
    (newline)

    ;; Content
    (for-each
      (lambda (line)
        (print (if (> (string-length line) width)
                   (substring line 0 width)
                   line)))
      visible)

    ;; Pad to fill screen
    (let ((pad (- height (length visible))))
      (when (> pad 0)
        (do ((i 0 (+ i 1))) ((= i pad)) (newline))))

    ;; Bottom status line (reversed)
    (ansi-goto (term-height) 1)
    (display (ansi-reverse
               (string-pad-right
                 (sprintf " Line ~a-~a of ~a  [j/k:scroll  q:quit  /:search]"
                          (+ *pager-offset* 1)
                          end
                          total)
                 width)))))

(define (pager-down #!optional (n 1))
  "Scroll down n lines"
  (let ((max-offset (max 0 (- (length *pager-buffer*) (pager-content-height)))))
    (set! *pager-offset* (min max-offset (+ *pager-offset* n)))
    (pager-display)))

(define (pager-up #!optional (n 1))
  "Scroll up n lines"
  (set! *pager-offset* (max 0 (- *pager-offset* n)))
  (pager-display))

(define (pager-page-down)
  "Scroll down one page"
  (pager-down (pager-content-height)))

(define (pager-page-up)
  "Scroll up one page"
  (pager-up (pager-content-height)))

(define (pager-top)
  "Go to top"
  (set! *pager-offset* 0)
  (pager-display))

(define (pager-bottom)
  "Go to bottom"
  (set! *pager-offset* (max 0 (- (length *pager-buffer*) (pager-content-height))))
  (pager-display))

(define (info-pager lines title)
  "Display lines in pager with title"
  (set! *pager-buffer* lines)
  (set! *pager-offset* 0)
  (set! *pager-title* title)
  (pager-display)

  ;; Simple key loop
  (let loop ()
    (let ((c (read-char)))
      (cond
        ((or (eof-object? c) (char=? c #\q))
         (print "")  ; exit pager
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
    (let ((lines (with-input-from-file file read-lines)))
      (info-pager lines (pathname-strip-directory file)))))

;; Current state
(define *info-node* '(top))      ; current location
(define *info-history* '())       ; breadcrumb trail
(define *info-path* #f)           ; path to docs

;; Initialize path to memos
(define (info-init!)
  (let ((paths (list
                 "./docs/notes"
                 "../docs/notes"
                 "~/cyberspace/spki/scheme/docs/notes")))
    (set! *info-path*
      (find directory-exists? paths))))

;; Node structure: (category topic subtopic ...)
;; Maps to memo files and sections

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
           (let ((children (cdddr tree)))
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

      (print "")
      (print "═══════════════════════════════════════════════════════")
      (printf "  ~a~%" title)
      (print "═══════════════════════════════════════════════════════")
      (print "")

      ;; Show memo content if linked
      (when memo
        (info-show-memo memo))

      ;; Show children as menu
      (when (not (null? children))
        (print "Subtopics:")
        (print "")
        (for-each
          (lambda (child)
            (printf "  * ~a -~a~%"
                    (car child)
                    (if (> (length child) 1) (cadr child) "")))
          children)
        (print ""))

      ;; Navigation hint
      (print "───────────────────────────────────────────────────────")
      (print "  (info 'topic)  Navigate    (info-search \"term\")  Search")
      (print "  (info-up)      Go up       (info-index)          Index")
      (print ""))))

(define (info-show-memo memo-sym)
  "Display memo abstract/intro"
  (when *info-path*
    (let ((file (make-pathname *info-path*
                  (string-append (symbol->string memo-sym) ".txt"))))
      (when (file-exists? file)
        (let ((lines (with-input-from-file file read-lines)))
          ;; Show first ~20 non-empty lines as abstract
          (let loop ((lines lines) (count 0))
            (when (and (not (null? lines)) (< count 20))
              (let ((line (car lines)))
                (unless (string=? line "")
                  (print line))
                (loop (cdr lines) (+ count 1))))))
        (print "")
        (printf "[Full text: ~a]~%" file)
        (print "")))))

(define (info . args)
  "Browse documentation
   (info)           - top level
   (info 'topic)    - go to topic
   (info 'a 'b 'c)  - go to nested path"
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
  (print "")
  (print "Navigation:")
  (print "  (info 'topic)      Go to topic")
  (print "  (info-up)          Go up one level")
  (print "  (info-prev)        Go back in history")
  (print "  (info-search STR)  Search all docs")
  (print "  (info-index)       Show full index"))

(define (info-up)
  "Go up one level"
  (when (> (length *info-node*) 1)
    (set! *info-node* (drop-right *info-node* 1))
    (info-display-node (info-find-node *info-node*))))

(define (info-prev)
  "Go back in history"
  (when (not (null? *info-history*))
    (set! *info-node* (car *info-history*))
    (set! *info-history* (cdr *info-history*))
    (info-display-node (info-find-node *info-node*))))

(define (info-next)
  "Go to next sibling (placeholder)"
  (print "Not yet implemented"))

(define (info-search pattern)
  "Search all documentation for pattern"
  (info-init!)
  (print "")
  (printf "Searching for: ~a~%" pattern)
  (print "")
  (when *info-path*
    (let ((files (glob (make-pathname *info-path* "*.txt"))))
      (for-each
        (lambda (file)
          (let ((matches (info-grep-file file pattern)))
            (when (not (null? matches))
              (printf "~a:~%" (pathname-strip-directory file))
              (for-each (lambda (m) (printf "  ~a~%" m))
                        (take matches (min 3 (length matches))))
              (print ""))))
        files))))

(define (info-grep-file file pattern)
  "Search file for pattern, return matching lines"
  (let ((rx (irregex pattern 'i)))
    (with-input-from-file file
      (lambda ()
        (let loop ((lines '()))
          (let ((line (read-line)))
            (if (eof-object? line)
                (reverse lines)
                (loop (if (irregex-search rx line)
                          (cons line lines)
                          lines)))))))))

(define (info-index)
  "Show complete index of all topics"
  (print "")
  (print "Library of Cyberspace - Documentation Index")
  (print "════════════════════════════════════════════")
  (print "")
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

) ; end module
