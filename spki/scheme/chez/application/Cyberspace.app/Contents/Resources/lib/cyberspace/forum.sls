;;; forum.sls - Realm forum (VAX Notes style)
;;; Library of Cyberspace - Chez Port
;;;
;;; One forum per realm. Topics and replies. Sequential numbering.
;;; No likes. No avatars. Just text and cryptographic identity.
;;;
;;; Heritage: PLATO Notes -> BBS -> VAX Notes -> Usenet -> Cyberspace
;;;
;;; Ported from Chicken's forum.scm.
;;; Changes: module -> library, #!optional -> get-opt,
;;;          srfi-1/13/69 inlined or via compat, Chicken sort -> Chez sort,
;;;          seconds->local-time -> date(1) shell.

(library (cyberspace forum)
  (export
    ;; Forum navigation
    forum
    topics
    read-topic
    note

    ;; Posting
    post
    reply

    ;; State accessors
    current-topic
    forum-path)

  (import (rnrs)
          (only (chezscheme)
                printf format void sort)
          (cyberspace chicken-compatibility chicken)
          (only (cyberspace chicken-compatibility file)
                directory-exists? create-directory directory
                get-environment-variable current-seconds)
          (only (cyberspace chicken-compatibility process)
                with-input-from-pipe read-line))

  ;; ============================================================
  ;; Inline Helpers
  ;; ============================================================

  (define (string-suffix? suffix str)
    (let ((slen (string-length str))
          (xlen (string-length suffix)))
      (and (>= slen xlen)
           (string=? (substring str (- slen xlen) slen) suffix))))

  (define (string-prefix? prefix str)
    (and (>= (string-length str) (string-length prefix))
         (string=? (substring str 0 (string-length prefix)) prefix)))

  (define (string-pad-left str len . opts)
    ;; Left-pad str to len with char (default space)
    (let ((ch (if (null? opts) #\space (car opts)))
          (slen (string-length str)))
      (if (>= slen len)
          (substring str (- slen len) slen)
          (string-append (make-string (- len slen) ch) str))))

  (define (pathname-strip-extension path)
    (let loop ((i (- (string-length path) 1)))
      (cond
        ((< i 0) path)
        ((char=? (string-ref path i) #\.) (substring path 0 i))
        ((char=? (string-ref path i) #\/) path)
        (else (loop (- i 1))))))

  (define (filter-map f lst)
    (let loop ((rest lst) (acc '()))
      (if (null? rest)
          (reverse acc)
          (let ((result (f (car rest))))
            (loop (cdr rest)
                  (if result (cons result acc) acc))))))

  (define (take lst n)
    (if (or (<= n 0) (null? lst))
        '()
        (cons (car lst) (take (cdr lst) (- n 1)))))

  ;; ============================================================
  ;; Forum State
  ;; ============================================================

  (define *forum-path* ".vault/forum")
  (define *current-topic* #f)

  ;; Exported getters (R6RS can't export assigned variables)
  (define (current-topic) *current-topic*)
  (define (forum-path) *forum-path*)

  ;; ============================================================
  ;; Time Formatting
  ;; ============================================================

  (define (format-time secs)
    ;; Format epoch seconds as "YYYY-MM-DD HH:MM" via date(1)
    (guard (exn [#t (number->string secs)])
      (let* ((s (number->string (exact (truncate secs))))
             (result (with-input-from-pipe
                       (string-append "date -r " s " '+%Y-%m-%d %H:%M' 2>/dev/null")
                       read-line)))
        (if (or (not result) (eof-object? result) (string=? result ""))
            (number->string secs)
            result))))

  ;; ============================================================
  ;; Storage
  ;; ============================================================

  (define (ensure-forum!)
    (unless (directory-exists? *forum-path*)
      (create-directory *forum-path* #t)))

  (define (topic-path n)
    (string-append *forum-path* "/" (number->string n) ".sexp"))

  (define (next-topic-number)
    (ensure-forum!)
    (let* ((files (directory *forum-path*))
           (nums (filter-map
                  (lambda (f)
                    (and (string-suffix? ".sexp" f)
                         (not (string-prefix? "." f))
                         (string->number (pathname-strip-extension f))))
                  files)))
      (if (null? nums) 1 (+ 1 (apply max nums)))))

  (define (load-topic n)
    (let ((path (topic-path n)))
      (and (file-exists? path)
           (with-input-from-file path read))))

  (define (save-topic! n topic)
    (ensure-forum!)
    (let ((path (topic-path n)))
      ;; R6RS with-output-to-file won't overwrite; delete first
      (when (file-exists? path)
        (delete-file path))
      (with-output-to-file path
        (lambda () (write topic) (newline)))))

  ;; ============================================================
  ;; Topic Structure
  ;; ============================================================

  (define (make-topic num subject author body)
    `(topic
      (number ,num)
      (subject ,subject)
      (author ,author)
      (created ,(current-seconds))
      (body ,body)
      (replies ())))

  (define (make-reply author body)
    `((author ,author)
      (created ,(current-seconds))
      (body ,body)))

  (define (topic-ref t key)
    (let ((pair (assq key (cdr t))))
      (and pair (cadr pair))))

  ;; ============================================================
  ;; Display Helpers
  ;; ============================================================

  (define (short-principal p)
    (if (> (string-length p) 8)
        (substring p 0 8)
        p))

  ;; ============================================================
  ;; Commands
  ;; ============================================================

  (define (forum)
    ;; Enter the forum. Show recent topics.
    (ensure-forum!)
    (print "")
    (print "\x2550;\x2550;\x2550; Realm Forum \x2550;\x2550;\x2550;")
    (print "")
    (topics 10)
    (print "")
    (print "(post \"subject\") to start topic, (read N) to read, (reply) to respond")
    (void))

  (define (topics . opts)
    ;; List recent topics.
    (let ((limit (get-opt opts 0 20)))
      (ensure-forum!)
      (let* ((files (directory *forum-path*))
             (nums (sort >
                    (filter-map
                     (lambda (f)
                       (and (string-suffix? ".sexp" f)
                            (string->number (pathname-strip-extension f))))
                     files)))
             (recent (take nums (min limit (length nums)))))
        (if (null? recent)
            (print "  No topics yet. (post \"subject\") to start one.")
            (for-each
             (lambda (n)
               (let ((t (load-topic n)))
                 (when t
                   (let* ((subj (topic-ref t 'subject))
                          (author (topic-ref t 'author))
                          (created (topic-ref t 'created))
                          (replies (topic-ref t 'replies))
                          (reply-count (if replies (length replies) 0)))
                     (printf "  ~a. ~a  [~a] ~a~a~%"
                             (string-pad-left (number->string n) 3)
                             (if (> (string-length subj) 40)
                                 (string-append (substring subj 0 37) "...")
                                 subj)
                             (short-principal (or author "?"))
                             (format-time (or created 0))
                             (if (> reply-count 0)
                                 (format #f " (~a)" reply-count)
                                 ""))))))
             (reverse recent))))))

  (define (read-topic n . opts)
    ;; Read topic N.
    (let ((t (load-topic n)))
      (if (not t)
          (printf "Topic ~a not found.~%" n)
          (begin
            (set! *current-topic* n)
            (print "")
            (printf "\x2550;\x2550;\x2550; ~a. ~a \x2550;\x2550;\x2550;~%" n (topic-ref t 'subject))
            (printf "From: ~a  Date: ~a~%"
                    (short-principal (or (topic-ref t 'author) "?"))
                    (format-time (or (topic-ref t 'created) 0)))
            (print "")
            (print (topic-ref t 'body))
            (print "")
            (let ((replies (topic-ref t 'replies)))
              (when (and replies (not (null? replies)))
                (print "\x2500;\x2500;\x2500; Replies \x2500;\x2500;\x2500;")
                (let loop ((rs replies) (i 1))
                  (when (not (null? rs))
                    (let* ((r (car rs))
                           (author (cadr (assq 'author r)))
                           (created (cadr (assq 'created r)))
                           (body (cadr (assq 'body r))))
                      (printf "~a.~a [~a] ~a~%"
                              n i
                              (short-principal (or author "?"))
                              (format-time (or created 0)))
                      (print body)
                      (print ""))
                    (loop (cdr rs) (+ i 1))))))
            (void)))))

  ;; Alias for Notes-style (note 42) command
  (define note read-topic)

  (define (post subject . opts)
    ;; Post new topic. If body omitted, prompts for it.
    (let* ((body (get-opt opts 0 #f))
           (num (next-topic-number))
           (author (or (get-environment-variable "CYBERSPACE_PRINCIPAL") "anonymous"))
           (content (or body (begin
                               (print "Enter message (end with '.' on blank line):")
                               (read-body)))))
      (save-topic! num (make-topic num subject author content))
      (set! *current-topic* num)
      (printf "Posted topic ~a: ~a~%" num subject)
      num))

  (define (reply . opts)
    ;; Reply to current topic.
    (let ((body (get-opt opts 0 #f)))
      (if (not *current-topic*)
          (print "No topic selected. (read N) first.")
          (let* ((t (load-topic *current-topic*))
                 (author (or (get-environment-variable "CYBERSPACE_PRINCIPAL") "anonymous"))
                 (content (or body (begin
                                     (print "Enter reply (end with '.' on blank line):")
                                     (read-body))))
                 (replies (or (topic-ref t 'replies) '()))
                 (new-reply (make-reply author content))
                 (updated (append replies (list new-reply))))
            (let ((new-topic
                   `(topic
                     (number ,(topic-ref t 'number))
                     (subject ,(topic-ref t 'subject))
                     (author ,(topic-ref t 'author))
                     (created ,(topic-ref t 'created))
                     (body ,(topic-ref t 'body))
                     (replies ,updated))))
              (save-topic! *current-topic* new-topic)
              (printf "Reply ~a.~a posted.~%" *current-topic* (length updated)))))))

  (define (read-body)
    ;; Read multi-line input until '.' on blank line.
    (let loop ((lines '()))
      (let ((line (read-line)))
        (if (or (eof-object? line) (string=? line "."))
            (string-intersperse (reverse lines) "\n")
            (loop (cons line lines))))))

) ;; end library
