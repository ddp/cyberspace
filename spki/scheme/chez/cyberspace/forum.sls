;;; forum.scm - Realm forum (VAX Notes style)
;;; Library of Cyberspace - Chez Port
;;;
;;; One forum per realm. Topics and replies. Sequential numbering.
;;; No likes. No avatars. Just text and cryptographic identity.
;;;
;;; Heritage: PLATO Notes -> BBS -> VAX Notes -> Usenet -> Cyberspace

(library (cyberspace forum)
  (export
    ;; Forum navigation
    forum
    topics
    read-topic
    note  ; alias for read-topic

    ;; Posting
    post
    reply

    ;; State
    *current-topic*
    *forum-path*)

  (import (except (rnrs) with-input-from-file with-output-to-file file-exists? delete-file find)
          (only (chezscheme)
                printf format void
                with-input-from-file with-output-to-file
                file-exists? delete-file
                directory-list
                system sort
                getenv)
          (cyberspace chicken-compatibility chicken))

  ;;; ============================================================
  ;;; Forum State
  ;;; ============================================================

  (define *forum-path* ".vault/forum")
  (define *current-topic-box* (vector #f))
  (define-syntax *current-topic*
    (identifier-syntax
      [id (vector-ref *current-topic-box* 0)]
      [(set! id val) (vector-set! *current-topic-box* 0 val)]))

  ;;; ============================================================
  ;;; Storage
  ;;; ============================================================

  (define (ensure-forum!)
    "Create forum directory if needed."
    (unless (file-exists? *forum-path*)
      (system (string-append "mkdir -p " *forum-path*))))

  (define (topic-path n)
    "Path to topic N."
    (string-append *forum-path* "/" (number->string n) ".sexp"))

  (define (strip-extension filename)
    "Remove .sexp extension from filename."
    (let ((len (string-length filename)))
      (if (and (> len 5) (string=? (substring filename (- len 5) len) ".sexp"))
          (substring filename 0 (- len 5))
          filename)))

  (define (next-topic-number)
    "Get next available topic number."
    (ensure-forum!)
    (let* ((files (directory-list *forum-path*))
           (nums (filter-map
                  (lambda (f)
                    (and (string-suffix? ".sexp" f)
                         (string->number (strip-extension f))))
                  files)))
      (if (null? nums) 1 (+ 1 (apply max nums)))))

  (define (load-topic n)
    "Load topic N from disk."
    (let ((path (topic-path n)))
      (and (file-exists? path)
           (with-input-from-file path read))))

  (define (save-topic! n topic)
    "Save topic N to disk."
    (ensure-forum!)
    (with-output-to-file (topic-path n)
      (lambda () (write topic) (newline))))

  ;;; ============================================================
  ;;; Topic Structure
  ;;; ============================================================
  ;;
  ;; (topic
  ;;   (number 42)
  ;;   (subject "Design discussion")
  ;;   (author "abc123...")  ; principal hash
  ;;   (created 1234567890)
  ;;   (body "First post content...")
  ;;   (replies
  ;;     ((number 1)
  ;;      (author "def456...")
  ;;      (created 1234567900)
  ;;      (body "Reply content..."))
  ;;     ...))

  (define (make-topic num subject author body)
    "Create new topic structure."
    `(topic
      (number ,num)
      (subject ,subject)
      (author ,author)
      (created ,(current-seconds))
      (body ,body)
      (replies ())))

  (define (make-reply author body)
    "Create reply structure."
    `((author ,author)
      (created ,(current-seconds))
      (body ,body)))

  (define (topic-ref t key)
    "Get field from topic."
    (let ((pair (assq key (cdr t))))
      (and pair (cadr pair))))

  ;;; ============================================================
  ;;; Display Helpers
  ;;; ============================================================

  (define (format-time secs)
    "Format timestamp for display (Hinnant's civil_from_days)."
    (let* ((z (+ (quotient secs 86400) 719468))
           (era (quotient (if (>= z 0) z (- z 146096)) 146097))
           (doe (- z (* era 146097)))
           (yoe (quotient (- doe (+ (quotient doe 1460)
                                    (- (quotient doe 36524))
                                    (quotient doe 146096)))
                          365))
           (y (+ yoe (* era 400)))
           (doy (- doe (- (+ (* 365 yoe) (quotient yoe 4))
                          (quotient yoe 100))))
           (mp (quotient (+ (* 5 doy) 2) 153))
           (d (+ (- doy (quotient (+ (* 153 mp) 2) 5)) 1))
           (m (+ mp (if (< mp 10) 3 -9)))
           (y* (+ y (if (<= m 2) 1 0)))
           (time-of-day (modulo secs 86400))
           (hh (quotient time-of-day 3600))
           (mm (quotient (modulo time-of-day 3600) 60)))
      (string-append
        (number->string y*) "-"
        (if (< m 10) "0" "") (number->string m) "-"
        (if (< d 10) "0" "") (number->string d) " "
        (if (< hh 10) "0" "") (number->string hh) ":"
        (if (< mm 10) "0" "") (number->string mm))))

  (define (short-principal p)
    "Truncate principal for display."
    (if (> (string-length p) 8)
        (substring p 0 8)
        p))

  (define (string-pad-left s width ch)
    "Pad string on left to width with character ch."
    (let ((len (string-length s)))
      (if (>= len width)
          s
          (string-append (make-string (- width len) ch) s))))

  ;;; ============================================================
  ;;; Commands
  ;;; ============================================================

  (define (forum)
    "Enter the forum. Show recent topics."
    (ensure-forum!)
    (print "")
    (print "=== Realm Forum ===")
    (print "")
    (topics 10)
    (print "")
    (print "(post \"subject\") to start topic, (read-topic N) to read, (reply) to respond")
    (void))

  (define (topics . rest)
    "List recent topics."
    (let ((limit (if (null? rest) 20 (car rest))))
      (ensure-forum!)
      (let* ((files (directory-list *forum-path*))
             (nums (sort >
                     (filter-map
                      (lambda (f)
                        (and (string-suffix? ".sexp" f)
                             (string->number (strip-extension f))))
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
                             (string-pad-left (number->string n) 3 #\space)
                             (if (> (string-length subj) 40)
                                 (string-append (substring subj 0 37) "...")
                                 subj)
                             (short-principal (or author "?"))
                             (format-time (or created 0))
                             (if (> reply-count 0)
                                 (string-append " (" (number->string reply-count) ")")
                                 ""))))))
             (reverse recent))))))

  (define (read-topic n . rest)
    "Read topic N, optionally specific reply."
    (let ((t (load-topic n)))
      (if (not t)
          (printf "Topic ~a not found.~%" n)
          (begin
            (set! *current-topic* n)
            (print "")
            (printf "=== ~a. ~a ===~%" n (topic-ref t 'subject))
            (printf "From: ~a  Date: ~a~%"
                    (short-principal (or (topic-ref t 'author) "?"))
                    (format-time (or (topic-ref t 'created) 0)))
            (print "")
            (print (topic-ref t 'body))
            (print "")
            (let ((replies (topic-ref t 'replies)))
              (when (and replies (not (null? replies)))
                (print "--- Replies ---")
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

  (define (post subject . rest)
    "Post new topic. Optional body as argument."
    (let* ((body (if (null? rest) #f (car rest)))
           (num (next-topic-number))
           (author (or (getenv "CYBERSPACE_PRINCIPAL") "anonymous"))
           (content (or body
                        (begin
                          (print "Enter message (end with '.' on blank line):")
                          (read-body)))))
      (save-topic! num (make-topic num subject author content))
      (set! *current-topic* num)
      (printf "Posted topic ~a: ~a~%" num subject)
      num))

  (define (reply . rest)
    "Reply to current topic."
    (let ((body (if (null? rest) #f (car rest))))
      (if (not *current-topic*)
          (print "No topic selected. (read-topic N) first.")
          (let* ((t (load-topic *current-topic*))
                 (author (or (getenv "CYBERSPACE_PRINCIPAL") "anonymous"))
                 (content (or body
                              (begin
                                (print "Enter reply (end with '.' on blank line):")
                                (read-body))))
                 (replies (or (topic-ref t 'replies) '()))
                 (new-reply (make-reply author content))
                 (updated (append replies (list new-reply))))
            ;; Update topic with new reply
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
    "Read multi-line input until '.' on blank line."
    (let loop ((lines '()))
      (let ((line (get-line (current-input-port))))
        (if (or (eof-object? line) (string=? line "."))
            (string-intersperse (reverse lines) "\n")
            (loop (cons line lines))))))

) ;; end library
