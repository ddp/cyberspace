;;; board.scm - Realm bulletin board (VAX Notes style)
;;;
;;; One board per realm. Topics and replies. Sequential numbering.
;;; No likes. No avatars. Just text and cryptographic identity.
;;;
;;; Heritage: PLATO Notes -> VAX Notes -> Cyberspace
;;;

(module board
  (;; Board navigation
   board
   topics
   read-topic
   note  ; alias for read-topic

   ;; Posting
   post
   reply

   ;; State
   *current-topic*
   *board-path*)

  (import scheme
          (chicken base)
          (chicken format)
          (chicken file)
          (chicken io)
          (chicken pathname)
          (chicken string)
          (chicken time)
          (chicken time posix)
          (chicken sort)
          (chicken process-context)
          srfi-1
          srfi-13
          srfi-69)

  ;;; ============================================================
  ;;; Board State
  ;;; ============================================================

  (define *board-path* ".vault/board")
  (define *current-topic* #f)

  ;;; ============================================================
  ;;; Storage
  ;;; ============================================================

  (define (ensure-board!)
    "Create board directory if needed."
    (unless (directory-exists? *board-path*)
      (create-directory *board-path* #t)))

  (define (topic-path n)
    "Path to topic N."
    (string-append *board-path* "/" (number->string n) ".sexp"))

  (define (next-topic-number)
    "Get next available topic number."
    (ensure-board!)
    (let* ((files (directory *board-path*))
           (nums (filter-map
                  (lambda (f)
                    (and (string-suffix? ".sexp" f)
                         (not (string-contains f "."))
                         (string->number (pathname-strip-extension f))))
                  files)))
      (if (null? nums) 1 (+ 1 (apply max nums)))))

  (define (load-topic n)
    "Load topic N from disk."
    (let ((path (topic-path n)))
      (and (file-exists? path)
           (with-input-from-file path read))))

  (define (save-topic! n topic)
    "Save topic N to disk."
    (ensure-board!)
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
    "Format timestamp for display."
    (let ((tm (seconds->local-time secs)))
      (sprintf "~a-~a-~a ~a:~a"
               (+ 1900 (vector-ref tm 5))
               (string-pad (number->string (+ 1 (vector-ref tm 4))) 2 #\0)
               (string-pad (number->string (vector-ref tm 3)) 2 #\0)
               (string-pad (number->string (vector-ref tm 2)) 2 #\0)
               (string-pad (number->string (vector-ref tm 1)) 2 #\0))))

  (define (short-principal p)
    "Truncate principal for display."
    (if (> (string-length p) 8)
        (substring p 0 8)
        p))

  ;;; ============================================================
  ;;; Commands
  ;;; ============================================================

  (define (board)
    "Enter the board. Show recent topics."
    (ensure-board!)
    (print "")
    (print "═══ Realm Board ═══")
    (print "")
    (topics 10)
    (print "")
    (print "(post \"subject\") to start topic, (read N) to read, (reply) to respond")
    (void))

  (define (topics #!optional (limit 20))
    "List recent topics."
    (ensure-board!)
    (let* ((files (directory *board-path*))
           (nums (sort
                  (filter-map
                   (lambda (f)
                     (and (string-suffix? ".sexp" f)
                          (string->number (pathname-strip-extension f))))
                   files)
                  >))
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
                           (string-pad (number->string n) 3)
                           (if (> (string-length subj) 40)
                               (string-append (substring subj 0 37) "...")
                               subj)
                           (short-principal (or author "?"))
                           (format-time (or created 0))
                           (if (> reply-count 0)
                               (sprintf " (~a)" reply-count)
                               ""))))))
           (reverse recent)))))

  (define (read-topic n #!optional reply-num)
    "Read topic N, optionally specific reply."
    (let ((t (load-topic n)))
      (if (not t)
          (printf "Topic ~a not found.~%" n)
          (begin
            (set! *current-topic* n)
            (print "")
            (printf "═══ ~a. ~a ═══~%" n (topic-ref t 'subject))
            (printf "From: ~a  Date: ~a~%"
                    (short-principal (or (topic-ref t 'author) "?"))
                    (format-time (or (topic-ref t 'created) 0)))
            (print "")
            (print (topic-ref t 'body))
            (print "")
            (let ((replies (topic-ref t 'replies)))
              (when (and replies (not (null? replies)))
                (print "─── Replies ───")
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

  ;; Alias for Notes-style (read 42) command - exported as note
  (define note read-topic)

  (define (post subject #!optional body)
    "Post new topic. If body omitted, prompts for it."
    (let* ((num (next-topic-number))
           (author (or (get-environment-variable "CYBERSPACE_PRINCIPAL") "anonymous"))
           (content (or body (begin
                               (print "Enter message (end with '.' on blank line):")
                               (read-body)))))
      (save-topic! num (make-topic num subject author content))
      (set! *current-topic* num)
      (printf "Posted topic ~a: ~a~%" num subject)
      num))

  (define (reply #!optional body)
    "Reply to current topic."
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
            (printf "Reply ~a.~a posted.~%" *current-topic* (length updated))))))

  (define (read-body)
    "Read multi-line input until '.' on blank line."
    (let loop ((lines '()))
      (let ((line (read-line)))
        (if (or (eof-object? line) (string=? line "."))
            (string-intersperse (reverse lines) "\n")
            (loop (cons line lines))))))

) ;; end module board
