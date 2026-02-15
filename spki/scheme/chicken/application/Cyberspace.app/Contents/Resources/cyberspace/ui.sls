;;; ui.sls - Simple REPL UI
;;; Library of Cyberspace - Chez Scheme Port
;;;
;;; User-friendly commands for cyberspace operations.
;;; No Scheme required - just simple commands.
;;;
;;; Ported from Chicken's ui.scm.
;;; Changes: module -> library, handle-exceptions -> guard,
;;;          read-line -> get-line, ->string via compat.

(library (cyberspace ui)
  (export
    ;; Main UI
    start-ui
    ;; Commands (also available directly)
    cmd-enroll
    cmd-join
    cmd-status
    cmd-peers
    cmd-hw)

  (import (rnrs)
          (only (chezscheme)
                printf format
                current-time time-second)
          (cyberspace enroll)
          (cyberspace capability)
          (cyberspace auto-enroll)
          (cyberspace chicken-compatibility chicken))

  ;; ============================================================
  ;; Helpers
  ;; ============================================================

  (define (->string x)
    (cond ((string? x) x)
          ((symbol? x) (symbol->string x))
          ((number? x) (number->string x))
          (else (format "~a" x))))

  (define (flush) (flush-output-port (current-output-port)))

  (define (read-line-from port)
    (get-line port))

  ;; ============================================================
  ;; Command Handlers
  ;; ============================================================

  (define (cmd-enroll name)
    (let ((sym (if (symbol? name) name (string->symbol name))))
      (auto-enroll-realm sym)))

  (define (cmd-join name host)
    (let ((sym (if (symbol? name) name (string->symbol name))))
      (join-realm sym host)))

  (define (cmd-status)
    (let ((rs (realm-status))
          (es (enrollment-status)))
      (if (cdr (assq 'enrolled es))
          (begin
            (printf "~nRealm Status~n")
            (printf "  Master: ~a~n" (cdr (assq 'master rs)))
            (printf "  Role: ~a~n" (cdr (assq 'role rs)))
            (printf "  Members: ~a~n" (cdr (assq 'member-count rs)))
            (let ((scaling (cdr (assq 'scaling rs))))
              (when scaling
                (printf "  Effective capacity: ~a~n"
                        (cdr (assq 'effective-capacity scaling))))))
          (printf "~nNot enrolled in any realm.~n"))))

  (define (cmd-peers)
    (let ((rs (realm-status)))
      (let ((scaling (cdr (assq 'scaling rs))))
        (if scaling
            (begin
              (printf "~nPeer Scaling (normalized to ~a)~n"
                      (cdr (assq 'reference scaling)))
              (printf "~%  ~a~a~a~%" "Node" (make-string 16 #\space) "Scale")
              (printf "  ~a~a~a~%" "----" (make-string 16 #\space) "-----")
              (for-each
                (lambda (m)
                  (let* ((name (->string (car m)))
                         (pad (make-string (max 1 (- 20 (string-length name))) #\space)))
                    (printf "  ~a~a~a~%" name pad (cdr m))))
                (cdr (assq 'members scaling))))
            (printf "~nNo peers. Run 'enroll <name>' first.~n")))))

  (define (cmd-hw)
    (printf "~nBenchmarking...")
    (flush)
    (let ((hw (introspect-hardware)))
      (printf " done.~n~n")
      (printf "Hardware~n")
      (printf "  Hostname: ~a~n" (cadr (assq 'hostname (cdr hw))))
      (printf "  OS: ~a ~a~n" (cadr (assq 'os (cdr hw)))
                              (cadr (assq 'arch (cdr hw))))
      (printf "  CPU: ~a~n" (cadr (assq 'cpu (cdr hw))))
      (printf "  Cores: ~a~n" (cadr (assq 'cores (cdr hw))))
      (printf "  Memory: ~a GB~n" (cadr (assq 'memory-gb (cdr hw))))
      (printf "  Weave: ~a hashes/sec~n" (cadr (assq 'weave (cdr hw))))
      (printf "  Mobile: ~a~n" (if (cadr (assq 'mobile (cdr hw))) "yes" "no"))))

  (define (show-help)
    (printf "~nCyberspace Scheme~n~n")
    (printf "  (library)         - Enter the Library~n")
    (printf "  (search 'topic)   - Search everything~n")
    (printf "  (status)          - Node status~n")
    (printf "  (inspect OBJ)     - Inspect anything~n~n")
    (printf "  (help 'topics)    - All help topics~n")
    (printf "  (.) status  (?) help  (bye) exit~n~n")
    (printf "Enrollment:~n")
    (printf "  enroll <name>        Start/join realm as <name>~n")
    (printf "  join <name> <host>   Join realm at <host>~n")
    (printf "  status               Show realm status~n")
    (printf "  peers                Show peer scaling~n")
    (printf "  hw                   Show hardware info~n")
    (printf "  quit                 Exit~n"))

  ;; ============================================================
  ;; Command Parser
  ;; ============================================================

  (define (split-whitespace str)
    (let loop ((chars (string->list str))
               (current '())
               (result '()))
      (cond
        ((null? chars)
         (if (null? current)
             (reverse result)
             (reverse (cons (list->string (reverse current)) result))))
        ((char-whitespace? (car chars))
         (if (null? current)
             (loop (cdr chars) '() result)
             (loop (cdr chars) '() (cons (list->string (reverse current)) result))))
        (else
         (loop (cdr chars) (cons (car chars) current) result)))))

  (define (parse-command line)
    (let ((parts (split-whitespace line)))
      (if (null? parts)
          '(empty)
          (cons (string->symbol (car parts)) (cdr parts)))))

  (define (run-command cmd args)
    (guard (exn [#t (printf "Error: ~a~n"
                           (if (message-condition? exn)
                               (condition-message exn)
                               "unknown"))])
      (case cmd
        ((enroll)
         (if (null? args)
             (printf "Usage: enroll <name>~n")
             (cmd-enroll (car args))))
        ((join)
         (if (< (length args) 2)
             (printf "Usage: join <name> <host>~n")
             (cmd-join (car args) (cadr args))))
        ((status) (cmd-status))
        ((peers) (cmd-peers))
        ((hw) (cmd-hw))
        ((help ?) (show-help))
        ((quit exit q) 'quit)
        ((empty) #f)
        (else (printf "Unknown command: ~a (try 'help')~n" cmd)))))

  ;; ============================================================
  ;; REPL
  ;; ============================================================

  (define (start-ui)
    (printf "~n")
    (printf "Cyberspace Auto-Enroll~n")
    (printf "Type 'help' for commands.~n")
    (printf "~n")

    (let loop ()
      (display "> ")
      (flush)
      (let ((line (read-line-from (current-input-port))))
        (if (or (eof-object? line) (not line))
            (printf "~nBye.~n")
            (let* ((parsed (parse-command line))
                   (result (run-command (car parsed) (cdr parsed))))
              (unless (eq? result 'quit)
                (loop)))))))

) ;; end library
