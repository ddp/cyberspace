;;; ui.sls - Simple REPL UI (Chez Port)
;;; Library of Cyberspace
;;;
;;; User-friendly commands for cyberspace operations.
;;; No Scheme required - just simple commands.
;;;
;;; Ported from ui.scm.
;;; Copyright (c) 2026 Yoyodyne. See LICENSE.

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
                printf format void
                flush-output-port)
          (cyberspace chicken-compatibility chicken)
          (cyberspace enroll)
          (cyberspace capability)
          (cyberspace auto-enroll))

  ;; ============================================================
  ;; Command Handlers
  ;; ============================================================

  (define (cmd-enroll name)
    "Start or join a realm as NAME"
    (let ((sym (if (symbol? name) name (string->symbol name))))
      (auto-enroll-realm sym)))

  (define (cmd-join name host)
    "Join existing realm at HOST as NAME"
    (let ((sym (if (symbol? name) name (string->symbol name))))
      (join-realm sym host)))

  (define (cmd-status)
    "Show realm status"
    (let ((rs (realm-status))
          (es (enrollment-status)))
      (if (cdr (assq 'enrolled es))
          (begin
            (printf "~%Realm Status~%")
            (printf "  Master: ~a~%" (cdr (assq 'master rs)))
            (printf "  Role: ~a~%" (cdr (assq 'role rs)))
            (printf "  Members: ~a~%" (cdr (assq 'member-count rs)))
            (let ((scaling (cdr (assq 'scaling rs))))
              (when scaling
                (printf "  Effective capacity: ~a~%"
                        (cdr (assq 'effective-capacity scaling))))))
          (printf "~%Not enrolled in any realm.~%"))))

  (define (cmd-peers)
    "Show peer scaling"
    (let ((rs (realm-status)))
      (let ((scaling (cdr (assq 'scaling rs))))
        (if scaling
            (begin
              (printf "~%Peer Scaling (normalized to ~a)~%"
                      (cdr (assq 'reference scaling)))
              (printf "~%  ~a~a~a~%" "Node" (make-string 16 #\space) "Scale")
              (printf "  ~a~a~a~%" "----" (make-string 16 #\space) "-----")
              (for-each
                (lambda (m)
                  (let* ((name (->string (car m)))
                         (pad (make-string (max 1 (- 20 (string-length name))) #\space)))
                    (printf "  ~a~a~a~%" name pad (cdr m))))
                (cdr (assq 'members scaling))))
            (printf "~%No peers. Run 'enroll <name>' first.~%")))))

  (define (->string x)
    (if (string? x)
        x
        (format "~a" x)))

  (define (cmd-hw)
    "Show hardware info"
    (printf "~%Benchmarking...")
    (flush-output-port (current-output-port))
    (let ((hw (introspect-hardware)))
      (printf " done.~%~%")
      (printf "Hardware~%")
      (printf "  Hostname: ~a~%" (cadr (assq 'hostname (cdr hw))))
      (printf "  OS: ~a ~a~%" (cadr (assq 'os (cdr hw)))
                              (cadr (assq 'arch (cdr hw))))
      (printf "  CPU: ~a~%" (cadr (assq 'cpu (cdr hw))))
      (printf "  Cores: ~a~%" (cadr (assq 'cores (cdr hw))))
      (printf "  Memory: ~a GB~%" (cadr (assq 'memory-gb (cdr hw))))
      (printf "  Weave: ~a hashes/sec~%" (cadr (assq 'weave (cdr hw))))
      (printf "  Mobile: ~a~%" (if (cadr (assq 'mobile (cdr hw))) "yes" "no"))))

  (define (show-help)
    (printf "~%Cyberspace Scheme~%~%")
    (printf "  (library)         - Enter the Library~%")
    (printf "  (search 'topic)   - Search everything~%")
    (printf "  (status)          - Node status~%")
    (printf "  (inspect OBJ)     - Inspect anything~%~%")
    (printf "  (help 'topics)    - All help topics~%")
    (printf "  (.) status  (?) help  (bye) exit~%~%")
    (printf "Enrollment:~%")
    (printf "  enroll <name>        Start/join realm as <name>~%")
    (printf "  join <name> <host>   Join realm at <host>~%")
    (printf "  status               Show realm status~%")
    (printf "  peers                Show peer scaling~%")
    (printf "  hw                   Show hardware info~%")
    (printf "  quit                 Exit~%"))

  ;; ============================================================
  ;; REPL
  ;; ============================================================

  (define (parse-command line)
    "Parse command line into (cmd . args)"
    (let ((parts (split-whitespace line)))
      (if (null? parts)
          '(empty)
          (cons (string->symbol (car parts)) (cdr parts)))))

  (define (split-whitespace str)
    "Split string on whitespace"
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

  (define (run-command cmd args)
    "Execute a command"
    (guard (exn
      [#t (printf "Error: ~a~%"
                   (if (message-condition? exn)
                       (condition-message exn)
                       "unknown"))])
      (case cmd
        ((enroll)
         (if (null? args)
             (printf "Usage: enroll <name>~%")
             (cmd-enroll (car args))))
        ((join)
         (if (< (length args) 2)
             (printf "Usage: join <name> <host>~%")
             (cmd-join (car args) (cadr args))))
        ((status) (cmd-status))
        ((peers) (cmd-peers))
        ((hw) (cmd-hw))
        ((help ?) (show-help))
        ((quit exit q) 'quit)
        ((empty) #f)
        (else (printf "Unknown command: ~a (try 'help')~%" cmd)))))

  (define (start-ui)
    "Start the interactive UI"
    (printf "~%")
    (printf "Cyberspace Auto-Enroll~%")
    (printf "Type 'help' for commands.~%")
    (printf "~%")

    (let loop ()
      (display "> ")
      (flush-output-port (current-output-port))
      (let ((line (get-line (current-input-port))))
        (if (eof-object? line)
            (printf "~%Bye.~%")
            (let* ((parsed (parse-command line))
                   (result (run-command (car parsed) (cdr parsed))))
              (unless (eq? result 'quit)
                (loop)))))))

) ;; end library
