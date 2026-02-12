;;; Process Compatibility Library
;;; Library of Cyberspace - Chez Port
;;;
;;; Maps Chicken's (chicken process) and (chicken io) shell
;;; execution API onto Chez Scheme's process-port facilities.
;;;
;;;   with-input-from-pipe: run command, parameterize current-input-port
;;;   read-line: 0-arg wrapper around Chez's get-line
;;;   system: re-exported from (chezscheme)
;;;
;;; Used by: os (shell-command, shell-lines, shell-success?)

(library (cyberspace chicken-compatibility process)
  (export
    with-input-from-pipe
    read-line
    system)

  (import (except (rnrs) current-input-port)
          (only (chezscheme)
                open-process-ports current-transcoder
                parameterize system current-input-port))

  ;; Chicken's read-line: reads from current-input-port, no args
  ;; Chez's get-line requires a port argument
  (define (read-line)
    (get-line (current-input-port)))

  ;; Chicken's with-input-from-pipe: run shell command, bind stdout
  ;; to current-input-port, execute thunk.
  ;;
  ;; Chez's open-process-ports returns 4 values:
  ;;   (values stdin stdout stderr pid)
  ;; We parameterize current-input-port to stdout and run the thunk.
  (define (with-input-from-pipe command thunk)
    (let-values (((to-stdin from-stdout from-stderr pid)
                  (open-process-ports command 'line (current-transcoder))))
      (dynamic-wind
        (lambda () #f)
        (lambda ()
          (parameterize ((current-input-port from-stdout))
            (thunk)))
        (lambda ()
          (close-port to-stdin)
          (close-port from-stdout)
          (close-port from-stderr)))))

) ;; end library
