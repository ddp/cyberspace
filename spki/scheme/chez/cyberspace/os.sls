;;; os.sls - Operating System Introspection (Chez Port)
;;; Library of Cyberspace
;;;
;;; Level 0 module: no cyberspace dependencies.
;;; Foundation for platform-portable code.
;;;
;;; "Know thyself" - Delphi
;;; "uname -a" - Unix
;;;
;;; Ported from os.scm.
;;; Copyright (c) 2026 Yoyodyne. See LICENSE.

(library (cyberspace os)
  (export
    ;; Core identity
    os-type os-name os-version os-arch os-arch-name os-platform
    ;; Predicates
    darwin? linux? freebsd? arm64? x86-64? apple-silicon?
    ;; Hardware
    cpu-brand cpu-cores memory-gb hostname
    ;; Paths
    homebrew-prefix lib-path include-path
    ;; Feature detection
    has-libsodium? has-codesign? has-notarytool? has-homebrew?
    ;; System utilities
    open-keychain open-tickets open-console open-monitor open-finder
    ;; Shell utilities
    shell-command shell-lines shell-success?
    ;; Session statistics
    *session-stats*
    session-stat! session-stat session-stats session-stats-reset!
    ;; Cleanup hooks
    register-cleanup-hook! run-cleanup-hooks! cleanup-hooks-status
    ;; Box drawing
    make-box box-top box-bottom box-separator box-line box-print box-width
    *box-square* *box-rounded* *box-double*
    string-pad-left string-truncate string-display-width)

  (import (rnrs)
          (only (chezscheme)
                printf format void system
                file-exists? with-output-to-string
                open-process-ports native-transcoder
                scheme-environment top-level-value
                getenv)
          (cyberspace chicken-compatibility hashtable))

  ;; ============================================================
  ;; Shell Utilities
  ;; ============================================================

  (define (shell-command cmd)
    "Run shell command, return trimmed output or #f."
    (guard (exn [#t #f])
      (let-values (((to-stdin from-stdout from-stderr)
                    (open-process-ports cmd 'line (native-transcoder))))
        (let ((result (get-line from-stdout)))
          (close-port to-stdin)
          (close-port from-stdout)
          (close-port from-stderr)
          (if (eof-object? result) #f result)))))

  (define (shell-lines cmd)
    "Run shell command, return list of lines."
    (guard (exn [#t '()])
      (let-values (((to-stdin from-stdout from-stderr)
                    (open-process-ports cmd 'line (native-transcoder))))
        (let loop ((lines '()))
          (let ((line (get-line from-stdout)))
            (if (eof-object? line)
                (begin
                  (close-port to-stdin)
                  (close-port from-stdout)
                  (close-port from-stderr)
                  (reverse lines))
                (loop (cons line lines))))))))

  (define (shell-success? cmd)
    "Return #t if command exits successfully."
    (zero? (system (string-append cmd " >/dev/null 2>&1"))))

  ;; ============================================================
  ;; Core Identity (cached at load time)
  ;; ============================================================

  (define *os-name* (or (shell-command "uname -s") "Unknown"))
  (define *os-version* (or (shell-command "uname -r") ""))
  (define *os-arch-name* (or (shell-command "uname -m") "unknown"))

  (define (os-name) *os-name*)
  (define (os-version) *os-version*)
  (define (os-arch-name) *os-arch-name*)

  (define (os-type)
    (cond
     ((string=? *os-name* "Darwin") 'darwin)
     ((string=? *os-name* "Linux") 'linux)
     ((string=? *os-name* "FreeBSD") 'freebsd)
     (else 'unknown)))

  (define (os-arch)
    (cond
     ((string=? *os-arch-name* "arm64") 'arm64)
     ((string=? *os-arch-name* "aarch64") 'arm64)
     ((string=? *os-arch-name* "x86_64") 'x86-64)
     ((string=? *os-arch-name* "amd64") 'x86-64)
     (else 'unknown)))

  (define (os-platform)
    (string-append *os-name* "-" *os-arch-name*))

  ;; ============================================================
  ;; Predicates
  ;; ============================================================

  (define (darwin?) (eq? (os-type) 'darwin))
  (define (linux?) (eq? (os-type) 'linux))
  (define (freebsd?) (eq? (os-type) 'freebsd))
  (define (arm64?) (eq? (os-arch) 'arm64))
  (define (x86-64?) (eq? (os-arch) 'x86-64))
  (define (apple-silicon?) (and (darwin?) (arm64?)))

  ;; ============================================================
  ;; Hardware Introspection
  ;; ============================================================

  (define (hostname)
    (or (shell-command "/bin/hostname") "localhost"))

  (define (cpu-brand)
    (cond
     ((darwin?) (shell-command "sysctl -n machdep.cpu.brand_string"))
     ((linux?) (shell-command "grep -m1 'model name' /proc/cpuinfo | cut -d: -f2 | xargs"))
     (else #f)))

  (define (cpu-cores)
    (cond
     ((darwin?)
      (let ((n (shell-command "sysctl -n hw.ncpu")))
        (and n (string->number n))))
     ((linux?)
      (let ((n (shell-command "nproc")))
        (and n (string->number n))))
     (else #f)))

  (define (memory-gb)
    (cond
     ((darwin?)
      (let ((bytes (shell-command "sysctl -n hw.memsize")))
        (and bytes
             (exact (round (/ (string->number bytes) 1073741824))))))
     ((linux?)
      (let ((kb (shell-command "grep MemTotal /proc/meminfo | awk '{print $2}'")))
        (and kb
             (exact (round (/ (string->number kb) 1048576))))))
     (else #f)))

  ;; ============================================================
  ;; Platform Paths
  ;; ============================================================

  (define (homebrew-prefix)
    (cond
     ((and (darwin?) (arm64?) (file-exists? "/opt/homebrew")) "/opt/homebrew")
     ((and (darwin?) (file-exists? "/usr/local/Homebrew")) "/usr/local")
     ((and (linux?) (file-exists? "/home/linuxbrew/.linuxbrew")) "/home/linuxbrew/.linuxbrew")
     (else #f)))

  (define (lib-path)
    (let ((brew (homebrew-prefix)))
      (cond
       (brew (string-append brew "/lib"))
       ((linux?) "/usr/lib64")
       (else "/usr/local/lib"))))

  (define (include-path)
    (let ((brew (homebrew-prefix)))
      (cond
       (brew (string-append brew "/include"))
       ((linux?) "/usr/include")
       (else "/usr/local/include"))))

  ;; ============================================================
  ;; Feature Detection
  ;; ============================================================

  (define (has-libsodium?)
    (or (file-exists? (string-append (lib-path) "/libsodium.dylib"))
        (file-exists? (string-append (lib-path) "/libsodium.so"))
        (file-exists? "/usr/lib/libsodium.so")
        (file-exists? "/usr/lib/x86_64-linux-gnu/libsodium.so")))

  (define (has-codesign?)
    (and (darwin?) (shell-success? "which codesign")))

  (define (has-notarytool?)
    (and (darwin?) (shell-success? "which notarytool")))

  (define (has-homebrew?)
    (not (not (homebrew-prefix))))

  ;; ============================================================
  ;; System Utilities (Platform-Abstracted)
  ;; ============================================================

  (define (in-cyberspace-app?)
    (and (getenv "CYBERSPACE_APP") #t))

  ;; Simplified system openers -- these just call system
  (define (open-keychain)
    (cond
     ((darwin?) (system "open -g -a 'Keychain Access'") 'keychain-access)
     (else #f)))

  (define (open-tickets)
    (cond
     ((darwin?) (system "open -g -a 'Ticket Viewer'") 'ticket-viewer)
     (else #f)))

  (define (open-console)
    (cond
     ((darwin?) (system "open -g -a 'Console'") 'console)
     (else #f)))

  (define (open-monitor)
    (cond
     ((darwin?) (system "open -g -a 'Activity Monitor'") 'activity-monitor)
     (else #f)))

  (define (open-finder)
    (cond
     ((darwin?) (system "open -g .") 'finder)
     (else #f)))

  ;; ============================================================
  ;; Session Statistics
  ;; ============================================================

  (define *session-stats* (make-hash-table))

  (define (session-stat! key . rest)
    (let ((delta (if (null? rest) 1 (car rest))))
      (hash-table-set! *session-stats* key
                       (+ delta (hash-table-ref/default *session-stats* key 0)))))

  (define (session-stat key)
    (hash-table-ref/default *session-stats* key 0))

  (define (session-stats)
    (let ((pairs (hash-table->alist *session-stats*)))
      (list-sort (lambda (a b)
                   (string<? (symbol->string (car a))
                             (symbol->string (car b))))
                 pairs)))

  (define (session-stats-reset!)
    (set! *session-stats* (make-hash-table)))

  ;; ============================================================
  ;; Cleanup Hooks
  ;; ============================================================

  (define *cleanup-hooks* (make-hash-table))

  (define (register-cleanup-hook! name thunk)
    (hash-table-set! *cleanup-hooks* name thunk))

  (define (run-cleanup-hooks!)
    (for-each
     (lambda (name)
       (guard (exn [#t (void)])
         ((hash-table-ref *cleanup-hooks* name))))
     (hash-table-keys *cleanup-hooks*)))

  (define (cleanup-hooks-status)
    (hash-table-keys *cleanup-hooks*))

  ;; ============================================================
  ;; Box Drawing
  ;; ============================================================

  (define *box-square*  '("\x250C;" "\x2500;" "\x2510;" "\x2502;" "\x2514;" "\x2518;" "\x251C;" "\x2524;"))
  (define *box-rounded* '("\x256D;" "\x2500;" "\x256E;" "\x2502;" "\x2570;" "\x256F;" "\x251C;" "\x2524;"))
  (define *box-double*  '("\x2554;" "\x2550;" "\x2557;" "\x2551;" "\x255A;" "\x255D;" "\x2560;" "\x2563;"))

  (define (string-pad-left str len . rest)
    (let ((ch (if (null? rest) #\space (car rest))))
      (if (>= (string-length str) len)
          str
          (string-append (make-string (- len (string-length str)) ch) str))))

  (define (string-truncate str max-len . rest)
    (let ((ellipsis (if (null? rest) "..." (car rest))))
      (if (<= (string-length str) max-len)
          str
          (string-append (substring str 0 (- max-len (string-length ellipsis))) ellipsis))))

  (define (string-display-width str)
    "Approximate display width (byte length for ASCII, rough for Unicode)."
    (string-length str))

  (define (string-repeat str n)
    (let loop ((i n) (acc ""))
      (if (<= i 0) acc (loop (- i 1) (string-append acc str)))))

  (define (make-box width . rest)
    (let ((style (if (null? rest) *box-square* (car rest))))
      `((width . ,width) (style . ,style))))

  (define (box-width builder) (cdr (assq 'width builder)))
  (define (box-style builder) (cdr (assq 'style builder)))

  (define (box-tl s) (list-ref s 0))
  (define (box-h s)  (list-ref s 1))
  (define (box-tr s) (list-ref s 2))
  (define (box-v s)  (list-ref s 3))
  (define (box-bl s) (list-ref s 4))
  (define (box-br s) (list-ref s 5))
  (define (box-tee-l s) (list-ref s 6))
  (define (box-tee-r s) (list-ref s 7))

  (define (box-top builder . rest)
    (let* ((title (if (null? rest) #f (car rest)))
           (w (box-width builder))
           (s (box-style builder))
           (h (box-h s)))
      (if title
          (let* ((t (string-append " " title " "))
                 (tlen (string-length t))
                 (right-pad (- w 1 tlen)))
            (string-append
              (box-tl s) (string-repeat h 1) t
              (string-repeat h (max 0 right-pad)) (box-tr s)))
          (string-append (box-tl s) (string-repeat h w) (box-tr s)))))

  (define (box-bottom builder)
    (let ((w (box-width builder))
          (s (box-style builder)))
      (string-append (box-bl s) (string-repeat (box-h s) w) (box-br s))))

  (define (box-separator builder)
    (let ((w (box-width builder))
          (s (box-style builder)))
      (string-append (box-tee-l s) (string-repeat (box-h s) w) (box-tee-r s))))

  (define (box-line builder content)
    (let* ((w (box-width builder))
           (s (box-style builder))
           (inner-w (- w 2))
           (truncated (string-truncate content inner-w))
           (pad (max 0 (- inner-w (string-length truncated)))))
      (string-append
        (box-v s) " " truncated (make-string pad #\space) " " (box-v s))))

  (define (box-print builder content)
    (display (box-line builder content))
    (newline))

) ;; end library
