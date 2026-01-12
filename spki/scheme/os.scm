;;; os.scm - Operating System Introspection
;;;
;;; Level 0 module: no cyberspace dependencies.
;;; Foundation for platform-portable code.
;;;
;;; "Know thyself" - Delphi
;;; "uname -a" - Unix

(module os
  (;; Core identity
   os-type            ; 'darwin, 'linux, 'freebsd, 'unknown
   os-name            ; "Darwin", "Linux", etc.
   os-version         ; kernel version string
   os-arch            ; 'arm64, 'x86-64, 'unknown
   os-arch-name       ; "arm64", "x86_64", etc.
   os-platform        ; combined: "Darwin-arm64"

   ;; Predicates
   darwin?
   linux?
   freebsd?
   arm64?
   x86-64?
   apple-silicon?

   ;; Hardware
   cpu-brand
   cpu-cores
   memory-gb
   hostname

   ;; Paths (platform-appropriate)
   homebrew-prefix    ; /opt/homebrew or /usr/local or #f
   lib-path           ; library search path
   include-path       ; header search path

   ;; Feature detection
   has-libsodium?
   has-codesign?
   has-notarytool?
   has-homebrew?

   ;; Shell utilities
   shell-command
   shell-lines
   shell-success?

   ;; Session statistics (primitives for cross-module instrumentation)
   *session-stats*
   session-stat!
   session-stat)

  (import scheme
          (chicken base)
          (chicken io)
          (chicken file)
          (chicken format)
          (chicken string)
          (chicken process)
          (chicken condition)
          srfi-1
          srfi-13
          srfi-69)

  ;; ============================================================
  ;; Shell Utilities
  ;; ============================================================

  (define (shell-command cmd)
    "Run shell command, return trimmed output or #f"
    (handle-exceptions exn #f
      (let ((result (with-input-from-pipe cmd read-line)))
        (if (eof-object? result) #f result))))

  (define (shell-lines cmd)
    "Run shell command, return list of lines"
    (handle-exceptions exn '()
      (with-input-from-pipe cmd
        (lambda ()
          (let loop ((lines '()))
            (let ((line (read-line)))
              (if (eof-object? line)
                  (reverse lines)
                  (loop (cons line lines)))))))))

  (define (shell-success? cmd)
    "Return #t if command exits successfully"
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
    "Return OS as symbol: 'darwin, 'linux, 'freebsd, 'unknown"
    (cond
     ((string=? *os-name* "Darwin") 'darwin)
     ((string=? *os-name* "Linux") 'linux)
     ((string=? *os-name* "FreeBSD") 'freebsd)
     (else 'unknown)))

  (define (os-arch)
    "Return architecture as symbol: 'arm64, 'x86-64, 'unknown"
    (cond
     ((string=? *os-arch-name* "arm64") 'arm64)
     ((string=? *os-arch-name* "aarch64") 'arm64)
     ((string=? *os-arch-name* "x86_64") 'x86-64)
     ((string=? *os-arch-name* "amd64") 'x86-64)
     (else 'unknown)))

  (define (os-platform)
    "Return combined platform string: 'Darwin-arm64'"
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
    (or (shell-command "hostname -s") "localhost"))

  (define (cpu-brand)
    "Return CPU brand string"
    (cond
     ((darwin?)
      (shell-command "sysctl -n machdep.cpu.brand_string"))
     ((linux?)
      (shell-command "grep -m1 'model name' /proc/cpuinfo | cut -d: -f2 | xargs"))
     (else #f)))

  (define (cpu-cores)
    "Return number of CPU cores"
    (cond
     ((darwin?)
      (let ((n (shell-command "sysctl -n hw.ncpu")))
        (and n (string->number n))))
     ((linux?)
      (let ((n (shell-command "nproc")))
        (and n (string->number n))))
     (else #f)))

  (define (memory-gb)
    "Return system memory in gigabytes"
    (cond
     ((darwin?)
      (let ((bytes (shell-command "sysctl -n hw.memsize")))
        (and bytes
             (inexact->exact (round (/ (string->number bytes) 1073741824))))))
     ((linux?)
      (let ((kb (shell-command "grep MemTotal /proc/meminfo | awk '{print $2}'")))
        (and kb
             (inexact->exact (round (/ (string->number kb) 1048576))))))
     (else #f)))

  ;; ============================================================
  ;; Platform Paths
  ;; ============================================================

  (define (homebrew-prefix)
    "Return Homebrew prefix or #f if not installed"
    (cond
     ((and (darwin?) (arm64?) (file-exists? "/opt/homebrew"))
      "/opt/homebrew")
     ((and (darwin?) (file-exists? "/usr/local/Homebrew"))
      "/usr/local")
     ((and (linux?) (file-exists? "/home/linuxbrew/.linuxbrew"))
      "/home/linuxbrew/.linuxbrew")
     (else #f)))

  (define (lib-path)
    "Return appropriate library path for platform"
    (let ((brew (homebrew-prefix)))
      (cond
       (brew (string-append brew "/lib"))
       ((linux?) "/usr/lib64")  ; Fedora convention
       (else "/usr/local/lib"))))

  (define (include-path)
    "Return appropriate include path for platform"
    (let ((brew (homebrew-prefix)))
      (cond
       (brew (string-append brew "/include"))
       ((linux?) "/usr/include")
       (else "/usr/local/include"))))

  ;; ============================================================
  ;; Feature Detection
  ;; ============================================================

  (define (has-libsodium?)
    "Check if libsodium is available"
    (or (file-exists? (string-append (lib-path) "/libsodium.dylib"))
        (file-exists? (string-append (lib-path) "/libsodium.so"))
        (file-exists? "/usr/lib/libsodium.so")
        (file-exists? "/usr/lib/x86_64-linux-gnu/libsodium.so")))

  (define (has-codesign?)
    "Check if codesign is available (macOS only)"
    (and (darwin?)
         (shell-success? "which codesign")))

  (define (has-notarytool?)
    "Check if notarytool is available (macOS only)"
    (and (darwin?)
         (shell-success? "which notarytool")))

  (define (has-homebrew?)
    "Check if Homebrew is installed"
    (not (not (homebrew-prefix))))

  ;; ============================================================
  ;; Session Statistics
  ;; ============================================================
  ;;
  ;; Lightweight counters for session activity tracking.
  ;; Lives at level 0 so all modules can instrument themselves.
  ;; Initialization is done by portal's session-stat-init!.

  (define *session-stats*
    (make-hash-table))

  (define (session-stat! key #!optional (delta 1))
    "Increment a session statistic."
    (hash-table-set! *session-stats* key
                     (+ delta (hash-table-ref/default *session-stats* key 0))))

  (define (session-stat key)
    "Get a session statistic."
    (hash-table-ref/default *session-stats* key 0))

) ; end module os
