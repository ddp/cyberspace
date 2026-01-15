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

   ;; System utilities (platform-abstracted)
   open-keychain          ; open keychain/credential manager
   open-tickets           ; open Kerberos ticket viewer
   open-console           ; open system log viewer
   open-monitor           ; open process/activity monitor
   open-finder            ; reveal working directory

   ;; Shell utilities
   shell-command
   shell-lines
   shell-success?

   ;; Session statistics (primitives for cross-module instrumentation)
   *session-stats*
   session-stat!
   session-stat

   ;; Box drawing (centralized terminal formatting)
   make-box              ; create a box builder for given width/style
   box-top               ; (box-top builder #!optional title)
   box-bottom            ; (box-bottom builder)
   box-separator         ; (box-separator builder)
   box-line              ; (box-line builder content)
   box-print             ; (box-print builder content) - prints immediately
   box-width             ; (box-width builder) - get inner width
   *box-square*          ; ┌─┐│└┘├┤
   *box-rounded*         ; ╭─╮│╰╯├┤
   *box-double*          ; ╔═╗║╚╝╠╣
   string-pad-left       ; alias for srfi-13 string-pad
   string-truncate
   string-display-width)

  (import scheme
          (chicken base)
          (chicken io)
          (chicken file)
          (chicken format)
          (chicken string)
          (chicken process)
          (chicken process-context)
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
  ;; System Utilities (Platform-Abstracted)
  ;; ============================================================

  (define (in-cyberspace-app?)
    "True if running inside Cyberspace.app"
    (get-environment-variable "CYBERSPACE_APP"))

  (define (open-keychain)
    "Open the system keychain/credential manager.
     macOS: Keychain Access.app (background unless in app)
     Linux: seahorse (GNOME Keyring GUI) or secret-tool"
    (cond
     ((darwin?)
      (if (in-cyberspace-app?)
          (system "open -a 'Keychain Access'")
          (system "open -g -a 'Keychain Access'"))
      'keychain-access)
     ((linux?)
      (cond
       ((shell-success? "which seahorse")
        (system "seahorse &")
        'seahorse)
       ((shell-success? "which gnome-keyring")
        (system "gnome-keyring &")
        'gnome-keyring)
       (else
        (print "No keychain GUI found. Try: secret-tool or seahorse")
        #f)))
     (else
      (print "Keychain access not supported on this platform")
      #f)))

  (define (open-tickets)
    "Open the Kerberos ticket viewer.
     macOS: Ticket Viewer.app (background unless in app)
     Linux: klist (command-line) or krb5-auth-dialog"
    (cond
     ((darwin?)
      (if (in-cyberspace-app?)
          (system "open -a 'Ticket Viewer'")
          (system "open -g -a 'Ticket Viewer'"))
      'ticket-viewer)
     ((linux?)
      (cond
       ((shell-success? "which krb5-auth-dialog")
        (system "krb5-auth-dialog &")
        'krb5-auth-dialog)
       ((shell-success? "which klist")
        ;; No GUI, show tickets in terminal
        (print "=== Kerberos Tickets ===")
        (system "klist")
        'klist)
       (else
        (print "No Kerberos tools found. Try: krb5-user")
        #f)))
     (else
      (print "Ticket viewer not supported on this platform")
      #f)))

  (define (open-console)
    "Open system log viewer.
     macOS: Console.app
     Linux: gnome-logs or journalctl"
    (cond
     ((darwin?)
      (if (in-cyberspace-app?)
          (system "open -a 'Console'")
          (system "open -g -a 'Console'"))
      'console)
     ((linux?)
      (cond
       ((shell-success? "which gnome-logs")
        (system "gnome-logs &")
        'gnome-logs)
       ((shell-success? "which journalctl")
        (system "journalctl -f &")
        'journalctl)
       (else
        (print "No log viewer found. Try: gnome-logs")
        #f)))
     (else
      (print "Console not supported on this platform")
      #f)))

  (define (open-monitor)
    "Open process/activity monitor.
     macOS: Activity Monitor.app
     Linux: gnome-system-monitor or htop"
    (cond
     ((darwin?)
      (if (in-cyberspace-app?)
          (system "open -a 'Activity Monitor'")
          (system "open -g -a 'Activity Monitor'"))
      'activity-monitor)
     ((linux?)
      (cond
       ((shell-success? "which gnome-system-monitor")
        (system "gnome-system-monitor &")
        'gnome-system-monitor)
       ((shell-success? "which htop")
        (print "Opening htop in terminal...")
        (system "htop &")
        'htop)
       (else
        (print "No monitor found. Try: gnome-system-monitor or htop")
        #f)))
     (else
      (print "Monitor not supported on this platform")
      #f)))

  (define (open-finder)
    "Reveal current working directory in file manager.
     macOS: Finder
     Linux: nautilus, thunar, or xdg-open"
    (cond
     ((darwin?)
      (if (in-cyberspace-app?)
          (system "open .")
          (system "open -g ."))
      'finder)
     ((linux?)
      (cond
       ((shell-success? "which nautilus")
        (system "nautilus . &")
        'nautilus)
       ((shell-success? "which thunar")
        (system "thunar . &")
        'thunar)
       ((shell-success? "which xdg-open")
        (system "xdg-open . &")
        'xdg-open)
       (else
        (print "No file manager found")
        #f)))
     (else
      (print "File manager not supported on this platform")
      #f)))

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

  ;; ============================================================
  ;; Box Drawing
  ;; ============================================================
  ;;
  ;; Centralized terminal box drawing for consistent output.
  ;; Supports three styles: square, rounded, double.
  ;;
  ;; Usage:
  ;;   (let ((b (make-box 60)))
  ;;     (print (box-top b "Title"))
  ;;     (box-print b "Content line")
  ;;     (print (box-separator b))
  ;;     (box-print b "More content")
  ;;     (print (box-bottom b)))

  ;; Box character sets: (tl horiz tr vert bl br t-left t-right)
  (define *box-square*  '(#\┌ #\─ #\┐ #\│ #\└ #\┘ #\├ #\┤))
  (define *box-rounded* '(#\╭ #\─ #\╮ #\│ #\╰ #\╯ #\├ #\┤))
  (define *box-double*  '(#\╔ #\═ #\╗ #\║ #\╚ #\╝ #\╠ #\╣))

  ;; String utilities for box formatting
  ;; Note: srfi-13 provides string-pad (left) and string-pad-right
  ;; We provide string-pad-left as a clearer alias for string-pad

  (define (string-pad-left str len #!optional (char #\space))
    "Pad string on left to reach len. Alias for srfi-13 string-pad."
    (string-pad str len char))

  (define (string-truncate str max-len #!optional (ellipsis "..."))
    "Truncate string to max-len, adding ellipsis if needed."
    (if (<= (string-length str) max-len)
        str
        (string-append (substring str 0 (- max-len (string-length ellipsis))) ellipsis)))

  (define (string-display-width str)
    "Calculate display width of string, accounting for multi-byte Unicode.
     Common symbols like ✓ ✗ are 3 bytes but display as 1 character."
    (let ((len (string-length str)))
      ;; Subtract 2 for each known multi-byte single-width char
      (- len
         (if (string-contains str "✓") 2 0)
         (if (string-contains str "✗") 2 0)
         (if (string-contains str "→") 2 0)
         (if (string-contains str "←") 2 0)
         (if (string-contains str "↑") 2 0)
         (if (string-contains str "↓") 2 0))))

  ;; Box builder - alist with width and style
  (define (make-box width #!optional (style *box-square*))
    "Create a box builder for the given inner width and style."
    `((width . ,width) (style . ,style)))

  (define (box-width builder)
    "Get the inner width of a box."
    (cdr (assq 'width builder)))

  (define (box-style builder)
    "Get the style characters of a box."
    (cdr (assq 'style builder)))

  ;; Style accessors
  (define (box-tl s) (list-ref s 0))
  (define (box-h s)  (list-ref s 1))
  (define (box-tr s) (list-ref s 2))
  (define (box-v s)  (list-ref s 3))
  (define (box-bl s) (list-ref s 4))
  (define (box-br s) (list-ref s 5))
  (define (box-tee-l s) (list-ref s 6))
  (define (box-tee-r s) (list-ref s 7))

  (define (box-top builder #!optional title)
    "Generate top border, optionally with title."
    (let* ((w (box-width builder))
           (s (box-style builder))
           (h (box-h s)))
      (if title
          (let* ((t (string-append " " title " "))
                 (tlen (string-length t))
                 (left-pad 1)
                 (right-pad (- w left-pad tlen)))
            (string-append
              (string (box-tl s))
              (make-string left-pad h)
              t
              (make-string (max 0 right-pad) h)
              (string (box-tr s))))
          (string-append
            (string (box-tl s))
            (make-string w h)
            (string (box-tr s))))))

  (define (box-bottom builder)
    "Generate bottom border."
    (let ((w (box-width builder))
          (s (box-style builder)))
      (string-append
        (string (box-bl s))
        (make-string w (box-h s))
        (string (box-br s)))))

  (define (box-separator builder)
    "Generate horizontal separator."
    (let ((w (box-width builder))
          (s (box-style builder)))
      (string-append
        (string (box-tee-l s))
        (make-string w (box-h s))
        (string (box-tee-r s)))))

  (define (box-line builder content)
    "Generate content line with proper padding.
     Uses display-width for Unicode-aware padding."
    (let* ((w (box-width builder))
           (s (box-style builder))
           (inner-w (- w 2))  ; space for leading/trailing space
           (truncated (string-truncate content inner-w))
           (display-w (string-display-width truncated))
           (pad (max 0 (- inner-w display-w))))
      (string-append
        (string (box-v s))
        " "
        truncated
        (make-string pad #\space)
        " "
        (string (box-v s)))))

  (define (box-print builder content)
    "Print a content line (convenience wrapper)."
    (print (box-line builder content)))

) ; end module os
