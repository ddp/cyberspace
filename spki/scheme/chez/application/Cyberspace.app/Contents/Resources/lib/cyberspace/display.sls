;;; display.sls - Terminal and browser display modes
;;; Library of Cyberspace - Chez Port
;;;
;;; The operator lives between two worlds: the phosphor glow of VT100
;;; and the warmth of a reading lamp in the browser.
;;;
;;; Heritage: Memo-054 Terminal Interface Conventions
;;;
;;; Ported from Chicken's display.scm.
;;; Changes: module -> library, #!key -> get-key, (chicken process) -> system,
;;;          string-split/string-prefix? inlined.

(library (cyberspace display)
  (export
    ;; Display mode
    display-mode
    display-mode!

    ;; Themes
    current-theme
    theme!
    theme-color

    ;; VT100 codes
    vt100-bold
    vt100-dim
    vt100-normal
    vt100-reverse
    vt100-red
    vt100-green
    vt100-yellow
    vt100-blue
    vt100-cyan
    vt100-magenta
    vt100-clear
    vt100-clear-line
    vt100-home
    vt100-save-cursor
    vt100-restore-cursor

    ;; Terminal operations
    set-terminal-title!
    terminal-width
    terminal-height
    clear

    ;; Browser opening
    open-in-browser
    render-html

    ;; Sparklines
    sparkline)

  (import (rnrs)
          (only (chezscheme)
                printf format system void
                current-time time-second
                getenv)
          (cyberspace chicken-compatibility chicken))

  ;; ============================================================
  ;; Helpers
  ;; ============================================================

  (define (string-prefix? prefix str)
    (and (>= (string-length str) (string-length prefix))
         (string=? (substring str 0 (string-length prefix)) prefix)))

  (define (string-suffix? suffix str)
    (and (>= (string-length str) (string-length suffix))
         (string=? (substring str (- (string-length str) (string-length suffix))
                              (string-length str))
                   suffix)))

  (define (current-seconds)
    (time-second (current-time)))

  ;; ============================================================
  ;; Display Mode
  ;; ============================================================
  ;; 'vt100 for terminal, 'html for browser views

  (define *display-mode* 'vt100)

  (define (display-mode) *display-mode*)

  (define (display-mode! mode)
    ;; Set display mode: 'vt100 or 'html
    (unless (memq mode '(vt100 html))
      (error 'display-mode! "Invalid display mode" mode))
    (set! *display-mode* mode))

  ;; ============================================================
  ;; Themes
  ;; ============================================================
  ;; phosphor - classic green-on-black terminal
  ;; reading-lamp - warm sepia tones for browser

  (define *themes*
    '((phosphor
       (fg . "#33ff33")
       (bg . "#0a0a0a")
       (dim . "#1a8f1a")
       (accent . "#66ff66")
       (error . "#ff3333")
       (warn . "#ffff33"))
      (reading-lamp
       (fg . "#3d3929")
       (bg . "#f4ecd8")
       (dim . "#8b8378")
       (accent . "#5c4033")
       (error . "#8b0000")
       (warn . "#b8860b"))
      (midnight
       (fg . "#c0c0c0")
       (bg . "#1a1a2e")
       (dim . "#4a4a6a")
       (accent . "#00d4ff")
       (error . "#ff4444")
       (warn . "#ffa500"))))

  (define *theme* 'phosphor)

  (define (current-theme) *theme*)

  (define (theme! name)
    ;; Set theme: 'phosphor, 'reading-lamp, or 'midnight
    (unless (assq name *themes*)
      (error 'theme! "Unknown theme" name))
    (set! *theme* name)
    (print "[theme: " name "]"))

  (define (theme-color key)
    ;; Get color for key from current theme
    (let ((theme (assq *theme* *themes*)))
      (if theme
          (let ((color (assq key (cdr theme))))
            (if color (cdr color) "#ffffff"))
          "#ffffff")))

  ;; ============================================================
  ;; VT100 Escape Codes
  ;; ============================================================
  ;; ECMA-48 / ANSI X3.64 control sequences

  (define vt100-bold "\x1b;[1m")
  (define vt100-dim "\x1b;[2m")
  (define vt100-normal "\x1b;[0m")
  (define vt100-reverse "\x1b;[7m")
  (define vt100-red "\x1b;[31m")
  (define vt100-green "\x1b;[32m")
  (define vt100-yellow "\x1b;[33m")
  (define vt100-blue "\x1b;[34m")
  (define vt100-magenta "\x1b;[35m")
  (define vt100-cyan "\x1b;[36m")
  (define vt100-clear "\x1b;[2J")
  (define vt100-clear-line "\x1b;[2K\r")
  (define vt100-home "\x1b;[H")
  (define vt100-save-cursor "\x1b;[s")
  (define vt100-restore-cursor "\x1b;[u")

  ;; ============================================================
  ;; Terminal Operations
  ;; ============================================================

  (define (set-terminal-title! title)
    ;; Set terminal window title (xterm/vt100)
    (display (string-append "\x1b;]0;" title "\x7;"))
    (flush-output-port (current-output-port)))

  (define (terminal-width)
    ;; Get terminal width, default 80
    (guard (exn [#t 80])
      (let ((result (with-input-from-pipe "tput cols" read-line)))
        (if result (or (string->number result) 80) 80))))

  (define (terminal-height)
    ;; Get terminal height, default 24
    (guard (exn [#t 24])
      (let ((result (with-input-from-pipe "tput lines" read-line)))
        (if result (or (string->number result) 24) 24))))

  (define (with-input-from-pipe cmd proc)
    ;; Run cmd, read from its stdout
    (guard (exn [#t #f])
      (let* ((tmpfile (string-append "/tmp/cyberspace-pipe-"
                                      (number->string (current-seconds))))
             (exit-code (system (string-append cmd " > " tmpfile " 2>/dev/null"))))
        (if (= exit-code 0)
            (let ((result (guard (exn2 [#t #f])
                            (with-input-from-file tmpfile
                              (lambda ()
                                (proc (current-input-port)))))))
              (guard (exn3 [#t #f]) (delete-file tmpfile))
              result)
            (begin
              (guard (exn3 [#t #f]) (delete-file tmpfile))
              #f)))))

  (define (read-line port)
    ;; Read one line from port
    (let loop ((chars '()))
      (let ((c (read-char port)))
        (cond
          ((eof-object? c)
           (if (null? chars) #f (list->string (reverse chars))))
          ((char=? c #\newline)
           (list->string (reverse chars)))
          ((char=? c #\return)
           (loop chars))  ; skip CR
          (else
           (loop (cons c chars)))))))

  (define (clear)
    ;; Clear screen and home cursor
    (display vt100-clear)
    (display vt100-home)
    (flush-output-port (current-output-port))
    (void))

  ;; ============================================================
  ;; Sparklines
  ;; ============================================================
  ;; Eight ASCII levels for activity visualization

  (define *sparkline-chars* '#(" " "." "_" "," "-" "~" "=" "+" "#"))

  (define (sparkline values)
    ;; Render values (0.0-1.0) as ASCII sparkline
    (let ((chars (map (lambda (v)
                        (let ((idx (min 8 (max 0 (exact (floor (* v 9)))))))
                          (vector-ref *sparkline-chars* idx)))
                      values)))
      (apply string-append chars)))

  ;; ============================================================
  ;; HTML Rendering
  ;; ============================================================

  (define (render-html title body)
    ;; Render HTML page with current theme
    (let ((fg (theme-color 'fg))
          (bg (theme-color 'bg))
          (dim (theme-color 'dim))
          (accent (theme-color 'accent)))
      (string-append
       "<!DOCTYPE html>\n"
       "<html>\n"
       "<head>\n"
       "  <meta charset=\"utf-8\">\n"
       "  <title>" title "</title>\n"
       "  <style>\n"
       "    body {\n"
       "      font-family: 'Berkeley Mono', 'JetBrains Mono', 'Fira Code', monospace;\n"
       "      background: " bg ";\n"
       "      color: " fg ";\n"
       "      padding: 2em;\n"
       "      line-height: 1.6;\n"
       "    }\n"
       "    h1, h2, h3 { color: " accent "; }\n"
       "    .dim { color: " dim "; }\n"
       "    pre {\n"
       "      background: " (if (eq? *theme* 'phosphor) "#0f0f0f" "#efe6d0") ";\n"
       "      padding: 1em;\n"
       "      border-radius: 4px;\n"
       "      overflow-x: auto;\n"
       "    }\n"
       "    a { color: " accent "; }\n"
       "  </style>\n"
       "</head>\n"
       "<body>\n"
       body
       "</body>\n"
       "</html>\n")))

  ;; ============================================================
  ;; Browser Opening
  ;; ============================================================

  (define (open-in-browser content . opts)
    ;; Open HTML content in default browser
    (let* ((title (get-key opts 'title: "Cyberspace"))
           (tmpdir (or (getenv "TMPDIR") "/tmp"))
           (tmpfile (string-append tmpdir "/cyberspace-"
                                   (number->string (current-seconds))
                                   ".html")))
      ;; Write HTML to temp file
      (with-output-to-file tmpfile
        (lambda ()
          (display (if (string-prefix? "<!DOCTYPE" content)
                       content
                       (render-html title (string-append "<pre>" content "</pre>"))))))
      ;; Open in browser (macOS/Linux)
      (let ((cmd (cond
                   ((file-exists? "/usr/bin/open")
                    (string-append "open " tmpfile))
                   ((file-exists? "/usr/bin/xdg-open")
                    (string-append "xdg-open " tmpfile))
                   (else #f))))
        (if cmd
            (begin
              (system cmd)
              (print "[opened: " tmpfile "]"))
            (print "[browser not found, saved: " tmpfile "]")))
      tmpfile))

) ;; end library
