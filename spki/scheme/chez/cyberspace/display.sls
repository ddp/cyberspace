;;; display.sls - Terminal and Browser Display Modes (Chez Port)
;;; Library of Cyberspace
;;;
;;; The operator lives between two worlds: the phosphor glow of VT100
;;; and the warmth of a reading lamp in the browser.
;;;
;;; Heritage: Memo-054 Terminal Interface Conventions
;;;
;;; Ported from display.scm.
;;; Copyright (c) 2026 Yoyodyne. See LICENSE.

(library (cyberspace display)
  (export
    ;; Display mode
    *display-mode*
    display-mode!

    ;; Themes
    *theme*
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

  (import (except (rnrs) file-exists? with-output-to-file flush-output-port find)
          (only (chezscheme)
                printf format void system
                file-exists? with-output-to-file
                flush-output-port
                open-process-ports native-transcoder
                getenv
                with-output-to-string)
          (cyberspace chicken-compatibility chicken))

  ;;; ============================================================
  ;;; Display Mode
  ;;; ============================================================

  (define *display-mode-box* (vector 'vt100))
  (define-syntax *display-mode*
    (identifier-syntax
      [id (vector-ref *display-mode-box* 0)]
      [(set! id val) (vector-set! *display-mode-box* 0 val)]))

  (define (display-mode! mode)
    "Set display mode: 'vt100 or 'html"
    (unless (memq mode '(vt100 html))
      (error 'display-mode! "Invalid display mode" mode))
    (set! *display-mode* mode))

  ;;; ============================================================
  ;;; Themes
  ;;; ============================================================

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

  (define *theme-box* (vector 'phosphor))
  (define-syntax *theme*
    (identifier-syntax
      [id (vector-ref *theme-box* 0)]
      [(set! id val) (vector-set! *theme-box* 0 val)]))

  (define (theme! name)
    "Set theme: 'phosphor, 'reading-lamp, or 'midnight"
    (unless (assq name *themes*)
      (error 'theme! "Unknown theme" name))
    (set! *theme* name)
    (print "[theme: " name "]"))

  (define (theme-color key)
    "Get color for key from current theme"
    (let ((theme (assq *theme* *themes*)))
      (if theme
          (let ((color (assq key (cdr theme))))
            (if color (cdr color) "#ffffff"))
          "#ffffff")))

  ;;; ============================================================
  ;;; VT100 Escape Codes
  ;;; ============================================================

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

  ;;; ============================================================
  ;;; Terminal Operations
  ;;; ============================================================

  (define (shell-cmd cmd)
    "Run shell command, return trimmed output or #f."
    (guard (exn [#t #f])
      (let-values (((to-stdin from-stdout from-stderr)
                    (open-process-ports cmd 'line (native-transcoder))))
        (let ((result (get-line from-stdout)))
          (close-port to-stdin)
          (close-port from-stdout)
          (close-port from-stderr)
          (if (eof-object? result) #f result)))))

  (define (set-terminal-title! title)
    "Set terminal window title (xterm/vt100)"
    (display (string-append "\x1b;]0;" title "\x7;"))
    (flush-output-port (current-output-port)))

  (define (terminal-width)
    "Get terminal width, default 80"
    (guard (exn [#t 80])
      (let ((w (shell-cmd "tput cols")))
        (if w (or (string->number w) 80) 80))))

  (define (terminal-height)
    "Get terminal height, default 24"
    (guard (exn [#t 24])
      (let ((h (shell-cmd "tput lines")))
        (if h (or (string->number h) 24) 24))))

  (define (clear)
    "Clear screen and home cursor"
    (display vt100-clear)
    (display vt100-home)
    (flush-output-port (current-output-port))
    (void))

  ;;; ============================================================
  ;;; Sparklines
  ;;; ============================================================

  (define *sparkline-chars* '#(" " "." "_" "," "-" "~" "=" "+" "#"))

  (define (sparkline values)
    "Render values (0.0-1.0) as ASCII sparkline"
    (let ((chars (map (lambda (v)
                        (let ((idx (min 8 (max 0 (exact (floor (* v 9)))))))
                          (vector-ref *sparkline-chars* idx)))
                      values)))
      (apply string-append chars)))

  ;;; ============================================================
  ;;; HTML Rendering
  ;;; ============================================================

  (define (render-html title body)
    "Render HTML page with current theme"
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

  ;;; ============================================================
  ;;; Browser Opening
  ;;; ============================================================

  (define (open-in-browser content . rest)
    "Open HTML content in default browser.
     Optional keyword: title: \"string\""
    (let* ((title (get-key rest 'title: "Cyberspace"))
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
      ;; Open in browser
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
