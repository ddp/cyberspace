;;; display.scm - Terminal and browser display modes
;;;
;;; The operator lives between two worlds: the phosphor glow of VT100
;;; and the warmth of a reading lamp in the browser.
;;;
;;; Heritage: Memo-054 Terminal Interface Conventions
;;;

(module display
  (;; Display mode
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

   ;; Box drawing
   make-box
   box-header
   box-footer
   box-line

   ;; Browser opening
   open-in-browser
   render-html

   ;; Sparklines
   sparkline)

  (import scheme
          (chicken base)
          (chicken format)
          (chicken port)
          (chicken process)
          (chicken file)
          (chicken pathname)
          (chicken string)
          (chicken io)
          (chicken time)
          (chicken condition)
          (chicken process-context)
          srfi-1
          srfi-13)

  ;;; ============================================================
  ;;; Display Mode
  ;;; ============================================================
  ;;; 'vt100 for terminal, 'html for browser views

  (define *display-mode* 'vt100)

  (define (display-mode! mode)
    "Set display mode: 'vt100 or 'html"
    (unless (memq mode '(vt100 html))
      (error "Invalid display mode" mode))
    (set! *display-mode* mode))

  ;;; ============================================================
  ;;; Themes
  ;;; ============================================================
  ;;; phosphor - classic green-on-black terminal
  ;;; reading-lamp - warm sepia tones for browser

  (define *themes*
    '((phosphor
       (fg . "#33ff33")      ; bright green
       (bg . "#0a0a0a")      ; near black
       (dim . "#1a8f1a")     ; dim green
       (accent . "#66ff66")  ; highlight green
       (error . "#ff3333")   ; red
       (warn . "#ffff33"))   ; yellow
      (reading-lamp
       (fg . "#3d3929")      ; dark sepia
       (bg . "#f4ecd8")      ; cream
       (dim . "#8b8378")     ; muted brown
       (accent . "#5c4033")  ; chocolate
       (error . "#8b0000")   ; dark red
       (warn . "#b8860b"))   ; dark goldenrod
      (midnight
       (fg . "#c0c0c0")      ; silver
       (bg . "#1a1a2e")      ; midnight blue
       (dim . "#4a4a6a")     ; muted blue
       (accent . "#00d4ff")  ; cyan
       (error . "#ff4444")   ; bright red
       (warn . "#ffa500")))) ; orange

  (define *theme* 'phosphor)

  (define (theme! name)
    "Set theme: 'phosphor, 'reading-lamp, or 'midnight"
    (unless (assq name *themes*)
      (error "Unknown theme" name))
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
  ;;; ECMA-48 / ANSI X3.64 control sequences

  (define vt100-bold "\x1b[1m")
  (define vt100-dim "\x1b[2m")
  (define vt100-normal "\x1b[0m")
  (define vt100-reverse "\x1b[7m")
  (define vt100-red "\x1b[31m")
  (define vt100-green "\x1b[32m")
  (define vt100-yellow "\x1b[33m")
  (define vt100-blue "\x1b[34m")
  (define vt100-magenta "\x1b[35m")
  (define vt100-cyan "\x1b[36m")
  (define vt100-clear "\x1b[2J")
  (define vt100-clear-line "\x1b[2K\r")
  (define vt100-home "\x1b[H")
  (define vt100-save-cursor "\x1b[s")
  (define vt100-restore-cursor "\x1b[u")

  ;;; ============================================================
  ;;; Terminal Operations
  ;;; ============================================================

  (define (set-terminal-title! title)
    "Set terminal window title (xterm/vt100)"
    (display (string-append "\x1b]0;" title "\x07"))
    (flush-output))

  (define (terminal-width)
    "Get terminal width, default 80"
    (handle-exceptions exn 80
      (let ((w (with-input-from-pipe "tput cols" read-line)))
        (if (eof-object? w) 80 (or (string->number w) 80)))))

  (define (terminal-height)
    "Get terminal height, default 24"
    (handle-exceptions exn 24
      (let ((h (with-input-from-pipe "tput lines" read-line)))
        (if (eof-object? h) 24 (or (string->number h) 24)))))

  (define (clear)
    "Clear screen and home cursor"
    (display vt100-clear)
    (display vt100-home)
    (flush-output)
    (void))

  ;;; ============================================================
  ;;; Box Drawing (ASCII for portability)
  ;;; ============================================================
  ;;; Memo-054 style boxes

  (define (make-box title width)
    "Create a box drawing closure"
    (let* ((title-padded (if (string-null? title) "" (string-append " " title " ")))
           (title-len (string-length title-padded))
           (content-width (- width 2))  ; account for | borders
           (left-pad (quotient (- width title-len 2) 2))
           (right-pad (- width title-len 2 left-pad)))
      (lambda (cmd . args)
        (case cmd
          ((header)
           (string-append "+" (make-string left-pad #\-)
                          title-padded
                          (make-string right-pad #\-) "+\n"))
          ((footer)
           (string-append "+" (make-string (- width 2) #\-) "+\n"))
          ((line)
           (let* ((content (if (null? args) "" (car args)))
                  (pad (- content-width (string-length content))))
             (string-append "| " content
                            (make-string (max 0 pad) #\space) "|\n")))
          ((blank)
           (string-append "|" (make-string (- width 2) #\space) "|\n"))))))

  (define (box-header title width)
    "Draw box header"
    ((make-box title width) 'header))

  (define (box-footer width)
    "Draw box footer"
    ((make-box "" width) 'footer))

  (define (box-line content width)
    "Draw box content line"
    ((make-box "" width) 'line content))

  ;;; ============================================================
  ;;; Sparklines
  ;;; ============================================================
  ;;; Eight ASCII levels for activity visualization

  (define *sparkline-chars* '#(" " "." "_" "," "-" "~" "=" "+" "#"))

  (define (sparkline values)
    "Render values (0.0-1.0) as ASCII sparkline"
    (let ((chars (map (lambda (v)
                        (let ((idx (min 8 (max 0 (inexact->exact (floor (* v 9)))))))
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

  (define (open-in-browser content #!key (title "Cyberspace"))
    "Open HTML content in default browser"
    (let* ((tmpdir (or (get-environment-variable "TMPDIR") "/tmp"))
           (tmpfile (make-pathname tmpdir
                                   (string-append "cyberspace-"
                                                  (number->string (current-seconds))
                                                  ".html"))))
      ;; Write HTML to temp file
      (with-output-to-file tmpfile
        (lambda ()
          (display (if (string-prefix? "<!DOCTYPE" content)
                       content
                       (render-html title (string-append "<pre>" content "</pre>"))))))
      ;; Open in browser (macOS/Linux)
      (let ((cmd (cond
                  ((file-exists? "/usr/bin/open") ; macOS
                   (string-append "open " tmpfile))
                  ((file-exists? "/usr/bin/xdg-open") ; Linux
                   (string-append "xdg-open " tmpfile))
                  (else #f))))
        (if cmd
            (begin
              (system cmd)
              (print "[opened: " tmpfile "]"))
            (print "[browser not found, saved: " tmpfile "]")))
      tmpfile))

) ; end module
