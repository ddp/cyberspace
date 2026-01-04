;;; .emacs --- Personal init file -*- lexical-binding: t; -*-
;;; Commentary:
;;  Personal Emacs configuration for macOS Tahoe (NS build).

;;; Code:

;; --- Core identity ----------------------------------------------------

(defconst *host*
  (car (split-string (system-name) "\\."))
  "Short hostname for this machine (no domain).")

(defconst *os* system-type
  "Symbol identifying the OS (e.g., 'darwin, 'gnu/linux).")

(defvar my/identity-logged nil
  "Non-nil once host/OS/path have been logged in *Messages*.")

(unless my/identity-logged
  (setq my/identity-logged t)
  (message "*host*: %s" *host*)
  (message "*os*: %s" *os*)
  (message "*path*: %s" (getenv "PATH")))

;;;; ----ddp's .emacs ----

;; /ssh:servfail.adelman.com|ssh:ns1.adelman.com:/usr/local/etc/nsd/master

;;;; Debug configuration - set to t to enable tracing
(defvar ddp-debug-loading nil
  "Enable verbose loading and timing diagnostics.")

;;;; Load timing
(when ddp-debug-loading
  (defvar *emacs-load-start* (current-time)))

;;;; Modern load tracing  
(when ddp-debug-loading
  (advice-add 'load :before 
              (lambda (file &rest _)
                (message "Loading %s..." (locate-library file)))))

;;;; Modern require tracing
(when ddp-debug-loading
  (defvar ddp-require-depth 0)
  
  (advice-add 'require :around
              (lambda (orig-fun feature &optional filename noerror)
                (cond ((memq feature features)
                       (message "%sRequiring `%s' (already loaded)"
                               (make-string (* 2 ddp-require-depth) ?-)
                               feature))
                      (t
                       (message "%sRequiring `%s'"
                               (make-string (* 2 ddp-require-depth) ?-)
                               feature)
                       (let ((ddp-require-depth (1+ ddp-require-depth)))
                         (funcall orig-fun feature filename noerror))
                       (message "%sRequiring `%s'...done"
                               (make-string (* 2 ddp-require-depth) ?-)
                               feature))))))

(defun ddp-append-path (p)
  (setenv "PATH" (concat (getenv "PATH") ":" p))
  (defvar *path* (getenv "PATH")))

(defun ddp-prepend-path (p)
  (setenv "PATH" (concat p ":" (getenv "PATH")))
  (defvar *path* (getenv "PATH")))

;;;; make load-path use whole subtree under ~/src/.emacs.d root

(defvar *emacs-home* "~/src/.emacs.d")
(unless (file-exists-p *emacs-home*)
  (make-directory *emacs-home* t))

(if (fboundp 'normal-top-level-add-subdirs-to-load-path)
    (let* ((default-directory *emacs-home*))
      (setq load-path (cons "/usr/local/share/emacs/site-lisp" load-path))
      (setq load-path (cons *emacs-home* load-path))
      (normal-top-level-add-subdirs-to-load-path)))

(setq custom-file (concat *emacs-home* "/custom.el")
      custom-buffer-done-function 'kill-buffer)
(or (file-exists-p custom-file) (write-region "" nil custom-file))
(load custom-file t t)

(defun try-require (&rest args)
  "Attempt to load a library or module.  Returns T if all of the libraries
given as arguments are successfully loaded and NIL otherwise."
  (if (member nil
              (mapcar (lambda (thing)
                        (condition-case e
                                        (if (stringp thing)
                                            (load-library thing)
                                            (require thing))
                                        (file-error () nil)))
                      args))
      nil
      t))

;;; Set up package manager

(require 'package)
(setq package-archives
      '(("gnu"          . "https://elpa.gnu.org/packages/")
        ("melpa-stable" . "https://stable.melpa.org/packages/")
        ("melpa"        . "https://melpa.org/packages/")
        ("nongnu"       . "https://elpa.nongnu.org/nongnu/")))

;; Pin cond-let to nongnu archive (more stable than MELPA)
(setq package-pinned-packages
      '((cond-let . "nongnu")))

;; Keep warnings you care about; suppress "obsolete" noise.
(setq byte-compile-warnings '(docstrings unresolved (not obsolete)))

;;;; global defaults

(fset 'yes-or-no-p 'y-or-n-p)           ; allow abbrev.

(setq-default ctl-arrow t               ; display CTL char w/ carets
              tab-width 4               ; default is bad for code
              indent-tabs-mode nil      ; don't use TABs
              fill-column 72            ; text-mode wrap / comment fill
              kill-read-only-ok t)
                                        ; okey to kill read-only (copy)

(setq inhibit-startup-message t         ; disable startup messages
      initial-scratch-message nil       ; no initial message in *scratch*
      inferior-lisp-program
      (if (string= (shell-command-to-string "uname -m | tr -d '\n'") "arm64")
          "sbcl"                        ; Apple Silicon: SBCL
        "ccl")                          ; x86_64: Clozure CL
      transient-mark-mode nil           ; don't mark selections
      kill-ring-max 500                 ; grow kill ring
      kill-whole-line t                 ; kill through NL when at BOL
      kill-read-only t                  ; allow kill in read-only buffers
      global-font-lock-mode t           ; try to font lock all buffers
      auto-save-default nil             ; don't auto-save
      default-case-fold-search t        ; ignore case during search
      next-line-add-newlines nil        ; do not grow file past EOF
      column-number-mode t              ; show columns in mode line
      sentence-end-double-space t       ; just in case (default)
      enable-local-variables nil        ; process local variables

      lisp-simple-loop-indentations 1   ; make loop keywords aligned
      lisp-loop-keyword-indentation 6
      lisp-loop-forms-indentation 6

      user-mail-address "ddp@electric-loft.org"
      smtpmail-smtp-server "mail.yoyodyne.com"
      smtpmail-smtp-service 587

      ;; gnus-nntp-server "news.gmane.org"
      gnus-nntp-server "news.eternal-september.org"
      ispell-program-name "ispell"

      ;; Prefer SSH method for TRAMP
      tramp-default-method "ssh"

      ;; Use POSIX-compatible shell on remote if default is csh/tcsh
      tramp-remote-shell "/bin/sh"
      tramp-default-remote-shell "/bin/sh"

      ;; Make TRAMP less chatty
      tramp-verbose 1

      ;; Set persistent remote file cache size
      tramp-chunksize 2000

      ;; Optional: Clean up remote tmp files
      tramp-cleanup-connection t
      tramp-cleanup-all-buffers t

      backup-by-copying t
      backup-directory-alist '(("." . "~/.saves/"))
      delete-old-versions t
      kept-new-versions 10
      kept-old-versions 10
      make-backup-files t
      version-control t )

;; Load TRAMP explicitly after settings
(require 'tramp)

;; Fix TRAMP using GUI Emacs with ssh-agent
(when (and (getenv "SSH_AUTH_SOCK") 
           (file-exists-p (getenv "SSH_AUTH_SOCK")))
  (setenv "SSH_AUTH_SOCK" (getenv "SSH_AUTH_SOCK")))

;; Force tab to 8-column
(add-hook 'shell-mode-hook (lambda () (setq-local tab-width 8)))

(when (eq window-system 'ns)
  ;; Force load full tcsh environment including opam
  (let ((full-env (shell-command-to-string "tcsh -c 'source ~/.tcshrc && env'")))
    (dolist (line (split-string full-env "\n"))
      (when (string-match "^\\([^=]+\\)=\\(.*\\)$" line)
        (let ((var (match-string 1 line))
              (value (match-string 2 line)))
          (when (member var '("PATH" "OPAM_SWITCH_PREFIX" "OCAML_TOPLEVEL_PATH" "CAML_LD_LIBRARY_PATH"))
            (setenv var value)))))
    (setq exec-path (split-string (getenv "PATH") ":"))))

(when (memq window-system '(mac ns x))
  (condition-case nil
      (progn
        (require 'exec-path-from-shell)  
        (setq exec-path-from-shell-variables '("PATH" "SSH_AUTH_SOCK" "LANG" "LC_ALL"))
        (exec-path-from-shell-initialize))
    (error (message "exec-path-from-shell not available"))))

(defun open-remote-root-file (host path)
  "Open remote file as root via sudo over SSH."
  (interactive "sHost: \nsPath: ")
  (find-file (format "/ssh:%s|sudo:%s:%s" host host path)))

(put 'narrow-to-region 'disabled nil)

(when (fboundp 'blink-cursor-mode)
      (blink-cursor-mode t))        ; use blinking cursor

;; UI cleanup for all contexts

(when (fboundp 'tool-bar-mode) (tool-bar-mode -1))
(unless window-system (menu-bar-mode -1))

(when (display-graphic-p)
  (message "GUI window system active (%s)" window-system)

  ;; Host-specific frame dimensions
  (let ((frame-config
         (append
          '((left . 100)
            (top . 0)
            (left-fringe . 4)
            (right-fringe . 4))
          (cond
           ((string= *host* "om")
            '((width . 108) (height . 50)))
           ((or (string= *host* "lambda")
                (string= *host* "lambda.local"))
            '((width . 100) (height . 46)))
           ((or (string= *host* "fluffy")
                (string= *host* "fluffy.local"))
            '((width . 140) (height . 86)))
           (t
            '((width . 108) (height . 50)))))))
    (setq initial-frame-alist frame-config
          default-frame-alist frame-config))

  ;; Default font (adjust to taste)
  (set-face-attribute 'default nil
                      :family "IBM Plex Mono"   ;; or whatever you chose
                      :height 140)

  ;; Fringes
  (when (fboundp 'fringe-mode)
    (fringe-mode '(4 . 4)))

  ;; Titles and mouse behavior
  (setq mouse-yank-at-point t
        frame-title-format "Buffer: %b    File: %f%+"
        icon-title-format  "Emacs: %f")
  (mouse-avoidance-mode 'exile))

;;;; "dired" customizations

(eval-after-load 'dired
                 '(progn 
                   ;; 'b' -> browse file
                   (define-key dired-mode-map "b" 'browse-url-of-dired-file)

                   ;; 'o' -> 'open' command
                   (define-key dired-mode-map "o" 'dired-open-mac)

                   (defun dired-open-mac ()
                     (interactive)
                     (let ((file-name (dired-get-file-for-visit)))
                       (if (file-exists-p file-name)
                           (shell-command (concat "open '" file-name "'" nil)))))))

;;;; custom functions

(with-eval-after-load 'tramp
  ;; Remove the broken proxy if present
  (setq tramp-default-proxies-alist
        (delete '("\\`ns1\\.adelman\\.com\\'" nil "/ssh:servfail.adelman.com:")
                tramp-default-proxies-alist))

  ;; Correct: proxy includes ssh to %h (the target host)
  (add-to-list 'tramp-default-proxies-alist
               '("\\`ns1\\.adelman\\.com\\'" nil
                 "/ssh:servfail.adelman.com|ssh:%h:")))

(defun ddp-become-nameserver ()
  "Trampoline through servfail to edit /usr/local/etc/nsd/master/ on ns1.adelman.com."
  (interactive)
  (message "Opening trampoline through servfail to ns1...")
  (find-file "/ssh:servfail.adelman.com|ssh:ns1.adelman.com:/usr/local/etc/nsd/master/"))

;; this doesn't work
;; (defun ddp-become-nameserver-as-root ()
;;   (interactive)
;;   (find-file
;;    "/ssh:servfail.adelman.com|ssh:ns1.adelman.com|sudo::/usr/local/etc/nsd/master/"))

(defun ddp-become-servfail ()
  "Trampoline through servfail to servfail.adelman.com."
  (interactive)
  (message "Opening trampoline to servfail...")
  (find-file "/ssh:servfail.adelman.com:~"))

(defun ddp-become-yoyodyne ()
  "Trampoline through servfail to edit /www/yododyne/ddp/ on www.yoyodyne.com."
  (interactive)
  (message "Opening trampoline to yoyodyne...")
  (find-file "/ssh:www.yoyodyne.com:/www/yoyodyne/ddp/"))

(defun ddp-become-other ()
  "Open ~ locally when on fluffy; otherwise TRAMP to fluffy.eludom.net."
  (interactive)
  (message "Open an emacs on the logical other...")
  (let ((host (system-name)))
    (if (string-match-p "\\`fluffy\$begin:math:text$\\\\\.\.\*\\$end:math:text$?\\'" host)
        (find-file (expand-file-name "~/"))
      (find-file "/ssh:fluffy.eludom.net:~/"))))

(defun ddp-clear-buffer ()
 "Clear the entire buffer."
 (interactive)
 (mark-whole-buffer)
 (delete-region (point-min) (point-max)))

(defun ddp--previous-nonblank-line ()
  (let ((found nil))
    (while (and (not found) (not (bobp)))
      (forward-line -1)
      (unless (looking-at-p "^[[:space:]]*$")
        (setq found t)))
    found))

(defun ddp-copy-char-above ()
  (interactive)
  (copy-from-above-command 1))

(defun ddp-copy-to-eol-above ()
  (interactive)
  (let ((col (current-column)) (text ""))
    (save-excursion
      (when (ddp--previous-nonblank-line)
        (move-to-column col)
        (setq text (buffer-substring-no-properties
                    (point) (line-end-position)))))
    (insert text)))

(keymap-global-set "C-c <up>" #'ddp-copy-char-above)

(repeat-mode 1)
(setq repeat-exit-timeout nil)   ;; don't drop out just because you paused

(defun ddp-exit-repeat ()
  (interactive)
  ;; Do nothing; leaving the repeat map happens automatically because this key
  ;; isn't bound to ddp-copy-* commands.
  nil)

(defvar ddp-copy-from-above-repeat-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "<up>")    #'ddp-copy-char-above)
    (define-key map (kbd "<right>") #'ddp-copy-to-eol-above)
    (define-key map (kbd "<down>")  #'keyboard-quit)    ;; explicit quit
    (define-key map (kbd "<escape>") #'ddp-exit-repeat) ;; silent exit
    map))

(put 'ddp-copy-char-above   'repeat-map 'ddp-copy-from-above-repeat-map)
(put 'ddp-copy-to-eol-above 'repeat-map 'ddp-copy-from-above-repeat-map)

(defun ddp-copy-line (&optional arg)
  "Copy a line by temporarily marking it read-only.  Assume kill-read-only is T."
  (interactive "P")
  (read-only-mode 1)
  (kill-line arg)
  (read-only-mode 0))

(defun ddp-dvorak-on ()
  "Setup dvorak mode for new buffers; use C-\ to toggle modes."
  (interactive)
  (custom-set-variables
   '(default-input-method "english-dvorak"))
  (advice-add 'switch-to-buffer :after 
              (lambda (&rest _) (activate-input-method "english-dvorak"))))

(defun ddp-emacs-info ()
  "Go to system info node for this emacs."
  (interactive)
  (condition-case err
      (info "emacs")  ; Let Emacs find it
    (error 
     (message "Emacs info not found: %s" (error-message-string err)))))

(defun ddp-goto-match-beginning ()
  "Use with isearch hook to end search at first char of match."
  (when isearch-forward (goto-char isearch-other-end)))

(add-hook 'isearch-mode-end-hook 'ddp-goto-match-beginning)

(defun ddp-hex-edit ()
  "Go into hexl-mode for editing binary files."
  (interactive)
  (hexl-mode)
  (binary-overwrite-mode t))

(defun ddp-indent-for-comment ()
  "Indent for current comment column and return."
  (interactive)
  (save-excursion
   (indent-for-comment)))

(defun ddp-insert-euro ()
  "Insert the euro currency symbol in utf-8."
  (interactive)
  (ucs-insert #x20ac))

(defvar ddp-hyperspec-root "~/iCloud/src/HyperSpec/"
  "Root directory of local HyperSpec copy.")

(defun ddp-lookup-in-hyperspec ()
  "Look up symbol at point in Common Lisp HyperSpec."
  (interactive)
  (let ((symbol (thing-at-point 'symbol t)))
    (if symbol
        (let* ((symbol-name (upcase symbol))
               (index-file (expand-file-name "Front/index.htm" ddp-hyperspec-root)))
          (if (file-exists-p index-file)
              (browse-url (concat "file://" index-file "#" symbol-name))
            (message "HyperSpec not found at %s" ddp-hyperspec-root)))
      (message "No symbol at point"))))

;;;; Add a "Seen" column to ibuffer
(with-eval-after-load 'ibuffer
  (require 'ibuf-ext)   ;; for define-ibuffer-sorter
  (require 'time-date)

  ;; Track when buffers were last shown.
  (defvar ddp-buffer-last-viewed (make-hash-table :test 'eq))

  (defun ddp--stamp-current-buffer (&rest _)
    (puthash (current-buffer) (current-time) ddp-buffer-last-viewed))

  ;; Update on buffer display changes (and generally as Emacs updates the buffer list).
  (add-hook 'buffer-list-update-hook #'ddp--stamp-current-buffer)

  (define-ibuffer-column ddp-last-viewed
    (:name "Seen" :inline t)
    (let ((t0 (gethash buffer ddp-buffer-last-viewed)))
      (if t0 (format-time-string "%Y-%m-%d %H:%M" t0) "")))

  (define-ibuffer-sorter ddp-last-viewed
    "Sort by ddp last-viewed timestamp (newest first)."
    (:description "last viewed")
    (let ((ta (or (gethash a ddp-buffer-last-viewed) '(0 0 0 0)))
          (tb (or (gethash b ddp-buffer-last-viewed) '(0 0 0 0))))
      (time-less-p ta tb)))

  ;; Add the column to your format (adjust widths to taste).
  (setq ibuffer-formats
        '((mark modified read-only " "
                (name 24 24 :left :elide) " "
                (ddp-last-viewed 16 16 :left) " "
                (size 9 -1 :right) " "
                (mode 16 16 :left :elide) " "
                filename-and-process)))

  ;; Optional: make it the default sort.
  (setq ibuffer-default-sorting-mode 'ddp-last-viewed))

;;;; OCaml configuration

(when (executable-find "opam")
  (let ((opam-share (string-trim (shell-command-to-string "opam var share"))))
    (when (file-directory-p opam-share)
      (add-to-list 'load-path (concat opam-share "/emacs/site-lisp")))))

;; OCaml mode setup
(when (try-require 'tuareg)
  (setq auto-mode-alist 
        (append '(("\\.ml[ily]?$" . tuareg-mode)
                  ("\\.topml$" . tuareg-mode)) 
                auto-mode-alist))
  
  ;; Merlin for type information and completion
  (when (try-require 'merlin)
    (add-hook 'tuareg-mode-hook 'merlin-mode)
    (setq merlin-error-after-save nil))
  
  ;; Skip utop integration - use shell-based approach instead
  ;; (when (try-require 'utop)
  ;;   (add-hook 'tuareg-mode-hook 'utop-minor-mode)
  ;;   (setq utop-command "utop"))
  
  ;; OCaml-specific keybindings - using tuareg evaluation
  (eval-after-load 'tuareg
    '(progn
       (define-key tuareg-mode-map "\C-c\C-e" 'tuareg-eval-phrase)
       (define-key tuareg-mode-map "\C-c\C-r" 'tuareg-eval-region)
       (define-key tuareg-mode-map "\C-c\C-b" 'tuareg-eval-buffer))))

(when (try-require 'company)
  (add-hook 'tuareg-mode-hook 'company-mode))

(add-hook 'tuareg-mode-hook
  (lambda ()
    (setq compile-command 
          (concat "ocamlfind ocamlc -package str -linkpkg -o " 
                  (file-name-sans-extension (buffer-name)) " "
                  (buffer-name)))))

(defun ddp-run-ocaml ()
  "Start utop in dumb terminal mode for Emacs."
  (interactive)
  (let ((default-directory "~/src/ocaml/"))
    (unless (file-exists-p default-directory)
      (make-directory default-directory t))
    (let ((buffer (get-buffer-create "*utop*"))
          (process-environment (cons "TERM=dumb" process-environment)))
      (switch-to-buffer buffer)
      (unless (comint-check-proc buffer)
        (make-comint "utop" "utop")))))

(use-package lua-mode :ensure t)

(defun ddp-norns-connect ()
  "Connect to norns for script development."
  (interactive)
  (find-file "/ssh:we@192.168.0.161:/home/we/dust/code/"))

;;;; claude-code

;; add melpa to package archives, as vterm is on melpa:
(require 'package)
(add-to-list 'package-archives '("melpa" . "https://melpa.org/packages/") t)
(package-initialize)

;; Ensure projectile is loaded and configured
(use-package projectile
  :ensure t
  :init
  (projectile-mode +1)
  :config
  (setq projectile-project-search-path '("~/src" "~/"))
  (setq projectile-indexing-method 'alien))

;; install required inheritenv dependency:
(use-package inheritenv
  :vc (:url "https://github.com/purcell/inheritenv" :rev :newest))

;; install Monet IDE
(use-package monet
  :vc (:url "https://github.com/stevemolitor/monet" :rev :newest))

;; Terminal backends:
(use-package vterm :ensure t)
(use-package eat :ensure t)
;; Try eat instead of vterm to fix 1-second bounce issue
(setq claude-code-terminal-backend 'eat)

;; install claude-code.el
(use-package claude-code
  :vc (:url "https://github.com/stevemolitor/claude-code.el" :rev :newest)
  :demand t
  :config
  ;; Skip welcome screen to avoid 1-second periodic bounce issue
  (setq claude-code-program-switches '("--continue"))

  ;; optional IDE integration with Monet
  (add-hook 'claude-code-process-environment-functions
            #'monet-start-server-function)
  (monet-mode 1)
  ;; Bind to the transient menu (as recommended in the docs)
  (keymap-global-set "C-c c" #'claude-code-transient))

;; Prevent scroll bouncing in vterm/claude-code sessions
(setq-default scroll-margin 0
              scroll-conservatively 101        ; never recenter, scroll 1 line at a time
              scroll-step 1                    ; scroll smoothly, not in jumps
              scroll-preserve-screen-position t ; keep cursor position when scrolling
              auto-window-vscroll nil)         ; prevent automatic vertical scrolling

;; VTerm-specific: disable aggressive scrolling
(with-eval-after-load 'vterm
  (setq vterm-max-scrollback 10000)           ; reasonable scrollback
  (add-hook 'vterm-mode-hook
            (lambda ()
              (setq-local scroll-margin 0
                          scroll-conservatively 101
                          auto-window-vscroll nil)))

  ;; Prevent vterm from auto-scrolling during process output (fixes thinking mode bounce)
  (advice-add 'vterm--redraw :around
              (lambda (orig-fun &rest args)
                (let ((scroll-conservatively 101)
                      (scroll-margin 0))
                  (apply orig-fun args)))))

;;; Global overrides (Emacs 29+)
(keymap-global-set "C-j" #'backward-kill-word)
(keymap-global-set "C-r" #'query-replace)
(keymap-global-set "C-s" #'isearch-forward-regexp)
(keymap-global-set "C-t" #'tab-to-tab-stop)
(keymap-global-set "C-z" #'suspend-emacs)

(keymap-global-set "C-c e" (lambda () (interactive) (find-file "~/.emacs")))
(keymap-global-set "C-c z" (lambda () (interactive) (find-file "~/.zshrc")))

(keymap-global-set "C-x C-b" #'electric-buffer-list)
(keymap-global-set "C-x C-i" #'ibuffer)
(keymap-global-set "C-x C-q" #'read-only-mode)

(keymap-global-set "M-/" #'hippie-expand)
(keymap-global-set "M-@" #'ddp-insert-euro)

(keymap-global-set "<f1>" #'scroll-other-window-down)
(keymap-global-set "<f2>" #'scroll-other-window)
(keymap-global-set "<f3>" #'delete-other-windows)

(defvar-keymap ddp-map
  :doc "ddp personal keymap."
  "c" #'comment-or-uncomment-region
  "f" #'rgrep
  "g" #'gnus
  "i" #'indent-region
  "l" #'add-change-log-entry
  "n" #'ddp-norns-connect
  "o" #'ddp-become-other
  "p" #'list-packages
  "s" #'ddp-become-servfail
  "t" #'text-mode
  "x" #'ddp-clear-buffer
  "y" #'ddp-become-yoyodyne
  ";" #'ddp-indent-for-comment
  "," #'ddp-become-servfail
  "." #'ddp-become-nameserver
  "(" #'ddp-run-scheme

  "C-f" #'font-lock-mode
  "C-h" #'split-window-horizontally
  "C-l" #'ddp-run-lisp
  "C-m" #'ddp-run-ocaml
  "C-o" #'delete-other-windows
  "C-v" #'split-window-vertically
  "C-x" #'clean-buffer-list)

(keymap-global-set "C-c d" ddp-map)

;;; Your old lambda, modernized slightly (quote args for shells).
(defun ddp-ocaml-run-buffer-name ()
  (interactive)
  (compile (format "cd %s && ocaml %s"
                   (shell-quote-argument default-directory)
                   (shell-quote-argument (buffer-name)))))

(keymap-set ddp-map "C-e" #'ddp-ocaml-run-buffer-name)

;;; blank-mode (autoload is still fine; bind via keymap API)
(autoload 'blank-mode "blank-mode" nil t)
(keymap-global-set "<f4>" #'blank-mode)

;;; F8 macro behavior (keep your version gate)
(keymap-global-set "<f8>"
                   (if (< emacs-major-version 22)
                       #'call-last-kbd-macro
                     #'kmacro-end-and-call-macro))

;;;; ibuffer has 's r' for sort by recently used

(with-eval-after-load 'ibuffer
  (setq ibuffer-formats
        '((mark modified read-only locked
                " " (name 30 30 :left :elide)
                " " (size 9 -1 :right)
                " " (mode 16 16 :left :elide)
                " " filename-and-process)
          (mark " " (name 30 -1) " " filename-and-process))))

;;;; auto-modes

(setq auto-mode-alist (append 
                       '(("\\.lisp$" . lisp-mode)
                         ("\\.asd$" . lisp-mode)
                         ("\\.system$" . lisp-mode)
                         ("\\.scm$" . scheme-mode)
                         ("\\.meta$" . scheme-mode)
                         ("\\.setup$" . scheme-mode)
                         ) auto-mode-alist))

;;;; fancy lambda

(defconst ddp-lambda--keywords
  '(("\\_<lambda\\_>"
     (0 (progn
          (compose-region (match-beginning 0) (match-end 0) "λ")
          nil))))
  "Font-lock keywords to prettify `lambda` as `λ`.")

(defun ddp-lambda-mode-hook ()
  "Prettify `lambda` to `λ` in Scheme-family buffers."
  (font-lock-add-keywords nil ddp-lambda--keywords 'append)
  (when (fboundp 'font-lock-flush) (font-lock-flush)))

(add-hook 'scheme-mode-hook #'ddp-lambda-mode-hook)

;;;; Paredit mode

(use-package paredit
  :ensure t
  :hook (scheme-mode . paredit-mode))

;;;; Scheme settings

;; Use Chicken Scheme
(setq scheme-program-name "csi")  ; Chicken Scheme interpreter

(defun ddp-run-scheme ()
  "Start Chicken Scheme REPL in ~/src/scm."
  (interactive)
  (let ((default-directory "~/src/scm/"))
    (unless (file-exists-p default-directory)
      (make-directory default-directory t))
    (run-scheme scheme-program-name)))

;;;; Lisp settings

;; SLY: architecture-specific implementation (SBCL for arm64, Clozure for x86_64)
(let* ((arch (string-trim (shell-command-to-string "uname -m")))
       (is-arm64 (string= arch "arm64"))
       (sbcl-path (expand-file-name "~/bin/sbcl/bin/sbcl"))
       (ccl-path (expand-file-name "~/bin/ccl/dx86cl64")))
  (cond
   ;; Apple Silicon: use SBCL
   ((and is-arm64 (file-executable-p sbcl-path))
    (setq sly-lisp-implementations
          `((sbcl (,sbcl-path) :coding-system utf-8-unix)))
    (setq sly-default-lisp 'sbcl)
    (setenv "SBCL_HOME" (expand-file-name "~/bin/sbcl/lib/sbcl")))

   ;; x86_64: use Clozure CL
   ((and (not is-arm64) (file-executable-p ccl-path))
    (setq sly-lisp-implementations
          `((ccl (,ccl-path) :coding-system utf-8-unix)))
    (setq sly-default-lisp 'ccl))

   ;; Fallback: try to find either in PATH
   (t
    (let ((sbcl-found (executable-find "sbcl"))
          (ccl-found (executable-find "ccl")))
      (cond
       ((and is-arm64 sbcl-found)
        (setq sly-lisp-implementations
              `((sbcl (,sbcl-found) :coding-system utf-8-unix)))
        (setq sly-default-lisp 'sbcl))
       ((and (not is-arm64) ccl-found)
        (setq sly-lisp-implementations
              `((ccl (,ccl-found) :coding-system utf-8-unix)))
        (setq sly-default-lisp 'ccl))
       (sbcl-found
        (setq sly-lisp-implementations
              `((sbcl (,sbcl-found) :coding-system utf-8-unix)))
        (setq sly-default-lisp 'sbcl))
       (ccl-found
        (setq sly-lisp-implementations
              `((ccl (,ccl-found) :coding-system utf-8-unix)))
        (setq sly-default-lisp 'ccl)))))))

;; SLY (autoload; no eager load, so it won't perturb keymaps until you use it)
(autoload 'sly "sly" nil t)
(autoload 'sly-connect "sly" nil t)

(with-eval-after-load 'sly
  ;; Quality-of-life defaults.
  (setq sly-auto-start 'always)       ; start Lisp automatically when needed
  (setq sly-kill-without-query-p t))

(defun ddp-run-lisp ()
  (interactive)
  (cd "~/src/lisp")
  (if (fboundp 'sly)
      (sly)
    (user-error "SLY is not installed/loaded (install package `sly`)")))


(setq server-name "ns")             ; NeXTStep
(server-start)                      ; server for emacsclient

;;;; Load timing completion
(when ddp-debug-loading
  (let ((end-time (current-time)))
    (message "--> .emacs loaded in %.2fs" 
             (float-time (time-subtract end-time *emacs-load-start*)))))

;;;; ---- end of ddp's .emacs ----
(custom-set-variables
 ;; custom-set-variables was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(package-selected-packages
   '(sly)))
(custom-set-faces
 ;; custom-set-faces was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 )
