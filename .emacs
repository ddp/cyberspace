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

(defvar *host* (getenv "HOST")) ; 'nil
(defvar *os* (getenv "OSTYPE")) ; 'nil
(defvar *path* (getenv "PATH")) ; ok

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

(message "*emacs-home* %s" *emacs-home*)

(require 'package)
(setq package-enable-at-startup nil) ;; Optional: speeds startup, disables auto-loading
(add-to-list 'package-archives '("melpa-stable" . "https://stable.melpa.org/packages/") t)
(add-to-list 'package-archives '("melpa" . "https://melpa.org/packages/") t)
(package-initialize)

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
      server-name "editor"              ; for emacsclient and EDITOR
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

(server-start)                      ; server for emacsclient

;; UI cleanup for all contexts

(when (fboundp 'tool-bar-mode) (tool-bar-mode -1))
(unless window-system (menu-bar-mode -1))

;; GUI-specific config

(when window-system
  (message "X window system active")
  
  ;; Host-specific frame dimensions
  (let ((frame-config 
         (append '((left . 100) (top . 50) (left-fringe . 2) (right-fringe . 2))
                 (if (string= *host* "om.local")
                     '((width . 140) (height . 68))
                   '((width . 170) (height . 80))))))
    (setq initial-frame-alist frame-config
          default-frame-alist frame-config))
  
  ;; GUI preferences

  (when (fboundp 'fringe-mode) (fringe-mode '(2 . 2)))
  (setq mouse-wheel-progressive-speed nil
        mouse-yank-at-point t
        frame-title-format "Buffer: %b    File: %f%+"
        icon-title-format "Emacs: %f")
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

;;;; isearch - end at match instead of beginning

(defun ddp-goto-match-beginning ()
  "Use with isearch hook to end search at first char of match."
  (when isearch-forward (goto-char isearch-other-end)))

(add-hook 'isearch-mode-end-hook 'ddp-goto-match-beginning)

;;;; custom functions

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

(defun ddp-hex-edit ()
  "Go into hexl-mode for editing binary files."
  (interactive)
  (hexl-mode)
  (binary-overwrite-mode t))

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

(defun ddp-insert-euro ()
  "Insert the euro currency symbol in utf-8."
  (interactive)
  (ucs-insert #x20ac))

(defun ddp-indent-for-comment ()
  "Indent for current comment column and return."
  (interactive)
  (save-excursion
   (indent-for-comment)))

(defun ddp-become-nameserver ()
  "Trampoline through servfail to edit /usr/local/etc/nsd/master/ on ns1.adelman.com."
  (interactive)
  (message "Opening trampoline through servfail to ns1...")
  (find-file "/ssh:servfail.adelman.com|ssh:ns1.adelman.com:/usr/local/etc/nsd/master/"))

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
  "Open an emacs on the logical other."
  (interactive)
  (message "Open an emacs on the logical other...")
  (find-file "/ssh:fluffy.local:~/"))
  
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

;;;; key bindings ("\C-c" reserved for user bindings)

(global-set-key "\C-j" 'backward-kill-word)
(global-set-key "\C-r" 'query-replace)
(global-set-key "\C-s" 'isearch-forward-regexp)
(global-set-key "\C-t" 'tab-to-tab-stop)
(global-set-key "\C-z" 'suspend-emacs)

(global-set-key "\C-ca" 'add-change-log-entry)
(global-set-key "\C-cc" 'comment-or-uncomment-region)
(global-set-key "\C-cf" 'grep)
;; (global-set-key "\C-cg" 'gnus)
(global-set-key "\C-ci" 'indent-region)
(global-set-key "\C-cl" 'list-packages)
(global-set-key "\C-co" 'ddp-become-other)
(global-set-key "\C-cs" 'ddp-become-servfail)
(global-set-key "\C-ct" 'text-mode)
(global-set-key "\C-cy" 'ddp-become-yoyodyne)
(global-set-key "\C-cz" 'ddp-become-nameserver)
(global-set-key "\C-c;" 'ddp-indent-for-comment)

(global-set-key "\C-c\C-d" 'ddp-dvorak-on)
(global-set-key "\C-c\C-e" (lambda () 
                             (interactive)
                             (compile (format "cd %s && ocaml %s" 
                                 default-directory 
                                 (buffer-name)))))
(global-set-key "\C-c\C-f" 'font-lock-mode)
(global-set-key "\C-c\C-h" 'split-window-horizontally)
(global-set-key "\C-c\C-l" 'ddp-run-lisp)
(global-set-key "\C-c\C-m" 'ddp-run-ocaml)
(global-set-key "\C-c\C-o" 'delete-other-windows)
(global-set-key "\C-c\C-s" 'ddp-run-scheme)
(global-set-key "\C-c\C-x" 'clean-buffer-list)
(global-set-key "\C-c\C-v" 'split-window-vertically)

(global-set-key "\C-hi" 'ddp-emacs-info)

(global-set-key "\C-x\C-b" 'electric-buffer-list)
(global-set-key "\C-x\C-q" 'read-only-mode)

(global-set-key [(meta @)] 'ddp-insert-euro)
(global-set-key (kbd "M-/") 'hippie-expand)

(global-set-key [f1] 'scroll-other-window-down)
(global-set-key [f2] 'scroll-other-window)
(global-set-key [f3] 'delete-other-windows)

(autoload 'blank-mode "blank-mode" nil t)
(global-set-key [f4] 'blank-mode)

;; C-x e
(if (< emacs-major-version 22)
    (global-set-key [f8] 'call-last-kbd-macro)
    (global-set-key [f8] 'kmacro-end-and-call-macro))

;;(global-set-key [f9] 'gdb)
;;(global-set-key [f10] 'gud-next)
;;(global-set-key [f11] 'gud-step)
;;(global-set-key [f12] 'gud-finish)

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

(defun ddp-lambda-mode-hook ()
  (font-lock-add-keywords
   nil `(("\\<lambda\\>"
          (0 (progn (compose-region (match-beginning 0) (match-end 0)
                                    ,(make-char 'greek-iso8859-7 107))
                    nil))))))
(add-hook 'emacs-lisp-mode-hook 'ddp-lambda-mode-hook)
(add-hook 'lisp-interactive-mode-hook 'ddp-lambda-mode-hook)
(add-hook 'scheme-mode-hook 'ddp-lambda-mode-hook)

;;;; Scheme settings

(defun ddp-run-scheme ()
  (interactive)
  (cd "~/src/scm")
  (racket-repl))

;;;; Lisp settings

(setq inferior-lisp-program "/usr/local/bin/sbcl")
(setenv "SBCL_HOME" "/usr/local/lib/sbcl")

(defun ddp-run-lisp ()
  (interactive)
  (cd "~/src/lisp")
  (sly))

(require 'sly-autoloads)
(setq inferior-lisp-program "/usr/local/bin/sbcl")

;;;; Load timing completion
(when ddp-debug-loading
  (let ((end-time (current-time)))
    (message "--> .emacs loaded in %.2fs" 
             (float-time (time-subtract end-time *emacs-load-start*)))))

;;;; ---- end of ddp's .emacs ----
