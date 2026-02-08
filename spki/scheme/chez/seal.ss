#!/usr/bin/env chez-script
;;; seal.ss - Cryptographically Sealed Version Control CLI (Chez Port)
;;; Library of Cyberspace
;;;
;;; Usage:
;;;   chez --program seal.ss commit <message> [files...]
;;;   chez --program seal.ss update
;;;   chez --program seal.ss history [--count N]
;;;   chez --program seal.ss verify <version>
;;;   chez --program seal.ss check [--deep]
;;;   chez --program seal.ss init [--signing-key KEY]
;;;
;;; Ported from seal.scm.
;;; Copyright (c) 2026 Yoyodyne. See LICENSE.

(import (rnrs)
        (only (chezscheme)
              printf format void
              command-line exit
              with-output-to-string)
        (cyberspace chicken-compatibility chicken)
        (cyberspace vault))

(define (usage)
  (display "seal - Cryptographically sealed version control\n")
  (display "\n")
  (display "Usage:\n")
  (display "  seal commit <message> [files...]      Seal changes into vault\n")
  (display "           [--catalog]                   Add discovery metadata\n")
  (display "           [--subjects S1,S2,...]         Subject headings\n")
  (display "           [--keywords K1,K2,...]         Search keywords\n")
  (display "           [--description TEXT]           Extended description\n")
  (display "           [--preserve]                   Full preservation metadata\n")
  (display "  seal update                           Update vault from origin\n")
  (display "  seal undo [--hard] [file]             Undo changes\n")
  (display "  seal history [--count N]              Show vault history\n")
  (display "  seal branch <name> [--from ref]       Create sealed branch\n")
  (display "  seal merge <from>                     Merge sealed changes\n")
  (display "\n")
  (display "  seal release <version> [--message M]  Create sealed release\n")
  (display "           [--migrate-from V]\n")
  (display "  seal verify <version>                 Verify release seal\n")
  (display "  seal archive <version> [--format F]   Create sealed archive\n")
  (display "  seal restore <archive>                Restore from archive\n")
  (display "  seal migrate <from> <to> [--script S] Migrate between versions\n")
  (display "           [--dry-run]\n")
  (display "  seal check [--deep]                   Check vault integrity\n")
  (display "\n")
  (display "  seal init [--signing-key KEY]         Initialize vault\n")
  (exit 1))

(define (parse-options args)
  "Parse options and positional arguments"
  (let loop ((args args)
             (options '())
             (positional '()))
    (if (null? args)
        (cons (reverse options) (reverse positional))
        (let ((arg (car args)))
          (if (and (>= (string-length arg) 2)
                   (string=? (substring arg 0 2) "--"))
              (let ((key (string->symbol (substring arg 2 (string-length arg)))))
                (if (and (not (null? (cdr args)))
                         (not (and (>= (string-length (cadr args)) 2)
                                   (string=? (substring (cadr args) 0 2) "--"))))
                    (loop (cddr args)
                          (cons (cons key (cadr args)) options)
                          positional)
                    (loop (cdr args)
                          (cons (cons key #t) options)
                          positional)))
              (loop (cdr args)
                    options
                    (cons arg positional)))))))

(define (get-option options key . rest)
  (let ((default (if (null? rest) #f (car rest))))
    (let ((pair (assq key options)))
      (if pair (cdr pair) default))))

;;; ============================================================
;;; Command Handlers
;;; ============================================================

(define (cmd-commit positional options)
  (when (null? positional)
    (display "Error: commit message required\n") (exit 1))
  (seal-commit (car positional)
               'files: (if (null? (cdr positional)) #f (cdr positional))
               'catalog: (get-option options 'catalog)
               'subjects: (let ((s (get-option options 'subjects)))
                             (and s (string-split s ",")))
               'keywords: (let ((k (get-option options 'keywords)))
                             (and k (string-split k ",")))
               'description: (get-option options 'description)
               'preserve: (get-option options 'preserve)))

(define (cmd-update positional options)
  (seal-update))

(define (cmd-undo positional options)
  (seal-undo 'file: (and (pair? positional) (car positional))
             'hard: (get-option options 'hard)))

(define (cmd-history positional options)
  (let ((c (get-option options 'count)))
    (seal-history 'count: (and c (string->number c)))))

(define (cmd-branch positional options)
  (when (null? positional)
    (display "Error: branch name required\n") (exit 1))
  (seal-branch (car positional) 'from: (get-option options 'from)))

(define (cmd-merge positional options)
  (when (null? positional)
    (display "Error: source branch required\n") (exit 1))
  (seal-merge (car positional) 'strategy: (get-option options 'strategy)))

(define (cmd-release positional options)
  (when (null? positional)
    (display "Error: version required\n") (exit 1))
  (seal-release (car positional)
                'message: (get-option options 'message)
                'migrate-from: (get-option options 'migrate-from)))

(define (cmd-verify positional options)
  (when (null? positional)
    (display "Error: version required\n") (exit 1))
  (seal-verify (car positional) 'verify-key: (get-option options 'verify-key)))

(define (cmd-archive positional options)
  (when (null? positional)
    (display "Error: version required\n") (exit 1))
  (let ((fmt (get-option options 'format)))
    (seal-archive (car positional)
                  'format: (and fmt (string->symbol fmt))
                  'output: (get-option options 'output))))

(define (cmd-restore positional options)
  (when (null? positional)
    (display "Error: archive file required\n") (exit 1))
  (seal-restore (car positional)
                'verify-key: (get-option options 'verify-key)
                'target: (get-option options 'target)))

(define (cmd-migrate positional options)
  (when (< (length positional) 2)
    (display "Error: from and to versions required\n") (exit 1))
  (seal-migrate (car positional) (cadr positional)
                'script: (get-option options 'script)
                'dry-run: (get-option options 'dry-run)))

(define (cmd-check positional options)
  (seal-check 'deep: (get-option options 'deep)))

(define (cmd-init positional options)
  (vault-init 'signing-key: (get-option options 'signing-key)))

;; Command dispatch table
(define *seal-commands*
  `((commit   . ,cmd-commit)
    (update   . ,cmd-update)
    (undo     . ,cmd-undo)
    (history  . ,cmd-history)
    (branch   . ,cmd-branch)
    (merge    . ,cmd-merge)
    (release  . ,cmd-release)
    (verify   . ,cmd-verify)
    (archive  . ,cmd-archive)
    (restore  . ,cmd-restore)
    (migrate  . ,cmd-migrate)
    (check    . ,cmd-check)
    (init     . ,cmd-init)))

;;; ============================================================
;;; Main
;;; ============================================================

(define (main args)
  (when (null? args) (usage))
  (let* ((parsed (cons (car args) (parse-options (cdr args))))
         (command (string->symbol (car parsed)))
         (options (cadr parsed))
         (positional (cddr parsed))
         (handler (assq command *seal-commands*)))
    (if handler
        ((cdr handler) positional options)
        (begin (display (string-append "Error: unknown command: " (car parsed) "\n"))
               (usage)))))

;; Run main (skip program name in command-line)
(let ((args (cdr (command-line))))
  (when (pair? args)
    (main args)))
