#!/usr/bin/env csi -s
;;; seal - Cryptographically sealed version control CLI
;;;
;;; Usage:
;;;   seal commit <message> [files...]   - Seal changes into vault
;;;   seal update                        - Update vault from origin
;;;   seal undo [--hard] [file]          - Undo changes
;;;   seal history [--count N]           - Show vault history
;;;   seal branch <name> [--from ref]    - Create sealed branch
;;;   seal merge <from>                  - Merge sealed changes
;;;
;;;   seal release <version> [--message M] [--migrate-from V]
;;;                                      - Create sealed release
;;;   seal verify <version>              - Verify release seal
;;;   seal archive <version> [--format F] - Create sealed archive
;;;   seal restore <archive>             - Restore from archive
;;;   seal migrate <from> <to> [--script S] [--dry-run]
;;;                                      - Migrate between versions
;;;   seal check [--deep]                - Check vault integrity
;;;
;;;   seal init [--signing-key KEY]      - Initialize vault

(import (chicken base)
        (chicken process-context)
        (chicken string)
        (chicken format)
        vault)

(define (usage)
  (print "seal - Cryptographically sealed version control")
  (print "")
  (print "Usage:")
  (print "  seal commit <message> [files...]      Seal changes into vault
           [--catalog]                   Add discovery metadata
           [--subjects S1,S2,...]         Subject headings
           [--keywords K1,K2,...]         Search keywords
           [--description TEXT]           Extended description
           [--preserve]                   Full preservation metadata")
  (print "  seal update                           Update vault from origin")
  (print "  seal undo [--hard] [file]             Undo changes")
  (print "  seal history [--count N]              Show vault history")
  (print "  seal branch <name> [--from ref]       Create sealed branch")
  (print "  seal merge <from>                     Merge sealed changes")
  (print "")
  (print "  seal release <version> [--message M]  Create sealed release")
  (print "           [--migrate-from V]")
  (print "  seal verify <version>                 Verify release seal")
  (print "  seal archive <version> [--format F]   Create sealed archive")
  (print "  seal restore <archive>                Restore from archive")
  (print "  seal migrate <from> <to> [--script S] Migrate between versions")
  (print "           [--dry-run]")
  (print "  seal check [--deep]                   Check vault integrity")
  (print "")
  (print "  seal init [--signing-key KEY]         Initialize vault")
  (print "")
  (print "The seal metaphor connects:")
  (print "  - Cryptographic sealing (SPKI signatures)")
  (print "  - Library seals (official marks)")
  (print "  - Vault seals (securing archives)")
  (exit 1))

(define (parse-args args)
  "Parse command line arguments into (command . options)"
  (if (null? args)
      (usage)
      (let ((command (car args))
            (rest (cdr args)))
        (cons command (parse-options rest)))))

(define (parse-options args)
  "Parse options and positional arguments"
  (let loop ((args args)
             (options '())
             (positional '()))
    (if (null? args)
        (cons (reverse options) (reverse positional))
        (let ((arg (car args)))
          (if (string-prefix? "--" arg)
              ;; Option flag
              (let ((key (string->symbol (substring arg 2))))
                (if (and (not (null? (cdr args)))
                         (not (string-prefix? "--" (cadr args))))
                    ;; Has value
                    (loop (cddr args)
                          (cons (cons key (cadr args)) options)
                          positional)
                    ;; Boolean flag
                    (loop (cdr args)
                          (cons (cons key #t) options)
                          positional)))
              ;; Positional argument
              (loop (cdr args)
                    options
                    (cons arg positional)))))))

(define (get-option options key #!optional default)
  "Get option value by key"
  (let ((pair (assq key options)))
    (if pair (cdr pair) default)))

(define (main args)
  (when (null? args)
    (usage))

  (let* ((parsed (parse-args args))
         (command (car parsed))
         (options (cadr parsed))
         (positional (cddr parsed)))

    (case (string->symbol command)
      ;; Core operations
      ((commit)
       (when (null? positional)
         (print "Error: commit message required")
         (exit 1))
       (let ((message (car positional))
             (files (cdr positional))
             (catalog (get-option options 'catalog))
             (subjects-str (get-option options 'subjects))
             (keywords-str (get-option options 'keywords))
             (description (get-option options 'description))
             (preserve (get-option options 'preserve)))
         (seal-commit message
                     files: (if (null? files) #f files)
                     catalog: catalog
                     subjects: (if subjects-str
                                  (string-split subjects-str ",")
                                  #f)
                     keywords: (if keywords-str
                                  (string-split keywords-str ",")
                                  #f)
                     description: description
                     preserve: preserve)))

      ((update)
       (seal-update))

      ((undo)
       (let ((file (if (null? positional) #f (car positional)))
             (hard (get-option options 'hard)))
         (seal-undo file: file hard: hard)))

      ((history)
       (let ((count (get-option options 'count)))
         (seal-history count: (if count (string->number count) #f))))

      ((branch)
       (when (null? positional)
         (print "Error: branch name required")
         (exit 1))
       (let ((name (car positional))
             (from (get-option options 'from)))
         (seal-branch name from: from)))

      ((merge)
       (when (null? positional)
         (print "Error: source branch required")
         (exit 1))
       (let ((from (car positional))
             (strategy (get-option options 'strategy)))
         (seal-merge from strategy: strategy)))

      ;; Version management
      ((release)
       (when (null? positional)
         (print "Error: version required")
         (exit 1))
       (let ((version (car positional))
             (message (get-option options 'message))
             (migrate-from (get-option options 'migrate-from)))
         (seal-release version
                      message: message
                      migrate-from: migrate-from)))

      ((verify)
       (when (null? positional)
         (print "Error: version required")
         (exit 1))
       (let ((version (car positional))
             (verify-key (get-option options 'verify-key)))
         (seal-verify version verify-key: verify-key)))

      ((archive)
       (when (null? positional)
         (print "Error: version required")
         (exit 1))
       (let ((version (car positional))
             (format-str (get-option options 'format))
             (output (get-option options 'output)))
         (seal-archive version
                      format: (if format-str
                                 (string->symbol format-str)
                                 #f)
                      output: output)))

      ((restore)
       (when (null? positional)
         (print "Error: archive file required")
         (exit 1))
       (let ((archive (car positional))
             (verify-key (get-option options 'verify-key))
             (target (get-option options 'target)))
         (seal-restore archive
                      verify-key: verify-key
                      target: target)))

      ((migrate)
       (when (< (length positional) 2)
         (print "Error: from and to versions required")
         (exit 1))
       (let ((from (car positional))
             (to (cadr positional))
             (script (get-option options 'script))
             (dry-run (get-option options 'dry-run)))
         (seal-migrate from to
                      script: script
                      dry-run: dry-run)))

      ((check)
       (let ((deep (get-option options 'deep)))
         (seal-check deep: deep)))

      ;; Configuration
      ((init)
       (let ((signing-key (get-option options 'signing-key)))
         (vault-init signing-key: signing-key)))

      (else
       (print "Error: unknown command: " command)
       (usage)))))

;; Run main
(main (command-line-arguments))
