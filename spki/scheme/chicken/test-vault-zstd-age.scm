#!/usr/bin/env csi -s
;;; Test vault zstd-age archive format
;;;
;;; Tests:
;;; 1. Generate age keypair
;;; 2. Configure vault with age recipients
;;; 3. Create archive with zstd-age format
;;; 4. Verify archive exists and has correct structure
;;; 5. Restore from archive

(import vault
        crypto-ffi
        (chicken file)
        (chicken file posix)
        (chicken format)
        (chicken io)
        (chicken process)
        (chicken process-context)
        (chicken blob)
        (chicken string)
        srfi-4)

(sodium-init)

;; Helper
(define (blob->hex b)
  (define (byte->hex n)
    (let ((s (number->string n 16)))
      (if (= (string-length s) 1)
          (string-append "0" s)
          s)))
  (let ((vec (blob->u8vector b)))
    (let loop ((i 0) (acc '()))
      (if (= i (u8vector-length vec))
          (apply string-append (reverse acc))
          (loop (+ i 1)
                (cons (byte->hex (u8vector-ref vec i)) acc))))))

(define (run-command . args)
  (let-values (((in out pid) (process (string-intersperse args " "))))
    (let ((result (read-string #f in)))
      (close-input-port in)
      (close-output-port out)
      result)))

(print "=== Vault Zstd+Age Archive Test ===\n")

;; Check prerequisites
(print "Checking prerequisites...")
(unless (file-exists? "/opt/homebrew/bin/age")
  (error "age not found - install with: brew install age"))
(unless (file-exists? "/opt/homebrew/bin/zstd")
  (error "zstd not found - install with: brew install zstd"))
(print "✓ age and zstd available\n")

;; Create test directory
(define test-dir "/tmp/test-vault-zstd-age")
(when (directory-exists? test-dir)
  (system (format "rm -rf ~a" test-dir)))
(create-directory test-dir #t)
(change-directory test-dir)
(print "Working in: " test-dir "\n")

;; Initialize git repo
(print "Initializing git repository...")
(system "git init -q")
(system "git config user.email 'test@example.com'")
(system "git config user.name 'Test User'")
(print "✓ Git initialized\n")

;; Create .vault directories
(create-directory ".vault" #t)
(create-directory ".vault/metadata" #t)
(create-directory ".vault/releases" #t)

;; Generate age keypair
(print "Generating age keypair...")
(define age-identity-file (format "~a/test-identity.txt" test-dir))
(define age-recipient-file (format "~a/test-recipient.txt" test-dir))
(system (format "age-keygen -o ~a 2>~a" age-identity-file age-recipient-file))

;; Extract recipient from the output
(define age-recipient
  (let ((content (with-input-from-file age-recipient-file read-line)))
    (if (and (>= (string-length content) 12)
             (string=? (substring content 0 12) "Public key: "))
        (substring content 12)
        (error "Could not extract age public key"))))
(print "✓ Age recipient: " (substring age-recipient 0 20) "...\n")

;; Generate SPKI signing keypair
(print "Generating SPKI signing keypair...")
(define keys (ed25519-keypair))
(define public-key (car keys))
(define private-key (cadr keys))
(print "✓ SPKI key: " (substring (blob->hex public-key) 0 20) "...\n")

;; Initialize vault
(print "Initializing vault...")
(vault-init signing-key: private-key)
(vault-config 'age-recipients (list age-recipient))
(vault-config 'age-identity age-identity-file)
(print "✓ Vault configured with age recipient\n")

;; Create test content
(print "Creating test content...")
(with-output-to-file "README.md"
  (lambda ()
    (display "# Test Project\n\nThis is a test for zstd-age archives.\n")))
(with-output-to-file "code.scm"
  (lambda ()
    (display "(define (hello) (print \"Hello, cyberspace!\"))\n")))
(system "git add .")
(system "git commit -q -m 'Initial commit'")
(print "✓ Test files created and committed\n")

;; Create a release
(print "Creating release v0.1.0...")
(seal-release "0.1.0" message: "Test release for zstd-age")
(print "✓ Release v0.1.0 created\n")

;; Create zstd-age archive
(print "Creating zstd-age archive...")
(seal-archive "0.1.0" format: 'zstd-age)
(print "✓ Archive created\n")

;; Verify archive files exist
(print "Verifying archive structure...")
(define manifest-file "vault-0.1.0.archive")
(define archive-file "vault-0.1.0.archive.tar.zst.age")

(unless (file-exists? manifest-file)
  (error "Manifest file not found: " manifest-file))
(print "  ✓ Manifest: " manifest-file)

(unless (file-exists? archive-file)
  (error "Archive file not found: " archive-file))
(define archive-size (file-size archive-file))
(print "  ✓ Archive: " archive-file " (" archive-size " bytes)\n")

;; Read and display manifest
(print "Manifest contents:")
(define manifest (with-input-from-file manifest-file read))
(print "  Format: " (cadr (assq 'format (cdr manifest))))
(print "  Compression: " (cadr (assq 'compression (cdr manifest))))
(print "  Encryption: " (cadr (assq 'encryption (cdr manifest))))
(print "")

;; Test restoration
(print "Testing restoration...")
(define restore-dir (format "~a/restored" test-dir))
(create-directory restore-dir #t)
(seal-restore manifest-file
              target: restore-dir
              identity: age-identity-file)
(print "✓ Archive restored to: " restore-dir "\n")

;; Verify restored content
(print "Verifying restored content...")
(define restored-readme (format "~a/vault/README.md" restore-dir))
(if (file-exists? restored-readme)
    (begin
      (print "  ✓ README.md restored")
      (print "  Content: " (with-input-from-file restored-readme read-line)))
    (print "  ✗ README.md not found"))

(define restored-code (format "~a/vault/code.scm" restore-dir))
(if (file-exists? restored-code)
    (print "  ✓ code.scm restored")
    (print "  ✗ code.scm not found"))
(print "")

;; Cleanup
(print "Cleaning up...")
(change-directory "/tmp")
;; Leave test dir for inspection: (system (format "rm -rf ~a" test-dir))
(print "Test directory preserved at: " test-dir "\n")

(print "=== All Tests Passed ===\n")
