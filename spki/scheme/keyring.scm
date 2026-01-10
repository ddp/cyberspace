;;; keyring.scm - Key Management for the Soup
;;;
;;; "Not your keys, not your crypto" - Bitcoin wisdom
;;;
;;; Provides:
;;; - Named keypair generation and storage
;;; - Key lookup by name or fingerprint
;;; - Key listing and inspection
;;; - Keyring persistence (.vault/keys/)

(module keyring
  (;; Keyring operations
   keyring-init
   keyring-list
   keyring-generate
   keyring-import
   keyring-export
   keyring-delete
   keyring-rename

   ;; Key lookup
   key-by-name
   key-by-fingerprint
   key-exists?

   ;; Key info
   key-info
   key-fingerprint
   key-created
   key-public
   key-private

   ;; Display
   display-key
   display-keyring

   ;; Paths
   keyring-path
   key-path)

  (import scheme
          (chicken base)
          (chicken format)
          (chicken string)
          (chicken file)
          (chicken file posix)
          (chicken pathname)
          (chicken io)
          (chicken port)
          (chicken time)
          (chicken time posix)
          (chicken blob)
          (chicken condition)
          srfi-1
          srfi-13
          (chicken sort)
          crypto-ffi)

  ;; ============================================================
  ;; Paths
  ;; ============================================================

  (define (keyring-path)
    ".vault/keys")

  (define (key-path name ext)
    (make-pathname (keyring-path) name ext))

  ;; ============================================================
  ;; Initialization
  ;; ============================================================

  (define (keyring-init)
    "Initialize keyring directory"
    (let ((path (keyring-path)))
      (unless (directory-exists? path)
        (create-directory path #t)
        (print "Keyring initialized: " path))
      path))

  ;; ============================================================
  ;; Key Storage Format
  ;; ============================================================
  ;; Keys stored as:
  ;;   .vault/keys/NAME.pub  - public key (32 bytes, hex)
  ;;   .vault/keys/NAME.key  - private key (64 bytes, hex, chmod 600)
  ;;   .vault/keys/NAME.meta - metadata (s-expression)

  (define (write-key-files name public-key private-key)
    "Write key files to keyring"
    (let ((pub-path (key-path name "pub"))
          (key-path* (key-path name "key"))
          (meta-path (key-path name "meta")))

      ;; Write public key
      (with-output-to-file pub-path
        (lambda () (display (blob->hex public-key))))

      ;; Write private key (restricted permissions)
      (with-output-to-file key-path*
        (lambda () (display (blob->hex private-key))))
      (set-file-permissions! key-path* #o600)

      ;; Write metadata
      (with-output-to-file meta-path
        (lambda ()
          (write `((name ,name)
                   (algorithm ed25519)
                   (created ,(current-seconds))
                   (fingerprint ,(fingerprint public-key))))))))

  (define (read-key-files name)
    "Read key files from keyring, returns (public private metadata) or #f"
    (let ((pub-path (key-path name "pub"))
          (key-path* (key-path name "key"))
          (meta-path (key-path name "meta")))
      (if (and (file-exists? pub-path)
               (file-exists? key-path*))
          (let ((pub (hex->blob (with-input-from-file pub-path read-line)))
                (priv (hex->blob (with-input-from-file key-path* read-line)))
                (meta (if (file-exists? meta-path)
                          (with-input-from-file meta-path read)
                          '())))
            (list pub priv meta))
          #f)))

  ;; ============================================================
  ;; Hex Conversion
  ;; ============================================================

  (define (blob->hex blob)
    "Convert blob to hex string"
    (let* ((size (blob-size blob))
           (str (blob->string blob))
           (result (make-string (* 2 size))))
      (do ((i 0 (+ i 1)))
          ((>= i size) result)
        (let* ((byte (char->integer (string-ref str i)))
               (hi (quotient byte 16))
               (lo (remainder byte 16)))
          (string-set! result (* i 2) (string-ref "0123456789abcdef" hi))
          (string-set! result (+ (* i 2) 1) (string-ref "0123456789abcdef" lo))))))

  (define (hex->blob hex)
    "Convert hex string to blob"
    (let* ((len (quotient (string-length hex) 2))
           (result (make-string len)))
      (do ((i 0 (+ i 1)))
          ((>= i len) (string->blob result))
        (let ((hi (hex-digit (string-ref hex (* i 2))))
              (lo (hex-digit (string-ref hex (+ (* i 2) 1)))))
          (string-set! result i (integer->char (+ (* hi 16) lo)))))))

  (define (hex-digit c)
    (cond
     ((and (char>=? c #\0) (char<=? c #\9))
      (- (char->integer c) (char->integer #\0)))
     ((and (char>=? c #\a) (char<=? c #\f))
      (+ 10 (- (char->integer c) (char->integer #\a))))
     ((and (char>=? c #\A) (char<=? c #\F))
      (+ 10 (- (char->integer c) (char->integer #\A))))
     (else 0)))

  ;; ============================================================
  ;; Fingerprint
  ;; ============================================================

  (define (fingerprint public-key)
    "Generate fingerprint from public key"
    (let* ((hash (sha512-hash public-key))
           (hex (blob->hex hash)))
      ;; First 32 chars in groups of 4
      (string-join
       (let loop ((s (substring hex 0 32)) (acc '()))
         (if (< (string-length s) 4)
             (reverse (if (string-null? s) acc (cons s acc)))
             (loop (substring s 4) (cons (substring s 0 4) acc))))
       ":")))

  ;; ============================================================
  ;; Keyring Operations
  ;; ============================================================

  (define (keyring-list)
    "List all keys in keyring"
    (keyring-init)
    (let* ((files (directory (keyring-path)))
           (pub-files (filter (lambda (f) (string-suffix? ".pub" f)) files))
           (names (map (lambda (f) (pathname-strip-extension f)) pub-files)))
      (if (null? names)
          (begin
            (print "Keyring is empty.")
            '())
          (begin
            (print "")
            (print "╭───────────────────────────────────────────────────────╮")
            (print "│                    keyring                            │")
            (print "├───────────────────────────────────────────────────────┤")
            (for-each
             (lambda (name)
               (let ((keys (read-key-files name)))
                 (when keys
                   (let* ((pub (car keys))
                          (meta (caddr keys))
                          (created (assq 'created meta))
                          (fp (fingerprint pub)))
                     (printf "│ ~a~a│~%"
                             name
                             (make-string (max 0 (- 53 (string-length name))) #\space))
                     (printf "│   ~a │~%"
                             (substring fp 0 (min 50 (string-length fp))))
                     (when created
                       (printf "│   Created: ~a~a│~%"
                               (seconds->string (cadr created))
                               (make-string 20 #\space)))))))
             (sort names string<?))
            (print "╰───────────────────────────────────────────────────────╯")
            (print "")
            names))))

  (define (keyring-generate name)
    "Generate new keypair with name"
    (keyring-init)
    (if (key-exists? name)
        (begin
          (print "Key already exists: " name)
          #f)
        (let ((keys (ed25519-keypair)))
          (let ((pub (car keys))
                (priv (cadr keys)))
            (write-key-files name pub priv)
            (print "")
            (print "Generated key: " name)
            (print "  Fingerprint: " (fingerprint pub))
            (print "  Public key:  " (key-path name "pub"))
            (print "  Private key: " (key-path name "key") " (chmod 600)")
            (print "")
            name))))

  (define (keyring-delete name)
    "Delete keypair from keyring"
    (if (not (key-exists? name))
        (begin
          (print "Key not found: " name)
          #f)
        (begin
          (safe-delete-file (key-path name "pub"))
          (safe-delete-file (key-path name "key"))
          (safe-delete-file (key-path name "meta"))
          (print "Deleted key: " name)
          #t)))

  (define (keyring-rename old-name new-name)
    "Rename a key"
    (cond
     ((not (key-exists? old-name))
      (print "Key not found: " old-name)
      #f)
     ((key-exists? new-name)
      (print "Key already exists: " new-name)
      #f)
     (else
      (rename-file (key-path old-name "pub") (key-path new-name "pub"))
      (rename-file (key-path old-name "key") (key-path new-name "key"))
      (when (file-exists? (key-path old-name "meta"))
        (rename-file (key-path old-name "meta") (key-path new-name "meta")))
      (print "Renamed: " old-name " → " new-name)
      #t)))

  (define (keyring-import name pub-hex #!optional priv-hex)
    "Import key from hex strings"
    (keyring-init)
    (if (key-exists? name)
        (begin
          (print "Key already exists: " name)
          #f)
        (let ((pub (hex->blob pub-hex))
              (priv (if priv-hex (hex->blob priv-hex) #f)))
          (with-output-to-file (key-path name "pub")
            (lambda () (display pub-hex)))
          (when priv
            (with-output-to-file (key-path name "key")
              (lambda () (display priv-hex)))
            (set-file-permissions! (key-path name "key") #o600))
          (with-output-to-file (key-path name "meta")
            (lambda ()
              (write `((name ,name)
                       (algorithm ed25519)
                       (created ,(current-seconds))
                       (imported #t)
                       (fingerprint ,(fingerprint pub))))))
          (print "Imported key: " name)
          name)))

  (define (keyring-export name #!optional (include-private #f))
    "Export key as hex (public only by default)"
    (let ((keys (read-key-files name)))
      (if (not keys)
          (begin
            (print "Key not found: " name)
            #f)
          (let ((pub (car keys))
                (priv (cadr keys)))
            (print "")
            (print "Public key (" name "):")
            (print (blob->hex pub))
            (when include-private
              (print "")
              (print "Private key (" name ") [SENSITIVE]:")
              (print (blob->hex priv)))
            (print "")
            (if include-private
                (list (blob->hex pub) (blob->hex priv))
                (blob->hex pub))))))

  ;; ============================================================
  ;; Key Lookup
  ;; ============================================================

  (define (key-exists? name)
    "Check if key exists"
    (file-exists? (key-path name "pub")))

  (define (key-by-name name)
    "Get key by name, returns (public private) or #f"
    (let ((keys (read-key-files name)))
      (if keys
          (list (car keys) (cadr keys))
          #f)))

  (define (key-by-fingerprint fp)
    "Find key by fingerprint prefix"
    (keyring-init)
    (let* ((files (directory (keyring-path)))
           (pub-files (filter (lambda (f) (string-suffix? ".pub" f)) files))
           (names (map pathname-strip-extension pub-files)))
      (find
       (lambda (name)
         (let ((keys (read-key-files name)))
           (and keys
                (string-prefix? fp (fingerprint (car keys))))))
       names)))

  ;; ============================================================
  ;; Key Info
  ;; ============================================================

  (define (key-info name)
    "Get detailed key info"
    (let ((keys (read-key-files name)))
      (if (not keys)
          #f
          (let* ((pub (car keys))
                 (priv (cadr keys))
                 (meta (caddr keys))
                 (created (assq 'created meta)))
            `((name . ,name)
              (fingerprint . ,(fingerprint pub))
              (algorithm . ed25519)
              (public-key-size . ,(blob-size pub))
              (private-key-size . ,(blob-size priv))
              (created . ,(and created (cadr created)))
              (has-private . #t))))))

  (define (key-public name)
    "Get public key blob"
    (let ((keys (key-by-name name)))
      (and keys (car keys))))

  (define (key-private name)
    "Get private key blob"
    (let ((keys (key-by-name name)))
      (and keys (cadr keys))))

  (define (key-fingerprint name)
    "Get key fingerprint"
    (let ((pub (key-public name)))
      (and pub (fingerprint pub))))

  (define (key-created name)
    "Get key creation time"
    (let ((info (key-info name)))
      (and info (cdr (assq 'created info)))))

  ;; ============================================================
  ;; Display
  ;; ============================================================

  (define (display-key name)
    "Display key details"
    (let ((info (key-info name)))
      (if (not info)
          (print "Key not found: " name)
          (begin
            (print "")
            (print "╭───────────────────────────────────────────────────────╮")
            (printf "│ key: ~a~a│~%"
                    name (make-string (max 0 (- 49 (string-length name))) #\space))
            (print "├───────────────────────────────────────────────────────┤")
            (printf "│ Fingerprint: ~a~%" (cdr (assq 'fingerprint info)))
            (printf "│ Algorithm:   ~a~%" (cdr (assq 'algorithm info)))
            (let ((created (cdr (assq 'created info))))
              (when created
                (printf "│ Created:     ~a~%" (seconds->string created))))
            (printf "│ Public:      ~a bytes~%" (cdr (assq 'public-key-size info)))
            (printf "│ Private:     ~a bytes~%" (cdr (assq 'private-key-size info)))
            (print "╰───────────────────────────────────────────────────────╯")
            (print "")))))

  (define (display-keyring)
    "Display full keyring"
    (keyring-list))

  ;; ============================================================
  ;; Helpers
  ;; ============================================================

  (define (safe-delete-file path)
    "Delete file if exists"
    (when (file-exists? path)
      (delete-file path)))

) ; end module keyring
