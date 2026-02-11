;;; SPKI Scheme - Key Management for the Soup
;;; Library of Cyberspace - Chez Port
;;;
;;; "Not your keys, not your crypto" - Bitcoin wisdom
;;;
;;; Provides:
;;; - Named keypair generation and storage
;;; - Key lookup by name or fingerprint
;;; - Key listing and inspection
;;; - Keyring persistence (.vault/keys/)
;;;
;;; Ported from Chicken's keyring.scm.
;;; Changes: module -> library, blob -> bytevector, #!optional -> get-opt,
;;;          pq-crypto deferred (ed25519 only), file ops via chezscheme,
;;;          string-set! -> functional hex, sort args reversed.

(library (cyberspace keyring)
  (export
    ;; Keyring operations
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
    key-algorithm

    ;; Signing/verification
    key-sign
    key-verify

    ;; Supported algorithms
    supported-algorithms

    ;; Display
    display-key
    display-keyring

    ;; Paths
    keyring-path
    key-path)

  (import (rnrs)
          (only (chezscheme)
                printf format
                directory-list mkdir
                current-time time-second make-time
                sort system
                date->time-utc time-utc->date
                date-year date-month date-day
                date-hour date-minute date-second)
          (cyberspace crypto-ffi)
          (cyberspace chicken-compatibility chicken)
          (cyberspace chicken-compatibility blob))

  ;; ============================================================
  ;; String helpers (inline SRFI-13 replacements)
  ;; ============================================================

  (define (string-suffix? suffix str)
    (let ((slen (string-length str))
          (xlen (string-length suffix)))
      (and (>= slen xlen)
           (string=? (substring str (- slen xlen) slen) suffix))))

  (define (string-prefix? prefix str)
    (let ((slen (string-length str))
          (plen (string-length prefix)))
      (and (>= slen plen)
           (string=? (substring str 0 plen) prefix))))

  (define (string-null? s) (= (string-length s) 0))

  ;; ============================================================
  ;; Pathname helpers (inline Chicken pathname replacements)
  ;; ============================================================

  (define (make-pathname dir name ext)
    ;; Construct dir/name.ext
    (string-append dir "/" name "." ext))

  (define (pathname-strip-extension filename)
    ;; Remove .ext from filename
    (let loop ((i (- (string-length filename) 1)))
      (cond
        ((< i 0) filename)
        ((char=? (string-ref filename i) #\.)
         (substring filename 0 i))
        (else (loop (- i 1))))))

  ;; ============================================================
  ;; Time helpers
  ;; ============================================================

  (define (current-seconds)
    (time-second (current-time 'time-utc)))

  (define (seconds->string secs)
    ;; Convert epoch seconds to human-readable string
    (let* ((t (make-time 'time-utc 0 secs))
           (d (time-utc->date t 0)))
      (format "~a-~2,'0d-~2,'0d ~2,'0d:~2,'0d:~2,'0d"
              (date-year d) (date-month d) (date-day d)
              (date-hour d) (date-minute d) (date-second d))))

  ;; ============================================================
  ;; Hex Conversion
  ;; ============================================================

  (define hex-chars "0123456789abcdef")

  (define (bytevector->hex bv)
    ;; Convert bytevector to hex string
    (let ((size (bytevector-length bv)))
      (let loop ((i 0) (acc '()))
        (if (>= i size)
            (apply string-append (reverse acc))
            (let* ((byte (bytevector-u8-ref bv i))
                   (hi (div byte 16))
                   (lo (mod byte 16)))
              (loop (+ i 1)
                    (cons (string (string-ref hex-chars hi)
                                  (string-ref hex-chars lo))
                          acc)))))))

  (define (hex->bytevector hex)
    ;; Convert hex string to bytevector
    (let* ((len (div (string-length hex) 2))
           (result (make-bytevector len)))
      (do ((i 0 (+ i 1)))
          ((>= i len) result)
        (let ((hi (hex-digit (string-ref hex (* i 2))))
              (lo (hex-digit (string-ref hex (+ (* i 2) 1)))))
          (bytevector-u8-set! result i (+ (* hi 16) lo))))))

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
    ;; Generate fingerprint from public key
    (let* ((hash (sha512-hash public-key))
           (hex (bytevector->hex hash)))
      ;; First 32 chars in groups of 4
      (string-join
       (let loop ((s (substring hex 0 32)) (acc '()))
         (if (< (string-length s) 4)
             (reverse (if (string-null? s) acc (cons s acc)))
             (loop (substring s 4 (string-length s))
                   (cons (substring s 0 4) acc))))
       ":")))

  (define (string-join lst sep)
    (cond
      ((null? lst) "")
      ((null? (cdr lst)) (car lst))
      (else
       (let loop ((rest (cdr lst)) (acc (car lst)))
         (if (null? rest)
             acc
             (loop (cdr rest)
                   (string-append acc sep (car rest))))))))

  ;; ============================================================
  ;; Paths
  ;; ============================================================

  (define (keyring-path)
    ".vault/keys")

  (define (key-path name ext)
    (make-pathname (keyring-path) name ext))

  ;; ============================================================
  ;; Filesystem helpers
  ;; ============================================================

  (define (directory-exists? path)
    (and (file-exists? path)
         (let ((r (system (string-append "test -d " path " 2>/dev/null"))))
           (= r 0))))

  (define (create-directory path recursive?)
    (if recursive?
        (system (string-append "mkdir -p " path))
        (mkdir path)))

  (define (set-file-permissions! path mode)
    ;; mode is octal, e.g. #o600
    (system (string-append "chmod " (number->string mode 8) " " path)))

  (define (safe-delete-file path)
    (when (file-exists? path)
      (delete-file path)))

  (define (rename-file old new)
    (system (string-append "mv " old " " new)))

  ;; ============================================================
  ;; Initialization
  ;; ============================================================

  (define (keyring-init)
    ;; Initialize keyring directory
    (let ((path (keyring-path)))
      (unless (directory-exists? path)
        (create-directory path #t)
        (print "Keyring initialized: " path))
      path))

  ;; ============================================================
  ;; Supported Algorithms
  ;; ============================================================
  ;; Chez port: ed25519 only. PQ algorithms deferred.

  (define (supported-algorithms)
    '(ed25519))

  (define (algorithm-valid? alg)
    (memq alg '(ed25519)))

  ;; ============================================================
  ;; Key Storage Format
  ;; ============================================================
  ;; Keys stored as:
  ;;   .vault/keys/NAME.pub  - public key (hex)
  ;;   .vault/keys/NAME.key  - private key (hex, chmod 600)
  ;;   .vault/keys/NAME.meta - metadata (s-expression)

  (define (write-key-files name public-key private-key . opts)
    ;; Write key files to keyring
    (let ((algorithm (get-opt opts 0 'ed25519))
          (pub-path (key-path name "pub"))
          (key-path* (key-path name "key"))
          (meta-path (key-path name "meta")))

      ;; Write public key
      (with-output-to-file pub-path
        (lambda () (display (bytevector->hex public-key))))

      ;; Write private key (restricted permissions)
      (with-output-to-file key-path*
        (lambda () (display (bytevector->hex private-key))))
      (set-file-permissions! key-path* #o600)

      ;; Write metadata
      (with-output-to-file meta-path
        (lambda ()
          (write `((name ,name)
                   (algorithm ,algorithm)
                   (created ,(current-seconds))
                   (fingerprint ,(fingerprint public-key))))))))

  (define (read-key-files name)
    ;; Read key files from keyring, returns (public private metadata) or #f
    (let ((pub-path (key-path name "pub"))
          (key-path* (key-path name "key"))
          (meta-path (key-path name "meta")))
      (if (and (file-exists? pub-path)
               (file-exists? key-path*))
          (let* ((pub-hex (with-input-from-file pub-path
                            (lambda () (get-line (current-input-port)))))
                 (priv-hex (with-input-from-file key-path*
                             (lambda () (get-line (current-input-port)))))
                 (pub (hex->bytevector pub-hex))
                 (priv (hex->bytevector priv-hex))
                 (meta (if (file-exists? meta-path)
                           (with-input-from-file meta-path read)
                           '())))
            (list pub priv meta))
          #f)))

  ;; ============================================================
  ;; Keyring Operations
  ;; ============================================================

  (define (keyring-list)
    ;; List all keys in keyring
    (keyring-init)
    (let* ((files (directory-list (keyring-path)))
           (pub-files (filter (lambda (f) (string-suffix? ".pub" f)) files))
           (names (map pathname-strip-extension pub-files)))
      (if (null? names)
          (begin
            (print "Keyring is empty.")
            '())
          (begin
            (print "")
            (print "+-------------------------------------------------------+")
            (print "|                    keyring                             |")
            (print "+-------------------------------------------------------+")
            (for-each
              (lambda (name)
                (let ((keys (read-key-files name)))
                  (when keys
                    (let* ((pub (car keys))
                           (meta (caddr keys))
                           (created (assq 'created meta))
                           (fp (fingerprint pub)))
                      (printf "| ~a~a|~%"
                              name
                              (make-string (max 0 (- 54 (string-length name))) #\space))
                      (printf "|   ~a |~%"
                              (substring fp 0 (min 50 (string-length fp))))
                      (when created
                        (printf "|   Created: ~a~a|~%"
                                (seconds->string (cadr created))
                                (make-string 20 #\space)))))))
              (sort string<? names))
            (print "+-------------------------------------------------------+")
            (print "")
            names))))

  (define (keyring-generate name . opts)
    ;; Generate new keypair. Ed25519 only in Chez port.
    (let ((algorithm (get-opt opts 0 'ed25519)))
      (keyring-init)
      (unless (algorithm-valid? algorithm)
        (error 'keyring-generate
               "Only ed25519 supported in Chez port (PQ deferred)"
               algorithm))
      (if (key-exists? name)
          (begin
            (print "Key already exists: " name)
            #f)
          (let* ((keys (ed25519-keypair))
                 (pub (car keys))
                 (priv (cadr keys)))
            (write-key-files name pub priv 'ed25519)
            (print "")
            (print "Generated Ed25519 key: " name)
            (print "  Fingerprint: " (fingerprint pub))
            (print "  Algorithm:   ed25519 (classical)")
            (print "  Public:      " (key-path name "pub") " (32 bytes)")
            (print "  Private:     " (key-path name "key") " (chmod 600)")
            (print "")
            name))))

  (define (keyring-delete name)
    ;; Delete keypair from keyring
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
    ;; Rename a key
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
       (print "Renamed: " old-name " -> " new-name)
       #t)))

  (define (keyring-import name pub-hex . opts)
    ;; Import key from hex strings
    (let ((priv-hex (get-opt opts 0 #f)))
      (keyring-init)
      (if (key-exists? name)
          (begin
            (print "Key already exists: " name)
            #f)
          (let ((pub (hex->bytevector pub-hex)))
            (with-output-to-file (key-path name "pub")
              (lambda () (display pub-hex)))
            (when priv-hex
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
            name))))

  (define (keyring-export name . opts)
    ;; Export key as hex (public only by default)
    (let ((include-private (get-opt opts 0 #f)))
      (let ((keys (read-key-files name)))
        (if (not keys)
            (begin
              (print "Key not found: " name)
              #f)
            (let ((pub (car keys))
                  (priv (cadr keys)))
              (print "")
              (print "Public key (" name "):")
              (print (bytevector->hex pub))
              (when include-private
                (print "")
                (print "Private key (" name ") [SENSITIVE]:")
                (print (bytevector->hex priv)))
              (print "")
              (if include-private
                  (list (bytevector->hex pub) (bytevector->hex priv))
                  (bytevector->hex pub)))))))

  ;; ============================================================
  ;; Key Lookup
  ;; ============================================================

  (define (key-exists? name)
    (file-exists? (key-path name "pub")))

  (define (key-by-name name)
    ;; Get key by name, returns (public private) or #f
    (let ((keys (read-key-files name)))
      (if keys
          (list (car keys) (cadr keys))
          #f)))

  (define (key-by-fingerprint fp)
    ;; Find key by fingerprint prefix
    (keyring-init)
    (let* ((files (directory-list (keyring-path)))
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
    ;; Get detailed key info
    (let ((keys (read-key-files name)))
      (if (not keys)
          #f
          (let* ((pub (car keys))
                 (priv (cadr keys))
                 (meta (caddr keys))
                 (alg-entry (assq 'algorithm meta))
                 (alg (if alg-entry (cadr alg-entry) 'ed25519))
                 (created (assq 'created meta)))
            `((name . ,name)
              (fingerprint . ,(fingerprint pub))
              (algorithm . ,alg)
              (public-key-size . ,(bytevector-length pub))
              (private-key-size . ,(bytevector-length priv))
              (created . ,(and created (cadr created)))
              (has-private . #t)
              (quantum-resistant . #f))))))

  (define (key-public name)
    ;; Get public key bytevector
    (let ((keys (key-by-name name)))
      (and keys (car keys))))

  (define (key-private name)
    ;; Get private key bytevector
    (let ((keys (key-by-name name)))
      (and keys (cadr keys))))

  (define (key-fingerprint name)
    ;; Get key fingerprint
    (let ((pub (key-public name)))
      (and pub (fingerprint pub))))

  (define (key-created name)
    ;; Get key creation time
    (let ((info (key-info name)))
      (and info (cdr (assq 'created info)))))

  (define (key-algorithm name)
    ;; Get key algorithm
    (let ((info (key-info name)))
      (and info (cdr (assq 'algorithm info)))))

  ;; ============================================================
  ;; Signing and Verification (Ed25519 only in Chez port)
  ;; ============================================================

  (define (key-sign name message)
    ;; Sign message with named key
    (let* ((info (key-info name))
           (keys (read-key-files name)))
      (unless info (error 'key-sign "Key not found" name))
      (let ((msg-bv (if (bytevector? message) message (string->utf8 message)))
            (priv (cadr keys)))
        (ed25519-sign priv msg-bv))))

  (define (key-verify name message signature)
    ;; Verify signature with named key
    (let* ((info (key-info name))
           (keys (read-key-files name)))
      (unless info (error 'key-verify "Key not found" name))
      (let ((msg-bv (if (bytevector? message) message (string->utf8 message)))
            (pub (car keys)))
        (ed25519-verify pub msg-bv signature))))

  ;; ============================================================
  ;; Display
  ;; ============================================================

  (define (display-key name)
    ;; Display key details
    (let ((info (key-info name)))
      (if (not info)
          (print "Key not found: " name)
          (let ((alg (cdr (assq 'algorithm info))))
            (print "")
            (print "+-------------------------------------------------------+")
            (printf "| key: ~a~a|~%"
                    name (make-string (max 0 (- 50 (string-length name))) #\space))
            (print "+-------------------------------------------------------+")
            (printf "| Fingerprint: ~a~%" (cdr (assq 'fingerprint info)))
            (printf "| Algorithm:   ~a~%" alg)
            (let ((created (cdr (assq 'created info))))
              (when created
                (printf "| Created:     ~a~%" (seconds->string created))))
            (printf "| Public:      ~a bytes~%" (cdr (assq 'public-key-size info)))
            (printf "| Private:     ~a bytes~%" (cdr (assq 'private-key-size info)))
            (print "+-------------------------------------------------------+")
            (print "")))))

  (define (display-keyring)
    ;; Display full keyring
    (keyring-list))

) ;; end library
