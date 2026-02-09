;;; keyring.sls - Key Management for the Soup
;;; Chez Scheme Port
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
;;; Changes: module -> library, blob/u8vector -> bytevector compat,
;;;          (chicken file) -> Chez file ops, SRFI-9 -> R6RS records,
;;;          #!optional/#!key -> get-opt/get-key, receive -> let-values,
;;;          seconds->string -> local, pathname-strip-extension -> local.

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

    ;; Signing/verification (algorithm-aware)
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
          (rnrs mutable-strings)
          (only (chezscheme)
                sort format printf
                time-second current-time
                make-time time-utc->date
                date-year date-month date-day
                date-hour date-minute date-second
                file-exists? delete-file rename-file
                directory-list mkdir
                foreign-procedure
                with-output-to-file with-input-from-file
                with-output-to-string
                current-input-port get-line read write)
          (cyberspace chicken-compatibility blob)
          (cyberspace chicken-compatibility chicken)
          (cyberspace crypto-ffi)
          (cyberspace pq-crypto))

  ;; ============================================================
  ;; SRFI-1 helpers
  ;; ============================================================

  (define (find pred lst)
    (let loop ((rest lst))
      (cond
       ((null? rest) #f)
       ((pred (car rest)) (car rest))
       (else (loop (cdr rest))))))

  ;; ============================================================
  ;; String helpers
  ;; ============================================================

  (define (string-suffix? suffix str)
    (let ((slen (string-length suffix))
          (len (string-length str)))
      (and (>= len slen)
           (string=? suffix (substring str (- len slen) len)))))

  (define (string-prefix? prefix str)
    (let ((plen (string-length prefix))
          (len (string-length str)))
      (and (>= len plen)
           (string=? prefix (substring str 0 plen)))))

  (define (string-null? s)
    (= (string-length s) 0))

  (define (string-join lst sep)
    (cond
     ((null? lst) "")
     ((null? (cdr lst)) (car lst))
     (else
      (let loop ((rest (cdr lst)) (acc (car lst)))
        (if (null? rest) acc
            (loop (cdr rest)
                  (string-append acc sep (car rest))))))))

  ;; ============================================================
  ;; File system helpers
  ;; ============================================================

  (define (directory-exists? path)
    (file-exists? path))

  (define (create-directory path recursive?)
    ;; Chez's mkdir doesn't have recursive flag; create parents manually
    (when recursive?
      (let ((parts (string-split-path path)))
        (let loop ((i 1))
          (when (<= i (length parts))
            (let ((partial (string-join-path (list-head parts i))))
              (unless (file-exists? partial)
                (mkdir partial))
              (loop (+ i 1)))))))
    (unless (file-exists? path)
      (mkdir path)))

  (define (string-split-path path)
    "Split path on / separators"
    (let loop ((i 0) (start 0) (acc '()))
      (cond
       ((= i (string-length path))
        (reverse (if (= start i) acc
                     (cons (substring path start i) acc))))
       ((char=? (string-ref path i) #\/)
        (loop (+ i 1) (+ i 1)
              (if (= start i) acc
                  (cons (substring path start i) acc))))
       (else (loop (+ i 1) start acc)))))

  (define (string-join-path parts)
    (string-join parts "/"))

  (define (list-head lst n)
    (let loop ((i 0) (rest lst) (acc '()))
      (if (or (= i n) (null? rest))
          (reverse acc)
          (loop (+ i 1) (cdr rest) (cons (car rest) acc)))))

  (define chmod-raw (foreign-procedure "chmod" (string int) int))

  (define (set-file-permissions! path mode)
    (chmod-raw path mode))

  (define (pathname-strip-extension path)
    "Strip the last extension from a filename.
     foo.pub -> foo, foo.pq.pub -> foo.pq"
    (let ((dot-pos (let loop ((i (- (string-length path) 1)))
                     (cond
                      ((< i 0) #f)
                      ((char=? (string-ref path i) #\.) i)
                      ((char=? (string-ref path i) #\/) #f)
                      (else (loop (- i 1)))))))
      (if dot-pos
          (substring path 0 dot-pos)
          path)))

  (define (seconds->string secs)
    "Convert epoch seconds to a human-readable string.
     Returns ISO-ish format: YYYY-MM-DD HH:MM:SS"
    ;; Use Chez's date facilities
    (let ((d (time-utc->date (make-time 'time-utc 0 secs))))
      (format "~4d-~2,'0d-~2,'0d ~2,'0d:~2,'0d:~2,'0d"
              (date-year d) (date-month d) (date-day d)
              (date-hour d) (date-minute d) (date-second d))))

  (define (current-seconds)
    (time-second (current-time)))

  (define (read-line-from-file path)
    "Read first line from a file"
    (with-input-from-file path
      (lambda ()
        (let ((line (get-line (current-input-port))))
          (if (eof-object? line) "" line)))))

  ;; ============================================================
  ;; Paths
  ;; ============================================================

  (define (keyring-path)
    ".vault/keys")

  (define (key-path name ext)
    (string-append (keyring-path) "/" name "." ext))

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
  ;; Supported Algorithms
  ;; ============================================================
  ;; ed25519      - Classical, fast, small (32B pk, 64B sig)
  ;; ml-dsa-65    - Post-quantum lattice (1952B pk, 3309B sig) - FIPS 204
  ;; sphincs+     - Post-quantum hash-based (64B pk, ~30KB sig) - FIPS 205
  ;; hybrid       - Ed25519 + ML-DSA (both signatures required)

  (define (supported-algorithms)
    '(ed25519 ml-dsa-65 sphincs+ hybrid))

  (define (algorithm-valid? alg)
    (memq alg (supported-algorithms)))

  ;; ============================================================
  ;; Hex Conversion
  ;; ============================================================

  (define (blob->hex bv)
    "Convert bytevector to hex string"
    (let* ((size (bytevector-length bv))
           (result (make-string (* 2 size))))
      (do ((i 0 (+ i 1)))
          ((>= i size) result)
        (let* ((byte (bytevector-u8-ref bv i))
               (hi (div byte 16))
               (lo (mod byte 16)))
          (string-set! result (* i 2) (string-ref "0123456789abcdef" hi))
          (string-set! result (+ (* i 2) 1) (string-ref "0123456789abcdef" lo))))))

  (define (hex->blob hex)
    "Convert hex string to bytevector"
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
    "Generate fingerprint from public key"
    (let* ((hash (sha512-hash public-key))
           (hex (blob->hex hash)))
      ;; First 32 chars in groups of 4
      (string-join
       (let loop ((s (substring hex 0 32)) (acc '()))
         (if (< (string-length s) 4)
             (reverse (if (string-null? s) acc (cons s acc)))
             (loop (substring s 4 (string-length s))
                   (cons (substring s 0 4) acc))))
       ":")))

  ;; ============================================================
  ;; Key Storage Format
  ;; ============================================================
  ;; Keys stored as:
  ;;   .vault/keys/NAME.pub  - public key (hex, size varies by algorithm)
  ;;   .vault/keys/NAME.key  - private key (hex, chmod 600)
  ;;   .vault/keys/NAME.meta - metadata (s-expression with algorithm)
  ;;
  ;; For hybrid keys:
  ;;   .vault/keys/NAME.pub      - Ed25519 public key
  ;;   .vault/keys/NAME.key      - Ed25519 private key
  ;;   .vault/keys/NAME.pq.pub   - ML-DSA public key
  ;;   .vault/keys/NAME.pq.key   - ML-DSA private key

  (define (write-key-files name public-key private-key . rest)
    "Write key files to keyring"
    (let ((algorithm (get-opt rest 0 'ed25519))
          (pub-path (key-path name "pub"))
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
                   (algorithm ,algorithm)
                   (created ,(current-seconds))
                   (fingerprint ,(fingerprint public-key))))))))

  (define (write-hybrid-key-files name ed-pub ed-priv pq-pub pq-priv)
    "Write hybrid key files (Ed25519 + ML-DSA)"
    ;; Write Ed25519 keys
    (write-key-files name ed-pub ed-priv 'hybrid)
    ;; Write PQ keys
    (let ((pq-pub-path (key-path name "pq.pub"))
          (pq-key-path (key-path name "pq.key")))
      (with-output-to-file pq-pub-path
        (lambda () (display (blob->hex pq-pub))))
      (with-output-to-file pq-key-path
        (lambda () (display (blob->hex pq-priv))))
      (set-file-permissions! pq-key-path #o600)))

  (define (read-key-files name)
    "Read key files from keyring, returns (public private metadata) or #f
     For hybrid keys, public/private are lists: ((ed25519 pub priv) (ml-dsa pub priv))"
    (let ((pub-path (key-path name "pub"))
          (key-path* (key-path name "key"))
          (meta-path (key-path name "meta")))
      (if (and (file-exists? pub-path)
               (file-exists? key-path*))
          (let* ((pub (hex->blob (read-line-from-file pub-path)))
                 (priv (hex->blob (read-line-from-file key-path*)))
                 (meta (if (file-exists? meta-path)
                           (with-input-from-file meta-path read)
                           '()))
                 (alg (let ((a (assq 'algorithm meta)))
                        (if a (cadr a) 'ed25519))))
            ;; For hybrid, also read PQ keys
            (if (eq? alg 'hybrid)
                (let ((pq-pub-path (key-path name "pq.pub"))
                      (pq-key-path (key-path name "pq.key")))
                  (if (and (file-exists? pq-pub-path)
                           (file-exists? pq-key-path))
                      (let ((pq-pub (hex->blob (read-line-from-file pq-pub-path)))
                            (pq-priv (hex->blob (read-line-from-file pq-key-path))))
                        (list `((ed25519 ,pub ,priv) (ml-dsa ,pq-pub ,pq-priv)) meta))
                      #f))
                (list pub priv meta)))
          #f)))

  ;; ============================================================
  ;; Keyring Operations
  ;; ============================================================

  (define (keyring-list)
    "List all keys in keyring"
    (keyring-init)
    (let* ((files (directory-list (keyring-path)))
           (pub-files (filter (lambda (f) (string-suffix? ".pub" f)) files))
           ;; Exclude .pq.pub files (hybrid PQ keys listed with their parent)
           (pub-files (filter (lambda (f) (not (string-suffix? ".pq.pub" f))) pub-files))
           (names (map pathname-strip-extension pub-files)))
      (if (null? names)
          (begin
            (print "Keyring is empty.")
            '())
          (begin
            (print "")
            (print "+-------------------------------------------------------+")
            (print "|                    keyring                            |")
            (print "+-------------------------------------------------------+")
            (for-each
             (lambda (name)
               (let ((keys (read-key-files name)))
                 (when keys
                   (let* ((pub (car keys))
                          (meta (if (= (length keys) 3) (caddr keys) (cadr keys)))
                          (alg-entry (assq 'algorithm meta))
                          (alg (if alg-entry (cadr alg-entry) 'ed25519))
                          (fp-str (if (eq? alg 'hybrid)
                                      ;; Hybrid: pub is key-data list
                                      (fingerprint (cadr (assq 'ed25519 pub)))
                                      (fingerprint pub)))
                          (created (assq 'created meta)))
                     (printf "| ~a~a|~%"
                             name
                             (make-string (max 0 (- 53 (string-length name))) #\space))
                     (printf "|   ~a |~%"
                             (substring fp-str 0 (min 50 (string-length fp-str))))
                     (when created
                       (printf "|   Created: ~a~a|~%"
                               (seconds->string (cadr created))
                               (make-string 20 #\space)))))))
             (sort string<? names))
            (print "+-------------------------------------------------------+")
            (print "")
            names))))

  (define (keyring-generate name . rest)
    "Generate new keypair with name and algorithm.
     Algorithms: ed25519 (default), ml-dsa-65, sphincs+, hybrid
     Hybrid creates both Ed25519 and ML-DSA keys for transition security."
    (let ((algorithm (get-opt rest 0 'ed25519)))
      (keyring-init)
      (unless (algorithm-valid? algorithm)
        (error 'keyring-generate "Unknown algorithm" algorithm))
      (if (key-exists? name)
          (begin
            (print "Key already exists: " name)
            #f)
          (case algorithm
            ;; Classical Ed25519
            ((ed25519)
             (let ((keys (ed25519-keypair)))
               (let ((pub (car keys))
                     (priv (cadr keys)))
                 (write-key-files name pub priv 'ed25519)
                 (print "")
                 (print "Generated Ed25519 key: " name)
                 (print "  Fingerprint: " (fingerprint pub))
                 (print "  Algorithm:   ed25519 (classical)")
                 (print "  Public:      " (key-path name "pub") " (32 bytes)")
                 (print "  Private:     " (key-path name "key") " (chmod 600)")
                 (print "")
                 name)))

            ;; Post-quantum ML-DSA-65 (lattice-based)
            ((ml-dsa-65 ml-dsa)
             (let-values (((pub priv) (ml-dsa-keygen)))
               (write-key-files name pub priv 'ml-dsa-65)
               (print "")
               (print "Generated ML-DSA-65 key: " name)
               (print "  Fingerprint: " (fingerprint pub))
               (print "  Algorithm:   ml-dsa-65 (post-quantum, FIPS 204)")
               (print "  Public:      " (key-path name "pub") " (1952 bytes)")
               (print "  Private:     " (key-path name "key") " (chmod 600)")
               (print "  Signature:   3309 bytes")
               (print "")
               name))

            ;; Post-quantum SPHINCS+ (hash-based, conservative)
            ((sphincs+ sphincs+-shake-256s)
             (let-values (((pub priv) (sphincs+-keygen)))
               (write-key-files name pub priv 'sphincs+)
               (print "")
               (print "Generated SPHINCS+ key: " name)
               (print "  Fingerprint: " (fingerprint pub))
               (print "  Algorithm:   sphincs+-shake-256s (post-quantum, FIPS 205)")
               (print "  Public:      " (key-path name "pub") " (64 bytes)")
               (print "  Private:     " (key-path name "key") " (chmod 600)")
               (print "  Signature:   ~30KB (conservative, hash-based)")
               (print "")
               name))

            ;; Hybrid: Ed25519 + ML-DSA (transition security)
            ((hybrid)
             (let ((ed-keys (ed25519-keypair)))
               (let-values (((pq-pub pq-priv) (ml-dsa-keygen)))
                 (let ((ed-pub (car ed-keys))
                       (ed-priv (cadr ed-keys)))
                   (write-hybrid-key-files name ed-pub ed-priv pq-pub pq-priv)
                   (print "")
                   (print "Generated HYBRID key: " name)
                   (print "  Fingerprint: " (fingerprint ed-pub))
                   (print "  Algorithm:   hybrid (Ed25519 + ML-DSA-65)")
                   (print "  Classical:   " (key-path name "pub") " (Ed25519)")
                   (print "  Post-quantum:" (key-path name "pq.pub") " (ML-DSA)")
                   (print "  Both signatures required for verification")
                   (print "  Survives Q-Day: YES")
                   (print "")
                   name))))

            (else
             (error 'keyring-generate "Unknown algorithm" algorithm))))))

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
          ;; Also delete hybrid PQ keys if present
          (safe-delete-file (key-path name "pq.pub"))
          (safe-delete-file (key-path name "pq.key"))
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
      ;; Also rename hybrid PQ keys if present
      (when (file-exists? (key-path old-name "pq.pub"))
        (rename-file (key-path old-name "pq.pub") (key-path new-name "pq.pub")))
      (when (file-exists? (key-path old-name "pq.key"))
        (rename-file (key-path old-name "pq.key") (key-path new-name "pq.key")))
      (print "Renamed: " old-name " -> " new-name)
      #t)))

  (define (keyring-import name pub-hex . rest)
    "Import key from hex strings"
    (let ((priv-hex (get-opt rest 0 #f)))
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
            name))))

  (define (keyring-export name . rest)
    "Export key as hex (public only by default)"
    (let ((include-private (get-opt rest 0 #f)))
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
                  (blob->hex pub)))))))

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
    (let* ((files (directory-list (keyring-path)))
           (pub-files (filter (lambda (f) (string-suffix? ".pub" f)) files))
           (pub-files (filter (lambda (f) (not (string-suffix? ".pq.pub" f))) pub-files))
           (names (map pathname-strip-extension pub-files)))
      (find
       (lambda (name)
         (let ((keys (read-key-files name)))
           (and keys
                (let ((pub (car keys)))
                  (string-prefix? fp
                    (if (and (pair? pub) (not (bytevector? pub)))
                        ;; Hybrid: pub is key-data list
                        (fingerprint (cadr (assq 'ed25519 pub)))
                        (fingerprint pub)))))))
       names)))

  ;; ============================================================
  ;; Key Info
  ;; ============================================================

  (define (key-info name)
    "Get detailed key info"
    (let ((keys (read-key-files name)))
      (if (not keys)
          #f
          (let* ((meta (if (= (length keys) 2) (cadr keys) (caddr keys)))
                 (alg-entry (assq 'algorithm meta))
                 (alg (if alg-entry (cadr alg-entry) 'ed25519))
                 (created (assq 'created meta)))
            (if (eq? alg 'hybrid)
                ;; Hybrid key info
                (let* ((key-data (car keys))
                       (ed-keys (assq 'ed25519 key-data))
                       (pq-keys (assq 'ml-dsa key-data))
                       (ed-pub (cadr ed-keys))
                       (pq-pub (cadr pq-keys)))
                  `((name . ,name)
                    (fingerprint . ,(fingerprint ed-pub))
                    (algorithm . hybrid)
                    (ed25519-public-size . ,(bytevector-length ed-pub))
                    (ml-dsa-public-size . ,(bytevector-length pq-pub))
                    (created . ,(and created (cadr created)))
                    (has-private . #t)
                    (quantum-resistant . #t)))
                ;; Single-algorithm key info
                (let ((pub (car keys))
                      (priv (cadr keys)))
                  `((name . ,name)
                    (fingerprint . ,(fingerprint pub))
                    (algorithm . ,alg)
                    (public-key-size . ,(bytevector-length pub))
                    (private-key-size . ,(bytevector-length priv))
                    (created . ,(and created (cadr created)))
                    (has-private . #t)
                    (quantum-resistant . ,(and (memq alg '(ml-dsa-65 sphincs+ hybrid)) #t)))))))))

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

  (define (key-algorithm name)
    "Get key algorithm"
    (let ((info (key-info name)))
      (and info (cdr (assq 'algorithm info)))))

  ;; ============================================================
  ;; Algorithm-Aware Signing and Verification
  ;; ============================================================

  (define (key-sign name message)
    "Sign message with named key, dispatching by algorithm.
     Returns signature blob(s) appropriate for the algorithm.
     For hybrid: returns (hybrid-signature (ed25519 sig) (ml-dsa sig))"
    (let* ((info (key-info name))
           (alg (and info (cdr (assq 'algorithm info))))
           (keys (read-key-files name)))
      (unless info (error 'key-sign "Key not found" name))
      (let ((msg-blob (if (bytevector? message) message (string->utf8 message))))
        (case alg
          ((ed25519)
           (let ((priv (cadr keys)))
             (ed25519-sign priv msg-blob)))

          ((ml-dsa-65)
           (let ((priv (cadr keys)))
             (ml-dsa-sign msg-blob priv)))

          ((sphincs+)
           (let ((priv (cadr keys)))
             (sphincs+-sign msg-blob priv)))

          ((hybrid)
           (let* ((key-data (car keys))
                  (ed-keys (assq 'ed25519 key-data))
                  (pq-keys (assq 'ml-dsa key-data))
                  (ed-priv (caddr ed-keys))
                  (pq-priv (caddr pq-keys)))
             `(hybrid-signature
               (ed25519 ,(ed25519-sign ed-priv msg-blob))
               (ml-dsa ,(ml-dsa-sign msg-blob pq-priv)))))

          (else
           (error 'key-sign "Unknown algorithm" alg))))))

  (define (key-verify name message signature)
    "Verify signature with named key, dispatching by algorithm.
     For hybrid: signature must be (hybrid-signature ...) and BOTH must verify."
    (let* ((info (key-info name))
           (alg (and info (cdr (assq 'algorithm info))))
           (keys (read-key-files name)))
      (unless info (error 'key-verify "Key not found" name))
      (let ((msg-blob (if (bytevector? message) message (string->utf8 message))))
        (case alg
          ((ed25519)
           (let ((pub (car keys)))
             (ed25519-verify pub msg-blob signature)))

          ((ml-dsa-65)
           (let ((pub (car keys)))
             (ml-dsa-verify msg-blob signature pub)))

          ((sphincs+)
           (let ((pub (car keys)))
             (sphincs+-verify msg-blob signature pub)))

          ((hybrid)
           ;; Both signatures must verify
           (and (pair? signature)
                (eq? (car signature) 'hybrid-signature)
                (let* ((key-data (car keys))
                       (ed-keys (assq 'ed25519 key-data))
                       (pq-keys (assq 'ml-dsa key-data))
                       (ed-pub (cadr ed-keys))
                       (pq-pub (cadr pq-keys))
                       (ed-sig (cadr (assq 'ed25519 (cdr signature))))
                       (pq-sig (cadr (assq 'ml-dsa (cdr signature)))))
                  (and ed-sig pq-sig
                       (ed25519-verify ed-pub msg-blob ed-sig)
                       (ml-dsa-verify msg-blob pq-sig pq-pub)))))

          (else
           (error 'key-verify "Unknown algorithm" alg))))))

  ;; ============================================================
  ;; Display
  ;; ============================================================

  (define (display-key name)
    "Display key details"
    (let ((info (key-info name)))
      (if (not info)
          (print "Key not found: " name)
          (let ((alg (cdr (assq 'algorithm info)))
                (qr (assq 'quantum-resistant info)))
            (print "")
            (print "+-------------------------------------------------------+")
            (printf "| key: ~a~a|~%"
                    name (make-string (max 0 (- 49 (string-length name))) #\space))
            (print "+-------------------------------------------------------+")
            (printf "| Fingerprint: ~a~%" (cdr (assq 'fingerprint info)))
            (printf "| Algorithm:   ~a~a~%"
                    alg
                    (if (and qr (cdr qr)) " (quantum-resistant)" ""))
            (let ((created (cdr (assq 'created info))))
              (when created
                (printf "| Created:     ~a~%" (seconds->string created))))
            (if (eq? alg 'hybrid)
                (begin
                  (printf "| Ed25519:     ~a bytes~%" (cdr (assq 'ed25519-public-size info)))
                  (printf "| ML-DSA:      ~a bytes~%" (cdr (assq 'ml-dsa-public-size info))))
                (begin
                  (printf "| Public:      ~a bytes~%" (cdr (assq 'public-key-size info)))
                  (printf "| Private:     ~a bytes~%" (cdr (assq 'private-key-size info)))))
            (print "+-------------------------------------------------------+")
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

) ;; end library
