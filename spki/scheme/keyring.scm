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
          crypto-ffi
          pq-crypto)

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

  (define (write-key-files name public-key private-key #!optional (algorithm 'ed25519))
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
          (let* ((pub (hex->blob (with-input-from-file pub-path read-line)))
                 (priv (hex->blob (with-input-from-file key-path* read-line)))
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
                      (let ((pq-pub (hex->blob (with-input-from-file pq-pub-path read-line)))
                            (pq-priv (hex->blob (with-input-from-file pq-key-path read-line))))
                        (list `((ed25519 ,pub ,priv) (ml-dsa ,pq-pub ,pq-priv)) meta))
                      #f))
                (list pub priv meta)))
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

  (define (keyring-generate name #!optional (algorithm 'ed25519))
    "Generate new keypair with name and algorithm.
     Algorithms: ed25519 (default), ml-dsa-65, sphincs+, hybrid
     Hybrid creates both Ed25519 and ML-DSA keys for transition security."
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
           (receive (pub priv) (ml-dsa-keygen)
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
           (receive (pub priv) (sphincs+-keygen)
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
             (receive (pq-pub pq-priv) (ml-dsa-keygen)
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
           (error 'keyring-generate "Unknown algorithm" algorithm)))))

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
          (let* ((meta (if (eq? (length keys) 2) (cadr keys) (caddr keys)))
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
                    (ed25519-public-size . ,(blob-size ed-pub))
                    (ml-dsa-public-size . ,(blob-size pq-pub))
                    (created . ,(and created (cadr created)))
                    (has-private . #t)
                    (quantum-resistant . #t)))
                ;; Single-algorithm key info
                (let ((pub (car keys))
                      (priv (cadr keys)))
                  `((name . ,name)
                    (fingerprint . ,(fingerprint pub))
                    (algorithm . ,alg)
                    (public-key-size . ,(blob-size pub))
                    (private-key-size . ,(blob-size priv))
                    (created . ,(and created (cadr created)))
                    (has-private . #t)
                    (quantum-resistant . ,(memq alg '(ml-dsa-65 sphincs+ hybrid))))))))))

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
      (let ((msg-blob (if (blob? message) message (string->blob message))))
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
      (let ((msg-blob (if (blob? message) message (string->blob message))))
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
            (print "╭───────────────────────────────────────────────────────╮")
            (printf "│ key: ~a~a│~%"
                    name (make-string (max 0 (- 49 (string-length name))) #\space))
            (print "├───────────────────────────────────────────────────────┤")
            (printf "│ Fingerprint: ~a~%" (cdr (assq 'fingerprint info)))
            (printf "│ Algorithm:   ~a~a~%"
                    alg
                    (if (and qr (cdr qr)) " (quantum-resistant)" ""))
            (let ((created (cdr (assq 'created info))))
              (when created
                (printf "│ Created:     ~a~%" (seconds->string created))))
            (if (eq? alg 'hybrid)
                (begin
                  (printf "│ Ed25519:     ~a bytes~%" (cdr (assq 'ed25519-public-size info)))
                  (printf "│ ML-DSA:      ~a bytes~%" (cdr (assq 'ml-dsa-public-size info))))
                (begin
                  (printf "│ Public:      ~a bytes~%" (cdr (assq 'public-key-size info)))
                  (printf "│ Private:     ~a bytes~%" (cdr (assq 'private-key-size info)))))
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
