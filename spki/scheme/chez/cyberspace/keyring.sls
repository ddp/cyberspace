;;; keyring.scm - Key Management for the Soup
;;; Library of Cyberspace - Chez Port
;;;
;;; "Not your keys, not your crypto" - Bitcoin wisdom
;;;
;;; Provides:
;;; - Named keypair generation and storage
;;; - Key lookup by name or fingerprint
;;; - Key listing and inspection
;;; - Keyring persistence (.vault/keys/)

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
          (only (chezscheme)
                printf format void
                with-input-from-file with-output-to-file
                current-time time-second
                directory-list
                file-exists? delete-file
                system
                make-parameter
                sort)
          (cyberspace chicken-compatibility chicken)
          (cyberspace chicken-compatibility hashtable)
          (cyberspace chicken-compatibility blob)
          (cyberspace crypto-ffi))

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
      (unless (file-exists? path)
        (system (string-append "mkdir -p " path))
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

  (define (bytevector->hex bv)
    "Convert bytevector to hex string"
    (let ((len (bytevector-length bv)))
      (let loop ((i 0) (acc '()))
        (if (= i len)
            (apply string-append (reverse acc))
            (let* ((byte (bytevector-u8-ref bv i))
                   (hi (quotient byte 16))
                   (lo (remainder byte 16)))
              (loop (+ i 1)
                    (cons (string
                            (string-ref "0123456789abcdef" hi)
                            (string-ref "0123456789abcdef" lo))
                          acc)))))))

  (define (hex->bytevector hex)
    "Convert hex string to bytevector"
    (let* ((len (quotient (string-length hex) 2))
           (bv (make-bytevector len)))
      (do ((i 0 (+ i 1)))
          ((= i len) bv)
        (let ((hi (hex-digit (string-ref hex (* i 2))))
              (lo (hex-digit (string-ref hex (+ (* i 2) 1)))))
          (bytevector-u8-set! bv i (+ (* hi 16) lo))))))

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
           (hex (bytevector->hex hash)))
      ;; First 32 chars in groups of 4
      (string-join
       (let loop ((s (substring hex 0 32)) (acc '()))
         (if (< (string-length s) 4)
             (reverse (if (string=? s "") acc (cons s acc)))
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
    (let ((algorithm (if (null? rest) 'ed25519 (car rest)))
          (pub-path (key-path name "pub"))
          (key-path* (key-path name "key"))
          (meta-path (key-path name "meta")))

      ;; Write public key
      (with-output-to-file pub-path
        (lambda () (display (bytevector->hex public-key))))

      ;; Write private key (restricted permissions)
      (with-output-to-file key-path*
        (lambda () (display (bytevector->hex private-key))))
      (system (string-append "chmod 600 " key-path*))

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
        (lambda () (display (bytevector->hex pq-pub))))
      (with-output-to-file pq-key-path
        (lambda () (display (bytevector->hex pq-priv))))
      (system (string-append "chmod 600 " pq-key-path))))

  (define (read-key-files name)
    "Read key files from keyring, returns (public private metadata) or #f"
    (let ((pub-path (key-path name "pub"))
          (key-path* (key-path name "key"))
          (meta-path (key-path name "meta")))
      (if (and (file-exists? pub-path)
               (file-exists? key-path*))
          (let* ((pub (hex->bytevector
                        (with-input-from-file pub-path
                          (lambda () (get-line (current-input-port))))))
                 (priv (hex->bytevector
                         (with-input-from-file key-path*
                           (lambda () (get-line (current-input-port))))))
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
                      (let ((pq-pub (hex->bytevector
                                      (with-input-from-file pq-pub-path
                                        (lambda () (get-line (current-input-port))))))
                            (pq-priv (hex->bytevector
                                       (with-input-from-file pq-key-path
                                         (lambda () (get-line (current-input-port)))))))
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
           ;; Strip .pub extension: remove last 4 chars
           (names (map (lambda (f)
                         (substring f 0 (- (string-length f) 4)))
                       ;; Only direct .pub, not .pq.pub
                       (filter (lambda (f)
                                 (not (string-contains f ".pq.")))
                               pub-files))))
      (if (null? names)
          (begin
            (print "Keyring is empty.")
            '())
          (begin
            (print "")
            (print "\x2500;\x2500;\x2500; keyring \x2500;\x2500;\x2500;")
            (print "")
            (for-each
             (lambda (name)
               (let ((keys (read-key-files name)))
                 (when keys
                   (let* ((pub (car keys))
                          (meta (if (= (length keys) 3) (caddr keys) (cadr keys)))
                          (alg-entry (assq 'algorithm meta))
                          (alg (if alg-entry (cadr alg-entry) 'ed25519))
                          (fp (if (eq? alg 'hybrid)
                                  ;; For hybrid, fingerprint the ed25519 pub
                                  (let ((ed-keys (assq 'ed25519 pub)))
                                    (fingerprint (cadr ed-keys)))
                                  (fingerprint pub)))
                          (created (assq 'created meta)))
                     (printf "  ~a  [~a]~%" name alg)
                     (printf "    ~a~%" fp)
                     (when created
                       (printf "    Created: ~a~%" (seconds->string (cadr created))))
                     (printf "~%")))))
             (sort string<? names))
            names))))

  (define (keyring-generate name . rest)
    "Generate new keypair with name and algorithm.
     Algorithms: ed25519 (default), ml-dsa-65, sphincs+, hybrid"
    (let ((algorithm (if (null? rest) 'ed25519 (car rest))))
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

            ;; Post-quantum algorithms - guard for now
            ((ml-dsa-65 ml-dsa sphincs+ sphincs+-shake-256s hybrid)
             (error 'keyring-generate
                    "Post-quantum algorithms not yet ported to Chez"
                    algorithm))

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
          ;; Also clean up hybrid keys if present
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
      ;; Use system rename since Chez doesn't have rename-file in (chezscheme)
      ;; Actually Chez does have rename-file, but it's from (rnrs files)
      (rename-file (key-path old-name "pub") (key-path new-name "pub"))
      (rename-file (key-path old-name "key") (key-path new-name "key"))
      (when (file-exists? (key-path old-name "meta"))
        (rename-file (key-path old-name "meta") (key-path new-name "meta")))
      ;; Hybrid keys
      (when (file-exists? (key-path old-name "pq.pub"))
        (rename-file (key-path old-name "pq.pub") (key-path new-name "pq.pub")))
      (when (file-exists? (key-path old-name "pq.key"))
        (rename-file (key-path old-name "pq.key") (key-path new-name "pq.key")))
      (print "Renamed: " old-name " -> " new-name)
      #t)))

  (define (keyring-import name pub-hex . rest)
    "Import key from hex strings"
    (let ((priv-hex (if (null? rest) #f (car rest))))
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
              (system (string-append "chmod 600 " (key-path name "key"))))
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
    (let ((include-private (and (pair? rest) (car rest))))
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
           (pub-files (filter (lambda (f)
                                (and (string-suffix? ".pub" f)
                                     (not (string-contains f ".pq."))))
                              files))
           (names (map (lambda (f)
                         (substring f 0 (- (string-length f) 4)))
                       pub-files)))
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
                    (quantum-resistant . ,(memq alg '(ml-dsa-65 sphincs+ hybrid))))))))))

  (define (key-public name)
    "Get public key bytevector"
    (let ((keys (key-by-name name)))
      (and keys (car keys))))

  (define (key-private name)
    "Get private key bytevector"
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
     Returns signature bytevector appropriate for the algorithm.
     For hybrid: returns (hybrid-signature (ed25519 sig) (ml-dsa sig))"
    (let* ((info (key-info name))
           (alg (and info (cdr (assq 'algorithm info))))
           (keys (read-key-files name)))
      (unless info (error 'key-sign "Key not found" name))
      (let ((msg-bv (if (bytevector? message)
                        message
                        (string->utf8 message))))
        (case alg
          ((ed25519)
           (let ((priv (cadr keys)))
             (ed25519-sign priv msg-bv)))

          ((ml-dsa-65 sphincs+ hybrid)
           (error 'key-sign
                  "Post-quantum signing not yet ported to Chez"
                  alg))

          (else
           (error 'key-sign "Unknown algorithm" alg))))))

  (define (key-verify name message signature)
    "Verify signature with named key, dispatching by algorithm."
    (let* ((info (key-info name))
           (alg (and info (cdr (assq 'algorithm info))))
           (keys (read-key-files name)))
      (unless info (error 'key-verify "Key not found" name))
      (let ((msg-bv (if (bytevector? message)
                        message
                        (string->utf8 message))))
        (case alg
          ((ed25519)
           (let ((pub (car keys)))
             (ed25519-verify pub msg-bv signature)))

          ((ml-dsa-65 sphincs+ hybrid)
           (error 'key-verify
                  "Post-quantum verification not yet ported to Chez"
                  alg))

          (else
           (error 'key-verify "Unknown algorithm" alg))))))

  ;; ============================================================
  ;; Display
  ;; ============================================================

  (define (seconds->string secs)
    "Convert epoch seconds to ISO-8601 string (Hinnant's algorithm)"
    (let* ((z (+ (quotient secs 86400) 719468))
           (era (quotient (if (>= z 0) z (- z 146096)) 146097))
           (doe (- z (* era 146097)))
           (yoe (quotient (- doe (+ (quotient doe 1460)
                                    (- (quotient doe 36524))
                                    (quotient doe 146096)))
                          365))
           (y (+ yoe (* era 400)))
           (doy (- doe (- (+ (* 365 yoe) (quotient yoe 4))
                          (quotient yoe 100))))
           (mp (quotient (+ (* 5 doy) 2) 153))
           (d (+ (- doy (quotient (+ (* 153 mp) 2) 5)) 1))
           (m (+ mp (if (< mp 10) 3 -9)))
           (y* (+ y (if (<= m 2) 1 0)))
           (time-of-day (modulo secs 86400))
           (hh (quotient time-of-day 3600))
           (mm (quotient (modulo time-of-day 3600) 60))
           (ss (modulo time-of-day 60)))
      (string-append
        (number->string y*) "-"
        (if (< m 10) "0" "") (number->string m) "-"
        (if (< d 10) "0" "") (number->string d) "T"
        (if (< hh 10) "0" "") (number->string hh) ":"
        (if (< mm 10) "0" "") (number->string mm) ":"
        (if (< ss 10) "0" "") (number->string ss))))

  (define (display-key name)
    "Display key details"
    (let ((info (key-info name)))
      (if (not info)
          (print "Key not found: " name)
          (let ((alg (cdr (assq 'algorithm info)))
                (qr (assq 'quantum-resistant info)))
            (print "")
            (printf "  key: ~a~%" name)
            (printf "  Fingerprint: ~a~%" (cdr (assq 'fingerprint info)))
            (printf "  Algorithm:   ~a~a~%"
                    alg
                    (if (and qr (cdr qr)) " (quantum-resistant)" ""))
            (let ((created (cdr (assq 'created info))))
              (when created
                (printf "  Created:     ~a~%" (seconds->string created))))
            (if (eq? alg 'hybrid)
                (begin
                  (printf "  Ed25519:     ~a bytes~%" (cdr (assq 'ed25519-public-size info)))
                  (printf "  ML-DSA:      ~a bytes~%" (cdr (assq 'ml-dsa-public-size info))))
                (begin
                  (printf "  Public:      ~a bytes~%" (cdr (assq 'public-key-size info)))
                  (printf "  Private:     ~a bytes~%" (cdr (assq 'private-key-size info)))))
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
