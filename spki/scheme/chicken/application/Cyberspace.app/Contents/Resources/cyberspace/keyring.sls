;;; keyring.sls - Key Management for the Soup
;;; Library of Cyberspace - Chez Port
;;;
;;; "Not your keys, not your crypto" - Bitcoin wisdom
;;;
;;; Provides:
;;; - Named keypair generation and storage
;;; - Key lookup by name or fingerprint
;;; - Key listing and inspection
;;; - Keyring persistence (.vault/keys/)
;;; - Multi-algorithm support (Ed25519, ML-DSA-65, SPHINCS+, hybrid)
;;;
;;; Ported from Chicken's keyring.scm.
;;; Changes: module -> library, #!optional -> get-opt,
;;;          (chicken file/pathname) -> Chez equivalents,
;;;          receive -> let-values.

(library (cyberspace keyring)
  (export
    keyring-init
    keyring-list
    keyring-generate
    keyring-import
    keyring-export
    keyring-delete
    keyring-rename
    key-by-name
    key-by-fingerprint
    key-exists?
    key-info
    key-fingerprint
    key-created
    key-public
    key-private
    key-algorithm
    key-sign
    key-verify
    supported-algorithms
    display-key
    display-keyring
    keyring-path
    key-path)

  (import (except (rnrs) find)
          (only (chezscheme)
                printf format
                file-directory?
                directory-list mkdir
                rename-file
                sort
                current-time time-second)
          (cyberspace crypto-ffi)
          (cyberspace pq-crypto)
          (cyberspace chicken-compatibility blob)
          (cyberspace chicken-compatibility chicken))

  ;; ============================================================
  ;; Helpers
  ;; ============================================================

  (define (find pred lst)
    (cond ((null? lst) #f)
          ((pred (car lst)) (car lst))
          (else (find pred (cdr lst)))))

  (define (string-suffix? suffix str)
    (and (>= (string-length str) (string-length suffix))
         (string=? (substring str (- (string-length str) (string-length suffix))
                              (string-length str))
                   suffix)))

  (define (string-prefix? prefix str)
    (and (>= (string-length str) (string-length prefix))
         (string=? (substring str 0 (string-length prefix)) prefix)))

  (define (string-null? s) (= 0 (string-length s)))

  (define (string-join lst sep)
    (if (null? lst) ""
        (let loop ((rest (cdr lst)) (acc (car lst)))
          (if (null? rest) acc
              (loop (cdr rest) (string-append acc sep (car rest)))))))

  (define (pathname-strip-extension path)
    "Remove file extension from path"
    (let loop ((i (- (string-length path) 1)))
      (cond
        ((< i 0) path)
        ((char=? (string-ref path i) #\.) (substring path 0 i))
        ((char=? (string-ref path i) #\/) path)
        (else (loop (- i 1))))))

  (define (directory-exists? path)
    (and (file-exists? path) (file-directory? path)))

  (define (current-seconds)
    (time-second (current-time)))

  (define (seconds->string secs)
    ;; Simplified timestamp
    (format #f "~a" secs))

  ;; ============================================================
  ;; Paths
  ;; ============================================================

  (define (keyring-path) ".vault/keys")

  (define (key-path name ext)
    (string-append (keyring-path) "/" name "." ext))

  ;; ============================================================
  ;; Initialization
  ;; ============================================================

  (define (keyring-init)
    (let ((path (keyring-path)))
      (unless (directory-exists? path)
        ;; Create .vault first, then .vault/keys
        (unless (directory-exists? ".vault")
          (guard (exn [#t #f]) (mkdir ".vault" #o755)))
        (guard (exn [#t #f]) (mkdir path #o755))
        (print "Keyring initialized: " path))
      path))

  ;; ============================================================
  ;; Hex Conversion
  ;; ============================================================

  (define (blob->hex blob)
    (let* ((vec (blob->u8vector blob))
           (len (u8vector-length vec)))
      (let loop ((i 0) (acc '()))
        (if (= i len) (apply string-append (reverse acc))
            (let* ((byte (u8vector-ref vec i))
                   (hi (div byte 16))
                   (lo (mod byte 16)))
              (loop (+ i 1)
                    (cons (string (string-ref "0123456789abcdef" hi)
                                  (string-ref "0123456789abcdef" lo))
                          acc)))))))

  (define (hex-digit c)
    (cond
     ((and (char>=? c #\0) (char<=? c #\9))
      (- (char->integer c) (char->integer #\0)))
     ((and (char>=? c #\a) (char<=? c #\f))
      (+ 10 (- (char->integer c) (char->integer #\a))))
     ((and (char>=? c #\A) (char<=? c #\F))
      (+ 10 (- (char->integer c) (char->integer #\A))))
     (else 0)))

  (define (hex->blob hex)
    (let* ((len (div (string-length hex) 2))
           (vec (make-u8vector len)))
      (do ((i 0 (+ i 1)))
          ((>= i len) (u8vector->blob vec))
        (let ((hi (hex-digit (string-ref hex (* i 2))))
              (lo (hex-digit (string-ref hex (+ (* i 2) 1)))))
          (u8vector-set! vec i (+ (* hi 16) lo))))))

  ;; ============================================================
  ;; Fingerprint
  ;; ============================================================

  (define (fingerprint public-key)
    (let* ((hash (sha512-hash public-key))
           (hex (blob->hex hash)))
      (string-join
       (let loop ((s (substring hex 0 32)) (acc '()))
         (if (< (string-length s) 4)
             (reverse (if (string-null? s) acc (cons s acc)))
             (loop (substring s 4 (string-length s)) (cons (substring s 0 4) acc))))
       ":")))

  ;; ============================================================
  ;; Supported Algorithms
  ;; ============================================================

  (define (supported-algorithms)
    '(ed25519 ml-dsa-65 sphincs+ hybrid))

  (define (algorithm-valid? alg)
    (memq alg (supported-algorithms)))

  ;; ============================================================
  ;; Key Storage
  ;; ============================================================

  (define (write-key-files name public-key private-key . rest)
    (let ((algorithm (get-opt rest 0 'ed25519)))
      (let ((pub-path (key-path name "pub"))
            (priv-path (key-path name "key"))
            (meta-path (key-path name "meta")))
        (with-output-to-file pub-path
          (lambda () (display (blob->hex public-key))))
        (with-output-to-file priv-path
          (lambda () (display (blob->hex private-key))))
        (with-output-to-file meta-path
          (lambda ()
            (write `((name ,name)
                     (algorithm ,algorithm)
                     (created ,(current-seconds))
                     (fingerprint ,(fingerprint public-key)))))))))

  (define (write-hybrid-key-files name ed-pub ed-priv pq-pub pq-priv)
    (write-key-files name ed-pub ed-priv 'hybrid)
    (let ((pq-pub-path (key-path name "pq.pub"))
          (pq-key-path (key-path name "pq.key")))
      (with-output-to-file pq-pub-path
        (lambda () (display (blob->hex pq-pub))))
      (with-output-to-file pq-key-path
        (lambda () (display (blob->hex pq-priv))))))

  (define (read-key-files name)
    (let ((pub-path (key-path name "pub"))
          (priv-path (key-path name "key"))
          (meta-path (key-path name "meta")))
      (if (and (file-exists? pub-path) (file-exists? priv-path))
          (let* ((pub-hex (with-input-from-file pub-path
                            (lambda () (get-line (current-input-port)))))
                 (priv-hex (with-input-from-file priv-path
                             (lambda () (get-line (current-input-port)))))
                 (pub (hex->blob pub-hex))
                 (priv (hex->blob priv-hex))
                 (meta (if (file-exists? meta-path)
                           (with-input-from-file meta-path read)
                           '()))
                 (alg (let ((a (assq 'algorithm meta)))
                        (if a (cadr a) 'ed25519))))
            (if (eq? alg 'hybrid)
                (let ((pq-pub-path (key-path name "pq.pub"))
                      (pq-key-path (key-path name "pq.key")))
                  (if (and (file-exists? pq-pub-path)
                           (file-exists? pq-key-path))
                      (let ((pq-pub-hex (with-input-from-file pq-pub-path
                                          (lambda () (get-line (current-input-port)))))
                            (pq-priv-hex (with-input-from-file pq-key-path
                                           (lambda () (get-line (current-input-port))))))
                        (let ((pq-pub (hex->blob pq-pub-hex))
                              (pq-priv (hex->blob pq-priv-hex)))
                          (list `((ed25519 ,pub ,priv) (ml-dsa ,pq-pub ,pq-priv)) meta)))
                      #f))
                (list pub priv meta)))
          #f)))

  ;; ============================================================
  ;; Keyring Operations
  ;; ============================================================

  (define (key-exists? name)
    (file-exists? (key-path name "pub")))

  (define (keyring-list)
    (keyring-init)
    (let* ((files (directory-list (keyring-path)))
           (pub-files (filter (lambda (f) (string-suffix? ".pub" f)) files))
           ;; Exclude .pq.pub files
           (pub-files (filter (lambda (f) (not (string-suffix? ".pq.pub" f))) pub-files))
           (names (map pathname-strip-extension pub-files)))
      (if (null? names)
          (begin (print "Keyring is empty.") '())
          (begin
            (print "")
            (print "+-------------------------------------------------------+")
            (print "|                    keyring                             |")
            (print "+-------------------------------------------------------+")
            (for-each
             (lambda (name)
               (let ((keys (read-key-files name)))
                 (when keys
                   (let* ((pub (if (and (pair? (car keys)) (pair? (caar keys)))
                                   ;; Hybrid: first element is ((ed25519 pub priv) ...)
                                   (cadar (car keys))
                                   (car keys)))
                          (fp (fingerprint pub)))
                     (printf "| ~a~a|~%"
                             name
                             (make-string (max 0 (- 55 (string-length name))) #\space))
                     (printf "|   ~a |~%"
                             (substring fp 0 (min 50 (string-length fp))))))))
             (sort string<? names))
            (print "+-------------------------------------------------------+")
            (print "")
            names))))

  (define (keyring-generate name . rest)
    (let ((algorithm (get-opt rest 0 'ed25519)))
      (keyring-init)
      (unless (algorithm-valid? algorithm)
        (error 'keyring-generate "Unknown algorithm" algorithm))
      (if (key-exists? name)
          (begin (print "Key already exists: " name) #f)
          (case algorithm
            ((ed25519)
             (let ((keys (ed25519-keypair)))
               (let ((pub (car keys)) (priv (cadr keys)))
                 (write-key-files name pub priv 'ed25519)
                 (print "")
                 (print "Generated Ed25519 key: " name)
                 (print "  Fingerprint: " (fingerprint pub))
                 (print "  Algorithm:   ed25519 (classical)")
                 (print "")
                 name)))

            ((ml-dsa-65 ml-dsa)
             (let-values (((pub priv) (ml-dsa-keygen)))
               (write-key-files name pub priv 'ml-dsa-65)
               (print "")
               (print "Generated ML-DSA-65 key: " name)
               (print "  Fingerprint: " (fingerprint pub))
               (print "  Algorithm:   ml-dsa-65 (post-quantum, FIPS 204)")
               (print "")
               name))

            ((sphincs+ sphincs+-shake-256s)
             (let-values (((pub priv) (sphincs+-keygen)))
               (write-key-files name pub priv 'sphincs+)
               (print "")
               (print "Generated SPHINCS+ key: " name)
               (print "  Fingerprint: " (fingerprint pub))
               (print "  Algorithm:   sphincs+-shake-256s (post-quantum, FIPS 205)")
               (print "")
               name))

            ((hybrid)
             (let ((ed-keys (ed25519-keypair)))
               (let-values (((pq-pub pq-priv) (ml-dsa-keygen)))
                 (let ((ed-pub (car ed-keys)) (ed-priv (cadr ed-keys)))
                   (write-hybrid-key-files name ed-pub ed-priv pq-pub pq-priv)
                   (print "")
                   (print "Generated HYBRID key: " name)
                   (print "  Fingerprint: " (fingerprint ed-pub))
                   (print "  Algorithm:   hybrid (Ed25519 + ML-DSA-65)")
                   (print "  Survives Q-Day: YES")
                   (print "")
                   name))))

            (else (error 'keyring-generate "Unknown algorithm" algorithm))))))

  (define (keyring-delete name)
    (if (not (key-exists? name))
        (begin (print "Key not found: " name) #f)
        (begin
          (safe-delete-file (key-path name "pub"))
          (safe-delete-file (key-path name "key"))
          (safe-delete-file (key-path name "meta"))
          (safe-delete-file (key-path name "pq.pub"))
          (safe-delete-file (key-path name "pq.key"))
          (print "Deleted key: " name)
          #t)))

  (define (keyring-rename old-name new-name)
    (cond
     ((not (key-exists? old-name))
      (print "Key not found: " old-name) #f)
     ((key-exists? new-name)
      (print "Key already exists: " new-name) #f)
     (else
      (rename-file (key-path old-name "pub") (key-path new-name "pub"))
      (rename-file (key-path old-name "key") (key-path new-name "key"))
      (when (file-exists? (key-path old-name "meta"))
        (rename-file (key-path old-name "meta") (key-path new-name "meta")))
      (print "Renamed: " old-name " -> " new-name)
      #t)))

  (define (keyring-import name pub-hex . rest)
    (let ((priv-hex (get-opt rest 0 #f)))
      (keyring-init)
      (if (key-exists? name)
          (begin (print "Key already exists: " name) #f)
          (let ((pub (hex->blob pub-hex)))
            (with-output-to-file (key-path name "pub")
              (lambda () (display pub-hex)))
            (when priv-hex
              (with-output-to-file (key-path name "key")
                (lambda () (display priv-hex))))
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
    (let ((include-private (get-opt rest 0 #f)))
      (let ((keys (read-key-files name)))
        (if (not keys)
            (begin (print "Key not found: " name) #f)
            (let ((pub (car keys)) (priv (cadr keys)))
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

  (define (key-by-name name)
    (let ((keys (read-key-files name)))
      (if keys (list (car keys) (cadr keys)) #f)))

  (define (key-by-fingerprint fp)
    (keyring-init)
    (let* ((files (directory-list (keyring-path)))
           (pub-files (filter (lambda (f) (string-suffix? ".pub" f)) files))
           (pub-files (filter (lambda (f) (not (string-suffix? ".pq.pub" f))) pub-files))
           (names (map pathname-strip-extension pub-files)))
      (find
       (lambda (name)
         (let ((keys (read-key-files name)))
           (and keys
                (let ((pub (if (and (pair? (car keys)) (pair? (caar keys)))
                               (cadar (car keys))
                               (car keys))))
                  (string-prefix? fp (fingerprint pub))))))
       names)))

  ;; ============================================================
  ;; Key Info
  ;; ============================================================

  (define (key-info name)
    (let ((keys (read-key-files name)))
      (if (not keys)
          #f
          (let* ((meta (if (= (length keys) 2) (cadr keys) (caddr keys)))
                 (alg-entry (assq 'algorithm meta))
                 (alg (if alg-entry (cadr alg-entry) 'ed25519))
                 (created (assq 'created meta)))
            (if (eq? alg 'hybrid)
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
                (let ((pub (car keys)) (priv (cadr keys)))
                  `((name . ,name)
                    (fingerprint . ,(fingerprint pub))
                    (algorithm . ,alg)
                    (public-key-size . ,(blob-size pub))
                    (private-key-size . ,(blob-size priv))
                    (created . ,(and created (cadr created)))
                    (has-private . #t)
                    (quantum-resistant . ,(if (memq alg '(ml-dsa-65 sphincs+ hybrid)) #t #f)))))))))

  (define (key-public name)
    (let ((keys (key-by-name name)))
      (and keys (car keys))))

  (define (key-private name)
    (let ((keys (key-by-name name)))
      (and keys (cadr keys))))

  (define (key-fingerprint name)
    (let ((pub (key-public name)))
      (and pub (fingerprint pub))))

  (define (key-created name)
    (let ((info (key-info name)))
      (and info (cdr (assq 'created info)))))

  (define (key-algorithm name)
    (let ((info (key-info name)))
      (and info (cdr (assq 'algorithm info)))))

  ;; ============================================================
  ;; Algorithm-Aware Signing and Verification
  ;; ============================================================

  (define (key-sign name message)
    (let* ((info (key-info name))
           (alg (and info (cdr (assq 'algorithm info))))
           (keys (read-key-files name)))
      (unless info (error 'key-sign "Key not found" name))
      (let ((msg-blob (if (bytevector? message) message (string->blob message))))
        (case alg
          ((ed25519)
           (ed25519-sign (cadr keys) msg-blob))
          ((ml-dsa-65)
           (ml-dsa-sign msg-blob (cadr keys)))
          ((sphincs+)
           (sphincs+-sign msg-blob (cadr keys)))
          ((hybrid)
           (let* ((key-data (car keys))
                  (ed-keys (assq 'ed25519 key-data))
                  (pq-keys (assq 'ml-dsa key-data))
                  (ed-priv (caddr ed-keys))
                  (pq-priv (caddr pq-keys)))
             `(hybrid-signature
               (ed25519 ,(ed25519-sign ed-priv msg-blob))
               (ml-dsa ,(ml-dsa-sign msg-blob pq-priv)))))
          (else (error 'key-sign "Unknown algorithm" alg))))))

  (define (key-verify name message signature)
    (let* ((info (key-info name))
           (alg (and info (cdr (assq 'algorithm info))))
           (keys (read-key-files name)))
      (unless info (error 'key-verify "Key not found" name))
      (let ((msg-blob (if (bytevector? message) message (string->blob message))))
        (case alg
          ((ed25519)
           (ed25519-verify (car keys) msg-blob signature))
          ((ml-dsa-65)
           (ml-dsa-verify msg-blob signature (car keys)))
          ((sphincs+)
           (sphincs+-verify msg-blob signature (car keys)))
          ((hybrid)
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
          (else (error 'key-verify "Unknown algorithm" alg))))))

  ;; ============================================================
  ;; Display
  ;; ============================================================

  (define (display-key name)
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
                    alg (if (and qr (cdr qr)) " (quantum-resistant)" ""))
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
    (keyring-list))

  ;; ============================================================
  ;; Helpers
  ;; ============================================================

  (define (safe-delete-file path)
    (when (file-exists? path)
      (delete-file path)))

) ;; end library
