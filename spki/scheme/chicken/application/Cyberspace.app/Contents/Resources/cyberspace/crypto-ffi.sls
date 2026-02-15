;;; SPKI Scheme - Cryptography FFI to libsodium
;;; Chez Scheme Port
;;;
;;; Chez Scheme bindings to libsodium for Ed25519 signatures,
;;; hashing, randomness, encryption, and Shamir secret sharing.
;;;
;;; Architecture:
;;;   Chez Scheme → foreign-procedure → libsodium (same as OCaml TCB)
;;;   Chez Scheme → foreign-procedure → libcrypto-bridge → libkeccak (SHAKE256)
;;;
;;; The OCaml TCB exists for Rocq verification.
;;; The Scheme FFI exists for policy/tools/human-readable code.
;;; Both use the same underlying cryptography: libsodium Ed25519.

(library (cyberspace crypto-ffi)
  (export
    sodium-init
    ed25519-keypair!
    ed25519-keypair
    ed25519-sign
    ed25519-verify
    ed25519-secret-to-public
    sha256-hash
    sha512-hash
    blake2b-hash
    ;; SHAKE256 and Merkle trees (Memo-047)
    shake256-hash
    merkle-root
    merkle-chunk-size
    merkle-fanout
    merkle-hash-leaf
    merkle-hash-node
    dual-hash
    ;; Merkle inclusion proofs (selective disclosure)
    merkle-prove
    merkle-verify-proof
    merkle-proof?
    merkle-proof-chunk-index
    merkle-proof-chunk-hash
    merkle-proof-path
    crypto-sign-publickeybytes
    crypto-generichash-bytes
    crypto-sign-secretkeybytes
    crypto-sign-bytes
    ;; Entropy & randomness (cryptographically secure)
    random-bytes
    random-u8
    random-u32
    random-uniform
    entropy-status
    ;; Vault cryptography (Memo-041)
    argon2id-hash
    secretbox-encrypt
    secretbox-decrypt
    secretbox-keybytes
    secretbox-noncebytes
    memzero!
    ;; Symmetric encryption aliases (choose your vocabulary)
    seal unseal                   ; General purpose
    encipher decipher             ; Classical cryptography
    shroud unshroud               ; Concealment
    ward unward                   ; Protective barrier
    veil unveil                   ; Hidden from view
    entrust recover               ; Key relationship
    ;; X25519 key exchange (Memo-039 network encryption)
    x25519-keypair
    x25519-scalarmult
    x25519-publickeybytes
    x25519-secretkeybytes
    ;; Shamir secret sharing
    shamir-split
    shamir-reconstruct
    shamir-share?
    share-id
    share-threshold
    share-x
    share-y
    ;; GF(256) arithmetic (for testing)
    gf256-add
    gf256-mul
    gf256-div)

  (import (rnrs)
          (only (chezscheme)
                load-shared-object foreign-procedure format)
          (cyberspace chicken-compatibility blob)
          (cyberspace chicken-compatibility chicken))

  ;; ============================================================
  ;; Library Loading
  ;; ============================================================

  ;; Load libsodium
  (define *sodium-loaded*
    (let loop ((paths '("/opt/homebrew/lib/libsodium.dylib"
                        "/usr/local/lib/libsodium.dylib"
                        "/usr/lib/libsodium.dylib"
                        "libsodium.dylib"
                        "/opt/homebrew/lib/libsodium.so"
                        "/usr/local/lib/libsodium.so"
                        "/usr/lib/libsodium.so"
                        "libsodium.so")))
      (if (null? paths)
          (error 'cyberspace-crypto-ffi
                 "Cannot find libsodium -- install with: brew install libsodium")
          (guard (exn [#t (loop (cdr paths))])
            (load-shared-object (car paths))
            #t))))

  ;; Load crypto-bridge (SHAKE256 via libkeccak)
  (define *bridge-loaded*
    (let loop ((paths '("./libcrypto-bridge.dylib"
                        "../libcrypto-bridge.dylib"
                        "libcrypto-bridge.dylib")))
      (if (null? paths)
          (error 'cyberspace-crypto-ffi
                 "Cannot find libcrypto-bridge.dylib -- run build-crypto-bridge.sh")
          (guard (exn [#t (loop (cdr paths))])
            (load-shared-object (car paths))
            #t))))

  ;; ============================================================
  ;; Constants from libsodium
  ;; ============================================================

  (define crypto-sign-publickeybytes 32)
  (define crypto-sign-secretkeybytes 64)
  (define crypto-sign-bytes 64)
  (define crypto-hash-sha256-bytes 32)
  (define crypto-hash-sha512-bytes 64)
  (define crypto-generichash-bytes 32)

  ;; Secretbox (XSalsa20-Poly1305)
  (define secretbox-keybytes 32)
  (define secretbox-noncebytes 24)
  (define secretbox-macbytes 16)

  ;; X25519
  (define x25519-publickeybytes 32)
  (define x25519-secretkeybytes 32)

  ;; Argon2id
  (define argon2id-opslimit-moderate 3)
  (define argon2id-memlimit-moderate 268435456)  ; 256 MB

  ;; ============================================================
  ;; Foreign Procedure Declarations
  ;; ============================================================

  ;; Initialize libsodium
  (define %sodium-init
    (foreign-procedure "sodium_init" () int))

  (define (sodium-init) (%sodium-init))

  ;; Ed25519 keypair generation (mutating)
  (define %crypto-sign-keypair
    (foreign-procedure "crypto_sign_keypair" (u8* u8*) int))

  ;; Ed25519 detached signature
  (define %crypto-sign-detached
    (foreign-procedure "crypto_sign_detached"
      (u8* u8* u8* unsigned-64 u8*) int))

  ;; Ed25519 detached verification
  (define %crypto-sign-verify-detached
    (foreign-procedure "crypto_sign_verify_detached"
      (u8* u8* unsigned-64 u8*) int))

  ;; SHA-256
  (define %crypto-hash-sha256
    (foreign-procedure "crypto_hash_sha256"
      (u8* u8* unsigned-64) int))

  ;; SHA-512
  (define %crypto-hash-sha512
    (foreign-procedure "crypto_hash_sha512"
      (u8* u8* unsigned-64) int))

  ;; BLAKE2b (generic hash)
  ;; Key parameter is void* so we can pass 0 for NULL (unkeyed)
  (define %crypto-generichash
    (foreign-procedure "crypto_generichash"
      (u8* unsigned-64 u8* unsigned-64 void* unsigned-64) int))

  ;; Randomness (cryptographically secure via OS CSPRNG)
  (define %randombytes-buf
    (foreign-procedure "randombytes_buf"
      (u8* unsigned-64) void))

  (define %randombytes-random
    (foreign-procedure "randombytes_random" () unsigned-32))

  (define %randombytes-uniform
    (foreign-procedure "randombytes_uniform" (unsigned-32) unsigned-32))

  (define %randombytes-implementation-name
    (foreign-procedure "randombytes_implementation_name" () string))

  ;; Memory zeroing (for sensitive data)
  (define %sodium-memzero
    (foreign-procedure "sodium_memzero"
      (u8* unsigned-64) void))

  ;; Argon2id password hashing
  (define %crypto-pwhash
    (foreign-procedure "crypto_pwhash"
      (u8* unsigned-64 u8* unsigned-64 u8* unsigned-64 unsigned-64 int) int))

  ;; Secretbox (XSalsa20-Poly1305)
  (define %crypto-secretbox-easy
    (foreign-procedure "crypto_secretbox_easy"
      (u8* u8* unsigned-64 u8* u8*) int))

  (define %crypto-secretbox-open-easy
    (foreign-procedure "crypto_secretbox_open_easy"
      (u8* u8* unsigned-64 u8* u8*) int))

  ;; X25519 key exchange
  (define %crypto-box-keypair
    (foreign-procedure "crypto_box_keypair" (u8* u8*) int))

  (define %crypto-scalarmult
    (foreign-procedure "crypto_scalarmult" (u8* u8* u8*) int))

  ;; SHAKE256 (via crypto-bridge → libkeccak)
  (define %shake256-hash
    (foreign-procedure "shake256_hash_c"
      (u8* unsigned-64 u8* unsigned-64) int))

  ;; ============================================================
  ;; Ed25519 Scheme Wrappers
  ;; ============================================================

  ;; Generate Ed25519 keypair (mutating version)
  (define (ed25519-keypair! public-key secret-key)
    (%crypto-sign-keypair public-key secret-key))

  ;; Generate Ed25519 keypair (allocating version)
  (define (ed25519-keypair)
    (let ((public-key (make-blob crypto-sign-publickeybytes))
          (secret-key (make-blob crypto-sign-secretkeybytes)))
      (ed25519-keypair! public-key secret-key)
      (list public-key secret-key)))

  ;; Extract public key from secret key
  ;; Ed25519 64-byte secret key contains 32-byte public key at offset 32
  (define (ed25519-secret-to-public secret-key)
    (let* ((public-key (make-blob crypto-sign-publickeybytes))
           (sk-vec (blob->u8vector/shared secret-key))
           (pk-vec (blob->u8vector/shared public-key)))
      (do ((i 0 (+ i 1)))
          ((= i crypto-sign-publickeybytes) public-key)
        (u8vector-set! pk-vec i (u8vector-ref sk-vec (+ i 32))))))

  ;; Sign message with Ed25519
  (define (ed25519-sign secret-key message)
    (let* ((msg-bytes (if (string? message)
                          (string->blob message)
                          message))
           (signature (make-blob crypto-sign-bytes))
           (sig-len-buf (make-blob 8)))  ; unsigned long long output (ignored)
      (%crypto-sign-detached
       signature sig-len-buf msg-bytes (blob-size msg-bytes) secret-key)
      signature))

  ;; Verify Ed25519 signature
  ;;
  ;; TCB CRITICAL: This is the core security guarantee.
  ;; If this returns #t, the signature was created by holder of the private key.
  (define (ed25519-verify public-key message signature)
    (let* ((msg-bytes (if (string? message)
                          (string->blob message)
                          message))
           (result (%crypto-sign-verify-detached
                    signature msg-bytes (blob-size msg-bytes) public-key)))
      (= result 0)))

  ;; ============================================================
  ;; Hash Functions
  ;; ============================================================

  (define (sha256-hash data)
    (let* ((data-bytes (if (string? data) (string->blob data) data))
           (hash (make-blob crypto-hash-sha256-bytes)))
      (%crypto-hash-sha256 hash data-bytes (blob-size data-bytes))
      hash))

  (define (sha512-hash data)
    (let* ((data-bytes (if (string? data) (string->blob data) data))
           (hash (make-blob crypto-hash-sha512-bytes)))
      (%crypto-hash-sha512 hash data-bytes (blob-size data-bytes))
      hash))

  (define (blake2b-hash data)
    (let* ((data-bytes (if (string? data) (string->blob data) data))
           (hash (make-blob crypto-generichash-bytes)))
      (%crypto-generichash
       hash crypto-generichash-bytes
       data-bytes (blob-size data-bytes)
       0 0)  ; No key (NULL via void* = 0)
      hash))

  ;; ============================================================
  ;; SHAKE256 and Merkle Trees (Memo-047)
  ;; ============================================================

  ;; Canonical Merkle tree parameters
  (define merkle-chunk-size 4096)   ; 4 KB chunks
  (define merkle-fanout 16)         ; Children per internal node
  (define merkle-hash-len 32)       ; 256-bit output

  ;; Domain separation prefixes
  (define merkle-leaf-prefix (string->blob "\x0;"))
  (define merkle-node-prefix (string->blob "\x1;"))

  (define (shake256-hash data . rest)
    (let* ((outlen (get-opt rest 0 32))
           (data-bytes (if (string? data) (string->blob data) data))
           (hash (make-blob outlen)))
      (if (= 0 (%shake256-hash hash outlen data-bytes (blob-size data-bytes)))
          hash
          (error 'shake256-hash "SHAKE256 hash failed"))))

  ;; Hash a leaf chunk with domain separation
  (define (merkle-hash-leaf chunk)
    (let ((prefixed (blob-append merkle-leaf-prefix chunk)))
      (shake256-hash prefixed)))

  ;; Hash internal node with domain separation
  (define (merkle-hash-node children)
    (let ((concat (apply blob-append (cons merkle-node-prefix children))))
      (shake256-hash concat)))

  ;; Split content into chunks
  (define (merkle-chunk content)
    (let ((len (blob-size content)))
      (if (= len 0)
          (list (make-blob 0))
          (let loop ((offset 0) (acc '()))
            (if (>= offset len)
                (reverse acc)
                (let* ((chunk-len (min merkle-chunk-size (- len offset)))
                       (chunk (make-blob chunk-len)))
                  (move-memory! content chunk chunk-len offset 0)
                  (loop (+ offset merkle-chunk-size) (cons chunk acc))))))))

  ;; Build Merkle tree from leaves, return root
  (define (merkle-build-tree leaves)
    (cond
      ((null? leaves) (merkle-hash-leaf (make-blob 0)))
      ((null? (cdr leaves)) (car leaves))
      (else
       (let loop ((nodes leaves) (groups '()) (current '()) (count 0))
         (cond
           ((null? nodes)
            (let ((final-groups (if (null? current)
                                    (reverse groups)
                                    (reverse (cons (reverse current) groups)))))
              (let ((parents (map merkle-hash-node final-groups)))
                (merkle-build-tree parents))))
           ((>= count merkle-fanout)
            (loop nodes (cons (reverse current) groups) '() 0))
           (else
            (loop (cdr nodes) groups (cons (car nodes) current) (+ count 1))))))))

  ;; Compute Merkle root of content
  ;; This is THE quantum-resistant object identity function (Memo-047).
  (define (merkle-root content)
    (let* ((data (if (string? content) (string->blob content) content))
           (chunks (merkle-chunk data))
           (leaves (map merkle-hash-leaf chunks)))
      (merkle-build-tree leaves)))

  ;; Compute both legacy SHA-512 and Merkle root (dual-hash transition)
  (define (dual-hash content)
    (let ((data (if (string? content) (string->blob content) content)))
      (cons (sha512-hash data) (merkle-root data))))

  ;; ============================================================
  ;; Merkle Inclusion Proofs (Selective Disclosure)
  ;; ============================================================

  (define (make-merkle-proof chunk-index chunk-hash path)
    (list 'merkle-proof chunk-index chunk-hash path))

  (define (merkle-proof? x)
    (and (pair? x) (eq? 'merkle-proof (car x))))

  (define (merkle-proof-chunk-index proof)
    (list-ref proof 1))

  (define (merkle-proof-chunk-hash proof)
    (list-ref proof 2))

  (define (merkle-proof-path proof)
    (list-ref proof 3))

  ;; Build full Merkle tree with all intermediate nodes
  (define (merkle-build-full-tree leaves)
    (let loop ((levels '()) (current leaves))
      (cond
        ((null? current) (reverse levels))
        ((null? (cdr current)) (reverse (cons current levels)))
        (else
         (let ((groups (group-by-n current merkle-fanout)))
           (let ((parents (map merkle-hash-node groups)))
             (loop (cons current levels) parents)))))))

  (define (group-by-n lst n)
    (if (null? lst)
        '()
        (let loop ((lst lst) (current '()) (count 0) (acc '()))
          (cond
            ((null? lst)
             (reverse (if (null? current) acc (cons (reverse current) acc))))
            ((>= count n)
             (loop lst '() 0 (cons (reverse current) acc)))
            (else
             (loop (cdr lst) (cons (car lst) current) (+ count 1) acc))))))

  ;; Generate inclusion proof for a chunk
  (define (merkle-prove content chunk-index)
    (let* ((data (if (string? content) (string->blob content) content))
           (chunks (merkle-chunk data))
           (num-chunks (length chunks)))
      (if (or (< chunk-index 0) (>= chunk-index num-chunks))
          #f
          (let* ((leaves (map merkle-hash-leaf chunks))
                 (levels (merkle-build-full-tree leaves))
                 (chunk-hash (list-ref leaves chunk-index)))
            (let loop ((idx chunk-index) (level-idx 0) (path '()))
              (if (>= level-idx (- (length levels) 1))
                  (make-merkle-proof chunk-index chunk-hash (reverse path))
                  (let* ((level (list-ref levels level-idx))
                         (group-idx (div idx merkle-fanout))
                         (group-start (* group-idx merkle-fanout))
                         (group-end (min (+ group-start merkle-fanout) (length level))))
                    (let sibling-loop ((i group-start) (siblings '()))
                      (if (>= i group-end)
                          (loop group-idx (+ level-idx 1)
                                (append (reverse siblings) path))
                          (if (= i idx)
                              (sibling-loop (+ i 1) siblings)
                              (let ((pos (if (< i idx) 'left 'right)))
                                (sibling-loop (+ i 1)
                                              (cons (cons (list-ref level i) pos)
                                                    siblings)))))))))))))

  ;; Compare two blobs for equality
  (define (merkle-blob=? a b)
    (and (= (blob-size a) (blob-size b))
         (let ((va (blob->u8vector a))
               (vb (blob->u8vector b)))
           (let loop ((i 0))
             (if (>= i (u8vector-length va))
                 #t
                 (and (= (u8vector-ref va i) (u8vector-ref vb i))
                      (loop (+ i 1))))))))

  ;; Verify inclusion proof
  (define (merkle-verify-proof root proof)
    (if (not (merkle-proof? proof))
        #f
        (let ((chunk-hash (merkle-proof-chunk-hash proof))
              (path (merkle-proof-path proof)))
          (let loop ((current-hash chunk-hash) (remaining-path path))
            (if (null? remaining-path)
                (or (merkle-blob=? current-hash root)
                    (merkle-blob=? (merkle-hash-node (list current-hash)) root))
                (let collect ((path remaining-path)
                              (left-siblings '())
                              (right-siblings '())
                              (count 0))
                  (if (or (null? path) (>= count (- merkle-fanout 1)))
                      (let* ((all-left (reverse left-siblings))
                             (all-right right-siblings)
                             (children (append all-left
                                               (list current-hash)
                                               all-right))
                             (parent (merkle-hash-node children)))
                        (loop parent path))
                      (let* ((sibling (car path))
                             (hash (car sibling))
                             (pos (cdr sibling)))
                        (if (eq? pos 'left)
                            (collect (cdr path) (cons hash left-siblings)
                                     right-siblings (+ count 1))
                            (collect (cdr path) left-siblings
                                     (cons hash right-siblings) (+ count 1)))))))))))

  ;; ============================================================
  ;; Entropy & Cryptographic Randomness
  ;; ============================================================
  ;;
  ;; All randomness from libsodium's randombytes API which:
  ;;   - Uses /dev/urandom on Unix, CryptGenRandom on Windows
  ;;   - Automatically reseeds from system entropy
  ;;   - Safe for key generation, nonces, IVs

  (define (random-bytes n)
    (let ((buf (make-blob n)))
      (%randombytes-buf buf n)
      buf))

  (define (random-u8)
    (let ((buf (make-blob 1)))
      (%randombytes-buf buf 1)
      (u8vector-ref (blob->u8vector/shared buf) 0)))

  (define (random-u32)
    (%randombytes-random))

  (define (random-uniform upper-bound)
    (%randombytes-uniform upper-bound))

  (define (entropy-status)
    (let ((impl (%randombytes-implementation-name)))
      `((implementation . ,impl)
        (source . ,(cond
                    ((string=? impl "sysrandom") "/dev/urandom")
                    ((string=? impl "internal") "ChaCha20 (seeded)")
                    (else "unknown")))
        (status . ok))))

  ;; ============================================================
  ;; Vault Cryptography (Memo-041)
  ;; ============================================================

  (define (memzero! buf)
    (%sodium-memzero buf (blob-size buf)))

  (define (argon2id-hash password salt)
    (let* ((pass-bytes (if (string? password) (string->blob password) password))
           (key (make-blob secretbox-keybytes)))
      (let ((result
             (%crypto-pwhash
              key secretbox-keybytes
              pass-bytes (blob-size pass-bytes)
              salt
              argon2id-opslimit-moderate
              argon2id-memlimit-moderate
              2)))  ; crypto_pwhash_ALG_ARGON2ID13
        (if (= result 0)
            key
            (error 'argon2id-hash "argon2id-hash failed")))))

  (define (secretbox-encrypt plaintext nonce key)
    (let* ((plen (blob-size plaintext))
           (ciphertext (make-blob (+ plen secretbox-macbytes))))
      (let ((result
             (%crypto-secretbox-easy ciphertext plaintext plen nonce key)))
        (if (= result 0)
            ciphertext
            (error 'secretbox-encrypt "secretbox-encrypt failed")))))

  (define (secretbox-decrypt ciphertext nonce key)
    (let* ((clen (blob-size ciphertext))
           (plaintext (make-blob (- clen secretbox-macbytes))))
      (let ((result
             (%crypto-secretbox-open-easy plaintext ciphertext clen nonce key)))
        (if (= result 0)
            plaintext
            #f))))  ; Authentication failed

  ;; ============================================================
  ;; Symmetric Encryption Aliases
  ;; ============================================================

  (define seal secretbox-encrypt)
  (define unseal secretbox-decrypt)
  (define encipher secretbox-encrypt)
  (define decipher secretbox-decrypt)
  (define shroud secretbox-encrypt)
  (define unshroud secretbox-decrypt)
  (define ward secretbox-encrypt)
  (define unward secretbox-decrypt)
  (define veil secretbox-encrypt)
  (define unveil secretbox-decrypt)
  (define entrust secretbox-encrypt)
  (define recover secretbox-decrypt)

  ;; ============================================================
  ;; X25519 Key Exchange (Memo-039 Network Encryption)
  ;; ============================================================

  (define (x25519-keypair)
    (let ((public-key (make-blob x25519-publickeybytes))
          (secret-key (make-blob x25519-secretkeybytes)))
      (%crypto-box-keypair public-key secret-key)
      (list public-key secret-key)))

  (define (x25519-scalarmult secret-key public-key)
    (let ((shared (make-blob 32)))
      (let ((result (%crypto-scalarmult shared secret-key public-key)))
        (if (= result 0)
            shared
            (error 'x25519-scalarmult "x25519-scalarmult failed")))))

  ;; ============================================================
  ;; Shamir Secret Sharing (GF(256))
  ;; ============================================================

  ;; GF(256) arithmetic tables (precomputed for efficiency)
  ;; Using polynomial x^8 + x^4 + x^3 + x + 1 (0x11b)

  (define gf256-exp (make-u8vector 512))
  (define gf256-log (make-u8vector 256))

  (define (init-gf256-tables!)
    (let ((x 1))
      (do ((i 0 (+ i 1)))
          ((= i 255))
        (u8vector-set! gf256-exp i x)
        (u8vector-set! gf256-log x i)
        (when (< i 254)
          (let* ((x2 (bitwise-arithmetic-shift x 1))
                 (x2-reduced (if (>= x2 256)
                                 (bitwise-xor x2 #x11b)
                                 x2)))
            (set! x (bitwise-xor x2-reduced x))))))
    (do ((i 255 (+ i 1)))
        ((= i 510))
      (u8vector-set! gf256-exp i (u8vector-ref gf256-exp (- i 255)))))

  ;; Initialize tables on module load
  ;; Wrapped in define to satisfy R6RS body ordering (definitions before expressions)
  (define initialize-gf256-tables (begin (init-gf256-tables!) #t))

  (define (gf256-add a b)
    (bitwise-xor a b))

  (define (gf256-mul a b)
    (if (or (= a 0) (= b 0))
        0
        (u8vector-ref gf256-exp
                     (mod (+ (u8vector-ref gf256-log a)
                             (u8vector-ref gf256-log b))
                          255))))

  (define (gf256-div a b)
    (if (= a 0)
        0
        (u8vector-ref gf256-exp
                     (mod (- (+ (u8vector-ref gf256-log a) 255)
                             (u8vector-ref gf256-log b))
                          255))))

  (define (gf256-poly-eval coeffs x)
    (let loop ((i (- (length coeffs) 1))
               (result 0))
      (if (< i 0)
          result
          (loop (- i 1)
                (gf256-add (list-ref coeffs i)
                          (gf256-mul result x))))))

  ;; Shamir share record type (R6RS)
  (define-record-type shamir-share
    (fields (immutable id share-id)
            (immutable threshold share-threshold)
            (immutable x share-x)
            (immutable y share-y)))

  (define (shamir-split secret . opts)
    (let ((threshold (get-key opts 'threshold: 3))
          (total (get-key opts 'total: 5)))

      (unless (<= threshold total)
        (error 'shamir-split "Threshold must be <= total shares"))

      (unless (> threshold 1)
        (error 'shamir-split "Threshold must be > 1"))

      (let* ((secret-bytes (blob->u8vector secret))
             (secret-len (u8vector-length secret-bytes))
             (shares (make-vector total)))

        ;; Initialize all share y-value vectors
        (do ((i 0 (+ i 1)))
            ((= i total))
          (vector-set! shares i (make-u8vector secret-len)))

        ;; For each byte of the secret
        (do ((byte-idx 0 (+ byte-idx 1)))
            ((= byte-idx secret-len))

          ;; Generate ONE random polynomial for this byte
          ;; a[0] = secret byte, a[1..k-1] = random
          (let ((coeffs (make-vector threshold)))
            (vector-set! coeffs 0 (u8vector-ref secret-bytes byte-idx))

            ;; CRITICAL: Use cryptographic randomness for polynomial coefficients
            (do ((i 1 (+ i 1)))
                ((= i threshold))
              (vector-set! coeffs i (random-u8)))

            ;; Evaluate this polynomial at each share's x-value
            (do ((share-num 1 (+ share-num 1)))
                ((> share-num total))
              (u8vector-set! (vector-ref shares (- share-num 1))
                            byte-idx
                            (gf256-poly-eval (vector->list coeffs) share-num)))))

        ;; Convert u8vectors to share records
        (do ((i 0 (+ i 1)))
            ((= i total))
          (vector-set! shares i
                      (make-shamir-share
                        (string->symbol (string-append "share-" (number->string (+ i 1))))
                        threshold
                        (+ i 1)
                        (u8vector->blob (vector-ref shares i)))))

        (vector->list shares))))

  (define (shamir-reconstruct shares)
    (when (null? shares)
      (error 'shamir-reconstruct "Need at least one share"))

    (let* ((threshold (share-threshold (car shares)))
           (num-shares (length shares)))

      (unless (>= num-shares threshold)
        (error 'shamir-reconstruct
               (format #f "Need at least ~a shares, got ~a" threshold num-shares)))

      (let* ((k-shares (take shares threshold))
             (share-len (blob-size (share-y (car k-shares))))
             (secret (make-u8vector share-len)))

        ;; For each byte position
        (do ((byte-idx 0 (+ byte-idx 1)))
            ((= byte-idx share-len))

          ;; Lagrange interpolation at x=0
          (let ((result 0))
            (do ((i 0 (+ i 1)))
                ((= i threshold))

              (let ((xi (share-x (list-ref k-shares i)))
                    (yi (u8vector-ref (blob->u8vector (share-y (list-ref k-shares i)))
                                     byte-idx)))

                (let ((basis 1))
                  (do ((j 0 (+ j 1)))
                      ((= j threshold))
                    (when (not (= i j))
                      (let ((xj (share-x (list-ref k-shares j))))
                        (set! basis (gf256-mul basis
                                              (gf256-div xj
                                                        (gf256-add xi xj)))))))

                  (set! result (gf256-add result (gf256-mul yi basis))))))

            (u8vector-set! secret byte-idx result)))

        (u8vector->blob secret))))

  ;; SRFI-1 take (needed for shamir-reconstruct)
  (define (take lst n)
    (if (or (= n 0) (null? lst))
        '()
        (cons (car lst) (take (cdr lst) (- n 1)))))

) ;; end library
