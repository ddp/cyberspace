;;; SPKI Scheme - Cryptography FFI (Chez Port)
;;; Library of Cyberspace
;;;
;;; Chez Scheme bindings to libsodium for Ed25519 signatures, hashing,
;;; secretbox encryption, X25519 key exchange, and Shamir secret sharing.
;;;
;;; Architecture:
;;;   Chez Scheme -> foreign-procedure -> libsodium (direct)
;;;   Chez Scheme -> foreign-procedure -> libcrypto-bridge.dylib (SHAKE256 only)
;;;
;;; Port notes:
;;;   - Chicken's scheme-pointer (GC-safe interior pointer) maps to
;;;     explicit bytevector<->foreign memory copying in Chez.
;;;   - All foreign calls go through helper functions that copy bytevector
;;;     contents to foreign-alloc'd memory, call the C function, and copy back.
;;;   - SHAKE256 uses a C shim because libkeccak's API uses stack-allocated structs.
;;;
;;; Copyright (c) 2026 Yoyodyne. See LICENSE.

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
    ;; Symmetric encryption aliases
    seal unseal
    encipher decipher
    shroud unshroud
    ward unward
    veil unveil
    entrust recover
    ;; X25519 key exchange (Memo-039)
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
                foreign-procedure foreign-alloc foreign-free foreign-ref
                foreign-set! load-shared-object
                record-writer with-output-to-string
                iota void format printf))

  ;; ============================================================
  ;; Load shared libraries at init time
  ;;
  ;; foreign-procedure resolves symbols at definition time in Chez,
  ;; so libraries MUST be loaded before any foreign-procedure forms.
  ;; ============================================================

  (define *sodium-loaded*
    (guard (exn [#t (error 'cyberspace-crypto "Cannot load libsodium")])
      (load-shared-object "libsodium.dylib")
      #t))

  (define *crypto-bridge-loaded*
    (let loop ((paths '("./libcrypto-bridge.dylib"
                        "../libcrypto-bridge.dylib"
                        "libcrypto-bridge.dylib")))
      (if (null? paths)
          ;; SHAKE256 will be unavailable but don't fail -- rest of crypto works
          #f
          (guard (exn [#t (loop (cdr paths))])
            (load-shared-object (car paths))
            #t))))

  ;; ============================================================
  ;; Foreign procedure bindings (libsodium)
  ;; ============================================================

  (define %sodium-init
    (foreign-procedure "sodium_init" () int))

  (define %crypto-sign-keypair
    (foreign-procedure "crypto_sign_keypair" (void* void*) int))

  (define %crypto-sign-detached
    (foreign-procedure "crypto_sign_detached"
                       (void* void* void* unsigned-long void*) int))

  (define %crypto-sign-verify-detached
    (foreign-procedure "crypto_sign_verify_detached"
                       (void* void* unsigned-long void*) int))

  (define %crypto-hash-sha256
    (foreign-procedure "crypto_hash_sha256"
                       (void* void* unsigned-long) int))

  (define %crypto-hash-sha512
    (foreign-procedure "crypto_hash_sha512"
                       (void* void* unsigned-long) int))

  (define %crypto-generichash
    (foreign-procedure "crypto_generichash"
                       (void* unsigned-long void* unsigned-long void* unsigned-long) int))

  (define %randombytes-buf
    (foreign-procedure "randombytes_buf" (void* unsigned-long) void))

  (define %randombytes-random
    (foreign-procedure "randombytes_random" () unsigned-32))

  (define %randombytes-uniform
    (foreign-procedure "randombytes_uniform" (unsigned-32) unsigned-32))

  (define %randombytes-implementation-name
    (foreign-procedure "randombytes_implementation_name" () string))

  (define %sodium-memzero
    (foreign-procedure "sodium_memzero" (void* unsigned-long) void))

  (define %crypto-pwhash
    (foreign-procedure "crypto_pwhash"
                       (void* unsigned-long void* unsigned-long void*
                        unsigned-long unsigned-long int) int))

  (define %crypto-secretbox-easy
    (foreign-procedure "crypto_secretbox_easy"
                       (void* void* unsigned-long void* void*) int))

  (define %crypto-secretbox-open-easy
    (foreign-procedure "crypto_secretbox_open_easy"
                       (void* void* unsigned-long void* void*) int))

  (define %crypto-box-keypair
    (foreign-procedure "crypto_box_keypair" (void* void*) int))

  (define %crypto-scalarmult
    (foreign-procedure "crypto_scalarmult" (void* void* void*) int))

  ;; SHAKE256 from our C bridge (if available)
  (define %shake256-hash
    (if *crypto-bridge-loaded*
        (foreign-procedure "shake256_hash"
                           (void* unsigned-long void* unsigned-long) int)
        (lambda (out outlen in inlen)
          (error 'shake256-hash "libcrypto-bridge not loaded (libkeccak unavailable)"))))

  ;; ============================================================
  ;; Constants
  ;; ============================================================

  (define crypto-sign-publickeybytes 32)
  (define crypto-sign-secretkeybytes 64)
  (define crypto-sign-bytes 64)
  (define crypto-hash-sha256-bytes 32)
  (define crypto-hash-sha512-bytes 64)
  (define crypto-generichash-bytes 32)
  (define secretbox-keybytes 32)
  (define secretbox-noncebytes 24)
  (define secretbox-macbytes 16)
  (define x25519-publickeybytes 32)
  (define x25519-secretkeybytes 32)
  (define argon2id-opslimit-moderate 3)
  (define argon2id-memlimit-moderate 268435456) ; 256 MB

  ;; ============================================================
  ;; Bytevector <-> Foreign Memory Helpers
  ;;
  ;; Chez bytevectors are GC-managed and can move during collection.
  ;; We cannot pass interior pointers to C.  Instead:
  ;;   1. foreign-alloc a buffer
  ;;   2. Copy bytevector contents in
  ;;   3. Call C function
  ;;   4. Copy results out
  ;;   5. foreign-free the buffer
  ;; ============================================================

  (define (bytevector->foreign bv)
    "Copy bytevector to foreign-alloc'd memory. Caller must free."
    (let* ((len (bytevector-length bv))
           (ptr (foreign-alloc len)))
      (do ((i 0 (+ i 1)))
          ((= i len) ptr)
        (foreign-set! 'unsigned-8 ptr i (bytevector-u8-ref bv i)))))

  (define (foreign->bytevector ptr len)
    "Copy len bytes from foreign pointer into a new bytevector."
    (let ((bv (make-bytevector len)))
      (do ((i 0 (+ i 1)))
          ((= i len) bv)
        (bytevector-u8-set! bv i (foreign-ref 'unsigned-8 ptr i)))))

  (define (foreign->bytevector! ptr bv len)
    "Copy len bytes from foreign pointer into existing bytevector."
    (do ((i 0 (+ i 1)))
        ((= i len))
      (bytevector-u8-set! bv i (foreign-ref 'unsigned-8 ptr i))))

  ;; ============================================================
  ;; Macro for typical FFI call pattern:
  ;;   allocate foreign buffers, call, copy out, free
  ;; ============================================================

  ;; Helper: ensure data is a bytevector (convert strings)
  (define (ensure-bytevector data)
    (if (string? data) (string->utf8 data) data))

  ;; ============================================================
  ;; Initialize libsodium
  ;; ============================================================

  (define (sodium-init)
    (%sodium-init))

  ;; ============================================================
  ;; Ed25519 Key Generation
  ;; ============================================================

  (define (ed25519-keypair! public-key secret-key)
    "Fill pre-allocated bytevectors with a new Ed25519 keypair."
    (let ((pk-ptr (foreign-alloc 32))
          (sk-ptr (foreign-alloc 64)))
      (let ((result (%crypto-sign-keypair pk-ptr sk-ptr)))
        (foreign->bytevector! pk-ptr public-key 32)
        (foreign->bytevector! sk-ptr secret-key 64)
        (foreign-free pk-ptr)
        (foreign-free sk-ptr)
        result)))

  (define (ed25519-keypair)
    "Generate a new Ed25519 keypair.  Returns (public-key secret-key)."
    (let ((pk (make-bytevector crypto-sign-publickeybytes))
          (sk (make-bytevector crypto-sign-secretkeybytes)))
      (ed25519-keypair! pk sk)
      (list pk sk)))

  (define (ed25519-secret-to-public secret-key)
    "Extract 32-byte public key from 64-byte Ed25519 secret key."
    (let ((pk (make-bytevector crypto-sign-publickeybytes)))
      (do ((i 0 (+ i 1)))
          ((= i crypto-sign-publickeybytes) pk)
        (bytevector-u8-set! pk i (bytevector-u8-ref secret-key (+ i 32))))))

  ;; ============================================================
  ;; Ed25519 Sign / Verify
  ;; ============================================================

  (define (ed25519-sign secret-key message)
    "Sign message with Ed25519. Returns 64-byte signature."
    (let* ((msg (ensure-bytevector message))
           (msg-len (bytevector-length msg))
           (sig (make-bytevector crypto-sign-bytes))
           (sig-ptr (foreign-alloc 64))
           (siglen-ptr (foreign-alloc 8))
           (msg-ptr (bytevector->foreign msg))
           (sk-ptr (bytevector->foreign secret-key)))
      (%crypto-sign-detached sig-ptr siglen-ptr msg-ptr msg-len sk-ptr)
      (foreign->bytevector! sig-ptr sig 64)
      (foreign-free sig-ptr)
      (foreign-free siglen-ptr)
      (foreign-free msg-ptr)
      (foreign-free sk-ptr)
      sig))

  (define (ed25519-verify public-key message signature)
    "Verify Ed25519 signature. Returns #t if valid."
    (let* ((msg (ensure-bytevector message))
           (msg-len (bytevector-length msg))
           (sig-ptr (bytevector->foreign signature))
           (msg-ptr (bytevector->foreign msg))
           (pk-ptr (bytevector->foreign public-key)))
      (let ((result (%crypto-sign-verify-detached sig-ptr msg-ptr msg-len pk-ptr)))
        (foreign-free sig-ptr)
        (foreign-free msg-ptr)
        (foreign-free pk-ptr)
        (= result 0))))

  ;; ============================================================
  ;; Hashing: SHA-256, SHA-512, BLAKE2b, SHAKE256
  ;; ============================================================

  (define (sha256-hash data)
    "Compute SHA-256 hash. Returns 32-byte bytevector."
    (let* ((d (ensure-bytevector data))
           (dlen (bytevector-length d))
           (hash (make-bytevector crypto-hash-sha256-bytes))
           (h-ptr (foreign-alloc 32))
           (d-ptr (bytevector->foreign d)))
      (%crypto-hash-sha256 h-ptr d-ptr dlen)
      (foreign->bytevector! h-ptr hash 32)
      (foreign-free h-ptr)
      (foreign-free d-ptr)
      hash))

  (define (sha512-hash data)
    "Compute SHA-512 hash. Returns 64-byte bytevector."
    (let* ((d (ensure-bytevector data))
           (dlen (bytevector-length d))
           (hash (make-bytevector crypto-hash-sha512-bytes))
           (h-ptr (foreign-alloc 64))
           (d-ptr (bytevector->foreign d)))
      (%crypto-hash-sha512 h-ptr d-ptr dlen)
      (foreign->bytevector! h-ptr hash 64)
      (foreign-free h-ptr)
      (foreign-free d-ptr)
      hash))

  (define (blake2b-hash data)
    "Compute BLAKE2b hash. Returns 32-byte bytevector."
    (let* ((d (ensure-bytevector data))
           (dlen (bytevector-length d))
           (hash (make-bytevector crypto-generichash-bytes))
           (h-ptr (foreign-alloc 32))
           (d-ptr (bytevector->foreign d)))
      (%crypto-generichash h-ptr crypto-generichash-bytes d-ptr dlen 0 0)
      (foreign->bytevector! h-ptr hash 32)
      (foreign-free h-ptr)
      (foreign-free d-ptr)
      hash))

  (define (shake256-hash data . rest)
    "Compute SHAKE256 hash. Optional outlen (default 32)."
    (let* ((outlen (if (null? rest) 32 (car rest)))
           (d (ensure-bytevector data))
           (dlen (bytevector-length d))
           (hash (make-bytevector outlen))
           (h-ptr (foreign-alloc outlen))
           (d-ptr (bytevector->foreign d)))
      (let ((result (%shake256-hash h-ptr outlen d-ptr dlen)))
        (if (= result 0)
            (begin
              (foreign->bytevector! h-ptr hash outlen)
              (foreign-free h-ptr)
              (foreign-free d-ptr)
              hash)
            (begin
              (foreign-free h-ptr)
              (foreign-free d-ptr)
              (error 'shake256-hash "SHAKE256 hash failed"))))))

  ;; ============================================================
  ;; Entropy & Cryptographic Randomness
  ;; ============================================================

  (define (random-bytes n)
    "Generate n cryptographically random bytes."
    (let* ((ptr (foreign-alloc n))
           (bv (make-bytevector n)))
      (%randombytes-buf ptr n)
      (foreign->bytevector! ptr bv n)
      (foreign-free ptr)
      bv))

  (define (random-u8)
    "Generate single random byte [0, 255]."
    (bytevector-u8-ref (random-bytes 1) 0))

  (define (random-u32)
    "Generate random 32-bit unsigned integer."
    (%randombytes-random))

  (define (random-uniform upper-bound)
    "Generate uniform random integer in [0, upper-bound)."
    (%randombytes-uniform upper-bound))

  (define (entropy-status)
    "Get entropy source status as alist."
    (let ((impl (%randombytes-implementation-name)))
      `((implementation . ,impl)
        (source . ,(cond
                    ((string=? impl "sysrandom") "/dev/urandom")
                    ((string=? impl "internal") "ChaCha20 (seeded)")
                    (else "unknown")))
        (status . ok))))

  (define (memzero! bv)
    "Zero sensitive memory."
    (let* ((len (bytevector-length bv))
           (ptr (bytevector->foreign bv)))
      (%sodium-memzero ptr len)
      (foreign->bytevector! ptr bv len)
      (foreign-free ptr)))

  ;; ============================================================
  ;; Argon2id Password Hashing
  ;; ============================================================

  (define (argon2id-hash password salt)
    "Derive 32-byte key from password using Argon2id."
    (let* ((pass (ensure-bytevector password))
           (pass-len (bytevector-length pass))
           (key (make-bytevector secretbox-keybytes))
           (k-ptr (foreign-alloc secretbox-keybytes))
           (p-ptr (bytevector->foreign pass))
           (s-ptr (bytevector->foreign salt)))
      (let ((result (%crypto-pwhash k-ptr secretbox-keybytes
                                    p-ptr pass-len
                                    s-ptr
                                    argon2id-opslimit-moderate
                                    argon2id-memlimit-moderate
                                    2))) ; crypto_pwhash_ALG_ARGON2ID13
        (foreign-free p-ptr)
        (foreign-free s-ptr)
        (if (= result 0)
            (begin
              (foreign->bytevector! k-ptr key secretbox-keybytes)
              (foreign-free k-ptr)
              key)
            (begin
              (foreign-free k-ptr)
              (error 'argon2id-hash "argon2id hash failed"))))))

  ;; ============================================================
  ;; Secretbox (XSalsa20-Poly1305)
  ;; ============================================================

  (define (secretbox-encrypt plaintext nonce key)
    "Encrypt with XSalsa20-Poly1305. Returns ciphertext+MAC."
    (let* ((plen (bytevector-length plaintext))
           (clen (+ plen secretbox-macbytes))
           (ciphertext (make-bytevector clen))
           (c-ptr (foreign-alloc clen))
           (p-ptr (bytevector->foreign plaintext))
           (n-ptr (bytevector->foreign nonce))
           (k-ptr (bytevector->foreign key)))
      (let ((result (%crypto-secretbox-easy c-ptr p-ptr plen n-ptr k-ptr)))
        (foreign-free p-ptr)
        (foreign-free n-ptr)
        (foreign-free k-ptr)
        (if (= result 0)
            (begin
              (foreign->bytevector! c-ptr ciphertext clen)
              (foreign-free c-ptr)
              ciphertext)
            (begin
              (foreign-free c-ptr)
              (error 'secretbox-encrypt "encryption failed"))))))

  (define (secretbox-decrypt ciphertext nonce key)
    "Decrypt with XSalsa20-Poly1305. Returns plaintext or #f."
    (let* ((clen (bytevector-length ciphertext))
           (plen (- clen secretbox-macbytes))
           (plaintext (make-bytevector plen))
           (p-ptr (foreign-alloc plen))
           (c-ptr (bytevector->foreign ciphertext))
           (n-ptr (bytevector->foreign nonce))
           (k-ptr (bytevector->foreign key)))
      (let ((result (%crypto-secretbox-open-easy p-ptr c-ptr clen n-ptr k-ptr)))
        (foreign-free c-ptr)
        (foreign-free n-ptr)
        (foreign-free k-ptr)
        (if (= result 0)
            (begin
              (foreign->bytevector! p-ptr plaintext plen)
              (foreign-free p-ptr)
              plaintext)
            (begin
              (foreign-free p-ptr)
              #f)))))

  ;; Symmetric encryption aliases
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
  ;; X25519 Key Exchange (Memo-039)
  ;; ============================================================

  (define (x25519-keypair)
    "Generate X25519 keypair. Returns (public-key secret-key)."
    (let ((pk (make-bytevector x25519-publickeybytes))
          (sk (make-bytevector x25519-secretkeybytes))
          (pk-ptr (foreign-alloc 32))
          (sk-ptr (foreign-alloc 32)))
      (%crypto-box-keypair pk-ptr sk-ptr)
      (foreign->bytevector! pk-ptr pk 32)
      (foreign->bytevector! sk-ptr sk 32)
      (foreign-free pk-ptr)
      (foreign-free sk-ptr)
      (list pk sk)))

  (define (x25519-scalarmult secret-key public-key)
    "Compute X25519 shared secret. Returns 32-byte bytevector."
    (let ((shared (make-bytevector 32))
          (q-ptr (foreign-alloc 32))
          (sk-ptr (bytevector->foreign secret-key))
          (pk-ptr (bytevector->foreign public-key)))
      (let ((result (%crypto-scalarmult q-ptr sk-ptr pk-ptr)))
        (foreign-free sk-ptr)
        (foreign-free pk-ptr)
        (if (= result 0)
            (begin
              (foreign->bytevector! q-ptr shared 32)
              (foreign-free q-ptr)
              shared)
            (begin
              (foreign-free q-ptr)
              (error 'x25519-scalarmult "scalar multiplication failed"))))))

  ;; ============================================================
  ;; Merkle Trees (Memo-047)
  ;;
  ;; Quantum-resistant object identity using SHAKE256.
  ;; 256-bit classical / 128-bit quantum security.
  ;; Domain separation prevents leaf/node confusion attacks.
  ;; ============================================================

  (define merkle-chunk-size 4096)
  (define merkle-fanout 16)
  (define merkle-hash-len 32)

  ;; Domain separation prefixes
  (define merkle-leaf-prefix (make-bytevector 1 0))   ; 0x00
  (define merkle-node-prefix (make-bytevector 1 1))   ; 0x01

  ;; Bytevector concatenation (blob-append equivalent)
  (define (bv-append . bvs)
    (if (null? bvs)
        (make-bytevector 0)
        (let* ((sizes (map bytevector-length bvs))
               (total (apply + sizes))
               (result (make-bytevector total)))
          (let loop ((rest bvs) (offset 0))
            (if (null? rest)
                result
                (let ((b (car rest))
                      (len (bytevector-length (car rest))))
                  (bytevector-copy! b 0 result offset len)
                  (loop (cdr rest) (+ offset len))))))))

  (define (merkle-hash-leaf chunk)
    "Hash a leaf chunk with domain separation."
    (shake256-hash (bv-append merkle-leaf-prefix chunk)))

  (define (merkle-hash-node children)
    "Hash internal node with domain separation."
    (shake256-hash (apply bv-append (cons merkle-node-prefix children))))

  ;; Split content into chunks
  (define (merkle-chunk content)
    (let ((len (bytevector-length content)))
      (if (= len 0)
          (list (make-bytevector 0))
          (let loop ((offset 0) (acc '()))
            (if (>= offset len)
                (reverse acc)
                (let* ((chunk-len (min merkle-chunk-size (- len offset)))
                       (chunk (make-bytevector chunk-len)))
                  (bytevector-copy! content offset chunk 0 chunk-len)
                  (loop (+ offset merkle-chunk-size) (cons chunk acc))))))))

  ;; Build Merkle tree, return root
  (define (merkle-build-tree leaves)
    (cond
      ((null? leaves) (merkle-hash-leaf (make-bytevector 0)))
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

  (define (merkle-root content)
    "Compute Merkle root -- THE quantum-resistant object identity (Memo-047)."
    (let* ((data (ensure-bytevector content))
           (chunks (merkle-chunk data))
           (leaves (map merkle-hash-leaf chunks)))
      (merkle-build-tree leaves)))

  (define (dual-hash content)
    "Compute both SHA-512 and Merkle root (transition period)."
    (let ((data (ensure-bytevector content)))
      (cons (sha512-hash data) (merkle-root data))))

  ;; ============================================================
  ;; Merkle Inclusion Proofs
  ;; ============================================================

  (define (make-merkle-proof chunk-index chunk-hash path)
    (list 'merkle-proof chunk-index chunk-hash path))

  (define (merkle-proof? x)
    (and (pair? x) (eq? 'merkle-proof (car x))))

  (define (merkle-proof-chunk-index proof) (list-ref proof 1))
  (define (merkle-proof-chunk-hash proof)  (list-ref proof 2))
  (define (merkle-proof-path proof)        (list-ref proof 3))

  ;; Group list into sublists of size n
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

  (define (merkle-prove content chunk-index)
    "Generate inclusion proof for a chunk."
    (let* ((data (ensure-bytevector content))
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

  (define (merkle-bv=? a b)
    (bytevector=? a b))

  (define (merkle-verify-proof root proof)
    "Verify inclusion proof against expected root."
    (if (not (merkle-proof? proof))
        #f
        (let ((chunk-hash (merkle-proof-chunk-hash proof))
              (path (merkle-proof-path proof)))
          (let loop ((current-hash chunk-hash) (remaining-path path))
            (if (null? remaining-path)
                (or (merkle-bv=? current-hash root)
                    (merkle-bv=? (merkle-hash-node (list current-hash)) root))
                (let collect ((path remaining-path)
                              (left-siblings '())
                              (right-siblings '())
                              (count 0))
                  (if (or (null? path) (>= count (- merkle-fanout 1)))
                      (let* ((all-left (reverse left-siblings))
                             (all-right right-siblings)
                             (children (append all-left (list current-hash) all-right))
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
  ;; Shamir Secret Sharing over GF(256)
  ;; ============================================================

  ;; GF(256) tables (precomputed with generator 3, polynomial 0x11b)
  (define gf256-exp (make-bytevector 512))
  (define gf256-log (make-bytevector 256))

  (define (init-gf256-tables!)
    (let ((x 1))
      (do ((i 0 (+ i 1)))
          ((= i 255))
        (bytevector-u8-set! gf256-exp i x)
        (bytevector-u8-set! gf256-log x i)
        (when (< i 254)
          (let* ((x2 (bitwise-arithmetic-shift-left x 1))
                 (x2-reduced (if (>= x2 256)
                                 (bitwise-xor x2 #x11b)
                                 x2)))
            (set! x (bitwise-xor x2-reduced x))))))
    ;; Duplicate exp table for convenience
    (do ((i 255 (+ i 1)))
        ((= i 510))
      (bytevector-u8-set! gf256-exp i (bytevector-u8-ref gf256-exp (- i 255)))))

  ;; Initialize on load
  (init-gf256-tables!)

  (define (gf256-add a b)
    (bitwise-xor a b))

  (define (gf256-mul a b)
    (if (or (= a 0) (= b 0))
        0
        (bytevector-u8-ref gf256-exp
                           (mod (+ (bytevector-u8-ref gf256-log a)
                                   (bytevector-u8-ref gf256-log b))
                                255))))

  (define (gf256-div a b)
    (if (= a 0)
        0
        (bytevector-u8-ref gf256-exp
                           (mod (- (+ (bytevector-u8-ref gf256-log a) 255)
                                   (bytevector-u8-ref gf256-log b))
                                255))))

  (define (gf256-poly-eval coeffs x)
    "Evaluate polynomial at x using Horner's method in GF(256)."
    (let loop ((i (- (length coeffs) 1))
               (result 0))
      (if (< i 0)
          result
          (loop (- i 1)
                (gf256-add (list-ref coeffs i)
                          (gf256-mul result x))))))

  ;; Shamir share record
  (define-record-type shamir-share
    (fields id threshold x y))

  (define (share-id s) (shamir-share-id s))
  (define (share-threshold s) (shamir-share-threshold s))
  (define (share-x s) (shamir-share-x s))
  (define (share-y s) (shamir-share-y s))
  (define (shamir-share? x)
    (and (record? x)
         (eq? (record-type-descriptor x)
              (record-type-descriptor (make-shamir-share 'dummy 0 0 #vu8())))))

  ;; We need a proper predicate -- use a tag instead
  ;; Redefine with a simpler approach using a unique tag
  (define *shamir-share-tag* (list 'shamir-share))

  (define (make-shamir-share-tagged id threshold x y)
    (vector *shamir-share-tag* id threshold x y))

  (define (shamir-share? x)
    (and (vector? x)
         (= (vector-length x) 5)
         (eq? (vector-ref x 0) *shamir-share-tag*)))

  (define (share-id s) (vector-ref s 1))
  (define (share-threshold s) (vector-ref s 2))
  (define (share-x s) (vector-ref s 3))
  (define (share-y s) (vector-ref s 4))

  (define (shamir-split secret . opts)
    "Split secret into N shares, requiring K to reconstruct.
     Usage: (shamir-split secret threshold: 3 total: 5)"
    (let ((threshold (let loop ((r opts))
                       (cond ((null? r) 3)
                             ((null? (cdr r)) 3)
                             ((eq? (car r) 'threshold:) (cadr r))
                             (else (loop (cddr r))))))
          (total (let loop ((r opts))
                   (cond ((null? r) 5)
                         ((null? (cdr r)) 5)
                         ((eq? (car r) 'total:) (cadr r))
                         (else (loop (cddr r)))))))

      (unless (<= threshold total)
        (error 'shamir-split "Threshold must be <= total shares"))
      (unless (> threshold 1)
        (error 'shamir-split "Threshold must be > 1"))

      (let* ((secret-bytes secret)  ; already a bytevector
             (secret-len (bytevector-length secret-bytes))
             (shares (make-vector total)))

        ;; Initialize share y-value vectors
        (do ((i 0 (+ i 1)))
            ((= i total))
          (vector-set! shares i (make-bytevector secret-len)))

        ;; For each byte of the secret
        (do ((byte-idx 0 (+ byte-idx 1)))
            ((= byte-idx secret-len))
          (let ((coeffs (make-vector threshold)))
            (vector-set! coeffs 0 (bytevector-u8-ref secret-bytes byte-idx))
            ;; Cryptographic randomness for polynomial coefficients
            (do ((i 1 (+ i 1)))
                ((= i threshold))
              (vector-set! coeffs i (random-u8)))
            ;; Evaluate at each share's x-value
            (do ((share-num 1 (+ share-num 1)))
                ((> share-num total))
              (bytevector-u8-set! (vector-ref shares (- share-num 1))
                                  byte-idx
                                  (gf256-poly-eval (vector->list coeffs) share-num)))))

        ;; Convert to share records
        (do ((i 0 (+ i 1)))
            ((= i total))
          (vector-set! shares i
                      (make-shamir-share-tagged
                        (string->symbol (string-append "share-" (number->string (+ i 1))))
                        threshold
                        (+ i 1)
                        (vector-ref shares i))))

        (vector->list shares))))

  (define (shamir-reconstruct shares)
    "Reconstruct secret from K or more shares."
    (when (null? shares)
      (error 'shamir-reconstruct "Need at least one share"))

    (let* ((threshold (share-threshold (car shares)))
           (num-shares (length shares)))

      (unless (>= num-shares threshold)
        (error 'shamir-reconstruct
               (string-append "Need at least "
                              (number->string threshold)
                              " shares, got "
                              (number->string num-shares))))

      (let* ((k-shares (list-head shares threshold))
             (share-len (bytevector-length (share-y (car k-shares))))
             (secret (make-bytevector share-len)))

        ;; For each byte position: Lagrange interpolation at x=0
        (do ((byte-idx 0 (+ byte-idx 1)))
            ((= byte-idx share-len))
          (let ((result 0))
            (do ((i 0 (+ i 1)))
                ((= i threshold))
              (let ((xi (share-x (list-ref k-shares i)))
                    (yi (bytevector-u8-ref (share-y (list-ref k-shares i))
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
            (bytevector-u8-set! secret byte-idx result)))

        secret)))

) ;; end library
