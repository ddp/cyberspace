;;; SPKI Scheme - Cryptography FFI to libsodium
;;;
;;; Chicken Scheme bindings to libsodium for Ed25519 signatures.
;;; This provides the same cryptographic operations as the OCaml TCB,
;;; but from Scheme for the policy layer.
;;;
;;; Architecture:
;;;   Chicken Scheme → crypto-ffi.scm → libsodium (same as OCaml TCB)
;;;
;;; The OCaml TCB exists for Rocq verification.
;;; The Scheme FFI exists for policy/tools/human-readable code.
;;; Both use the same underlying cryptography: libsodium Ed25519.

(module crypto-ffi
  (sodium-init
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
   ;; AEAD ChaCha20-Poly1305 (CIP secure channel)
   aead-chacha20poly1305-ietf-encrypt
   aead-chacha20poly1305-ietf-decrypt
   aead-chacha20poly1305-ietf-keybytes
   aead-chacha20poly1305-ietf-npubbytes
   aead-chacha20poly1305-ietf-abytes
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

  (import scheme
          (chicken base)
          (chicken foreign)
          (chicken format)
          (chicken blob)
          (chicken memory)
          (chicken memory representation)
          (chicken bitwise)
          srfi-1   ; list utilities (take)
          srfi-4)
          ;; NOTE: Do NOT import (chicken random) - use libsodium for all cryptographic randomness

  ;; Include libsodium and libkeccak headers
  (foreign-declare "#include <sodium.h>")
  (foreign-declare "#include <libkeccak.h>")

  ;; Constants from libsodium
  (define crypto-sign-publickeybytes 32)
  (define crypto-sign-secretkeybytes 64)
  (define crypto-sign-bytes 64)
  (define crypto-hash-sha256-bytes 32)
  (define crypto-hash-sha512-bytes 64)

  ;; Initialize libsodium
  ;; Returns: 0 on success, -1 on error, 1 if already initialized
  (define sodium-init
    (foreign-lambda int "sodium_init"))

  ;; Generate Ed25519 keypair (mutating version)
  ;; Takes pre-allocated scheme-objects and fills them with keypair
  ;; @param public-key: 32-byte blob (will be filled)
  ;; @param secret-key: 64-byte blob (will be filled)
  ;; @return: 0 on success, -1 on failure
  (define ed25519-keypair!
    (foreign-lambda int "crypto_sign_keypair"
                    scheme-pointer scheme-pointer))

  ;; Generate Ed25519 keypair (allocating version)
  ;; Creates and returns new keypair as blobs
  ;; @return: list of (public-key secret-key) as blobs
  (define (ed25519-keypair)
    (let ((public-key (make-blob crypto-sign-publickeybytes))
          (secret-key (make-blob crypto-sign-secretkeybytes)))
      (ed25519-keypair! public-key secret-key)
      (list public-key secret-key)))

  ;; Extract public key from secret key
  ;; In Ed25519, the 64-byte secret key contains the 32-byte public key at offset 32
  ;; @param secret-key: 64-byte secret key (blob)
  ;; @return: 32-byte public key (blob)
  (define (ed25519-secret-to-public secret-key)
    (let* ((public-key (make-blob crypto-sign-publickeybytes))
           (sk-vec (blob->u8vector/shared secret-key))
           (pk-vec (blob->u8vector/shared public-key)))
      ;; Copy bytes 32-63 from secret key to public key
      (do ((i 0 (+ i 1)))
          ((= i crypto-sign-publickeybytes) public-key)
        (u8vector-set! pk-vec i (u8vector-ref sk-vec (+ i 32))))))

  ;; Sign message with Ed25519
  ;; @param secret-key: 64-byte secret key (blob)
  ;; @param message: message to sign (blob or string)
  ;; @return signature: 64-byte signature (blob)
  (define (ed25519-sign secret-key message)
    (let* ((msg-bytes (if (string? message)
                          (string->blob message)
                          message))
           (signature (make-blob crypto-sign-bytes))
           (sig-len-ptr (make-blob 8)))  ; unsigned long long
      ((foreign-lambda int "crypto_sign_detached"
                      scheme-pointer     ; signature
                      scheme-pointer     ; signature length (out)
                      scheme-pointer     ; message
                      unsigned-integer   ; message length
                      scheme-pointer)    ; secret key
       signature sig-len-ptr msg-bytes (blob-size msg-bytes) secret-key)
      signature))

  ;; Verify Ed25519 signature
  ;; @param public-key: 32-byte public key (blob)
  ;; @param message: message that was signed (blob or string)
  ;; @param signature: 64-byte signature (blob)
  ;; @return #t if valid, #f otherwise
  ;;;
  ;;; TCB CRITICAL: This is the core security guarantee.
  ;;; If this returns #t, the signature was created by holder of the private key.
  (define (ed25519-verify public-key message signature)
    (let* ((msg-bytes (if (string? message)
                          (string->blob message)
                          message))
           (result ((foreign-lambda int "crypto_sign_verify_detached"
                                   scheme-pointer     ; signature
                                   scheme-pointer     ; message
                                   unsigned-integer   ; message length
                                   scheme-pointer)    ; public key
                    signature msg-bytes (blob-size msg-bytes) public-key)))
      ;; crypto_sign_verify_detached returns 0 on success, -1 on failure
      (= result 0)))

  ;; Compute SHA-256 hash
  ;; @param data: data to hash (blob or string)
  ;; @return hash: 32-byte hash (blob)
  (define (sha256-hash data)
    (let* ((data-bytes (if (string? data)
                           (string->blob data)
                           data))
           (hash (make-blob crypto-hash-sha256-bytes)))
      ((foreign-lambda int "crypto_hash_sha256"
                      scheme-pointer     ; hash output
                      scheme-pointer     ; data
                      unsigned-integer)  ; data length
       hash data-bytes (blob-size data-bytes))
      hash))

  ;; Compute SHA-512 hash
  ;; @param data: data to hash (blob or string)
  ;; @return hash: 64-byte hash (blob)
  (define (sha512-hash data)
    (let* ((data-bytes (if (string? data)
                           (string->blob data)
                           data))
           (hash (make-blob crypto-hash-sha512-bytes)))
      ((foreign-lambda int "crypto_hash_sha512"
                      scheme-pointer     ; hash output
                      scheme-pointer     ; data
                      unsigned-integer)  ; data length
       hash data-bytes (blob-size data-bytes))
      hash))

  ;; BLAKE2b constants
  (define crypto-generichash-bytes 32)  ;; Default output size

  ;; Compute BLAKE2b hash
  ;; @param data: data to hash (blob or string)
  ;; @return hash: 32-byte hash (blob)
  ;;
  ;; BLAKE2b is faster than SHA-256 and used for:
  ;; - Content addressing
  ;; - Key derivation
  ;; - Audit trail hashing
  (define (blake2b-hash data)
    (let* ((data-bytes (if (string? data)
                           (string->blob data)
                           data))
           (hash (make-blob crypto-generichash-bytes)))
      ((foreign-lambda int "crypto_generichash"
                      scheme-pointer     ; hash output
                      unsigned-integer   ; hash length
                      scheme-pointer     ; data
                      unsigned-integer   ; data length
                      scheme-pointer     ; key (NULL for unkeyed)
                      unsigned-integer)  ; key length
       hash crypto-generichash-bytes
       data-bytes (blob-size data-bytes)
       #f 0)  ;; No key
      hash))

  ;;; ============================================================================
  ;;; SHAKE256 and Merkle Trees (Memo-047)
  ;;;
  ;;; Quantum-resistant object identity using SHAKE256-based Merkle trees.
  ;;; - 256-bit classical security (pre-image)
  ;;; - 128-bit quantum security (Grover's algorithm)
  ;;; - Domain separation prevents leaf/node confusion attacks
  ;;; ============================================================================

  ;; Canonical Merkle tree parameters
  (define merkle-chunk-size 4096)   ; 4 KB chunks
  (define merkle-fanout 16)         ; Children per internal node
  (define merkle-hash-len 32)       ; 256-bit output

  ;; Domain separation prefixes
  (define merkle-leaf-prefix (string->blob "\x00"))
  (define merkle-node-prefix (string->blob "\x01"))

  ;; SHAKE256 via libkeccak (low-level C helper)
  (foreign-declare "
#include <stdlib.h>
#include <string.h>

/* SHAKE256 hash with specified output length */
static int shake256_hash_c(unsigned char *out, size_t outlen,
                           const unsigned char *in, size_t inlen) {
    struct libkeccak_spec spec;
    struct libkeccak_state state;

    libkeccak_spec_shake(&spec, 256, (long)(outlen * 8));

    if (libkeccak_state_initialise(&state, &spec) != 0)
        return -1;

    if (libkeccak_digest(&state, (const char*)in, inlen, 0,
                         LIBKECCAK_SHAKE_SUFFIX, NULL) != 0) {
        libkeccak_state_wipe(&state);
        return -1;
    }

    libkeccak_squeeze(&state, (char*)out);
    libkeccak_state_wipe(&state);
    return 0;
}
")

  ;; Compute SHAKE256 hash
  ;; @param data: data to hash (blob or string)
  ;; @param outlen: output length in bytes (default 32)
  ;; @return hash: outlen-byte hash (blob)
  ;;
  ;; SHAKE256 is a FIPS 202 XOF (extendable output function) used for:
  ;; - Quantum-resistant Merkle trees
  ;; - Post-quantum signature schemes (SLH-DSA)
  (define (shake256-hash data #!optional (outlen 32))
    (let* ((data-bytes (if (string? data)
                           (string->blob data)
                           data))
           (hash (make-blob outlen)))
      (if (= 0 ((foreign-lambda int "shake256_hash_c"
                                scheme-pointer unsigned-integer
                                scheme-pointer unsigned-integer)
                hash outlen
                data-bytes (blob-size data-bytes)))
          hash
          (error "SHAKE256 hash failed"))))

  ;; Hash a leaf chunk with domain separation
  ;; @param chunk: raw chunk data (blob)
  ;; @return: 32-byte SHAKE256 hash with leaf domain prefix
  (define (merkle-hash-leaf chunk)
    (let ((prefixed (blob-append merkle-leaf-prefix chunk)))
      (shake256-hash prefixed)))

  ;; Hash internal node with domain separation
  ;; @param children: list of child hashes (each 32-byte blob)
  ;; @return: 32-byte SHAKE256 hash with node domain prefix
  (define (merkle-hash-node children)
    (let ((concat (apply blob-append (cons merkle-node-prefix children))))
      (shake256-hash concat)))

  ;; Append blobs together
  (define (blob-append . blobs)
    (let* ((total-size (apply + (map blob-size blobs)))
           (result (make-blob total-size)))
      (let loop ((blobs blobs) (offset 0))
        (if (null? blobs)
            result
            (let* ((b (car blobs))
                   (len (blob-size b)))
              (move-memory! b result len 0 offset)
              (loop (cdr blobs) (+ offset len)))))))

  ;; Split content into chunks
  ;; @param content: raw content (blob)
  ;; @return: list of chunks (each up to merkle-chunk-size bytes)
  (define (merkle-chunk content)
    (let ((len (blob-size content)))
      (if (= len 0)
          (list (make-blob 0))  ; Empty content = single empty chunk
          (let loop ((offset 0) (acc '()))
            (if (>= offset len)
                (reverse acc)
                (let* ((chunk-len (min merkle-chunk-size (- len offset)))
                       (chunk (make-blob chunk-len)))
                  (move-memory! content chunk chunk-len offset 0)
                  (loop (+ offset merkle-chunk-size) (cons chunk acc))))))))

  ;; Build Merkle tree from leaves, return root
  ;; @param leaves: list of leaf hashes
  ;; @return: root hash (32-byte blob)
  (define (merkle-build-tree leaves)
    (cond
      ((null? leaves) (merkle-hash-leaf (make-blob 0)))
      ((null? (cdr leaves)) (car leaves))  ; Single node is root
      (else
       ;; Group into chunks of fanout size
       (let loop ((nodes leaves) (groups '()) (current '()) (count 0))
         (cond
           ((null? nodes)
            (let ((final-groups (if (null? current)
                                    (reverse groups)
                                    (reverse (cons (reverse current) groups)))))
              ;; Hash each group to create parent level
              (let ((parents (map merkle-hash-node final-groups)))
                (merkle-build-tree parents))))
           ((>= count merkle-fanout)
            (loop nodes (cons (reverse current) groups) '() 0))
           (else
            (loop (cdr nodes) groups (cons (car nodes) current) (+ count 1))))))))

  ;; Compute Merkle root of content
  ;; @param content: raw content (blob or string)
  ;; @return: 32-byte Merkle root hash
  ;;
  ;; This is THE quantum-resistant object identity function (Memo-047).
  (define (merkle-root content)
    (let* ((data (if (string? content)
                     (string->blob content)
                     content))
           (chunks (merkle-chunk data))
           (leaves (map merkle-hash-leaf chunks)))
      (merkle-build-tree leaves)))

  ;; Compute both legacy SHA-512 and Merkle root (dual-hash transition)
  ;; @param content: raw content (blob or string)
  ;; @return: (sha512-hash . merkle-root) pair
  ;;
  ;; During transition period (Memo-047 Phase 1), objects carry both hashes.
  ;; Old clients use SHA-512, new clients use Merkle root.
  (define (dual-hash content)
    (let ((data (if (string? content)
                    (string->blob content)
                    content)))
      (cons (sha512-hash data) (merkle-root data))))

  ;;; ============================================================================
  ;;; Merkle Inclusion Proofs (Selective Disclosure)
  ;;;
  ;;; Prove a chunk exists in an object without revealing other chunks.
  ;;; Used for streaming verification and privacy-preserving data sharing.
  ;;; ============================================================================

  ;; Merkle proof structure: (chunk-index chunk-hash path)
  ;; where path is list of (sibling-hash . position) pairs
  ;; position is 'left or 'right

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
  ;; @param leaves: list of leaf hashes
  ;; @return: list of levels, from leaves (level 0) to root
  (define (merkle-build-full-tree leaves)
    (let loop ((levels '()) (current leaves))
      (cond
        ((null? current) (reverse levels))
        ((null? (cdr current)) (reverse (cons current levels)))
        (else
         (let ((groups (group-by-n current merkle-fanout)))
           (let ((parents (map merkle-hash-node groups)))
             (loop (cons current levels) parents)))))))

  ;; Helper: group list into sublists of size n
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
  ;; @param content: full content (blob or string)
  ;; @param chunk-index: index of chunk to prove (0-based)
  ;; @return: merkle-proof or #f if index out of bounds
  ;;
  ;; The proof contains siblings along the path from leaf to root.
  ;; Verifier can reconstruct path to root without seeing other chunks.
  (define (merkle-prove content chunk-index)
    (let* ((data (if (string? content) (string->blob content) content))
           (chunks (merkle-chunk data))
           (num-chunks (length chunks)))
      (if (or (< chunk-index 0) (>= chunk-index num-chunks))
          #f  ; Invalid index
          (let* ((leaves (map merkle-hash-leaf chunks))
                 (levels (merkle-build-full-tree leaves))
                 (chunk-hash (list-ref leaves chunk-index)))
            ;; Walk up tree, collecting siblings
            (let loop ((idx chunk-index) (level-idx 0) (path '()))
              (if (>= level-idx (- (length levels) 1))
                  (make-merkle-proof chunk-index chunk-hash (reverse path))
                  (let* ((level (list-ref levels level-idx))
                         (group-idx (quotient idx merkle-fanout))
                         (pos-in-group (remainder idx merkle-fanout))
                         (group-start (* group-idx merkle-fanout))
                         (group-end (min (+ group-start merkle-fanout) (length level))))
                    ;; Collect siblings in this group
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

  ;; Verify inclusion proof
  ;; @param root: expected Merkle root (32-byte blob)
  ;; @param proof: merkle-proof from merkle-prove
  ;; @return: #t if proof is valid, #f otherwise
  ;;
  ;; Reconstructs path from leaf to root using siblings in proof.
  (define (merkle-verify-proof root proof)
    (if (not (merkle-proof? proof))
        #f
        (let ((chunk-hash (merkle-proof-chunk-hash proof))
              (path (merkle-proof-path proof)))
          ;; Group siblings by level and verify path to root
          (let loop ((current-hash chunk-hash) (remaining-path path))
            (if (null? remaining-path)
                ;; Reached end - check against root
                (or (merkle-blob=? current-hash root)
                    (merkle-blob=? (merkle-hash-node (list current-hash)) root))
                ;; Collect siblings for this level, hash together
                (let collect ((path remaining-path)
                              (left-siblings '())
                              (right-siblings '())
                              (count 0))
                  (if (or (null? path) (>= count (- merkle-fanout 1)))
                      ;; Hash this level
                      (let* ((all-left (reverse left-siblings))
                             (all-right right-siblings)
                             (children (append all-left
                                               (list current-hash)
                                               all-right))
                             (parent (merkle-hash-node children)))
                        (loop parent path))
                      ;; Accumulate sibling
                      (let* ((sibling (car path))
                             (hash (car sibling))
                             (pos (cdr sibling)))
                        (if (eq? pos 'left)
                            (collect (cdr path) (cons hash left-siblings)
                                     right-siblings (+ count 1))
                            (collect (cdr path) left-siblings
                                     (cons hash right-siblings) (+ count 1)))))))))))

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

  ;;; ============================================================================
  ;;; Vault Cryptography (Memo-041)
  ;;; ============================================================================

  ;; Constants for secretbox (XSalsa20-Poly1305)
  (define secretbox-keybytes 32)
  (define secretbox-noncebytes 24)
  (define secretbox-macbytes 16)

  ;; Constants for X25519
  (define x25519-publickeybytes 32)
  (define x25519-secretkeybytes 32)

  ;; Constants for Argon2id
  (define argon2id-opslimit-moderate 3)
  (define argon2id-memlimit-moderate 268435456)  ; 256 MB

  ;; ============================================================
  ;; Entropy & Cryptographic Randomness
  ;; ============================================================
  ;;
  ;; All randomness from libsodium's randombytes API which:
  ;;   - Uses /dev/urandom on Unix, CryptGenRandom on Windows
  ;;   - Automatically reseeds from system entropy
  ;;   - Safe for key generation, nonces, IVs
  ;;
  ;; NEVER use chicken:random or pseudo-random-integer for crypto!

  ;; Generate random bytes
  ;; @param n: number of bytes
  ;; @return: blob of n random bytes
  (define (random-bytes n)
    (let ((buf (make-blob n)))
      ((foreign-lambda void "randombytes_buf"
                      scheme-pointer
                      unsigned-integer)
       buf n)
      buf))

  ;; Generate single random byte [0, 255]
  ;; @return: integer in range [0, 255]
  (define (random-u8)
    (let ((buf (make-blob 1)))
      ((foreign-lambda void "randombytes_buf"
                      scheme-pointer
                      unsigned-integer)
       buf 1)
      (blob->u8vector/shared buf)
      (u8vector-ref (blob->u8vector/shared buf) 0)))

  ;; Generate random 32-bit unsigned integer
  ;; @return: integer in range [0, 2^32-1]
  (define (random-u32)
    ((foreign-lambda unsigned-int32 "randombytes_random")))

  ;; Generate uniform random integer in range [0, upper_bound)
  ;; Uses rejection sampling to avoid modulo bias
  ;; @param upper-bound: exclusive upper bound
  ;; @return: integer in range [0, upper_bound)
  (define (random-uniform upper-bound)
    ((foreign-lambda unsigned-int32 "randombytes_uniform" unsigned-int32)
     upper-bound))

  ;; Get entropy source status
  ;; @return: alist with entropy info
  (define (entropy-status)
    (let ((impl ((foreign-lambda c-string "randombytes_implementation_name"))))
      `((implementation . ,impl)
        (source . ,(cond
                    ((string=? impl "sysrandom") "/dev/urandom")
                    ((string=? impl "internal") "ChaCha20 (seeded)")
                    (else "unknown")))
        (status . ok))))

  ;; Zero memory (for sensitive data)
  ;; @param buf: blob to zero
  (define (memzero! buf)
    ((foreign-lambda void "sodium_memzero"
                    scheme-pointer
                    unsigned-integer)
     buf (blob-size buf)))

  ;; Argon2id password hash
  ;; @param password: password string or blob
  ;; @param salt: 16-byte salt blob
  ;; @return: 32-byte derived key blob
  (define (argon2id-hash password salt)
    (let* ((pass-bytes (if (string? password)
                           (string->blob password)
                           password))
           (key (make-blob secretbox-keybytes)))
      (let ((result
             ((foreign-lambda int "crypto_pwhash"
                             scheme-pointer     ; out (key)
                             unsigned-integer   ; outlen
                             scheme-pointer     ; passwd
                             unsigned-integer   ; passwdlen
                             scheme-pointer     ; salt
                             unsigned-integer   ; opslimit
                             unsigned-integer   ; memlimit
                             int)               ; alg
              key secretbox-keybytes
              pass-bytes (blob-size pass-bytes)
              salt
              argon2id-opslimit-moderate
              argon2id-memlimit-moderate
              2)))  ; crypto_pwhash_ALG_ARGON2ID13
        (if (= result 0)
            key
            (error "argon2id-hash failed")))))

  ;; Secretbox encrypt (XSalsa20-Poly1305)
  ;; @param plaintext: data to encrypt (blob)
  ;; @param nonce: 24-byte nonce (blob)
  ;; @param key: 32-byte key (blob)
  ;; @return: ciphertext blob (plaintext-len + 16 bytes MAC)
  (define (secretbox-encrypt plaintext nonce key)
    (let* ((plen (blob-size plaintext))
           (ciphertext (make-blob (+ plen secretbox-macbytes))))
      (let ((result
             ((foreign-lambda int "crypto_secretbox_easy"
                             scheme-pointer     ; ciphertext
                             scheme-pointer     ; plaintext
                             unsigned-integer   ; plaintext length
                             scheme-pointer     ; nonce
                             scheme-pointer)    ; key
              ciphertext plaintext plen nonce key)))
        (if (= result 0)
            ciphertext
            (error "secretbox-encrypt failed")))))

  ;; Secretbox decrypt (XSalsa20-Poly1305)
  ;; @param ciphertext: encrypted data (blob)
  ;; @param nonce: 24-byte nonce (blob)
  ;; @param key: 32-byte key (blob)
  ;; @return: plaintext blob or #f if authentication failed
  (define (secretbox-decrypt ciphertext nonce key)
    (let* ((clen (blob-size ciphertext))
           (plaintext (make-blob (- clen secretbox-macbytes))))
      (let ((result
             ((foreign-lambda int "crypto_secretbox_open_easy"
                             scheme-pointer     ; plaintext
                             scheme-pointer     ; ciphertext
                             unsigned-integer   ; ciphertext length
                             scheme-pointer     ; nonce
                             scheme-pointer)    ; key
              plaintext ciphertext clen nonce key)))
        (if (= result 0)
            plaintext
            #f))))  ; Authentication failed

  ;;; ============================================================================
  ;;; Symmetric Encryption Aliases
  ;;; ============================================================================
  ;;;
  ;;; Multiple vocabularies for the same operation (XSalsa20-Poly1305).
  ;;; Choose the terminology that fits your mental model.
  ;;;

  ;; General purpose
  (define seal secretbox-encrypt)
  (define unseal secretbox-decrypt)

  ;; Classical cryptography
  (define encipher secretbox-encrypt)
  (define decipher secretbox-decrypt)

  ;; Concealment
  (define shroud secretbox-encrypt)
  (define unshroud secretbox-decrypt)

  ;; Protective barrier
  (define ward secretbox-encrypt)
  (define unward secretbox-decrypt)

  ;; Hidden from view
  (define veil secretbox-encrypt)
  (define unveil secretbox-decrypt)

  ;; Key relationship
  (define entrust secretbox-encrypt)
  (define recover secretbox-decrypt)

  ;;; ============================================================================
  ;;; X25519 Key Exchange (Memo-039 Network Encryption)
  ;;; ============================================================================

  ;; Generate X25519 keypair
  ;; @return: list of (public-key secret-key) as blobs
  (define (x25519-keypair)
    (let ((public-key (make-blob x25519-publickeybytes))
          (secret-key (make-blob x25519-secretkeybytes)))
      ((foreign-lambda int "crypto_box_keypair"
                      scheme-pointer
                      scheme-pointer)
       public-key secret-key)
      (list public-key secret-key)))

  ;; X25519 scalar multiplication (compute shared secret)
  ;; @param secret-key: our secret key (32 bytes)
  ;; @param public-key: their public key (32 bytes)
  ;; @return: 32-byte shared secret blob
  (define (x25519-scalarmult secret-key public-key)
    (let ((shared (make-blob 32)))
      (let ((result
             ((foreign-lambda int "crypto_scalarmult"
                             scheme-pointer     ; shared secret
                             scheme-pointer     ; secret key
                             scheme-pointer)    ; public key
              shared secret-key public-key)))
        (if (= result 0)
            shared
            (error "x25519-scalarmult failed")))))

  ;;; ============================================================================
  ;;; AEAD ChaCha20-Poly1305 (CIP Secure Channel)
  ;;; ============================================================================

  ;; Constants for AEAD
  (define aead-chacha20poly1305-ietf-keybytes 32)
  (define aead-chacha20poly1305-ietf-npubbytes 12)
  (define aead-chacha20poly1305-ietf-abytes 16)

  ;; AEAD encrypt (ChaCha20-Poly1305 IETF)
  ;; @param plaintext: data to encrypt (blob)
  ;; @param ad: additional data to authenticate (blob or #f for none)
  ;; @param nonce: 12-byte nonce (blob)
  ;; @param key: 32-byte key (blob)
  ;; @return: ciphertext blob (plaintext-len + 16 bytes tag)
  (define (aead-chacha20poly1305-ietf-encrypt plaintext ad nonce key)
    (let* ((plen (blob-size plaintext))
           (ciphertext (make-blob (+ plen aead-chacha20poly1305-ietf-abytes)))
           (clen-buf (make-blob 8))  ; unsigned long long
           (ad-ptr (if ad ad #f))
           (ad-len (if ad (blob-size ad) 0)))
      (let ((result
             ((foreign-lambda int "crypto_aead_chacha20poly1305_ietf_encrypt"
                             scheme-pointer     ; ciphertext
                             scheme-pointer     ; ciphertext_len (out)
                             scheme-pointer     ; plaintext
                             unsigned-integer   ; plaintext length
                             scheme-pointer     ; ad
                             unsigned-integer   ; ad length
                             scheme-pointer     ; nsec (NULL)
                             scheme-pointer     ; nonce
                             scheme-pointer)    ; key
              ciphertext clen-buf plaintext plen ad-ptr ad-len #f nonce key)))
        (if (= result 0)
            ciphertext
            (error "aead-chacha20poly1305-ietf-encrypt failed")))))

  ;; AEAD decrypt (ChaCha20-Poly1305 IETF)
  ;; @param ciphertext: encrypted data with tag (blob)
  ;; @param ad: additional data that was authenticated (blob or #f for none)
  ;; @param nonce: 12-byte nonce (blob)
  ;; @param key: 32-byte key (blob)
  ;; @return: plaintext blob or #f if authentication failed
  (define (aead-chacha20poly1305-ietf-decrypt ciphertext ad nonce key)
    (let* ((clen (blob-size ciphertext))
           (plaintext (make-blob (- clen aead-chacha20poly1305-ietf-abytes)))
           (mlen-buf (make-blob 8))  ; unsigned long long
           (ad-ptr (if ad ad #f))
           (ad-len (if ad (blob-size ad) 0)))
      (let ((result
             ((foreign-lambda int "crypto_aead_chacha20poly1305_ietf_decrypt"
                             scheme-pointer     ; plaintext
                             scheme-pointer     ; plaintext_len (out)
                             scheme-pointer     ; nsec (NULL)
                             scheme-pointer     ; ciphertext
                             unsigned-integer   ; ciphertext length
                             scheme-pointer     ; ad
                             unsigned-integer   ; ad length
                             scheme-pointer     ; nonce
                             scheme-pointer)    ; key
              plaintext mlen-buf #f ciphertext clen ad-ptr ad-len nonce key)))
        (if (= result 0)
            plaintext
            #f))))  ; Authentication failed

  ;;; ============================================================================
  ;;; Helper Functions
  ;;; ============================================================================

  ;; Helper: convert string to u8vector
  (define (string->u8vector str)
    (let* ((len (string-length str))
           (vec (make-u8vector len)))
      (do ((i 0 (+ i 1)))
          ((= i len) vec)
        (u8vector-set! vec i (char->integer (string-ref str i))))))

  ;; Helper: convert u8vector to hex string
  (define (u8vector->hex vec)
    (let ((len (u8vector-length vec)))
      (let loop ((i 0) (acc '()))
        (if (= i len)
            (apply string-append (reverse acc))
            (loop (+ i 1)
                  (cons (sprintf "~x" (u8vector-ref vec i)) acc))))))

  ;;; ============================================================================
  ;;; Shamir Secret Sharing (GF(256))
  ;;; ============================================================================

  ;; GF(256) arithmetic tables (precomputed for efficiency)
  ;; Using polynomial x^8 + x^4 + x^3 + x + 1 (0x11b)

  (define gf256-exp (make-u8vector 512))
  (define gf256-log (make-u8vector 256))

  (define (init-gf256-tables!)
    "Initialize GF(256) logarithm and exponential tables using generator 3"
    (let ((x 1))
      ;; GF(256) multiplicative group has 255 elements
      ;; Using generator 3 (not 2!) with polynomial 0x11b
      ;; 3^255 = 1, so we stop at i=254 to avoid overwriting log[1]
      (do ((i 0 (+ i 1)))
          ((= i 255))
        (u8vector-set! gf256-exp i x)
        (u8vector-set! gf256-log x i)
        ;; x = x * 3 in GF(256)
        (when (< i 254)
          ;; Multiply by 3 = multiply by 2, then XOR with original
          (let* ((x2 (arithmetic-shift x 1))
                 (x2-reduced (if (>= x2 256)
                                 (bitwise-xor x2 #x11b)
                                 x2)))
            (set! x (bitwise-xor x2-reduced x))))))
    ;; Duplicate exp table for convenience
    (do ((i 255 (+ i 1)))
        ((= i 510))
      (u8vector-set! gf256-exp i (u8vector-ref gf256-exp (- i 255)))))

  ;; Initialize tables on module load
  (init-gf256-tables!)

  (define (gf256-add a b)
    "Add two elements in GF(256)"
    (bitwise-xor a b))

  (define (gf256-mul a b)
    "Multiply two elements in GF(256)"
    (if (or (= a 0) (= b 0))
        0
        (u8vector-ref gf256-exp
                     (modulo (+ (u8vector-ref gf256-log a)
                               (u8vector-ref gf256-log b))
                            255))))

  (define (gf256-div a b)
    "Divide a by b in GF(256)"
    (if (= a 0)
        0
        (u8vector-ref gf256-exp
                     (modulo (- (+ (u8vector-ref gf256-log a) 255)
                               (u8vector-ref gf256-log b))
                            255))))

  (define (gf256-poly-eval coeffs x)
    "Evaluate polynomial at x using Horner's method in GF(256)"
    (let loop ((i (- (length coeffs) 1))
               (result 0))
      (if (< i 0)
          result
          (loop (- i 1)
                (gf256-add (list-ref coeffs i)
                          (gf256-mul result x))))))

  ;; Share record type
  (define-record-type <shamir-share>
    (make-shamir-share-internal id threshold x y)
    shamir-share?
    (id share-id)
    (threshold share-threshold)
    (x share-x)
    (y share-y))

  (define (shamir-split secret #!key (threshold 3) (total 5))
    "Split secret into N shares, requiring K to reconstruct

     secret: blob (e.g., Ed25519 private key)
     threshold: minimum shares needed (K)
     total: total shares to create (N)

     Returns: list of N shares"

    (unless (<= threshold total)
      (error "Threshold must be <= total shares"))

    (unless (> threshold 1)
      (error "Threshold must be > 1"))

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
          ;; pseudo-random-integer is NOT secure for secret sharing!
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
                    (make-shamir-share-internal
                      (string->symbol (string-append "share-" (number->string (+ i 1))))
                      threshold
                      (+ i 1)
                      (u8vector->blob (vector-ref shares i)))))

      (vector->list shares)))

  (define (shamir-reconstruct shares)
    "Reconstruct secret from K or more shares

     shares: list of share records

     Returns: reconstructed secret (blob)"

    (when (null? shares)
      (error "Need at least one share"))

    (let* ((threshold (share-threshold (car shares)))
           (num-shares (length shares)))

      (unless (>= num-shares threshold)
        (error (sprintf "Need at least ~a shares, got ~a" threshold num-shares)))

      ;; Take exactly K shares
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

                ;; Compute Lagrange basis polynomial at x=0
                (let ((basis 1))
                  (do ((j 0 (+ j 1)))
                      ((= j threshold))
                    (when (not (= i j))
                      (let ((xj (share-x (list-ref k-shares j))))
                        ;; basis *= (0 - xj) / (xi - xj)
                        ;; In GF(256): basis *= xj / (xi ^ xj)
                        (set! basis (gf256-mul basis
                                              (gf256-div xj
                                                        (gf256-add xi xj)))))))

                  ;; result += yi * basis
                  (set! result (gf256-add result (gf256-mul yi basis))))))

            (u8vector-set! secret byte-idx result)))

        (u8vector->blob secret))))

  ) ;; end module

;;;
;;; TCB Properties (same as OCaml TCB):
;;;
;;; 1. Signature correctness:
;;;    For all keypairs and messages,
;;;    (ed25519-verify pk msg (ed25519-sign sk msg)) = #t
;;;
;;; 2. Unforgeability:
;;;    If (ed25519-verify pk msg sig) = #t, then
;;;    sig was created by the holder of the corresponding secret key
;;;
;;; 3. Constant-time:
;;;    All operations are constant-time (libsodium guarantee)
;;;
