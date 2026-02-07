;;; Crypto FFI Test Suite
;;; Library of Cyberspace - Chez Port
;;;
;;; Tests Ed25519, SHA-256/512, BLAKE2b, SHAKE256, secretbox,
;;; X25519, Merkle trees, and Shamir secret sharing.

(import (rnrs)
        (only (chezscheme) printf format with-output-to-string
              time void)
        (cyberspace crypto-ffi))

;; ============================================================
;; Test harness (same pattern as test-compat-sexp.ss)
;; ============================================================

(define *pass* 0)
(define *fail* 0)

(define (check name ok?)
  (if ok?
      (begin
        (printf "  pass ~a\n" name)
        (set! *pass* (+ *pass* 1)))
      (begin
        (printf "  FAIL ~a\n" name)
        (set! *fail* (+ *fail* 1)))))

(define (bytevector->hex bv)
  (let ((len (bytevector-length bv)))
    (let loop ((i 0) (acc '()))
      (if (= i len)
          (apply string-append (reverse acc))
          (let* ((b (bytevector-u8-ref bv i))
                 (hi (div b 16))
                 (lo (mod b 16))
                 (hex-char (lambda (n) (string-ref "0123456789abcdef" n))))
            (loop (+ i 1)
                  (cons (string (hex-char hi) (hex-char lo)) acc)))))))

;; ============================================================
;; Tests
;; ============================================================

(printf "\n=== Crypto FFI Test Suite ===\n\n")

;; --- Init ---
(printf "--- Sodium Init ---\n")
(let ((result (sodium-init)))
  (check "sodium-init" (or (= result 0) (= result 1))))

;; --- Ed25519 ---
(printf "\n--- Ed25519 ---\n")

(let* ((kp (ed25519-keypair))
       (pk (car kp))
       (sk (cadr kp)))
  (check "keypair sizes" (and (= (bytevector-length pk) 32)
                              (= (bytevector-length sk) 64)))

  ;; Sign and verify
  (let ((sig (ed25519-sign sk "hello cyberspace")))
    (check "sign produces 64 bytes" (= (bytevector-length sig) 64))
    (check "verify valid signature" (ed25519-verify pk "hello cyberspace" sig))
    (check "reject wrong message" (not (ed25519-verify pk "wrong message" sig))))

  ;; Extract public key from secret key
  (let ((pk2 (ed25519-secret-to-public sk)))
    (check "secret-to-public" (bytevector=? pk pk2)))

  ;; Verify with bytevector message
  (let* ((msg (string->utf8 "bytevector message"))
         (sig (ed25519-sign sk msg)))
    (check "sign/verify bytevector" (ed25519-verify pk msg sig))))

;; --- Hashing ---
(printf "\n--- Hashing ---\n")

;; SHA-256 known answer test
(let ((h (sha256-hash "abc")))
  (check "sha256 length" (= (bytevector-length h) 32))
  (check "sha256 KAT"
    (string=? (bytevector->hex h)
              "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")))

;; SHA-512 known answer test
(let ((h (sha512-hash "abc")))
  (check "sha512 length" (= (bytevector-length h) 64))
  (check "sha512 KAT prefix"
    (string=? (substring (bytevector->hex h) 0 16)
              "ddaf35a193617aba")))

;; BLAKE2b
(let ((h (blake2b-hash "test")))
  (check "blake2b length" (= (bytevector-length h) 32))
  ;; Different inputs should produce different hashes
  (let ((h2 (blake2b-hash "test2")))
    (check "blake2b different inputs" (not (bytevector=? h h2)))))

;; SHA-256 deterministic
(let ((h1 (sha256-hash "deterministic"))
      (h2 (sha256-hash "deterministic")))
  (check "sha256 deterministic" (bytevector=? h1 h2)))

;; --- Randomness ---
(printf "\n--- Randomness ---\n")

(let ((rb (random-bytes 32)))
  (check "random-bytes length" (= (bytevector-length rb) 32))
  ;; Very unlikely to be all zeros
  (check "random-bytes non-zero"
    (not (= 0 (apply + (map (lambda (i) (bytevector-u8-ref rb i))
                            (iota 32)))))))

(let ((b (random-u8)))
  (check "random-u8 range" (and (>= b 0) (<= b 255))))

(let ((u (random-u32)))
  (check "random-u32" (and (>= u 0) (<= u 4294967295))))

(let ((u (random-uniform 100)))
  (check "random-uniform range" (and (>= u 0) (< u 100))))

(let ((status (entropy-status)))
  (check "entropy-status alist"
    (and (pair? status)
         (assq 'status status)
         (eq? (cdr (assq 'status status)) 'ok))))

;; --- Secretbox ---
(printf "\n--- Secretbox (XSalsa20-Poly1305) ---\n")

(let* ((key (random-bytes secretbox-keybytes))
       (nonce (random-bytes secretbox-noncebytes))
       (plaintext (string->utf8 "Peace for all mankind"))
       (ciphertext (secretbox-encrypt plaintext nonce key)))
  (check "ciphertext length" (= (bytevector-length ciphertext)
                                 (+ (bytevector-length plaintext) 16)))
  (let ((decrypted (secretbox-decrypt ciphertext nonce key)))
    (check "decrypt roundtrip" (bytevector=? decrypted plaintext)))

  ;; Wrong key should fail
  (let* ((wrong-key (random-bytes secretbox-keybytes))
         (result (secretbox-decrypt ciphertext nonce wrong-key)))
    (check "wrong key fails" (eq? result #f)))

  ;; Aliases work
  (let ((ct2 (seal plaintext nonce key)))
    (check "seal alias" (bytevector=? (unseal ct2 nonce key) plaintext)))
  (let ((ct3 (encipher plaintext nonce key)))
    (check "encipher alias" (bytevector=? (decipher ct3 nonce key) plaintext))))

;; --- X25519 ---
(printf "\n--- X25519 Key Exchange ---\n")

(let* ((alice (x25519-keypair))
       (bob (x25519-keypair))
       (alice-pk (car alice))
       (alice-sk (cadr alice))
       (bob-pk (car bob))
       (bob-sk (cadr bob)))
  (check "x25519 key sizes" (and (= (bytevector-length alice-pk) 32)
                                  (= (bytevector-length alice-sk) 32)))
  ;; Shared secret should be the same from both sides
  (let ((shared-a (x25519-scalarmult alice-sk bob-pk))
        (shared-b (x25519-scalarmult bob-sk alice-pk)))
    (check "x25519 shared secret agreement" (bytevector=? shared-a shared-b))
    (check "shared secret 32 bytes" (= (bytevector-length shared-a) 32))))

;; --- SHAKE256 ---
(printf "\n--- SHAKE256 ---\n")

(guard (exn
  [#t (printf "  skip SHAKE256 (libkeccak not available)\n")])
  (let ((h (shake256-hash "test")))
    (check "shake256 length" (= (bytevector-length h) 32))
    ;; Variable output length
    (let ((h64 (shake256-hash "test" 64)))
      (check "shake256 variable output" (= (bytevector-length h64) 64)))
    ;; Deterministic
    (let ((h2 (shake256-hash "test")))
      (check "shake256 deterministic" (bytevector=? h h2)))))

;; --- Merkle Trees ---
(printf "\n--- Merkle Trees (Memo-047) ---\n")

(guard (exn
  [#t (printf "  skip Merkle trees (requires SHAKE256)\n")])

  ;; Small content
  (let ((root (merkle-root "hello")))
    (check "merkle-root produces 32 bytes" (= (bytevector-length root) 32))
    ;; Deterministic
    (let ((root2 (merkle-root "hello")))
      (check "merkle-root deterministic" (bytevector=? root root2)))
    ;; Different content -> different root
    (let ((root3 (merkle-root "world")))
      (check "merkle-root different input" (not (bytevector=? root root3)))))

  ;; Dual hash
  (let ((dh (dual-hash "test content")))
    (check "dual-hash pair" (pair? dh))
    (check "dual-hash sha512" (= (bytevector-length (car dh)) 64))
    (check "dual-hash merkle" (= (bytevector-length (cdr dh)) 32)))

  ;; Merkle proof
  (let* ((content "Hello, Merkle!")
         (root (merkle-root content))
         (proof (merkle-prove content 0)))
    (check "merkle-prove returns proof" (merkle-proof? proof))
    (check "merkle-verify-proof valid" (merkle-verify-proof root proof))
    ;; Wrong root should fail
    (let ((fake-root (make-bytevector 32 42)))
      (check "merkle-verify-proof wrong root" (not (merkle-verify-proof fake-root proof))))))

;; --- Shamir Secret Sharing ---
(printf "\n--- Shamir Secret Sharing ---\n")

;; GF(256) basics
(check "gf256-add" (= (gf256-add 5 3) 6))  ; XOR
(check "gf256-mul identity" (= (gf256-mul 1 42) 42))
(check "gf256-mul zero" (= (gf256-mul 0 42) 0))
(check "gf256-div inverse" (= (gf256-div (gf256-mul 7 13) 13) 7))

;; Split and reconstruct
(let* ((secret (string->utf8 "secret key material"))
       (shares (shamir-split secret 'threshold: 3 'total: 5)))
  (check "shamir produces 5 shares" (= (length shares) 5))
  (check "shares are shamir-share?" (shamir-share? (car shares)))
  (check "share threshold" (= (share-threshold (car shares)) 3))

  ;; Reconstruct with exactly threshold shares
  (let ((recovered (shamir-reconstruct (list (list-ref shares 0)
                                             (list-ref shares 2)
                                             (list-ref shares 4)))))
    (check "shamir reconstruct exact K" (bytevector=? recovered secret)))

  ;; Reconstruct with different subset
  (let ((recovered (shamir-reconstruct (list (list-ref shares 1)
                                             (list-ref shares 3)
                                             (list-ref shares 4)))))
    (check "shamir reconstruct different subset" (bytevector=? recovered secret)))

  ;; Reconstruct with more than threshold
  (let ((recovered (shamir-reconstruct (list (list-ref shares 0)
                                             (list-ref shares 1)
                                             (list-ref shares 2)
                                             (list-ref shares 3)))))
    (check "shamir reconstruct K+1 shares" (bytevector=? recovered secret))))

;; --- memzero! ---
(printf "\n--- Memory Safety ---\n")
(let ((buf (string->utf8 "sensitive")))
  (memzero! buf)
  (check "memzero! clears buffer"
    (= 0 (apply + (map (lambda (i) (bytevector-u8-ref buf i))
                        (iota (bytevector-length buf)))))))

;; ============================================================
;; Results
;; ============================================================

(printf "\n=== Results: ~a passed, ~a failed ===\n\n" *pass* *fail*)

(if (= *fail* 0)
    (printf "Crypto FFI: GO\n\n")
    (begin
      (printf "Crypto FFI: FAIL\n\n")
      (exit 1)))
