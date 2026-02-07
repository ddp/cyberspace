;;; Cert + Bloom Test Suite
;;; Library of Cyberspace - Chez Port
;;;
;;; Tests SPKI certificates (sign/verify/chain) and Bloom filters.

(import (rnrs)
        (only (chezscheme) printf format iota void)
        (cyberspace sexp)
        (cyberspace crypto-ffi)
        (cyberspace cert)
        (cyberspace bloom))

;; ============================================================
;; Test harness
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

(printf "\n=== Cert + Bloom Test Suite ===\n\n")

;; Init sodium
(sodium-init)

;; ============================================================
;; Certificate Tests
;; ============================================================

(printf "--- Principals ---\n")

(let* ((kp (ed25519-keypair))
       (pk (car kp))
       (p (make-key-principal pk)))
  (check "make-key-principal" (key-principal? p))
  (check "principal-public-key" (bytevector=? (principal-public-key p) pk))
  (check "not keyhash" (not (keyhash-principal? p))))

(let* ((h (sha512-hash "test key"))
       (p (make-keyhash-principal 'sha512 h)))
  (check "make-keyhash-principal" (keyhash-principal? p))
  (check "principal-hash-alg" (eq? (principal-hash-alg p) 'sha512))
  (check "principal-hash" (bytevector=? (principal-hash p) h)))

(printf "\n--- Tags ---\n")

(let ((t (make-tag (sexp-list (list (sexp-atom "read") (sexp-atom "/data"))))))
  (check "make-tag" (tag? t))
  (check "tag-sexp" (sexp-list? (tag-sexp t))))

(let ((ap (make-all-perms)))
  (check "make-all-perms" (all-perms? ap))
  (check "not tag" (not (tag? ap))))

(check "all-perms implies tag" (tag-implies (make-all-perms)
                                             (make-tag (sexp-atom "x"))))
(check "tag doesn't imply all-perms" (not (tag-implies (make-tag (sexp-atom "x"))
                                                         (make-all-perms))))

(printf "\n--- Validity ---\n")

(let ((v (make-validity 1000 2000)))
  (check "make-validity" (validity? v))
  (check "not-before" (= (validity-not-before v) 1000))
  (check "not-after" (= (validity-not-after v) 2000)))

(printf "\n--- Certificate Creation ---\n")

(let* ((alice-keys (ed25519-keypair))
       (bob-keys (ed25519-keypair))
       (alice-pk (car alice-keys))
       (alice-sk (cadr alice-keys))
       (bob-pk (car bob-keys))
       (read-tag (make-tag (sexp-list (list (sexp-atom "read")
                                             (sexp-atom "/data"))))))
  ;; Create cert
  (let ((cert (create-cert
                (make-key-principal alice-pk)
                (make-key-principal bob-pk)
                read-tag
                'propagate: #f)))
    (check "create-cert" (cert? cert))
    (check "cert-issuer" (key-principal? (cert-issuer cert)))
    (check "cert-subject" (key-principal? (cert-subject cert)))
    (check "cert-tag" (tag? (cert-tag cert)))
    (check "cert-propagate" (not (cert-propagate cert)))

    ;; Sign cert
    (let ((sc (sign-cert cert alice-sk)))
      (check "sign-cert" (signed-cert? sc))
      (check "signed-cert-cert" (cert? (signed-cert-cert sc)))
      (check "signed-cert-signature" (signature? (signed-cert-signature sc)))

      ;; Verify
      (check "verify valid signature" (verify-signed-cert sc alice-pk))
      (check "reject wrong key" (not (verify-signed-cert sc bob-pk)))

      ;; S-expression roundtrip
      (let* ((sexp-str (signed-cert->string sc))
             (sc2 (signed-cert-of-string sexp-str)))
        (check "sexp roundtrip" (signed-cert? sc2))
        (check "roundtrip verify" (verify-signed-cert sc2 alice-pk))))))

(printf "\n--- Delegation Chain ---\n")

(let* ((alice-keys (ed25519-keypair))
       (bob-keys (ed25519-keypair))
       (carol-keys (ed25519-keypair))
       (alice-pk (car alice-keys))
       (alice-sk (cadr alice-keys))
       (bob-pk (car bob-keys))
       (bob-sk (cadr bob-keys))
       (carol-pk (car carol-keys))
       (read-tag (make-tag (sexp-list (list (sexp-atom "read")
                                             (sexp-atom "/data"))))))

  ;; Alice -> Bob (propagate)
  (let* ((cert1 (create-cert
                  (make-key-principal alice-pk)
                  (make-key-principal bob-pk)
                  (make-all-perms)
                  'propagate: #t))
         (sc1 (sign-cert cert1 alice-sk))
         ;; Bob -> Carol (no propagate)
         (cert2 (create-cert
                  (make-key-principal bob-pk)
                  (make-key-principal carol-pk)
                  read-tag
                  'propagate: #f))
         (sc2 (sign-cert cert2 bob-sk)))

    (check "verify chain"
      (verify-chain alice-pk (list sc1 sc2) read-tag))

    ;; Wrong root key should fail
    (check "wrong root key fails"
      (guard (exn [#t #t])
        (verify-chain carol-pk (list sc1 sc2) read-tag)
        #f))))

;; ============================================================
;; Bloom Filter Tests
;; ============================================================

(printf "\n--- Standard Bloom Filter ---\n")

(let ((bf (make-bloom 'capacity: 1000 'error-rate: 0.01)))
  (bloom-add! bf "hello")
  (bloom-add! bf "world")
  (check "bloom contains hello" (bloom-contains? bf "hello"))
  (check "bloom contains world" (bloom-contains? bf "world"))
  (check "bloom count" (= (bloom-count bf) 2))
  ;; Very unlikely false positive for random string
  (check "bloom probably not contains xyz" (not (bloom-contains? bf "xyzzy-not-added"))))

(printf "\n--- Bloom Merge ---\n")

(let ((bf1 (make-bloom 'capacity: 1000 'error-rate: 0.01))
      (bf2 (make-bloom 'capacity: 1000 'error-rate: 0.01)))
  (bloom-add! bf1 "alpha")
  (bloom-add! bf2 "beta")
  (bloom-merge! bf1 bf2)
  (check "merge: contains alpha" (bloom-contains? bf1 "alpha"))
  (check "merge: contains beta" (bloom-contains? bf1 "beta")))

(printf "\n--- Bloom Serialize/Deserialize ---\n")

(let* ((bf (make-bloom 'capacity: 100 'error-rate: 0.01)))
  (bloom-add! bf "test")
  (let* ((serialized (bloom-serialize bf))
         (bf2 (bloom-deserialize serialized)))
    (check "deserialize contains test" (bloom-contains? bf2 "test"))))

(printf "\n--- Blocked Bloom Filter ---\n")

(let ((bbf (make-blocked-bloom 'capacity: 1000 'error-rate: 0.01)))
  (blocked-bloom-add! bbf "foo")
  (blocked-bloom-add! bbf "bar")
  (check "blocked contains foo" (blocked-bloom-contains? bbf "foo"))
  (check "blocked contains bar" (blocked-bloom-contains? bbf "bar"))
  (check "blocked not contains baz" (not (blocked-bloom-contains? bbf "baz-not-added"))))

(printf "\n--- Counting Bloom Filter ---\n")

(let ((cbf (make-counting-bloom 'capacity: 1000 'error-rate: 0.01)))
  (counting-bloom-add! cbf "item1")
  (counting-bloom-add! cbf "item2")
  (check "counting contains item1" (counting-bloom-contains? cbf "item1"))
  (check "counting contains item2" (counting-bloom-contains? cbf "item2"))
  (check "counting count" (= (counting-bloom-count cbf) 2))

  ;; Remove item1
  (counting-bloom-remove! cbf "item1")
  (check "counting removed item1" (not (counting-bloom-contains? cbf "item1")))
  (check "counting still has item2" (counting-bloom-contains? cbf "item2"))
  (check "counting count after remove" (= (counting-bloom-count cbf) 1)))

(printf "\n--- Inventory Operations ---\n")

(let* ((local-hashes '("hash-a" "hash-b" "hash-c"))
       (remote-hashes '("hash-b" "hash-c" "hash-d"))
       (local-bloom (make-inventory-bloom local-hashes))
       (remote-bloom (make-inventory-bloom remote-hashes)))
  ;; hash-d is in remote but not local
  (let ((missing (inventory-diff local-bloom remote-bloom '("hash-d"))))
    (check "inventory-diff finds missing" (= (length missing) 1))))

(printf "\n--- Bloom Utilities ---\n")

(let ((m (optimal-bloom-size 100000 0.01)))
  (check "optimal size > 0" (> m 0))
  (check "optimal size reasonable" (< m 10000000)))  ; < 10M bits

(let ((k (optimal-hash-count 958506 100000)))
  (check "optimal k" (and (> k 0) (<= k 20))))

(let ((fpr (bloom-false-positive-rate 958506 100000 7)))
  (check "fpr near 1%" (and (> fpr 0.005) (< fpr 0.02))))

;; ============================================================
;; Results
;; ============================================================

(printf "\n=== Results: ~a passed, ~a failed ===\n\n" *pass* *fail*)

(if (= *fail* 0)
    (printf "Cert + Bloom: GO\n\n")
    (begin
      (printf "Cert + Bloom: FAIL\n\n")
      (exit 1)))
