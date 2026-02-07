;;; Capability + Merkle + PQ-Crypto + Wordlist + Security Test Suite
;;; Library of Cyberspace - Chez Port
;;;
;;; Run: CHEZSCHEMELIBDIRS=. chez --program test-capability-merkle-security.ss

(import (rnrs)
        (only (chezscheme) printf format void)
        (cyberspace chicken-compatibility chicken)
        (cyberspace chicken-compatibility blob)
        (cyberspace crypto-ffi)
        (cyberspace cert)
        (cyberspace sexp)
        (cyberspace capability)
        (cyberspace merkle)
        (cyberspace pq-crypto)
        (cyberspace wordlist)
        (cyberspace security))

;; ============================================================
;; Test harness
;; ============================================================

(define *pass* 0)
(define *fail* 0)

(define (check name ok?)
  (if ok?
      (begin
        (printf "  pass ~a~%" name)
        (set! *pass* (+ *pass* 1)))
      (begin
        (printf "  FAIL ~a~%" name)
        (set! *fail* (+ *fail* 1)))))

(printf "~%=== Capability + Merkle + Security Test Suite ===~%~%")

;; Init sodium
(sodium-init)

;; ============================================================
;; Capability Tests
;; ============================================================

(printf "--- Capability Scoring ---~%")

;; Build test hardware specs
(define server-hw
  '(hardware
    (model "Mac Studio")
    (weave 2000000)
    (memory-gb 128)
    (cores 12)
    (root-avail-gb 500)
    (mobile #f)))

(define laptop-hw
  '(hardware
    (model "MacBook Air M2")
    (weave 500000)
    (memory-gb 16)
    (cores 8)
    (root-avail-gb 256)
    (mobile #t)))

(define unknown-hw
  '(hardware
    (model "Unknown Server")
    (weave 1000000)
    (memory-gb 64)
    (cores 16)
    (root-avail-gb 1000)))

;; Capability scoring
(let ((server-score (compute-capability-score server-hw))
      (laptop-score (compute-capability-score laptop-hw)))
  (check "server scores higher than laptop"
    (> server-score laptop-score))
  (check "server score positive" (> server-score 0))
  (check "laptop score positive" (> laptop-score 0))
  ;; Laptop should be ~10% due to mobile penalty
  (check "mobile penalty applied"
    (< laptop-score (* 0.2 server-score))))

;; Mobile detection
(check "laptop is mobile" (is-mobile? laptop-hw))
(check "server is not mobile" (not (is-mobile? server-hw)))
(check "unknown not mobile" (not (is-mobile? unknown-hw)))

;; Compare capabilities
(check "compare: server wins"
  (eq? 'first (compare-capabilities server-hw laptop-hw)))
(check "compare: laptop loses"
  (eq? 'second (compare-capabilities laptop-hw server-hw)))

;; Master election
(let-values (((winner score all)
              (elect-master `((starlight . ,laptop-hw)
                              (fluffy . ,server-hw)))))
  (check "elect-master winner" (eq? winner 'fluffy))
  (check "elect-master score" (> score 0))
  (check "elect-master all scored" (= (length all) 2)))

;; Empty election
(let-values (((winner score all) (elect-master '())))
  (check "elect empty" (not winner))
  (check "elect empty score" (= score 0)))

;; Weights
(check "capability-weights" (pair? (capability-weights)))
(let ((old-weights (capability-weights)))
  (set-capability-weights! '((weave . 1.0) (memory-gb . 0) (storage-gb . 0) (mobile-penalty . 1.0)))
  (check "custom weights" (= 1.0 (cdr (assq 'weave (capability-weights)))))
  (set-capability-weights! old-weights))

;; Aggregate resources
(let ((agg (aggregate-confederation-resources (list server-hw laptop-hw))))
  (check "aggregate cores" (= (cdr (assq 'total-cores agg)) 20))
  (check "aggregate memory" (= (cdr (assq 'total-memory-gb agg)) 144))
  (check "aggregate count" (= (cdr (assq 'member-count agg)) 2)))

;; Scaling factor
(let ((sf (compute-scaling-factor `((fluffy . ,server-hw) (starlight . ,laptop-hw)))))
  (check "scaling reference" (eq? (cdr (assq 'reference sf)) 'fluffy))
  (check "scaling member-count" (= (cdr (assq 'member-count sf)) 2))
  (check "scaling replication" (<= (cdr (assq 'recommended-replication sf)) 3)))

;; Empty scaling
(let ((sf (compute-scaling-factor '())))
  (check "empty scaling" (not (cdr (assq 'reference sf)))))

;; ============================================================
;; Merkle Tree Tests
;; ============================================================

(printf "~%--- Merkle Trees ---~%")

;; Basic hash
(let ((hash (merkle-hash "Hello, Merkle!")))
  (check "merkle-hash returns bv" (bytevector? hash))
  (check "merkle-hash length" (> (bytevector-length hash) 0)))

;; Deterministic
(let ((h1 (merkle-hash "test data"))
      (h2 (merkle-hash "test data")))
  (check "merkle-hash deterministic"
    (let loop ((i 0))
      (or (= i (bytevector-length h1))
          (and (= (bytevector-u8-ref h1 i) (bytevector-u8-ref h2 i))
               (loop (+ i 1)))))))

;; Different content = different hash
(let ((h1 (merkle-hash "alpha"))
      (h2 (merkle-hash "beta")))
  (check "different content different hash"
    (not (let loop ((i 0))
           (or (= i (bytevector-length h1))
               (and (= (bytevector-u8-ref h1 i) (bytevector-u8-ref h2 i))
                    (loop (+ i 1))))))))

;; Chunking
(let ((chunks (chunk-content (string->utf8 "Hello, World!") 4)))
  (check "chunk-content splits" (= (length chunks) 4))
  (check "chunk sizes" (= (bytevector-length (car chunks)) 4)))

;; Leaf/node domain separation
(let ((leaf (merkle-hash-leaf (string->utf8 "test")))
      (node (merkle-hash-node (list (merkle-hash-leaf (string->utf8 "test"))))))
  (check "leaf hash bytevector" (bytevector? leaf))
  (check "node hash bytevector" (bytevector? node))
  (check "leaf != node"
    (not (let loop ((i 0))
           (or (= i (bytevector-length leaf))
               (and (= (bytevector-u8-ref leaf i) (bytevector-u8-ref node i))
                    (loop (+ i 1))))))))

;; Tree construction
(let ((tree (merkle-tree "Hello, Merkle tree with enough data to make multiple chunks" 8)))
  (check "merkle-tree?" (merkle-tree? tree))
  (check "merkle-tree-root" (bytevector? (merkle-tree-root tree)))
  (check "merkle-tree-depth > 0" (> (merkle-tree-depth tree) 0))
  (check "merkle-tree-chunk-count > 0" (> (merkle-tree-chunk-count tree) 0)))

;; Proof and verification
(let* ((data "Hello, Merkle tree with enough data for proof testing to work properly!")
       (tree (merkle-tree data 8))
       (proof (merkle-proof tree 0))
       (chunks (chunk-content (string->utf8 data) 8)))
  (check "merkle-proof?" (merkle-proof? proof))
  (check "merkle-verify valid" (merkle-verify proof (car chunks)))
  ;; Wrong data should fail
  (check "merkle-verify invalid"
    (not (merkle-verify proof (string->utf8 "wrong data")))))

;; Dual hash
(let ((dh (dual-hash "test content")))
  (check "dual-hash?" (dual-hash? dh))
  (check "dual-hash-legacy" (bytevector? (dual-hash-legacy dh)))
  (check "dual-hash-merkle" (bytevector? (dual-hash-merkle dh))))

;; Constants
(check "chunk-size-default" (= chunk-size-default 4096))
(check "fanout-default" (= fanout-default 16))

;; ============================================================
;; PQ-Crypto Tests (without liboqs)
;; ============================================================

(printf "~%--- PQ-Crypto ---~%")

;; pq-init should fail gracefully without liboqs
(let ((result (pq-init)))
  (check "pq-init without liboqs" (< result 0)))

;; Algorithm info should work without init
(let ((info (pq-algorithm-info 'sphincs+)))
  (check "pq-algorithm-info sphincs+" (pair? info))
  (check "sphincs+ type" (eq? (cdr (assq 'type info)) 'hash-based)))

(let ((info (pq-algorithm-info 'ml-dsa-65)))
  (check "pq-algorithm-info ml-dsa" (pair? info))
  (check "ml-dsa type" (eq? (cdr (assq 'type info)) 'lattice-based)))

(check "pq-supported-algorithms"
  (and (pair? (pq-supported-algorithms))
       (memq 'sphincs+-shake-256s (pq-supported-algorithms))
       (memq 'ml-dsa-65 (pq-supported-algorithms))))

;; Operations should error without init
(check "sphincs+-keygen errors"
  (guard (exn (#t #t))
    (sphincs+-keygen)
    #f))

(check "ml-dsa-keygen errors"
  (guard (exn (#t #t))
    (ml-dsa-keygen)
    #f))

;; ============================================================
;; Wordlist Tests
;; ============================================================

(printf "~%--- Wordlist ---~%")

;; Byte to syllable
(let ((syl (byte->syllable 0)))
  (check "byte->syllable" (string? syl))
  (check "syllable length 3" (= (string-length syl) 3)))

;; Different bytes -> different syllables (mostly)
(check "syllable variation"
  (not (string=? (byte->syllable 0) (byte->syllable 100))))

;; FIPS-181 encode
(let ((encoded (fips181-encode (string->utf8 "test"))))
  (check "fips181-encode" (string? encoded))
  (check "fips181 length" (= (string-length encoded) 12)))  ; 4 bytes * 3 chars each

;; PGP word list
(check "even-words vector" (= (vector-length even-words) 256))
(check "odd-words vector" (= (vector-length odd-words) 256))

(let ((w0 (byte->word 0 0))
      (w1 (byte->word 0 1)))
  (check "even word" (string? w0))
  (check "odd word" (string? w1))
  (check "parity distinction" (not (string=? w0 w1))))

;; Pubkey verification words
(let* ((keys (ed25519-keypair))
       (pub (car keys))
       (words (pubkey->words pub)))
  (check "pubkey->words" (= (length words) 4))
  (check "words are strings" (string? (car words)))
  ;; Deterministic
  (check "pubkey->words deterministic"
    (equal? words (pubkey->words pub))))

;; Pubkey syllables
(let* ((keys (ed25519-keypair))
       (pub (car keys))
       (syls (pubkey->syllables pub)))
  (check "pubkey->syllables" (= (length syls) 4))
  (check "syllables are strings" (string? (car syls))))

;; Display formatters
(check "syllables->display"
  (string=? (syllables->display '("baf" "dux" "gim")) "baf-dux-gim"))
(check "words->display"
  (string=? (words->display '("alpha" "bravo")) "alpha  bravo"))

;; ============================================================
;; Security Tests
;; ============================================================

(printf "~%--- Security ---~%")

;; Create test principals and certs
(let* ((keys1 (ed25519-keypair))
       (pub1 (car keys1))
       (priv1 (cadr keys1))
       (keys2 (ed25519-keypair))
       (pub2 (car keys2))
       (p1 (make-key-principal pub1))
       (p2 (make-key-principal pub2)))

  ;; Principal fingerprint
  (let ((fp (principal-fingerprint p1)))
    (check "principal-fingerprint" (string? fp))
    (check "fingerprint has colons" (string-contains fp ":")))

  ;; Different keys -> different fingerprints
  (check "unique fingerprints"
    (not (string=? (principal-fingerprint p1)
                   (principal-fingerprint p2))))

  ;; Create a cert
  (let* ((the-cert (create-cert p1 p2 (make-all-perms) #f #t))
         (signed (sign-cert the-cert priv1)))

    ;; Inspect cert
    (let ((info (inspect-cert signed)))
      (check "inspect-cert returns alist" (pair? info))
      (check "inspect-cert issuer" (string? (cdr (assq 'issuer info))))
      (check "inspect-cert capability" (equal? (cdr (assq 'capability info)) '(*))))

    ;; Cert status
    (check "cert-status valid"
      (eq? 'valid (cert-status signed pub1)))

    ;; Check revocation
    (check "check-revocation no-list"
      (eq? 'no-list (check-revocation signed '())))

    ;; Inspect principal with certs
    (let ((summary (inspect-principal p1 (list signed))))
      (check "inspect-principal" (pair? summary))
      (check "principal issued" (= 1 (cdr (assq 'issued summary)))))

    ;; who-can
    (let ((holders (who-can '(test capability) (list signed))))
      ;; All-perms cert should match
      (check "who-can finds holder" (pair? holders)))

    ;; what-can
    (let ((caps (what-can p2 (list signed))))
      (check "what-can finds caps" (pair? caps))
      (check "what-can all-perms" (all-perms? (car caps))))

    ;; Verify chain
    (check "verify-chain-to valid"
      (verify-chain-to p1 (list signed)))

    (check "verify-chain-to empty"
      (not (verify-chain-to p1 '())))))

;; Security summary (just check it runs)
(security-summary)
(check "security-summary runs" #t)

;; KeyHash principal fingerprint
(let ((khp (make-keyhash-principal 'sha256 (make-bytevector 32 42))))
  (let ((fp (principal-fingerprint khp)))
    (check "keyhash fingerprint" (string? fp))
    (check "keyhash prefix" (string-prefix? "hash:" fp))))

;; ============================================================
;; Results
;; ============================================================

(printf "~%=== Results: ~a passed, ~a failed ===~%~%" *pass* *fail*)

(if (= *fail* 0)
    (printf "Capability+Merkle+Security: GO~%~%")
    (begin
      (printf "Capability+Merkle+Security: FAIL~%~%")
      (exit 1)))
