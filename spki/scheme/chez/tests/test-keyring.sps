#!/usr/bin/env chez --libdirs . --script
;;; test-keyring.ss - Test keyring.sls port
;;; Exercises key generation, storage, lookup, signing, fingerprinting

(import (rnrs)
        (only (chezscheme) printf format system file-exists? delete-file)
        (cyberspace crypto-ffi)
        (cyberspace keyring))

(sodium-init)

(define pass 0)
(define fail 0)

(define (check name result)
  (if result
      (begin
        (printf "  ok: ~a~%" name)
        (set! pass (+ pass 1)))
      (begin
        (printf "  FAIL: ~a~%" name)
        (set! fail (+ fail 1)))))

;; Use a temp directory for test keyring
(system "rm -rf .vault/keys/test-chez-*")

;; Test keyring-init
(let ((path (keyring-init)))
  (check "keyring-init returns path"
         (string? path)))

;; Test key generation
(let ((name (keyring-generate "test-chez-alice")))
  (check "keyring-generate returns name"
         (and name (string=? name "test-chez-alice"))))

;; Test key-exists?
(check "key-exists? true"
       (key-exists? "test-chez-alice"))
(check "key-exists? false"
       (not (key-exists? "test-chez-nonexistent")))

;; Test duplicate detection
(check "duplicate key rejected"
       (not (keyring-generate "test-chez-alice")))

;; Test key-by-name
(let ((keys (key-by-name "test-chez-alice")))
  (check "key-by-name returns list"
         (and (list? keys) (= (length keys) 2)))
  (check "public key is 32 bytes"
         (= (bytevector-length (car keys)) 32))
  (check "private key is 64 bytes"
         (= (bytevector-length (cadr keys)) 64)))

;; Test key-fingerprint
(let ((fp (key-fingerprint "test-chez-alice")))
  (check "key-fingerprint returns string"
         (string? fp))
  (check "fingerprint has colons"
         (let loop ((i 0) (count 0))
           (cond
             ((>= i (string-length fp)) (> count 1))
             ((char=? (string-ref fp i) #\:) (loop (+ i 1) (+ count 1)))
             (else (loop (+ i 1) count))))))

;; Test key-info
(let ((info (key-info "test-chez-alice")))
  (check "key-info returns alist"
         (pair? info))
  (check "algorithm is ed25519"
         (eq? 'ed25519 (cdr (assq 'algorithm info))))
  (check "has-private is true"
         (cdr (assq 'has-private info)))
  (check "created is a number"
         (number? (cdr (assq 'created info)))))

;; Test key-sign and key-verify
(let* ((msg "Hello, Cyberspace!")
       (sig (key-sign "test-chez-alice" msg)))
  (check "key-sign returns bytevector"
         (bytevector? sig))
  (check "signature is 64 bytes"
         (= (bytevector-length sig) 64))
  (check "key-verify valid signature"
         (key-verify "test-chez-alice" msg sig))
  (check "key-verify rejects bad message"
         (not (key-verify "test-chez-alice" "tampered" sig))))

;; Test key-by-fingerprint
(let* ((fp (key-fingerprint "test-chez-alice"))
       (prefix (substring fp 0 4))
       (found (key-by-fingerprint prefix)))
  (check "key-by-fingerprint finds key"
         (and found (string=? found "test-chez-alice"))))

;; Test keyring-export
(let ((hex (keyring-export "test-chez-alice")))
  (check "keyring-export returns hex string"
         (and (string? hex) (= (string-length hex) 64))))  ; 32 bytes = 64 hex chars

;; Test second key generation
(keyring-generate "test-chez-bob")

;; Test keyring-list
(let ((names (keyring-list)))
  (check "keyring-list returns names"
         (and (list? names) (>= (length names) 2))))

;; Test display functions don't crash
(display-key "test-chez-alice")
(check "display-key completed" #t)

;; Test keyring-rename
(check "keyring-rename succeeds"
       (keyring-rename "test-chez-bob" "test-chez-carol"))
(check "old name gone"
       (not (key-exists? "test-chez-bob")))
(check "new name exists"
       (key-exists? "test-chez-carol"))

;; Test keyring-delete
(check "keyring-delete succeeds"
       (keyring-delete "test-chez-carol"))
(check "deleted key gone"
       (not (key-exists? "test-chez-carol")))

;; Clean up
(keyring-delete "test-chez-alice")

(printf "~%Results: ~a passed, ~a failed~%" pass fail)
(when (> fail 0) (exit 1))
