;;; Test Shamir Secret Sharing - Chez Scheme Port

(import (rnrs)
        (only (chezscheme) printf format)
        (cyberspace chicken-compatibility blob)
        (cyberspace crypto-ffi))

(define (print . args) (for-each display args) (newline))

;; Initialize libsodium
(sodium-init)

;; Local blob->hex (avoids importing entire vault)
(define (blob->hex bv)
  (let* ((len (bytevector-length bv))
         (hex-chars "0123456789abcdef"))
    (let loop ((i 0) (acc '()))
      (if (= i len) (apply string-append (reverse acc))
          (let ((b (bytevector-u8-ref bv i)))
            (loop (+ i 1)
                  (cons (string
                         (string-ref hex-chars (div b 16))
                         (string-ref hex-chars (mod b 16)))
                        acc)))))))

;; Helper
(define (take lst n)
  (if (or (= n 0) (null? lst)) '()
      (cons (car lst) (take (cdr lst) (- n 1)))))

(print "=== Shamir Secret Sharing Test ===")
(print "")

;; Test 1: Split and reconstruct a simple secret
(print "Test 1: Split and reconstruct 32-byte secret (3-of-5 threshold)")
(let* ((secret (make-blob 32))
       (secret-bv secret))
  (do ((i 0 (+ i 1)))
      ((= i 32))
    (bytevector-u8-set! secret-bv i (mod (* i 7) 256)))

  (print "Original secret: " (blob->hex secret))

  ;; Split into 5 shares, requiring 3 to reconstruct
  (let ((shares (shamir-split secret 'threshold: 3 'total: 5)))
    (print "Created " (length shares) " shares")
    (print "Threshold: " (share-threshold (car shares)))

    ;; Show share info
    (for-each
     (lambda (share)
       (print "  " (share-id share)
              " x=" (share-x share)
              " y=" (substring (blob->hex (share-y share)) 0 16) "..."))
     shares)

    ;; Reconstruct from first 3 shares
    (print "")
    (print "Reconstructing from first 3 shares...")
    (let ((reconstructed (shamir-reconstruct (take shares 3))))
      (print "Reconstructed:   " (blob->hex reconstructed))
      (if (equal? (blob->hex secret) (blob->hex reconstructed))
          (print "✓ SUCCESS: Reconstruction matches original!")
          (begin (print "✗ FAILURE: Reconstruction differs!")
                 (exit 1))))

    ;; Reconstruct from different 3 shares (2, 3, 4)
    (print "")
    (print "Reconstructing from shares 2, 3, 4...")
    (let ((reconstructed (shamir-reconstruct (cdr shares))))
      (print "Reconstructed:   " (blob->hex reconstructed))
      (if (equal? (blob->hex secret) (blob->hex reconstructed))
          (print "✓ SUCCESS: Reconstruction matches original!")
          (begin (print "✗ FAILURE: Reconstruction differs!")
                 (exit 1))))))

(print "")
(print "=== Test 2: Ed25519 Key Splitting ===")
(print "")

;; Test 2: Split an actual Ed25519 private key
(let* ((keypair (ed25519-keypair))
       (public-key (car keypair))
       (private-key (cadr keypair)))

  (print "Generated Ed25519 keypair")
  (print "Public key:  " (blob->hex public-key))
  (print "Private key: " (blob->hex private-key))

  ;; Split the private key (5-of-7 threshold for production)
  (let ((shares (shamir-split private-key 'threshold: 5 'total: 7)))
    (print "")
    (print "Split private key into " (length shares) " shares (threshold="
           (share-threshold (car shares)) ")")

    ;; Reconstruct from exactly 5 shares
    (print "Reconstructing from 5 shares...")
    (let ((reconstructed-key (shamir-reconstruct (take shares 5))))
      (print "Reconstructed:   " (blob->hex reconstructed-key))

      ;; Verify the reconstructed key works
      (let* ((message "Test message for threshold signature")
             (signature (ed25519-sign reconstructed-key message))
             (verified (ed25519-verify public-key message signature)))
        (if verified
            (print "✓ SUCCESS: Reconstructed key produces valid signatures!")
            (begin (print "✗ FAILURE: Reconstructed key is broken!")
                   (exit 1)))))))

(print "")
(print "=== All Tests Complete ===")
