#!/usr/bin/env csi -s
;;; Test Shamir secret sharing

(import crypto-ffi
        (chicken blob)
        (chicken format)
        (chicken string)
        srfi-1
        srfi-4)

;; Initialize libsodium
(sodium-init)

;; Helper to display blob as hex
(define (blob->hex b)
  (define (byte->hex n)
    (let ((s (sprintf "~x" n)))
      (if (= (string-length s) 1)
          (string-append "0" s)
          s)))
  (let ((vec (blob->u8vector b)))
    (let loop ((i 0) (acc '()))
      (if (= i (u8vector-length vec))
          (apply string-append (reverse acc))
          (loop (+ i 1)
                (cons (byte->hex (u8vector-ref vec i)) acc))))))

(print "=== Shamir Secret Sharing Test ===\n")

;; Test 1: Split and reconstruct a simple secret
(print "Test 1: Split and reconstruct 32-byte secret (3-of-5 threshold)")
(let* ((secret (make-blob 32))
       ;; Fill with recognizable pattern
       (secret-vec (blob->u8vector secret)))
  (do ((i 0 (+ i 1)))
      ((= i 32))
    (u8vector-set! secret-vec i (modulo (* i 7) 256)))

  (print "Original secret: " (blob->hex secret))

  ;; Split into 5 shares, requiring 3 to reconstruct
  (let ((shares (shamir-split secret threshold: 3 total: 5)))
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
    (print "\nReconstructing from first 3 shares...")
    (let ((reconstructed (shamir-reconstruct (take shares 3))))
      (print "Reconstructed:   " (blob->hex reconstructed))
      (if (equal? (blob->hex secret) (blob->hex reconstructed))
          (print "✓ SUCCESS: Reconstruction matches original!")
          (print "✗ FAILURE: Reconstruction differs!")))

    ;; Reconstruct from different 3 shares (2, 3, 4)
    (print "\nReconstructing from shares 2, 3, 4...")
    (let ((reconstructed (shamir-reconstruct (cdr shares))))
      (print "Reconstructed:   " (blob->hex reconstructed))
      (if (equal? (blob->hex secret) (blob->hex reconstructed))
          (print "✓ SUCCESS: Reconstruction matches original!")
          (print "✗ FAILURE: Reconstruction differs!")))))

(print "\n=== Test 2: Ed25519 Key Splitting ===\n")

;; Test 2: Split an actual Ed25519 private key
(let* ((keypair (ed25519-keypair))
       (public-key (car keypair))
       (private-key (cadr keypair)))

  (print "Generated Ed25519 keypair")
  (print "Public key:  " (blob->hex public-key))
  (print "Private key: " (blob->hex private-key))

  ;; Split the private key (5-of-7 threshold for production)
  (let ((shares (shamir-split private-key threshold: 5 total: 7)))
    (print "\nSplit private key into " (length shares) " shares (threshold="
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
            (print "✗ FAILURE: Reconstructed key is broken!"))))))

(print "\n=== All Tests Complete ===")
