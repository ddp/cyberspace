#!/usr/bin/env csi -s
;;; Test threshold signatures for cyberspace governance

(import script
        crypto-ffi
        (chicken blob)
        (chicken format)
        srfi-4)

(sodium-init)

(print "=== Cyberspace Threshold Signature Test ===\n")

;; Scenario: Production deployment requires 3-of-5 signatures from governance council

(print "Governance Council Setup:")
(print "  Alice, Bob, Carol, Dave, Eve")
(print "  Production threshold: 3-of-5\n")

;; Generate keypairs for 5 council members
(define alice-keys (ed25519-keypair))
(define bob-keys (ed25519-keypair))
(define carol-keys (ed25519-keypair))
(define dave-keys (ed25519-keypair))
(define eve-keys (ed25519-keypair))

(define (keypair-to-string keys)
  (let ((pub (car keys)))
    (substring (blob->hex pub) 0 16)))

(define (blob->hex b)
  (define (byte->hex n)
    (let ((s (number->string n 16)))
      (if (= (string-length s) 1)
          (string-append "0" s)
          s)))
  (let ((vec (blob->u8vector b)))
    (let loop ((i 0) (acc '()))
      (if (= i (u8vector-length vec))
          (apply string-append (reverse acc))
          (loop (+ i 1)
                (cons (byte->hex (u8vector-ref vec i)) acc))))))

(print "Council members:")
(print "  Alice: " (keypair-to-string alice-keys) "...")
(print "  Bob:   " (keypair-to-string bob-keys) "...")
(print "  Carol: " (keypair-to-string carol-keys) "...")
(print "  Dave:  " (keypair-to-string dave-keys) "...")
(print "  Eve:   " (keypair-to-string eve-keys) "...\n")

;; Script to be deployed
(define deployment-script
  "(seal-release \"2.0.0\"
  message: \"Major release with new governance model\"
  preserve: #t)")

(print "Script to deploy:")
(print deployment-script)
(print "")

;; Test 1: Insufficient signatures (only 2)
(print "\n=== Test 1: Insufficient Signatures (2-of-5) ===")

(define insufficient-sigs
  (list (sign-script deployment-script (cadr alice-keys) (car alice-keys))
        (sign-script deployment-script (cadr bob-keys) (car bob-keys))))

(print "Signatures collected from: Alice, Bob")

(if (verify-threshold-script deployment-script insufficient-sigs 3)
    (print "✗ FAILURE: Should have rejected with only 2 signatures")
    (print "✓ SUCCESS: Rejected - need 3 signatures, got 2"))

;; Test 2: Sufficient signatures (exactly 3)
(print "\n=== Test 2: Sufficient Signatures (3-of-5) ===")

(define sufficient-sigs
  (list (sign-script deployment-script (cadr alice-keys) (car alice-keys))
        (sign-script deployment-script (cadr carol-keys) (car carol-keys))
        (sign-script deployment-script (cadr dave-keys) (car dave-keys))))

(print "Signatures collected from: Alice, Carol, Dave")

(if (verify-threshold-script deployment-script sufficient-sigs 3)
    (print "✓ SUCCESS: Accepted with 3 valid signatures")
    (print "✗ FAILURE: Should have accepted 3 signatures"))

;; Test 3: More than threshold (4 signatures)
(print "\n=== Test 3: More Than Threshold (4-of-5) ===")

(define extra-sigs
  (list (sign-script deployment-script (cadr alice-keys) (car alice-keys))
        (sign-script deployment-script (cadr bob-keys) (car bob-keys))
        (sign-script deployment-script (cadr carol-keys) (car carol-keys))
        (sign-script deployment-script (cadr eve-keys) (car eve-keys))))

(print "Signatures collected from: Alice, Bob, Carol, Eve")

(if (verify-threshold-script deployment-script extra-sigs 3)
    (print "✓ SUCCESS: Accepted with 4 signatures (threshold=3)")
    (print "✗ FAILURE: Should have accepted 4 signatures"))

;; Test 4: Tampered script
(print "\n=== Test 4: Tampered Script Detection ===")

(define tampered-script
  "(seal-release \"2.0.0\"
  message: \"HACKED - deploying malware\"
  preserve: #t)")

(print "Attacker modifies script content...")

(if (verify-threshold-script tampered-script sufficient-sigs 3)
    (print "✗ FAILURE: Accepted tampered script!")
    (print "✓ SUCCESS: Rejected tampered script"))

;; Test 5: Tiered signing models
(print "\n=== Test 5: Tiered Signing Models ===\n")

(define dev-script "(print \"dev build\")")
(define staging-script "(print \"staging build\")")
(define prod-script "(print \"production build\")")

(print "Development (1-of-1):")
(let ((dev-sig (list (sign-script dev-script (cadr alice-keys) (car alice-keys)))))
  (if (verify-threshold-script dev-script dev-sig 1)
      (print "  ✓ Deployed with Alice's signature\n")
      (print "  ✗ Failed\n")))

(print "Staging (2-of-2):")
(let ((staging-sigs (list (sign-script staging-script (cadr alice-keys) (car alice-keys))
                          (sign-script staging-script (cadr bob-keys) (car bob-keys)))))
  (if (verify-threshold-script staging-script staging-sigs 2)
      (print "  ✓ Deployed with Alice + Bob signatures\n")
      (print "  ✗ Failed\n")))

(print "Production (3-of-5):")
(if (verify-threshold-script prod-script sufficient-sigs 3)
    (print "  ✓ Deployed with 3-of-5 council signatures\n")
    (print "  ✗ Failed\n"))

(print "=== All Threshold Signature Tests Complete ===")
