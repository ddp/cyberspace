;;; FIPS + Forge + Keyring Test Suite
;;; Library of Cyberspace - Chez Port
;;;
;;; Tests the FIPS self-tests, forge password generator,
;;; and keyring key management.
;;;
;;; Run: CHEZSCHEMELIBDIRS=. chez --program test-fips-forge-keyring.ss

(import (rnrs)
        (only (chezscheme) printf format void system
              directory-list file-exists? delete-file)
        (cyberspace chicken-compatibility chicken)
        (cyberspace chicken-compatibility hashtable)
        (cyberspace chicken-compatibility blob)
        (cyberspace crypto-ffi)
        (cyberspace fips)
        (cyberspace keyring))

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

(printf "~%=== FIPS + Forge + Keyring Test Suite ===~%~%")

;; Init sodium
(sodium-init)

;; ============================================================
;; FIPS Self-Tests
;; ============================================================

(printf "--- FIPS Self-Tests ---~%")

;; Status starts untested
(check "fips-status initial" (eq? (fips-status) 'untested))

;; SHA-256 KAT
(check "test-sha256" (test-sha256))

;; SHA-512 KAT
(check "test-sha512" (test-sha512))

;; Ed25519 KAT
(check "test-ed25519" (test-ed25519))

;; Randomness tests
(check "test-randomness" (test-randomness))

;; Individual FIPS randomness tests
(let ((sample (random-bytes 2500)))
  (check "fips-monobit-test" (fips-monobit-test sample))
  (check "fips-poker-test" (fips-poker-test sample))
  (check "fips-runs-test" (fips-runs-test sample))
  (check "fips-long-run-test" (fips-long-run-test sample)))

;; Full self-test
(check "fips-self-test" (fips-self-test))
(check "fips-status passed" (eq? (fips-status) 'passed))

;; Verbose self-test
(check "fips-self-test verbose" (fips-self-test #t))

;; ============================================================
;; Keyring Operations
;; ============================================================

(printf "~%--- Keyring Operations ---~%")

;; Clean up any leftover test keys
(let ((test-keyring ".vault/keys"))
  (when (file-exists? test-keyring)
    (let ((files (directory-list test-keyring)))
      (for-each (lambda (f)
                  (when (string-prefix? "test-" f)
                    (delete-file (string-append test-keyring "/" f))))
                files))))

;; Init
(let ((path (keyring-init)))
  (check "keyring-init" (string? path)))

;; Supported algorithms
(let ((algs (supported-algorithms)))
  (check "supported-algorithms" (and (list? algs) (>= (length algs) 4)))
  (check "has ed25519" (memq 'ed25519 algs))
  (check "has ml-dsa-65" (memq 'ml-dsa-65 algs)))

;; Generate key
(let ((name (keyring-generate "test-chez-key")))
  (check "keyring-generate" (string? name))
  (check "key-exists?" (key-exists? "test-chez-key")))

;; Key info
(let ((info (key-info "test-chez-key")))
  (check "key-info" (pair? info))
  (check "key-info algorithm" (eq? (cdr (assq 'algorithm info)) 'ed25519))
  (check "key-info fingerprint" (string? (cdr (assq 'fingerprint info))))
  (check "key-info public-size" (= (cdr (assq 'public-key-size info)) 32))
  (check "key-info private-size" (= (cdr (assq 'private-key-size info)) 64))
  (check "key-info has-private" (cdr (assq 'has-private info))))

;; Key lookup
(let ((keys (key-by-name "test-chez-key")))
  (check "key-by-name" (and (list? keys) (= (length keys) 2)))
  (check "key-by-name pub" (bytevector? (car keys)))
  (check "key-by-name priv" (bytevector? (cadr keys))))

;; Fingerprint
(let ((fp (key-fingerprint "test-chez-key")))
  (check "key-fingerprint" (string? fp))
  (check "fingerprint format" (string-contains fp ":")))

;; Public/private accessors
(check "key-public" (bytevector? (key-public "test-chez-key")))
(check "key-private" (bytevector? (key-private "test-chez-key")))
(check "key-algorithm" (eq? (key-algorithm "test-chez-key") 'ed25519))

;; Signing and verification
(printf "~%--- Signing/Verification ---~%")

(let* ((msg "Hello, Cyberspace!")
       (sig (key-sign "test-chez-key" msg)))
  (check "key-sign" (bytevector? sig))
  (check "key-sign size" (= (bytevector-length sig) 64))
  (check "key-verify" (key-verify "test-chez-key" msg sig))
  ;; Verify wrong message fails
  (check "key-verify wrong msg" (not (key-verify "test-chez-key" "wrong" sig))))

;; Export
(printf "~%--- Import/Export ---~%")

(let ((hex (keyring-export "test-chez-key")))
  (check "keyring-export" (string? hex))
  (check "export hex length" (= (string-length hex) 64)))  ; 32 bytes = 64 hex

;; Import
(let* ((pub (key-public "test-chez-key"))
       (pub-hex (let ((len (bytevector-length pub)))
                  (let loop ((i 0) (acc '()))
                    (if (= i len)
                        (apply string-append (reverse acc))
                        (let* ((byte (bytevector-u8-ref pub i))
                               (hi (quotient byte 16))
                               (lo (remainder byte 16)))
                          (loop (+ i 1)
                                (cons (string
                                        (string-ref "0123456789abcdef" hi)
                                        (string-ref "0123456789abcdef" lo))
                                      acc))))))))
  (let ((name (keyring-import "test-chez-import" pub-hex)))
    (check "keyring-import" (string? name))
    (check "imported exists" (key-exists? "test-chez-import"))))

;; Duplicate key should fail
(check "duplicate generate"
  (not (keyring-generate "test-chez-key")))

;; Rename
(printf "~%--- Rename/Delete ---~%")

(check "keyring-rename"
  (keyring-rename "test-chez-import" "test-chez-renamed"))
(check "renamed exists" (key-exists? "test-chez-renamed"))
(check "old gone" (not (key-exists? "test-chez-import")))

;; Delete
(check "keyring-delete" (keyring-delete "test-chez-key"))
(check "deleted gone" (not (key-exists? "test-chez-key")))

(check "keyring-delete renamed" (keyring-delete "test-chez-renamed"))
(check "renamed deleted" (not (key-exists? "test-chez-renamed")))

;; Delete nonexistent
(check "delete nonexistent" (not (keyring-delete "no-such-key")))

;; Key lookup on nonexistent
(check "key-by-name nonexistent" (not (key-by-name "no-such-key")))
(check "key-info nonexistent" (not (key-info "no-such-key")))
(check "key-public nonexistent" (not (key-public "no-such-key")))

;; ============================================================
;; Chicken Compat Extras (find, string-join)
;; ============================================================

(printf "~%--- Compat Utilities ---~%")

;; find
(check "find found" (= (find even? '(1 3 4 5 6)) 4))
(check "find not found" (not (find even? '(1 3 5 7))))
(check "find empty" (not (find even? '())))

;; string-join
(check "string-join" (string=? (string-join '("a" "b" "c") "-") "a-b-c"))
(check "string-join default" (string=? (string-join '("a" "b" "c")) "a b c"))
(check "string-join single" (string=? (string-join '("hello")) "hello"))
(check "string-join empty" (string=? (string-join '()) ""))

;; ============================================================
;; Results
;; ============================================================

(printf "~%=== Results: ~a passed, ~a failed ===~%~%" *pass* *fail*)

(if (= *fail* 0)
    (printf "FIPS+Forge+Keyring: GO~%~%")
    (begin
      (printf "FIPS+Forge+Keyring: FAIL~%~%")
      (exit 1)))
