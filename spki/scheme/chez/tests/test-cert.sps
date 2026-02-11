;;; SPKI Certificate Tests - Chez Scheme Port

(import (rnrs)
        (only (chezscheme) printf format)
        (cyberspace chicken-compatibility blob)
        (cyberspace test)
        (cyberspace sexp)
        (cyberspace cert)
        (cyberspace crypto-ffi))

(display "=== SPKI Certificate Tests ===\n\n")

;;; Test 1: Create principals
(test-case "create key principal"
  (lambda ()
    (let ((public-key (make-bytevector 32 0)))
      (let ((principal (make-key-principal public-key)))
        (assert-true (key-principal? principal) "should be key principal")
        (assert-equal public-key (principal-public-key principal) "public key")))))

;;; Test 2: Create hash principal
(test-case "create hash principal"
  (lambda ()
    (let ((hash (make-bytevector 64 0)))
      (let ((principal (make-keyhash-principal 'sha512 hash)))
        (assert-true (keyhash-principal? principal) "should be keyhash principal")
        (assert-equal 'sha512 (principal-hash-alg principal) "hash algorithm")
        (assert-equal hash (principal-hash principal) "hash value")))))

;;; Test 3: Create tags
(test-case "create tags"
  (lambda ()
    (let ((read-tag (make-tag (sexp-list (list (sexp-atom "read")))))
          (all-perms (make-all-perms)))
      (assert-true (tag? read-tag) "read-tag should be tag")
      (assert-true (all-perms? all-perms) "all-perms should be all-perms"))))

;;; Test 4: Create validity
(test-case "create validity"
  (lambda ()
    (let ((validity (make-validity 1767225600 1798761600)))
      (assert-true (validity? validity) "should be validity")
      (assert-equal 1767225600 (validity-not-before validity) "not-before")
      (assert-equal 1798761600 (validity-not-after validity) "not-after"))))

;;; Test 5: Create certificate
(test-case "create certificate"
  (lambda ()
    (let* ((alice-pk (make-bytevector 32 1))
           (bob-pk (make-bytevector 32 2))
           (issuer (make-key-principal alice-pk))
           (subject (make-key-principal bob-pk))
           (tag (make-tag (sexp-atom "read")))
           (cert (create-cert issuer subject tag 'propagate: #t)))
      (assert-true (cert? cert) "should be certificate")
      (assert-equal issuer (cert-issuer cert) "issuer")
      (assert-equal subject (cert-subject cert) "subject")
      (assert-equal tag (cert-tag cert) "tag")
      (assert-equal #t (cert-propagate cert) "propagate"))))

;;; Test 6: Principal to/from s-expression
(test-case "principal s-expression round-trip"
  (lambda ()
    (let* ((public-key (make-bytevector 32 42))
           (principal (make-key-principal public-key))
           (sexp (principal->sexp principal))
           (principal2 (sexp->principal sexp)))
      (assert-true (key-principal? principal2) "should be key principal")
      (assert-equal public-key (principal-public-key principal2) "public key"))))

;;; Test 7: Tag to/from s-expression
(test-case "tag s-expression round-trip"
  (lambda ()
    (let* ((tag (make-tag (sexp-list (list (sexp-atom "read") (sexp-atom "/data")))))
           (sexp (tag->sexp tag))
           (tag2 (sexp->tag sexp)))
      (assert-true (tag? tag2) "should be tag")
      (assert-equal (tag-sexp tag) (tag-sexp tag2) "tag sexp"))))

;;; Test 8: AllPerms to/from s-expression
(test-case "all-perms s-expression round-trip"
  (lambda ()
    (let* ((tag (make-all-perms))
           (sexp (tag->sexp tag))
           (tag2 (sexp->tag sexp)))
      (assert-true (all-perms? tag2) "should be all-perms"))))

;;; Test 9: Validity to/from s-expression
(test-case "validity s-expression round-trip"
  (lambda ()
    (let* ((validity (make-validity 1767225600 1798761600))
           (sexp (validity->sexp validity))
           (validity2 (sexp->validity sexp)))
      (assert-equal "1767225600" (validity-not-before validity2) "not-before")
      (assert-equal "1798761600" (validity-not-after validity2) "not-after"))))

;;; Test 10: Certificate to/from s-expression
(test-case "certificate s-expression round-trip"
  (lambda ()
    (let* ((alice-pk (make-bytevector 32 1))
           (bob-pk (make-bytevector 32 2))
           (issuer (make-key-principal alice-pk))
           (subject (make-key-principal bob-pk))
           (tag (make-tag (sexp-atom "read")))
           (cert (create-cert issuer subject tag 'propagate: #t))
           (sexp (cert->sexp cert))
           (cert2 (sexp->cert sexp)))
      (assert-true (cert? cert2) "should be certificate")
      (assert-equal #t (cert-propagate cert2) "propagate"))))

;;; Test 11: Tag implication
(test-case "tag implication"
  (lambda ()
    (let ((all-perms (make-all-perms))
          (read-tag (make-tag (sexp-atom "read")))
          (write-tag (make-tag (sexp-atom "write"))))
      (assert-true (tag-implies all-perms read-tag) "AllPerms implies read")
      (assert-true (tag-implies all-perms write-tag) "AllPerms implies write")
      (assert-true (tag-implies read-tag read-tag) "read implies read")
      (assert-equal #f (tag-implies read-tag write-tag) "read doesn't imply write")
      (assert-equal #f (tag-implies read-tag all-perms) "read doesn't imply AllPerms"))))

;;; Test 12: Sign and verify certificate
(test-case "sign and verify certificate"
  (lambda ()
    (sodium-init)
    (let* ((keypair (ed25519-keypair))
           (public-key (car keypair))
           (private-key (cadr keypair)))
      (let* ((issuer (make-key-principal public-key))
             (subject (make-key-principal public-key))
             (tag (make-tag (sexp-atom "test")))
             (cert (create-cert issuer subject tag))
             (signed-cert (sign-cert cert private-key)))
        (assert-true (verify-signed-cert signed-cert public-key)
                    "signature should verify")))))

;;; Test 13: Tampered certificate fails verification
(test-case "tampered certificate fails"
  (lambda ()
    (let* ((keypair (ed25519-keypair))
           (public-key (car keypair))
           (private-key (cadr keypair)))
      (let* ((issuer (make-key-principal public-key))
             (subject (make-key-principal public-key))
             (tag (make-tag (sexp-atom "test")))
             (cert (create-cert issuer subject tag))
             (signed-cert (sign-cert cert private-key)))
        (let* ((tampered-cert (create-cert issuer subject (make-tag (sexp-atom "evil"))))
               (tampered-signed (make-signed-cert tampered-cert (signed-cert-signature signed-cert))))
          (assert-equal #f (verify-signed-cert tampered-signed public-key)
                       "tampered cert should fail verification"))))))

;;; Test 14: Signed cert to/from string
(test-case "signed cert string round-trip"
  (lambda ()
    (let* ((keypair (ed25519-keypair))
           (public-key (car keypair))
           (private-key (cadr keypair)))
      (let* ((issuer (make-key-principal public-key))
             (subject (make-key-principal public-key))
             (tag (make-tag (sexp-atom "test")))
             (cert (create-cert issuer subject tag))
             (signed-cert (sign-cert cert private-key)))
        (let* ((str (signed-cert->string signed-cert))
               (signed-cert2 (signed-cert-of-string str)))
          (assert-true (verify-signed-cert signed-cert2 public-key)
                      "deserialized cert should verify"))))))

(display "\n=== All Certificate tests PASSED ===\n")
