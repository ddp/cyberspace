;;; S-expression Parser Tests - Chez Scheme Port

(import (rnrs)
        (only (chezscheme) format)
        (cyberspace test)
        (cyberspace sexp))

(display "=== SPKI S-expression Parser Tests ===\n\n")

;;; Test 1: Parse simple atom
(test-case "parse atom"
  (lambda ()
    (let ((s (parse-sexp "hello")))
      (assert-equal #t (sexp-atom? s) "should be atom")
      (assert-equal "hello" (atom-value s) "atom value"))))

;;; Test 2: Parse empty list
(test-case "parse empty list"
  (lambda ()
    (let ((s (parse-sexp "()")))
      (assert-equal #t (sexp-list? s) "should be list")
      (assert-equal 0 (length (list-items s)) "should be empty"))))

;;; Test 3: Parse simple list
(test-case "parse simple list"
  (lambda ()
    (let ((s (parse-sexp "(foo bar baz)")))
      (assert-equal #t (sexp-list? s) "should be list")
      (assert-equal 3 (length (list-items s)) "should have 3 items")
      (let ((items (list-items s)))
        (assert-equal "foo" (atom-value (car items)) "first item")
        (assert-equal "bar" (atom-value (cadr items)) "second item")
        (assert-equal "baz" (atom-value (caddr items)) "third item")))))

;;; Test 4: Parse nested list
(test-case "parse nested list"
  (lambda ()
    (let ((s (parse-sexp "(outer (inner value))")))
      (assert-equal #t (sexp-list? s) "should be list")
      (let* ((items (list-items s))
             (inner (cadr items)))
        (assert-equal "outer" (atom-value (car items)) "outer tag")
        (assert-equal #t (sexp-list? inner) "inner should be list")
        (let ((inner-items (list-items inner)))
          (assert-equal "inner" (atom-value (car inner-items)) "inner tag")
          (assert-equal "value" (atom-value (cadr inner-items)) "inner value"))))))

;;; Test 5: Parse SPKI certificate structure
(test-case "parse SPKI cert"
  (lambda ()
    (let ((s (parse-sexp "(cert (issuer alice) (subject bob) (tag read))")))
      (assert-equal #t (sexp-list? s) "should be list")
      (let ((items (list-items s)))
        (assert-equal "cert" (atom-value (car items)) "cert tag")
        (assert-equal 4 (length items) "cert + 3 fields")))))

;;; Test 6: Pretty-print simple
(test-case "pretty-print atom"
  (lambda ()
    (let* ((s (sexp-atom "hello"))
           (str (sexp->string s)))
      (assert-equal "hello" str "atom string"))))

;;; Test 7: Pretty-print list
(test-case "pretty-print list"
  (lambda ()
    (let* ((s (sexp-list (list (sexp-atom "foo")
                              (sexp-atom "bar"))))
           (str (sexp->string s)))
      (assert-equal "(foo bar)" str "list string"))))

;;; Test 8: Pretty-print nested
(test-case "pretty-print nested"
  (lambda ()
    (let* ((inner (sexp-list (list (sexp-atom "inner")
                                  (sexp-atom "value"))))
           (outer (sexp-list (list (sexp-atom "outer") inner)))
           (str (sexp->string outer)))
      (assert-equal "(outer (inner value))" str "nested string"))))

;;; Test 9: Round-trip
(test-case "round-trip parse and print"
  (lambda ()
    (let* ((input "(cert (issuer alice) (subject bob))")
           (parsed (parse-sexp input))
           (output (sexp->string parsed))
           (reparsed (parse-sexp output)))
      (assert-equal #t (sexp-list? parsed) "parsed is list")
      (assert-equal #t (sexp-list? reparsed) "reparsed is list"))))

;;; Test 10: find-tag
(test-case "find-tag helper"
  (lambda ()
    (let* ((cert (parse-sexp "(cert (issuer alice) (subject bob))"))
           (issuer-tag (find-tag "issuer" cert)))
      (assert-equal #t (not (eq? issuer-tag #f)) "found issuer tag")
      (assert-equal #t (sexp-list? issuer-tag) "issuer tag is list")
      (let ((items (list-items issuer-tag)))
        (assert-equal "issuer" (atom-value (car items)) "issuer tag name")
        (assert-equal "alice" (atom-value (cadr items)) "issuer value")))))

;;; Test 11: get-tag-value
(test-case "get-tag-value helper"
  (lambda ()
    (let* ((cert (parse-sexp "(cert (issuer alice) (subject bob))"))
           (issuer (get-tag-value "issuer" cert))
           (subject (get-tag-value "subject" cert)))
      (assert-equal #t (sexp-atom? issuer) "issuer is atom")
      (assert-equal "alice" (atom-value issuer) "issuer value")
      (assert-equal #t (sexp-atom? subject) "subject is atom")
      (assert-equal "bob" (atom-value subject) "subject value"))))

;;; Test 12: Whitespace handling
(test-case "whitespace handling"
  (lambda ()
    (let* ((s1 (parse-sexp "(foo bar)"))
           (s2 (parse-sexp "(foo  bar)"))
           (s3 (parse-sexp "(foo\n  bar)"))
           (s4 (parse-sexp "  (  foo   bar  )  ")))
      (assert-equal (sexp->string s1) (sexp->string s2) "double space")
      (assert-equal (sexp->string s1) (sexp->string s3) "newline")
      (assert-equal (sexp->string s1) (sexp->string s4) "extra whitespace"))))

(display "\n=== All S-expression tests PASSED ===\n")
