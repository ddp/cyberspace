#!/usr/bin/env scheme-script
;;; Test compat libraries + sexp module
;;; Library of Cyberspace - Chez Port
;;;
;;; Run: CHEZSCHEMELIBDIRS=. chez --program test-compat-sexp.ss

(import (rnrs)
        (only (chezscheme) printf format)
        (cyberspace compat blob)
        (cyberspace compat chicken)
        (cyberspace compat base64)
        (cyberspace sexp))

(define pass-count 0)
(define fail-count 0)

(define (test name thunk)
  (guard (exn
          [#t (set! fail-count (+ fail-count 1))
              (printf "  FAIL ~a: ~a~n" name
                      (if (message-condition? exn)
                          (condition-message exn)
                          exn))])
    (thunk)
    (set! pass-count (+ pass-count 1))
    (printf "  pass ~a~n" name)))

(define (assert-equal name expected actual)
  (unless (equal? expected actual)
    (error 'assert-equal
           (format "~a: expected ~s, got ~s" name expected actual))))

;; ============================================================
(printf "~n=== Compat + Sexp Test Suite ===~n~n")

;; ---- Blob Compat ----
(printf "--- Blob Compat ---~n")

(test "make-blob and blob-size"
  (lambda ()
    (let ((b (make-blob 32)))
      (assert-equal "size" 32 (blob-size b))
      (assert-equal "is-blob" #t (blob? b)))))

(test "string->blob->string roundtrip"
  (lambda ()
    (let* ((s "cyberspace")
           (b (string->blob s))
           (back (blob->string b)))
      (assert-equal "roundtrip" s back))))

(test "blob->u8vector identity"
  (lambda ()
    (let* ((b (string->blob "test"))
           (v (blob->u8vector b)))
      (assert-equal "identity" #t (eq? b v)))))

(test "blob-append"
  (lambda ()
    (let* ((a (string->blob "hello"))
           (b (string->blob " "))
           (c (string->blob "world"))
           (result (blob-append a b c)))
      (assert-equal "append" "hello world" (blob->string result)))))

(test "move-memory!"
  (lambda ()
    (let ((src (string->blob "abcdefgh"))
          (dst (make-blob 4)))
      (move-memory! src dst 4 2 0)  ; copy "cdef" from offset 2
      (assert-equal "moved" "cdef" (blob->string dst)))))

(test "u8vector operations"
  (lambda ()
    (let ((v (make-u8vector 4 0)))
      (u8vector-set! v 0 65)
      (u8vector-set! v 1 66)
      (assert-equal "ref" 65 (u8vector-ref v 0))
      (assert-equal "length" 4 (u8vector-length v))
      (assert-equal "list" '(65 66 0 0) (u8vector->list v)))))

(test "list->u8vector"
  (lambda ()
    (let ((v (list->u8vector '(1 2 3 4))))
      (assert-equal "length" 4 (u8vector-length v))
      (assert-equal "ref" 3 (u8vector-ref v 2)))))

;; ---- Chicken Compat ----
(printf "~n--- Chicken Compat ---~n")

(test "conc"
  (lambda ()
    (assert-equal "conc" "port4433" (conc "port" 4433))))

(test "string-intersperse"
  (lambda ()
    (assert-equal "join" "a, b, c"
                  (string-intersperse '("a" "b" "c") ", "))
    (assert-equal "empty" "" (string-intersperse '()))))

(test "alist-ref"
  (lambda ()
    (let ((al '((a . 1) (b . 2) (c . 3))))
      (assert-equal "found" 2 (alist-ref 'b al))
      (assert-equal "not-found" #f (alist-ref 'z al)))))

(test "alist-update"
  (lambda ()
    (let* ((al '((a . 1) (b . 2)))
           (al2 (alist-update 'b 99 al)))
      (assert-equal "updated" 99 (alist-ref 'b al2))
      (assert-equal "kept" 1 (alist-ref 'a al2)))))

(test "handle-exceptions"
  (lambda ()
    (let ((result (handle-exceptions exn "caught"
                    (error 'test "boom"))))
      (assert-equal "caught" "caught" result))))

(test "get-condition-property"
  (lambda ()
    (guard (exn [#t
                 (assert-equal "message" "test error"
                               (get-condition-property exn 'exn 'message "default"))])
      (error 'test "test error"))))

;; ---- Base64 ----
(printf "~n--- Base64 ---~n")

(test "base64 encode"
  (lambda ()
    (assert-equal "encode" "SGVsbG8=" (base64-encode "Hello"))))

(test "base64 decode"
  (lambda ()
    (assert-equal "decode" "Hello" (base64-decode "SGVsbG8="))))

(test "base64 roundtrip"
  (lambda ()
    (let* ((original "SPKI certificates use s-expressions")
           (encoded (base64-encode original))
           (decoded (base64-decode encoded)))
      (assert-equal "roundtrip" original decoded))))

(test "base64 empty"
  (lambda ()
    (assert-equal "empty-encode" "" (base64-encode ""))
    (assert-equal "empty-decode" "" (base64-decode ""))))

;; ---- Sexp ----
(printf "~n--- Sexp Parser ---~n")

(test "parse atom"
  (lambda ()
    (let ((s (parse-sexp "hello")))
      (assert-equal "is-atom" #t (sexp-atom? s))
      (assert-equal "value" "hello" (atom-value s)))))

(test "parse simple list"
  (lambda ()
    (let ((s (parse-sexp "(cert issuer subject)")))
      (assert-equal "is-list" #t (sexp-list? s))
      (assert-equal "count" 3 (length (list-items s))))))

(test "parse nested list"
  (lambda ()
    (let ((s (parse-sexp "(cert (issuer alice) (subject bob))")))
      (assert-equal "is-list" #t (sexp-list? s))
      (let ((items (list-items s)))
        (assert-equal "tag" "cert" (atom-value (car items)))
        (assert-equal "nested" #t (sexp-list? (cadr items)))))))

(test "parse bytes literal"
  (lambda ()
    (let ((s (parse-sexp "(key |SGVsbG8=|)")))
      (assert-equal "is-list" #t (sexp-list? s))
      (let ((items (list-items s)))
        (assert-equal "has-bytes" #t (sexp-bytes? (cadr items)))
        (assert-equal "decoded" "Hello"
                      (blob->string (bytes-value (cadr items))))))))

(test "sexp->string roundtrip"
  (lambda ()
    (let* ((input "(cert (issuer alice) (subject bob))")
           (parsed (parse-sexp input))
           (output (sexp->string parsed)))
      (assert-equal "roundtrip" input output))))

(test "sexp->string-indent"
  (lambda ()
    (let* ((s (parse-sexp "(cert (issuer alice) (subject bob))"))
           (output (sexp->string-indent s "")))
      ;; Just verify it produces output without crashing
      (assert-equal "non-empty" #t (> (string-length output) 0)))))

(test "find-tag"
  (lambda ()
    (let* ((s (parse-sexp "(cert (issuer alice) (subject bob))"))
           (found (find-tag "issuer" s)))
      (assert-equal "found" #t (sexp-list? found))
      (assert-equal "not-found" #f (find-tag "validity" s)))))

(test "get-tag-value"
  (lambda ()
    (let ((s (parse-sexp "(cert (issuer alice) (subject bob))")))
      (let ((issuer (get-tag-value "issuer" s)))
        (assert-equal "value" "alice" (atom-value issuer))))))

(test "SPKI certificate parse"
  (lambda ()
    (let* ((cert-str (string-append
                      "(cert"
                      " (issuer (hash sha256 |AQID|))"
                      " (subject (hash sha256 |BAUG|))"
                      " (tag (ftp (* prefix /pub/)))"
                      " (valid"
                      "   (not-before \"2026-01-01\")"
                      "   (not-after \"2027-01-01\")))"))
           (cert (parse-sexp cert-str))
           (issuer (find-tag "issuer" cert))
           (tag (find-tag "tag" cert))
           (valid (find-tag "valid" cert)))
      (assert-equal "has-issuer" #t (sexp-list? issuer))
      (assert-equal "has-tag" #t (sexp-list? tag))
      (assert-equal "has-valid" #t (sexp-list? valid)))))

;; ============================================================
;; Results
;; ============================================================

(printf "~n=== Results: ~d passed, ~d failed ===~n~n"
        pass-count fail-count)

(when (> fail-count 0)
  (printf "*** ~d failures ***~n" fail-count)
  (exit 1))

(printf "Compat libraries + sexp: GO~n~n")
