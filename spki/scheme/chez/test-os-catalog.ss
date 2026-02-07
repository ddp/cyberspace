;;; OS + Catalog + Hashtable Test Suite
;;; Library of Cyberspace - Chez Port

(import (rnrs)
        (only (chezscheme) printf format iota void)
        (cyberspace chicken-compatibility hashtable)
        (cyberspace os)
        (cyberspace crypto-ffi)
        (cyberspace catalog))

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

(printf "\n=== OS + Catalog + Hashtable Test Suite ===\n\n")

;; Init sodium (needed by catalog)
(sodium-init)

;; ============================================================
;; Hash Table Tests (SRFI-69 compat)
;; ============================================================

(printf "--- Hash Tables (SRFI-69) ---\n")

(let ((ht (make-hash-table)))
  (check "make-hash-table" (hash-table? ht))
  (hash-table-set! ht 'foo 42)
  (check "set!/ref" (= (hash-table-ref ht 'foo) 42))
  (check "ref/default" (= (hash-table-ref/default ht 'bar 99) 99))
  (check "exists?" (hash-table-exists? ht 'foo))
  (check "not exists?" (not (hash-table-exists? ht 'bar)))
  (hash-table-set! ht 'baz 7)
  (check "size" (= (hash-table-size ht) 2))
  (check "keys" (= (length (hash-table-keys ht)) 2))
  (check "values" (= (length (hash-table-values ht)) 2))
  (hash-table-delete! ht 'foo)
  (check "delete!" (not (hash-table-exists? ht 'foo)))
  (check "size after delete" (= (hash-table-size ht) 1)))

;; String keys
(let ((ht (make-hash-table string=?)))
  (hash-table-set! ht "hello" 1)
  (hash-table-set! ht "world" 2)
  (check "string keys" (= (hash-table-ref ht "hello") 1))
  (check "string exists" (hash-table-exists? ht "world")))

;; Walk and fold
(let ((ht (make-hash-table)))
  (hash-table-set! ht 'a 1)
  (hash-table-set! ht 'b 2)
  (hash-table-set! ht 'c 3)
  (let ((sum 0))
    (hash-table-walk ht (lambda (k v) (set! sum (+ sum v))))
    (check "walk sum" (= sum 6)))
  (check "fold sum" (= (hash-table-fold ht (lambda (k v acc) (+ acc v)) 0) 6)))

;; alist conversion
(let* ((ht (alist->hash-table '((x . 10) (y . 20)))))
  (check "alist->hash-table" (= (hash-table-ref ht 'x) 10))
  (let ((al (hash-table->alist ht)))
    (check "hash-table->alist" (= (length al) 2))))

;; ============================================================
;; OS Tests
;; ============================================================

(printf "\n--- OS Introspection ---\n")

(check "os-name string" (string? (os-name)))
(check "os-version string" (string? (os-version)))
(check "os-type symbol" (symbol? (os-type)))
(check "os-arch symbol" (symbol? (os-arch)))
(check "os-platform string" (string? (os-platform)))

(check "hostname" (string? (hostname)))

(let ((cores (cpu-cores)))
  (check "cpu-cores" (and cores (> cores 0))))

(let ((mem (memory-gb)))
  (check "memory-gb" (and mem (> mem 0))))

(check "lib-path string" (string? (lib-path)))
(check "include-path string" (string? (include-path)))

;; Shell utilities
(check "shell-command uname" (string? (shell-command "echo test")))
(check "shell-lines" (pair? (shell-lines "echo line1; echo line2")))
(check "shell-success?" (shell-success? "true"))
(check "shell-failure" (not (shell-success? "false")))

;; Session stats
(printf "\n--- Session Stats ---\n")

(session-stats-reset!)
(session-stat! 'test-counter)
(session-stat! 'test-counter)
(session-stat! 'test-counter 5)
(check "session-stat" (= (session-stat 'test-counter) 7))
(check "session-stats alist" (pair? (session-stats)))
(session-stats-reset!)
(check "reset" (= (session-stat 'test-counter) 0))

;; Cleanup hooks
(printf "\n--- Cleanup Hooks ---\n")

(let ((ran? #f))
  (register-cleanup-hook! 'test-hook (lambda () (set! ran? #t)))
  (check "hook registered" (memq 'test-hook (cleanup-hooks-status)))
  (run-cleanup-hooks!)
  (check "hook ran" ran?))

;; Box drawing
(printf "\n--- Box Drawing ---\n")

(let ((b (make-box 40)))
  (check "box-width" (= (box-width b) 40))
  (check "box-top" (string? (box-top b)))
  (check "box-top with title" (string? (box-top b "Title")))
  (check "box-bottom" (string? (box-bottom b)))
  (check "box-separator" (string? (box-separator b)))
  (check "box-line" (string? (box-line b "content"))))

(check "string-truncate" (string=? (string-truncate "hello world" 8) "hello..."))
(check "string-truncate short" (string=? (string-truncate "hi" 8) "hi"))
(check "string-pad-left" (string=? (string-pad-left "42" 5) "   42"))

;; ============================================================
;; Catalog Tests
;; ============================================================

(printf "\n--- Merkle Catalog ---\n")

(let ((cat (make-catalog)))
  (check "empty catalog" (= (catalog-size cat) 0))
  (check "empty root" (not (catalog-root cat)))

  (catalog-add! cat "sha256:aaa")
  (check "add" (= (catalog-size cat) 1))
  (check "contains" (catalog-contains? cat "sha256:aaa"))
  (check "not contains" (not (catalog-contains? cat "sha256:bbb")))
  (check "root exists" (bytevector? (catalog-root cat)))

  (catalog-add! cat "sha256:bbb")
  (catalog-add! cat "sha256:ccc")
  (check "size 3" (= (catalog-size cat) 3))

  ;; Deterministic root
  (let ((root1 (catalog-root cat)))
    (let ((cat2 (make-catalog)))
      (catalog-add! cat2 "sha256:ccc")
      (catalog-add! cat2 "sha256:aaa")
      (catalog-add! cat2 "sha256:bbb")
      ;; Same items in different order should give same root
      (check "deterministic root" (bytevector=? root1 (catalog-root cat2)))))

  ;; Remove
  (catalog-remove! cat "sha256:bbb")
  (check "remove" (= (catalog-size cat) 2))
  (check "removed not contains" (not (catalog-contains? cat "sha256:bbb"))))

;; Catalog diff
(printf "\n--- Catalog Diff ---\n")

(let ((cat1 (make-catalog))
      (cat2 (make-catalog)))
  (catalog-add! cat1 "x")
  (catalog-add! cat1 "y")
  (catalog-add! cat2 "x")
  (catalog-add! cat2 "y")
  ;; Same catalogs
  (let-values (((missing extra) (catalog-diff cat1 (catalog-root cat2))))
    (check "same catalogs no diff" (and (null? missing) (null? extra))))

  ;; Different catalogs
  (catalog-add! cat2 "z")
  (let-values (((missing extra) (catalog-diff cat1 (catalog-root cat2))))
    (check "different catalogs" (eq? missing 'subtree-diff-needed))))

;; Catalog proof
(printf "\n--- Catalog Proof ---\n")

(let ((cat (make-catalog)))
  (catalog-add! cat "alpha")
  (catalog-add! cat "beta")
  (catalog-add! cat "gamma")
  (catalog-add! cat "delta")
  (let* ((root (catalog-root cat))
         (proof (catalog-proof cat "beta")))
    (check "proof exists" (list? proof))
    (check "verify proof" (catalog-verify-proof root "beta" proof))
    ;; Wrong item
    (check "verify wrong item" (not (catalog-verify-proof root "omega" proof)))
    ;; Invalid item
    (check "proof for missing" (not (catalog-proof cat "omega")))))

;; Serialize/deserialize
(printf "\n--- Catalog Serialize ---\n")

(let* ((cat (make-catalog)))
  (catalog-add! cat "item1")
  (catalog-add! cat "item2")
  (let* ((s (catalog-serialize cat))
         (cat2 (catalog-deserialize s)))
    (check "deserialize size" (= (catalog-size cat2) 2))
    (check "deserialize contains" (catalog-contains? cat2 "item1"))
    (check "deserialize root" (bytevector=? (catalog-root cat) (catalog-root cat2)))))

;; ============================================================
;; Results
;; ============================================================

(printf "\n=== Results: ~a passed, ~a failed ===\n\n" *pass* *fail*)

(if (= *fail* 0)
    (printf "OS + Catalog + Hashtable: GO\n\n")
    (begin
      (printf "OS + Catalog + Hashtable: FAIL\n\n")
      (exit 1)))
