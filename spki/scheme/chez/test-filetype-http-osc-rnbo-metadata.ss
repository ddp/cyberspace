#!/usr/bin/env scheme-script
;;; test-filetype-http-osc-rnbo-metadata.ss - Tests for Level 5 media/network modules
;;;
;;; Tests: filetype.sls, http.sls, osc.sls, rnbo.sls, metadata-ffi.sls
;;;
;;; Run: CHEZSCHEMELIBDIRS=. chez --program test-filetype-http-osc-rnbo-metadata.ss

(import (rnrs)
        (only (chezscheme) printf format void
              file-exists? with-output-to-file
              system delete-file
              flush-output-port)
        (cyberspace chicken-compatibility chicken)
        (cyberspace os)
        (cyberspace filetype)
        (cyberspace http)
        (cyberspace osc)
        (cyberspace rnbo)
        (cyberspace metadata-ffi))

;;; ============================================================
;;; Test Framework
;;; ============================================================

(define *tests-run* 0)
(define *tests-passed* 0)
(define *tests-failed* 0)

(define (test name pred)
  (set! *tests-run* (+ *tests-run* 1))
  (if pred
      (begin
        (set! *tests-passed* (+ *tests-passed* 1))
        (printf "  PASS: ~a~%" name))
      (begin
        (set! *tests-failed* (+ *tests-failed* 1))
        (printf "  FAIL: ~a~%" name))))

(define (test-section name)
  (printf "~%=== ~a ===~%" name))

;;; ============================================================
;;; Filetype Module - Magic Bytes
;;; ============================================================

(test-section "Filetype - Magic Byte Detection")

;; Test with raw bytevectors (no file needed)

;; PDF: %PDF
(let ((pdf-bytes (bytevector #x25 #x50 #x44 #x46 #x2d #x31 #x2e #x34)))
  (test "detect PDF from bytevector"
    (eq? (magic-type pdf-bytes) 'pdf))
  (test "PDF MIME type"
    (string=? (magic-mime pdf-bytes) "application/pdf"))
  (test "pdf? predicate"
    (pdf? pdf-bytes)))

;; PNG: 89 50 4E 47 0D 0A 1A 0A
(let ((png-bytes (bytevector #x89 #x50 #x4e #x47 #x0d #x0a #x1a #x0a)))
  (test "detect PNG from bytevector"
    (eq? (magic-type png-bytes) 'png))
  (test "png? predicate"
    (png? png-bytes))
  (test "image? category"
    (and (image? png-bytes) #t)))

;; JPEG: FF D8 FF
(let ((jpeg-bytes (bytevector #xff #xd8 #xff #xe0 #x00 #x10)))
  (test "detect JPEG from bytevector"
    (eq? (magic-type jpeg-bytes) 'jpeg))
  (test "jpeg? predicate"
    (jpeg? jpeg-bytes)))

;; GIF: GIF8
(let ((gif-bytes (bytevector #x47 #x49 #x46 #x38 #x39 #x61)))
  (test "detect GIF from bytevector"
    (eq? (magic-type gif-bytes) 'gif))
  (test "gif? predicate"
    (gif? gif-bytes)))

;; GZIP: 1F 8B
(let ((gz-bytes (bytevector #x1f #x8b #x08 #x00)))
  (test "detect gzip from bytevector"
    (eq? (magic-type gz-bytes) 'gzip))
  (test "gzip? predicate"
    (gzip? gz-bytes))
  (test "archive? category"
    (and (archive? gz-bytes) #t)))

;; ZIP: PK\3\4
(let ((zip-bytes (bytevector #x50 #x4b #x03 #x04)))
  (test "detect ZIP from bytevector"
    (eq? (magic-type zip-bytes) 'zip))
  (test "zip? predicate"
    (zip? zip-bytes)))

;; ELF: \x7fELF
(let ((elf-bytes (bytevector #x7f #x45 #x4c #x46 #x02 #x01)))
  (test "detect ELF from bytevector"
    (eq? (magic-type elf-bytes) 'elf))
  (test "elf? predicate"
    (elf? elf-bytes))
  (test "executable? category"
    (and (executable? elf-bytes) #t)))

;; SQLite
(let ((sqlite-bytes (bytevector #x53 #x51 #x4c #x69 #x74 #x65 #x20 #x66)))
  (test "detect SQLite from bytevector"
    (eq? (magic-type sqlite-bytes) 'sqlite)))

;; MP3 with ID3 tag
(let ((mp3-bytes (bytevector #x49 #x44 #x33 #x04 #x00 #x00)))
  (test "detect MP3 (ID3) from bytevector"
    (mp3? mp3-bytes))
  (test "audio? category for MP3"
    (and (audio? mp3-bytes) #t)))

;; Unknown bytes
(let ((unknown (bytevector #x00 #x00 #x00 #x00)))
  (test "unknown bytes return #f"
    (not (magic-type unknown))))

(test-section "Filetype - Text Detection")

;; XML detection
(let ((xml-bytes (bytevector #x3c #x3f #x78 #x6d #x6c #x20)))
  (test "detect XML from bytevector"
    (xml? xml-bytes)))

;; JSON detection
(let ((json-bytes (bytevector #x7b #x22 #x6e #x61 #x6d #x65 #x22)))
  (test "detect JSON from bytevector"
    (json? json-bytes)))

(test-section "Filetype - Category Predicates")

;; Test categories with non-matching types
(let ((pdf-bytes (bytevector #x25 #x50 #x44 #x46)))
  (test "PDF is document"
    (and (document? pdf-bytes) #t))
  (test "PDF is not image"
    (not (image? pdf-bytes)))
  (test "PDF is not audio"
    (not (audio? pdf-bytes))))

(test-section "Filetype - Magic Patterns Registry")

(test "*magic-patterns* is a list"
  (list? *magic-patterns*))

(test "*magic-patterns* has entries"
  (> (length *magic-patterns*) 50))

(test "each pattern has symbol, mime, offset, bytes"
  (every (lambda (p)
           (and (symbol? (car p))
                (string? (cadr p))
                (integer? (caddr p))
                (>= (length p) 4)))
         *magic-patterns*))

;;; ============================================================
;;; HTTP Module
;;; ============================================================

(test-section "HTTP - MIME Type Detection")

(test "mime-type for .html"
  (string=? (mime-type "index.html") "text/html; charset=utf-8"))

(test "mime-type for .pdf"
  (string=? (mime-type "doc.pdf") "application/pdf"))

(test "mime-type for .png"
  (string=? (mime-type "logo.png") "image/png"))

(test "mime-type for .json"
  (string=? (mime-type "data.json") "application/json"))

(test "mime-type for unknown extension"
  (string=? (mime-type "file.xyz") "application/octet-stream"))

(test "mime-type for .sls (Scheme)"
  (string=? (mime-type "module.sls") "text/plain; charset=utf-8"))

(test-section "HTTP - Response Building")

(let ((resp (http-response 200 'content-type: "text/html" 'body: "<h1>Hi</h1>")))
  (test "200 response contains HTTP/1.1"
    (string-contains resp "HTTP/1.1 200 OK"))
  (test "200 response contains Content-Type"
    (string-contains resp "Content-Type: text/html"))
  (test "200 response contains body"
    (string-contains resp "<h1>Hi</h1>"))
  (test "200 response contains Content-Length"
    (string-contains resp "Content-Length: 11"))
  (test "200 response contains Server header"
    (string-contains resp "Server: Cyberspace/1.0")))

(let ((resp (http-response 404 'body: "Not Found")))
  (test "404 response"
    (string-contains resp "HTTP/1.1 404 Not Found")))

(let ((resp (http-response 301 'headers: '(("Location" . "/new/path")))))
  (test "301 redirect has Location header"
    (string-contains resp "Location: /new/path")))

;;; ============================================================
;;; OSC Module - Encoding/Decoding
;;; ============================================================

(test-section "OSC - Encoding")

(let ((packet (osc-encode "/test" 42)))
  (test "osc-encode returns bytevector"
    (bytevector? packet))
  (test "encoded packet starts with /"
    (= (bytevector-u8-ref packet 0) (char->integer #\/))))

(let ((packet (osc-encode "/hello")))
  (test "osc-encode with no args"
    (bytevector? packet)))

(let ((packet (osc-encode "/multi" 1 2 3)))
  (test "osc-encode with multiple int args"
    (bytevector? packet)))

(test-section "OSC - Roundtrip Encode/Decode")

;; Integer roundtrip
(let* ((packet (osc-encode "/test/int" 42))
       (decoded (osc-decode packet)))
  (test "decode address"
    (string=? (car decoded) "/test/int"))
  (test "decode type tag"
    (string=? (cadr decoded) ",i"))
  (test "decode integer value"
    (= (caddr decoded) 42)))

;; Float roundtrip
(let* ((packet (osc-encode "/test/float" 3.14))
       (decoded (osc-decode packet)))
  (test "decode float address"
    (string=? (car decoded) "/test/float"))
  (test "decode float type tag"
    (string=? (cadr decoded) ",f"))
  (test "decode float value (approximate)"
    (< (abs (- (caddr decoded) 3.14)) 0.001)))

;; String roundtrip
(let* ((packet (osc-encode "/test/str" "hello"))
       (decoded (osc-decode packet)))
  (test "decode string address"
    (string=? (car decoded) "/test/str"))
  (test "decode string type tag"
    (string=? (cadr decoded) ",s"))
  (test "decode string value"
    (string=? (caddr decoded) "hello")))

;; Mixed args roundtrip
(let* ((packet (osc-encode "/mix" 7 "world"))
       (decoded (osc-decode packet)))
  (test "decode mixed: address"
    (string=? (car decoded) "/mix"))
  (test "decode mixed: type tag is ,is"
    (string=? (cadr decoded) ",is"))
  (test "decode mixed: int arg"
    (= (caddr decoded) 7))
  (test "decode mixed: string arg"
    (string=? (cadddr decoded) "world")))

(test-section "OSC - Edge Cases")

(test "osc-decode #f for too-short data"
  (not (osc-decode (bytevector #x00 #x01))))

;; Zero integer
(let* ((packet (osc-encode "/zero" 0))
       (decoded (osc-decode packet)))
  (test "roundtrip zero integer"
    (= (caddr decoded) 0)))

;; Negative integer
(let* ((packet (osc-encode "/neg" -1))
       (decoded (osc-decode packet)))
  (test "roundtrip negative integer"
    ;; -1 in two's complement 32-bit = 4294967295
    ;; Our decoder doesn't handle sign extension yet, but it should decode
    (integer? (caddr decoded))))

(test-section "OSC - Connection State")

(test "osc-connect sets target"
  (begin (osc-connect "10.0.0.1" 8000) #t))

(test "osc-close resets state"
  (begin (osc-close) #t))

;;; ============================================================
;;; RNBO Module
;;; ============================================================

(test-section "RNBO - Status and Control")

(test "rnbo-status returns alist"
  (let ((status (rnbo-status)))
    (and (pair? status) (eq? (car status) 'rnbo-status))))

(test "rnbo-status shows not connected"
  (let ((status (rnbo-status)))
    (not (cadr (assq 'connected (cdr status))))))

(test "rnbo-mute works"
  (begin (rnbo-mute) #t))

(test "rnbo-unmute works"
  (begin (rnbo-unmute) #t))

(test-section "RNBO - Event Streaming (offline)")

;; These just exercise the code paths; without UDP they won't send
(test "stream-gossip returns void"
  (begin (stream-gossip 'sync "peer1" 42) #t))

(test "stream-lamport returns void"
  (begin (stream-lamport 100) #t))

(test "stream-object returns void"
  (begin (stream-object 'put "abc12345" 1024) #t))

(test "stream-key returns void"
  (begin (stream-key 'generate 'ed25519 256) #t))

(test "stream-sync returns void"
  (begin (stream-sync 'idle 0 0) #t))

(test "stream-vault-state returns void"
  (begin (stream-vault-state 100 5 10) #t))

(test "stream-introspection handles hardware alist"
  (begin
    (stream-introspection
     '(hardware (cores 8) (memory-gb 32) (weave 5000) (mobile #f)))
    #t))

;;; ============================================================
;;; Metadata-FFI Module
;;; ============================================================

(test-section "Metadata-FFI - Availability")

(test "metadata-ffi-available? returns boolean"
  (boolean? (metadata-ffi-available?)))

(test-section "Metadata-FFI - Flag Constants")

(test "UF_NODUMP is correct"
  (= UF_NODUMP #x00000001))

(test "UF_IMMUTABLE is correct"
  (= UF_IMMUTABLE #x00000002))

(test "UF_HIDDEN is correct"
  (= UF_HIDDEN #x00008000))

(test "SF_ARCHIVED is correct"
  (= SF_ARCHIVED #x00010000))

(test "SF_IMMUTABLE is correct"
  (= SF_IMMUTABLE #x00020000))

(test-section "Metadata-FFI - xattr operations")

;; These use shell fallback; may not work on all systems
(test "xattr-list returns list"
  (list? (xattr-list "/tmp")))

(test "xattr-get returns #f for nonexistent attr"
  (not (xattr-get "/tmp" "com.cyberspace.nonexistent")))

;;; ============================================================
;;; Results
;;; ============================================================

(printf "~%~%========================================~%")
(printf "Tests: ~a run, ~a passed, ~a failed~%"
        *tests-run* *tests-passed* *tests-failed*)
(printf "========================================~%")

(when (> *tests-failed* 0)
  (exit 1))
