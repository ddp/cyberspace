#!/usr/bin/env csi -s
;; Capability-Based Authentication System
;; Based on Lampson & others' capability research (1970s-1980s)
;;
;; Papers: ~/cyberspace/library/cryptographers/lampson/
;;
;; Concept: Security through unforgeable tokens
;;   - Capability = unforgeable reference to object + rights
;;   - Possession = authority (no ACL checks needed)
;;   - Delegation without central authority
;;   - Fine-grained access control
;;
;; "Don't separate designation from authority"
;; —Capability security principle

(import scheme)
(import (chicken base))
(import (chicken io))
(import (chicken file))
(import (chicken process))
(import (chicken process-context))
(import (chicken string))
(import (chicken format))
(import (chicken time))
(import srfi-1)
(import srfi-13)

;; ============================================================================
;; Cryptographic Primitives
;; ============================================================================

(define (random-bytes n)
  "Generate n random bytes as hex string"
  (let ((result (with-input-from-pipe
                 (string-append "openssl rand -hex " (number->string n))
                 read-line)))
    result))

(define (sha256 text)
  "Compute SHA-256 hash"
  (let ((result (with-input-from-pipe
                 (string-append "echo -n '" (escape-shell text) "' | openssl dgst -sha256 -hex")
                 read-line)))
    (if result
        (string-trim-both (car (reverse (string-split result " "))))
        #f)))

(define (escape-shell text)
  "Escape single quotes for shell"
  (string-translate* text '(("'" . "'\"'\"'"))))

(define (hmac-sha256 key message)
  "Compute HMAC-SHA256"
  (let ((result (with-input-from-pipe
                 (string-append "echo -n '" (escape-shell message)
                               "' | openssl dgst -sha256 -hmac '"
                               (escape-shell key) "' -hex")
                 read-line)))
    (if result
        (string-trim-both (car (reverse (string-split result " "))))
        #f)))

;; ============================================================================
;; Capability Structure
;; ============================================================================

;; Capability: (object-id rights secret expiry)
;;   object-id: identifier of protected resource
;;   rights: list of allowed operations (read write execute delete)
;;   secret: unforgeable random token
;;   expiry: Unix timestamp (or 'never)

(define (make-capability object-id rights #!optional (expiry 'never))
  "Create a new capability"
  (let ((secret (random-bytes 32)))  ; 256-bit secret
    (list object-id rights secret expiry)))

(define (capability-object cap) (car cap))
(define (capability-rights cap) (cadr cap))
(define (capability-secret cap) (caddr cap))
(define (capability-expiry cap) (cadddr cap))

(define (capability-expired? cap)
  "Check if capability has expired"
  (let ((expiry (capability-expiry cap)))
    (if (eq? expiry 'never)
        #f
        (> (current-seconds) expiry))))

(define (capability-allows? cap right)
  "Check if capability grants a specific right"
  (and (not (capability-expired? cap))
       (member right (capability-rights cap))))

;; ============================================================================
;; Capability Serialization (Unforgeable Tokens)
;; ============================================================================

(define *master-key* #f)

(define (init-master-key!)
  "Initialize or load master signing key"
  (if (file-exists? ".master-key")
      (begin
        (set! *master-key* (with-input-from-file ".master-key" read-line))
        (print "Loaded master key"))
      (begin
        (set! *master-key* (random-bytes 32))
        (with-output-to-file ".master-key"
          (lambda () (display *master-key*)))
        (print "Generated new master key: .master-key")
        (print "Keep this file secure!"))))

(define (serialize-capability cap)
  "Serialize capability to unforgeable token"
  (unless *master-key* (init-master-key!))

  (let* ((object-id (capability-object cap))
         (rights (capability-rights cap))
         (secret (capability-secret cap))
         (expiry (capability-expiry cap))
         ;; Create payload
         (payload (string-append object-id ":"
                                (string-join (map symbol->string rights) ",") ":"
                                secret ":"
                                (if (eq? expiry 'never)
                                    "never"
                                    (number->string expiry))))
         ;; Sign with HMAC
         (signature (hmac-sha256 *master-key* payload))
         ;; Token = payload:signature
         (token (string-append payload ":" signature)))
    token))

(define (parse-capability token)
  "Parse and verify capability token"
  (unless *master-key* (init-master-key!))

  (let ((parts (string-split token ":")))
    (if (< (length parts) 5)
        #f
        (let* ((object-id (car parts))
               (rights-str (cadr parts))
               (secret (caddr parts))
               (expiry-str (cadddr parts))
               (signature (car (cddddr parts)))
               ;; Reconstruct payload
               (payload (string-append object-id ":" rights-str ":"
                                      secret ":" expiry-str))
               ;; Verify signature
               (expected-sig (hmac-sha256 *master-key* payload)))

          (if (string=? signature expected-sig)
              ;; Valid signature
              (let ((rights (map string->symbol (string-split rights-str ",")))
                    (expiry (if (string=? expiry-str "never")
                               'never
                               (string->number expiry-str))))
                (list object-id rights secret expiry))
              ;; Invalid signature
              #f)))))

;; ============================================================================
;; Capability Delegation (Attenuation)
;; ============================================================================

(define (attenuate-capability cap new-rights)
  "Create restricted capability (subset of rights)"
  ;; New capability can only have subset of original rights
  (let ((original-rights (capability-rights cap))
        (object-id (capability-object cap))
        (expiry (capability-expiry cap)))

    ;; Verify all new rights are in original
    (if (every (lambda (r) (member r original-rights)) new-rights)
        (make-capability object-id new-rights expiry)
        (begin
          (print "Error: Cannot grant rights not in original capability")
          #f))))

(define (expire-capability cap seconds-from-now)
  "Create time-limited version of capability"
  (let ((object-id (capability-object cap))
        (rights (capability-rights cap))
        (new-expiry (+ (current-seconds) seconds-from-now)))
    (make-capability object-id rights new-expiry)))

;; ============================================================================
;; Object Store (Protected Resources)
;; ============================================================================

(define *objects* '())  ; List of (object-id content owner-cap)

(define (create-object! content)
  "Create a new object and return full-access capability"
  (let* ((object-id (substring (sha256 content) 0 16))
         (cap (make-capability object-id '(read write delete))))
    (set! *objects* (cons (list object-id content cap) *objects*))
    (print "Created object: " object-id)
    cap))

(define (find-object object-id)
  "Find object by ID"
  (let ((result (find (lambda (obj) (string=? (car obj) object-id))
                     *objects*)))
    result))

(define (read-object cap)
  "Read object using capability"
  (if (capability-allows? cap 'read)
      (let ((obj (find-object (capability-object cap))))
        (if obj
            (cadr obj)  ; Return content
            #f))
      (begin
        (print "Permission denied: read access required")
        #f)))

(define (write-object cap new-content)
  "Write object using capability"
  (if (capability-allows? cap 'write)
      (let ((obj (find-object (capability-object cap))))
        (if obj
            (begin
              (set-car! (cdr obj) new-content)
              (print "Object updated")
              #t)
            #f))
      (begin
        (print "Permission denied: write access required")
        #f)))

(define (delete-object cap)
  "Delete object using capability"
  (if (capability-allows? cap 'delete)
      (begin
        (set! *objects* (filter (lambda (obj)
                                 (not (string=? (car obj)
                                              (capability-object cap))))
                               *objects*))
        (print "Object deleted")
        #t)
      (begin
        (print "Permission denied: delete access required")
        #f)))

;; ============================================================================
;; Demonstration & Examples
;; ============================================================================

(define (demo-basic)
  "Basic capability demonstration"
  (print "═══════════════════════════════════════════════════")
  (print "Capability System Demo: Basic Operations")
  (print "═══════════════════════════════════════════════════\n")

  ;; Alice creates a document
  (print "1. Alice creates a document")
  (define alice-doc-cap (create-object! "Secret research notes"))
  (print "   Alice's capability: " (capability-rights alice-doc-cap))
  (print "")

  ;; Alice reads her document
  (print "2. Alice reads her document")
  (print "   Content: " (read-object alice-doc-cap))
  (print "")

  ;; Alice delegates read-only access to Bob
  (print "3. Alice shares read-only access with Bob")
  (define bob-cap (attenuate-capability alice-doc-cap '(read)))
  (print "   Bob's capability: " (capability-rights bob-cap))
  (print "")

  ;; Bob reads the document
  (print "4. Bob reads the document")
  (print "   Content: " (read-object bob-cap))
  (print "")

  ;; Bob tries to write (should fail)
  (print "5. Bob tries to modify the document")
  (write-object bob-cap "Hacked!")
  (print "")

  ;; Alice can still write
  (print "6. Alice modifies her document")
  (write-object alice-doc-cap "Updated research notes")
  (print "   New content: " (read-object alice-doc-cap))
  (print ""))

(define (demo-serialization)
  "Demonstrate unforgeable tokens"
  (print "═══════════════════════════════════════════════════")
  (print "Capability System Demo: Unforgeable Tokens")
  (print "═══════════════════════════════════════════════════\n")

  ;; Create object
  (print "1. Create object with capability")
  (define cap (create-object! "Sensitive data"))
  (print "")

  ;; Serialize to token
  (print "2. Serialize capability to unforgeable token")
  (define token (serialize-capability cap))
  (print "   Token: " (substring token 0 (min 80 (string-length token))) "...")
  (print "")

  ;; Verify token works
  (print "3. Parse token and use it")
  (define parsed-cap (parse-capability token))
  (if parsed-cap
      (begin
        (print "   ✓ Token verified")
        (print "   Content: " (read-object parsed-cap)))
      (print "   ✗ Token invalid"))
  (print "")

  ;; Try forged token (tamper with signature)
  (print "4. Attempt to forge token (tamper with signature)")
  (define forged-token (string-append (substring token 0 (- (string-length token) 5)) "XXXXX"))
  (define forged-cap (parse-capability forged-token))
  (if forged-cap
      (print "   ✗ SECURITY FAILURE: Forged token accepted!")
      (print "   ✓ Forged token rejected"))
  (print ""))

(define (demo-delegation-chain)
  "Demonstrate delegation chain"
  (print "═══════════════════════════════════════════════════")
  (print "Capability System Demo: Delegation Chain")
  (print "═══════════════════════════════════════════════════\n")

  ;; Alice creates object
  (print "Alice creates object:")
  (define alice-cap (create-object! "Company secrets"))
  (print "  Rights: " (capability-rights alice-cap))
  (print "")

  ;; Alice → Bob (read + write)
  (print "Alice → Bob (read + write):")
  (define bob-cap (attenuate-capability alice-cap '(read write)))
  (print "  Rights: " (capability-rights bob-cap))
  (print "")

  ;; Bob → Carol (read only)
  (print "Bob → Carol (read only):")
  (define carol-cap (attenuate-capability bob-cap '(read)))
  (print "  Rights: " (capability-rights carol-cap))
  (print "")

  ;; Carol tries to delegate write (should fail)
  (print "Carol tries to grant write to Dave:")
  (define dave-cap (attenuate-capability carol-cap '(read write)))
  (print "")

  ;; Show delegation is transitive
  (print "Delegation chain verification:")
  (print "  Alice can write: " (capability-allows? alice-cap 'write))
  (print "  Bob can write:   " (capability-allows? bob-cap 'write))
  (print "  Carol can write: " (capability-allows? carol-cap 'write))
  (print ""))

(define (demo-expiry)
  "Demonstrate time-limited capabilities"
  (print "═══════════════════════════════════════════════════")
  (print "Capability System Demo: Time-Limited Access")
  (print "═══════════════════════════════════════════════════\n")

  ;; Create object
  (print "1. Create object")
  (define permanent-cap (create-object! "Temporary access document"))
  (print "")

  ;; Create 5-second capability
  (print "2. Grant temporary access (expires in 3 seconds)")
  (define temp-cap (expire-capability permanent-cap 3))
  (print "   Expiry: " (capability-expiry temp-cap))
  (print "")

  ;; Use before expiry
  (print "3. Use capability immediately")
  (print "   Content: " (read-object temp-cap))
  (print "")

  ;; Wait and try again
  (print "4. Wait 4 seconds and try again...")
  (sleep 4)
  (if (read-object temp-cap)
      (print "   ✗ SECURITY FAILURE: Expired capability still works!")
      (print "   ✓ Expired capability rejected"))
  (print "")

  ;; Original still works
  (print "5. Original unlimited capability still works")
  (print "   Content: " (read-object permanent-cap))
  (print ""))

;; ============================================================================
;; CLI Interface
;; ============================================================================

(define (show-help)
  (display "╔═══════════════════════════════════════════════════════════════════╗\n")
  (display "║        CAPABILITY-BASED AUTHENTICATION SYSTEM                     ║\n")
  (display "║        Based on Lampson & others (1970s-1980s)                    ║\n")
  (display "╚═══════════════════════════════════════════════════════════════════╝\n\n")
  (display "CONCEPT:\n")
  (display "  Capabilities = Unforgeable references to objects + access rights\n")
  (display "  Possession = Authority (no ACL checks, no ambient authority)\n")
  (display "  Delegation without central authority\n")
  (display "\n")
  (display "USAGE:\n")
  (display "  ./capabilities.scm demo-basic        # Basic operations\n")
  (display "  ./capabilities.scm demo-serialize    # Unforgeable tokens\n")
  (display "  ./capabilities.scm demo-delegation   # Delegation chain\n")
  (display "  ./capabilities.scm demo-expiry       # Time-limited access\n")
  (display "  ./capabilities.scm demo-all          # Run all demos\n")
  (display "\n")
  (display "SECURITY PROPERTIES:\n")
  (display "  ✓ Unforgeable (HMAC-signed tokens)\n")
  (display "  ✓ Attenuatable (delegate subset of rights)\n")
  (display "  ✓ No ambient authority (can't access without capability)\n")
  (display "  ✓ Transitive delegation (Bob can share what Alice shared)\n")
  (display "  ✓ Time-limited access (capabilities can expire)\n")
  (display "\n")
  (display "PAPER:\n")
  (display "  Butler Lampson (1971) \"Protection\"\n")
  (display "  Butler Lampson (1992) \"Authentication in Distributed Systems\"\n")
  (display "  ~/cyberspace/library/cryptographers/lampson/\n")
  (display "\n"))

;; Main entry point
(when (not (null? (command-line-arguments)))
  (init-master-key!)
  (let ((cmd (car (command-line-arguments))))
    (cond
     ((string=? cmd "demo-basic") (demo-basic))
     ((string=? cmd "demo-serialize") (demo-serialization))
     ((string=? cmd "demo-delegation") (demo-delegation-chain))
     ((string=? cmd "demo-expiry") (demo-expiry))
     ((string=? cmd "demo-all")
      (demo-basic)
      (demo-serialization)
      (demo-delegation-chain)
      (demo-expiry))
     (else (show-help)))))

;; REPL usage
(when (and (equal? (program-name) "csi")
           (null? (command-line-arguments)))
  (show-help)
  (init-master-key!)
  (print "REPL Functions:")
  (print "  (create-object! \"content\")              → capability")
  (print "  (read-object cap)")
  (print "  (write-object cap \"new-content\")")
  (print "  (attenuate-capability cap '(read))")
  (print "  (serialize-capability cap)               → token")
  (print "  (parse-capability token)                 → capability")
  (print ""))
