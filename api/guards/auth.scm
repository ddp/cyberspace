#!/usr/bin/env csi -s
;; Authentication Guard for Cyberspace API
;; Capability-based authentication using HMAC-signed tokens
;;
;; Based on: Butler Lampson (1971), "Protection"
;;           Butler Lampson et al. (1992), "Authentication in Distributed Systems"
;;
;; Philosophy:
;;   - Unforgeable tokens (HMAC-signed)
;;   - Time-limited (expiry timestamps)
;;   - Attenuatable (delegate subset of rights)
;;   - No ambient authority (possession = authority)

(module auth-guard
  (init-auth-guard
   create-capability
   verify-capability
   parse-capability-token
   refresh-capability)

  (import scheme)
  (import (chicken base))
  (import (chicken string))
  (import (chicken process))
  (import (chicken port))
  (import (chicken io))
  (import (chicken time))
  (import (chicken random))
  (import srfi-1)    ;; List utilities
  (import srfi-13)   ;; String libraries
  (import srfi-69)   ;; Hash tables

  ;; ============================================================================
  ;; Configuration
  ;; ============================================================================

  ;; Master key for HMAC signing (in production, load from secure storage)
  (define *master-key* #f)
  (define *default-expiry* 3600)  ;; 1 hour

  ;; ============================================================================
  ;; HMAC Signing
  ;; ============================================================================

  (define (hmac-sha256 key message)
    "Compute HMAC-SHA256 of message using key (via OpenSSL)"
    (let* ((cmd (sprintf "echo -n '~A' | openssl dgst -sha256 -hmac '~A' | awk '{print $2}'"
                        message key))
           (port (open-input-pipe cmd))
           (signature (read-line port)))
      (close-input-port port)
      (string-trim-both signature)))

  ;; ============================================================================
  ;; Random Generation
  ;; ============================================================================

  (define (random-hex-string length)
    "Generate random hex string of given length"
    (let ((bytes (make-string length)))
      (do ((i 0 (+ i 1)))
          ((= i length) bytes)
        (string-set! bytes i (integer->char (random 256))))
      ;; Convert to hex
      (let ((hex (make-string (* length 2))))
        (do ((i 0 (+ i 1)))
            ((= i length) hex)
          (let* ((byte (char->integer (string-ref bytes i)))
                 (high (quotient byte 16))
                 (low (remainder byte 16))
                 (high-char (if (< high 10)
                               (integer->char (+ high 48))
                               (integer->char (+ high 87))))
                 (low-char (if (< low 10)
                              (integer->char (+ low 48))
                              (integer->char (+ low 87)))))
            (string-set! hex (* i 2) high-char)
            (string-set! hex (+ (* i 2) 1) low-char))))))

  ;; ============================================================================
  ;; Capability Token Format
  ;; ============================================================================

  ;; Token format: object-id:rights:secret:expiry:signature
  ;; Example: user123:read-library,use-crypto:abc123:1234567890:hmac-sig

  (define (make-token-payload object-id rights secret expiry)
    "Create token payload (before signing)"
    (sprintf "~A:~A:~A:~A" object-id rights secret expiry))

  (define (sign-token payload)
    "Sign token payload with HMAC-SHA256"
    (unless *master-key*
      (error "Master key not initialized - call init-auth-guard first"))
    (hmac-sha256 *master-key* payload))

  (define (parse-token token)
    "Parse capability token into components"
    (let ((parts (string-split token ":")))
      (if (< (length parts) 5)
          #f
          `((object-id . ,(list-ref parts 0))
            (rights . ,(string-split (list-ref parts 1) ","))
            (secret . ,(list-ref parts 2))
            (expiry . ,(string->number (list-ref parts 3)))
            (signature . ,(list-ref parts 4))
            (payload . ,(string-join (take parts 4) ":"))))))

  ;; ============================================================================
  ;; Capability Creation
  ;; ============================================================================

  (define (create-capability object-id rights #!optional (expiry-seconds *default-expiry*))
    "Create new capability token"
    (let* ((rights-str (string-join (map symbol->string rights) ","))
           (secret (random-hex-string 16))
           (expiry (+ (current-seconds) expiry-seconds))
           (payload (make-token-payload object-id rights-str secret expiry))
           (signature (sign-token payload))
           (token (sprintf "~A:~A" payload signature)))
      `((token . ,token)
        (expires . ,expiry)
        (rights . ,rights))))

  ;; ============================================================================
  ;; Capability Verification
  ;; ============================================================================

  (define (verify-capability token required-right)
    "Verify capability token has required right"
    (let ((parsed (parse-token token)))
      (if (not parsed)
          `((valid . #f)
            (reason . "Malformed token"))

          (let* ((payload (alist-ref 'payload parsed))
                 (signature (alist-ref 'signature parsed))
                 (expiry (alist-ref 'expiry parsed))
                 (rights (alist-ref 'rights parsed))
                 (now (current-seconds))
                 (expected-sig (sign-token payload)))

            ;; Check signature
            (if (not (string=? signature expected-sig))
                `((valid . #f)
                  (reason . "Invalid signature"))

                ;; Check expiry
                (if (> now expiry)
                    `((valid . #f)
                      (reason . "Token expired")
                      (expired-at . ,expiry)
                      (current-time . ,now))

                    ;; Check rights
                    (if (not (member required-right rights))
                        `((valid . #f)
                          (reason . "Insufficient rights")
                          (required . ,required-right)
                          (granted . ,rights))

                        ;; All checks passed
                        `((valid . #t)
                          (object-id . ,(alist-ref 'object-id parsed))
                          (rights . ,rights)
                          (expiry . ,expiry)))))))))

  ;; ============================================================================
  ;; Capability Refresh
  ;; ============================================================================

  (define (refresh-capability token #!optional (expiry-seconds *default-expiry*))
    "Refresh capability token with new expiry"
    (let ((parsed (parse-token token)))
      (if (not parsed)
          #f
          (let* ((object-id (alist-ref 'object-id parsed))
                 (rights (alist-ref 'rights parsed)))
            ;; Create new token with same rights but new expiry
            (create-capability object-id
                             (map string->symbol rights)
                             expiry-seconds)))))

  ;; ============================================================================
  ;; Guard Initialization
  ;; ============================================================================

  (define (init-auth-guard master-key)
    "Initialize authentication guard with master key"
    (set! *master-key* master-key))

  ;; ============================================================================
  ;; Token Parsing (for external use)
  ;; ============================================================================

  (define (parse-capability-token token)
    "Parse capability token and return components (external API)"
    (parse-token token))

  ;; ============================================================================
  ;; Export
  ;; ============================================================================

) ;; end module
