#!/usr/bin/env csi -s
;; Cyberspace API Server
;; RESTful HTTP API for the Library of Cyberspace
;;
;; Philosophy: "Rough consensus, cryptography, trusted systems and running code."
;;
;; Architecture:
;;   - Capability-based authentication (Lampson)
;;   - ChaCha20-Poly1305 AEAD for transport security
;;   - RESTful endpoints for library, crypto, implementations
;;   - JSON request/response format
;;   - Guards for authentication, rate limiting, and logging
;;
;; Endpoints:
;;   /library/* - Search papers, retrieve metadata
;;   /crypto/* - Cryptographic operations (sign, encrypt, MAC)
;;   /impl/* - List and demo implementations
;;   /auth/* - Authentication and capability management

(import scheme)
(import (chicken base))
(import (chicken string))
(import (chicken io))
(import (chicken process-context))
(import (chicken port))
(import (chicken file))
(import (chicken format))
(import srfi-1)    ;; List utilities
(import srfi-13)   ;; String libraries
(import srfi-18)   ;; Threads
(import srfi-69)   ;; Hash tables
(import spiffy)    ;; HTTP server
(import intarweb)  ;; HTTP request/response handling
(import uri-common) ;; URI parsing
(import medea)     ;; JSON parsing

;; ============================================================================
;; Configuration
;; ============================================================================

(define *api-version* "1.0.0")
(define *server-port* 8080)
(define *library-path* "/Users/ddp/cyberspace/library")
(define *impl-path* "/Users/ddp/cyberspace/implementations")

;; Master key for HMAC capability signing (in production, load from secure storage)
(define *master-key* "cyberspace-master-key-change-in-production")

;; ============================================================================
;; Logging
;; ============================================================================

(define (log-info msg . args)
  "Log informational message"
  (let ((timestamp (current-seconds)))
    (fprintf (current-error-port) "[~A] INFO: ~A~%"
             timestamp
             (apply sprintf msg args))))

(define (log-error msg . args)
  "Log error message"
  (let ((timestamp (current-seconds)))
    (fprintf (current-error-port) "[~A] ERROR: ~A~%"
             timestamp
             (apply sprintf msg args))))

(define (log-request method path)
  "Log HTTP request"
  (log-info "~A ~A" method path))

;; ============================================================================
;; JSON Response Helpers
;; ============================================================================

(define (json-response data #!optional (status 200))
  "Send JSON response with proper headers"
  (send-status 'ok)
  (with-headers
   `((content-type application/json))
   (lambda ()
     (write-json data))))

(define (json-error code message #!optional (details '()))
  "Send JSON error response"
  (send-status 'bad-request)
  (with-headers
   `((content-type application/json))
   (lambda ()
     (write-json `((error . ((code . ,code)
                            (message . ,message)
                            (details . ,details))))))))

(define (json-success data)
  "Send successful JSON response"
  (json-response data 200))

;; ============================================================================
;; Capability-Based Authentication
;; ============================================================================

(define (parse-capability-header)
  "Extract capability token from Authorization header"
  (let ((auth-header (header-value 'authorization (request-headers (current-request)))))
    (if auth-header
        (let ((parts (string-split auth-header " ")))
          (if (and (>= (length parts) 2)
                   (string=? (car parts) "Capability"))
              (cadr parts)
              #f))
        #f)))

(define (verify-capability token operation)
  "Verify capability token has required rights for operation"
  ;; Token format: object-id:rights:secret:expiry:signature
  (if (not token)
      #f
      (let ((parts (string-split token ":")))
        (if (< (length parts) 5)
            #f
            (let* ((object-id (list-ref parts 0))
                   (rights-str (list-ref parts 1))
                   (secret (list-ref parts 2))
                   (expiry-str (list-ref parts 3))
                   (signature (list-ref parts 4))
                   (rights (string-split rights-str ","))
                   (payload (string-join (take parts 4) ":")))

              ;; TODO: Verify HMAC signature
              ;; TODO: Check expiry timestamp
              ;; For now, simple rights check
              (member operation rights))))))

(define (require-capability operation)
  "Middleware: require valid capability for operation"
  (let ((token (parse-capability-header)))
    (if (verify-capability token operation)
        #t
        (begin
          (json-error "INVALID_CAPABILITY"
                     "Missing or invalid capability token"
                     `((required_right . ,operation)))
          #f))))

;; ============================================================================
;; Route Handlers
;; ============================================================================

;; --- Health Check ---

(define (handle-health-check)
  "Health check endpoint"
  (json-success `((status . "healthy")
                 (version . ,*api-version*)
                 (timestamp . ,(current-seconds)))))

;; --- Authentication Endpoints ---

(define (handle-auth-login)
  "POST /auth/login - Authenticate and receive capability"
  (let ((body (read-json)))
    (let ((username (alist-ref 'username body))
          (password (alist-ref 'password body)))

      ;; TODO: Proper password verification
      ;; For demo, accept any credentials
      (if (and username password)
          (let* ((object-id "user123")
                 (rights "read-library,use-crypto")
                 (secret "random-secret-todo")
                 (expiry (+ (current-seconds) 3600))  ; 1 hour
                 (payload (sprintf "~A:~A:~A:~A" object-id rights secret expiry))
                 (signature "hmac-signature-todo")
                 (token (sprintf "~A:~A" payload signature)))

            (json-success `((capability . ,token)
                           (expires . ,expiry)
                           (rights . (read-library use-crypto)))))

          (json-error "INVALID_CREDENTIALS"
                     "Invalid username or password")))))

(define (handle-auth-verify)
  "POST /auth/verify - Verify capability token"
  (let ((body (read-json)))
    (let ((token (alist-ref 'capability body)))
      (if (verify-capability token "read-library")
          (json-success `((valid . #t)
                         (rights . (read-library use-crypto))))
          (json-success `((valid . #f)))))))

;; --- Library Endpoints ---

(define (handle-library-search)
  "GET /library/search?q=<query> - Search library papers"
  (let* ((uri (request-uri (current-request)))
         (query-params (uri-query uri))
         (search-query (alist-ref 'q query-params)))

    (if search-query
        ;; TODO: Implement actual search
        (json-success `((query . ,search-query)
                       (results . #())
                       (count . 0)
                       (message . "Search not yet implemented")))

        (json-error "INVALID_INPUT" "Missing search query parameter 'q'"))))

(define (handle-library-catalog)
  "GET /library/catalog - List all papers"
  ;; TODO: Scan library directory and build catalog
  (json-success `((catalog . #())
                 (count . 0)
                 (message . "Catalog not yet implemented"))))

(define (handle-library-paper paper-id)
  "GET /library/papers/<paper-id> - Get paper metadata"
  ;; TODO: Look up paper by ID
  (json-success `((paper_id . ,paper-id)
                 (title . "Paper Title")
                 (authors . #("Author 1" "Author 2"))
                 (year . 1979)
                 (abstract . "Paper abstract...")
                 (message . "Paper lookup not yet implemented"))))

;; --- Crypto Endpoints ---

(define (handle-crypto-lamport-keygen)
  "POST /crypto/lamport/keygen - Generate Lamport keypair"
  (let ((body (read-json)))
    (let ((bits (or (alist-ref 'bits body) 256)))

      ;; TODO: Call actual Lamport implementation
      (json-success `((message . "Lamport keygen not yet implemented")
                     (bits . ,bits))))))

(define (handle-crypto-chacha20-encrypt)
  "POST /crypto/chacha20/encrypt - Encrypt with ChaCha20"
  (let ((body (read-json)))
    (let ((key (alist-ref 'key body))
          (nonce (alist-ref 'nonce body))
          (plaintext (alist-ref 'plaintext body)))

      ;; TODO: Call actual ChaCha20 implementation
      (json-success `((message . "ChaCha20 encrypt not yet implemented"))))))

;; --- Implementation Endpoints ---

(define (handle-impl-list)
  "GET /impl/list - List all implementations"
  ;; TODO: Scan implementations directory
  (json-success `((implementations . #())
                 (count . 0)
                 (message . "Implementation listing not yet implemented"))))

;; ============================================================================
;; Routing
;; ============================================================================

(define (route-request method path)
  "Route HTTP request to appropriate handler"
  (log-request method path)

  (cond
   ;; Health check (no auth required)
   ((and (eq? method 'GET) (string=? path "/health"))
    (handle-health-check))

   ;; Authentication endpoints (no auth required)
   ((and (eq? method 'POST) (string=? path "/auth/login"))
    (handle-auth-login))

   ((and (eq? method 'POST) (string=? path "/auth/verify"))
    (handle-auth-verify))

   ;; Library endpoints (require read-library capability)
   ((and (eq? method 'GET) (string-prefix? "/library/search" path))
    (if (or #t (require-capability "read-library"))  ; TODO: Enable auth
        (handle-library-search)
        (void)))

   ((and (eq? method 'GET) (string=? path "/library/catalog"))
    (if (or #t (require-capability "read-library"))  ; TODO: Enable auth
        (handle-library-catalog)
        (void)))

   ((and (eq? method 'GET) (string-prefix? "/library/papers/" path))
    (if (or #t (require-capability "read-library"))  ; TODO: Enable auth
        (let ((paper-id (substring path 16)))  ; Strip "/library/papers/"
          (handle-library-paper paper-id))
        (void)))

   ;; Crypto endpoints (require use-crypto capability)
   ((and (eq? method 'POST) (string=? path "/crypto/lamport/keygen"))
    (if (or #t (require-capability "use-crypto"))  ; TODO: Enable auth
        (handle-crypto-lamport-keygen)
        (void)))

   ((and (eq? method 'POST) (string=? path "/crypto/chacha20/encrypt"))
    (if (or #t (require-capability "use-crypto"))  ; TODO: Enable auth
        (handle-crypto-chacha20-encrypt)
        (void)))

   ;; Implementation endpoints
   ((and (eq? method 'GET) (string=? path "/impl/list"))
    (handle-impl-list))

   ;; 404 Not Found
   (else
    (send-status 'not-found)
    (json-error "NOT_FOUND"
               (sprintf "Endpoint not found: ~A ~A" method path)))))

;; ============================================================================
;; Request Handler
;; ============================================================================

(define (handle-request continue)
  "Main request handler for spiffy"
  (let ((request (current-request)))
    (let ((method (request-method request))
          (uri (request-uri request)))
      (let ((path (uri-path uri)))

        ;; Handle CORS preflight
        (when (eq? method 'OPTIONS)
          (send-status 'ok)
          (with-headers
           `((access-control-allow-origin "*")
             (access-control-allow-methods "GET, POST, OPTIONS")
             (access-control-allow-headers "Content-Type, Authorization"))
           (lambda () "")))

        ;; Route to handler
        (handle-exceptions
         exn
         (begin
           (log-error "Request handler error: ~A" exn)
           (json-error "SERVER_ERROR" "Internal server error"))

         (with-headers
          `((access-control-allow-origin "*")
            (access-control-allow-methods "GET, POST, OPTIONS")
            (access-control-allow-headers "Content-Type, Authorization"))
          (lambda ()
            (route-request method (uri-path uri)))))))))

;; ============================================================================
;; Server Startup
;; ============================================================================

(define (run-api-server)
  "Start the Cyberspace API server"
  (display "╔═══════════════════════════════════════════════════════════════════╗\n")
  (display "║                     CYBERSPACE API SERVER                         ║\n")
  (display "╚═══════════════════════════════════════════════════════════════════╝\n\n")

  (printf "Version:  ~A~%" *api-version*)
  (printf "Port:     ~A~%" *server-port*)
  (printf "Library:  ~A~%" *library-path*)
  (printf "Impls:    ~A~%~%" *impl-path*)

  (printf "Philosophy: \"Rough consensus, cryptography, trusted systems and running code.\"~%~%")

  (printf "Endpoints:~%")
  (printf "  GET  /health                       - Health check~%")
  (printf "  POST /auth/login                   - Authenticate~%")
  (printf "  GET  /library/search?q=<query>     - Search papers~%")
  (printf "  GET  /library/catalog              - List all papers~%")
  (printf "  POST /crypto/lamport/keygen        - Generate Lamport keypair~%")
  (printf "  POST /crypto/chacha20/encrypt      - Encrypt with ChaCha20~%")
  (printf "  GET  /impl/list                    - List implementations~%~%")

  (printf "Starting server on http://localhost:~A~%~%" *server-port*)

  ;; Configure spiffy
  (server-port *server-port*)
  (root-path "/")
  (handle-not-found handle-request)

  ;; Start spiffy HTTP server
  (start-server))

;; ============================================================================
;; Main Entry Point
;; ============================================================================

(cond
 ;; Start server
 ((null? (command-line-arguments))
  (run-api-server))

 ;; Show help
 (else
  (display "Cyberspace API Server\n\n")
  (display "Usage:\n")
  (display "  ./server.scm              Start server on port 8080\n")
  (display "\n")
  (display "Environment Variables:\n")
  (display "  PORT                      Server port (default: 8080)\n")
  (display "\n")))
