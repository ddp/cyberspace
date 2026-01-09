;;; SPKI Scheme - Node Enrollment and Presence (RFC-044)
;;;
;;; Handles node enrollment in the confederation and continuous
;;; presence announcement for peer discovery.
;;;
;;; Features:
;;; - Initial enrollment with verification words
;;; - Continuous mDNS realm presence
;;; - Rich system introspection (hardware, network, capabilities)
;;; - Certificate management (issue, renew, revoke)

(module enroll
  (;; System introspection
   introspect-system
   introspect-hardware
   introspect-network
   introspect-storage
   introspect-realm
   ;; Enrollment (node side)
   enroll-request
   enroll-wait
   enroll-complete
   ;; Enrollment (master side)
   enroll-listen
   enroll-approve
   enroll-reject
   ;; Certificate management
   create-enrollment-cert
   renew-certificate
   revoke-certificate
   ;; Presence
   announce-presence
   stop-presence
   discover-peers
   ;; Helpers
   format-enrollment-display
   format-approval-display)

  (import scheme
          (chicken base)
          (chicken io)
          (chicken port)
          (chicken format)
          (chicken file)
          (chicken file posix)
          (chicken pathname)
          (chicken process)
          (chicken process-context)
          (chicken time)
          (chicken time posix)
          (chicken blob)
          (chicken string)
          (chicken condition)
          srfi-1      ; list utilities
          srfi-4      ; u8vectors
          srfi-13     ; string utilities
          srfi-18     ; threads
          crypto-ffi
          wordlist)

  ;; Use FIPS-181 by default for federal compliance
  (define (pubkey->verification-code pubkey)
    "Generate verification code from public key (FIPS-181)"
    (pubkey->syllables pubkey))

  (define (verification-code->display code)
    "Format verification code for display"
    (syllables->display code))

  ;; ============================================================
  ;; System Introspection - Know Thyself
  ;; ============================================================

  (define (shell-command cmd)
    "Run shell command, return trimmed output or #f"
    (handle-exceptions exn #f
      (let ((result (with-input-from-pipe cmd read-line)))
        (if (eof-object? result) #f result))))

  (define (shell-lines cmd)
    "Run shell command, return list of lines"
    (handle-exceptions exn '()
      (with-input-from-pipe cmd
        (lambda ()
          (let loop ((lines '()))
            (let ((line (read-line)))
              (if (eof-object? line)
                  (reverse lines)
                  (loop (cons line lines)))))))))

  (define (introspect-hardware)
    "Introspect hardware configuration"
    (let ((os (shell-command "uname -s"))
          (arch (shell-command "uname -m"))
          (hostname (shell-command "hostname -s")))
      `(hardware
        (os ,os)
        (arch ,arch)
        (hostname ,hostname)
        (kernel ,(shell-command "uname -r"))
        ,@(cond
           ;; macOS
           ((and os (string=? os "Darwin"))
            `((cpu ,(shell-command "sysctl -n machdep.cpu.brand_string"))
              (cores ,(string->number (or (shell-command "sysctl -n hw.ncpu") "0")))
              (memory-gb ,(let ((bytes (shell-command "sysctl -n hw.memsize")))
                           (if bytes
                               (inexact->exact (round (/ (string->number bytes) 1073741824)))
                               0)))
              (model ,(shell-command "sysctl -n hw.model"))))
           ;; Linux
           ((and os (string=? os "Linux"))
            `((cpu ,(shell-command "grep -m1 'model name' /proc/cpuinfo | cut -d: -f2 | xargs"))
              (cores ,(string->number (or (shell-command "nproc") "0")))
              (memory-gb ,(let ((kb (shell-command "grep MemTotal /proc/meminfo | awk '{print $2}'")))
                           (if kb
                               (inexact->exact (round (/ (string->number kb) 1048576)))
                               0)))))
           (else '())))))

  (define (introspect-network)
    "Introspect network configuration"
    (let ((os (shell-command "uname -s")))
      `(network
        ,@(cond
           ;; macOS - get active interfaces
           ((and os (string=? os "Darwin"))
            (let ((interfaces (shell-lines "ifconfig -l")))
              `((interfaces
                 ,@(filter-map
                    (lambda (iface)
                      (let ((addr (shell-command
                                   (string-append "ifconfig " iface " 2>/dev/null | grep 'inet ' | awk '{print $2}'"))))
                        (and addr (not (string=? addr ""))
                             `(,iface ,addr))))
                    (if (pair? interfaces)
                        (string-split (car interfaces))
                        '())))
                (gateway ,(shell-command "route -n get default 2>/dev/null | grep gateway | awk '{print $2}'")))))
           ;; Linux
           ((and os (string=? os "Linux"))
            `((interfaces
               ,@(filter-map
                  (lambda (line)
                    (let ((parts (string-split line)))
                      (and (>= (length parts) 2)
                           `(,(string->symbol (car parts)) ,(cadr parts)))))
                  (shell-lines "ip -4 addr show | grep inet | awk '{print $NF, $2}' | cut -d/ -f1")))
              (gateway ,(shell-command "ip route | grep default | awk '{print $3}'"))))
           (else '())))))

  (define (introspect-storage)
    "Introspect storage configuration"
    (let ((os (shell-command "uname -s")))
      `(storage
        ,@(cond
           ;; macOS
           ((and os (string=? os "Darwin"))
            (let* ((df-out (shell-command "df -g / | tail -1"))
                   (parts (if df-out (string-split df-out) '())))
              (if (>= (length parts) 4)
                  `((root-total-gb ,(string->number (list-ref parts 1)))
                    (root-used-gb ,(string->number (list-ref parts 2)))
                    (root-avail-gb ,(string->number (list-ref parts 3))))
                  '())))
           ;; Linux
           ((and os (string=? os "Linux"))
            (let* ((df-out (shell-command "df -BG / | tail -1"))
                   (parts (if df-out (string-split df-out) '())))
              (if (>= (length parts) 4)
                  `((root-total-gb ,(string->number (string-delete #\G (list-ref parts 1))))
                    (root-used-gb ,(string->number (string-delete #\G (list-ref parts 2))))
                    (root-avail-gb ,(string->number (string-delete #\G (list-ref parts 3)))))
                  '())))
           (else '())))))

  (define (introspect-realm)
    "Introspect realm/vault configuration"
    (let* ((vault-path (or (get-environment-variable "VAULT_PATH") ".vault"))
           (vault-exists (directory-exists? vault-path)))
      `(realm
        (vault-path ,vault-path)
        (vault-exists ,vault-exists)
        ,@(if vault-exists
              (let ((objects (handle-exceptions exn 0
                              (length (directory vault-path)))))
                `((object-count ,objects)
                  (has-keystore ,(file-exists? (make-pathname vault-path "keystore")))
                  (has-audit ,(file-exists? (make-pathname vault-path "audit.log")))))
              '()))))

  (define (introspect-system)
    "Full system introspection - all the thangs!"
    `(system-info
      (timestamp ,(current-seconds))
      (uptime ,(shell-command "uptime | sed 's/.*up //' | sed 's/,.*//'"))
      ,(introspect-hardware)
      ,(introspect-network)
      ,(introspect-storage)
      ,(introspect-realm)
      (versions
       (chicken ,(shell-command "csi -version 2>&1 | head -1"))
       (libsodium ,(shell-command "pkg-config --modversion libsodium 2>/dev/null || echo unknown")))))

  ;; ============================================================
  ;; Enrollment Display Formatting
  ;; ============================================================

  (define (format-enrollment-display name code)
    "Format enrollment request display for node"
    (let* ((code-str (verification-code->display code))
           (name-str (->string name))
           (w 48))  ; box width
      (string-append
       "\n"
       "+" (make-string w #\-) "+\n"
       "|" (make-string w #\space) "|\n"
       "|  Requesting enrollment as: " (string-pad-right name-str (- w 29)) "|\n"
       "|" (make-string w #\space) "|\n"
       "|  Verification code (FIPS-181):" (make-string (- w 33) #\space) "|\n"
       "|" (make-string w #\space) "|\n"
       "|      " (string-pad-right code-str (- w 7)) "|\n"
       "|" (make-string w #\space) "|\n"
       "|  Waiting for master to approve..." (make-string (- w 35) #\space) "|\n"
       "|" (make-string w #\space) "|\n"
       "+" (make-string w #\-) "+\n")))

  (define (format-approval-display name code host hw)
    "Format enrollment approval display for master"
    (let* ((code-str (verification-code->display code))
           (name-str (->string name))
           (host-str (->string host))
           (cpu (or (and hw (cadr (assq 'cpu (cdr hw)))) "unknown"))
           (cpu-short (if (> (string-length cpu) 30)
                         (substring cpu 0 30)
                         cpu))
           (mem (or (and hw (cadr (assq 'memory-gb (cdr hw)))) "?"))
           (w 48))  ; box width
      (string-append
       "\n"
       "+" (make-string w #\-) "+\n"
       "|" (make-string w #\space) "|\n"
       "|  Enrollment request received" (make-string (- w 30) #\space) "|\n"
       "|" (make-string w #\space) "|\n"
       "|  Proposed name: " (string-pad-right name-str (- w 18)) "|\n"
       "|  From: " (string-pad-right host-str (- w 9)) "|\n"
       "|  Hardware: " (string-pad-right cpu-short (- w 13)) "|\n"
       "|  Memory: " (string-pad-right (string-append (->string mem) " GB") (- w 11)) "|\n"
       "|" (make-string w #\space) "|\n"
       "|  Verification code (FIPS-181):" (make-string (- w 33) #\space) "|\n"
       "|" (make-string w #\space) "|\n"
       "|      " (string-pad-right code-str (- w 7)) "|\n"
       "|" (make-string w #\space) "|\n"
       "|  Match what you see on " (string-pad-right (string-append name-str "?") (- w 25)) "|\n"
       "|" (make-string w #\space) "|\n"
       "|  [y] Approve   [n] Reject   [?] Help" (make-string (- w 38) #\space) "|\n"
       "|" (make-string w #\space) "|\n"
       "+" (make-string w #\-) "+\n")))

  (define (->string x)
    (cond ((string? x) x)
          ((symbol? x) (symbol->string x))
          ((number? x) (number->string x))
          (else (with-output-to-string (lambda () (write x))))))

  (define (string-pad-right str len)
    (if (>= (string-length str) len)
        (substring str 0 len)
        (string-append str (make-string (- len (string-length str)) #\space))))

  ;; ============================================================
  ;; Enrollment Protocol - Node Side
  ;; ============================================================

  (define (enroll-request name #!key (port 7654))
    "Request enrollment in the confederation.
     Returns: (values pubkey privkey code)

     name: proposed node name (string or symbol)"

    ;; Generate keypair
    (let* ((keypair (ed25519-keypair))
           (pubkey (car keypair))
           (privkey (cadr keypair))
           (code (pubkey->verification-code pubkey)))

      ;; Display verification code (FIPS-181)
      (display (format-enrollment-display name code))

      ;; Store private key temporarily
      ;; (Will be permanently stored on successful enrollment)

      ;; Return what the caller needs
      (values pubkey privkey code)))

  (define (enroll-wait pubkey privkey words name #!key (timeout 300))
    "Wait for master approval.
     Returns: certificate on success, #f on timeout/rejection"
    ;; This would integrate with mdns module to wait for response
    ;; For now, return a placeholder indicating manual process needed
    `(awaiting-approval
      (name ,name)
      (words ,words)
      (timeout ,timeout)))

  (define (enroll-complete cert privkey vault-path)
    "Complete enrollment by storing certificate and key.
     Returns: #t on success"
    ;; Store in vault keystore
    (let ((keystore-path (make-pathname vault-path "keystore")))
      ;; Create keystore directory if needed
      (unless (directory-exists? keystore-path)
        (create-directory keystore-path))
      ;; Store would happen here
      #t))

  ;; ============================================================
  ;; Enrollment Protocol - Master Side
  ;; ============================================================

  (define *enrollment-requests* '())

  (define (enroll-listen #!key (port 7654))
    "Listen for enrollment requests.
     Returns requests as they arrive."
    ;; This integrates with mdns module
    ;; Returns list of pending requests
    *enrollment-requests*)

  (define (enroll-approve request master-key #!key (role 'full) (validity-days 365))
    "Approve an enrollment request.
     Returns: signed certificate"
    (let* ((name (cadr (assq 'name request)))
           (pubkey (cadr (assq 'pubkey request)))
           (now (current-seconds))
           (not-after (+ now (* validity-days 24 60 60))))

      ;; Create enrollment certificate
      (create-enrollment-cert
       name pubkey master-key
       role: role
       not-before: now
       not-after: not-after)))

  (define (enroll-reject request #!key (reason "Rejected by operator"))
    "Reject an enrollment request.
     Returns: rejection notice"
    `(enrollment-rejected
      (name ,(cadr (assq 'name request)))
      (reason ,reason)
      (timestamp ,(current-seconds))))

  ;; ============================================================
  ;; Certificate Creation
  ;; ============================================================

  (define (create-enrollment-cert name pubkey master-key
                                  #!key (role 'full)
                                        (not-before (current-seconds))
                                        (not-after (+ (current-seconds) 31536000)))
    "Create and sign an enrollment certificate.

     name: node name (symbol)
     pubkey: node's public key (blob)
     master-key: master's signing key (blob, 64 bytes)
     role: one of (full witness archive)
     Returns: signed SPKI certificate s-expression"

    (let* ((capabilities (case role
                          ((full) '(vault-read vault-write sync-participate witness-vote))
                          ((witness) '(vault-read sync-participate witness-vote))
                          ((archive) '(vault-read sync-receive))
                          (else '(vault-read))))

           ;; Create certificate body
           (cert-body `(spki-cert
                        (issuer (public-key (ed25519 ,(blob->base64 (ed25519-secret-to-public master-key)))))
                        (subject (public-key (ed25519 ,(blob->base64 pubkey))))
                        (name ,name)
                        (role ,role)
                        (capabilities ,capabilities)
                        (validity
                         (not-before ,not-before)
                         (not-after ,not-after))
                        (issued ,(current-seconds))))

           ;; Serialize for signing
           (cert-bytes (string->blob (with-output-to-string
                                       (lambda () (write cert-body)))))

           ;; Sign with master key
           (signature (ed25519-sign master-key cert-bytes)))

      ;; Return signed certificate
      `(signed-enrollment-cert
        ,cert-body
        (signature (ed25519 ,(blob->base64 signature))))))

  (define (renew-certificate old-cert master-key #!key (validity-days 365))
    "Renew an existing certificate.
     Returns: new signed certificate"
    (let* ((cert-body (cadr old-cert))
           (name (cadr (assq 'name cert-body)))
           (subject (cadr (assq 'subject cert-body)))
           (pubkey-b64 (cadr (caddr subject)))
           (role (cadr (assq 'role cert-body)))
           (now (current-seconds))
           (not-after (+ now (* validity-days 24 60 60))))

      ;; Create new certificate with extended validity
      `(signed-enrollment-cert
        (spki-cert
         (issuer ,(cadr (assq 'issuer cert-body)))
         (subject ,subject)
         (name ,name)
         (role ,role)
         (capabilities ,(cadr (assq 'capabilities cert-body)))
         (validity
          (not-before ,now)
          (not-after ,not-after))
         (issued ,now)
         (renewed-from ,(cadr (assq 'issued cert-body))))
        (signature (ed25519 "SIGNATURE_PLACEHOLDER")))))

  (define (revoke-certificate cert master-key #!key (reason 'unspecified))
    "Revoke a certificate.
     Returns: revocation record for distribution"
    (let* ((cert-body (cadr cert))
           (name (cadr (assq 'name cert-body)))
           (subject (cadr (assq 'subject cert-body))))

      `(revocation
        (certificate-name ,name)
        (certificate-subject ,subject)
        (revoked-at ,(current-seconds))
        (reason ,reason)
        (issuer ,(cadr (assq 'issuer cert-body)))
        (signature (ed25519 "SIGNATURE_PLACEHOLDER")))))

  ;; ============================================================
  ;; Presence Announcement
  ;; ============================================================

  (define *presence-thread* #f)
  (define *presence-running* #f)

  (define (announce-presence name pubkey #!key (interval 30) (port 7654))
    "Start announcing realm presence on local network.
     Updates mDNS with current system info periodically.

     name: realm name
     pubkey: realm public key
     interval: seconds between announcements"

    (when *presence-running*
      (stop-presence))

    (set! *presence-running* #t)
    (set! *presence-thread*
      (thread-start!
        (make-thread
          (lambda ()
            (let loop ()
              (when *presence-running*
                ;; Gather current system info
                (let ((info (introspect-system)))
                  ;; Announce via mDNS (would integrate with mdns module)
                  ;; For now, just a heartbeat
                  (handle-exceptions exn #f
                    ;; mDNS announcement would go here
                    #f))
                (thread-sleep! interval)
                (loop)))))))

    `(presence-started
      (name ,name)
      (interval ,interval)))

  (define (stop-presence)
    "Stop presence announcement"
    (set! *presence-running* #f)
    (when *presence-thread*
      (handle-exceptions exn #f
        (thread-terminate! *presence-thread*))
      (set! *presence-thread* #f)))

  (define (discover-peers #!key (timeout 5))
    "Discover peers on local network via mDNS.
     Returns: list of discovered peers with their system info"
    ;; Would scan mDNS for _cyberspace._tcp services
    ;; Return list of (name host port system-info) tuples
    '())

  ;; ============================================================
  ;; Helpers
  ;; ============================================================

  (define (blob->base64 blob)
    "Convert blob to base64 string (placeholder)"
    ;; Real implementation would use proper base64 encoding
    (let ((vec (blob->u8vector blob)))
      (with-output-to-string
        (lambda ()
          (do ((i 0 (+ i 1)))
              ((= i (u8vector-length vec)))
            (printf "~2,'0x" (u8vector-ref vec i)))))))

) ;; end module

;;;
;;; Example: Node enrollment
;;;
;;;   (import enroll crypto-ffi)
;;;   (sodium-init)
;;;
;;;   ;; On new node:
;;;   (let-values (((pubkey privkey words) (enroll-request 'starlight)))
;;;     (printf "Words: ~a~n" (words->display words))
;;;     ;; Wait for master approval...
;;;     )
;;;
;;; Example: Master approval
;;;
;;;   (import enroll)
;;;
;;;   (let* ((request '((name starlight) (pubkey #${...})))
;;;          (master-key (load-master-key))
;;;          (cert (enroll-approve request master-key role: 'full)))
;;;     ;; Send cert back to node
;;;     )
;;;
;;; Example: System introspection
;;;
;;;   (import enroll)
;;;   (pp (introspect-system))
;;;
;;;   => (system-info
;;;       (timestamp 1736450000)
;;;       (uptime "2 days")
;;;       (hardware
;;;        (os "Darwin")
;;;        (arch "arm64")
;;;        (hostname "fluffy")
;;;        (cpu "Apple M3 Max")
;;;        (cores 14)
;;;        (memory-gb 128))
;;;       (network
;;;        (interfaces (en0 192.168.1.100))
;;;        (gateway 192.168.1.1))
;;;       (storage
;;;        (root-total-gb 1000)
;;;        (root-avail-gb 500))
;;;       (realm
;;;        (vault-path ".vault")
;;;        (vault-exists #t)
;;;        (object-count 42)))
;;;
