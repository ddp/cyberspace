;;; SPKI Scheme - Node Enrollment and Presence (Memo-044)
;;; Library of Cyberspace - Chez Port
;;;
;;; Handles node enrollment in the confederation and continuous
;;; presence announcement for peer discovery.
;;;
;;; Features:
;;; - Initial enrollment with verification words
;;; - Continuous mDNS realm presence
;;; - Rich system introspection (hardware, network, capabilities)
;;; - Certificate management (issue, renew, revoke)
;;;
;;; Ported from enroll.scm.
;;; Copyright (c) 2026 Yoyodyne. See LICENSE.

(library (cyberspace enroll)
  (export
    ;; System introspection
    introspect-system
    introspect-system-refresh!
    introspect-hardware
    introspect-network
    introspect-storage
    introspect-realm
    introspect-codebase
    introspect-library
    probe-scaling
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

  (import (rnrs)
          (only (chezscheme)
                printf format void system
                file-exists? directory-list
                directory-exists? current-directory
                with-output-to-string with-output-to-file
                getenv flush-output-port)
          (cyberspace chicken-compatibility chicken)
          (cyberspace chicken-compatibility base64)
          (cyberspace crypto-ffi)
          (cyberspace wordlist)
          (cyberspace os)
          (cyberspace vault))

  ;; ============================================================
  ;; Local Helpers
  ;; ============================================================

  (define (string-index str ch)
    "Find first index of character ch in str, or #f."
    (let ((len (string-length str)))
      (let loop ((i 0))
        (cond ((= i len) #f)
              ((char=? (string-ref str i) ch) i)
              (else (loop (+ i 1)))))))

  (define (string-delete ch str)
    "Remove all occurrences of character ch from str."
    (list->string (filter (lambda (c) (not (char=? c ch)))
                          (string->list str))))

  (define (bytevector->latin1 bv)
    "Convert bytevector to Latin-1 string (one byte per char)."
    (let ((len (bytevector-length bv)))
      (let loop ((i 0) (chars '()))
        (if (= i len)
            (list->string (reverse chars))
            (loop (+ i 1)
                  (cons (integer->char (bytevector-u8-ref bv i)) chars))))))

  (define (bytevector->base64 bv)
    "Convert bytevector to base64 string."
    (base64-encode (bytevector->latin1 bv)))

  (define (val->string x)
    (cond ((string? x) x)
          ((symbol? x) (symbol->string x))
          ((number? x) (number->string x))
          (else (with-output-to-string (lambda () (write x))))))

  (define (pad-right str len)
    (if (>= (string-length str) len)
        (substring str 0 len)
        (string-append str (make-string (- len (string-length str)) #\space))))

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

  ;; shell-command and shell-lines are imported from os.sls

  ;; ============================================================
  ;; Weave Benchmark - Measure actual compute speed
  ;; ============================================================

  (define *benchmark-iterations* 10000)  ; SHA-256 hashes to run

  (define (probe-scaling)
    "Measure compute speed (weave = hashes/second).
     Runs SHA-256 benchmark and returns hashes per second."
    (let* ((test-data (make-bytevector 64 0))  ; 64 bytes of zeros
           (start (current-seconds))
           (_ (let loop ((i 0) (data test-data))
                (if (< i *benchmark-iterations*)
                    (loop (+ i 1) (sha256-hash data))
                    data)))
           (end (current-seconds))
           (elapsed-sec (max 1 (- end start))))  ; at least 1 second
      (exact (round (/ *benchmark-iterations* elapsed-sec)))))

  ;; Mobile device detection patterns
  (define *mobile-patterns*
    '("MacBook" "Macbook" "Book" "Laptop" "laptop"
      "iPad" "iPhone" "Surface" "ThinkPad" "XPS"))

  (define (detect-mobile model)
    "Detect if model string indicates a mobile device.
     Returns #t for laptops/tablets, #f for desktops/servers."
    (if (not model)
        #f
        (let ((model-down (list->string (map char-downcase (string->list model)))))
          (any (lambda (pat)
                 (let ((pat-down (list->string (map char-downcase (string->list pat)))))
                   (substring-match? model-down pat-down)))
               *mobile-patterns*))))

  (define (substring-match? str pattern)
    "Check if str contains pattern as substring"
    (let ((slen (string-length str))
          (plen (string-length pattern)))
      (let loop ((i 0))
        (cond ((> (+ i plen) slen) #f)
              ((string=? (substring str i (+ i plen)) pattern) #t)
              (else (loop (+ i 1)))))))

  (define (introspect-hardware)
    "Introspect hardware configuration.
     Includes (mobile #t/#f) flag and (weave N) benchmark for capability scoring."
    (let ((os-str (shell-command "uname -s"))
          (arch (shell-command "uname -m"))
          (host (shell-command "hostname -s")))
      (let* ((model (cond
                     ((and os-str (string=? os-str "Darwin"))
                      (shell-command "sysctl -n hw.model"))
                     ((and os-str (string=? os-str "Linux"))
                      (or (shell-command "cat /sys/devices/virtual/dmi/id/product_name 2>/dev/null")
                          (shell-command "hostnamectl --json short 2>/dev/null | grep -o '\"Chassis\":\"[^\"]*\"' | cut -d'\"' -f4")))
                     (else #f)))
             (mobile (detect-mobile model))
             (weave (probe-scaling)))  ; benchmark during introspection
        `(hardware
          (os ,os-str)
          (arch ,arch)
          (hostname ,host)
          (kernel ,(shell-command "uname -r"))
          (mobile ,mobile)
          (weave ,weave)
          ,@(cond
             ;; macOS
             ((and os-str (string=? os-str "Darwin"))
              `((cpu ,(shell-command "sysctl -n machdep.cpu.brand_string"))
                (cores ,(string->number (or (shell-command "sysctl -n hw.ncpu") "0")))
                (memory-gb ,(let ((bytes (shell-command "sysctl -n hw.memsize")))
                             (if bytes
                                 (exact (round (/ (string->number bytes) 1073741824)))
                                 0)))
                (model ,model)))
             ;; Linux
             ((and os-str (string=? os-str "Linux"))
              `((cpu ,(shell-command "grep -m1 'model name' /proc/cpuinfo | cut -d: -f2 | xargs"))
                (cores ,(string->number (or (shell-command "nproc") "0")))
                (memory-gb ,(let ((kb (shell-command "grep MemTotal /proc/meminfo | awk '{print $2}'")))
                             (if kb
                                 (exact (round (/ (string->number kb) 1048576)))
                                 0)))
                (model ,model)))
             (else `((model ,model))))))))

  (define (introspect-network)
    "Introspect network configuration (IPv4 and IPv6)"
    (let ((os-str (shell-command "uname -s")))
      `(network
        ,@(cond
           ;; macOS - get active interfaces with both IPv4 and IPv6
           ((and os-str (string=? os-str "Darwin"))
            (let ((interfaces (shell-lines "ifconfig -l")))
              `((interfaces
                 ,@(filter-map
                    (lambda (iface)
                      (let* ((ipv4 (shell-command
                                    (string-append "ifconfig " iface " 2>/dev/null | grep 'inet ' | awk '{print $2}'")))
                             (ipv6 (shell-command
                                    (string-append "ifconfig " iface " 2>/dev/null | grep 'inet6 ' | grep -v '%' | grep -v 'fe80' | awk '{print $2}'")))
                             (ipv6-link (shell-command
                                         (string-append "ifconfig " iface " 2>/dev/null | grep 'inet6 fe80' | awk '{print $2}' | cut -d% -f1"))))
                        (and (or (and ipv4 (not (string=? ipv4 "")))
                                 (and ipv6 (not (string=? ipv6 ""))))
                             `(,(string->symbol iface)
                               ,@(if (and ipv4 (not (string=? ipv4 ""))) `((ipv4 ,ipv4)) '())
                               ,@(if (and ipv6 (not (string=? ipv6 ""))) `((ipv6 ,ipv6)) '())
                               ,@(if (and ipv6-link (not (string=? ipv6-link ""))) `((ipv6-link ,ipv6-link)) '())))))
                    (if (pair? interfaces)
                        (string-split (car interfaces))
                        '())))
                (gateway ,(shell-command "route -n get default 2>/dev/null | grep gateway | awk '{print $2}'"))
                (gateway6 ,(shell-command "route -n get -inet6 default 2>/dev/null | grep gateway | awk '{print $2}'")))))
           ;; Linux - get both IPv4 and IPv6
           ((and os-str (string=? os-str "Linux"))
            `((interfaces
               ,@(let ((ifaces (shell-lines "ip link show | grep '^[0-9]' | awk -F': ' '{print $2}'")))
                   (filter-map
                    (lambda (iface)
                      (let* ((ipv4 (shell-command
                                    (string-append "ip -4 addr show " iface " 2>/dev/null | grep inet | awk '{print $2}' | cut -d/ -f1")))
                             (ipv6 (shell-command
                                    (string-append "ip -6 addr show " iface " scope global 2>/dev/null | grep inet6 | awk '{print $2}' | cut -d/ -f1")))
                             (ipv6-link (shell-command
                                         (string-append "ip -6 addr show " iface " scope link 2>/dev/null | grep inet6 | awk '{print $2}' | cut -d/ -f1"))))
                        (and (or (and ipv4 (not (string=? ipv4 "")))
                                 (and ipv6 (not (string=? ipv6 ""))))
                             `(,(string->symbol iface)
                               ,@(if (and ipv4 (not (string=? ipv4 ""))) `((ipv4 ,ipv4)) '())
                               ,@(if (and ipv6 (not (string=? ipv6 ""))) `((ipv6 ,ipv6)) '())
                               ,@(if (and ipv6-link (not (string=? ipv6-link ""))) `((ipv6-link ,ipv6-link)) '())))))
                    ifaces)))
              (gateway ,(shell-command "ip route | grep default | awk '{print $3}'"))
              (gateway6 ,(shell-command "ip -6 route | grep default | awk '{print $3}'"))))
           (else '())))))

  (define (introspect-storage)
    "Introspect storage configuration"
    (let ((os-str (shell-command "uname -s")))
      `(storage
        ,@(cond
           ;; macOS
           ((and os-str (string=? os-str "Darwin"))
            (let* ((df-out (shell-command "df -g / | tail -1"))
                   (parts (if df-out (string-split df-out) '())))
              (if (>= (length parts) 4)
                  `((root-total-gb ,(string->number (list-ref parts 1)))
                    (root-used-gb ,(string->number (list-ref parts 2)))
                    (root-avail-gb ,(string->number (list-ref parts 3))))
                  '())))
           ;; Linux
           ((and os-str (string=? os-str "Linux"))
            (let* ((df-out (shell-command "df -BG / | tail -1"))
                   (parts (if df-out (string-split df-out) '())))
              (if (>= (length parts) 4)
                  `((root-total-gb ,(string->number (string-delete #\G (list-ref parts 1))))
                    (root-used-gb ,(string->number (string-delete #\G (list-ref parts 2))))
                    (root-avail-gb ,(string->number (string-delete #\G (list-ref parts 3)))))
                  '())))
           (else '())))))

  (define (count-vault-subdir vault-path subdir)
    "Count non-hidden items in vault subdirectory"
    (let ((path (string-append vault-path "/" subdir)))
      (if (directory-exists? path)
          (length (filter (lambda (f) (not (string-prefix? "." f)))
                          (directory-list path)))
          0)))

  (define (introspect-realm)
    "Introspect realm/vault configuration"
    (let* ((vault-path (or (getenv "VAULT_PATH") ".vault"))
           (vault-exists (directory-exists? vault-path)))
      `(realm
        (vault-path ,vault-path)
        (vault-exists ,vault-exists)
        ,@(if vault-exists
              (let ((obj-count (count-vault-subdir vault-path "objects"))
                    (key-count (count-vault-subdir vault-path "keys"))
                    (release-count (count-vault-subdir vault-path "releases"))
                    (audit-count (count-vault-subdir vault-path "audit")))
                `((has-keystore ,(directory-exists? (string-append vault-path "/keystore")))
                  (has-audit ,(directory-exists? (string-append vault-path "/audit")))
                  (objects ,obj-count)
                  (keys ,key-count)
                  (releases ,release-count)
                  (audits ,audit-count)))
              '()))))

  (define (introspect-codebase)
    "Introspect Cyberspace codebase - LOC and module inventory"
    (let* ((base-dir (or (getenv "CYBERSPACE_HOME")
                         (current-directory)))
           ;; Count .scm files and lines
           (loc-output (shell-command
                        (string-append "find " base-dir " -name '*.scm' -type f 2>/dev/null | "
                                       "xargs wc -l 2>/dev/null | tail -1 | awk '{print $1}'")))
           (file-count (shell-command
                        (string-append "find " base-dir " -name '*.scm' -type f 2>/dev/null | wc -l")))
           ;; Count modules (files with (module ...))
           (module-count (shell-command
                          (string-append "grep -l '^(module' " base-dir "/*.scm 2>/dev/null | wc -l")))
           ;; Count memos (numbered, excluding reserved)
           (memo-count (shell-command
                       (string-append "ls " base-dir "/docs/notes/memo-[0-9]*.scm 2>/dev/null | "
                                      "xargs grep -L '(reserved)' 2>/dev/null | wc -l"))))
      `(codebase
        (loc ,(if loc-output (string->number (string-trim-both loc-output)) 0))
        (files ,(if file-count (string->number (string-trim-both file-count)) 0))
        (modules ,(if module-count (string->number (string-trim-both module-count)) 0))
        (memos ,(if memo-count (string->number (string-trim-both memo-count)) 0)))))

  (define (parse-memo-txt path)
    "Parse Memo .txt file for metadata"
    (guard (exn [#t #f])
      (let* ((lines (shell-lines (string-append "head -4 " path)))
             (line1 (and (pair? lines) (car lines))))
        (and line1
             (let ((colon-pos (string-index line1 #\:)))
               (and colon-pos
                    (let* ((num-part (substring line1 5 colon-pos))  ; "Memo-" is 5 chars
                           (title (string-trim-both (substring line1 (+ colon-pos 1)
                                                              (string-length line1))))
                           (line3 (and (>= (length lines) 3) (list-ref lines 2)))
                           (line4 (and (>= (length lines) 4) (list-ref lines 3)))
                           (status (and line3
                                        (string-prefix? "Status:" line3)
                                        (string-trim-both (substring line3 7
                                                                     (string-length line3)))))
                           (category (and line4
                                          (string-prefix? "Category:" line4)
                                          (string-trim-both (substring line4 9
                                                                       (string-length line4))))))
                      `((number ,num-part)
                        (title ,title)
                        (status ,(or status "unknown"))
                        (category ,(or category "unknown"))))))))))

  (define (introspect-library)
    "Introspect the Library of Cyberspace - Memo catalog from .txt files"
    (let* ((base-dir (or (getenv "CYBERSPACE_HOME")
                         (current-directory)))
           (memo-dir (string-append base-dir "/docs/notes"))
           (files (shell-lines
                   (string-append "ls " memo-dir "/memo-[0-9]*.txt 2>/dev/null | sort"))))
      (if (null? files)
          '(library (count 0) (memos ()))
          (let ((memos (filter-map
                        (lambda (path)
                          (let ((meta (parse-memo-txt path)))
                            (and meta
                                 `(memo ,@meta (path ,path)))))
                        files)))
            `(library
              (count ,(length memos))
              (memos ,memos))))))

  ;; Cache for static system info (hardware, network, versions don't change)
  (define *hardware-cache* #f)
  (define *network-cache* #f)
  (define *storage-cache* #f)
  (define *codebase-cache* #f)
  (define *versions-cache* #f)

  (define (introspect-system-refresh!)
    "Refresh all cached system info"
    (set! *hardware-cache* (introspect-hardware))
    (set! *network-cache* (introspect-network))
    (set! *storage-cache* (introspect-storage))
    (set! *codebase-cache* (introspect-codebase))
    (set! *versions-cache*
      `(versions
        (chez ,(shell-command "scheme --version 2>&1 | head -1"))
        (libsodium ,(shell-command "pkg-config --modversion libsodium 2>/dev/null || echo unknown")))))

  (define (introspect-system)
    "Full system introspection - uses cache for static info"
    (unless *hardware-cache*
      (introspect-system-refresh!))
    `(system-info
      (timestamp ,(current-seconds))
      (lamport-time ,(lamport-time))
      (uptime ,(shell-command "uptime | sed 's/.*up //' | sed 's/,.*//'"))
      ,*hardware-cache*
      ,*network-cache*
      ,*storage-cache*
      ,(introspect-realm)  ; realm can change (vault state)
      ,*codebase-cache*
      ,*versions-cache*))

  ;; ============================================================
  ;; Enrollment Display Formatting
  ;; ============================================================

  (define (make-enroll-box title w)
    "Create a box drawing closure with given title and width"
    (let* ((title-padded (string-append " " title " "))
           (title-len (string-length title-padded))
           (left-pad (quotient (- w title-len) 2))
           (right-pad (- w title-len left-pad))
           (header (string-append "\x250C;" (make-string left-pad #\x2500;) title-padded (make-string right-pad #\x2500;) "\x2510;\n"))
           (footer (string-append "\x2514;" (make-string w #\x2500;) "\x2518;\n")))
      (lambda (cmd . args)
        (case cmd
          ((header) header)
          ((footer) footer)
          ((line) (let* ((content (if (null? args) "" (car args)))
                         (pad (- w (string-length content) 2)))
                    (string-append "\x2502; " content (make-string (max 0 pad) #\space) " \x2502;\n")))))))

  (define (format-enrollment-display name code)
    "Format enrollment request display for node"
    (let* ((code-str (verification-code->display code))
           (name-str (val->string name))
           (box (make-enroll-box "enroll" 50)))
      (string-append
       "\n"
       (box 'header)
       (box 'line (string-append "Requesting enrollment as: " name-str))
       (box 'line)
       (box 'line "Verification code (FIPS-181):")
       (box 'line (string-append "    " code-str))
       (box 'line)
       (box 'line "Waiting for master to approve...")
       (box 'footer))))

  (define (format-approval-display name code host hw)
    "Format enrollment approval display for master"
    (let* ((code-str (verification-code->display code))
           (name-str (val->string name))
           (host-str (val->string host))
           (cpu (or (and hw (assq 'cpu (cdr hw))
                         (cadr (assq 'cpu (cdr hw))))
                    "unknown"))
           (cpu-short (if (> (string-length cpu) 30)
                         (substring cpu 0 30)
                         cpu))
           (mem (or (and hw (assq 'memory-gb (cdr hw))
                         (cadr (assq 'memory-gb (cdr hw))))
                    "?"))
           (box (make-enroll-box "approve" 50)))
      (string-append
       "\n"
       (box 'header)
       (box 'line "Enrollment request received")
       (box 'line)
       (box 'line (string-append "Name: " name-str))
       (box 'line (string-append "From: " host-str))
       (box 'line (string-append "Hardware: " cpu-short))
       (box 'line (string-append "Memory: " (val->string mem) " GB"))
       (box 'line)
       (box 'line "Verification code (FIPS-181):")
       (box 'line (string-append "    " code-str))
       (box 'line)
       (box 'line (string-append "Match what you see on " name-str "?"))
       (box 'line)
       (box 'line "[y] Approve   [n] Reject   [?] Help")
       (box 'footer))))

  ;; ============================================================
  ;; Enrollment Protocol - Node Side
  ;; ============================================================

  (define (enroll-request name . rest)
    "Request enrollment in the confederation.
     Returns: (values pubkey privkey code)

     name: proposed node name (string or symbol)
     Optional keyword: port: N (default 7654)"

    ;; Generate keypair
    (let* ((keypair (ed25519-keypair))
           (pubkey (car keypair))
           (privkey (cadr keypair))
           (code (pubkey->verification-code pubkey)))

      ;; Display verification code (FIPS-181)
      (display (format-enrollment-display name code))

      ;; Return what the caller needs
      (values pubkey privkey code)))

  (define (enroll-wait pubkey privkey words name . rest)
    "Wait for master approval.
     Returns: certificate on success, #f on timeout/rejection"
    (let ((timeout (get-key rest 'timeout: 300)))
      ;; This would integrate with mdns module to wait for response
      ;; For now, return a placeholder indicating manual process needed
      `(awaiting-approval
        (name ,name)
        (words ,words)
        (timeout ,timeout))))

  (define (enroll-complete cert privkey vault-path)
    "Complete enrollment by storing certificate and key.
     Returns: #t on success"
    ;; Store in vault keystore
    (let ((keystore-path (string-append vault-path "/keystore")))
      ;; Create keystore directory if needed
      (unless (directory-exists? keystore-path)
        (system (string-append "mkdir -p " keystore-path)))
      ;; Store would happen here
      #t))

  ;; ============================================================
  ;; Enrollment Protocol - Master Side
  ;; ============================================================

  (define *enrollment-requests* '())

  (define (enroll-listen . rest)
    "Listen for enrollment requests.
     Returns requests as they arrive."
    ;; This integrates with mdns module
    ;; Returns list of pending requests
    *enrollment-requests*)

  (define (enroll-approve request master-key . rest)
    "Approve an enrollment request.
     Returns: signed certificate"
    (let* ((role (get-key rest 'role: 'full))
           (validity-days (get-key rest 'validity-days: 365))
           (name (cadr (assq 'name request)))
           (pubkey (cadr (assq 'pubkey request)))
           (now (current-seconds))
           (not-after (+ now (* validity-days 24 60 60))))

      ;; Create enrollment certificate
      (create-enrollment-cert
       name pubkey master-key
       'role: role
       'not-before: now
       'not-after: not-after)))

  (define (enroll-reject request . rest)
    "Reject an enrollment request.
     Returns: rejection notice"
    (let ((reason (get-key rest 'reason: "Rejected by operator")))
      `(enrollment-rejected
        (name ,(cadr (assq 'name request)))
        (reason ,reason)
        (timestamp ,(current-seconds)))))

  ;; ============================================================
  ;; Certificate Creation
  ;; ============================================================

  (define (create-enrollment-cert name pubkey master-key . rest)
    "Create and sign an enrollment certificate.

     name: node name (symbol)
     pubkey: node's public key (bytevector)
     master-key: master's signing key (bytevector, 64 bytes)
     Optional keywords: role: not-before: not-after:
     Returns: signed SPKI certificate s-expression"

    (let* ((role (get-key rest 'role: 'full))
           (not-before (get-key rest 'not-before: (current-seconds)))
           (not-after (get-key rest 'not-after: (+ (current-seconds) 31536000)))
           (capabilities (case role
                           ((master) '(vault-read vault-write sync-participate
                                       witness-vote master-delegate))
                           ((full) '(vault-read vault-write sync-participate witness-vote))
                           ((witness) '(vault-read sync-participate witness-vote))
                           ((archive) '(vault-read sync-receive))
                           (else '(vault-read))))

           ;; Create certificate body
           (cert-body `(spki-cert
                        (issuer (public-key (ed25519 ,(bytevector->base64
                                                        (ed25519-secret-to-public master-key)))))
                        (subject (public-key (ed25519 ,(bytevector->base64 pubkey))))
                        (name ,name)
                        (role ,role)
                        (capabilities ,capabilities)
                        (validity
                         (not-before ,not-before)
                         (not-after ,not-after))
                        (issued ,(current-seconds))))

           ;; Serialize for signing
           (cert-bytes (string->utf8 (with-output-to-string
                                       (lambda () (write cert-body)))))

           ;; Sign with master key
           (signature (ed25519-sign master-key cert-bytes)))

      ;; Return signed certificate
      `(signed-enrollment-cert
        ,cert-body
        (signature (ed25519 ,(bytevector->base64 signature))))))

  (define (renew-certificate old-cert master-key . rest)
    "Renew an existing certificate.
     Returns: new signed certificate"
    (let* ((validity-days (get-key rest 'validity-days: 365))
           (cert-body (cadr old-cert))
           (name (cadr (assq 'name cert-body)))
           (subject (cadr (assq 'subject cert-body)))
           (role (cadr (assq 'role cert-body)))
           (now (current-seconds))
           (not-after (+ now (* validity-days 24 60 60)))
           ;; Build new cert body
           (new-cert-body
            `(spki-cert
              (issuer ,(cadr (assq 'issuer cert-body)))
              (subject ,subject)
              (name ,name)
              (role ,role)
              (capabilities ,(cadr (assq 'capabilities cert-body)))
              (validity
               (not-before ,now)
               (not-after ,not-after))
              (issued ,now)
              (renewed-from ,(cadr (assq 'issued cert-body)))))
           ;; Serialize and sign
           (cert-bytes (string->utf8 (with-output-to-string
                                       (lambda () (write new-cert-body)))))
           (signature (ed25519-sign master-key cert-bytes)))

      ;; Return signed certificate
      `(signed-enrollment-cert
        ,new-cert-body
        (signature (ed25519 ,(bytevector->base64 signature))))))

  (define (revoke-certificate cert master-key . rest)
    "Revoke a certificate.
     Returns: revocation record for distribution"
    (let* ((reason (get-key rest 'reason: 'unspecified))
           (cert-body (cadr cert))
           (name (cadr (assq 'name cert-body)))
           (subject (cadr (assq 'subject cert-body)))
           ;; Build revocation body
           (revocation-body
            `(revocation-data
              (certificate-name ,name)
              (certificate-subject ,subject)
              (revoked-at ,(current-seconds))
              (reason ,reason)
              (issuer ,(cadr (assq 'issuer cert-body)))))
           ;; Serialize and sign
           (rev-bytes (string->utf8 (with-output-to-string
                                      (lambda () (write revocation-body)))))
           (signature (ed25519-sign master-key rev-bytes)))

      ;; Return signed revocation
      `(revocation
        ,@(cdr revocation-body)  ; expand inner fields
        (signature (ed25519 ,(bytevector->base64 signature))))))

  ;; ============================================================
  ;; Presence Announcement (_cyberspace._tcp service)
  ;; ============================================================

  (define *presence-running* #f)

  (define (announce-presence name . rest)
    "Start announcing as Cyberspace node on local network.
     Registers _cyberspace._tcp service via dns-sd (macOS) or avahi (Linux).

     name: node name (shown in discovery)
     Optional keyword: port: N (default 7654)"

    (let ((port (get-key rest 'port: 7654)))
      (when *presence-running*
        (stop-presence))

      (let* ((os-str (shell-command "uname -s"))
             (name-str (if (symbol? name) (symbol->string name) name)))
        (cond
          ((and os-str (string=? os-str "Darwin"))
           ;; macOS: dns-sd -R <name> _cyberspace._tcp local. <port>
           (let ((cmd (string-append "dns-sd -R '" name-str "' _cyberspace._tcp local. "
                                     (number->string port) " &")))
             (set! *presence-running* #t)
             (system cmd)
             (print "Announcing: " name-str " (_cyberspace._tcp on port " port ")")
             `(presence-started (name ,name-str) (port ,port) (service "_cyberspace._tcp"))))

          ((and os-str (string=? os-str "Linux"))
           ;; Linux: avahi-publish -s <name> _cyberspace._tcp <port>
           (let ((cmd (string-append "avahi-publish -s '" name-str "' _cyberspace._tcp "
                                     (number->string port) " &")))
             (set! *presence-running* #t)
             (system cmd)
             (print "Announcing: " name-str " (_cyberspace._tcp on port " port ")")
             `(presence-started (name ,name-str) (port ,port) (service "_cyberspace._tcp"))))

          (else
           (print "mDNS announcement not available on this platform")
           #f)))))

  (define (stop-presence)
    "Stop presence announcement"
    (set! *presence-running* #f)
    ;; Kill background dns-sd/avahi process
    (system "pkill -f '_cyberspace._tcp' 2>/dev/null")
    (print "Presence announcement stopped"))

  (define *cyberspace-service* "_cyberspace._tcp")

  (define (discover-peers . rest)
    "Discover Cyberspace peers on local network via mDNS.
     Uses dns-sd (macOS) or avahi-browse (Linux) to find _cyberspace._tcp services.
     Optional keyword: timeout: N (default 3)
     Returns: list of peer names"
    (let* ((timeout (get-key rest 'timeout: 3))
           (os-str (shell-command "uname -s"))
           (cmd (cond
                  ((and os-str (string=? os-str "Darwin"))
                   ;; macOS: dns-sd -B _cyberspace._tcp local.
                   (string-append "timeout " (number->string timeout)
                                  " dns-sd -B " *cyberspace-service* " local. 2>/dev/null"
                                  " | grep 'Add' | awk '{print $7}'"))
                  ((and os-str (string=? os-str "Linux"))
                   ;; Linux: avahi-browse -t _cyberspace._tcp
                   (string-append "timeout " (number->string timeout)
                                  " avahi-browse -t -p " *cyberspace-service*
                                  " 2>/dev/null | grep '^=' | cut -d';' -f4"))
                  (else #f))))
      (if (not cmd)
          (begin
            (print "mDNS discovery not available on this platform")
            '())
          (let ((lines (shell-lines cmd)))
            (if (null? lines)
                (begin
                  (print "No Cyberspace peers found (service: " *cyberspace-service* ")")
                  '())
                (begin
                  (print "")
                  (print "Cyberspace peers:")
                  (for-each (lambda (name) (print "  " name)) lines)
                  (print "")
                  lines))))))

  ;; ============================================================
  ;; Hex Helpers
  ;; ============================================================

  (define hex-chars "0123456789abcdef")

  (define (byte->hex byte)
    "Convert byte to two-character hex string"
    (string (string-ref hex-chars (quotient byte 16))
            (string-ref hex-chars (modulo byte 16))))

) ;; end library
