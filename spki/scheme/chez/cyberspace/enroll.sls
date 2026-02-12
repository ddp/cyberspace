;;; enroll.sls - Node Enrollment and Presence (Memo-044)
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
;;; Ported from Chicken's enroll.scm.
;;; Changes: module -> library, #!key -> get-key, srfi-1/13 inlined,
;;;          (chicken process) -> process compat, base64 prefix removed,
;;;          inexact->exact -> exact, quotient -> div.

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
                printf format
                with-output-to-string
                current-time time-second
                file-directory? current-directory
                getenv)
          (cyberspace crypto-ffi)
          (cyberspace wordlist)
          (only (cyberspace vault) lamport-time)
          (cyberspace chicken-compatibility chicken)
          (cyberspace chicken-compatibility blob)
          (cyberspace chicken-compatibility base64)
          (only (cyberspace chicken-compatibility process)
                with-input-from-pipe read-line system)
          (only (cyberspace chicken-compatibility file)
                directory-exists? create-directory directory
                get-environment-variable current-seconds))

  ;; ============================================================
  ;; Inline Helpers (from srfi-1, srfi-13, chicken pathname)
  ;; ============================================================

  (define (string-prefix? prefix str)
    (and (>= (string-length str) (string-length prefix))
         (string=? (substring str 0 (string-length prefix)) prefix)))

  (define (string-trim-both str)
    (let* ((len (string-length str))
           (start (let loop ((i 0))
                    (if (or (>= i len) (not (char-whitespace? (string-ref str i))))
                        i (loop (+ i 1)))))
           (end (let loop ((i (- len 1)))
                  (if (or (< i start) (not (char-whitespace? (string-ref str i))))
                      (+ i 1) (loop (- i 1))))))
      (substring str start end)))

  (define (string-chomp str suffix)
    (let ((slen (string-length str))
          (xlen (string-length suffix)))
      (if (and (>= slen xlen)
               (string=? (substring str (- slen xlen) slen) suffix))
          (substring str 0 (- slen xlen))
          str)))

  (define (string-delete char str)
    (list->string (filter (lambda (c) (not (char=? c char))) (string->list str))))

  (define (string-index str char)
    (let loop ((i 0))
      (cond
        ((>= i (string-length str)) #f)
        ((char=? (string-ref str i) char) i)
        (else (loop (+ i 1))))))

  (define (make-pathname dir file)
    (if (string=? file "") dir
        (string-append dir "/" file)))

  (define (pathname-directory path)
    (let loop ((i (- (string-length path) 1)))
      (cond
        ((< i 0) ".")
        ((char=? (string-ref path i) #\/) (substring path 0 i))
        (else (loop (- i 1))))))

  (define (filter-map f lst)
    (let loop ((rest lst) (acc '()))
      (if (null? rest)
          (reverse acc)
          (let ((result (f (car rest))))
            (loop (cdr rest)
                  (if result (cons result acc) acc))))))

  (define (substring-match? str pattern)
    (let ((slen (string-length str))
          (plen (string-length pattern)))
      (let loop ((i 0))
        (cond ((> (+ i plen) slen) #f)
              ((string=? (substring str i (+ i plen)) pattern) #t)
              (else (loop (+ i 1)))))))

  ;; ============================================================
  ;; Verification Codes (FIPS-181)
  ;; ============================================================

  (define (pubkey->verification-code pubkey)
    (pubkey->syllables pubkey))

  (define (verification-code->display code)
    (syllables->display code))

  ;; ============================================================
  ;; System Introspection - Know Thyself
  ;; ============================================================

  (define (shell-command cmd)
    ;; Run shell command, return trimmed output or #f
    (guard (exn [#t #f])
      (let ((result (with-input-from-pipe cmd read-line)))
        (if (eof-object? result) #f result))))

  (define (shell-lines cmd)
    ;; Run shell command, return list of lines
    (guard (exn [#t '()])
      (with-input-from-pipe cmd
        (lambda ()
          (let loop ((lines '()))
            (let ((line (read-line)))
              (if (eof-object? line)
                  (reverse lines)
                  (loop (cons line lines)))))))))

  ;; ============================================================
  ;; Weave Benchmark - Measure actual compute speed
  ;; ============================================================

  (define *benchmark-iterations* 10000)

  (define (probe-scaling)
    ;; Measure compute speed (weave = hashes/second).
    (let* ((test-data (make-blob 64))
           (start (current-seconds))
           (_ (let loop ((i 0) (data test-data))
                (if (< i *benchmark-iterations*)
                    (loop (+ i 1) (sha256-hash data))
                    data)))
           (end (current-seconds))
           (elapsed-sec (max 1 (- end start))))
      (exact (round (/ *benchmark-iterations* elapsed-sec)))))

  ;; Mobile device detection patterns
  (define *mobile-patterns*
    '("MacBook" "Macbook" "Book" "Laptop" "laptop"
      "iPad" "iPhone" "Surface" "ThinkPad" "XPS"))

  (define (detect-mobile model)
    (if (not model)
        #f
        (let ((model-down (string-downcase model)))
          (let loop ((patterns *mobile-patterns*))
            (if (null? patterns)
                #f
                (let ((pat-down (string-downcase (car patterns))))
                  (if (substring-match? model-down pat-down)
                      #t
                      (loop (cdr patterns)))))))))

  (define (introspect-hardware)
    ;; Introspect hardware configuration.
    (let ((os (shell-command "uname -s"))
          (arch (shell-command "uname -m"))
          (hostname (shell-command "hostname -s")))
      (let* ((model (cond
                     ((and os (string=? os "Darwin"))
                      (shell-command "sysctl -n hw.model"))
                     ((and os (string=? os "Linux"))
                      (or (shell-command "cat /sys/devices/virtual/dmi/id/product_name 2>/dev/null")
                          (shell-command "hostnamectl --json short 2>/dev/null | grep -o '\"Chassis\":\"[^\"]*\"' | cut -d'\"' -f4")))
                     (else #f)))
             (mobile (detect-mobile model))
             (weave (probe-scaling)))
        `(hardware
          (os ,os)
          (arch ,arch)
          (hostname ,hostname)
          (kernel ,(shell-command "uname -r"))
          (mobile ,mobile)
          (weave ,weave)
          ,@(cond
             ((and os (string=? os "Darwin"))
              `((cpu ,(shell-command "sysctl -n machdep.cpu.brand_string"))
                (cores ,(string->number (or (shell-command "sysctl -n hw.ncpu") "0")))
                (memory-gb ,(let ((bytes (shell-command "sysctl -n hw.memsize")))
                             (if bytes
                                 (exact (round (/ (string->number bytes) 1073741824)))
                                 0)))
                (model ,model)))
             ((and os (string=? os "Linux"))
              `((cpu ,(shell-command "grep -m1 'model name' /proc/cpuinfo | cut -d: -f2 | xargs"))
                (cores ,(string->number (or (shell-command "nproc") "0")))
                (memory-gb ,(let ((kb (shell-command "grep MemTotal /proc/meminfo | awk '{print $2}'")))
                             (if kb
                                 (exact (round (/ (string->number kb) 1048576)))
                                 0)))
                (model ,model)))
             (else `((model ,model))))))))

  (define (introspect-network)
    ;; Introspect network configuration (IPv4 and IPv6)
    (let ((os (shell-command "uname -s")))
      `(network
        ,@(cond
           ((and os (string=? os "Darwin"))
            (let ((interfaces (shell-lines "ifconfig -l")))
              `((interfaces
                 ,@(filter-map
                    (lambda (iface)
                      (let* ((ipv4 (shell-command
                                    (string-append "ifconfig " iface
                                                   " 2>/dev/null | grep 'inet ' | awk '{print $2}'")))
                             (ipv6 (shell-command
                                    (string-append "ifconfig " iface
                                                   " 2>/dev/null | grep 'inet6 ' | grep -v '%' | grep -v 'fe80' | awk '{print $2}'")))
                             (ipv6-link (shell-command
                                         (string-append "ifconfig " iface
                                                        " 2>/dev/null | grep 'inet6 fe80' | awk '{print $2}' | cut -d% -f1"))))
                        (and (or (and ipv4 (not (string=? ipv4 "")))
                                 (and ipv6 (not (string=? ipv6 ""))))
                             `(,(string->symbol iface)
                               ,@(if (and ipv4 (not (string=? ipv4 ""))) `((ipv4 ,ipv4)) '())
                               ,@(if (and ipv6 (not (string=? ipv6 ""))) `((ipv6 ,ipv6)) '())
                               ,@(if (and ipv6-link (not (string=? ipv6-link "")))
                                     `((ipv6-link ,ipv6-link)) '())))))
                    (if (pair? interfaces)
                        (string-split (car interfaces))
                        '())))
                (gateway ,(shell-command "route -n get default 2>/dev/null | grep gateway | awk '{print $2}'"))
                (gateway6 ,(shell-command "route -n get -inet6 default 2>/dev/null | grep gateway | awk '{print $2}'")))))
           ((and os (string=? os "Linux"))
            `((interfaces
               ,@(let ((ifaces (shell-lines "ip link show | grep '^[0-9]' | awk -F': ' '{print $2}'")))
                   (filter-map
                    (lambda (iface)
                      (let* ((ipv4 (shell-command
                                    (string-append "ip -4 addr show " iface
                                                   " 2>/dev/null | grep inet | awk '{print $2}' | cut -d/ -f1")))
                             (ipv6 (shell-command
                                    (string-append "ip -6 addr show " iface
                                                   " scope global 2>/dev/null | grep inet6 | awk '{print $2}' | cut -d/ -f1")))
                             (ipv6-link (shell-command
                                         (string-append "ip -6 addr show " iface
                                                        " scope link 2>/dev/null | grep inet6 | awk '{print $2}' | cut -d/ -f1"))))
                        (and (or (and ipv4 (not (string=? ipv4 "")))
                                 (and ipv6 (not (string=? ipv6 ""))))
                             `(,(string->symbol iface)
                               ,@(if (and ipv4 (not (string=? ipv4 ""))) `((ipv4 ,ipv4)) '())
                               ,@(if (and ipv6 (not (string=? ipv6 ""))) `((ipv6 ,ipv6)) '())
                               ,@(if (and ipv6-link (not (string=? ipv6-link "")))
                                     `((ipv6-link ,ipv6-link)) '())))))
                    ifaces)))
              (gateway ,(shell-command "ip route | grep default | awk '{print $3}'"))
              (gateway6 ,(shell-command "ip -6 route | grep default | awk '{print $3}'"))))
           (else '())))))

  (define (introspect-storage)
    ;; Introspect storage configuration
    (let ((os (shell-command "uname -s")))
      `(storage
        ,@(cond
           ((and os (string=? os "Darwin"))
            (let* ((df-out (shell-command "df -g / | tail -1"))
                   (parts (if df-out (string-split df-out) '())))
              (if (>= (length parts) 4)
                  `((root-total-gb ,(string->number (list-ref parts 1)))
                    (root-used-gb ,(string->number (list-ref parts 2)))
                    (root-avail-gb ,(string->number (list-ref parts 3))))
                  '())))
           ((and os (string=? os "Linux"))
            (let* ((df-out (shell-command "df -BG / | tail -1"))
                   (parts (if df-out (string-split df-out) '())))
              (if (>= (length parts) 4)
                  `((root-total-gb ,(string->number (string-delete #\G (list-ref parts 1))))
                    (root-used-gb ,(string->number (string-delete #\G (list-ref parts 2))))
                    (root-avail-gb ,(string->number (string-delete #\G (list-ref parts 3)))))
                  '())))
           (else '())))))

  (define (count-vault-subdir vault-path subdir)
    ;; Count non-hidden items in vault subdirectory
    (let ((path (make-pathname vault-path subdir)))
      (if (directory-exists? path)
          (length (filter (lambda (f) (not (string-prefix? "." f)))
                          (directory path)))
          0)))

  (define (introspect-realm)
    ;; Introspect realm/vault configuration
    (let* ((vault-path (or (get-environment-variable "VAULT_PATH") ".vault"))
           (vault-exists (directory-exists? vault-path)))
      `(realm
        (vault-path ,vault-path)
        (vault-exists ,vault-exists)
        ,@(if vault-exists
              (let ((obj-count (count-vault-subdir vault-path "objects"))
                    (key-count (count-vault-subdir vault-path "keys"))
                    (release-count (count-vault-subdir vault-path "releases"))
                    (audit-count (count-vault-subdir vault-path "audit")))
                `((has-keystore ,(directory-exists? (make-pathname vault-path "keystore")))
                  (has-audit ,(directory-exists? (make-pathname vault-path "audit")))
                  (objects ,obj-count)
                  (keys ,key-count)
                  (releases ,release-count)
                  (audits ,audit-count)))
              '()))))

  (define (introspect-codebase)
    ;; Introspect Cyberspace codebase - LOC and module inventory
    (let* ((base-dir (or (get-environment-variable "CYBERSPACE_HOME")
                         (current-directory)))
           (loc-output (shell-command
                        (string-append "find " base-dir " -name '*.scm' -type f 2>/dev/null | "
                                       "xargs wc -l 2>/dev/null | tail -1 | awk '{print $1}'")))
           (file-count (shell-command
                        (string-append "find " base-dir " -name '*.scm' -type f 2>/dev/null | wc -l")))
           (module-count (shell-command
                          (string-append "grep -l '^(module' " base-dir "/*.scm 2>/dev/null | wc -l")))
           (memo-count (shell-command
                       (string-append "ls " base-dir "/docs/notes/memo-[0-9]*.scm 2>/dev/null | "
                                      "xargs grep -L '(reserved)' 2>/dev/null | wc -l")))
           (tcb-dir (let ((trimmed (string-chomp base-dir "/")))
                      (string-append (pathname-directory trimmed) "/tcb")))
           (tcb-output (shell-command
                        (string-append "wc -l " tcb-dir "/spki_tcb.ml " tcb-dir "/signature.ml "
                                       tcb-dir "/export.ml 2>/dev/null | tail -1 | awk '{print $1}'"))))
      `(codebase
        (loc ,(if loc-output (string->number (string-trim-both loc-output)) 0))
        (tcb ,(if tcb-output (string->number (string-trim-both tcb-output)) 0))
        (files ,(if file-count (string->number (string-trim-both file-count)) 0))
        (modules ,(if module-count (string->number (string-trim-both module-count)) 0))
        (memos ,(if memo-count (string->number (string-trim-both memo-count)) 0)))))

  (define (parse-memo-txt path)
    ;; Parse Memo .txt file for metadata
    (guard (exn [#t #f])
      (with-input-from-file path
        (lambda ()
          (let ((line1 (read-line))
                (line2 (read-line))
                (line3 (read-line))
                (line4 (read-line)))
            (and (not (eof-object? line1))
                 (let ((colon-pos (string-index line1 #\:)))
                   (and colon-pos
                        (let* ((num-part (substring line1 5 colon-pos))
                               (title (string-trim-both
                                       (substring line1 (+ colon-pos 1) (string-length line1))))
                               (status (and (not (eof-object? line3))
                                            (string-prefix? "Status:" line3)
                                            (string-trim-both
                                             (substring line3 7 (string-length line3)))))
                               (category (and (not (eof-object? line4))
                                              (string-prefix? "Category:" line4)
                                              (string-trim-both
                                               (substring line4 9 (string-length line4))))))
                          `((number ,num-part)
                            (title ,title)
                            (status ,(or status "unknown"))
                            (category ,(or category "unknown"))))))))))))

  (define (introspect-library)
    ;; Introspect the Library of Cyberspace - Memo catalog from .txt files
    (let* ((base-dir (or (get-environment-variable "CYBERSPACE_HOME")
                         (current-directory)))
           (memo-dir (make-pathname base-dir "docs/notes"))
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

  ;; Cache for static system info
  (define *hardware-cache* #f)
  (define *network-cache* #f)
  (define *storage-cache* #f)
  (define *codebase-cache* #f)
  (define *versions-cache* #f)

  (define (introspect-system-refresh!)
    ;; Refresh all cached system info
    (set! *hardware-cache* (introspect-hardware))
    (set! *network-cache* (introspect-network))
    (set! *storage-cache* (introspect-storage))
    (set! *codebase-cache* (introspect-codebase))
    (set! *versions-cache*
      `(versions
        (chez ,(shell-command "chez --version 2>&1 | head -1"))
        (libsodium ,(shell-command "pkg-config --modversion libsodium 2>/dev/null || echo unknown")))))

  (define (introspect-system)
    ;; Full system introspection - uses cache for static info
    (unless *hardware-cache*
      (introspect-system-refresh!))
    `(system-info
      (timestamp ,(current-seconds))
      (lamport-time ,(lamport-time))
      (uptime ,(shell-command "uptime | sed 's/.*up //' | sed 's/,.*//'"))
      ,*hardware-cache*
      ,*network-cache*
      ,*storage-cache*
      ,(introspect-realm)
      ,*codebase-cache*
      ,*versions-cache*))

  ;; ============================================================
  ;; Enrollment Display Formatting
  ;; ============================================================

  (define (val->string x)
    (cond ((string? x) x)
          ((symbol? x) (symbol->string x))
          ((number? x) (number->string x))
          (else (with-output-to-string (lambda () (write x))))))

  (define (pad-right str len)
    (if (>= (string-length str) len)
        (substring str 0 len)
        (string-append str (make-string (- len (string-length str)) #\space))))

  (define (make-box title w)
    ;; Create a box drawing closure with given title and width
    (let* ((title-padded (string-append " " title " "))
           (title-len (string-length title-padded))
           (left-pad (div (- w title-len) 2))
           (right-pad (- w title-len left-pad))
           (header (string-append "\x250C;" (make-string left-pad #\x2500)
                                  title-padded
                                  (make-string right-pad #\x2500) "\x2510;\n"))
           (footer (string-append "\x2514;" (make-string w #\x2500) "\x2518;\n")))
      (lambda (cmd . args)
        (case cmd
          ((header) header)
          ((footer) footer)
          ((line) (let* ((content (if (null? args) "" (car args)))
                         (pad (- w (string-length content) 2)))
                    (string-append "\x2502; " content
                                   (make-string (max 0 pad) #\space)
                                   " \x2502;\n")))))))

  (define (format-enrollment-display name code)
    ;; Format enrollment request display for node
    (let* ((code-str (verification-code->display code))
           (name-str (val->string name))
           (box (make-box "enroll" 50)))
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
    ;; Format enrollment approval display for master
    (let* ((code-str (verification-code->display code))
           (name-str (val->string name))
           (host-str (val->string host))
           (cpu (or (and hw (cadr (assq 'cpu (cdr hw)))) "unknown"))
           (cpu-short (if (> (string-length cpu) 30)
                         (substring cpu 0 30)
                         cpu))
           (mem (or (and hw (cadr (assq 'memory-gb (cdr hw)))) "?"))
           (box (make-box "approve" 50)))
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

  (define (enroll-request name . opts)
    ;; Request enrollment in the confederation.
    ;; Returns: (values pubkey privkey code)
    (let* ((keypair (ed25519-keypair))
           (pubkey (car keypair))
           (privkey (cadr keypair))
           (code (pubkey->verification-code pubkey)))
      (display (format-enrollment-display name code))
      (values pubkey privkey code)))

  (define (enroll-wait pubkey privkey words name . opts)
    ;; Wait for master approval.
    ;; Returns: certificate on success, #f on timeout/rejection
    (let ((timeout (get-key opts 'timeout: 300)))
      `(awaiting-approval
        (name ,name)
        (words ,words)
        (timeout ,timeout))))

  (define (enroll-complete cert privkey vault-path)
    ;; Complete enrollment by storing certificate and key.
    (let ((keystore-path (make-pathname vault-path "keystore")))
      (unless (directory-exists? keystore-path)
        (create-directory keystore-path))
      #t))

  ;; ============================================================
  ;; Enrollment Protocol - Master Side
  ;; ============================================================

  (define *enrollment-requests* '())

  (define (enroll-listen . opts)
    ;; Listen for enrollment requests.
    *enrollment-requests*)

  (define (enroll-approve request master-key . opts)
    ;; Approve an enrollment request. Returns: signed certificate
    (let ((role (get-key opts 'role: 'full))
          (validity-days (get-key opts 'validity-days: 365)))
      (let* ((name (cadr (assq 'name request)))
             (pubkey (cadr (assq 'pubkey request)))
             (now (current-seconds))
             (not-after (+ now (* validity-days 24 60 60))))
        (create-enrollment-cert
         name pubkey master-key
         'role: role
         'not-before: now
         'not-after: not-after))))

  (define (enroll-reject request . opts)
    ;; Reject an enrollment request.
    (let ((reason (get-key opts 'reason: "Rejected by operator")))
      `(enrollment-rejected
        (name ,(cadr (assq 'name request)))
        (reason ,reason)
        (timestamp ,(current-seconds)))))

  ;; ============================================================
  ;; Certificate Creation
  ;; ============================================================

  (define (blob->base64 blob)
    ;; Chez base64-encode takes bytevectors directly
    (base64-encode blob))

  (define hex-chars "0123456789abcdef")

  (define (byte->hex byte)
    (string (string-ref hex-chars (div byte 16))
            (string-ref hex-chars (mod byte 16))))

  (define (create-enrollment-cert name pubkey master-key . opts)
    ;; Create and sign an enrollment certificate.
    (let ((role (get-key opts 'role: 'full))
          (not-before (get-key opts 'not-before: (current-seconds)))
          (not-after (get-key opts 'not-after: (+ (current-seconds) 31536000))))
      (let* ((capabilities (case role
                            ((full) '(vault-read vault-write sync-participate witness-vote))
                            ((witness) '(vault-read sync-participate witness-vote))
                            ((archive) '(vault-read sync-receive))
                            (else '(vault-read))))
             (cert-body `(spki-cert
                          (issuer (public-key (ed25519 ,(blob->base64
                                                         (ed25519-secret-to-public master-key)))))
                          (subject (public-key (ed25519 ,(blob->base64 pubkey))))
                          (name ,name)
                          (role ,role)
                          (capabilities ,capabilities)
                          (validity
                           (not-before ,not-before)
                           (not-after ,not-after))
                          (issued ,(current-seconds))))
             (cert-bytes (string->blob (with-output-to-string
                                         (lambda () (write cert-body)))))
             (signature (ed25519-sign master-key cert-bytes)))
        `(signed-enrollment-cert
          ,cert-body
          (signature (ed25519 ,(blob->base64 signature)))))))

  (define (renew-certificate old-cert master-key . opts)
    ;; Renew an existing certificate.
    (let ((validity-days (get-key opts 'validity-days: 365)))
      (let* ((cert-body (cadr old-cert))
             ;; Skip tag symbol (spki-cert ...) for R6RS assq
             (fields (cdr cert-body))
             (name (cadr (assq 'name fields)))
             (subject (cadr (assq 'subject fields)))
             (role (cadr (assq 'role fields)))
             (now (current-seconds))
             (not-after (+ now (* validity-days 24 60 60)))
             (new-cert-body
              `(spki-cert
                (issuer ,(cadr (assq 'issuer fields)))
                (subject ,subject)
                (name ,name)
                (role ,role)
                (capabilities ,(cadr (assq 'capabilities fields)))
                (validity
                 (not-before ,now)
                 (not-after ,not-after))
                (issued ,now)
                (renewed-from ,(cadr (assq 'issued fields)))))
             (cert-bytes (string->blob (with-output-to-string
                                         (lambda () (write new-cert-body)))))
             (signature (ed25519-sign master-key cert-bytes)))
        `(signed-enrollment-cert
          ,new-cert-body
          (signature (ed25519 ,(blob->base64 signature)))))))

  (define (revoke-certificate cert master-key . opts)
    ;; Revoke a certificate.
    (let ((reason (get-key opts 'reason: 'unspecified)))
      (let* ((cert-body (cadr cert))
             ;; Skip tag symbol (spki-cert ...) for R6RS assq
             (fields (cdr cert-body))
             (name (cadr (assq 'name fields)))
             (subject (cadr (assq 'subject fields)))
             (revocation-body
              `(revocation-data
                (certificate-name ,name)
                (certificate-subject ,subject)
                (revoked-at ,(current-seconds))
                (reason ,reason)
                (issuer ,(cadr (assq 'issuer fields)))))
             (rev-bytes (string->blob (with-output-to-string
                                        (lambda () (write revocation-body)))))
             (signature (ed25519-sign master-key rev-bytes)))
        `(revocation
          ,@(cdr revocation-body)
          (signature (ed25519 ,(blob->base64 signature)))))))

  ;; ============================================================
  ;; Presence Announcement (_cyberspace._tcp service)
  ;; ============================================================

  (define *presence-running* #f)

  (define *cyberspace-service* "_cyberspace._tcp")

  (define (announce-presence name . opts)
    ;; Start announcing as Cyberspace node on local network.
    (let ((port (get-key opts 'port: 7654)))
      (when *presence-running*
        (stop-presence))
      (let* ((os (shell-command "uname -s"))
             (name-str (if (symbol? name) (symbol->string name) name)))
        (cond
          ((and os (string=? os "Darwin"))
           (let ((cmd (string-append "dns-sd -R '" name-str "' _cyberspace._tcp local. "
                                     (number->string port) " &")))
             (set! *presence-running* #t)
             (system cmd)
             (print "Announcing: " name-str " (_cyberspace._tcp on port " port ")")
             `(presence-started (name ,name-str) (port ,port) (service "_cyberspace._tcp"))))
          ((and os (string=? os "Linux"))
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
    ;; Stop presence announcement
    (set! *presence-running* #f)
    (system "pkill -f '_cyberspace._tcp' 2>/dev/null")
    (print "Presence announcement stopped"))

  (define (discover-peers . opts)
    ;; Discover Cyberspace peers on local network via mDNS.
    ;; Returns: list of peer name strings
    (let* ((timeout (get-key opts 'timeout: 3))
           (os (shell-command "uname -s"))
           (cmd (cond
                  ((and os (string=? os "Darwin"))
                   (string-append "timeout " (number->string timeout)
                                  " dns-sd -B " *cyberspace-service* " local. 2>/dev/null"
                                  " | grep 'Add' | awk '{print $7}'"))
                  ((and os (string=? os "Linux"))
                   (string-append "timeout " (number->string timeout)
                                  " avahi-browse -t -p " *cyberspace-service*
                                  " 2>/dev/null | grep '^=' | cut -d';' -f4"))
                  (else #f))))
      (if (not cmd)
          (begin
            (print "mDNS discovery not available on this platform")
            '())
          (let ((result (shell-command cmd)))
            (if (or (not result) (string=? result ""))
                (begin
                  (print "No Cyberspace peers found (service: " *cyberspace-service* ")")
                  '())
                (let ((names (let ((port (open-string-input-port result)))
                               (let loop ((names '()))
                                 (let ((line (get-line port)))
                                   (if (eof-object? line)
                                       (reverse names)
                                       (loop (cons line names))))))))
                  (print "")
                  (print "Cyberspace peers:")
                  (for-each (lambda (name) (print "  " name)) names)
                  (print "")
                  names))))))

) ;; end library
