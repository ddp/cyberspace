;;; cyberspace-server.scm - HTTP/WebSocket server for Cyberspace.app
;;;
;;; Serves the web UI and provides WebSocket bridge to Scheme REPL.
;;; Lightweight embedded server for the native macOS application.
;;;
;;; Port: 7780 (default)
;;;
;;; Endpoints:
;;;   GET /           - Main UI (index.html)
;;;   GET /static/*   - Static assets (CSS, JS)
;;;   WS  /ws         - WebSocket REPL connection
;;;
;;; Copyright (c) 2026 Yoyodyne. See LICENSE.

(import scheme
        (chicken base)
        (chicken io)
        (chicken port)
        (chicken format)
        (chicken string)
        (chicken tcp)
        (chicken time)
        (chicken file)
        (chicken pathname)
        (chicken process-context)
        (chicken process)
        (chicken bitwise)
        (chicken blob)
        srfi-1
        srfi-13
        srfi-18
        srfi-69)

;; ============================================================
;; Configuration
;; ============================================================

(define *server-port* 7780)
(define *server-host* "127.0.0.1")
(define *static-dir* #f)  ; set at startup

;; ============================================================
;; MIME Types
;; ============================================================

(define *mime-types*
  '(("html" . "text/html; charset=utf-8")
    ("css"  . "text/css; charset=utf-8")
    ("js"   . "application/javascript; charset=utf-8")
    ("json" . "application/json")
    ("png"  . "image/png")
    ("svg"  . "image/svg+xml")
    ("ico"  . "image/x-icon")
    ("woff2" . "font/woff2")))

(define (get-mime-type path)
  (let* ((ext (pathname-extension path))
         (pair (and ext (assoc ext *mime-types*))))
    (if pair (cdr pair) "application/octet-stream")))

;; ============================================================
;; HTTP Response Helpers
;; ============================================================

(define (http-response out status headers body)
  (display (sprintf "HTTP/1.1 ~a\r\n" status) out)
  (for-each (lambda (h)
              (display (sprintf "~a: ~a\r\n" (car h) (cdr h)) out))
            headers)
  (display "\r\n" out)
  (when body
    (if (string? body)
        (display body out)
        (write-string body out)))
  (flush-output out))

(define (http-ok out content-type body)
  (http-response out "200 OK"
    `(("Content-Type" . ,content-type)
      ("Content-Length" . ,(if (string? body) (string-length body) (blob-size body)))
      ("Cache-Control" . "no-cache")
      ("Connection" . "close"))
    body))

(define (http-not-found out)
  (http-response out "404 Not Found"
    '(("Content-Type" . "text/plain")
      ("Connection" . "close"))
    "Not Found"))

(define (http-error out msg)
  (http-response out "500 Internal Server Error"
    '(("Content-Type" . "text/plain")
      ("Connection" . "close"))
    msg))

;; ============================================================
;; HTTP Request Parser
;; ============================================================

(define (parse-request-line line)
  ;; "GET /path HTTP/1.1" -> (method path version)
  (let ((parts (string-split line " ")))
    (if (>= (length parts) 2)
        (values (car parts) (cadr parts))
        (values #f #f))))

(define (parse-headers in)
  (let loop ((headers '()))
    (let ((line (read-line in)))
      (if (or (eof-object? line) (string=? line "") (string=? line "\r"))
          (reverse headers)
          (let ((colon (string-index line #\:)))
            (if colon
                (loop (cons (cons (string-downcase (string-trim-both (substring line 0 colon)))
                                  (string-trim-both (substring line (+ colon 1))))
                            headers))
                (loop headers)))))))

(define (string-split str delim)
  (let ((dchar (if (string? delim) (string-ref delim 0) delim)))
    (let loop ((chars (string->list str))
               (current '())
               (result '()))
      (cond
        ((null? chars)
         (reverse (cons (list->string (reverse current)) result)))
        ((char=? (car chars) dchar)
         (loop (cdr chars) '() (cons (list->string (reverse current)) result)))
        (else
         (loop (cdr chars) (cons (car chars) current) result))))))

;; ============================================================
;; Static File Serving
;; ============================================================

(define (serve-static out path)
  (let ((file-path (make-pathname *static-dir* path)))
    (if (and (file-exists? file-path)
             (not (directory-exists? file-path)))
        (let ((content (call-with-input-file file-path
                         (lambda (p) (read-string #f p))))
              (mime (get-mime-type file-path)))
          (http-ok out mime content))
        (http-not-found out))))

;; ============================================================
;; WebSocket Support
;; ============================================================

(define *ws-magic* "258EAFA5-E914-47DA-95CA-C5AB0DC85B11")

(define (ws-accept-key key)
  ;; SHA-1 hash of key + magic, base64 encoded
  ;; Simplified - in production use proper SHA-1
  ;; For now, use a placeholder that browsers accept for testing
  (let* ((combined (string-append key *ws-magic*)))
    ;; This needs proper SHA-1 + base64
    ;; Placeholder for structure
    "dGhlIHNhbXBsZSBub25jZQ=="))

(define (handle-websocket in out headers)
  ;; Upgrade to WebSocket
  (let* ((key (cdr (or (assoc "sec-websocket-key" headers) '(#f . ""))))
         (accept (ws-accept-key key)))
    (display "HTTP/1.1 101 Switching Protocols\r\n" out)
    (display "Upgrade: websocket\r\n" out)
    (display "Connection: Upgrade\r\n" out)
    (display (sprintf "Sec-WebSocket-Accept: ~a\r\n" accept) out)
    (display "\r\n" out)
    (flush-output out)

    ;; WebSocket message loop
    (ws-loop in out)))

(define (ws-loop in out)
  ;; Simple WebSocket frame handling
  ;; Frame format: [fin+opcode] [mask+len] [mask-key if masked] [payload]
  (let loop ()
    (let ((b1 (read-byte in)))
      (when (and b1 (not (eof-object? b1)))
        (let* ((fin (bitwise-and b1 #x80))
               (opcode (bitwise-and b1 #x0f))
               (b2 (read-byte in))
               (masked (bitwise-and b2 #x80))
               (len (bitwise-and b2 #x7f)))

          ;; Handle extended length
          (let ((payload-len
                 (cond
                   ((= len 126)
                    (+ (arithmetic-shift (read-byte in) 8) (read-byte in)))
                   ((= len 127)
                    ;; 64-bit length - just read lower bytes
                    (let loop ((i 8) (n 0))
                      (if (zero? i) n
                          (loop (- i 1) (+ (arithmetic-shift n 8) (read-byte in))))))
                   (else len))))

            ;; Read mask key if present
            (let ((mask-key
                   (if (> masked 0)
                       (list (read-byte in) (read-byte in)
                             (read-byte in) (read-byte in))
                       #f)))

              ;; Read and unmask payload
              (let* ((payload (read-string payload-len in))
                     (unmasked
                      (if mask-key
                          (list->string
                            (map (lambda (c i)
                                   (integer->char
                                     (bitwise-xor (char->integer c)
                                                  (list-ref mask-key (modulo i 4)))))
                                 (string->list payload)
                                 (iota (string-length payload))))
                          payload)))

                (case opcode
                  ((1) ; Text frame
                   (ws-handle-message unmasked in out)
                   (loop))
                  ((8) ; Close
                   (ws-send-close out))
                  ((9) ; Ping
                   (ws-send-pong out unmasked)
                   (loop))
                  (else
                   (loop)))))))))))

(define (ws-send-frame out opcode payload)
  (let ((len (string-length payload)))
    (write-byte (bitwise-ior #x80 opcode) out)  ; FIN + opcode
    (cond
      ((< len 126)
       (write-byte len out))
      ((< len 65536)
       (write-byte 126 out)
       (write-byte (arithmetic-shift len -8) out)
       (write-byte (bitwise-and len #xff) out))
      (else
       (write-byte 127 out)
       (let loop ((i 8))
         (when (> i 0)
           (write-byte (bitwise-and (arithmetic-shift len (* -8 (- i 1))) #xff) out)
           (loop (- i 1))))))
    (display payload out)
    (flush-output out)))

(define (ws-send-text out msg)
  (ws-send-frame out 1 msg))

(define (ws-send-close out)
  (ws-send-frame out 8 ""))

(define (ws-send-pong out data)
  (ws-send-frame out 10 data))

(define *repl-input* #f)
(define *repl-output* #f)
(define *repl-process* #f)

(define (ensure-repl-running)
  "Start the REPL subprocess if not running"
  (unless (and *repl-process* *repl-input* *repl-output*)
    (let* ((repl-path (or (get-environment-variable "CYBERSPACE_REPL")
                          "./cyberspace-repl"))
           (proc (process* repl-path '("-q"))))  ; quiet mode
      (set! *repl-process* proc)
      (set! *repl-output* (car proc))      ; stdout from repl
      (set! *repl-input* (cadr proc))      ; stdin to repl
      (printf "[repl] Started subprocess~n"))))

(define (eval-in-repl expr)
  "Send expression to REPL and get result"
  (handle-exceptions exn
    (sprintf "Error: ~a" ((condition-property-accessor 'exn 'message) exn))
    (ensure-repl-running)
    (display expr *repl-input*)
    (newline *repl-input*)
    (flush-output *repl-input*)
    ;; Read result (simple approach - read one line)
    (let ((result (read-line *repl-output*)))
      (if (eof-object? result)
          "Error: REPL disconnected"
          result))))

(define (ws-handle-message msg in out)
  ;; Handle incoming WebSocket message (JSON)
  ;; Parse and route to appropriate handler
  (printf "[ws] Received: ~a~n" msg)

  ;; Try to parse as JSON and extract expression
  (let* ((expr (extract-expression msg))
         (result (if expr
                     (eval-in-repl expr)
                     msg)))
    (ws-send-text out (sprintf "{\"type\":\"result\",\"value\":~s}" result))))

(define (extract-expression json-str)
  "Extract expression from JSON message, or return #f"
  ;; Simple JSON parsing for {\"type\":\"eval\",\"expression\":\"...\"}
  (let ((expr-match (string-search "\"expression\":\"" json-str)))
    (if expr-match
        (let* ((start (+ expr-match 14))
               (rest (substring json-str start))
               (end (string-index rest #\")))
          (if end
              (substring rest 0 end)
              #f))
        ;; Not JSON, treat as raw expression
        json-str)))

(define (string-search needle haystack)
  "Find position of needle in haystack, or #f"
  (let ((nlen (string-length needle))
        (hlen (string-length haystack)))
    (let loop ((i 0))
      (cond
        ((> (+ i nlen) hlen) #f)
        ((string=? needle (substring haystack i (+ i nlen))) i)
        (else (loop (+ i 1)))))))

;; ============================================================
;; API Functions - Read from .vault
;; ============================================================

(define (api-vault-list)
  "List objects in .vault/objects"
  (let ((dir ".vault/objects"))
    (if (directory-exists? dir)
        (let* ((files (filter (lambda (f) (not (string-prefix? "." f)))
                              (directory dir)))
               (objects (map (lambda (f)
                              (let ((path (make-pathname dir f)))
                                `((hash . ,f)
                                  (size . ,(if (file-exists? path)
                                              (file-size path)
                                              0)))))
                            (take files (min 100 (length files))))))
          (sprintf "{\"objects\":[~a]}"
                   (string-intersperse
                     (map (lambda (obj)
                            (sprintf "{\"hash\":\"~a\",\"size\":~a}"
                                     (cdr (assq 'hash obj))
                                     (cdr (assq 'size obj))))
                          objects)
                     ",")))
        "{\"objects\":[]}")))

(define (api-keys-list)
  "List keys in .vault/keys"
  (let ((dir ".vault/keys"))
    (if (directory-exists? dir)
        (let* ((files (filter (lambda (f)
                               (and (not (string-prefix? "." f))
                                    (or (string-suffix? ".pub" f)
                                        (string-suffix? ".cert" f)
                                        (string-suffix? ".key" f))))
                              (directory dir)))
               (keys (map (lambda (f)
                           (let ((ext (pathname-extension f)))
                             `((name . ,(pathname-strip-extension f))
                               (type . ,(cond
                                         ((equal? ext "pub") "public key")
                                         ((equal? ext "cert") "certificate")
                                         ((equal? ext "key") "private key")
                                         (else "key"))))))
                          files)))
          (sprintf "{\"keys\":[~a]}"
                   (string-intersperse
                     (map (lambda (k)
                            (sprintf "{\"name\":\"~a\",\"type\":\"~a\"}"
                                     (cdr (assq 'name k))
                                     (cdr (assq 'type k))))
                          keys)
                     ",")))
        "{\"keys\":[]}")))

(define (api-peers-list)
  "List known federation peers"
  ;; For now, return empty - would read from gossip state
  "{\"peers\":[]}")

(define (take lst n)
  (if (or (null? lst) (<= n 0))
      '()
      (cons (car lst) (take (cdr lst) (- n 1)))))

;; ============================================================
;; Main Request Handler
;; ============================================================

(define (handle-request in out)
  (let ((request-line (read-line in)))
    (when (and request-line (not (eof-object? request-line)))
      (let-values (((method path) (parse-request-line request-line)))
        (let ((headers (parse-headers in)))
          (printf "[http] ~a ~a~n" method path)

          (cond
            ;; WebSocket upgrade
            ((and (equal? path "/ws")
                  (assoc "upgrade" headers)
                  (string-ci=? (cdr (assoc "upgrade" headers)) "websocket"))
             (handle-websocket in out headers))

            ;; Main page
            ((or (equal? path "/") (equal? path "/index.html"))
             (http-ok out "text/html; charset=utf-8" (index-html)))

            ;; API: system info
            ((equal? path "/api/info")
             (http-ok out "application/json"
               (sprintf "{\"version\":\"0.9.12\",\"name\":\"Cyberspace\",\"port\":~a}"
                        *server-port*)))

            ;; API: vault objects
            ((equal? path "/api/vault")
             (http-ok out "application/json" (api-vault-list)))

            ;; API: keys
            ((equal? path "/api/keys")
             (http-ok out "application/json" (api-keys-list)))

            ;; API: federation peers
            ((equal? path "/api/peers")
             (http-ok out "application/json" (api-peers-list)))

            ;; API: preferences (defaults, actual prefs stored in native app)
            ((equal? path "/api/preferences")
             (http-ok out "application/json"
               "{\"fontName\":\"SF Mono\",\"fontSize\":13,\"theme\":\"dark\"}"))

            ;; Static files
            ((string-prefix? "/static/" path)
             (serve-static out (substring path 8)))

            ;; Favicon
            ((equal? path "/favicon.ico")
             (http-not-found out))

            (else
             (http-not-found out))))))))

;; ============================================================
;; Embedded UI (index.html)
;; ============================================================

(define (index-html)
  #<<EOF
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>Cyberspace</title>
  <style>
    :root {
      --bg: #1a1a2e;
      --fg: #eee;
      --accent: #0f3460;
      --highlight: #e94560;
      --border: #333;
      --mono: 'SF Mono', 'Monaco', 'Menlo', monospace;
      --font-size: 13px;
    }
    /* Light theme */
    :root.theme-light {
      --bg: #f5f5f5;
      --fg: #333;
      --accent: #e0e0e0;
      --highlight: #d63384;
      --border: #ccc;
    }
    /* Solarized theme */
    :root.theme-solarized {
      --bg: #002b36;
      --fg: #839496;
      --accent: #073642;
      --highlight: #cb4b16;
      --border: #586e75;
    }
    * { box-sizing: border-box; margin: 0; padding: 0; }
    body {
      font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;
      background: var(--bg);
      color: var(--fg);
      height: 100vh;
      display: flex;
      flex-direction: column;
    }
    header {
      background: var(--accent);
      padding: 12px 20px;
      display: flex;
      align-items: center;
      justify-content: space-between;
      border-bottom: 1px solid var(--border);
    }
    header h1 {
      font-size: 18px;
      font-weight: 500;
      letter-spacing: 1px;
    }
    .status {
      font-size: 12px;
      color: #888;
    }
    .status.connected { color: #4caf50; }
    .status.disconnected { color: var(--highlight); }
    main {
      flex: 1;
      display: flex;
      overflow: hidden;
    }
    .sidebar {
      width: 200px;
      background: rgba(0,0,0,0.2);
      border-right: 1px solid var(--border);
      padding: 10px 0;
    }
    .sidebar-item {
      padding: 10px 20px;
      cursor: pointer;
      transition: background 0.2s;
    }
    .sidebar-item:hover { background: rgba(255,255,255,0.05); }
    .sidebar-item.active { background: var(--accent); }
    .content {
      flex: 1;
      display: flex;
      flex-direction: column;
      overflow: hidden;
    }
    #repl {
      flex: 1;
      display: flex;
      flex-direction: column;
      padding: 10px;
    }
    #output {
      flex: 1;
      font-family: var(--mono);
      font-size: var(--font-size);
      line-height: 1.5;
      overflow-y: auto;
      padding: 10px;
      background: rgba(0,0,0,0.3);
      border-radius: 4px;
      margin-bottom: 10px;
      white-space: pre-wrap;
    }
    #input-line {
      display: flex;
      align-items: center;
      background: rgba(0,0,0,0.3);
      border-radius: 4px;
      padding: 0 10px;
    }
    #prompt {
      font-family: var(--mono);
      font-size: 13px;
      color: var(--highlight);
      margin-right: 5px;
    }
    #input {
      flex: 1;
      font-family: var(--mono);
      font-size: var(--font-size);
      background: transparent;
      border: none;
      color: var(--fg);
      outline: none;
      padding: 10px 0;
    }
    .output-line { }
    .output-result { color: #4caf50; }
    .output-error { color: var(--highlight); }
    .view { display: none; flex-direction: column; height: 100%; }
    .view.active { display: flex; }
    .view-header {
      font-size: 14px;
      font-weight: 600;
      padding: 15px;
      border-bottom: 1px solid var(--border);
      color: #aaa;
      text-transform: uppercase;
      letter-spacing: 1px;
    }
    .item-list {
      flex: 1;
      overflow-y: auto;
      padding: 10px;
    }
    .item {
      padding: 10px 15px;
      border-radius: 4px;
      margin-bottom: 5px;
      background: rgba(0,0,0,0.2);
      font-family: var(--mono);
      font-size: calc(var(--font-size) - 1px);
      cursor: pointer;
      transition: background 0.2s;
    }
    .item:hover { background: rgba(255,255,255,0.05); }
    .item-hash { color: var(--highlight); }
    .item-meta { color: #666; font-size: 11px; margin-top: 4px; }
    footer {
      padding: 8px 20px;
      font-size: 11px;
      color: #666;
      border-top: 1px solid var(--border);
      display: flex;
      justify-content: space-between;
    }
  </style>
</head>
<body>
  <header>
    <h1>CYBERSPACE</h1>
    <span class="status disconnected" id="status">Disconnected</span>
  </header>
  <main>
    <nav class="sidebar">
      <div class="sidebar-item active" data-view="repl">REPL</div>
      <div class="sidebar-item" data-view="vault">Vault</div>
      <div class="sidebar-item" data-view="keys">Keys</div>
      <div class="sidebar-item" data-view="peers">Federation</div>
    </nav>
    <div class="content">
      <div id="repl" class="view active">
        <div id="output">Welcome to Cyberspace.
Library of Cyberspace v0.9.12

Type (help) for commands.

</div>
        <div id="input-line">
          <span id="prompt">&gt;</span>
          <input type="text" id="input" autofocus placeholder="Enter Cyberspace Scheme expression...">
        </div>
      </div>
      <div id="vault" class="view">
        <div class="view-header">Vault Objects</div>
        <div id="vault-list" class="item-list">Loading...</div>
      </div>
      <div id="keys" class="view">
        <div class="view-header">Keys</div>
        <div id="keys-list" class="item-list">Loading...</div>
      </div>
      <div id="peers" class="view">
        <div class="view-header">Federation</div>
        <div id="peers-list" class="item-list">No peers discovered.</div>
      </div>
    </div>
  </main>
  <footer>
    <span>Library of Cyberspace</span>
    <span id="info"></span>
  </footer>
  <script>
    const output = document.getElementById('output');
    const input = document.getElementById('input');
    const status = document.getElementById('status');
    let ws = null;
    let history = [];
    let historyIndex = -1;

    function connect() {
      ws = new WebSocket('ws://' + location.host + '/ws');
      ws.onopen = () => {
        status.textContent = 'Connected';
        status.className = 'status connected';
        appendOutput('Connected to backend.\n', 'output-line');
      };
      ws.onclose = () => {
        status.textContent = 'Disconnected';
        status.className = 'status disconnected';
        setTimeout(connect, 2000);
      };
      ws.onmessage = (e) => {
        try {
          const msg = JSON.parse(e.data);
          if (msg.type === 'result') {
            appendOutput(msg.value + '\n', 'output-result');
          } else if (msg.type === 'error') {
            appendOutput('Error: ' + msg.message + '\n', 'output-error');
          } else if (msg.type === 'echo') {
            appendOutput('< ' + msg.data + '\n', 'output-line');
          }
        } catch (err) {
          appendOutput(e.data + '\n', 'output-line');
        }
      };
    }

    function appendOutput(text, className) {
      const span = document.createElement('span');
      span.className = className;
      span.textContent = text;
      output.appendChild(span);
      output.scrollTop = output.scrollHeight;
    }

    function send(expr) {
      if (ws && ws.readyState === WebSocket.OPEN) {
        appendOutput('> ' + expr + '\n', 'output-line');
        ws.send(JSON.stringify({ type: 'eval', expression: expr }));
        history.unshift(expr);
        historyIndex = -1;
      }
    }

    input.addEventListener('keydown', (e) => {
      if (e.key === 'Enter' && input.value.trim()) {
        send(input.value);
        input.value = '';
      } else if (e.key === 'ArrowUp') {
        if (historyIndex < history.length - 1) {
          historyIndex++;
          input.value = history[historyIndex];
        }
        e.preventDefault();
      } else if (e.key === 'ArrowDown') {
        if (historyIndex > 0) {
          historyIndex--;
          input.value = history[historyIndex];
        } else if (historyIndex === 0) {
          historyIndex = -1;
          input.value = '';
        }
        e.preventDefault();
      }
    });

    // Native bridge (for Cyberspace.app)
    window.addEventListener('cyberspace', (e) => {
      const msg = e.detail;
      console.log('Native message:', msg);

      if (msg.type === 'preferences.theme') {
        applyTheme(msg.theme);
      } else if (msg.type === 'preferences.font') {
        applyFont(msg.fontName, msg.fontSize);
      }
    });

    function applyTheme(theme) {
      document.documentElement.className = '';
      if (theme !== 'dark') {
        document.documentElement.classList.add('theme-' + theme);
      }
      localStorage.setItem('theme', theme);
    }

    function applyFont(fontName, fontSize) {
      document.documentElement.style.setProperty('--mono', "'" + fontName + "', Monaco, monospace");
      document.documentElement.style.setProperty('--font-size', fontSize + 'px');
      localStorage.setItem('fontName', fontName);
      localStorage.setItem('fontSize', fontSize);
    }

    // Load saved preferences on startup
    function loadPreferences() {
      const theme = localStorage.getItem('theme') || 'dark';
      const fontName = localStorage.getItem('fontName') || 'SF Mono';
      const fontSize = localStorage.getItem('fontSize') || 13;
      applyTheme(theme);
      applyFont(fontName, fontSize);
    }
    loadPreferences();

    // View switching
    document.querySelectorAll('.sidebar-item').forEach(item => {
      item.addEventListener('click', () => {
        const viewId = item.dataset.view;
        document.querySelectorAll('.sidebar-item').forEach(i => i.classList.remove('active'));
        document.querySelectorAll('.view').forEach(v => v.classList.remove('active'));
        item.classList.add('active');
        document.getElementById(viewId).classList.add('active');
        if (viewId === 'vault') loadVault();
        if (viewId === 'keys') loadKeys();
        if (viewId === 'peers') loadPeers();
        if (viewId === 'repl') input.focus();
      });
    });

    function loadVault() {
      fetch('/api/vault').then(r => r.json()).then(data => {
        const list = document.getElementById('vault-list');
        if (data.objects && data.objects.length > 0) {
          list.innerHTML = data.objects.map(obj =>
            `<div class="item"><span class="item-hash">${obj.hash.substring(0,12)}...</span><div class="item-meta">${obj.size} bytes</div></div>`
          ).join('');
        } else {
          list.innerHTML = '<div style="color:#666;padding:20px;">No objects in vault.</div>';
        }
      }).catch(() => {
        document.getElementById('vault-list').innerHTML = '<div style="color:#666;padding:20px;">Vault not available.</div>';
      });
    }

    function loadKeys() {
      fetch('/api/keys').then(r => r.json()).then(data => {
        const list = document.getElementById('keys-list');
        if (data.keys && data.keys.length > 0) {
          list.innerHTML = data.keys.map(key =>
            `<div class="item"><span class="item-hash">${key.name}</span><div class="item-meta">${key.type}</div></div>`
          ).join('');
        } else {
          list.innerHTML = '<div style="color:#666;padding:20px;">No keys stored.</div>';
        }
      }).catch(() => {
        document.getElementById('keys-list').innerHTML = '<div style="color:#666;padding:20px;">Keys not available.</div>';
      });
    }

    function loadPeers() {
      fetch('/api/peers').then(r => r.json()).then(data => {
        const list = document.getElementById('peers-list');
        if (data.peers && data.peers.length > 0) {
          list.innerHTML = data.peers.map(peer =>
            `<div class="item"><span class="item-hash">${peer.name}</span><div class="item-meta">${peer.address}</div></div>`
          ).join('');
        } else {
          list.innerHTML = '<div style="color:#666;padding:20px;">No peers discovered.</div>';
        }
      }).catch(() => {
        document.getElementById('peers-list').innerHTML = '<div style="color:#666;padding:20px;">Federation not available.</div>';
      });
    }

    // Start connection
    connect();
    fetch('/api/info').then(r => r.json()).then(info => {
      document.getElementById('info').textContent = info.name + ' v' + info.version;
    });
  </script>
</body>
</html>
EOF
)

;; ============================================================
;; Server Main Loop
;; ============================================================

(define (start-server #!optional (port *server-port*))
  (set! *server-port* port)
  (set! *static-dir* (or (get-environment-variable "CYBERSPACE_STATIC")
                         (make-pathname (current-directory) "static")))

  (printf "~n")
  (printf "  Cyberspace Server~n")
  (printf "  Port: ~a~n" port)
  (printf "  Static: ~a~n" *static-dir*)
  (printf "~n")

  (let ((listener (tcp-listen port)))
    (printf "  Listening on http://~a:~a/~n~n" *server-host* port)

    (let loop ()
      (let-values (((in out) (tcp-accept listener)))
        ;; Handle each connection in a thread
        (thread-start!
          (make-thread
            (lambda ()
              (handle-exceptions exn
                (begin
                  (printf "[error] ~a~n"
                    ((condition-property-accessor 'exn 'message) exn))
                  (close-input-port in)
                  (close-output-port out))
                (begin
                  (handle-request in out)
                  (close-input-port in)
                  (close-output-port out))))))
        (loop)))))

;; ============================================================
;; Entry Point
;; ============================================================

(define (main args)
  (let ((port (if (and (pair? args) (pair? (cdr args)))
                  (string->number (cadr args))
                  *server-port*)))
    (start-server port)))

;; Run if executed directly
(main (command-line-arguments))
