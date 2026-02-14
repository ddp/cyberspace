;;; server.sls - HTTP/WebSocket server for Cyberspace
;;;
;;; Serves the web UI and provides WebSocket bridge to Scheme REPL.
;;; Lightweight embedded server for the native macOS application.
;;;
;;; Port: 4321 (default)
;;;
;;; Endpoints:
;;;   GET /           - Main UI (index.html)
;;;   GET /static/*   - Static assets (CSS, JS)
;;;   WS  /ws         - WebSocket REPL connection

(library (cyberspace server)
  (export
    start-server
    server-port
    server-host)

  (import (rnrs)
          (rnrs mutable-strings)
          (only (chezscheme)
                printf format with-output-to-string
                file-directory? directory-list
                current-directory getenv
                fork-thread sleep
                system open-process-ports
                make-time current-time time-second
                void sort
                eval interaction-environment
                open-input-string read
                call-with-string-output-port
                pretty-print display-condition)
          (cyberspace tcp)
          (cyberspace chicken-compatibility blob)
          (cyberspace chicken-compatibility chicken))

  ;; ============================================================
  ;; Configuration
  ;; ============================================================

  (define *server-port* 4321)
  (define *server-host* "127.0.0.1")
  (define *static-dir* #f)

  ;; R6RS can't export assigned variables
  (define (server-port) *server-port*)
  (define (server-host) *server-host*)

  ;; ============================================================
  ;; String Helpers
  ;; ============================================================

  (define (string-prefix? prefix str)
    (let ((plen (string-length prefix))
          (slen (string-length str)))
      (and (<= plen slen)
           (string=? prefix (substring str 0 plen)))))

  (define (string-suffix? suffix str)
    (let ((xlen (string-length suffix))
          (slen (string-length str)))
      (and (<= xlen slen)
           (string=? suffix (substring str (- slen xlen) slen)))))

  (define (string-contains haystack needle)
    (let ((nlen (string-length needle))
          (hlen (string-length haystack)))
      (let loop ((i 0))
        (cond
          ((> (+ i nlen) hlen) #f)
          ((string=? needle (substring haystack i (+ i nlen))) i)
          (else (loop (+ i 1)))))))

  (define (string-trim-both str)
    (let* ((len (string-length str))
           (start (let loop ((i 0))
                    (if (or (>= i len) (not (char-whitespace? (string-ref str i))))
                        i (loop (+ i 1)))))
           (end (let loop ((i (- len 1)))
                  (if (or (< i start) (not (char-whitespace? (string-ref str i))))
                      (+ i 1) (loop (- i 1))))))
      (substring str start end)))

  (define (pathname-extension path)
    (let ((len (string-length path)))
      (let loop ((i (- len 1)))
        (cond
          ((< i 0) #f)
          ((char=? (string-ref path i) #\.) (substring path (+ i 1) len))
          ((char=? (string-ref path i) #\/) #f)
          (else (loop (- i 1)))))))

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
  ;; Binary Port Text I/O
  ;; ============================================================
  ;; Server uses binary ports throughout. These helpers read/write
  ;; text over binary ports so WebSocket can use raw bytes.

  (define (bin-get-line in)
    "Read a line from binary port, return string (without \\n). Strips \\r."
    (let loop ((acc '()))
      (let ((b (get-u8 in)))
        (cond
          ((eof-object? b)
           (if (null? acc) b (utf8->string (u8-list->bytevector (reverse acc)))))
          ((= b 10)  ; \n
           (utf8->string (u8-list->bytevector (reverse acc))))
          ((= b 13)  ; \r — skip, will be followed by \n
           (loop acc))
          (else (loop (cons b acc)))))))

  (define (bin-put-string out str)
    "Write a string to a binary port as UTF-8."
    (put-bytevector out (string->utf8 str)))

  (define (bin-flush out)
    (flush-output-port out))

  ;; ============================================================
  ;; HTTP Response Helpers
  ;; ============================================================

  (define (http-response out status headers body)
    (bin-put-string out (format #f "HTTP/1.1 ~a\r\n" status))
    (for-each (lambda (h)
                (bin-put-string out (format #f "~a: ~a\r\n" (car h) (cdr h))))
              headers)
    (bin-put-string out "\r\n")
    (when body
      (bin-put-string out body))
    (bin-flush out))

  (define (http-ok out content-type body)
    (http-response out "200 OK"
      `(("Content-Type" . ,content-type)
        ("Content-Length" . ,(string-length body))
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
    (let ((sp1 (string-contains line " ")))
      (if sp1
          (let ((rest (substring line (+ sp1 1) (string-length line))))
            (let ((sp2 (string-contains rest " ")))
              (values (substring line 0 sp1)
                      (if sp2 (substring rest 0 sp2) rest))))
          (values #f #f))))

  (define (parse-headers in)
    (let loop ((headers '()))
      (let ((line (bin-get-line in)))
        (if (or (eof-object? line) (string=? line ""))
            (reverse headers)
            (let ((colon (string-contains line ":")))
              (if colon
                  (loop (cons (cons (string-downcase (string-trim-both (substring line 0 colon)))
                                    (string-trim-both (substring line (+ colon 1) (string-length line))))
                              headers))
                  (loop headers)))))))

  ;; ============================================================
  ;; WebSocket Support
  ;; ============================================================

  (define *ws-magic* "258EAFA5-E914-47DA-95CA-C5AB0DC85B11")

  (define (ws-accept-key key)
    (let ((combined (string-append key *ws-magic*)))
      (let-values (((to-stdin from-stdout from-stderr pid)
                    (open-process-ports
                      "openssl dgst -sha1 -binary | openssl base64"
                      (buffer-mode block)
                      (make-transcoder (utf-8-codec)))))
        (put-string to-stdin combined)
        (close-port to-stdin)
        (let ((result (get-line from-stdout)))
          (close-port from-stdout)
          (close-port from-stderr)
          (if (eof-object? result) "" (string-trim-both result))))))

  (define (handle-websocket in out headers)
    (printf "[ws] Upgrading connection~%")
    (let* ((key-pair (assoc "sec-websocket-key" headers))
           (key (if key-pair (cdr key-pair) "")))
      (let ((accept (ws-accept-key key)))
        (bin-put-string out "HTTP/1.1 101 Switching Protocols\r\n")
        (bin-put-string out "Upgrade: websocket\r\n")
        (bin-put-string out "Connection: Upgrade\r\n")
        (bin-put-string out (format #f "Sec-WebSocket-Accept: ~a\r\n" accept))
        (bin-put-string out "\r\n")
        (bin-flush out)
        (ws-loop in out))))

  (define (ws-loop in out)
    (guard (exn
            [#t (printf "[ws] Loop error: ~a~%"
                        (if (message-condition? exn) (condition-message exn) exn))])
      (let loop ()
        (let ((b1 (get-u8 in)))
          (when (not (eof-object? b1))
            (let* ((opcode (bitwise-and b1 #x0f))
                   (b2 (get-u8 in))
                   (masked (bitwise-and b2 #x80))
                   (len (bitwise-and b2 #x7f)))
              (let ((payload-len
                     (cond
                       ((= len 126)
                        (+ (bitwise-arithmetic-shift-left (get-u8 in) 8)
                           (get-u8 in)))
                       ((= len 127)
                        (let ploop ((i 8) (n 0))
                          (if (zero? i) n
                              (ploop (- i 1)
                                     (+ (bitwise-arithmetic-shift-left n 8)
                                        (get-u8 in))))))
                       (else len))))

                (let ((mask-key
                       (if (> masked 0)
                           (get-bytevector-n in 4)
                           #f)))

                  (let* ((raw (if (zero? payload-len)
                                  (make-bytevector 0)
                                  (get-bytevector-n in payload-len)))
                         (payload-bv (if (bytevector? raw) raw (make-bytevector 0)))
                         (unmasked-bv
                          (if (and mask-key (bytevector? mask-key))
                              (let ((ubv (make-bytevector (bytevector-length payload-bv))))
                                (do ((i 0 (+ i 1)))
                                    ((>= i (bytevector-length payload-bv)) ubv)
                                  (bytevector-u8-set! ubv i
                                    (bitwise-xor (bytevector-u8-ref payload-bv i)
                                                 (bytevector-u8-ref mask-key (mod i 4))))))
                              payload-bv))
                         (text (utf8->string unmasked-bv)))

                    (case opcode
                      ((1)  ; Text frame
                       (ws-handle-message text out)
                       (loop))
                      ((8)  ; Close
                       (ws-send-close out))
                      ((9)  ; Ping
                       (ws-send-pong out text)
                       (loop))
                      (else (loop))))))))))))

  (define (ws-send-frame out opcode payload)
    (let* ((payload-bv (string->utf8 payload))
           (len (bytevector-length payload-bv)))
      (put-u8 out (bitwise-ior #x80 opcode))
      (cond
        ((< len 126)
         (put-u8 out len))
        ((< len 65536)
         (put-u8 out 126)
         (put-u8 out (bitwise-arithmetic-shift-right len 8))
         (put-u8 out (bitwise-and len #xff)))
        (else
         (put-u8 out 127)
         (do ((i 7 (- i 1)))
             ((< i 0))
           (put-u8 out
             (bitwise-and (bitwise-arithmetic-shift-right len (* 8 i)) #xff)))))
      (put-bytevector out payload-bv)
      (bin-flush out)))

  (define (ws-send-text out msg)
    (guard (exn [#t (printf "[ws] Send failed~%") #f])
      (ws-send-frame out 1 msg)
      #t))

  (define (ws-send-close out)
    (ws-send-frame out 8 ""))

  (define (ws-send-pong out data)
    (ws-send-frame out 10 data))

  ;; ============================================================
  ;; WebSocket Message Handling
  ;; ============================================================

  (define (eval-to-string expr-str)
    "Read and evaluate expr-str in the interaction environment.
     Returns (values result-string error?)"
    (guard (exn
            [#t (values
                  (call-with-string-output-port
                    (lambda (p) (display-condition exn p)))
                  #t)])
      (let* ((port (open-input-string expr-str))
             (datum (read port))
             (result (eval datum (interaction-environment)))
             (result-str (if (eq? result (void))
                             ""
                             (call-with-string-output-port
                               (lambda (p) (pretty-print result p))))))
        (values (string-trim-both result-str) #f))))

  (define (json-escape str)
    "Escape a string for embedding in a JSON string value."
    (let loop ((i 0) (acc '()))
      (if (>= i (string-length str))
          (list->string (reverse acc))
          (let ((c (string-ref str i)))
            (cond
              ((char=? c #\") (loop (+ i 1) (append '(#\" #\\) acc)))
              ((char=? c #\\) (loop (+ i 1) (append '(#\\ #\\) acc)))
              ((char=? c #\newline) (loop (+ i 1) (append '(#\n #\\) acc)))
              ((char=? c #\return) (loop (+ i 1) (append '(#\r #\\) acc)))
              ((char=? c #\tab) (loop (+ i 1) (append '(#\t #\\) acc)))
              (else (loop (+ i 1) (cons c acc))))))))

  (define (ws-handle-message msg out)
    (printf "[ws] Received: ~a~%" msg)
    (let* ((type (extract-json-field "type" msg))
           (data (extract-json-field "data" msg)))
      (cond
        ((equal? type "eval")
         (let ((expr (extract-json-field "expression" msg)))
           (when expr
             (let-values (((result error?) (eval-to-string expr)))
               (ws-send-text out
                 (format #f "{\"type\":\"~a\",\"value\":\"~a\"}"
                   (if error? "error" "result")
                   (json-escape result)))))))
        (else
         (ws-send-text out (format #f "{\"type\":\"echo\",\"data\":~s}" msg))))))

  (define (extract-json-field field json-str)
    "Extract a string value for a JSON field. Handles optional space after colon."
    (let ((key (format #f "\"~a\":" field)))
      (let ((start (string-contains json-str key)))
        (if start
            (let* ((after-colon (+ start (string-length key)))
                   ;; Skip optional whitespace
                   (pos (let skip ((i after-colon))
                          (if (and (< i (string-length json-str))
                                   (char-whitespace? (string-ref json-str i)))
                              (skip (+ i 1)) i))))
              (if (and (< pos (string-length json-str))
                       (char=? (string-ref json-str pos) #\"))
                  (let* ((val-start (+ pos 1))
                         (rest (substring json-str val-start (string-length json-str)))
                         (end (find-json-string-end rest)))
                    (if end (substring rest 0 end) #f))
                  #f))
            #f))))

  (define (find-json-string-end str)
    (let loop ((i 0) (escaped #f))
      (if (>= i (string-length str)) #f
          (let ((c (string-ref str i)))
            (cond
              (escaped (loop (+ i 1) #f))
              ((char=? c #\\) (loop (+ i 1) #t))
              ((char=? c #\") i)
              (else (loop (+ i 1) #f)))))))

  ;; ============================================================
  ;; Static File Serving
  ;; ============================================================

  (define (serve-static out path)
    (let ((file-path (string-append *static-dir* "/" path)))
      (if (and (file-exists? file-path)
               (not (file-directory? file-path)))
          (let ((content (call-with-input-file file-path
                           (lambda (p) (get-string-all p))))
                (mime (get-mime-type file-path)))
            (http-ok out mime content))
          (http-not-found out))))

  ;; ============================================================
  ;; API Endpoints
  ;; ============================================================

  (define (api-vault-list)
    (let ((dir ".vault/objects"))
      (if (and (file-exists? dir) (file-directory? dir))
          (let* ((files (filter (lambda (f) (not (string-prefix? "." f)))
                                (directory-list dir)))
                 (limited (if (> (length files) 100)
                              (let loop ((i 0) (fs files) (acc '()))
                                (if (or (null? fs) (>= i 100)) (reverse acc)
                                    (loop (+ i 1) (cdr fs) (cons (car fs) acc))))
                              files)))
            (format #f "{\"objects\":[~a]}"
                    (apply string-append
                      (let loop ((fs limited) (first #t))
                        (if (null? fs) '()
                            (cons (format #f "~a{\"hash\":\"~a\"}"
                                          (if first "" ",") (car fs))
                                  (loop (cdr fs) #f)))))))
          "{\"objects\":[]}")))

  (define (api-keys-list)
    (let ((dir ".vault/keys"))
      (if (and (file-exists? dir) (file-directory? dir))
          (let ((files (filter (lambda (f)
                                 (or (string-suffix? ".pub" f)
                                     (string-suffix? ".cert" f)
                                     (string-suffix? ".key" f)))
                               (directory-list dir))))
            (format #f "{\"keys\":[~a]}"
                    (apply string-append
                      (let loop ((fs files) (first #t))
                        (if (null? fs) '()
                            (cons (format #f "~a{\"name\":\"~a\"}"
                                          (if first "" ",") (car fs))
                                  (loop (cdr fs) #f)))))))
          "{\"keys\":[]}")))

  ;; ============================================================
  ;; Main Request Handler
  ;; ============================================================

  (define (handle-request in out)
    (let ((request-line (bin-get-line in)))
      (if (or (not request-line) (eof-object? request-line))
          #f
          (let ((clean request-line))
            (let-values (((method path) (parse-request-line clean)))
              (let ((headers (parse-headers in)))
                (printf "[http] ~a ~a~%" method path)
                (cond
                  ;; WebSocket upgrade
                  ((and (equal? path "/ws")
                        (assoc "upgrade" headers)
                        (string-ci=? (cdr (assoc "upgrade" headers)) "websocket"))
                   (handle-websocket in out headers)
                   'websocket)

                  ;; Main page
                  ((or (equal? path "/") (equal? path "/index.html"))
                   (http-ok out "text/html; charset=utf-8" (index-html)))

                  ;; API: system info
                  ((equal? path "/api/info")
                   (http-ok out "application/json"
                     (format #f "{\"version\":\"0.9.12\",\"name\":\"Cyberspace\",\"port\":~a}"
                             *server-port*)))

                  ;; API: vault objects
                  ((equal? path "/api/vault")
                   (http-ok out "application/json" (api-vault-list)))

                  ;; API: keys
                  ((equal? path "/api/keys")
                   (http-ok out "application/json" (api-keys-list)))

                  ;; API: federation peers
                  ((equal? path "/api/peers")
                   (http-ok out "application/json" "{\"peers\":[]}"))

                  ;; API: preferences
                  ((equal? path "/api/preferences")
                   (http-ok out "application/json"
                     "{\"fontName\":\"SF Mono\",\"fontSize\":13,\"theme\":\"dark\"}"))

                  ;; Static files
                  ((string-prefix? "/static/" path)
                   (serve-static out (substring path 8 (string-length path))))

                  ;; Favicon
                  ((equal? path "/favicon.ico")
                   (http-not-found out))

                  (else
                   (http-not-found out)))))))))

  ;; ============================================================
  ;; Embedded UI (index.html) — REPL terminal
  ;; ============================================================

  (define (index-html)
    (string-append
"<!DOCTYPE html><html><head><meta charset='UTF-8'>
<title>Cyberspace</title>
<style>
*{margin:0;padding:0;box-sizing:border-box}
body{font-family:'SF Mono',Monaco,'Fira Code',monospace;
     background:#0a0a0a;color:#33ff33;height:100vh;display:flex;flex-direction:column}
#output{flex:1;overflow-y:auto;padding:12px 16px;white-space:pre-wrap;word-wrap:break-word;
        font-size:13px;line-height:1.5}
#output .banner{color:#66ff66}
#output .dim{color:#1a8f1a}
#output .error{color:#ff3333}
#output .result{color:#33ff33}
#output .echo{color:#1a8f1a}
#input-line{display:flex;align-items:center;padding:4px 16px 12px;border-top:1px solid #1a3a1a}
#prompt{color:#66ff66;margin-right:8px;font-size:13px;user-select:none}
#buf{color:#33ff33;font-size:13px}
#cursor{display:inline-block;width:8px;height:15px;background:#33ff33;
        animation:blink 1s step-end infinite;vertical-align:text-bottom}
@keyframes blink{50%{opacity:0}}
#status{position:fixed;top:8px;right:16px;font-size:11px;color:#1a8f1a}
#status.connected{color:#33ff33}
#status.disconnected{color:#ff3333}
::-webkit-scrollbar{width:8px}
::-webkit-scrollbar-track{background:#0a0a0a}
::-webkit-scrollbar-thumb{background:#1a3a1a;border-radius:4px}
</style></head><body>
<div id='output'></div>
<div id='input-line'><span id='prompt'>&gt;</span><span id='buf'></span><span id='cursor'>&nbsp;</span></div>
<div id='status'>disconnected</div>
<script>
var ws,output=document.getElementById('output'),
    bufEl=document.getElementById('buf'),cursorEl=document.getElementById('cursor'),
    status=document.getElementById('status'),
    buf='',cmdHistory=[],histIdx=-1;

function emit(text,cls){
  var el=document.createElement('div');
  if(cls)el.className=cls;
  el.textContent=text;
  output.appendChild(el);
  output.scrollTop=output.scrollHeight;
}
function updateBuf(){bufEl.textContent=buf;}

function banner(){
  emit('CYBERSPACE','banner');
  emit('Library of Cyberspace v0.9.12','dim');
  emit('','dim');
}

function connect(){
  var loc=window.location;
  ws=new WebSocket('ws://'+loc.hostname+':'+loc.port+'/ws');
  ws.onopen=function(){status.textContent='connected';status.className='connected';
    emit('Connected to REPL','dim');};
  ws.onclose=function(){status.textContent='disconnected';status.className='disconnected';
    emit('Disconnected','error');setTimeout(connect,3000);};
  ws.onerror=function(){};
  ws.onmessage=function(e){
    try{
      var msg=JSON.parse(e.data);
      if(msg.type==='result')emit(msg.value,'result');
      else if(msg.type==='error')emit(msg.value||msg.data,'error');
      else if(msg.type==='echo')emit(msg.data,'echo');
      else emit(e.data,'dim');
    }catch(x){emit(e.data,'dim');}
  };
}

function sendExpr(){
  var expr=buf.trim();
  if(!expr)return;
  cmdHistory.push(expr);histIdx=cmdHistory.length;
  emit('> '+expr,'dim');
  if(ws&&ws.readyState===1)
    ws.send(JSON.stringify({type:'eval',expression:expr}));
  else emit('Not connected','error');
  buf='';updateBuf();
}

function handleNativeKey(chars,keyCode,ctrl,shift){
  if(keyCode===36){sendExpr();return;}
  if(keyCode===51){buf=buf.slice(0,-1);updateBuf();return;}
  if(keyCode===126){if(histIdx>0){histIdx--;buf=cmdHistory[histIdx];updateBuf();}return;}
  if(keyCode===125){
    if(histIdx<cmdHistory.length-1){histIdx++;buf=cmdHistory[histIdx];updateBuf();}
    else{histIdx=cmdHistory.length;buf='';updateBuf();}return;}
  if(ctrl&&chars==='l'){output.innerHTML='';return;}
  if(ctrl&&chars==='u'){buf='';updateBuf();return;}
  if(ctrl)return;
  if(chars.length===1&&chars.charCodeAt(0)>=32){buf+=chars;updateBuf();}
}

banner();connect();
</script></body></html>"))

  ;; ============================================================
  ;; Server Main Loop
  ;; ============================================================

  (define (start-server . opts)
    (let ((port (get-opt opts 0 *server-port*)))
      (set! *server-port* port)
      (set! *static-dir* (or (getenv "CYBERSPACE_STATIC")
                             (string-append (current-directory) "/static")))

      (printf "~%  Cyberspace Server~%")
      (printf "  Port: ~a~%"  port)
      (printf "  Static: ~a~%" *static-dir*)
      (printf "~%")

      (let ((listener (tcp-listen port)))
        (printf "  Listening on http://~a:~a/~%~%" *server-host* port)
        (flush-output-port (current-output-port))

        (let loop ()
          (let-values (((in out) (tcp-accept-binary listener)))
            (fork-thread
              (lambda ()
                (guard (exn
                        [#t (printf "[error] ~a~%"
                              (if (message-condition? exn)
                                  (condition-message exn)
                                  "unknown error"))
                            (close-port in)
                            (close-port out)])
                  (let ((keep-alive (handle-request in out)))
                    (unless (eq? keep-alive 'websocket)
                      (close-port in)
                      (close-port out))))))
            (loop))))))

) ; end library
