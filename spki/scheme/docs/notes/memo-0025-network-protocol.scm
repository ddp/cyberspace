;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 25)
  (title "Network Protocol")
  (section
    "Abstract"
    (p "This Memo specifies the network protocol for the Library of Cyberspace: how vaults discover each other, authenticate, exchange objects, and synchronize state. The protocol is transport-agnostic, capability-authenticated, and optimized for content-addressed data."))
  (section
    "Motivation"
    (p "Vaults must communicate to:")
    (list
      (item "Replicate")
      (item "Distribute objects across vaults")
      (item "Federate")
      (item "Link independent vaults into networks")
      (item "Subscribe")
      (item "Receive updates from publishers")
      (item "Query")
      (item "Search the distributed soup"))
    (p "The protocol must handle:")
    (list
      (item "Intermittent connectivity")
      (item "Vaults may be offline")
      (item "Untrusted networks")
      (item "All communication authenticated")
      (item "Large objects")
      (item "Efficient chunked transfer")
      (item "Partial sync")
      (item "Resume interrupted transfers")))
  (section
    "Protocol Layers"
    (code "┌─────────────────────────────────────────┐\n│           APPLICATION LAYER             │\n│  (vault operations, soup queries)       │\n├─────────────────────────────────────────┤\n│           MESSAGE LAYER                 │\n│  (request/response, streaming)          │\n├─────────────────────────────────────────┤\n│           SECURITY LAYER                │\n│  (authentication, encryption)           │\n├─────────────────────────────────────────┤\n│           TRANSPORT LAYER               │\n│  (TCP, QUIC, Unix socket, etc.)         │\n└─────────────────────────────────────────┘"))
  (section
    "Transport Layer"
    (subsection
      "Supported Transports"
      (code scheme "(define transports\n  '((tcp \"Traditional TCP/IP\")\n    (quic \"UDP-based, multiplexed\")\n    (unix \"Local Unix domain socket\")\n    (tor \"Onion-routed TCP\")\n    (i2p \"Garlic-routed\")\n    (bluetooth \"Local mesh\")\n    (sneakernet \"Physical media exchange\")))"))
    (subsection
      "Connection Establishment"
      (code scheme "(define (connect-vault address transport)\n  \"Establish connection to remote vault\"\n  (let* ((socket (transport-connect transport address))\n         (connection (make-connection socket transport)))\n\n    ;; Perform handshake\n    (connection-handshake connection)\n\n    ;; Return authenticated connection\n    connection))"))
    (subsection
      "Multiplexing"
      (p "Multiple streams over single connection:")
      (code scheme "(define (open-stream connection stream-type)\n  \"Open multiplexed stream within connection\"\n  (let ((stream-id (allocate-stream-id connection)))\n    (send-frame connection\n      (frame type: 'stream-open\n             stream-id: stream-id\n             stream-type: stream-type))\n    (make-stream connection stream-id stream-type)))")))
  (section
    "Security Layer"
    (subsection
      "Handshake Protocol"
      (p "Mutual authentication using SPKI certificates:")
      (code "Client                                   Server\n  │                                        │\n  │──── ClientHello ──────────────────────▶│\n  │     (protocol version, capabilities)   │\n  │                                        │\n  │◀──── ServerHello ─────────────────────│\n  │      (protocol version, certificate)   │\n  │                                        │\n  │──── ClientAuth ───────────────────────▶│\n  │     (certificate, challenge-response)  │\n  │                                        │\n  │◀──── ServerAuth ──────────────────────│\n  │      (challenge-response)              │\n  │                                        │\n  │══════ Encrypted Channel ══════════════│"))
    (subsection
      "Handshake Implementation"
      (code scheme "(define (connection-handshake connection)\n  \"Perform mutual authentication handshake\"\n\n  ;; Send ClientHello\n  (send-message connection\n    (client-hello\n      (version ,protocol-version)\n      (capabilities ,(local-capabilities))))\n\n  ;; Receive ServerHello\n  (let ((server-hello (receive-message connection)))\n    (verify-protocol-version (server-hello-version server-hello))\n\n    ;; Verify server certificate\n    (let ((server-cert (server-hello-certificate server-hello)))\n      (unless (verify-certificate server-cert)\n        (error \"Server certificate invalid\"))\n\n      ;; Generate session key using X25519\n      (let* ((ephemeral-keypair (x25519-keypair))\n             (shared-secret (x25519-shared (keypair-secret ephemeral-keypair)\n                                          (cert-public-key server-cert))))\n\n        ;; Send ClientAuth\n        (send-message connection\n          (client-auth\n            (certificate ,(local-certificate))\n            (ephemeral-public ,(keypair-public ephemeral-keypair))\n            (signature ,(sign-challenge server-hello))))\n\n        ;; Receive ServerAuth\n        (let ((server-auth (receive-message connection)))\n          (unless (verify-server-signature server-auth server-cert)\n            (error \"Server authentication failed\"))\n\n          ;; Derive session keys\n          (derive-session-keys connection shared-secret))))))"))
    (subsection
      "Session Encryption"
      (code scheme "(define (derive-session-keys connection shared-secret)\n  \"Derive symmetric keys for session\"\n  (let* ((key-material (hkdf shared-secret\n                             info: \"library-session\"\n                             length: 64))\n         (client-key (subbytes key-material 0 32))\n         (server-key (subbytes key-material 32 64)))\n\n    (set-connection-keys! connection\n      (if (connection-is-client? connection)\n          (keys send: client-key receive: server-key)\n          (keys send: server-key receive: client-key)))))\n\n(define (encrypt-message connection message)\n  \"Encrypt message with session key\"\n  (let ((nonce (connection-next-nonce connection)))\n    (chacha20-poly1305-encrypt\n      (connection-send-key connection)\n      nonce\n      (serialize message))))\n\n(define (decrypt-message connection ciphertext)\n  \"Decrypt message with session key\"\n  (let ((nonce (connection-next-nonce connection)))\n    (deserialize\n      (chacha20-poly1305-decrypt\n        (connection-receive-key connection)\n        nonce\n        ciphertext))))")))
  (section
    "Message Layer"
    (subsection
      "Message Format"
      (code scheme "(library-message\n  (version 1)\n  (type request|response|stream|error)\n  (id <message-id>)\n  (in-reply-to <message-id>|#f)\n  (capability <spki-cert>|#f)\n  (body <payload>))"))
    (subsection
      "Request Types"
      (code scheme "(define request-types\n  '(;; Object operations\n    (get-object hash)\n    (put-object hash data)\n    (has-object hash)\n\n    ;; Bulk operations\n    (get-objects hashes)\n    (get-tree root-hash)\n    (sync-objects bloom-filter)\n\n    ;; Soup queries\n    (soup-query query)\n    (soup-subscribe query)\n\n    ;; Vault operations\n    (get-refs pattern)\n    (get-head)\n    (get-releases)\n\n    ;; Discovery\n    (get-capabilities)\n    (get-peers)))"))
    (subsection
      "Request/Response"
      (code scheme "(define (vault-request connection request #!key capability timeout)\n  \"Send request, wait for response\"\n  (let ((message-id (generate-message-id)))\n\n    ;; Send request\n    (send-message connection\n      (library-message\n        version: 1\n        type: 'request\n        id: message-id\n        capability: capability\n        body: request))\n\n    ;; Wait for response\n    (let ((response (receive-response connection message-id timeout)))\n      (if (eq? (message-type response) 'error)\n          (error (message-body response))\n          (message-body response)))))"))
    (subsection
      "Streaming"
      (p "For large transfers:")
      (code scheme "(define (stream-object connection hash)\n  \"Stream large object in chunks\"\n  (let ((stream (open-stream connection 'object-transfer)))\n\n    ;; Send chunks\n    (let ((data (cas-get hash)))\n      (let loop ((offset 0))\n        (when (< offset (blob-length data))\n          (let ((chunk (blob-copy data offset chunk-size)))\n            (stream-send stream chunk)\n            (loop (+ offset chunk-size)))))\n\n      ;; End stream\n      (stream-close stream))))\n\n(define (receive-stream connection stream callback)\n  \"Receive streamed data\"\n  (let loop ((chunks '()))\n    (let ((chunk (stream-receive stream)))\n      (if (stream-ended? stream)\n          (apply bytes-append (reverse chunks))\n          (begin\n            (callback chunk)\n            (loop (cons chunk chunks)))))))")))
  (section
    "Object Exchange"
    (subsection
      "Get Object"
      (code scheme ";; Request\n(get-object\n  (hash \"sha256:abc123...\"))\n\n;; Response (small object)\n(object-data\n  (hash \"sha256:abc123...\")\n  (size 1024)\n  (data #${...}))\n\n;; Response (large object - streaming)\n(object-stream\n  (hash \"sha256:abc123...\")\n  (size 10485760)\n  (stream-id 42))"))
    (subsection
      "Put Object"
      (code scheme ";; Request\n(put-object\n  (hash \"sha256:abc123...\")\n  (data #${...}))\n\n;; Response\n(put-result\n  (hash \"sha256:abc123...\")\n  (status stored|duplicate|rejected)\n  (reason #f|\"quota exceeded\"))"))
    (subsection
      "Batch Operations"
      (code scheme ";; Request multiple objects\n(get-objects\n  (hashes (\"sha256:aaa...\" \"sha256:bbb...\" \"sha256:ccc...\")))\n\n;; Response\n(objects-batch\n  (objects\n    ((hash \"sha256:aaa...\" data #${...})\n     (hash \"sha256:bbb...\" data #${...})\n     (hash \"sha256:ccc...\" status: missing))))"))
    (subsection
      "Tree Transfer"
      (p "Efficient Merkle tree sync:")
      (code scheme ";; Request tree\n(get-tree\n  (root \"sha256:root...\")\n  (depth 3)  ; How deep to fetch\n  (exclude (\"sha256:already-have...\")))\n\n;; Response\n(tree-data\n  (root \"sha256:root...\")\n  (objects\n    ((hash \"sha256:root...\" data #${...})\n     (hash \"sha256:child1...\" data #${...})\n     (hash \"sha256:child2...\" data #${...}))))")))
  (section
    "Synchronization"
    (subsection
      "Bloom Filter Exchange"
      (p "Efficient \"what do you have?\" queries:")
      (code scheme ";; Step 1: Exchange bloom filters\n(define (sync-init local-vault remote-connection)\n  (let ((local-bloom (vault-bloom-filter local-vault)))\n\n    ;; Send our bloom filter\n    (send-message remote-connection\n      `(sync-bloom\n        (filter ,local-bloom)\n        (population ,(bloom-population local-bloom))))\n\n    ;; Receive their bloom filter\n    (let ((remote-bloom (receive-bloom remote-connection)))\n\n      ;; Compute what they might want\n      (let ((to-send (filter (lambda (hash)\n                               (not (bloom-contains? remote-bloom hash)))\n                             (vault-all-hashes local-vault))))\n        to-send))))\n\n;; Step 2: Exchange missing objects\n(define (sync-exchange to-send to-receive connection)\n  (parallel\n    ;; Send what they need\n    (for-each (lambda (hash)\n                (stream-object connection hash))\n              to-send)\n    ;; Receive what we need\n    (for-each (lambda (hash)\n                (receive-object connection hash))\n              to-receive)))"))
    (subsection
      "Incremental Sync"
      (code scheme "(define (incremental-sync local-vault remote-connection since)\n  \"Sync changes since timestamp or commit\"\n\n  ;; Get remote changes\n  (let ((remote-changes (vault-request remote-connection\n                          `(changes-since ,since))))\n\n    ;; Get local changes\n    (let ((local-changes (vault-changes-since local-vault since)))\n\n      ;; Bidirectional merge\n      (sync-merge local-vault remote-connection\n                  local-changes remote-changes))))"))
    (subsection
      "Conflict Resolution"
      (code scheme "(define (sync-merge local-vault remote changes-local changes-remote)\n  \"Merge changes with conflict resolution\"\n\n  (for-each\n    (lambda (hash)\n      (cond\n        ;; Only local has it - push\n        ((and (member hash changes-local)\n              (not (member hash changes-remote)))\n         (push-object local-vault remote hash))\n\n        ;; Only remote has it - pull\n        ((and (member hash changes-remote)\n              (not (member hash changes-local)))\n         (pull-object local-vault remote hash))\n\n        ;; Both have it - verify same\n        ((and (member hash changes-local)\n              (member hash changes-remote))\n         ;; Content-addressed, so same hash = same content\n         #t)))\n    (union changes-local changes-remote)))")))
  (section
    "Discovery"
    (subsection
      "Peer Discovery"
      (code scheme ";; Well-known peers (bootstrap)\n(define (discover-bootstrap)\n  (map parse-address\n       (read-file \"/etc/library/bootstrap-peers\")))\n\n;; mDNS/DNS-SD for local network\n(define (discover-local)\n  (mdns-browse \"library.tcp.local\"))\n\n;; DHT for global discovery\n(define (discover-dht target-hash)\n  (dht-find-providers target-hash))\n\n;; Peer exchange\n(define (discover-pex connection)\n  (vault-request connection '(get-peers)))"))
    (subsection
      "Capability Advertisement"
      (code scheme ";; Query vault capabilities\n(get-capabilities)\n\n;; Response\n(vault-capabilities\n  (protocol-version 1)\n  (features (bloom-sync tree-transfer streaming soup-query))\n  (max-object-size 104857600)  ; 100MB\n  (storage-available 10737418240)  ; 10GB\n  (public-key \"ed25519:abc...\")\n  (services\n    ((soup-query rate-limit: 100/minute)\n     (object-transfer rate-limit: 10MB/second))))")))
  (section
    "Soup Queries"
    (subsection
      "Remote Query"
      (code scheme ";; Query remote soup\n(soup-query\n  (type certificate)\n  (issuer \"vault-admin\")\n  (limit 100))\n\n;; Response\n(soup-results\n  (count 47)\n  (objects\n    ((name \"cert/alice\" type certificate ...)\n     (name \"cert/bob\" type certificate ...)\n     ...)))"))
    (subsection
      "Subscription"
      (code scheme ";; Subscribe to soup changes\n(soup-subscribe\n  (query (type release))\n  (callback-url \"library://my-vault/callbacks/releases\"))\n\n;; Subscription confirmation\n(subscription\n  (id \"sub-123\")\n  (query (type release))\n  (expires \"2026-02-07T00:00:00Z\"))\n\n;; Push notification (when matching object appears)\n(soup-notification\n  (subscription-id \"sub-123\")\n  (object (name \"release/1.2.0\" type release ...)))")))
  (section
    "Error Handling"
    (subsection
      "Error Types"
      (code scheme "(define error-types\n  '((not-found \"Object not found\")\n    (unauthorized \"Capability required\")\n    (forbidden \"Capability insufficient\")\n    (quota-exceeded \"Storage quota exceeded\")\n    (rate-limited \"Too many requests\")\n    (timeout \"Operation timed out\")\n    (invalid-request \"Malformed request\")\n    (internal-error \"Server error\")\n    (unavailable \"Service temporarily unavailable\")))"))
    (subsection
      "Error Response"
      (code scheme "(library-message\n  (type error)\n  (id <message-id>)\n  (in-reply-to <request-id>)\n  (body\n    (error-response\n      (code not-found)\n      (message \"Object sha256:abc... not found\")\n      (retry-after #f))))"))
    (subsection
      "Retry Logic"
      (code scheme "(define (vault-request-with-retry connection request #!key max-retries)\n  \"Request with exponential backoff retry\"\n  (let loop ((attempt 0) (delay 1000))\n    (let ((result (vault-request connection request)))\n      (if (and (error-response? result)\n               (retryable-error? result)\n               (< attempt max-retries))\n          (begin\n            (sleep delay)\n            (loop (+ attempt 1) (* delay 2)))\n          result))))")))
  (section
    "Security Considerations"
    (subsection
      "Capability Verification"
      (code scheme "(define (verify-request-capability request connection)\n  \"Verify request has sufficient capability\"\n  (let ((required-cap (request->capability request))\n        (presented-cap (message-capability request)))\n\n    (unless presented-cap\n      (error 'unauthorized \"Capability required\"))\n\n    (unless (valid-certificate? presented-cap)\n      (error 'unauthorized \"Invalid capability certificate\"))\n\n    (unless (capability-grants? presented-cap required-cap)\n      (error 'forbidden \"Insufficient capability\"))\n\n    ;; Verify capability chain back to trusted root\n    (unless (verify-capability-chain presented-cap)\n      (error 'forbidden \"Capability chain invalid\"))))"))
    (subsection
      "Denial of Service Protection"
      (code scheme "(define (rate-limit connection request-type)\n  \"Apply rate limiting\"\n  (let ((limit (get-rate-limit request-type))\n        (current (connection-request-count connection request-type)))\n    (when (> current limit)\n      (error 'rate-limited\n             (format \"Rate limit exceeded: ~a/~a\" current limit)))))\n\n(define (size-limit request)\n  \"Enforce size limits\"\n  (when (> (request-size request) max-request-size)\n    (error 'invalid-request \"Request too large\")))"))
    (subsection
      "Replay Prevention"
      (code scheme "(define (verify-nonce connection message)\n  \"Prevent replay attacks\"\n  (let ((nonce (message-nonce message)))\n    (when (nonce-seen? connection nonce)\n      (error 'invalid-request \"Replay detected\"))\n    (record-nonce connection nonce)))")))
  (section
    "Implementation Notes"
    (subsection
      "Wire Format"
      (p "Messages serialized as canonical S-expressions:")
      (code scheme "(define (serialize-message message)\n  \"Canonical S-expression serialization\"\n  (canonical-sexp->bytes message))\n\n(define (deserialize-message bytes)\n  \"Parse S-expression\"\n  (bytes->canonical-sexp bytes))"))
    (subsection
      "Compression"
      (p "Optional compression for large payloads:")
      (code scheme "(define (maybe-compress data)\n  (if (> (blob-length data) compression-threshold)\n      (values (zstd-compress data) 'zstd)\n      (values data 'none)))"))
    (subsection
      "Connection Pooling"
      (code scheme "(define connection-pool (make-hash-table))\n\n(define (get-connection address)\n  \"Get pooled connection or create new\"\n  (or (hash-table-ref connection-pool address #f)\n      (let ((conn (connect-vault address)))\n        (hash-table-set! connection-pool address conn)\n        conn)))")))
  (section
    "References"
    (p "1. [QUIC Protocol - RFC 9000](https://tools.ietf.org/html/rfc9000) 2. [Noise Protocol Framework](http://noiseprotocol.org/) 3. [Memo-020: Content-Addressed Storage](memo-020-content-addressed-storage.html) 4. [Memo-021: Capability Delegation](memo-021-capability-delegation.html) 5. [IPFS Bitswap Protocol](https://docs.ipfs.tech/concepts/bitswap/) 6. [libp2p Specifications](https://github.com/libp2p/specs)"))
  (section
    "Changelog"
    (list
      (item "2026-01-07")
      (item "Initial draft"))))

