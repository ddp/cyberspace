;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 31)
  (title "Encryption at Rest")
  (section
    "Abstract"
    (p "This Memo specifies encryption at rest for the Library of Cyberspace: how vaults protect stored data using modern cryptography while maintaining content-addressability, key management, and operational flexibility. All sensitive data is encrypted before touching persistent storage."))
  (section
    "Motivation"
    (p "Data at rest faces threats:")
    (list
      (item "Physical theft")
      (item "Disks, servers, backups stolen")
      (item "Insider access")
      (item "Unauthorized admin access")
      (item "Legal compulsion")
      (item "Forced disclosure orders")
      (item "Decommissioning")
      (item "Data remnants on old hardware"))
    (p "Encryption must be:")
    (list
      (item "Transparent")
      (item "Applications unaware of encryption")
      (item "Performant")
      (item "Minimal overhead")
      (item "Recoverable")
      (item "Key loss doesn't mean data loss")
      (item "Auditable")
      (item "All key operations logged")))
  (section
    "Encryption Model"
    (subsection
      "Layered Encryption"
      (code "┌─────────────────────────────────────┐\n│         Application Layer           │\n│       (plaintext objects)           │\n├─────────────────────────────────────┤\n│      Object-Level Encryption        │\n│    (per-object keys, age format)    │\n├─────────────────────────────────────┤\n│      Storage-Level Encryption       │\n│    (volume encryption, LUKS/dm)     │\n├─────────────────────────────────────┤\n│         Physical Storage            │\n│        (encrypted at rest)          │\n└─────────────────────────────────────┘"))
    (subsection
      "Encryption Scope"
      (code scheme ";; What gets encrypted\n(define encryption-policy\n  `((content . always)           ; Object content - always encrypted\n    (soup-metadata . optional)   ; Metadata - configurable\n    (indexes . optional)         ; Search indexes - configurable\n    (audit-log . always)         ; Audit trail - always encrypted\n    (keys . never-plaintext)))   ; Keys never stored plaintext")))
  (section
    "Key Hierarchy"
    (subsection
      "Key Types"
      (code scheme "(define key-hierarchy\n  '(master-key                    ; Root of trust\n    └── vault-key                 ; Per-vault encryption\n        ├── content-key           ; Object encryption\n        ├── metadata-key          ; Soup encryption\n        ├── index-key             ; Index encryption\n        └── audit-key))           ; Audit log encryption\n\n(define (derive-key parent purpose)\n  \"Derive child key from parent\"\n  (hkdf-sha256 parent\n               salt: (purpose->salt purpose)\n               info: (string->utf8 (symbol->string purpose))\n               length: 32))"))
    (subsection
      "Master Key"
      (code scheme ";; Master key from key ceremony (Memo-022)\n(define (initialize-master-key shares threshold)\n  \"Reconstruct master key from shares\"\n  (let ((master (shamir-combine shares threshold)))\n    ;; Derive vault key\n    (let ((vault-key (derive-key master 'vault)))\n      ;; Store encrypted vault key\n      (store-encrypted-vault-key vault-key master)\n      ;; Clear master from memory\n      (secure-clear! master)\n      vault-key)))"))
    (subsection
      "Key Derivation"
      (code scheme "(define (derive-content-key vault-key object-hash)\n  \"Derive unique key for each object\"\n  (hkdf-sha256 vault-key\n               salt: (string->utf8 object-hash)\n               info: #u8(99 111 110 116 101 110 116)  ; \"content\"\n               length: 32))\n\n(define (derive-chunk-key content-key chunk-index)\n  \"Derive key for each chunk within object\"\n  (hkdf-sha256 content-key\n               salt: (integer->bytevector chunk-index)\n               info: #u8(99 104 117 110 107)  ; \"chunk\"\n               length: 32))")))
  (section
    "Object Encryption"
    (subsection
      "Age Format"
      (code scheme ";; Use age for object encryption (Memo-018)\n(define (encrypt-object data recipient-keys)\n  \"Encrypt object using age format\"\n  (age-encrypt data recipient-keys))\n\n(define (decrypt-object encrypted identity)\n  \"Decrypt object using age format\"\n  (age-decrypt encrypted identity))"))
    (subsection
      "Symmetric Encryption"
      (code scheme ";; For internal encryption with derived keys\n(define (encrypt-symmetric data key)\n  \"Encrypt with ChaCha20-Poly1305\"\n  (let ((nonce (generate-nonce 12)))\n    (let ((ciphertext (chacha20-poly1305-encrypt data key nonce)))\n      (bytevector-append nonce ciphertext))))\n\n(define (decrypt-symmetric encrypted key)\n  \"Decrypt ChaCha20-Poly1305\"\n  (let ((nonce (subbytevector encrypted 0 12))\n        (ciphertext (subbytevector encrypted 12)))\n    (chacha20-poly1305-decrypt ciphertext key nonce)))"))
    (subsection
      "Streaming Encryption"
      (code scheme "(define (encrypt-stream input-port output-port key)\n  \"Stream encryption for large objects\"\n  (let ((chunk-size 65536)\n        (chunk-index 0))\n    (let loop ()\n      (let ((chunk (read-bytevector chunk-size input-port)))\n        (unless (eof-object? chunk)\n          (let ((chunk-key (derive-chunk-key key chunk-index)))\n            (write-bytevector (encrypt-symmetric chunk chunk-key) output-port)\n            (secure-clear! chunk-key))\n          (set! chunk-index (+ chunk-index 1))\n          (loop))))))")))
  (section
    "Storage Integration"
    (subsection
      "Encrypted CAS"
      (code scheme "(define (cas-put-encrypted data)\n  \"Store encrypted object in CAS\"\n  (let ((hash (content-hash data))            ; Hash plaintext\n         (key (derive-content-key (vault-key) hash))\n         (encrypted (encrypt-symmetric data key)))\n    (secure-clear! key)\n    (storage-put hash encrypted)               ; Store ciphertext\n    (soup-put hash encrypted: #t)\n    hash))\n\n(define (cas-get-decrypted hash)\n  \"Retrieve and decrypt object from CAS\"\n  (let ((encrypted (storage-get hash))\n         (key (derive-content-key (vault-key) hash))\n         (data (decrypt-symmetric encrypted key)))\n    (secure-clear! key)\n    ;; Verify hash\n    (unless (equal? hash (content-hash data))\n      (error \"Hash verification failed after decryption\"))\n    data))"))
    (subsection
      "Encrypted Soup"
      (code scheme "(define (soup-put-encrypted hash metadata)\n  \"Store encrypted soup entry\"\n  (let ((serialized (serialize metadata))\n         (key (derive-key (vault-key) 'metadata))\n         (encrypted (encrypt-symmetric serialized key)))\n    (secure-clear! key)\n    (soup-storage-put hash encrypted)))\n\n(define (soup-get-decrypted hash)\n  \"Retrieve and decrypt soup entry\"\n  (let ((encrypted (soup-storage-get hash))\n         (key (derive-key (vault-key) 'metadata))\n         (serialized (decrypt-symmetric encrypted key)))\n    (secure-clear! key)\n    (deserialize serialized)))"))
    (subsection
      "Encrypted Indexes"
      (code scheme ";; Searchable encryption for indexes\n(define (index-put-encrypted term hash)\n  \"Add encrypted index entry\"\n  (let* ((key (derive-key (vault-key) 'index))\n         (encrypted-term (deterministic-encrypt term key))\n         (encrypted-hash (encrypt-symmetric hash key)))\n    (secure-clear! key)\n    (index-storage-put encrypted-term encrypted-hash)))\n\n;; Deterministic encryption enables equality search\n(define (deterministic-encrypt data key)\n  \"Deterministic encryption for searchable indexes\"\n  (let ((derived-key (hkdf-sha256 key salt: data length: 32)))\n    (siv-encrypt data derived-key)))")))
  (section
    "Key Management"
    (subsection
      "Key Storage"
      (code scheme ";; Keys encrypted with master key\n(define (store-vault-key vault-key master-key)\n  \"Store vault key encrypted with master key\"\n  (let ((encrypted (encrypt-symmetric vault-key master-key)))\n    (write-file (vault-key-path) encrypted)))\n\n;; Keys can also be stored as SPKI-encrypted blobs\n(define (store-key-for-principal key principal)\n  \"Store key encrypted for specific principal\"\n  (let* ((encrypted (age-encrypt key (list (principal-public-key principal))))\n         (hash (cas-put encrypted)))\n    (soup-put hash\n      type: 'encrypted-key\n      recipient: principal)\n    hash))"))
    (subsection
      "Key Rotation"
      (code scheme "(define (rotate-vault-key)\n  \"Rotate vault encryption key\"\n  (let ((old-key (vault-key))\n        (new-key (generate-key 32)))\n\n    (audit-append action: 'key-rotation-start)\n\n    ;; Re-encrypt all objects\n    (for-each (lambda (hash)\n                (let* ((encrypted (storage-get hash))\n                       (data (decrypt-symmetric encrypted old-key))\n                       (new-encrypted (encrypt-symmetric data new-key)))\n                  (storage-put hash new-encrypted)))\n              (all-object-hashes))\n\n    ;; Update vault key\n    (set-vault-key! new-key)\n    (secure-clear! old-key)\n\n    (audit-append action: 'key-rotation-complete)))"))
    (subsection
      "Key Escrow"
      (code scheme ";; Threshold key escrow for recovery\n(define (escrow-vault-key vault-key custodians threshold)\n  \"Split vault key among custodians\"\n  (let ((shares (shamir-split vault-key (length custodians) threshold)))\n    (for-each (lambda (custodian share)\n                (let ((encrypted-share\n                       (age-encrypt share (list (custodian-public-key custodian)))))\n                  (send-to-custodian custodian encrypted-share)))\n              custodians shares)))\n\n(define (recover-vault-key custodian-shares)\n  \"Recover vault key from custodian shares\"\n  (let ((decrypted-shares\n         (map (lambda (share custodian)\n                (age-decrypt share (custodian-identity custodian)))\n              custodian-shares custodians)))\n    (shamir-combine decrypted-shares)))")))
  (section
    "Access Control"
    (subsection
      "Key Access"
      (code scheme ";; Keys protected by capabilities\n(spki-cert\n  (issuer vault-admin)\n  (subject data-processor)\n  (capability\n    (action decrypt)\n    (object (type 'content)))\n  (validity (not-after \"2027-01-01\")))\n\n(define (authorized-decrypt? principal hash)\n  \"Check if principal can decrypt object\"\n  (has-capability? principal 'decrypt hash))"))
    (subsection
      "Envelope Encryption"
      (code scheme ";; Object encrypted with DEK, DEK encrypted with KEK\n(define (envelope-encrypt data recipients)\n  \"Envelope encryption for multiple recipients\"\n  (let ((dek (generate-key 32))                      ; Data Encryption Key\n         (encrypted-data (encrypt-symmetric data dek))\n         (encrypted-deks                              ; KEK per recipient\n          (map (lambda (recipient)\n                 (age-encrypt dek (list recipient)))\n               recipients)))\n    `(envelope\n      (encrypted-data . ,encrypted-data)\n      (encrypted-keys . ,encrypted-deks))))\n\n(define (envelope-decrypt envelope identity)\n  \"Decrypt envelope\"\n  (let ((encrypted-deks (assoc-ref envelope 'encrypted-keys))\n         (dek (find-and-decrypt-dek encrypted-deks identity))\n         (encrypted-data (assoc-ref envelope 'encrypted-data)))\n    (decrypt-symmetric encrypted-data dek)))")))
  (section
    "Secure Memory"
    (subsection
      "Key Handling"
      (code scheme ";; Keys must be handled carefully in memory\n(define (with-key key-source proc)\n  \"Use key with automatic cleanup\"\n  (let ((key (key-source)))\n    (dynamic-wind\n      (lambda () #t)\n      (lambda () (proc key))\n      (lambda () (secure-clear! key)))))\n\n(define (secure-clear! bytevector)\n  \"Securely zero memory\"\n  (bytevector-fill! bytevector 0)\n  ;; Prevent compiler optimization\n  (memory-barrier))"))
    (subsection
      "Memory Protection"
      (code scheme ";; Lock key pages in memory (prevent swap)\n(define (allocate-secure-memory size)\n  (let ((mem (allocate-memory size)))\n    (mlock mem size)\n    mem))\n\n(define (free-secure-memory mem size)\n  (secure-clear! mem)\n  (munlock mem size)\n  (free-memory mem))")))
  (section
    "Volume Encryption"
    (subsection
      "LUKS Integration"
      (code scheme ";; Storage volume encryption\n(define (setup-encrypted-volume device passphrase)\n  \"Initialize LUKS encrypted volume\"\n  (run-command \"cryptsetup\" \"luksFormat\" device)\n  (run-command \"cryptsetup\" \"luksOpen\" device \"vault-storage\"))\n\n(define (mount-encrypted-volume passphrase)\n  \"Mount encrypted storage volume\"\n  (run-command \"cryptsetup\" \"luksOpen\"\n               (storage-device)\n               \"vault-storage\"\n               stdin: passphrase)\n  (run-command \"mount\" \"/dev/mapper/vault-storage\" (storage-path)))"))
    (subsection
      "Hardware Security Modules"
      (code scheme ";; HSM for key protection\n(define (hsm-generate-key hsm-slot)\n  \"Generate key in HSM\"\n  (pkcs11-generate-key\n    session: (hsm-session)\n    slot: hsm-slot\n    mechanism: 'aes-256\n    extractable: #f))\n\n(define (hsm-encrypt data key-handle)\n  \"Encrypt using HSM-held key\"\n  (pkcs11-encrypt\n    session: (hsm-session)\n    key: key-handle\n    mechanism: 'aes-gcm\n    data: data))")))
  (section
    "Audit"
    (subsection
      "Encryption Audit"
      (code scheme "(define (audit-encryption-operation op hash principal)\n  \"Log encryption operation\"\n  (audit-append\n    action: op\n    hash: hash\n    principal: principal\n    timestamp: (current-time)\n    ;; Never log keys or plaintext!\n    ))\n\n;; Audit all key operations\n(define (audit-key-operation op key-id principal)\n  (audit-append\n    action: op\n    key-id: key-id\n    principal: principal\n    timestamp: (current-time)))"))
    (subsection
      "Compliance Reporting"
      (code scheme "(define (encryption-compliance-report)\n  \"Generate encryption compliance report\"\n  `((total-objects . ,(count-objects))\n    (encrypted-objects . ,(count-encrypted-objects))\n    (encryption-coverage . ,(/ (count-encrypted-objects) (count-objects)))\n    (key-rotation-date . ,(last-key-rotation))\n    (algorithm . \"ChaCha20-Poly1305\")\n    (key-length . 256)))")))
  (section
    "Performance"
    (subsection
      "Encryption Overhead"
      (code scheme ";; Benchmark encryption overhead\n(define (benchmark-encryption size iterations)\n  (let ((data (generate-random-bytes size))\n        (key (generate-key 32)))\n    (time-iterations iterations\n      (encrypt-symmetric data key))))"))
    (subsection
      "Hardware Acceleration"
      (code scheme ";; Use AES-NI when available\n(define (select-cipher)\n  (if (cpu-supports-aes-ni?)\n      'aes-256-gcm\n      'chacha20-poly1305))")))
  (section
    "Security Considerations"
    (subsection
      "Key Compromise"
      (code scheme ";; If key is compromised\n(define (handle-key-compromise compromised-key-id)\n  \"Emergency response to key compromise\"\n  ;; Immediate key rotation\n  (rotate-vault-key)\n\n  ;; Audit trail\n  (audit-append action: 'key-compromise\n                key-id: compromised-key-id\n                priority: 'critical)\n\n  ;; Notify administrators\n  (alert-key-compromise compromised-key-id)\n\n  ;; Re-encrypt with new key\n  (re-encrypt-all-objects))"))
    (subsection
      "Side Channels"
      (code scheme ";; Constant-time operations\n(define (constant-time-compare a b)\n  \"Compare without timing leaks\"\n  (let ((result 0))\n    (do ((i 0 (+ i 1)))\n        ((= i (bytevector-length a)) (= result 0))\n      (set! result (bitwise-ior result\n                    (bitwise-xor (bytevector-u8-ref a i)\n                                 (bytevector-u8-ref b i)))))))")))
  (section
    "References"
    (p "1. [age](https://age-encryption.org/) - Modern file encryption 2. [LUKS](https://gitlab.com/cryptsetup/cryptsetup) - Linux Unified Key Setup 3. [Memo-022: Key Ceremony Protocol](memo-022-key-ceremony.html) 4. [Memo-018: Sealed Archive Format](memo-018-sealed-archive.html)"))
  (section
    "Changelog"
    (list
      (item "2026-01-07")
      (item "Initial draft"))))

