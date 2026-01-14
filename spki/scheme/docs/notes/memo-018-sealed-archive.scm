;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 18)
  (title "Sealed Archive Format")
  (section
    "Abstract"
    (p "This RFC specifies the Zstd+Age archive format for the Library of Cyberspace: a modern archive format combining Zstd compression with Age encryption, replacing gzip for cryptographic archives."))
  (section
    "Motivation"
    (p "The legacy cryptographic archive format uses gzip compression without encryption:")
    (table
      (header "Aspect " "gzip (legacy) " "zstd + age ")
      (row "Compression speed " "Slow " "Fast (parallel) ")
      (row "Compression ratio " "Good " "Better ")
      (row "Encryption " "None " "Built-in (age) ")
      (row "Key compatibility " "N/A " "X25519/Ed25519 (SPKI aligned) ")
      (row "Streaming " "Yes " "Yes "))
    (p "Why change?")
    (p "1. Encryption at rest - Archives contain potentially sensitive data 2. Faster compression - Zstd is 3-5x faster than gzip 3. Better ratios - Zstd typically achieves 10-20% better compression 4. Key alignment - Age uses X25519/Ed25519, same curve family as SPKI 5. Parallel support - zstd -T0 uses all cores"))
  (section
    "Specification"
    (subsection
      "Archive Creation Pipeline"
      (code "git archive | tar --zstd | age -r <recipients> > archive.tar.zst.age")
      (p "Or equivalently:")
      (code "tar --zstd -cf - <files> | age -r <recipient1> -r <recipient2> > archive.tar.zst.age"))
    (subsection
      "Archive Restoration Pipeline"
      (code "age -d -i <identity> < archive.tar.zst.age | zstd -d | tar -xf -"))
    (subsection
      "Manifest Format"
      (code scheme "(sealed-archive\n  (version \"1.0.0\")\n  (format zstd-age)\n  (archive \"vault-1.0.0.archive.tar.zst.age\")\n  (compression zstd)\n  (encryption age)\n  (recipients (\"age1ql3z7hjy54pw3hyww5ayyfg7zqgvc7w3j2elw8zmrj2kg5sfn9aqmcac8p\"))\n  (hash \"sha512:...\")\n  (signature \"ed25519:...\"))"))
    (subsection
      "File Extensions"
      (table
        (header "Extension " "Contents ")
        (row ".archive " "S-expression manifest ")
        (row ".tar.zst.age " "Encrypted, compressed tarball ")))
    (subsection
      "Configuration"
      (code scheme ";; Set age recipients for encryption\n(vault-config 'age-recipients\n  '(\"age1ql3z7hjy54pw3hyww5ayyfg7zqgvc7w3j2elw8zmrj2kg5sfn9aqmcac8p\"\n    \"age1...\"))\n\n;; Set age identity for decryption\n(vault-config 'age-identity \"~/.config/age/identity.txt\")\n\n;; Set default archive format\n(vault-config 'archive-format 'zstd-age)")))
  (section
    "Performance Characteristics"
    (subsection
      "Compression"
      (code "Zstd default (-3):\n  Compression:   ~400 MB/s\n  Decompression: ~800 MB/s\n  Ratio:         ~3:1 (typical source code)\n\nZstd parallel (-T0):\n  Compression:   ~400 MB/s × cores\n  Decompression: ~800 MB/s × cores\n\nGzip comparison:\n  Compression:   ~30 MB/s\n  Decompression: ~200 MB/s\n  Ratio:         ~2.5:1"))
    (subsection
      "Encryption"
      (code "Age X25519:\n  Encrypt:  ~1 GB/s (ChaCha20-Poly1305)\n  Decrypt:  ~1 GB/s\n  Key size: 32 bytes (public), 32 bytes (private)\n\nAge overhead:\n  Header:   ~200 bytes per recipient\n  MAC:      16 bytes"))
    (subsection
      "Signature"
      (code "Ed25519:\n  Sign:     ~10 μs\n  Verify:   ~10 μs\n  Signature: 64 bytes"))
    (subsection
      "Total Pipeline"
      (code "10 MB archive:\n  Compress (zstd -T0): ~25 ms\n  Encrypt (age):       ~10 ms\n  Hash (SHA-512):      ~1 ms\n  Sign (Ed25519):      ~10 μs\n  Total:               ~36 ms\n\nvs gzip legacy:\n  Compress (gzip):     ~300 ms\n  Hash (SHA-512):      ~1 ms\n  Sign (Ed25519):      ~10 μs\n  Total:               ~301 ms\n\nSpeedup: ~8x")))
  (section
    "Security Model"
    (subsection
      "Encryption Layer (Age)"
      (list
        (item "Algorithm: X25519 + ChaCha20-Poly1305")
        (item "Recipients: Multiple allowed (each can decrypt)")
        (item "Forward secrecy: Ephemeral key per archive")
        (item "Authenticity: Poly1305 MAC")))
    (subsection
      "Signature Layer (SPKI)"
      (list
        (item "Algorithm: Ed25519")
        (item "Scope: Signs encrypted archive hash")
        (item "Non-repudiation: Signer cannot deny creating archive")))
    (subsection
      "Verification Order"
      (p "1. Verify signature - Before decryption (fail fast on tampering) 2. Verify hash - Encrypted archive integrity 3. Decrypt - Only after signature verified 4. Extract - Only after successful decryption"))
    (subsection
      "Threat Mitigations"
      (table
        (header "Threat " "Mitigation ")
        (row "Eavesdropping " "Age encryption (X25519 + ChaCha20) ")
        (row "Tampering " "SHA-512 hash + Ed25519 signature ")
        (row "Replay attacks " "Version + timestamp in manifest ")
        (row "Key compromise " "Multiple recipients, key rotation ")
        (row "Chosen ciphertext " "Poly1305 authentication "))))
  (section
    "Compatibility"
    (subsection
      "Age Identity Types"
      (code "# Native age key\nage1ql3z7hjy54pw3hyww5ayyfg7zqgvc7w3j2elw8zmrj2kg5sfn9aqmcac8p\n\n# SSH key (age supports ssh-ed25519 and ssh-rsa)\nssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAI...\n\n# GitHub key (via age-plugin-github or ssh)\ngithub:username"))
    (subsection
      "Platform Support"
      (table
        (header "Platform " "zstd " "age ")
        (row "macOS " "Homebrew " "Homebrew ")
        (row "Linux " "apt/yum " "apt/yum or binary ")
        (row "FreeBSD " "pkg " "pkg ")
        (row "Windows " "winget " "winget or binary ")))
    (subsection
      "Fallback"
      (p "If zstd or age unavailable, fall back to cryptographic format:")
      (code scheme "(if (and (command-exists? \"zstd\") (command-exists? \"age\"))\n    (seal-archive version format: 'zstd-age)\n    (seal-archive version format: 'cryptographic))")))
  (section
    "Implementation"
    (subsection
      "seal-archive-zstd-age"
      (code scheme "(define (seal-archive-zstd-age version output)\n  \"Create zstd-compressed, age-encrypted archive with SPKI signature\"\n\n  (let ((recipients (vault-config 'age-recipients))\n        (signing-key (vault-config 'signing-key))\n        (encrypted-file (sprintf \"~a.tar.zst.age\" output)))\n\n    ;; Require recipients\n    (unless (pair? recipients)\n      (error \"No age recipients configured\"))\n\n    ;; Build recipient args: -r key1 -r key2 ...\n    (let ((recipient-args\n           (string-join (map (lambda (r) (sprintf \"-r ~a\" r)) recipients) \" \")))\n\n      ;; Create archive: git archive | zstd | age\n      (let ((temp-tar (sprintf \"/tmp/vault-~a.tar\" version)))\n        (run-command \"git\" \"archive\" \"--prefix=vault/\"\n                     (sprintf \"--output=~a\" temp-tar) version)\n        (system (sprintf \"zstd -T0 -c ~a | age ~a > ~a\"\n                        temp-tar recipient-args encrypted-file))\n        (delete-file temp-tar))\n\n      ;; Sign the encrypted archive\n      (when signing-key\n        (let* ((archive-bytes (read-file-bytes encrypted-file))\n               (archive-hash (sha512-hash archive-bytes))\n               (signature (ed25519-sign signing-key archive-hash)))\n\n          ;; Write manifest\n          (with-output-to-file output\n            (lambda ()\n              (write `(sealed-archive\n                       (version ,version)\n                       (format zstd-age)\n                       (archive ,encrypted-file)\n                       (compression zstd)\n                       (encryption age)\n                       (recipients ,recipients)\n                       (hash ,(blob->hex archive-hash))\n                       (signature ,(blob->hex signature)))))))))))"))
    (subsection
      "seal-restore-zstd-age"
      (code scheme "(define (seal-restore-zstd-age manifest verify-key target-dir identity)\n  \"Restore zstd+age encrypted archive\"\n\n  (let ((version (cadr (assq 'version (cdr manifest))))\n        (archive-file (cadr (assq 'archive (cdr manifest))))\n        (hash-hex (cadr (assq 'hash (cdr manifest))))\n        (sig-hex (cadr (assq 'signature (cdr manifest))))\n        (id-file (or identity (vault-config 'age-identity))))\n\n    ;; Require identity\n    (unless id-file\n      (error \"No age identity configured\"))\n\n    ;; Verify signature first (before decryption)\n    (when verify-key\n      (let* ((archive-bytes (read-file-bytes archive-file))\n             (archive-hash (sha512-hash archive-bytes))\n             (expected-hash (hex->blob hash-hex))\n             (signature (hex->blob sig-hex))\n             (pubkey (read-key-from-file verify-key)))\n\n        (unless (equal? archive-hash expected-hash)\n          (error \"Archive hash mismatch\"))\n\n        (unless (ed25519-verify pubkey archive-hash signature)\n          (error \"Signature verification failed\"))))\n\n    ;; Decrypt and extract: age -d | zstd -d | tar -x\n    (system (sprintf \"age -d -i ~a < ~a | zstd -d | tar -xf - -C ~a\"\n                    id-file archive-file target-dir))))")))
  (section
    "Usage Examples"
    (subsection
      "Create Encrypted Archive"
      (code scheme ";; Configure recipients\n(vault-config 'age-recipients\n  '(\"age1ql3z7hjy54pw3hyww5ayyfg7zqgvc7w3j2elw8zmrj2kg5sfn9aqmcac8p\"))\n\n;; Create archive\n(seal-archive \"1.0.0\" format: 'zstd-age)\n;; => vault-1.0.0.archive\n;; => vault-1.0.0.archive.tar.zst.age"))
    (subsection
      "Restore Encrypted Archive"
      (code scheme ";; Configure identity\n(vault-config 'age-identity \"~/.config/age/identity.txt\")\n\n;; Restore with verification\n(seal-restore \"vault-1.0.0.archive\"\n              verify-key: \"publisher.public\"\n              target: \"./restored\")"))
    (subsection
      "Command Line Equivalents"
      (code bash "# Create\ngit archive --prefix=vault/ 1.0.0 | \\\n  zstd -T0 | \\\n  age -r age1ql3z7hjy54pw3hyww5ayyfg7zqgvc7w3j2elw8zmrj2kg5sfn9aqmcac8p \\\n  > vault-1.0.0.tar.zst.age\n\n# Restore\nage -d -i ~/.config/age/identity.txt < vault-1.0.0.tar.zst.age | \\\n  zstd -d | \\\n  tar -xf -")))
  (section
    "Migration"
    (subsection
      "From Cryptographic to Zstd-Age"
      (code scheme ";; Re-archive existing releases with new format\n(for-each\n  (lambda (version)\n    (seal-archive version format: 'zstd-age))\n  (get-local-releases))"))
    (subsection
      "Backward Compatibility"
      (p "Both formats can coexist. The manifest format field determines restoration method: - (format cryptographic) → seal-restore-cryptographic - (format zstd-age) → seal-restore-zstd-age")))
  (section
    "References"
    (p "1. [Zstd](https://github.com/facebook/zstd) - Facebook's compression algorithm 2. [Age](https://age-encryption.org/) - Modern encryption tool 3. [RFC-006](rfc-006-vault-architecture.html) - Vault System Architecture 4. [RFC-004](rfc-004-spki-authorization.html) - SPKI Authorization"))
  (section
    "Changelog"
    (list
      (item "2026-01-06")
      (item "Initial specification"))))

