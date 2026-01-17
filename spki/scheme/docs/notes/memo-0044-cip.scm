;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 44)
  (title "Cryptographic Imprint Protocol")
  (section
    "Abstract"
    (p "CIP establishes secure channels between Cyberspace nodes using stateless cookies for DoS resistance, ephemeral key exchange for forward secrecy, and capability attestation for authorization. Each imprint is an authoritative affirmation of trust - signed and sealed by the issuing principal in their realm. No X.509. No CA hierarchy. No algorithm negotiation."))
  (section
    "Motivation"
    (p "TLS is complex: - Certificate chains require PKI - Algorithm negotiation invites downgrade attacks - State allocated before client proven real - Identity exposed before encryption")
    (p "PHOTURIS (1995) had better ideas: - Cookies before crypto - Identity under encryption - Simple state machine")
    (p "CIP resurrects these ideas with modern primitives."))
  (section
    "Protocol Overview"
    (code "Initiator                          Responder\n    |                                   |\n    |-------- KNOCK (version) -------->|  Stateless\n    |<-------- COOKIE -----------------|  Stateless\n    |                                   |\n    |-------- EXCHANGE (eph key) ----->|  State committed\n    |<------- EXCHANGE (eph key) ------|\n    |                                   |\n    |========= encrypted below ========|\n    |                                   |\n    |-------- ATTEST (identity) ------>|\n    |<------- ATTEST (identity) -------|\n    |                                   |\n    |-------- OFFER (capabilities) --->|\n    |<------- OFFER (capabilities) ----|\n    |                                   |\n    |-------- CONFIRM (transcript) --->|\n    |<------- CONFIRM (transcript) ----|\n    |                                   |\n    |========= CHANNEL OPEN ===========|\n    |                                   |\n    |<----------- DATA -------------->|")
    (p "10 messages to establish. Unlimited encrypted DATA after."))
  (section
    "Message Format"
    (p "All messages use TLV encoding:")
    (code "┌──────┬────────┬──────────────────┐\n│ Type │ Length │ Payload          │\n│ 1B   │ 4B BE  │ variable         │\n└──────┴────────┴──────────────────┘")
    (subsection
      "Message Types"
      (table
        (header "Type " "Name " "Direction ")
        (row "0x01 " "KNOCK " "I → R ")
        (row "0x02 " "COOKIE " "R → I ")
        (row "0x03 " "EXCHANGE " "bidirectional ")
        (row "0x04 " "ATTEST " "bidirectional ")
        (row "0x05 " "OFFER " "bidirectional ")
        (row "0x06 " "CONFIRM " "bidirectional ")
        (row "0x10 " "DATA " "bidirectional ")
        (row "0xFF " "CLOSE " "bidirectional "))))
  (section
    "Phase 1: KNOCK"
    (p "Initiator announces intent and protocol version.")
    (code "KNOCK payload:\n  \"CIP/\" VERSIONMAJOR \".\" VERSIONMINOR\n\nExample: \"CIP/1.0\"")
    (p "Responder checks version compatibility: - Major mismatch: reject (incompatible suites) - Minor mismatch: accept (backward compatible)")
    (p "Responder allocates no state."))
  (section
    "Phase 2: COOKIE"
    (p "Responder returns stateless cookie.")
    (code scheme "(define (make-cookie remote-addr remote-port)\n  (let ((data (string-append\n                (blob->string cookie-secret)\n                remote-addr\n                (number->string remote-port)\n                (number->string cookie-epoch*)))\n         (hash (blake2b-hash (string->blob data))))\n    (substring hash 0 16)))")
    (p "Cookie properties: - Stateless: Responder doesn't store it - Unforgeable: Requires server secret - Expiring: Epoch rotation invalidates old cookies - Address-bound: Different address = different cookie")
    (p "Responder still allocates no state."))
  (section
    "Phase 3: EXCHANGE"
    (p "Both parties exchange ephemeral public keys.")
    (p "Initiator sends:")
    (code "EXCHANGE payload:\n  cookie-r \"|\" cookie-i \"|\" ephemeral-public-hex")
    (p "- cookie-r: Echo of responder's cookie (proves receipt) - cookie-i: Initiator's random cookie (for key derivation) - ephemeral-public: X25519 public key")
    (p "Responder verifies cookie echo, then responds with same format.")
    (p "State now committed. Keys derived.")
    (subsection
      "Key Derivation"
      (code scheme "(define (derive-session-keys shared-secret cookie-i cookie-r)\n  (let* ((ikm (blob-append shared-secret\n                           (string->blob cookie-i)\n                           (string->blob cookie-r)))\n         (prk (blake2b-hash ikm))\n         (k-ir (blake2b-hash (blob-append prk \"initiator->responder\")))\n         (k-ri (blake2b-hash (blob-append prk \"responder->initiator\"))))\n    (values (take k-ir 32) (take k-ri 32))))")
      (p "Directional keys prevent reflection attacks.")))
  (section
    "Phase 4: ATTEST"
    (p "All subsequent messages encrypted.")
    (p "Both parties prove identity using Simple Public Key Infrastructure (SPKI) principals.")
    (code "ATTEST payload (encrypted):\n  principal-hash \"|\" signature")
    (p "- principal-hash: SPKI principal (hex-encoded public key hash) - signature: Ed25519 signature over transcript")
    (p "Identity is cryptographic, not nominal. A principal is identified solely by its public key hash, never by a human-readable name. This is a prime directive.")
    (p "The attestation is the principal's authoritative affirmation of their own trust: I vouch for this channel. This is not a bearer token - it is my sealed declaration, bound to my realm.")
    (p "Transcript for signing:")
    (code "cookie-i || cookie-r || ephemeral-public")
    (subsection
      "Anonymous Attestation (Optional)"
      (p "For privacy, use Chaum-style blind signatures:")
      (code scheme "(define (blind-attest capability-hash)\n  ;; Prove authorization without revealing identity\n  (blind-sign capability-hash (blind-factor)))")))
  (section
    "Phase 5: OFFER"
    (p "Exchange authorized capabilities as SPKI tags.")
    (code "OFFER payload (encrypted):\n  (tag ( set capability ...))\n\nExample: \"(tag ( set read write replicate))\"")
    (p "Capabilities follow Memo-021 (Capability Delegation): - Only offer what you hold - Attenuation only, no amplification - Explicit, not ambient - Expressed as SPKI tag s-expressions")
    (p "Future: Full SPKI auth-certs with issuer signatures."))
  (section
    "Phase 6: CONFIRM"
    (p "Bind entire transcript.")
    (code "CONFIRM payload (encrypted):\n  BLAKE2b(cookie-i || cookie-r || their-principal)")
    (p "Both parties must produce matching hashes. Any tampering detected."))
  (section
    "DATA Phase"
    (p "Channel open. Encrypted messaging.")
    (code "DATA payload:\n  ChaCha20-Poly1305(key, nonce, plaintext)")
    (p "Nonce construction:")
    (code "nonce = sequence-number (8 bytes) || 0x00000000 (4 bytes)")
    (p "Sequence numbers: - Start at 0 - Increment per message - Prevent replay - Separate counters per direction"))
  (section
    "Algorithm Suites"
    (p "No runtime negotiation. Version determines suite.")
    (subsection
      "CIP/1.x (Current)"
      (table
        (header "Function " "Algorithm ")
        (row "Key Exchange " "X25519 ")
        (row "Signatures " "Ed25519 ")
        (row "AEAD " "ChaCha20-Poly1305 ")
        (row "Hash " "BLAKE2b ")
        (row "KDF " "HKDF-BLAKE2b ")))
    (subsection
      "CIP/2.x (Reserved: Post-Quantum)"
      (table
        (header "Function " "Algorithm ")
        (row "Key Exchange " "Kyber-1024 ")
        (row "Signatures " "Dilithium3 ")
        (row "AEAD " "ChaCha20-Poly1305 ")
        (row "Hash " "BLAKE2b ")))
    (subsection
      "CIP/3.x (Reserved: Hybrid)"
      (table
        (header "Function " "Algorithm ")
        (row "Key Exchange " "X25519 + Kyber ")
        (row "Signatures " "Ed25519 + Dilithium "))))
  (section
    "Security Properties"
    (subsection
      "DoS Resistance"
      (table
        (header "Attack " "Defense ")
        (row "SYN flood " "Cookie proves return path ")
        (row "Amplification " "No response until cookie echo ")
        (row "State exhaustion " "No state until Phase 3 ")))
    (subsection
      "Forward Secrecy"
      (p "Ephemeral X25519 keys: - Generated per session - Destroyed after key derivation - Compromise of long-term key doesn't expose past sessions"))
    (subsection
      "Identity Protection (SPKI Native)"
      (p "Principal identity: - Is the public key hash (not a name, not a certificate) - Only revealed after encryption established - Only revealed to authenticated peer - Never in plaintext on wire - Self-certifying: principal = hash(public_key)"))
    (subsection
      "Replay Protection"
      (list
        (item "Sequence numbers per direction")
        (item "Nonce never reused (fatal if violated)")
        (item "AEAD authentication fails on replay"))
      (p "Each security property addresses a specific attack class. DoS resistance prevents resource exhaustion before authentication; forward secrecy limits damage from key compromise; identity protection prevents traffic analysis; replay protection ensures message freshness.")))
  (section
    "Comparison"
    (table
      (header "Property " "TLS 1.3 " "IKEv2 " "CIP ")
      (row "Messages to establish " "2-3 " "4+ " "10 ")
      (row "DoS resistance " "Limited " "Cookies " "Cookies ")
      (row "Algorithm negotiation " "Yes " "Yes " "No ")
      (row "Certificate required " "Yes " "Yes " "No ")
      (row "Identity protection " "Partial " "Yes " "Yes ")
      (row "Capability binding " "No " "No " "Yes "))
    (p "CIP trades fewer round-trips for simplicity and capability integration."))
  (section
    "Implementation"
    (code scheme ";; Initiator\n(define ch (node-connect \"remote.host\" 4433))\n(channel-send ch '(request object-hash))\n(channel-recv ch)\n\n;; Responder\n(node-listen 4433 \"my-node\")\n(define ch (node-accept))\n(let ((msg (channel-recv ch)))\n  (channel-send ch (process msg)))"))
  (section
    "References"
    (list
      (item "Karn, P. & Simpson, W. (1999). PHOTURIS. RFC 2522.")
      (item "Karn, P. & Simpson, W. (1999). PHOTURIS Extended Schemes. RFC 2523.")
      (item "Bernstein, D.J. (2006). Curve25519.")
      (item "Bernstein, D.J. (2008). ChaCha20.")
      (item "Memo-021: Capability Delegation")
      (item "Memo-040: Security Architecture")))
  (section
    "Changelog"
    (p "- 2026-01-07: Initial specification")))

