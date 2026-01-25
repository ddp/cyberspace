;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 43)
  (title "Entropy Pool")
  (section
    "Abstract"
    (p "All cryptographic operations in Cyberspace require high-quality entropy. This Memo specifies the canonical entropy sources for each platform, ensuring consistent, auditable, and secure randomness across the entire system."))
  (section
    "Motivation"
    (subsection
      "The Fundamental Requirement"
      (p "All cryptography requires true quantum randomness. The math doesn't work otherwise.")
      (p "Cryptographic proofs assume a source of bits that are:")
      (list
        (item "Statistically uniform - Each bit equally likely 0 or 1")
        (item "Independent - No correlations between bits")
        (item "Unpredictable in principle - Not just hard to predict, but impossible"))
      (p "Only quantum mechanical processes satisfy condition 3. Classical chaotic systems (lava lamps, thermal noise, ring oscillators) are deterministic - an adversary with sufficient knowledge of initial conditions could, in theory, predict their output. Quantum processes have no \"initial conditions\" to know - the randomness is fundamental to physics itself.")
      (p "Why this matters: - Security proofs assume perfect randomness - Key security = min(algorithmbits, entropybits) - A 256-bit key from a 32-bit PRNG seed provides only 32 bits of security - Nation-state adversaries may have capabilities to model classical entropy sources"))
    (subsection
      "Cryptographic Operations Requiring Entropy"
      (list
        (item "Key generation (Ed25519, X25519)")
        (item "Nonce generation (XSalsa20-Poly1305)")
        (item "Salt generation (Argon2id)")
        (item "Shamir secret sharing")
        (item "Challenge-response protocols")
        (item "Zero-knowledge proofs"))
      (p "Every cryptographic primitive assumes access to uniformly random bits. Without true entropy, key generation produces predictable keys, nonces repeat, and mathematical security guarantees collapse. A realm's sovereignty rests entirely on the unpredictability of its secrets.")))
  (section
    "The Commandment"
    (p "THOU SHALT USE CRYPTOGRAPHIC RANDOMNESS.")
    (p "All randomness in Cyberspace flows through libsodium's randombytes_buf(), which uses:")
    (list
      (item "Linux: getrandom(2) syscall")
      (item "macOS: SecRandomCopyBytes")
      (item "OpenBSD: getentropy(2)")
      (item "Windows: RtlGenRandom"))
    (p "Hardware entropy (RDRAND/RDSEED) feeds the OS pool. Quantum RNG (ID Quantique, drand beacons) planned for Phase 3+.")
    (p "There are NO EXCEPTIONS. Never use:")
    (list
      (item "(chicken random) - Uses Mersenne Twister, not cryptographically secure")
      (item "srfi-27 - Statistical randomness, not cryptographic")
      (item "/dev/urandom directly - Platform-specific, misses getrandom(2) benefits")
      (item "arc4random_buf() directly - Use libsodium's abstraction")
      (item "Custom PRNGs - Unaudited, likely insecure"))
    (p "The only approved functions are from crypto-ffi:")
    (code scheme "(random-bytes n)         ; n cryptographically random bytes
(random-u8)              ; random byte [0, 255]
(random-u32)             ; random 32-bit unsigned
(random-uniform limit)   ; uniform [0, limit) with rejection sampling"))
  (section
    "Boot-Time FIPS Testing"
    (p "Trust but verify. Every entropy source MUST be tested at boot time with FIPS 140-2 statistical tests on 20,000 bits (2500 bytes):")
    (subsection
      "Monobit Test"
      (p "Count of 1-bits must be 9654 < n < 10346 (within 3.43σ of expected 10000).")
      (code scheme "(fips-monobit-test bytes)  ; Pass if balanced"))
    (subsection
      "Poker Test"
      (p "Distribution of 4-bit nibbles must be uniform. X = (16/5000) × Σf² - 5000 must satisfy 1.03 < X < 57.4.")
      (code scheme "(fips-poker-test bytes)   ; Pass if nibbles distributed"))
    (subsection
      "Runs Test"
      (p "Runs of consecutive 0s and 1s must fall within bounds:")
      (table
        (header "Run Length" "Expected Range (each bit value)")
        (row "1" "2267-2733")
        (row "2" "1079-1421")
        (row "3" "502-748")
        (row "4" "223-402")
        (row "5" "90-223")
        (row "6+" "90-223"))
      (code scheme "(fips-runs-test bytes)    ; Pass if run distribution normal"))
    (subsection
      "Long Run Test"
      (p "No run of 26 or more consecutive identical bits.")
      (code scheme "(fips-long-run-test bytes) ; Pass if no pathological runs"))
    (p "Implementation in fips.scm:")
    (code scheme "(define (test-randomness)
  \"FIPS 140-2 randomness tests on 20,000 bits.\"
  (let* ((sample (random-bytes 2500))
         (bytes (blob->u8vector sample)))
    (and (fips-monobit-test bytes)
         (fips-poker-test bytes)
         (fips-runs-test bytes)
         (fips-long-run-test bytes))))

;; Called at REPL boot and by forge module load
(unless (test-randomness)
  (error \"Entropy source failed FIPS 140-2 tests\"))")
    (p "If any test fails, Cyberspace refuses to start. There is no fallback. Weak entropy is not acceptable."))
  (section
    "Specification"
    (subsection
      "Canonical Source: libsodium"
      (p "All Cyberspace implementations MUST use libsodium's randombytes_buf() as the primary entropy source:")
      (code "randombytes_buf(buffer, size)")
      (p "libsodium automatically selects the best available source: - Linux: getrandom(2) syscall, falls back to /dev/urandom - macOS/iOS: arc4randombuf() - Windows: RtlGenRandom() - OpenBSD: arc4randombuf() (ChaCha20-based)"))
    (subsection
      "Why libsodium?"
      (list
        (item "Cross-platform consistency - Same API everywhere")
        (item "Automatic best-source selection - No platform-specific code")
        (item "Initialization safety - Blocks until entropy available")
        (item "Fork safety - Handles process forking correctly")
        (item "Audited implementation - Widely reviewed cryptographic library"))
      (p "libsodium provides a single canonical interface for entropy across all platforms. Using one audited implementation eliminates the class of bugs where platform-specific entropy code diverges or contains subtle flaws."))
    (subsection
      "Platform Requirements"
      (p "#### Scheme (CHICKEN)")
      (code scheme ";; crypto-ffi.scm provides:\n(define (random-bytes n)\n  \"Generate n cryptographically secure random bytes\"\n  (let ((buf (make-blob n)))\n    ((foreign-lambda void \"randombytes_buf\" scheme-pointer unsigned-integer)\n     buf n)\n    buf))")
      (p "All Scheme code MUST use random-bytes from crypto-ffi. NEVER use: - (chicken random) - Uses PRNG, not cryptographically secure - /dev/random directly - Platform-specific, may block - Custom PRNGs - Unaudited, likely insecure")
      (p "#### OCaml")
      (p "Status: Open Issue")
      (p "OCaml implementations should use one of: - mirage-crypto-rng with Nocrypto.Rng.generate - Direct FFI to libsodium via ctypes")
      (p "Decision pending based on: - Multicore OCaml compatibility - Domain-local PRNG state handling - Build system integration (dune vs opam)"))
    (subsection
      "Entropy Initialization"
      (p "Before ANY cryptographic operation, ensure libsodium is initialized:")
      (code scheme "(define (sodium-init)\n  (let ((result ((foreign-lambda int \"sodiuminit\"))))\n    (when (= result -1)\n      (error \"sodiuminit failed - entropy source unavailable\"))))")
      (p "sodium_init() is idempotent and thread-safe. Call it early in program startup."))
    (subsection
      "Key Generation"
      (p "All key generation MUST use libsodium's key generation functions, which internally use randombytes_buf():")
      (table
        (header "Operation " "Function ")
        (row "Ed25519 signing key " "cryptosignkeypair() ")
        (row "X25519 key exchange " "cryptoboxkeypair() ")
        (row "Symmetric key " "cryptosecretboxkeygen() ")
        (row "Generic random " "randombytes_buf() ")))
    (subsection
      "Nonce Generation"
      (p "Nonces MUST be generated fresh for each encryption:")
      (code scheme "(define (generate-nonce)\n  (random-bytes (secretbox-noncebytes)))  ;; 24 bytes")
      (p "For XSalsa20-Poly1305 with 24-byte nonces, random nonces are safe: - 2^192 possible nonces - Birthday collision after ~2^96 messages - Practical limit: ~2^64 messages per key (still astronomical)"))
    (subsection
      "Salt Generation"
      (p "For Argon2id key derivation:")
      (code scheme "(define (generate-salt)\n  (random-bytes 16))  ;; cryptopwhashSALTBYTES")
      (p "Salts prevent rainbow table attacks. Each salt MUST be unique per derived key.")))
  (section
    "Deep Dive: Entropy Sources"
    (p "Randomness is the foundation of all cryptography. This section explores the physics and engineering of true randomness.")
    (subsection
      "The Entropy Hierarchy"
      (code "┌───────────────────────────────────────────────────────────┐\n│                   Entropy Quality Pyramid                   │\n├───────────────────────────────────────────────────────────┤\n│                                                             │\n│                    ┌───────────────┐                        │\n│           ***      │  Quantum RNG  │  <- TRUE RANDOMNESS    │\n│                    └───────────────┘     (required for      │\n│                          ^               cryptographic      │\n│                          │               security)          │\n│                    ──────┴──────                            │\n│                    SECURITY BOUNDARY                        │\n│                    ─────────────────                        │\n│                          │                                  │\n│                          v                                  │\n│                  ┌───────────────────┐                      │\n│                  │  Hardware TRNG    │  <- Best effort      │\n│                  └───────────────────┘     (should feed     │\n│                ┌───────────────────────┐   quantum source)  │\n│                │  Environmental/Analog │                    │\n│                └───────────────────────┘                    │\n│              ┌───────────────────────────┐                  │\n│              │  Public Beacons (NIST)    │  <- Verifiable   │\n│              └───────────────────────────┘                  │\n│            ┌───────────────────────────────┐                │\n│            │  OS Entropy Pool              │  <- Mixed      │\n│            └───────────────────────────────┘                │\n│          ┌───────────────────────────────────┐              │\n│          │  CSPRNG (seeded from above)       │  <- Expand   │\n│          └───────────────────────────────────┘              │\n│                                                             │\n└───────────────────────────────────────────────────────────┘\n\n   *** = Cryptographic operations MUST trace to quantum sources")
      (p "Critical distinction: Everything below the security boundary is computationally secure (hard to predict), not information-theoretically secure (impossible to predict). For operations like key generation that must withstand future advances in computation and modeling, only quantum sources provide provable security."))
    (subsection
      "Practical Access to Quantum Randomness"
      (p "The ideal: Every cryptographic operation sources entropy from a local quantum RNG.")
      (p "Current reality: Most systems rely on:")
      (list
        (item "Hardware RNG (thermal noise, ring oscillators) - classical, but unpredictable at human scales")
        (item "OS mixing of multiple sources - defense in depth")
        (item "NIST beacon - quantum-sourced, publicly verifiable, but network-dependent"))
      (p "Path forward for Cyberspace: - Phase 1 (Now): libsodium with OS entropy (relies on hardware quality) - Phase 2: Optional quantum RNG hardware support (USB devices, PCIe cards) - Phase 3: Attestation of entropy source in realm metadata - Phase 4: Quantum RNG as standard infrastructure (as quantum internet develops)")
      (p "Minimum acceptable: Modern Intel/AMD RDSEED instruction, which samples thermal noise at the silicon level. While not provably quantum, it has no known exploits and is mixed with other sources.")
      (p "Goal: True quantum randomness as the foundation. The math requires it; the engineering will catch up."))
    (subsection
      "Cyberspace as Entropy Provider"
      (p "We will provide all the randomness that our users need - on demand, for whatever their cryptographic desires.")
      (p "Cyberspace realms can serve as entropy sources for their users:")
      (code scheme ";; Request entropy from the realm\n(realm-entropy-request\n  (bytes 32)\n  (purpose \"key-generation\")\n  (attestation-required #t))\n\n;; Response includes attestation of entropy source\n(realm-entropy-response\n  (value #${...32 bytes...})\n  (source \"quantum-rng\")\n  (attestation (signed-by realm-principal)\n               (hardware \"ID-Quantique-QUANTIS\")\n               (timestamp 1736344800)))")
      (p "Entropy services:")
      (list
        (item "Local generation - Realm uses its best available source")
        (item "Federated entropy - Request quantum entropy from realms with quantum hardware")
        (item "Beacon aggregation - Mix NIST + drand + realm sources")
        (item "Attestation chain - Prove the entropy source for audit"))
      (p "Long-term vision: A network of realms with quantum RNG hardware providing verifiable, quantum-sourced entropy to all participants. The soup carries randomness as naturally as it carries data."))
    (subsection
      "True Random Number Generators (TRNG)"
      (p "True randomness comes from physical processes that are fundamentally unpredictable:")
      (p "#### Quantum Sources (Required for Provable Security)")
      (p "The only sources that satisfy cryptographic assumptions. Quantum mechanics guarantees unpredictability:")
      (list
        (item "Photon beam splitters")
        (item "Single photon hits 50/50 beam splitter, detection is truly random")
        (item "Vacuum fluctuations")
        (item "Measuring quantum vacuum state")
        (item "Quantum tunneling")
        (item "Electron tunneling through barriers")
        (item "Nuclear decay")
        (item "Timing of radioactive decay events"))
      (p "Commercial quantum RNGs: ID Quantique (QUANTIS), Quintessence Labs, Crypta Labs")
      (p "#### Silicon-Based TRNG")
      (p "Modern CPUs include hardware random number generators:")
      (table
        (header "CPU " "Instruction " "Mechanism ")
        (row "Intel " "RDRAND/RDSEED " "Thermal noise + AES-CBC-MAC ")
        (row "AMD " "RDRAND/RDSEED " "Ring oscillator jitter ")
        (row "ARM " "TRNG " "Metastable flip-flops ")
        (row "RISC-V " "Zkr extension " "Implementation-defined "))
      (p "Security note: Intel's RDRAND has faced scrutiny. Mix with other sources."))
    (subsection
      "Environmental Entropy: Lavarand"
      (p "The most famous entropy source in computing.")
      (p "Silicon Graphics (SGI) invented Lavarand in 1996. Cloudflare operates the modern successor.")
      (p "#### How It Works")
      (code "┌─────────────────────────────────────────────────────────────┐\n│                     LAVARAND SYSTEM                          │\n├─────────────────────────────────────────────────────────────┤\n│                                                              │\n│   ┌─────────┐    ┌─────────┐    ┌─────────────────────┐     │\n│   │  Lava   │    │ Camera  │    │  Image → Hash       │     │\n│   │  Lamp   │───▶│  Feed   │───▶│  SHA-256 per frame  │     │\n│   │  Wall   │    │         │    │                     │     │\n│   └─────────┘    └─────────┘    └──────────┬──────────┘     │\n│                                            │                 │\n│                                            ▼                 │\n│                                  ┌─────────────────────┐     │\n│                                  │  Entropy Pool       │     │\n│                                  │  (mix with CSPRNG)  │     │\n│                                  └─────────────────────┘     │\n│                                                              │\n└─────────────────────────────────────────────────────────────┘")
      (p "#### Why Lava Lamps?")
      (list
        (item "Chaotic fluid dynamics - Wax movement is unpredictable")
        (item "Thermal convection - Heat creates complex flow patterns")
        (item "High bandwidth - Each video frame yields fresh entropy")
        (item "Tamper-evident - Physical installation is visible")
        (item "Independent source - Not correlated with CPU state"))
      (p "Cloudflare's wall of 100 lava lamps generates entropy for ~10% of internet HTTPS traffic.")
      (p "#### Other Environmental Sources")
      (table
        (header "Source " "Mechanism " "Bandwidth ")
        (row "Lava lamps " "Fluid dynamics " "~100 Kbit/s ")
        (row "Radioactive decay " "Nuclear physics " "~1-10 Kbit/s ")
        (row "Atmospheric noise " "RF antenna " "~1 Mbit/s ")
        (row "Thermal camera " "Johnson-Nyquist noise " "~10 Kbit/s ")
        (row "Double pendulum " "Chaotic motion " "~100 bit/s ")
        (row "Keyboard timing " "Human unpredictability " "~1-10 bit/keystroke ")))
    (subsection
      "Public Randomness Beacons"
      (p "Beacons provide verifiable public randomness - useful for: - Lottery systems - Audit sampling - Distributed protocols - Zero-knowledge proofs")
      (p "#### NIST Randomness Beacon")
      (p "The National Institute of Standards and Technology operates a public randomness beacon since 2013.")
      (code "https://beacon.nist.gov/beacon/2.0/pulse/last")
      (p "Architecture:")
      (code "┌─────────────────────────────────────────────────────────────┐\n│                   NIST BEACON 2.0                            │\n├─────────────────────────────────────────────────────────────┤\n│                                                              │\n│  Sources:           Processing:         Output:              │\n│  ┌─────────┐       ┌───────────┐      ┌──────────────┐      │\n│  │ Quantum │──┐    │           │      │ Pulse Record │      │\n│  │   RNG   │  │    │  SHA-512  │      ├──────────────┤      │\n│  └─────────┘  │    │  mixing   │      │ timestamp    │      │\n│  ┌─────────┐  ├───▶│     +     │─────▶│ localRandom  │      │\n│  │Photonic │  │    │  signing  │      │ outputValue  │      │\n│  │  Noise  │──┘    │           │      │ signatureVal │      │\n│  └─────────┘       └───────────┘      └──────────────┘      │\n│                                                              │\n│  Pulse interval: 60 seconds                                  │\n│  Hash chain: Each pulse includes hash of previous            │\n│  Signature: RSA-2048 (Beacon 2.0)                           │\n│                                                              │\n└─────────────────────────────────────────────────────────────┘")
      (p "Pulse Record Contents: - uri - Unique pulse identifier - version - Beacon protocol version - timeStamp - Unix timestamp - localRandomValue - 512 bits from quantum sources - outputValue - SHA-512 hash (the public random value) - statusCode - Health indicator - signatureValue - Digital signature")
      (p "Properties: - Unpredictable - Cannot be known before publication - Verifiable - Anyone can verify the signature chain - Non-manipulable - NIST cannot control output - Archived - Full history publicly available")
      (p "Use in Cyberspace:")
      (code scheme ";; For ceremonies, audits, public verifiability\n(define (fetch-nist-beacon)\n  (let* ((response (http-get \"https://beacon.nist.gov/beacon/2.0/pulse/last\"))\n         (pulse (json-parse response))\n         (output (assoc-ref pulse \"outputValue\")))\n    (hex->blob output)))")
      (p "#### Other Public Beacons")
      (table
        (header "Beacon " "Operator " "Source " "Interval ")
        (row "NIST Beacon " "US NIST " "Quantum + photonic " "60 seconds ")
        (row "Chile UChile " "University of Chile " "Seismic + radio " "60 seconds ")
        (row "Cloudflare drand " "League of Entropy " "Distributed threshold " "30 seconds ")
        (row "IRISA " "French research " "Multiple physical " "60 seconds "))
      (p "#### League of Entropy (drand)")
      (p "Distributed randomness beacon - no single party controls the output:")
      (code "┌─────────────────────────────────────────────────────────────┐\n│              DRAND DISTRIBUTED BEACON                        │\n├─────────────────────────────────────────────────────────────┤\n│                                                              │\n│   Cloudflare ──┐                                            │\n│                │                                             │\n│   EPFL ────────┼─── Threshold ───▶ Public Random           │\n│                │    BLS Sig          (t-of-n nodes          │\n│   Protocol ────┤    (t-of-n)          must participate)     │\n│   Labs         │                                             │\n│                │                                             │\n│   Kudelski ────┘                                            │\n│                                                              │\n│   Endpoint: https://api.drand.sh/public/latest              │\n│   Chain: 8990e7a9aaed2ffed73dbd7092123d6f289930540d7651336225dc172e51b2ce │\n│                                                              │\n└─────────────────────────────────────────────────────────────┘"))
    (subsection
      "Entropy Mixing"
      (p "Real systems mix multiple sources for defense in depth:")
      (code scheme ";; Conceptual entropy mixer\n(define (mix-entropy-sources)\n  (let ((hw (hardware-random-bytes 32))      ;; RDRAND\n        (os (os-entropy-pool-bytes 32))       ;; /dev/urandom\n        (env (environmental-entropy 32))      ;; If available\n        (beacon (cached-nist-beacon)))        ;; Public verifiability\n    ;; Mix with HKDF or similar\n    (hkdf-sha512\n      (blob-append hw os env beacon)\n      \"cyberspace-entropy-v1\"\n      64)))"))
    (subsection
      "Historical Entropy Failures"
      (p "Learning from disasters:")
      (table
        (header "Incident " "Year " "Cause " "Impact ")
        (row "Netscape SSL " "1995 " "PID + timestamp = predictable " "All SSL broken ")
        (row "Debian OpenSSL " "2006-2008 " "Valgrind \"fix\" removed entropy " "32,767 possible keys ")
        (row "Android SecureRandom " "2013 " "PRNG state reuse " "Bitcoin wallets drained ")
        (row "DualECDRBG " "2013 " "NSA backdoor in constants " "Unknown surveillance ")
        (row "Taiwan smart cards " "2013 " "Shared PRNG state " "Factored RSA keys "))
      (p "Lesson: Defense in depth. Mix multiple independent sources."))
    (subsection
      "Entropy Requirements by Operation"
      (table
        (header "Operation " "Entropy Needed " "Notes ")
        (row "Ed25519 keypair " "32 bytes " "Full key security ")
        (row "X25519 keypair " "32 bytes " "Full key security ")
        (row "XSalsa20 nonce " "24 bytes " "Random OK (large space) ")
        (row "AES-GCM nonce " "12 bytes " "Counter preferred (small space) ")
        (row "Argon2id salt " "16 bytes " "Unique per derivation ")
        (row "Session ID " "16-32 bytes " "Unpredictable ")
        (row "ECDSA k-value " "32 bytes " "CRITICAL - must not repeat "))))
  (section
    "Security Considerations"
    (subsection
      "Entropy Exhaustion"
      (p "libsodium's randombytes_buf() never blocks on modern systems: - Uses ChaCha20 CSPRNG seeded from OS entropy - OS entropy pools are continuously replenished - Hardware RNG (RDRAND/RDSEED) available on modern CPUs"))
    (subsection
      "VM/Container Considerations"
      (p "Virtual machines may have limited entropy at boot: - Use virtio-rng to pass host entropy to guests - Ensure haveged or rng-tools if entropy-limited - libsodium will block until sufficient entropy available"))
    (subsection
      "Fork Safety"
      (p "libsodium handles fork correctly: - Automatic re-seeding after fork() - No duplicate random sequences in child processes"))
    (subsection
      "Deterministic Testing"
      (p "For reproducible tests ONLY (never production):")
      (code scheme "(define (set-test-seed seed)\n  \"WARNING: Deterministic mode - testing only\"\n  ((foreign-lambda void \"randombytes_stir\")))")
      (p "Production code MUST use true entropy.")))
  (section
    "Implementation Notes"
    (subsection
      "Current Status"
      (table
        (header "Component " "Entropy Source " "Status ")
        (row "crypto-ffi.scm " "randombytes_buf() " "Implemented ")
        (row "vault.scm (keystore) " "random-bytes " "Implemented ")
        (row "OCaml core " "TBD " "Open Issue ")))
    (subsection
      "Audit Trail"
      (p "All key generation events should be logged (not the keys themselves):")
      (code scheme "(seal-commit #f\n  `(entropy-event\n    (type \"key-generation\")\n    (algorithm \"ed25519\")\n    (timestamp ,(current-seconds))\n    (entropy-source \"libsodium\")))"))
    (subsection
      "Hardware Entropy"
      (p "When available, hardware entropy sources enhance security:")
      (table
        (header "Platform " "Hardware RNG ")
        (row "Intel/AMD " "RDRAND, RDSEED instructions ")
        (row "ARM " "TRNG (True Random Number Generator) ")
        (row "Apple Silicon " "Secure Enclave entropy "))
      (p "libsodium automatically uses hardware entropy when available.")))
  (section
    "Migration"
    (subsection
      "Phase 1: Audit (Complete)"
      (list
        (item "Identified all randomness usage in codebase ✓")
        (item "Replaced non-libsodium sources ✓")
        (item "Fixed: repl.scm collapse used (random), now uses random-uniform")
        (item "Fixed: forge.scm read /dev/urandom directly, now uses crypto-ffi")))
    (subsection
      "Phase 2: Standardize (Complete)"
      (list
        (item "All Scheme uses random-bytes/random-uniform from crypto-ffi ✓")
        (item "OCaml approach: TBD (will use libsodium FFI)")))
    (subsection
      "Phase 3: Verify (Complete)"
      (list
        (item "FIPS 140-2 statistical tests implemented in fips.scm ✓")
        (item "Boot-time entropy verification on every REPL start ✓")
        (item "forge module verifies entropy source on load ✓")))
    (subsection
      "Phase 4: Quantum (Future)"
      (list
        (item "Hardware quantum RNG support (ID Quantique, etc.)")
        (item "Attestation of entropy source in realm metadata")
        (item "Federated quantum entropy from partner realms"))))
  (section
    "References"
    (list
      (item "libsodium documentation: https://doc.libsodium.org/")
      (item "NIST SP 800-90A: Recommendations for Random Number Generation")
      (item "RFC 4086: Randomness Requirements for Security")
      (item "ChaCha20: https://cr.yp.to/chacha.html")))
  (section
    "Appendix: Entropy Quality Testing"
    (subsection
      "Built-in FIPS Tests"
      (p "The fips.scm module provides FIPS 140-2 statistical tests that run automatically at boot:")
      (code scheme ";; Run all FIPS tests manually
(import fips)
(test-randomness)  ; => #t or #f

;; Individual tests on 2500 bytes
(let ((sample (blob->u8vector (random-bytes 2500))))
  (fips-monobit-test sample)
  (fips-poker-test sample)
  (fips-runs-test sample)
  (fips-long-run-test sample))"))
    (subsection
      "External Verification"
      (p "For additional paranoid verification with external tools:")
      (code bash "# Generate random data
csi -e \"(import crypto-ffi) (display (random-bytes 1000000))\" > random.bin

# Run NIST statistical tests
ent random.bin
dieharder -a -f random.bin")
      (p "Expected results: - Entropy: ~7.9999 bits per byte - Chi-square: p-value 0.01-0.99 - All dieharder tests: PASSED")))))

