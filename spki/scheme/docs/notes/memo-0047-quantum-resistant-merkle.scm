;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 47)
  (title "Quantum-Resistant Merkle Trees")
  (section
    "Abstract"
    (p "SHA-512 won't survive. Grover's algorithm halves the effective security - 256 bits becomes 128. For the wilderness of mirrors to endure the quantum winter, we need quantum-resistant Merkle trees. This Memo specifies the transition from flat SHA-512 hashes to tree-structured SHAKE256 hashes."))
  (section
    "The Problem"
    (p "Current cyberspace object identity:")
    (code "sha512(content) → 64 bytes → object address")
    (p "Against a quantum computer with Grover's algorithm: - Classical security: 256 bits - Quantum security: 128 bits (square root)")
    (p "128 bits may be acceptable for some threat models, but cyberspace is built to last. The Library of Alexandria burned once. We won't let quantum computers burn it again."))
  (section
    "The Solution: Merkle Trees"
    (p "Instead of hashing content as a flat blob, structure it as a tree:")
    (code "                    ┌─────────────────┐\n                    │   Merkle Root   │  ← Object identity\n                    │  shake256(...)  │\n                    └────────┬────────┘\n                             │\n              ┌──────────────┼──────────────┐\n              │              │              │\n         ┌────▼────┐    ┌────▼────┐    ┌────▼────┐\n         │ Node 0  │    │ Node 1  │    │ Node 2  │\n         └────┬────┘    └────┬────┘    └────┬────┘\n              │              │              │\n        ┌─────┴─────┐  ┌─────┴─────┐  ┌─────┴─────┐\n        │           │  │           │  │           │\n    ┌───▼───┐ ┌───▼───┐ ┌───▼───┐ ┌───▼───┐ ┌───▼───┐ ...\n    │Chunk 0│ │Chunk 1│ │Chunk 2│ │Chunk 3│ │Chunk 4│\n    │ 4 KB  │ │ 4 KB  │ │ 4 KB  │ │ 4 KB  │ │ 4 KB  │\n    └───────┘ └───────┘ └───────┘ └───────┘ └───────┘")
    (p "Benefits:")
    (list
      (item "Incremental updates - Change one chunk, rehash one branch")
      (item "Selective disclosure - Prove a chunk exists without revealing siblings")
      (item "Streaming verification - Verify chunks as they arrive")
      (item "Parallelizable - Hash chunks concurrently")
      (item "Quantum-resistant - SHAKE256 at every node")))
  (section
    "Hash Function: SHAKE256"
    (p "SHAKE256 is an extendable-output function (XOF) from the SHA-3 (Keccak) family.")
    (p "Why SHAKE256:")
    (table
      (header "Property " "Value ")
      (row "Security level " "256-bit classical, 128-bit quantum ")
      (row "Output length " "Variable (we use 256 bits) ")
      (row "Construction " "Sponge (different from SHA-2's Merkle-Damgård) ")
      (row "Standard " "NIST FIPS 202 ")
      (row "Used by " "SPHINCS+ (post-quantum signatures) ")
      (row "In libsodium " "No, but in OpenSSL, libgcrypt "))
    (p "Alternative: BLAKE3")
    (table
      (header "Property " "Value ")
      (row "Security level " "256-bit classical, 128-bit quantum ")
      (row "Output length " "Variable ")
      (row "Construction " "Merkle tree internally ")
      (row "Speed " "Very fast, SIMD optimized ")
      (row "Standard " "Not NIST, but widely trusted "))
    (p "BLAKE3 is faster and already tree-structured, but SHAKE256 has NIST blessing. We support both."))
  (section
    "Object Format"
    (subsection
      "Current (Legacy)"
      (code scheme "(object\n  (hash \"sha512:3a7bd3e2c4f8...\")\n  (size 1048576)\n  (content ...))"))
    (subsection
      "Quantum-Resistant"
      (code scheme "(object\n  (merkle-root \"shake256:7f4a2b9c...\")\n  (hash-algorithm \"shake256\")          ; or \"blake3\"\n  (tree-params\n    (chunk-size 4096)                  ; 4 KB chunks\n    (fanout 16)                        ; Children per node\n    (depth 4))                         ; Tree depth\n  (size 1048576)\n  (content ...))"))
    (subsection
      "Transition Period (Dual Hash)"
      (code scheme "(object\n  (hash \"sha512:3a7bd3e2c4f8...\")           ; Legacy - for old clients\n  (merkle-root \"shake256:7f4a2b9c...\")      ; Quantum-resistant\n  (hash-algorithm \"shake256\")\n  (tree-params\n    (chunk-size 4096)\n    (fanout 16)\n    (depth 4))\n  (size 1048576)\n  (content ...))")
      (p "Old clients use hash. New clients use merkle-root. Both verify the same content.")))
  (section
    "Tree Construction"
    (subsection
      "Algorithm"
      (code scheme "(define (merkle-hash content algorithm chunk-size fanout)\n  \"Build Merkle tree, return root hash\"\n\n  ;; 1. Split content into chunks\n  (let* ((chunks (chunk-content content chunk-size))\n\n         ;; 2. Hash each chunk (leaves)\n         (leaves (map (lambda (chunk)\n                        (hash algorithm chunk))\n                      chunks))\n\n         ;; 3. Build tree bottom-up\n         (root (build-tree leaves fanout algorithm)))\n\n    root))\n\n(define (build-tree nodes fanout algorithm)\n  \"Combine nodes into parent nodes until one root remains\"\n  (if (<= (length nodes) 1)\n      (car nodes)\n      (let ((parents (map (lambda (group)\n                            (hash algorithm (apply append group)))\n                          (partition nodes fanout))))\n        (build-tree parents fanout algorithm))))"))
    (subsection
      "Node Hashing"
      (p "Each internal node hashes the concatenation of its children:")
      (code "nodehash = shake256(child0 || child1 || ... || childn)")
      (p "For leaves:")
      (code "leafhash = shake256(chunkdata)"))
    (subsection
      "Canonical Parameters"
      (table
        (header "Parameter " "Default " "Notes ")
        (row "chunk-size " "4096 " "4 KB, filesystem-friendly ")
        (row "fanout " "16 " "Balance between depth and width ")
        (row "algorithm " "shake256 " "NIST approved ")
        (row "output-length " "32 " "256 bits "))))
  (section
    "Proofs"
    (subsection
      "Inclusion Proof"
      (p "Prove a chunk is part of an object without revealing other chunks:")
      (code scheme "(inclusion-proof\n  (merkle-root \"shake256:7f4a2b9c...\")\n  (chunk-index 42)\n  (chunk-hash \"shake256:abc123...\")\n  (path\n    ((sibling \"shake256:def456...\" position left)\n     (sibling \"shake256:789abc...\" position right)\n     (sibling \"shake256:012def...\" position left))))")
      (p "Verifier reconstructs path to root:")
      (code "chunk_hash → combine with sibling → ... → must equal merkle-root"))
    (subsection
      "Exclusion Proof"
      (p "Prove a chunk does NOT exist (for sparse objects):")
      (code scheme "(exclusion-proof\n  (merkle-root \"shake256:7f4a2b9c...\")\n  (chunk-index 999)\n  (boundary-left 998 \"shake256:left...\")\n  (boundary-right 1000 \"shake256:right...\")\n  (path ...))")))
  (section
    "Streaming Verification"
    (p "Large objects can be verified chunk-by-chunk as they stream:")
    (code scheme "(define (verify-stream merkle-root chunk-size)\n  \"Return a verifier that checks chunks as they arrive\"\n  (let ((received-chunks '())\n        (verified-nodes (make-hash-table)))\n\n    (lambda (chunk-index chunk-data proof)\n      ;; Verify this chunk against the proof\n      (let ((chunk-hash (shake256 chunk-data)))\n        (if (verify-inclusion-proof merkle-root chunk-index chunk-hash proof)\n            (begin\n              (cache-verified-node! verified-nodes chunk-index chunk-hash)\n              #t)\n            #f)))))")
    (p "You don't need the whole object to start verifying. Each chunk carries its own proof."))
  (section
    "The Forest"
    (p "The soup becomes a forest of Merkle trees:")
    (code "┌─────────────────────────────────────────────────────────────────┐\n│                    THE FOREST (formerly soup)                    │\n│                                                                  │\n│     🌲 obj    🌲 obj       ┌─────────────────┐      🌲 obj       │\n│          🌲 obj           │░░░░░░░░░░░░░░░░░│           🌲 obj  │\n│    🌲 obj          🌲 obj │░░░  REALM  ░░░░░│    🌲 obj         │\n│         🌲 obj            │░░░ (island) ░░░░│         🌲 obj    │\n│   🌲 obj       🌲 obj     │░░░░░░░░░░░░░░░░░│  🌲 obj           │\n│        🌲 obj             └─────────────────┘       🌲 obj      │\n│                                                                  │\n│   Each object a tree. Each tree quantum-hardened.               │\n└─────────────────────────────────────────────────────────────────┘")
    (p "Objects are trees. The wilderness of mirrors becomes a forest. Agents navigate between trees, climbing branches, verifying paths. The capability chain is still their thread - but now the mirrors are structured."))
  (section
    "Migration"
    (subsection
      "Phase 1: Dual Hash (Now → Q-Day - 5 years)"
      (p "All new objects get both hashes. Old objects rehashed on access.")
      (code scheme "(define (store-object content)\n  (let ((legacy-hash (sha512 content))\n        (merkle-root (merkle-hash content 'shake256 4096 16)))\n    (vault-store\n      `(object\n        (hash ,(string-append \"sha512:\" legacy-hash))\n        (merkle-root ,(string-append \"shake256:\" merkle-root))\n        ...))))"))
    (subsection
      "Phase 2: Merkle Primary (Q-Day - 5 years → Q-Day)"
      (p "Merkle root becomes the canonical address. SHA-512 kept for compatibility."))
    (subsection
      "Phase 3: Legacy Sunset (Q-Day → Q-Day + 2 years)"
      (p "SHA-512 hashes deprecated. Only Merkle roots used for addressing."))
    (subsection
      "Phase 4: Pure Quantum-Resistant (Q-Day + 2 years →)"
      (p "SHA-512 hashes removed from new objects. Legacy objects retain both for historical verification.")))
  (section
    "Performance"
    (table
      (header "Operation " "SHA-512 (flat) " "SHAKE256 (Merkle) " "Notes ")
      (row "Hash 1 MB " "2 ms " "3 ms " "Slightly slower ")
      (row "Hash 1 GB " "2000 ms " "2500 ms " "Tree overhead ")
      (row "Update 4 KB in 1 GB " "2000 ms " "15 ms " "Merkle wins ")
      (row "Prove inclusion " "N/A " "0.1 ms " "New capability ")
      (row "Streaming verify " "N/A " "Per-chunk " "New capability "))
    (p "The overhead is small. The benefits are large."))
  (section
    "Security Considerations"
    (subsection
      "Grover's Algorithm"
      (p "Grover's algorithm provides quadratic speedup for searching: - SHA-512: 2^256 → 2^128 quantum operations - SHAKE256-256: 2^256 → 2^128 quantum operations")
      (p "128-bit quantum security is considered sufficient for the foreseeable future."))
    (subsection
      "Second Preimage Resistance"
      (p "Finding another input that hashes to the same tree requires: - Classical: 2^256 operations - Quantum: 2^128 operations (Grover)"))
    (subsection
      "Tree Structure Attacks"
      (p "The Merkle tree structure must prevent: - Length extension: SHAKE256 immune (sponge construction) - Subtree collision: Domain separation in node hashing - Malleability: Canonical serialization required"))
    (subsection
      "Implementation"
      (code scheme ";; Domain separation for nodes vs leaves\n(define (hash-leaf algorithm chunk)\n  (hash algorithm (bytevector-append #u8(0) chunk)))\n\n(define (hash-node algorithm children)\n  (hash algorithm (bytevector-append #u8(1) (apply bytevector-append children))))")
      (p "The 0x00 prefix for leaves and 0x01 for nodes prevents a leaf from being interpreted as a node.")))
  (section
    "Invariants"
    (code "M1. Object identity is Merkle root\n    id(o) = merkle-root(shake256, chunks(o))\n\nM2. Any chunk is provable\n    chunk(o,i) → ∃proof: verify(root(o), i, chunk, proof)\n\nM3. Tree structure is canonical\n    tree(content, params) is deterministic\n\nM4. Dual hashes are consistent\n    sha512(content) ↔ merkle-root(content) verify same content\n\nM5. Migration preserves identity\n    old-objects retain verifiable legacy hashes"))
  (section
    "References"
    (list
      (item "NIST FIPS 202 - SHA-3 Standard (SHAKE256)")
      (item "BLAKE3 specification - https://github.com/BLAKE3-team/BLAKE3")
      (item "Merkle, R., \"A Digital Signature Based on a Conventional Encryption Function\", 1987")
      (item "Grover, L., \"A Fast Quantum Mechanical Algorithm for Database Search\", 1996")
      (item "Memo-040 - Cyberspace Security Architecture")))
  (section
    "Changelog"
    (list
      (item "2026-01-08")
      (item "Initial draft"))))

