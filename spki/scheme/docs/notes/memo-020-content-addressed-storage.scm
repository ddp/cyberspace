;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 20)
  (title "Content-Addressed Storage")
  (section
    "Abstract"
    (p "This RFC specifies content-addressed storage (CAS) for the Library of Cyberspace: a storage model where data is addressed by its cryptographic hash rather than by location. Content addressing provides immutability guarantees, automatic deduplication, and tamper-evident storage."))
  (section
    "Motivation"
    (p "Traditional storage systems use location-based addressing:")
    (list
      (item "DECtape: Physical position on magnetic tape")
      (item "Filesystems: Path names (/home/ddp/file.txt)")
      (item "Databases: Row IDs, primary keys")
      (item "URLs: Server + path (https://example.com/doc.ps)"))
    (p "Location-based addressing has fundamental problems:")
    (p "1. Mutability - Same address can point to different content over time 2. Link rot - Addresses become invalid when content moves 3. Duplication - Identical content stored multiple times 4. No verification - Address doesn't prove content integrity")
    (p "Content-addressed storage inverts this:")
    (code "Location-based:  address → content (many-to-one, mutable)\nContent-based:   content → address (one-to-one, immutable)")
    (p "The address IS the content's cryptographic fingerprint. If the content changes, the address changes. If two files have the same address, they are byte-for-byte identical."))
  (section
    "Content Addressing Model"
    (subsection
      "Hash as Address"
      (code scheme ";; Content determines address\n(define (content-address data)\n  (sha256 data))\n\n;; Store by hash\n(define (cas-store data)\n  (let ((hash (content-address data)))\n    (write-blob (hash->path hash) data)\n    hash))\n\n;; Retrieve by hash\n(define (cas-retrieve hash)\n  (let ((data (read-blob (hash->path hash))))\n    (if (equal? hash (content-address data))\n        data\n        (error \"Content tampered\"))))"))
    (subsection
      "Properties"
      (table
        (header "Property " "Location-Based " "Content-Addressed ")
        (row "Address stability " "Unstable " "Permanent ")
        (row "Content verification " "External " "Intrinsic ")
        (row "Deduplication " "Manual " "Automatic ")
        (row "Mutability " "Mutable " "Immutable ")
        (row "Link rot " "Common " "Impossible ")))
    (subsection
      "Hash Function Requirements"
      (p "The hash function MUST be:")
      (p "1. Collision-resistant - Computationally infeasible to find two inputs with same hash 2. Preimage-resistant - Cannot derive content from hash 3. Deterministic - Same content always produces same hash 4. Fast - Practical for large objects")
      (p "Specified hash: SHA-256 (32 bytes, 64 hex characters)")
      (code scheme ";; Example content address\n\"e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855\"\n;; This is the SHA-256 of the empty string")))
  (section
    "Storage Architecture"
    (subsection
      "Object Store"
      (code ".cas/\n├── objects/\n│   ├── e3/\n│   │   └── b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855\n│   ├── a7/\n│   │   └── ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a\n│   └── ...\n├── refs/\n│   ├── HEAD\n│   └── tags/\n└── index")
      (p "Sharding: First two hex characters of hash form directory name (256 buckets)."))
    (subsection
      "Object Types"
      (code scheme ";; Blob - raw data\n(cas-blob\n  (hash \"sha256:...\")\n  (size 1024)\n  (data #${...}))\n\n;; Tree - directory structure\n(cas-tree\n  (hash \"sha256:...\")\n  (entries\n    ((\"README.md\" blob \"sha256:abc...\")\n     (\"src\" tree \"sha256:def...\")\n     (\"lib\" tree \"sha256:ghi...\"))))\n\n;; Commit - snapshot with metadata\n(cas-commit\n  (hash \"sha256:...\")\n  (tree \"sha256:...\")\n  (parent \"sha256:...\" | #f)\n  (author \"ddp@eludom.net\")\n  (timestamp 1767700000)\n  (message \"Initial commit\"))"))
    (subsection
      "Merkle Trees"
      (p "Directories are trees of hashes. The root hash commits to all content:")
      (code "                    root: sha256:abc...\n                         /          \\\n              src: sha256:def     lib: sha256:ghi\n               /        \\              |\n        main.scm     test.scm      util.scm\n        sha256:111   sha256:222    sha256:333")
      (p "Changing ANY file changes ALL parent hashes up to root.")))
  (section
    "Operations"
    (subsection
      "Store"
      (code scheme "(define (cas-put content)\n  \"Store content, return hash\"\n  (let* ((hash (sha256 content))\n         (path (hash->path hash)))\n    (unless (file-exists? path)\n      (write-blob path content))\n    hash))")
      (p "Deduplication: If hash already exists, storage is a no-op."))
    (subsection
      "Retrieve"
      (code scheme "(define (cas-get hash)\n  \"Retrieve content by hash, verify integrity\"\n  (let* ((path (hash->path hash))\n         (content (read-blob path)))\n    (unless (equal? hash (sha256 content))\n      (error \"Content integrity failure\" hash))\n    content))")
      (p "Self-verifying: Every retrieval confirms integrity."))
    (subsection
      "Exists"
      (code scheme "(define (cas-exists? hash)\n  \"Check if content exists\"\n  (file-exists? (hash->path hash)))"))
    (subsection
      "Delete"
      (code scheme "(define (cas-gc roots)\n  \"Garbage collect unreachable objects\"\n  (let ((reachable (trace-reachable roots)))\n    (for-each\n      (lambda (hash)\n        (unless (set-member? reachable hash)\n          (delete-file (hash->path hash))))\n      (all-objects))))")
      (p "Note: Deletion requires garbage collection from known roots.")))
  (section
    "Naming Layer"
    (p "Content addresses are not human-friendly. A naming layer maps names to hashes:")
    (subsection
      "References"
      (code scheme ";; Mutable reference to immutable content\n(define (ref-set name hash)\n  (write-file (ref-path name) hash))\n\n(define (ref-get name)\n  (read-file (ref-path name)))\n\n;; Example\n(ref-set \"HEAD\" \"sha256:abc123...\")\n(ref-get \"HEAD\") ; => \"sha256:abc123...\""))
    (subsection
      "Tags"
      (code scheme ";; Immutable named reference\n(define (tag-create name hash #!key message signature)\n  (let ((tag-content\n         `(tag\n           (name ,name)\n           (object ,hash)\n           (message ,message)\n           (signature ,signature))))\n    (cas-put (serialize tag-content))))"))
    (subsection
      "Directory Entries"
      (code scheme ";; Human name -> content hash\n(define library-index\n  '((\"RFC-000\" . \"sha256:e3b0c44...\")\n    (\"RFC-001\" . \"sha256:a7ffc6f...\")\n    (\"RFC-002\" . \"sha256:b94d27b...\")))")))
  (section
    "The Soup: Object Directory"
    (p "Content-addressed storage provides retrieval by hash, but discovery requires an object directory. The Soup (inspired by NewtonOS) provides a unified view of all objects with rich metadata.")
    (subsection
      "Philosophy"
      (blockquote "\"The soup is infinite.\" - Objects swim in a queryable sea of metadata.")
      (p "The Soup inverts the traditional filesystem model:")
      (list
        (item "Filesystem: Navigate hierarchy to find objects")
        (item "Soup: Query attributes to discover objects")))
    (subsection
      "Object Enumeration"
      (code scheme "(define (soup)\n  \"List all objects in the vault with metadata\"\n  (append\n    (soup-releases)      ; Signed releases\n    (soup-archives)      ; Sealed archives\n    (soup-keys)          ; Cryptographic keys\n    (soup-audit-entries) ; Audit trail\n    (soup-commits)))     ; Recent commits"))
    (subsection
      "Rich Metadata"
      (p "Every object carries crypto metadata - the ciphers, hashes, and keys involved:")
      (code scheme ";; Archive object\n(soup-object\n  (name \"1.0.0\")\n  (type archive)\n  (size \"1.2MB\")\n  (crypto (zstd sha256 \"fe378a78...\")))\n\n;; Key object\n(soup-object\n  (name \"vault-signing\")\n  (type key)\n  (size \"64B\")\n  (crypto (ed25519/256 public sign\n           \"sha256:a1b2c3d4...\"    ; fingerprint\n           \"id:ddp@eludom.net\"     ; identity\n           \"2026-01-07\")))         ; creation date\n\n;; Release object\n(soup-object\n  (name \"0.1.0\")\n  (type release)\n  (size \"313B\")\n  (crypto (ed25519 sha512 \"abc123...\")))"))
    (subsection
      "Querying the Soup"
      (code scheme ";; Find all signed objects\n(soup-query type: 'release)\n\n;; Find objects using specific algorithm\n(soup-query crypto: 'ed25519)\n\n;; Find objects by size range\n(soup-query min-size: 1000 max-size: 100000)\n\n;; Find objects by content hash prefix\n(soup-query hash-prefix: \"fe378\")"))
    (subsection
      "Display Format"
      (p "The soup displays as a compact, human-readable listing:")
      (code "$ seal-soup\nvault-signing, 64B, ed25519/256, public, sign, sha256:a1b2c3d4...\n0.1.0, 313B, signed, ed25519, sha512\n1.0.0, 1.2MB, zstd, sha256, fe378a78...\naudit/1, sealed, 2026-01-07T10:30:00Z"))
    (subsection
      "Soup as Index"
      (p "The Soup can be serialized as a content-addressed index:")
      (code scheme "(define (soup-snapshot)\n  \"Create content-addressed snapshot of current soup\"\n  (let* ((entries (soup))\n         (serialized (serialize entries))\n         (hash (cas-put serialized)))\n    (ref-set \"soup/HEAD\" hash)\n    hash))")
      (p "This enables: - Time travel: Load historical soup snapshots - Replication: Sync soup indexes between vaults - Verification: Prove soup state at a point in time")))
  (section
    "Integration with Library of Cyberspace"
    (subsection
      "Vault Integration"
      (p "The Vault (RFC-006) uses content addressing internally via Git:")
      (code scheme ";; Git objects ARE content-addressed\n(define (git-hash-object content)\n  (sha1 (string-append \"blob \" (number->string (blob-length content)) \"\\x00\" content)))")
      (p "CAS extends this with SHA-256 and Library-specific semantics."))
    (subsection
      "Archive Storage"
      (p "Sealed archives (RFC-018) can be stored by content address:")
      (code scheme "(define (archive-to-cas archive-path)\n  (let* ((content (read-blob archive-path))\n         (hash (cas-put content)))\n    (ref-set (string-append \"archives/\" (archive-version archive-path)) hash)\n    hash))"))
    (subsection
      "Replication"
      (p "Content addressing enables efficient replication (RFC-001):")
      (code scheme ";; Only transfer objects receiver doesn't have\n(define (replicate-to remote root-hash)\n  (for-each\n    (lambda (hash)\n      (unless (remote-has? remote hash)\n        (remote-put remote hash (cas-get hash))))\n    (trace-reachable root-hash)))"))
    (subsection
      "SPKI Integration"
      (p "Content hashes can be authorization subjects (RFC-004):")
      (code scheme ";; Grant permission to specific content\n(spki-cert\n  (issuer publisher-key)\n  (subject (hash sha256 \"abc123...\"))\n  (permission read)\n  (validity (not-after \"2027-01-01\")))")))
  (section
    "Chunking for Large Objects"
    (p "Large files are split into chunks for:")
    (p "1. Deduplication at sub-file granularity 2. Parallel transfer 3. Incremental updates")
    (subsection
      "Fixed-Size Chunking"
      (code scheme "(define chunk-size (* 64 1024))  ; 64KB\n\n(define (chunk-fixed data)\n  (let loop ((offset 0) (chunks '()))\n    (if (>= offset (blob-length data))\n        (reverse chunks)\n        (loop (+ offset chunk-size)\n              (cons (blob-copy data offset (min chunk-size (- (blob-length data) offset)))\n                    chunks)))))"))
    (subsection
      "Content-Defined Chunking (Rabin fingerprinting)"
      (code scheme ";; Chunk boundaries determined by content\n;; Survives insertions/deletions better than fixed-size\n(define (chunk-rabin data)\n  (let ((window-size 48)\n        (min-chunk 2048)\n        (max-chunk 65536)\n        (mask #x0fff))  ; Average 4KB chunks\n    ...))"))
    (subsection
      "Chunk Tree"
      (code scheme "(cas-chunked\n  (hash \"sha256:...\")      ; Root hash\n  (size 10485760)          ; 10MB original\n  (chunks\n    (\"sha256:aaa...\" 65536)\n    (\"sha256:bbb...\" 65536)\n    (\"sha256:ccc...\" 32768)\n    ...))")))
  (section
    "Introspection"
    (p "The Library is fully introspective: it stores, addresses, and reasons about itself.")
    (subsection
      "Self-Hosting"
      (p "The system contains its own description:")
      (code scheme ";; The RFCs are in the CAS\n(cas-get (ref-get \"rfc/020\"))  ; => This document\n\n;; The code is in the CAS\n(cas-get (ref-get \"src/vault.scm\"))  ; => Implementation\n\n;; The schema is in the CAS\n(cas-get (ref-get \"schema/soup-object\"))  ; => Soup object definition"))
    (subsection
      "Meta-Objects"
      (p "Objects that describe objects:")
      (code scheme ";; Schema for soup objects (itself a soup object)\n(soup-object\n  (name \"schema/soup-object\")\n  (type schema)\n  (size \"412B\")\n  (crypto (sha256 \"def456...\"))\n  (describes soup-object))\n\n;; The soup can enumerate itself\n(soup-query type: 'schema)  ; => All schemas including this one"))
    (subsection
      "Reflexive Queries"
      (p "The soup answers questions about itself:")
      (code scheme ";; What types exist?\n(soup-types)  ; => (archive release key audit commit schema ...)\n\n;; What crypto algorithms are in use?\n(soup-algorithms)  ; => (sha256 ed25519 zstd age ...)\n\n;; What is the total size of the vault?\n(soup-total-size)  ; => 47.3MB\n\n;; How much deduplication?\n(soup-dedup-ratio)  ; => 0.73 (27% space saved)"))
    (subsection
      "Provenance"
      (p "Every object knows its origin:")
      (code scheme "(soup-object\n  (name \"rfc-020.ps\")\n  (type blob)\n  (size \"89KB\")\n  (crypto (sha256 \"abc123...\"))\n  (provenance\n    (created-by \"ddp@eludom.net\")\n    (created-at 1767700000)\n    (derived-from \"sha256:fff888...\")\n    (tool \"dvips\")))")
      (p "Provenance chains are themselves content-addressed:")
      (code scheme ";; Trace full history\n(define (provenance-chain hash)\n  (let ((obj (soup-get hash)))\n    (if (soup-object-derived-from obj)\n        (cons obj (provenance-chain (soup-object-derived-from obj)))\n        (list obj))))"))
    (subsection
      "Audit of Audits"
      (p "The audit trail audits itself:")
      (code scheme ";; Audit entry for an audit entry\n(audit-entry\n  (id 42)\n  (actor vault-key)\n  (action (audit-append 41))  ; Recorded adding entry 41\n  (timestamp 1767700100))\n\n;; The audit trail is in the soup\n(soup-query type: 'audit)  ; => All audit entries as soup objects"))
    (subsection
      "Bootstrapping"
      (p "The system can describe how to build itself:")
      (code scheme ";; Bootstrap manifest - everything needed to reconstruct\n(bootstrap-manifest\n  (hash \"sha256:bootstrap...\")\n  (contents\n    ((\"src/\" tree \"sha256:src...\")\n     (\"rfcs/\" tree \"sha256:rfcs...\")\n     (\"keys/\" tree \"sha256:keys...\")\n     (\"schema/\" tree \"sha256:schema...\")))\n  (build-instructions\n    \"Load src/boot.scm, call (bootstrap)\"))\n\n;; Verify bootstrap integrity\n(define (verify-bootstrap)\n  (let ((manifest (cas-get (ref-get \"bootstrap\"))))\n    (for-each verify-tree (manifest-contents manifest))))"))
    (subsection
      "The Library Contains Itself"
      (code "╭─────────────────────────────────────────╮\n│            LIBRARY OF CYBERSPACE        │\n│  ╭───────────────────────────────────╮  │\n│  │     Content-Addressed Storage     │  │\n│  │  ╭─────────────────────────────╮  │  │\n│  │  │    RFC-020 (this document)  │  │  │\n│  │  │    describing CAS           │  │  │\n│  │  │    stored in CAS            │  │  │\n│  │  ╰─────────────────────────────╯  │  │\n│  ╰───────────────────────────────────╯  │\n╰─────────────────────────────────────────╯")
      (p "Homoiconic storage: the description is the thing.")))
  (section
    "Tombstones"
    (p "Objects are never truly deleted - they are marked with tombstones.")
    (subsection
      "Soft Deletion"
      (code scheme "(define (cas-tombstone hash #!key reason actor)\n  \"Mark object as deleted without removing it\"\n  (let ((tombstone\n         (tombstone\n           (object ,hash)\n           (deleted-at ,(current-seconds))\n           (deleted-by ,actor)\n           (reason ,reason))))\n    (audit-append action: (tombstone ,hash) motivation: reason)\n    (cas-put (serialize tombstone))))"))
    (subsection
      "Tombstone Properties"
      (code scheme "(soup-object\n  (name \"sha256:deadbeef...\")\n  (type tombstone)\n  (size \"0B\")  ; Logical size is zero\n  (status deleted)\n  (reason \"Superseded by sha256:newversion...\")\n  (recoverable #t))"))
    (subsection
      "Recovery"
      (code scheme "(define (cas-resurrect hash)\n  \"Remove tombstone, restore object visibility\"\n  (let ((tombstone (find-tombstone hash)))\n    (when tombstone\n      (audit-append action: `(resurrect ,hash))\n      (cas-delete (tombstone-hash tombstone)))))"))
    (subsection
      "Garbage Collection with Tombstones"
      (code scheme "(define (cas-gc roots #!key preserve-tombstones)\n  \"GC respects tombstones by default\"\n  (let ((reachable (trace-reachable roots))\n        (tombstoned (all-tombstoned-hashes)))\n    (for-each\n      (lambda (hash)\n        (unless (or (set-member? reachable hash)\n                    (and preserve-tombstones\n                         (set-member? tombstoned hash)))\n          (delete-file (hash->path hash))))\n      (all-objects))))")))
  (section
    "Pinning"
    (p "Pinned objects are protected from garbage collection.")
    (subsection
      "Pin Operations"
      (code scheme "(define (cas-pin hash #!key recursive reason)\n  \"Pin object (and optionally its references)\"\n  (let ((pin `(pin\n               (object ,hash)\n               (pinned-at ,(current-seconds))\n               (recursive ,recursive)\n               (reason ,reason))))\n    (write-file (pin-path hash) (serialize pin))\n    (when recursive\n      (for-each (lambda (ref) (cas-pin ref recursive: #t))\n                (object-references hash)))))\n\n(define (cas-unpin hash)\n  \"Remove pin, allow GC\"\n  (delete-file (pin-path hash)))\n\n(define (cas-pinned? hash)\n  \"Check if object is pinned\"\n  (file-exists? (pin-path hash)))"))
    (subsection
      "Pin Manifest"
      (code scheme ";; All pins as soup objects\n(soup-query type: 'pin)\n\n;; Pin statistics\n(soup-pin-count)      ; => 142 objects pinned\n(soup-pinned-size)    ; => 23.4MB"))
    (subsection
      "Root Pins"
      (p "Certain objects are implicitly pinned:")
      (code scheme "(define implicit-roots\n  '(\"HEAD\"           ; Current commit\n    \"refs/tags/\"    ; All tags\n    \"bootstrap\"      ; System bootstrap\n    \"schema/\"))     ; All schemas")))
  (section
    "Bloom Filters"
    (p "Compact probabilistic set membership for efficient replication.")
    (subsection
      "Multi-Level Existence Check"
      (p "For the distributed soup, existence checks dominate replication overhead. A tiered approach minimizes latency:")
      (code "┌─────────────────────────────────────────────────────────┐\n│ L1: Hot Set Cache (1000 items, O(1), microseconds)     │\n├─────────────────────────────────────────────────────────┤\n│ L2: Blocked Bloom Filter (100K items, O(k), cache-     │\n│     friendly memory layout)                             │\n├─────────────────────────────────────────────────────────┤\n│ L3: Quotient Filter (1M items, supports deletion)      │\n├─────────────────────────────────────────────────────────┤\n│ L4: Disk/Network (authoritative, milliseconds)         │\n└─────────────────────────────────────────────────────────┘"))
    (subsection
      "Blocked Bloom Filters"
      (p "Cache-line aligned blocks for 10x faster lookups:")
      (code scheme ";; Blocked Bloom: each block fits in CPU cache line (64 bytes = 512 bits)\n(define block-bits 512)\n(define cache-line 64)\n\n(define (make-blocked-bloom capacity error-rate)\n  \"Cache-friendly blocked Bloom filter\"\n  (let ((bits (bloom-optimal-bits capacity error-rate))\n         (num-blocks (ceiling (/ bits block-bits)))\n         (hashes (bloom-optimal-hashes capacity bits)))\n    (blocked-bloom\n      (blocks (make-vector num-blocks (make-u8vector cache-line 0)))\n      (hash-count hashes)\n      (block-selector (lambda (hash) (modulo (hash-part-1 hash) num-blocks))))))\n\n(define (blocked-bloom-add! filter hash)\n  \"Add to block - all bits within same cache line\"\n  (let ((block-idx (block-select filter hash))\n         (block (vector-ref (bloom-blocks filter) block-idx)))\n    (for-each\n      (lambda (i)\n        (let ((bit-idx (modulo (bloom-hash filter hash i) block-bits)))\n          (u8vector-bit-set! block bit-idx 1)))\n      (iota (bloom-hash-count filter)))))\n\n(define (blocked-bloom-contains? filter hash)\n  \"Check within single cache line - no cache misses\"\n  (let ((block-idx (block-select filter hash))\n         (block (vector-ref (bloom-blocks filter) block-idx)))\n    (every\n      (lambda (i)\n        (let ((bit-idx (modulo (bloom-hash filter hash i) block-bits*)))\n          (= 1 (u8vector-bit-ref block bit-idx))))\n      (iota (bloom-hash-count filter)))))"))
    (subsection
      "Counting Bloom Filters"
      (p "For the soup, objects can be tombstoned (soft-deleted). Counting filters support removal:")
      (code scheme ";; Counting Bloom: 4-bit counters instead of single bits\n(define (make-counting-bloom capacity error-rate)\n  \"Counting Bloom filter supporting deletions\"\n  (let* ((slots (bloom-optimal-bits capacity error-rate))\n         (nibbles (make-u8vector (ceiling (/ slots 2)) 0))\n         (hashes (bloom-optimal-hashes capacity slots)))\n    (counting-bloom nibbles hashes slots)))\n\n(define (counting-bloom-add! filter hash)\n  \"Increment counters (saturate at 15)\"\n  (for-each\n    (lambda (i)\n      (let ((slot (bloom-slot filter hash i)))\n        (nibble-increment! (bloom-nibbles filter) slot)))\n    (iota (bloom-hash-count filter))))\n\n(define (counting-bloom-remove! filter hash)\n  \"Decrement counters (only if present)\"\n  (when (counting-bloom-contains? filter hash)\n    (for-each\n      (lambda (i)\n        (let ((slot (bloom-slot filter hash i)))\n          (nibble-decrement! (bloom-nibbles filter) slot)))\n      (iota (bloom-hash-count filter)))))\n\n;; Integration with tombstones\n(define (cas-tombstone/bloom hash reason)\n  \"Tombstone with Bloom filter update\"\n  (counting-bloom-remove! existence-filter hash)\n  (cas-tombstone hash reason: reason))"))
    (subsection
      "Quotient Filters"
      (p "Better space efficiency than Bloom, supports deletion, and can be resized:")
      (code scheme ";; Quotient filter: fingerprint stored in quotient/remainder form\n(define (make-quotient-filter capacity)\n  \"Space-efficient filter with deletion support\"\n  (let* ((slots (next-power-of-2 capacity))\n         (q-bits (integer-log2 slots))\n         (r-bits (- 64 q-bits)))  ; 64-bit fingerprints\n    (quotient-filter\n      (table (make-vector slots #f))\n      (q-bits q-bits)\n      (r-bits r-bits)\n      (count 0))))\n\n(define (qf-fingerprint hash q-bits r-bits)\n  \"Split hash into quotient and remainder\"\n  (let ((fp (hash->u64 hash)))\n    (values (arithmetic-shift fp (- r-bits))  ; quotient\n            (bitwise-and fp (- (arithmetic-shift 1 r-bits) 1)))))  ; remainder\n\n(define (qf-insert! qf hash)\n  \"Insert with Robin Hood linear probing\"\n  (let-values (((q r) (qf-fingerprint hash (qf-q-bits qf) (qf-r-bits qf))))\n    (qf-insert-slot! qf q r)))\n\n(define (qf-delete! qf hash)\n  \"Delete fingerprint\"\n  (let-values (((q r) (qf-fingerprint hash (qf-q-bits qf) (qf-r-bits qf))))\n    (qf-delete-slot! qf q r)))"))
    (subsection
      "Replication Protocol"
      (code scheme ";; Sender: \"Here's what I have\" (compressed Bloom)\n(define (bloom-inventory)\n  (let ((filter (make-blocked-bloom 100000 0.01)))\n    (for-each (lambda (hash) (blocked-bloom-add! filter hash))\n              (all-object-hashes))\n    filter))\n\n;; Receiver: \"Send me what I'm missing\"\n(define (bloom-diff local-filter remote-filter)\n  (filter (lambda (hash)\n            (and (blocked-bloom-contains? remote-filter hash)\n                 (not (cas-exists? hash))))\n          (all-object-hashes)))\n\n;; Exchange is O(bloom-size) not O(object-count)\n;; Blocked Bloom: 10-100x faster due to cache locality"))
    (subsection
      "Hierarchical Existence Check"
      (code scheme "(define (cas-exists?/fast hash)\n  \"Tiered existence check - fast path for common case\"\n  (or (lru-get hot-set hash)              ; L1: O(1) in-memory\n      (and (blocked-bloom-contains? l2-bloom hash)  ; L2: O(k) cache-friendly\n           (or (qf-contains? l3-qf hash)  ; L3: O(1) amortized\n               (cas-exists? hash)))))      ; L4: authoritative\n\n;; 99% of checks hit L1/L2, avoiding disk/network entirely"))
    (subsection
      "Soup Integration"
      (code scheme ";; Bloom filter itself is a soup object\n(soup-object\n  (name \"bloom/2026-01-09\")\n  (type bloom-filter)\n  (variant blocked)           ; blocked, counting, or quotient\n  (size \"12KB\")\n  (crypto (sha256 \"bloom-hash...\"))\n  (capacity 100000)\n  (error-rate 0.01)\n  (population 47230)\n  (load-factor 0.47))")))
  (section
    "Content Types"
    (p "Typed objects with schema validation.")
    (subsection
      "Type Registry"
      (code scheme "(define content-types\n  '((blob        . \"application/octet-stream\")\n    (text        . \"text/plain\")\n    (markdown    . \"text/markdown\")\n    (scheme      . \"text/x-scheme\")\n    (sexp        . \"application/x-sexp\")\n    (json        . \"application/json\")\n    (pdf         . \"application/pdf\")\n    (archive     . \"application/x-sealed-archive\")\n    (key         . \"application/x-spki-key\")\n    (certificate . \"application/x-spki-cert\")))"))
    (subsection
      "Typed Storage"
      (code scheme "(define (cas-put/typed content type #!key schema)\n  \"Store with type metadata\"\n  (let* ((hash (sha256 content))\n         (meta `(typed-object\n                 (hash ,hash)\n                 (type ,type)\n                 (size ,(blob-length content))\n                 (schema ,schema))))\n    (cas-put content)\n    (cas-put (serialize meta))\n    hash))"))
    (subsection
      "Schema Validation"
      (code scheme "(define (cas-validate hash)\n  \"Validate object against its schema\"\n  (let* ((meta (cas-get-meta hash))\n         (schema-hash (typed-object-schema meta))\n         (schema (cas-get schema-hash))\n         (content (cas-get hash)))\n    (schema-validate schema content)))\n\n;; Schema is itself content-addressed\n(soup-object\n  (name \"schema/soup-object\")\n  (type schema)\n  (validates soup-object)\n  (crypto (sha256 \"schema-hash...\")))"))
    (subsection
      "MIME Detection"
      (code scheme "(define (cas-detect-type content)\n  \"Detect content type from magic bytes\"\n  (cond\n    ((pdf-magic? content) 'pdf)\n    ((gzip-magic? content) 'archive)\n    ((utf8-text? content)\n     (cond\n       ((sexp-syntax? content) 'sexp)\n       ((markdown-syntax? content) 'markdown)\n       (else 'text)))\n    (else 'blob)))")))
  (section
    "Object Capabilities"
    (p "Content addresses as capabilities: if you know the hash, you can retrieve it.")
    (subsection
      "Hash as Capability"
      (code scheme ";; Knowledge of hash grants read access\n(define (cas-get-if-known hash)\n  \"Capability-based retrieval\"\n  (if (valid-hash? hash)\n      (cas-get hash)\n      (error \"Invalid capability\")))\n\n;; Hashes are unguessable (256-bit entropy)\n;; Sharing a hash = sharing read access"))
    (subsection
      "Capability Attenuation"
      (code scheme ";; SPKI certificate granting access to specific content\n(spki-cert\n  (issuer vault-key)\n  (subject reader-key)\n  (permission (read (hash sha256 \"specific-content...\")))\n  (validity (not-after \"2027-01-01\")))\n\n;; Grant access to a subtree\n(spki-cert\n  (issuer vault-key)\n  (subject reader-key)\n  (permission (read (tree sha256 \"subtree-root...\")))\n  (propagate #t))  ; Access to all referenced objects"))
    (subsection
      "Sealed Capabilities"
      (code scheme ";; Encrypted capability - only holder of key can use\n(define (seal-capability hash recipient-key)\n  (let ((cap `(capability\n               (object ,hash)\n               (granted-at ,(current-seconds)))))\n    (age-encrypt (serialize cap) recipient-key)))\n\n;; Recipient decrypts to obtain hash\n(define (unseal-capability sealed-cap identity)\n  (let ((cap (deserialize (age-decrypt sealed-cap identity))))\n    (capability-object cap)))"))
    (subsection
      "Capability Revocation"
      (code scheme ";; Revocation via tombstone\n(define (revoke-capability hash)\n  (cas-tombstone hash reason: \"Capability revoked\"))\n\n;; Or via SPKI CRL\n(spki-crl\n  (issuer vault-key)\n  (revoked\n    ((hash sha256 \"revoked-content...\")\n     (reason \"Superseded\")\n     (revoked-at 1767700000))))")))
  (section
    "Hash Migration"
    (p "When cryptographic algorithms weaken, the system must migrate.")
    (subsection
      "Multihash"
      (code scheme ";; Self-describing hash format\n(define (multihash algo data)\n  (let ((hash (case algo\n                ((sha256) (sha256 data))\n                ((sha384) (sha384 data))\n                ((sha512) (sha512 data))\n                ((blake3) (blake3 data)))))\n    (list algo (blob-length hash) hash)))\n\n;; Parse multihash\n(define (multihash-algorithm mh) (car mh))\n(define (multihash-digest mh) (caddr mh))"))
    (subsection
      "Dual-Hash Period"
      (code scheme ";; During migration, store under both hashes\n(define (cas-put/migrate content old-algo new-algo)\n  (let ((old-hash (hash-with old-algo content))\n        (new-hash (hash-with new-algo content)))\n    (cas-put-raw old-hash content)\n    (cas-put-raw new-hash content)\n    ;; Link old to new\n    (ref-set (string-append \"migrate/\" old-hash) new-hash)\n    new-hash))\n\n;; Lookup follows migration links\n(define (cas-get/migrate hash)\n  (let ((migrated (ref-get (string-append \"migrate/\" hash))))\n    (cas-get (or migrated hash))))"))
    (subsection
      "Migration Manifest"
      (code scheme "(migration-manifest\n  (from-algorithm sha256)\n  (to-algorithm sha384)\n  (started-at 1767700000)\n  (status in-progress)\n  (migrated 4723)\n  (remaining 1892)\n  (mappings\n    ((\"sha256:abc...\" . \"sha384:def...\")\n     (\"sha256:123...\" . \"sha384:456...\")\n     ...)))"))
    (subsection
      "Verification During Migration"
      (code scheme "(define (verify-migration hash)\n  \"Verify object under both old and new hash\"\n  (let* ((content (cas-get hash))\n         (old-hash (sha256 content))\n         (new-hash (sha384 content)))\n    (and (or (equal? hash old-hash)\n             (equal? hash new-hash))\n         (equal? (ref-get (string-append \"migrate/\" old-hash))\n                 new-hash))))")))
  (section
    "Comparison with Related Systems"
    (table
      (header "System " "Hash " "Chunking " "Naming ")
      (row "Git " "SHA-1 " "Pack files " "refs/branches ")
      (row "IPFS " "SHA-256/multihash " "Rabin " "IPNS, DNSLink ")
      (row "Perkeep " "SHA-224 " "Rolling hash " "Permanodes ")
      (row "Library CAS " "SHA-256 " "Configurable " "Vault refs ")))
  (section
    "Security Considerations"
    (subsection
      "Hash Collision Attacks"
      (p "SHA-256 provides 128-bit collision resistance. No practical attacks known.")
      (p "If SHA-256 is ever broken:")
      (code scheme ";; Multihash for algorithm agility\n(define (multihash algo data)\n  (case algo\n    ((sha256) (cons 'sha256 (sha256 data)))\n    ((sha384) (cons 'sha384 (sha384 data)))\n    ((blake3) (cons 'blake3 (blake3 data)))))"))
    (subsection
      "Length Extension Attacks"
      (p "SHA-256 is vulnerable to length extension. For authentication, use HMAC:")
      (code scheme "(define (cas-mac key hash)\n  (hmac-sha256 key hash))"))
    (subsection
      "Timing Attacks"
      (p "Hash comparison MUST be constant-time:")
      (code scheme "(define (hash-equal? a b)\n  (let ((result 0))\n    (do ((i 0 (+ i 1)))\n        ((= i 32) (zero? result))\n      (set! result (bitwise-ior result\n                    (bitwise-xor (blob-ref a i) (blob-ref b i)))))))")))
  (section
    "Performance Considerations"
    (subsection
      "Caching"
      (code scheme ";; LRU cache for hot objects\n(define cas-cache (make-lru-cache 1000))\n\n(define (cas-get/cached hash)\n  (or (lru-get cas-cache hash)\n      (let ((content (cas-get hash)))\n        (lru-put! cas-cache hash content)\n        content)))"))
    (subsection
      "Parallel Hashing"
      (p "Large files benefit from parallel hashing of chunks."))
    (subsection
      "SSD Optimization"
      (p "Random access pattern. Use write-ahead log for durability:")
      (code scheme "(define (cas-put/durable content)\n  (let ((hash (sha256 content)))\n    (wal-append hash content)\n    (write-blob (hash->path hash) content)\n    (wal-commit hash)\n    hash))")))
  (section
    "Implementation Notes"
    (subsection
      "Dependencies"
      (table
        (header "Component " "Library ")
        (row "SHA-256 " "message-digest, sha2 ")
        (row "Blob I/O " "CHICKEN I/O ")
        (row "Chunking " "Custom ")))
    (subsection
      "Error Handling"
      (code scheme "(define-condition-type &cas-error &error\n  cas-error?\n  (hash cas-error-hash))\n\n(define-condition-type &cas-not-found &cas-error\n  cas-not-found?)\n\n(define-condition-type &cas-corrupt &cas-error\n  cas-corrupt?)")))
  (section
    "References"
    (p "1. Merkle, R. (1987), \"A Digital Signature Based on a Conventional Encryption Function\" 2. Git Internals - Git Objects 3. IPFS Content Addressing 4. Putze, Sanders, Singler (2007), \"Cache-, Hash-, and Space-Efficient Bloom Filters\" 5. Bender et al. (2012), \"Don't Thrash: How to Cache Your Hash on Flash\" 6. RFC-006: Vault System Architecture 7. RFC-018: Sealed Archive Format"))
  (section
    "Changelog"
    (list
      (item "2026-01-09")
      (item "Advanced probabilistic data structures: blocked Bloom filters, counting Bloom filters, quotient filters, hierarchical existence checking - 2026-01-07")
      (item "Initial draft"))))

