;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 42)
  (title "Wormholes")
  (section
    "Abstract"
    (p "This Memo specifies wormholes—FUSE-based bidirectional portals between the macOS filesystem and the Library of Cyberspace vault. Wormholes preserve full metadata including extended attributes, Finder tags, and ACLs. All operations are auditable (Memo-003) and rate-limited (Memo-032).[^h1]")
    (p "[^h1]: Historical: FUSE originated in Linux 2.6 (2005), inspired by earlier userspace filesystem work in Plan 9 and Hurd. macFUSE (originally MacFUSE) brought it to macOS in 2007. The abstraction outlived Apple's hostility."))
  (section
    "Motivation"
    (p "Users need seamless integration between their existing filesystem and the vault. Manual import/export creates friction and risks metadata loss.")
    (p "A wormhole provides:")
    (list
      (item "Transparency - Finder, cp, rsync work unchanged")
      (item "Bidirectionality - No separate sync step; it IS the filesystem")
      (item "Metadata preservation - Full macOS attributes captured automatically")
      (item "Content addressing - Deduplication and integrity built-in")
      (item "Security - First-class Simple Public Key Infrastructure (SPKI) object with audit and rate-limit"))
    (p "The filesystem abstraction is the right boundary—everything above it (apps, shell, Finder) works without modification.[^d1]")
    (p "[^d1]: Design: FUSE inverts the usual model. Instead of teaching applications about vaults, we teach the vault to speak filesystem. Unix got this right: everything is a file."))
  (section
    "Wormhole as Security Object"
    (p "A wormhole is a first-class security object in cyberspace, subject to:[^d2]")
    (list
      (item "SPKI Authorization (Memo-004) — Opening requires valid certificate")
      (item "Capability Delegation (Memo-021) — Wormhole access can be delegated")
      (item "Audit Trail (Memo-003) — All operations logged")
      (item "Rate Limiting (Memo-032) — Configurable ops/minute")
      (item "Sandboxing (Memo-023) — Agents access wormholes through capabilities"))
    (p "Wormholes bridge two security domains—the filesystem and the vault—making them inherently privileged operations. Treating wormholes as first-class security objects ensures that filesystem access remains under cryptographic control, not just ambient POSIX permissions.")
    (p "[^d2]: Design: Wormholes are attack surface. Unrestricted filesystem access defeats vault security. Every wormhole must be explicitly authorized, continuously audited, and rate-limited against abuse.")
    (subsection
      "Wormhole Certificate"
      (code scheme "(define (wormhole-cert issuer fs-path vault-path permissions)\n  \"Create SPKI certificate authorizing wormhole\"\n  (create-cert\n   issuer\n   (wormhole-principal fs-path vault-path)\n   `(tag (wormhole\n          (fs-path ,fs-path)\n          (vault-path ,vault-path)\n          (permissions ,@permissions)   ; read, write, delete\n          (rate-limit 1000)             ; ops/minute\n          (expires ,(+ (current-seconds) 86400))))))"))
    (subsection
      "Capability Model"
      (p "Wormholes support fine-grained capabilities:[^d3]")
      (p "[^d3]: Design: Rich capabilities enable principle of least privilege. A backup agent needs read-only; a sync agent needs read-write but not delete. Capabilities compose—grant exactly what's needed.")
      (p "Table 0: Wormhole Capabilities")
      (table
        (header "Capability " "Allows ")
        (row "Data Access ")
        (row "read " "Read file contents ")
        (row "write " "Write/modify file contents ")
        (row "create " "Create new files ")
        (row "delete " "Remove files ")
        (row "rename " "Rename/move files ")
        (row "Metadata ")
        (row "stat " "Read POSIX attributes ")
        (row "chmod " "Modify permissions ")
        (row "chown " "Change ownership ")
        (row "xattr-read " "Read extended attributes ")
        (row "xattr-write " "Modify extended attributes ")
        (row "acl-read " "Read ACLs ")
        (row "acl-write " "Modify ACLs ")
        (row "Directory ")
        (row "readdir " "List directory contents ")
        (row "mkdir " "Create directories ")
        (row "rmdir " "Remove directories ")
        (row "Control ")
        (row "admin " "Configure wormhole ")
        (row "delegate " "Delegate capabilities to others ")
        (row "audit-read " "Read wormhole audit log ")
        (row "rate-limit " "Modify rate limits ")))
    (subsection
      "Capability Composition"
      (code scheme ";; Common capability sets (long form for readability)\n(define capability:read-only\n  '(read stat readdir xattr-read acl-read))\n\n(define capability:read-write\n  '(read write create stat chmod readdir mkdir xattr-read xattr-write))\n\n(define capability:full\n  '(read write create delete rename\n    stat chmod chown\n    xattr-read xattr-write acl-read acl-write\n    readdir mkdir rmdir admin delegate audit-read rate-limit))\n\n(define capability:backup\n  '(read stat readdir xattr-read acl-read))\n\n(define capability:synchronize\n  '(read write create delete rename\n    stat chmod readdir mkdir rmdir\n    xattr-read xattr-write))"))
    (subsection
      "Capability Attenuation"
      (p "Capabilities can only be reduced, never amplified:[^r1]")
      (p "[^r1]: Research: Capability attenuation is fundamental to the object-capability model. See Miller, \"Robust Composition\" (2006). You cannot grant more authority than you possess.")
      (code scheme "(define (wormhole-delegate wormhole new-caps recipient)\n  \"Delegate subset of wormhole capabilities\"\n  (let ((my-caps (wormhole-capabilities wormhole)))\n    (unless (subset? new-caps my-caps)\n      (error 'capability-amplification\n             \"Cannot delegate capabilities you don't have\"))\n    (wormhole-cert\n     (wormhole-issuer wormhole)\n     (wormhole-fs-path wormhole)\n     (wormhole-vault-path wormhole)\n     new-caps\n     recipient: recipient)))"))
    (subsection
      "Opening a Wormhole"
      (code scheme "(define (wormhole-open fs-path #!key (vault-path \"/\")\n                                     (capabilities capability:read-write)\n                                     (rate-limit 1000)\n                                     (locked #f)\n                                     (auth-required '())\n                                     (certificate #f))\n  \"Open wormhole - requires valid certificate\"\n  (unless certificate\n    (error 'unauthorized \"Wormhole requires SPKI certificate\"))\n  (unless (verify-wormhole-cert certificate fs-path vault-path)\n    (error 'unauthorized \"Invalid wormhole certificate\"))\n  ;; Audit the open\n  (wormhole-audit 'wormhole-open fs-path\n                  `((vault ,vault-path)\n                    (capabilities ,(length capabilities))))\n  ;; Proceed with FUSE mount\n  ...)"))
    (subsection
      "Usage Examples"
      (code scheme ";; Basic read-write wormhole\n(wormhole-open \"~/Cyberspace\")\n\n;; Read-only wormhole for browsing\n(wormhole-open \"~/Archive\" capabilities: capability:read-only)\n\n;; Sync wormhole with rate limiting\n(wormhole-open \"~/Sync\"\n  capabilities: capability:synchronize\n  rate-limit: 500)\n\n;; Locked wormhole requiring unlock for sensitive operations\n(wormhole-open \"~/Secure\"\n  capabilities: capability:full\n  locked: #t\n  auth-required: '(delete admin))")))
  (section
    "Architecture"
    (subsection
      "Mount Topology"
      (code "~/Cyberspace/                    ← FUSE mount point\n├── documents/\n│   ├── paper.pdf               ← Virtual file (content in vault)\n│   └── notes.txt\n├── projects/\n│   └── cyberspace/\n│       └── ...\n└── .vault/                      ← Hidden, actual storage\n    ├── objects/                 ← Content-addressed blobs\n    │   ├── sha256:abc123...\n    │   └── sha256:def456...\n    ├── manifests/               ← Directory → file mappings\n    └── metadata/                ← Per-file metadata store"))
    (subsection
      "Component Stack"
      (code "┌─────────────────────────────────────┐\n│         Applications                │\n│    (Finder, cp, rsync, etc.)        │\n├─────────────────────────────────────┤\n│         VFS (kernel)                │\n├─────────────────────────────────────┤\n│      FUSE-T / macFUSE               │\n├─────────────────────────────────────┤\n│    cyberspace-fuse daemon           │  ← Our code\n├─────────────────────────────────────┤\n│         Vault layer                 │\n│   (content-address, metadata)       │\n└─────────────────────────────────────┘")))
  (section
    "Metadata Preservation"
    (subsection
      "macOS Metadata Captured"
      (p "Table 1: Preserved Metadata")
      (table
        (header "Category " "Attributes " "Capture Method ")
        (row "POSIX " "mode, uid, gid, size " "stat() ")
        (row "Timestamps " "mtime, atime, ctime, birthtime " "stat() ")
        (row "Extended attrs " "Finder info, tags, quarantine " "listxattr(), getxattr() ")
        (row "Spotlight " "kMDItem* metadata " "mdls / MDItem API ")
        (row "ACLs " "Access control lists " "aclgetfile() ")
        (row "Flags " "hidden, locked, immutable " "chflags() / stat() ")
        (row "Resource fork " "Legacy resource data " "xattr com.apple.ResourceFork ")))
    (subsection
      "Internal Representation"
      (code scheme "(define-record-type <vault-file>\n  (make-vault-file path content-hash metadata)\n  vault-file?\n  (path vault-file-path)\n  (content-hash vault-file-hash)\n  (metadata vault-file-metadata))\n\n(define (capture-metadata path)\n  \"Capture all macOS metadata for a file\"\n  `((posix\n     (mode ,(file-mode path))\n     (uid ,(file-uid path))\n     (gid ,(file-gid path))\n     (size ,(file-size path))\n     (mtime ,(file-mtime path))\n     (atime ,(file-atime path))\n     (ctime ,(file-ctime path))\n     (birthtime ,(file-birthtime path)))\n    (xattr ,(capture-xattrs path))\n    (flags ,(capture-flags path))\n    (acl ,(capture-acl path))))"))
    (subsection
      "Restoration"
      (code scheme "(define (restore-metadata path metadata)\n  \"Restore all metadata to a file\"\n  (let ((posix (alist-ref 'posix metadata))\n        (xattr (alist-ref 'xattr metadata))\n        (flags (alist-ref 'flags metadata))\n        (acl (alist-ref 'acl metadata)))\n    (restore-posix path posix)\n    (restore-xattrs path xattr)\n    (restore-flags path flags)\n    (restore-acl path acl)))")))
  (section
    "FUSE Operations"
    (subsection
      "Required Operations"
      (p "Table 2: FUSE Operations")
      (table
        (header "Operation " "Purpose " "Vault Action ")
        (row "getattr " "stat() " "Return stored metadata ")
        (row "readdir " "List directory " "Read manifest ")
        (row "open " "Open file " "Validate hash exists ")
        (row "read " "Read content " "Fetch by content hash ")
        (row "write " "Write content " "Content-address, update manifest ")
        (row "create " "Create file " "Allocate manifest entry ")
        (row "unlink " "Delete file " "Remove from manifest (GC later) ")
        (row "mkdir " "Create directory " "Create manifest node ")
        (row "rmdir " "Remove directory " "Remove manifest node ")
        (row "rename " "Move/rename " "Update manifest path ")
        (row "setxattr " "Set extended attr " "Store in metadata ")
        (row "getxattr " "Get extended attr " "Retrieve from metadata ")
        (row "listxattr " "List extended attrs " "Enumerate metadata ")))
    (subsection
      "Implementation Sketch"
      (code scheme "(define (fuse-getattr path)\n  \"Return file attributes from vault metadata\"\n  (let ((entry (manifest-lookup path)))\n    (if entry\n        (let ((meta (vault-file-metadata entry)))\n          (make-stat\n           (alist-ref 'mode (alist-ref 'posix meta))\n           (alist-ref 'size (alist-ref 'posix meta))\n           (alist-ref 'mtime (alist-ref 'posix meta))\n           ...))\n        -ENOENT)))\n\n(define (fuse-read path size offset)\n  \"Read file content from vault\"\n  (let ((entry (manifest-lookup path))\n         (hash (vault-file-hash entry))\n         (content (vault-fetch hash)))\n    (subbytes content offset (+ offset size))))\n\n(define (fuse-write path data offset)\n  \"Write to file, content-address the result\"\n  (let ((entry (manifest-lookup path))\n         (current (vault-fetch (vault-file-hash entry)))\n         (updated (bytes-splice current offset data))\n         (new-hash (content-address updated)))\n    (manifest-update! path new-hash)\n    (string-length data)))\n\n(define (fuse-setxattr path name value)\n  \"Store extended attribute in vault metadata\"\n  (let ((entry (manifest-lookup path)))\n    (metadata-set-xattr! entry name value)\n    0))")))
  (section
    "Content Addressing"
    (p "Files are stored by content hash (Memo-020):")
    (code scheme "(define (content-address data)\n  \"Store data, return hash\"\n  (let* ((hash (sha256 data))\n         (path (vault-object-path hash)))\n    (unless (file-exists? path)\n      (write-blob path data))\n    hash))\n\n(define (vault-fetch hash)\n  \"Retrieve data by hash\"\n  (read-blob (vault-object-path hash)))")
    (p "Benefits: - Identical files stored once (deduplication) - Integrity verification on every read - Immutable objects enable safe caching"))
  (section
    "Synchronization"
    (subsection
      "Change Detection"
      (p "The FUSE layer captures all writes in real-time. No separate sync needed for local changes.")
      (p "For multi-device sync, the manifest includes version vectors (Memo-012):")
      (code scheme "(define (manifest-entry path hash metadata)\n  `(entry\n    (path ,path)\n    (hash ,hash)\n    (metadata ,metadata)\n    (version-vector ,local-node ,lamport-clock)))"))
    (subsection
      "Conflict Resolution"
      (p "When merging manifests from different devices (Memo-016 lazy clustering):")
      (list
        (item "Same hash - No conflict (identical content)")
        (item "Different hash, one newer - Take newer")
        (item "Different hash, concurrent - Conflict, apply lazy-resolve"))
      (p "Content-addressing eliminates most conflicts at the object level; the manifest's version vectors resolve the remainder. Lazy clustering defers conflicts to user decision rather than attempting automatic resolution that may lose work.")
      (code scheme "(define (merge-manifests local remote)\n  (for-each\n   (lambda (path)\n     (let ((l (manifest-lookup local path))\n           (r (manifest-lookup remote path)))\n       (cond\n        ((not l) (manifest-add! local r))\n        ((not r) 'keep-local)\n        ((equal? (vault-file-hash l) (vault-file-hash r)) 'identical)\n        ((version-newer? r l) (manifest-update! local r))\n        ((version-newer? l r) 'keep-local)\n        (else (queue-conflict! path l r)))))\n   (union (manifest-paths local) (manifest-paths remote))))")))
  (section
    "Mount Commands"
    (subsection
      "REPL Interface"
      (code scheme "(define (vault-mount point)\n  \"Mount vault at filesystem path\"\n  (fuse-main point\n    `((getattr . ,fuse-getattr)\n      (readdir . ,fuse-readdir)\n      (open . ,fuse-open)\n      (read . ,fuse-read)\n      (write . ,fuse-write)\n      (create . ,fuse-create)\n      (unlink . ,fuse-unlink)\n      (mkdir . ,fuse-mkdir)\n      (rmdir . ,fuse-rmdir)\n      (rename . ,fuse-rename)\n      (setxattr . ,fuse-setxattr)\n      (getxattr . ,fuse-getxattr)\n      (listxattr . ,fuse-listxattr))))\n\n(define (vault-unmount point)\n  \"Unmount vault filesystem\"\n  (fuse-unmount point))"))
    (subsection
      "Command Line"
      (code bash "# Mount\ncyberspace mount ~/Cyberspace\n\n# Unmount\ncyberspace unmount ~/Cyberspace\n\n# Or via REPL\n$ ./repl\n> (vault-mount \"~/Cyberspace\")\nMounted vault at /Users/ddp/Cyberspace")))
  (section
    "macOS Integration"
    (subsection
      "FUSE-T vs macFUSE"
      (p "Table 3: FUSE Implementation Options")
      (table
        (header "Feature " "macFUSE " "FUSE-T ")
        (row "Kernel extension " "Yes (deprecated) " "No ")
        (row "System extension " "Optional " "Uses NFS ")
        (row "SIP compatible " "Requires disable " "Yes ")
        (row "Performance " "Better " "Adequate ")
        (row "Maintenance " "Active " "Active "))
      (p "FUSE-T recommended for new installations—no kernel extension required.[^i1]")
      (p "[^i1]: Implementation: FUSE-T implements FUSE API over NFS loopback. Slightly higher latency but avoids Apple's kernel extension hostility."))
    (subsection
      "Installation"
      (code bash "# FUSE-T (recommended)\nbrew install fuse-t\n\n# Or macFUSE (if kernel ext acceptable)\nbrew install macfuse"))
    (subsection
      "Finder Integration"
      (p "The mount appears as a regular volume in Finder. Optional .VolumeIcon.icns for custom icon.")
      (p "Spotlight indexing can be enabled by implementing getxattr for com.apple.FinderInfo and related Spotlight attributes.")))
  (section
    "Information Flow Model"
    (p "Wormholes bridge two security domains—the macOS filesystem and the vault. This section makes the information flow semantics explicit.[^s1]")
    (p "[^s1]: Security: Classic mandatory access control (Bell-LaPadula, Biba) uses security labels and lattice-based flow rules. We choose a simpler model: capability attenuation at the boundary, no lattice, no mandatory labels.")
    (subsection
      "Vault-Authoritative"
      (p "The vault is the source of truth. The filesystem mount is a capability-constrained view of vault contents, not a peer. Writes are ingested into the vault's content-addressed store; reads retrieve content by hash. The filesystem namespace is a manifest overlay. Unmounted, the projection vanishes; the vault remains."))
    (subsection
      "Bidirectional by Default"
      (p "Unless capabilities restrict it, data flows both ways through the wormhole. A read-only capability creates a one-way flow (vault→filesystem); a write-only capability creates the reverse (filesystem→vault, the dropbox pattern). The default read+write permits bidirectional flow."))
    (subsection
      "No Implicit Labels"
      (p "Unlike VMS security classifications, vault objects carry no mandatory security labels. Flow control is purely through capability attenuation at the wormhole boundary.[^s2]")
      (p "[^s2]: Security: Mandatory labels require a trusted labeling authority and policy engine. We avoid this complexity. The tradeoff: no automatic \"top secret can't flow to unclassified\" enforcement. If an application requires labeled objects with mandatory flow rules, it must implement them at a layer above the wormhole.")
      (p "The deeper rationale is human factors: labels are cognitively hostile. SELinux is technically sound but practically disabled on most systems because administrators cannot reason about label propagation correctly. Capabilities are intuitive—\"I have this, I can use it, I can delegate a subset\"—requiring no classification decisions and producing no \"why can't I access my own file\" mysteries.[^s2a]")
      (p "[^s2a]: Security: Experience with deployed MAC systems (SEVMS, SELinux, Windows MIC) shows that label complexity defeats usability. SEVMS was a layered product on VMS providing B1-level security classifications—powerful but rarely deployed outside government contracts. Users misconfigure labels, administrators disable enforcement, and the security model exists only on paper. Capability attenuation succeeds because it matches human intuition about possession and delegation."))
    (subsection
      "Audit as Flow Record"
      (p "Every crossing (read or write) is logged. The audit trail IS the flow history. Post-hoc analysis can reconstruct what data moved through which wormholes, when, and under what authority.")
      (p "This is the key assurance property: you cannot prove that information didn't flow (covert channels exist in any real system), but you can prove what DID flow and reconstruct the path post-hoc. The audit trail provides accountability rather than prevention—a pragmatic tradeoff that scales to real-world use.[^s3]")
      (p "[^s3]: Security: Mandatory access control aims to prevent unauthorized flows. We aim to detect and attribute them. Prevention requires trusting the entire stack; detection requires only trusting the audit log. For most threat models, accountable flow is sufficient.")
      (p "Audit is orthogonal to authorization. The capability check determines what is permitted; audit records what occurred. The audit trail is never consulted to decide whether to allow an operation—only to reconstruct flow history after the fact."))
    (subsection
      "Capability as Flow Constraint"
      (p "Table 4: Capability and Information Flow")
      (table
        (header "Capabilities " "Flow Direction " "Pattern ")
        (row "read without write " "vault→filesystem only " "Browse, export ")
        (row "write without read " "filesystem→vault only " "Dropbox, ingest ")
        (row "read+write " "bidirectional " "Full sync ")
        (row "neither " "no data flow " "Metadata-only mount ")))
    (subsection
      "Reference Monitor"
      (p "The wormhole acts as a reference monitor at the domain boundary. Every operation crosses the monitor, which validates capability, enforces rate limits (Memo-032), and records the audit trail (Memo-003). The monitor is complete (all crossings pass through it) and verifiable (audit enables post-hoc analysis).")
      (code scheme "(define (wormhole-flow-guard wormhole operation object)\n  \"Reference monitor for wormhole operations\"\n  (let ((caps (wormhole-capabilities wormhole)))\n    (unless (memq operation caps)\n      (wormhole-audit 'denied operation object)\n      (error 'capability-denied operation))\n    (unless (rate-limit-ok? wormhole)\n      (wormhole-audit 'rate-limited operation object)\n      (error 'rate-limited))\n    (wormhole-audit 'permitted operation object)\n    `(permitted ,operation ,object)))")))
  (section
    "Security Considerations"
    (subsection
      "Permissions"
      (p "FUSE daemon runs as user, not root. Respects vault ACLs."))
    (subsection
      "Content Integrity"
      (p "Every read verifies content hash. Corruption detected immediately."))
    (subsection
      "Metadata Trust"
      (p "Metadata is stored separately from content. A compromised metadata store cannot alter file contents (hashes won't match)."))
    (subsection
      "Mount Security"
      (code scheme "(define (vault-mount point #!key (allow-other #f))\n  ;; allow-other permits other users to access mount\n  ;; Default: owner only\n  ...)")))
  (section
    "Dependencies"
    (table
      (header "Component " "Purpose ")
      (row "FUSE-T or macFUSE " "Userspace filesystem ")
      (row "libfuse " "FUSE library ")
      (row "Scheme FFI " "Bindings to libfuse ")))
  (section
    "References"
    (list
      (item "Memo-012: Lamport Clocks")
      (item "Memo-016: Lazy Clustering")
      (item "Memo-020: Content-Addressed Storage")
      (item "FUSE documentation: https://libfuse.github.io/")
      (item "FUSE-T: https://github.com/macos-fuse-t/fuse-t")))
  (section
    "Changelog"
    (list
      (item "2026-01-07")
      (item "Initial specification"))))

