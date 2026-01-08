# RFC-041: Wormholes (FUSE Filesystem Layer)

**Status:** Draft
**Created:** 2026-01-07
**Authors:** Library of Cyberspace Contributors

---

## Abstract

This RFC specifies wormholes—FUSE-based bidirectional portals between the
macOS filesystem and the Library of Cyberspace vault. Wormholes preserve full
metadata including extended attributes, Finder tags, and ACLs. All operations
are auditable (RFC-003) and rate-limited (RFC-032).[^h1]

[^h1]: Historical: FUSE originated in Linux 2.6 (2005), inspired by earlier
userspace filesystem work in Plan 9 and Hurd. macFUSE (originally MacFUSE)
brought it to macOS in 2007. The abstraction outlived Apple's hostility.

---

## Motivation

Users need seamless integration between their existing filesystem and the
vault. Manual import/export creates friction and risks metadata loss.

A wormhole provides:

1. **Transparency** — Finder, `cp`, `rsync` work unchanged
2. **Bidirectionality** — No separate sync step; it IS the filesystem
3. **Metadata preservation** — Full macOS attributes captured automatically
4. **Content addressing** — Deduplication and integrity built-in
5. **Security** — First-class SPKI object with audit and rate-limit

The filesystem abstraction is the right boundary—everything above it (apps,
shell, Finder) works without modification.[^d1]

[^d1]: Design: FUSE inverts the usual model. Instead of teaching applications
about vaults, we teach the vault to speak filesystem. Unix got this right:
everything is a file.

---

## Wormhole as Security Object

A wormhole is a first-class security object in cyberspace, subject to:[^d2]

- **SPKI Authorization** (RFC-004) — Opening requires valid certificate
- **Capability Delegation** (RFC-021) — Wormhole access can be delegated
- **Audit Trail** (RFC-003) — All operations logged
- **Rate Limiting** (RFC-032) — Configurable ops/minute
- **Sandboxing** (RFC-023) — Agents access wormholes through capabilities

[^d2]: Design: Wormholes are attack surface. Unrestricted filesystem access
defeats vault security. Every wormhole must be explicitly authorized,
continuously audited, and rate-limited against abuse.

### Wormhole Certificate

```scheme
(define (wormhole-cert issuer fs-path vault-path permissions)
  "Create SPKI certificate authorizing wormhole"
  (create-cert
   issuer
   (wormhole-principal fs-path vault-path)
   `(tag (wormhole
          (fs-path ,fs-path)
          (vault-path ,vault-path)
          (permissions ,@permissions)   ; read, write, delete
          (rate-limit 1000)             ; ops/minute
          (expires ,(+ (current-seconds) 86400))))))
```

### Capability Model

Wormholes support fine-grained capabilities:[^d3]

[^d3]: Design: Rich capabilities enable principle of least privilege.
A backup agent needs read-only; a sync agent needs read-write but not
delete. Capabilities compose—grant exactly what's needed.

*Table 0: Wormhole Capabilities*

| Capability | Allows |
|------------|--------|
| **Data Access** | |
| `read` | Read file contents |
| `write` | Write/modify file contents |
| `create` | Create new files |
| `delete` | Remove files |
| `rename` | Rename/move files |
| **Metadata** | |
| `stat` | Read POSIX attributes |
| `chmod` | Modify permissions |
| `chown` | Change ownership |
| `xattr-read` | Read extended attributes |
| `xattr-write` | Modify extended attributes |
| `acl-read` | Read ACLs |
| `acl-write` | Modify ACLs |
| **Directory** | |
| `readdir` | List directory contents |
| `mkdir` | Create directories |
| `rmdir` | Remove directories |
| **Control** | |
| `admin` | Configure wormhole |
| `delegate` | Delegate capabilities to others |
| `audit-read` | Read wormhole audit log |
| `rate-limit` | Modify rate limits |

### Capability Composition

```scheme
;; Common capability sets (long form for readability)
(define capability:read-only
  '(read stat readdir xattr-read acl-read))

(define capability:read-write
  '(read write create stat chmod readdir mkdir xattr-read xattr-write))

(define capability:full
  '(read write create delete rename
    stat chmod chown
    xattr-read xattr-write acl-read acl-write
    readdir mkdir rmdir admin delegate audit-read rate-limit))

(define capability:backup
  '(read stat readdir xattr-read acl-read))

(define capability:synchronize
  '(read write create delete rename
    stat chmod readdir mkdir rmdir
    xattr-read xattr-write))
```

### Capability Attenuation

Capabilities can only be reduced, never amplified:[^r1]

[^r1]: Research: Capability attenuation is fundamental to the object-capability
model. See Miller, "Robust Composition" (2006). You cannot grant more authority
than you possess.

```scheme
(define (wormhole-delegate wormhole new-caps recipient)
  "Delegate subset of wormhole capabilities"
  (let ((my-caps (wormhole-capabilities wormhole)))
    (unless (subset? new-caps my-caps)
      (error 'capability-amplification
             "Cannot delegate capabilities you don't have"))
    (wormhole-cert
     (wormhole-issuer wormhole)
     (wormhole-fs-path wormhole)
     (wormhole-vault-path wormhole)
     new-caps
     recipient: recipient)))
```

### Opening a Wormhole

```scheme
(define (wormhole-open fs-path #!key (vault-path "/")
                                     (capabilities capability:read-write)
                                     (rate-limit 1000)
                                     (locked #f)
                                     (auth-required '())
                                     (certificate #f))
  "Open wormhole - requires valid certificate"
  (unless certificate
    (error 'unauthorized "Wormhole requires SPKI certificate"))
  (unless (verify-wormhole-cert certificate fs-path vault-path)
    (error 'unauthorized "Invalid wormhole certificate"))
  ;; Audit the open
  (wormhole-audit 'wormhole-open fs-path
                  `((vault ,vault-path)
                    (capabilities ,(length capabilities))))
  ;; Proceed with FUSE mount
  ...)
```

### Usage Examples

```scheme
;; Basic read-write wormhole
(wormhole-open "~/Cyberspace")

;; Read-only wormhole for browsing
(wormhole-open "~/Archive" capabilities: capability:read-only)

;; Sync wormhole with rate limiting
(wormhole-open "~/Sync"
  capabilities: capability:synchronize
  rate-limit: 500)

;; Locked wormhole requiring unlock for sensitive operations
(wormhole-open "~/Secure"
  capabilities: capability:full
  locked: #t
  auth-required: '(delete admin))
```

---

## Architecture

### Mount Topology

```
~/Cyberspace/                    ← FUSE mount point
├── documents/
│   ├── paper.pdf               ← Virtual file (content in vault)
│   └── notes.txt
├── projects/
│   └── cyberspace/
│       └── ...
└── .vault/                      ← Hidden, actual storage
    ├── objects/                 ← Content-addressed blobs
    │   ├── sha256:abc123...
    │   └── sha256:def456...
    ├── manifests/               ← Directory → file mappings
    └── metadata/                ← Per-file metadata store
```

### Component Stack

```
┌─────────────────────────────────────┐
│         Applications                │
│    (Finder, cp, rsync, etc.)        │
├─────────────────────────────────────┤
│         VFS (kernel)                │
├─────────────────────────────────────┤
│      FUSE-T / macFUSE               │
├─────────────────────────────────────┤
│    cyberspace-fuse daemon           │  ← Our code
├─────────────────────────────────────┤
│         Vault layer                 │
│   (content-address, metadata)       │
└─────────────────────────────────────┘
```

---

## Metadata Preservation

### macOS Metadata Captured

*Table 1: Preserved Metadata*

| Category | Attributes | Capture Method |
|----------|------------|----------------|
| POSIX | mode, uid, gid, size | `stat()` |
| Timestamps | mtime, atime, ctime, birthtime | `stat()` |
| Extended attrs | Finder info, tags, quarantine | `listxattr()`, `getxattr()` |
| Spotlight | kMDItem* metadata | `mdls` / MDItem API |
| ACLs | Access control lists | `acl_get_file()` |
| Flags | hidden, locked, immutable | `chflags()` / `stat()` |
| Resource fork | Legacy resource data | `xattr com.apple.ResourceFork` |

### Internal Representation

```scheme
(define-record-type <vault-file>
  (make-vault-file path content-hash metadata)
  vault-file?
  (path vault-file-path)
  (content-hash vault-file-hash)
  (metadata vault-file-metadata))

(define (capture-metadata path)
  "Capture all macOS metadata for a file"
  `((posix
     (mode ,(file-mode path))
     (uid ,(file-uid path))
     (gid ,(file-gid path))
     (size ,(file-size path))
     (mtime ,(file-mtime path))
     (atime ,(file-atime path))
     (ctime ,(file-ctime path))
     (birthtime ,(file-birthtime path)))
    (xattr ,(capture-xattrs path))
    (flags ,(capture-flags path))
    (acl ,(capture-acl path))))
```

### Restoration

```scheme
(define (restore-metadata path metadata)
  "Restore all metadata to a file"
  (let ((posix (alist-ref 'posix metadata))
        (xattr (alist-ref 'xattr metadata))
        (flags (alist-ref 'flags metadata))
        (acl (alist-ref 'acl metadata)))
    (restore-posix path posix)
    (restore-xattrs path xattr)
    (restore-flags path flags)
    (restore-acl path acl)))
```

---

## FUSE Operations

### Required Operations

*Table 2: FUSE Operations*

| Operation | Purpose | Vault Action |
|-----------|---------|--------------|
| `getattr` | stat() | Return stored metadata |
| `readdir` | List directory | Read manifest |
| `open` | Open file | Validate hash exists |
| `read` | Read content | Fetch by content hash |
| `write` | Write content | Content-address, update manifest |
| `create` | Create file | Allocate manifest entry |
| `unlink` | Delete file | Remove from manifest (GC later) |
| `mkdir` | Create directory | Create manifest node |
| `rmdir` | Remove directory | Remove manifest node |
| `rename` | Move/rename | Update manifest path |
| `setxattr` | Set extended attr | Store in metadata |
| `getxattr` | Get extended attr | Retrieve from metadata |
| `listxattr` | List extended attrs | Enumerate metadata |

### Implementation Sketch

```scheme
(define (fuse-getattr path)
  "Return file attributes from vault metadata"
  (let ((entry (manifest-lookup path)))
    (if entry
        (let ((meta (vault-file-metadata entry)))
          (make-stat
           (alist-ref 'mode (alist-ref 'posix meta))
           (alist-ref 'size (alist-ref 'posix meta))
           (alist-ref 'mtime (alist-ref 'posix meta))
           ...))
        -ENOENT)))

(define (fuse-read path size offset)
  "Read file content from vault"
  (let* ((entry (manifest-lookup path))
         (hash (vault-file-hash entry))
         (content (vault-fetch hash)))
    (subbytes content offset (+ offset size))))

(define (fuse-write path data offset)
  "Write to file, content-address the result"
  (let* ((entry (manifest-lookup path))
         (current (vault-fetch (vault-file-hash entry)))
         (updated (bytes-splice current offset data))
         (new-hash (content-address updated)))
    (manifest-update! path new-hash)
    (string-length data)))

(define (fuse-setxattr path name value)
  "Store extended attribute in vault metadata"
  (let ((entry (manifest-lookup path)))
    (metadata-set-xattr! entry name value)
    0))
```

---

## Content Addressing

Files are stored by content hash (RFC-020):

```scheme
(define (content-address data)
  "Store data, return hash"
  (let* ((hash (sha256 data))
         (path (vault-object-path hash)))
    (unless (file-exists? path)
      (write-blob path data))
    hash))

(define (vault-fetch hash)
  "Retrieve data by hash"
  (read-blob (vault-object-path hash)))
```

Benefits:
- Identical files stored once (deduplication)
- Integrity verification on every read
- Immutable objects enable safe caching

---

## Synchronization

### Change Detection

The FUSE layer captures all writes in real-time. No separate sync needed
for local changes.

For multi-device sync, the manifest includes version vectors (RFC-012):

```scheme
(define (manifest-entry path hash metadata)
  `(entry
    (path ,path)
    (hash ,hash)
    (metadata ,metadata)
    (version-vector ,*local-node* ,*lamport-clock*)))
```

### Conflict Resolution

When merging manifests from different devices (RFC-016 lazy clustering):

1. Same hash → No conflict (identical content)
2. Different hash, one newer → Take newer
3. Different hash, concurrent → Conflict, apply `lazy-resolve`

```scheme
(define (merge-manifests local remote)
  (for-each
   (lambda (path)
     (let ((l (manifest-lookup local path))
           (r (manifest-lookup remote path)))
       (cond
        ((not l) (manifest-add! local r))
        ((not r) 'keep-local)
        ((equal? (vault-file-hash l) (vault-file-hash r)) 'identical)
        ((version-newer? r l) (manifest-update! local r))
        ((version-newer? l r) 'keep-local)
        (else (queue-conflict! path l r)))))
   (union (manifest-paths local) (manifest-paths remote))))
```

---

## Mount Commands

### REPL Interface

```scheme
(define (vault-mount point)
  "Mount vault at filesystem path"
  (fuse-main point
    `((getattr . ,fuse-getattr)
      (readdir . ,fuse-readdir)
      (open . ,fuse-open)
      (read . ,fuse-read)
      (write . ,fuse-write)
      (create . ,fuse-create)
      (unlink . ,fuse-unlink)
      (mkdir . ,fuse-mkdir)
      (rmdir . ,fuse-rmdir)
      (rename . ,fuse-rename)
      (setxattr . ,fuse-setxattr)
      (getxattr . ,fuse-getxattr)
      (listxattr . ,fuse-listxattr))))

(define (vault-unmount point)
  "Unmount vault filesystem"
  (fuse-unmount point))
```

### Command Line

```bash
# Mount
cyberspace mount ~/Cyberspace

# Unmount
cyberspace unmount ~/Cyberspace

# Or via REPL
$ ./cyberspace-repl
> (vault-mount "~/Cyberspace")
Mounted vault at /Users/ddp/Cyberspace
```

---

## macOS Integration

### FUSE-T vs macFUSE

*Table 3: FUSE Implementation Options*

| Feature | macFUSE | FUSE-T |
|---------|---------|--------|
| Kernel extension | Yes (deprecated) | No |
| System extension | Optional | Uses NFS |
| SIP compatible | Requires disable | Yes |
| Performance | Better | Adequate |
| Maintenance | Active | Active |

FUSE-T recommended for new installations—no kernel extension required.[^i1]

[^i1]: Implementation: FUSE-T implements FUSE API over NFS loopback.
Slightly higher latency but avoids Apple's kernel extension hostility.

### Installation

```bash
# FUSE-T (recommended)
brew install fuse-t

# Or macFUSE (if kernel ext acceptable)
brew install macfuse
```

### Finder Integration

The mount appears as a regular volume in Finder. Optional `.VolumeIcon.icns`
for custom icon.

Spotlight indexing can be enabled by implementing `getxattr` for
`com.apple.FinderInfo` and related Spotlight attributes.

---

## Security Considerations

### Permissions

FUSE daemon runs as user, not root. Respects vault ACLs.

### Content Integrity

Every read verifies content hash. Corruption detected immediately.

### Metadata Trust

Metadata is stored separately from content. A compromised metadata store
cannot alter file contents (hashes won't match).

### Mount Security

```scheme
(define (vault-mount point #!key (allow-other #f))
  ;; allow-other permits other users to access mount
  ;; Default: owner only
  ...)
```

---

## Dependencies

| Component | Purpose |
|-----------|---------|
| FUSE-T or macFUSE | Userspace filesystem |
| libfuse | FUSE library |
| Scheme FFI | Bindings to libfuse |

---

## References

1. RFC-012: Lamport Clocks
2. RFC-016: Lazy Clustering
3. RFC-020: Content-Addressed Storage
4. FUSE documentation: https://libfuse.github.io/
5. FUSE-T: https://github.com/macos-fuse-t/fuse-t

---

## Changelog

- **2026-01-07** - Initial specification

---

**Implementation Status:** Draft
