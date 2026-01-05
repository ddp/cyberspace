# Capability-Based Authentication System

**Practical implementation of unforgeable access tokens based on 1970s-1980s capability research**

From papers by: Butler Lampson, Dennis & Van Horn, Fabry, Miller & others
Source: `~/cyberspace/library/cryptographers/lampson/`

## The Concept

**"Don't separate designation from authority"**

Traditional security (ACLs):
```
User → Resource → Check ACL → Allow/Deny
         ↑
      Central authority decides
```

Capability security:
```
Capability = Unforgeable (Object Reference + Rights)
Possession = Authority
No central check needed
```

**Key Insight:** If you can name it (have the reference), you can use it (have authority).

## The Problem Capabilities Solve

### Access Control Lists (ACLs) - Traditional Approach

```
File: /docs/secret.txt
ACL:
  alice: read, write
  bob:   read
  carol: none
```

**Problems:**
- ✗ Confused deputy (program acts with wrong authority)
- ✗ Ambient authority (identity alone grants access)
- ✗ Hard to delegate (need central ACL update)
- ✗ Revocation requires finding all references
- ✗ Can't express "give Bob 1-hour read access"

### Capabilities - Solve All These

```
Capability = (object-id, [read write], secret, expiry)

alice-cap: ("secret.txt", [read write delete], "a3f5...", never)
bob-cap:   ("secret.txt", [read], "b2e4...", +3600s)
```

**Advantages:**
- ✓ No confused deputy (capability is explicit authority)
- ✓ No ambient authority (must possess capability)
- ✓ Easy delegation (just share capability)
- ✓ Fine-grained (per-object, per-operation)
- ✓ Time-limited (built-in expiry)

## Quick Start

```bash
cd ~/cyberspace/implementations/capabilities

# Run all demonstrations
./capabilities.scm demo-all

# Or run individual demos:
./capabilities.scm demo-basic        # Basic operations
./capabilities.scm demo-serialize    # Unforgeable tokens
./capabilities.scm demo-delegation   # Delegation chain
./capabilities.scm demo-expiry       # Time-limited access
```

## How It Works

### 1. Creating Capabilities

```scheme
; Alice creates a document
(define alice-cap (create-object! "Secret research notes"))

; alice-cap = ("8125a89a...", [read write delete], "b6f30b...", never)
;              └─ object-id   └─ rights            └─ secret  └─ expiry
```

**No ACL needed!** Possession of capability = authority to access.

### 2. Using Capabilities

```scheme
; Alice reads (has 'read right)
(read-object alice-cap)
→ "Secret research notes"

; Alice writes (has 'write right)
(write-object alice-cap "Updated notes")
→ #t

; Alice deletes (has 'delete right)
(delete-object alice-cap)
→ #t
```

**No identity check!** System only verifies: capability is valid + operation is allowed.

### 3. Delegation (Attenuation)

```scheme
; Alice shares read-only with Bob
(define bob-cap (attenuate-capability alice-cap '(read)))

; bob-cap = ("8125a89a...", [read], "c7a41d...", never)
;                            └─ subset of alice's rights

; Bob can read
(read-object bob-cap) → "Secret research notes"

; Bob cannot write (doesn't have 'write right)
(write-object bob-cap "Hacked!") → Permission denied
```

**Attenuation**: Delegation creates capability with ⊆ (subset) of rights.

**Security property:** Can never grant more rights than you have.

### 4. Delegation Chains

```scheme
Alice: [read write delete]
  ↓
  attenuate to [read write]
  ↓
Bob: [read write]
  ↓
  attenuate to [read]
  ↓
Carol: [read]
  ↓
  attempt to attenuate to [read write]
  ↓
  ✗ Error: Can't grant rights not in original capability
```

**Monotonic attenuation:** Rights can only decrease through delegation chain.

### 5. Unforgeable Tokens (Serialization)

Capabilities serialize to **HMAC-signed tokens**:

```
Token = object-id:rights:secret:expiry:HMAC-SHA256(master-key, payload)
        └────────────── payload ────────────┘  └──── signature ──────┘

Example:
8125a89a:read,write:b6f30b:never:3a5f7c2d8e9b1a4c6f8d0e2a4b6c8d0e
```

**Security:**
- Can't forge (need master key for HMAC)
- Can't tamper (signature verification fails)
- Can pass over network (self-contained)
- Can store in database/file (serializable)

**Verification:**
```scheme
(define token "8125a89a:read,write:b6f30b:never:3a5f7c2d...")
(define cap (parse-capability token))

If HMAC matches → valid capability
If HMAC doesn't match → #f (rejected)
```

### 6. Time-Limited Access

```scheme
; Alice's permanent capability
(define alice-cap (create-object! "Document"))

; Grant Bob 1-hour access
(define bob-temp-cap (expire-capability alice-cap 3600))

; bob-temp-cap expires in 3600 seconds
; After expiry: (capability-expired? bob-temp-cap) → #t
;              (read-object bob-temp-cap) → Permission denied
```

**Use cases:**
- Temporary contractor access
- Time-limited file sharing
- Session tokens
- Timed API keys

## Example Session

```bash
$ ./capabilities.scm demo-basic
Generated new master key: .master-key
Keep this file secure!
═══════════════════════════════════════════════════
Capability System Demo: Basic Operations
═══════════════════════════════════════════════════

1. Alice creates a document
Created object: 8125a89a876a8327
   Alice's capability: (read write delete)

2. Alice reads her document
   Content: Secret research notes

3. Alice shares read-only access with Bob
   Bob's capability: (read)

4. Bob reads the document
   Content: Secret research notes

5. Bob tries to modify the document
Permission denied: write access required

6. Alice modifies her document
Object updated
   New content: Updated research notes
```

## Security Properties

### ✓ Guarantees

**1. Unforgeable**
```
Attacker tries to create fake capability:
  Need to forge HMAC signature
  Need master key
  → Cryptographically hard (2²⁵⁶ brute force)
```

**2. Tamper-Evident**
```
Attacker modifies token to add 'write' right:
  "...read:..." → "...read,write:..."
  HMAC verification fails
  → Rejected
```

**3. Monotonic Attenuation**
```
Carol has [read]
Carol tries to delegate [read write] to Dave
  → Rejected (can't grant rights you don't have)
```

**4. No Ambient Authority**
```
Traditional: "I am alice, give me access to file X"
             System checks ACL, grants based on identity

Capability: "Here is capability for file X"
            System grants based on possession (no identity check)
```

**5. Principle of Least Privilege**
```
Don't give: [read write delete] when only [read] needed
Give: attenuate-capability to minimal rights
```

### ✗ Limitations

**1. Revocation is Hard**
```
Problem: Once capability shared, hard to revoke
  Alice → Bob (token passed over email)
  Alice wants to revoke
  → Can't "take back" token from Bob

Solutions:
  - Short expiry times (force renewal)
  - Revocation lists (check on each use)
  - Proxy capabilities (indirection layer)
```

**2. Confused Deputy (Partially Mitigated)**
```
Deputy program acts on behalf of users
  Receives capability from Alice
  Receives capability from Bob
  Must not mix them up!

Capability helps:
  - Explicit authority (not ambient)
  - Can't accidentally use wrong capability

But doesn't prevent:
  - Deputy intentionally switching capabilities
  - Deputy being tricked into misusing capabilities
```

**3. Delegation Can't Be Undone**
```
Alice → Bob → Carol → Dave
Alice later regrets sharing with Bob
  → Can't undo delegation to Carol, Dave

Mitigation:
  - Time-limited capabilities
  - Proxy capabilities (revocable)
```

## Real-World Applications

### seL4 Microkernel (2009)

**Pure capability system** - every resource is capability:

```
Capability types:
  - Endpoint (IPC)
  - TCB (thread control block)
  - CNode (capability space)
  - Page (memory)
  - IRQ (interrupt)
```

**Security:** Proven that kernel can't violate capability invariants (formal verification).

### CloudFlare Workers (2018)

**V8 Isolates** with capability-based security:

```javascript
// Worker receives capability to fetch
export default {
  async fetch(request, env) {
    // 'request' is capability to access incoming HTTP
    // 'env' contains capabilities to services
    const result = await env.KV.get('key')  // KV capability
    return new Response(result)
  }
}
```

**Security:** Worker can only access services it has capabilities for.

### Google Fuchsia (2016-present)

**Capability-based OS**:

```
Components receive capabilities, not ambient authority
Can only access services they're granted capabilities for
Fine-grained: capability per resource, per operation
```

### Amazon S3 Pre-Signed URLs (2006)

**Time-limited capabilities** for objects:

```
URL = https://bucket.s3.amazonaws.com/object?
      Expires=1767590000&
      Signature=3a5f7c2d8e9b1a4c...

Capabilities properties:
  ✓ Unforgeable (HMAC signature)
  ✓ Time-limited (Expires parameter)
  ✓ Fine-grained (per-object)
  ✓ Delegatable (share URL)
```

### WebAssembly Capability Model (2020s)

**WASI** (WebAssembly System Interface) uses capabilities:

```
WASM module receives capabilities for:
  - File descriptors
  - Network sockets
  - Environment variables

Cannot access anything not explicitly granted
```

## Comparison to Traditional Security

| Property | ACL (Traditional) | Capabilities |
|----------|-------------------|--------------|
| Authority | Identity-based | Possession-based |
| Delegation | Update ACL (complex) | Share capability (trivial) |
| Revocation | Update ACL (easy) | Hard (unless proxy) |
| Fine-grained | Per-resource | Per-resource + per-operation |
| Time-limited | Usually separate mechanism | Built-in (expiry) |
| Confused deputy | Vulnerable | Mitigated |
| Ambient authority | Yes (identity is authority) | No (must have capability) |

**When to use ACLs:**
- Centralized administration needed
- Need easy revocation
- Static access patterns
- Trust users

**When to use Capabilities:**
- Delegation is common
- Fine-grained access needed
- Time-limited access needed
- Minimize trust (principle of least privilege)

## Implementation Notes

### Master Key Security

The master key (`.master-key`) is **critical**:

```
If compromised:
  → Attacker can forge capabilities
  → All security lost

Protection:
  - Store in secure location (not in git!)
  - Encrypt at rest
  - Rotate periodically
  - Use HSM in production
```

**Production deployment:**
```
Don't store master key in file
Use: Hardware Security Module (HSM)
     Key Management Service (AWS KMS, GCP KMS)
     Vault (HashiCorp)
```

### HMAC vs Digital Signatures

**This implementation uses HMAC:**
```
+ Fast (symmetric crypto)
+ Simple
- Requires shared secret (master key)
- Can't verify without master key
```

**Alternative: Digital signatures (public-key):**
```
+ Anyone can verify (public key)
+ No shared secret
- Slower (asymmetric crypto)
- Larger tokens
```

**When to use each:**
- HMAC: Internal system, server-side
- Signatures: Distributed system, client-side verification

### Capability Storage

**This implementation:** In-memory `*objects*` list
```
+ Simple
+ Fast
- Lost on restart
- No persistence
```

**Production:** Database
```
CREATE TABLE objects (
  object_id TEXT PRIMARY KEY,
  content BLOB,
  created_at INTEGER,
  owner_secret TEXT
);

CREATE TABLE capability_grants (
  object_id TEXT,
  grantee TEXT,
  rights TEXT,
  secret TEXT,
  expiry INTEGER
);
```

## Design Patterns

### 1. Proxy Capabilities (Revocable)

```scheme
; Problem: Hard to revoke shared capability
; Solution: Indirection

(define *proxy-table* '())  ; (proxy-id → real-cap) mapping

(define (create-proxy-capability real-cap)
  (let ((proxy-id (random-bytes 16)))
    (set! *proxy-table* (cons (list proxy-id real-cap) *proxy-table*))
    proxy-id))

(define (revoke-proxy! proxy-id)
  (set! *proxy-table*
        (filter (lambda (entry) (not (equal? (car entry) proxy-id)))
                *proxy-table*)))

; Alice creates proxy capability
(define proxy (create-proxy-capability alice-cap))

; Alice shares proxy with Bob
; ...

; Alice revokes
(revoke-proxy! proxy)
; Bob's proxy no longer works
```

### 2. Capability Amplification (Guards)

```scheme
; Problem: Need to temporarily elevate rights
; Solution: Guard objects that grant additional rights

(define (with-elevated-rights cap additional-rights thunk)
  ; Temporarily combine rights
  (let ((elevated-cap (make-capability
                       (capability-object cap)
                       (append (capability-rights cap) additional-rights))))
    ; Run code with elevated capability
    (thunk elevated-cap)))

; Use:
(with-elevated-rights bob-cap '(write)
  (lambda (elevated-cap)
    (write-object elevated-cap "Temporary write access")))
```

### 3. Membrane Pattern (Interposition)

```scheme
; Problem: Want to mediate all access through capability
; Solution: Wrapper that intercepts operations

(define (create-logged-capability cap log-file)
  ; Return wrapper that logs all operations
  (lambda (operation . args)
    (log-to-file log-file (list operation args))
    (case operation
      ((read) (read-object cap))
      ((write) (write-object cap (car args)))
      ...)))
```

## Research Lineage

```
Dennis & Van Horn (1966)
"Programming Semantics for Multiprogrammed Computations"
  → Introduced capability concept
    ↓
Lampson (1971)
"Protection"
  → Formalized capability security
    ↓
Fabry (1974)
"Capability-Based Addressing"
  → Hardware support for capabilities
    ↓
Miller et al. (2003)
"Capability Myths Demolished"
  → Showed capabilities practical for modern systems
    ↓
seL4 (2009)
  → First verified capability-based OS
    ↓
Fuchsia (2016), CloudFlare Workers (2018)
  → Modern production capability systems
```

**60+ years** of capability research, now mainstream in modern systems.

## Educational Value

This implementation demonstrates:

**1. Security by Design**
- Unforgeable references (cryptographic tokens)
- Least privilege (minimal rights)
- No ambient authority (explicit capability needed)

**2. Cryptographic Primitives**
- HMAC (message authentication)
- Random secrets (entropy)
- Signature verification

**3. Access Control Models**
- Delegation (attenuation)
- Time-limited access
- Fine-grained permissions

**4. Real-World Systems**
- seL4 internals (capability-based OS)
- S3 pre-signed URLs (capability tokens)
- WebAssembly security (capability model)

## Files

```
capabilities/
├── README.md           (this file)
├── capabilities.scm    (implementation)
└── .master-key         (generated on first run - keep secure!)
```

## Dependencies

- Chicken Scheme 5.x
- OpenSSL (for HMAC, random generation)

## Future Enhancements

**Features:**
- [ ] Proxy capabilities (revocable)
- [ ] Capability delegation history (audit trail)
- [ ] Persistent storage (SQLite backend)
- [ ] Network protocol (capability over HTTP)
- [ ] Digital signatures (public-key verification)

**Security:**
- [ ] Capability revocation lists
- [ ] Master key rotation
- [ ] HSM integration (production)
- [ ] Capability confinement (membranes)

**Applications:**
- [ ] File system with capability-based access
- [ ] HTTP API with capability tokens
- [ ] Distributed system with capability-based RPC

## License

Public domain. Based on capability research from 1960s-1980s.

---

**"Don't separate designation from authority"**
—The core principle of capability security

**From research to reality:**
Dennis & Van Horn (1966) → Your capability-secured systems (now)
