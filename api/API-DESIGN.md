# Cyberspace API

**RESTful HTTP API for the Library of Cyberspace**

Provides programmatic access to research papers, cryptographic implementations, and distributed systems tools.

## Philosophy

> "Rough consensus, cryptography, trusted systems and running code."

The Cyberspace API demonstrates **research → practice** by:
- Exposing implemented cryptographic primitives as API endpoints
- Using capability-based authentication (Lampson)
- Providing ChaCha20-Poly1305 AEAD for transport security
- Serving as integration point for distributed agent architecture

## Architecture

```
┌─────────────────────────────────────────────┐
│  Cyberspace API Server (Chicken Scheme)    │
├─────────────────────────────────────────────┤
│                                             │
│  ┌──────────────┐  ┌─────────────────────┐ │
│  │   /library   │  │      /crypto        │ │
│  │              │  │                     │ │
│  │ - search     │  │ - lamport/sign      │ │
│  │ - papers     │  │ - chacha20/encrypt  │ │
│  │ - catalog    │  │ - poly1305/mac      │ │
│  └──────────────┘  │ - merkle/build      │ │
│                    │ - capabilities/     │ │
│  ┌──────────────┐  │   create            │ │
│  │    /impl     │  └─────────────────────┘ │
│  │              │                           │
│  │ - list       │  ┌─────────────────────┐ │
│  │ - run        │  │       /auth         │ │
│  │ - demo       │  │                     │ │
│  └──────────────┘  │ - login             │ │
│                    │ - capability        │ │
│                    │ - verify            │ │
│                    └─────────────────────┘ │
└─────────────────────────────────────────────┘
```

## Endpoints

### Library (`/library`)

**GET /library/search?q=<query>**
- Search papers by keyword, author, topic
- Returns: List of matching papers with metadata
- Example: `/library/search?q=lamport+signatures`

**GET /library/papers/<paper-id>**
- Retrieve paper metadata
- Returns: Title, authors, year, abstract, path
- Example: `/library/papers/lamport-1979-signatures`

**GET /library/catalog**
- List all papers in library
- Returns: Full catalog with categories
- Example: `/library/catalog`

**GET /library/papers/<paper-id>/download**
- Download PDF (if available)
- Returns: PDF file or link
- Requires: Read capability for paper

### Cryptography (`/crypto`)

**POST /crypto/lamport/keygen**
- Generate Lamport signature keypair
- Body: `{"bits": 256}`
- Returns: `{"private_key": "...", "public_key": "..."}`

**POST /crypto/lamport/sign**
- Sign message with Lamport signature
- Body: `{"private_key": "...", "message": "..."}`
- Returns: `{"signature": "...", "warning": "keypair now used"}`

**POST /crypto/lamport/verify**
- Verify Lamport signature
- Body: `{"public_key": "...", "message": "...", "signature": "..."}`
- Returns: `{"valid": true/false}`

**POST /crypto/chacha20/encrypt**
- Encrypt with ChaCha20
- Body: `{"key": "hex", "nonce": "hex", "plaintext": "..."}`
- Returns: `{"ciphertext": "hex"}`

**POST /crypto/chacha20/decrypt**
- Decrypt with ChaCha20
- Body: `{"key": "hex", "nonce": "hex", "ciphertext": "hex"}`
- Returns: `{"plaintext": "..."}`

**POST /crypto/poly1305/mac**
- Compute Poly1305 MAC
- Body: `{"key": "hex", "message": "..."}`
- Returns: `{"tag": "hex"}`

**POST /crypto/merkle/build**
- Build Merkle tree
- Body: `{"items": ["data1", "data2", ...]}`
- Returns: `{"root": "hex", "tree": {...}}`

**POST /crypto/merkle/prove**
- Generate inclusion proof
- Body: `{"tree": {...}, "item": "data"}`
- Returns: `{"proof": [...], "root": "hex"}`

**POST /crypto/merkle/verify**
- Verify inclusion proof
- Body: `{"root": "hex", "item": "data", "proof": [...]}`
- Returns: `{"valid": true/false}`

**POST /crypto/capabilities/create**
- Create capability token
- Body: `{"object_id": "...", "rights": ["read", "write"], "expiry": 3600}`
- Returns: `{"token": "...", "expires": 1234567890}`

**POST /crypto/capabilities/verify**
- Verify capability token
- Body: `{"token": "...", "operation": "read"}`
- Returns: `{"valid": true/false, "rights": [...]}`

**POST /crypto/capabilities/delegate**
- Delegate capability (attenuation)
- Body: `{"token": "...", "new_rights": ["read"]}`
- Returns: `{"token": "...", "rights": ["read"]}`

### Implementations (`/impl`)

**GET /impl/list**
- List all implementations
- Returns: Array of implementation metadata
- Example: `[{"name": "lamport-otp", "status": "complete", ...}, ...]`

**POST /impl/<name>/demo**
- Run implementation demo
- Body: `{"demo": "basic", "args": {...}}`
- Returns: Demo output

**GET /impl/<name>/info**
- Get implementation details
- Returns: README content, status, lineage

### Authentication (`/auth`)

**POST /auth/login**
- Authenticate and receive capability
- Body: `{"username": "...", "password": "..."}`
- Returns: `{"capability": "...", "expires": 3600}`

**POST /auth/verify**
- Verify authentication capability
- Body: `{"capability": "..."}`
- Returns: `{"valid": true/false, "user": "...", "rights": [...]}`

**POST /auth/refresh**
- Refresh expiring capability
- Body: `{"capability": "..."}`
- Returns: `{"capability": "...", "expires": 3600}`

## Authentication & Authorization

**Capability-Based Security** (using our implementation!)

```
1. Client authenticates → receives capability token
2. Capability token grants specific rights:
   - read-library: Search and read papers
   - use-crypto: Call /crypto endpoints
   - admin: Full access

3. Each request includes capability in header:
   Authorization: Capability <token>

4. Server verifies:
   - Token signature (HMAC)
   - Expiry timestamp
   - Rights for requested operation
```

**Example Flow:**

```bash
# 1. Login
curl -X POST http://localhost:8080/auth/login \
  -H "Content-Type: application/json" \
  -d '{"username": "alice", "password": "secret"}'

# Response:
{
  "capability": "obj123:read-library,use-crypto:abc123:1234567890:signature",
  "expires": 3600
}

# 2. Use capability to encrypt
curl -X POST http://localhost:8080/crypto/chacha20/encrypt \
  -H "Authorization: Capability obj123:read-library,use-crypto:abc123:..." \
  -H "Content-Type: application/json" \
  -d '{"key": "00...00", "nonce": "00...00", "plaintext": "Hello"}'

# Response:
{
  "ciphertext": "3edd8cc1cfdd1dd3..."
}
```

## Transport Security

**ChaCha20-Poly1305 AEAD** for encrypted communication:

```
1. TLS 1.3 with ChaCha20-Poly1305 cipher suite
2. Or custom protocol:
   - Client → Server: Nonce, Encrypted(Request)
   - Server → Client: Nonce, Encrypted(Response)
   - MAC: Poly1305 tag over ciphertext
```

**Why ChaCha20-Poly1305?**
- We implemented it!
- Demonstrates research → practice
- Fast on all platforms
- Constant-time (no timing attacks)

## Error Handling

**Consistent error format:**

```json
{
  "error": {
    "code": "INVALID_CAPABILITY",
    "message": "Capability expired",
    "details": {
      "expired_at": 1234567890,
      "current_time": 1234567900
    }
  }
}
```

**Error codes:**
- `INVALID_CAPABILITY`: Authentication failed
- `PERMISSION_DENIED`: Lacks required rights
- `INVALID_INPUT`: Malformed request
- `NOT_FOUND`: Resource doesn't exist
- `CRYPTO_ERROR`: Cryptographic operation failed
- `SERVER_ERROR`: Internal error

## Rate Limiting

**Capability-based rate limits:**

```
Each capability has embedded rate limit:
- read-library: 100 req/min
- use-crypto: 10 req/min
- admin: unlimited

Enforced by tracking capability usage in memory.
```

## Implementation

**Technology Stack:**
- **Server**: Chicken Scheme (spiffy HTTP server)
- **Crypto**: Our implementations (ChaCha20, Poly1305, etc.)
- **Auth**: Our capability system
- **Storage**: File-based (library/) + in-memory cache
- **Format**: JSON for requests/responses

**File Structure:**
```
api/
├── API-DESIGN.md          (this file)
├── server.scm             (main HTTP server)
├── routes/
│   ├── library.scm        (library endpoints)
│   ├── crypto.scm         (crypto endpoints)
│   ├── impl.scm           (implementation endpoints)
│   └── auth.scm           (authentication endpoints)
├── guards/
│   ├── auth.scm           (capability verification)
│   ├── rate-limit.scm     (rate limiting)
│   └── logging.scm        (request logging)
└── README.md              (API usage guide)
```

## Usage Examples

### Python Client

```python
import requests
import json

# Authenticate
resp = requests.post('http://localhost:8080/auth/login',
                     json={'username': 'alice', 'password': 'secret'})
capability = resp.json()['capability']

# Encrypt message
resp = requests.post('http://localhost:8080/crypto/chacha20/encrypt',
                     headers={'Authorization': f'Capability {capability}'},
                     json={
                         'key': '00' * 32,
                         'nonce': '00' * 12,
                         'plaintext': 'Hello, Cyberspace!'
                     })
ciphertext = resp.json()['ciphertext']

# Search library
resp = requests.get('http://localhost:8080/library/search?q=lamport',
                    headers={'Authorization': f'Capability {capability}'})
papers = resp.json()['papers']
```

### JavaScript Client

```javascript
// Authenticate
const loginResp = await fetch('http://localhost:8080/auth/login', {
  method: 'POST',
  headers: {'Content-Type': 'application/json'},
  body: JSON.stringify({username: 'alice', password: 'secret'})
});
const {capability} = await loginResp.json();

// Sign with Lamport
const signResp = await fetch('http://localhost:8080/crypto/lamport/sign', {
  method: 'POST',
  headers: {
    'Authorization': `Capability ${capability}`,
    'Content-Type': 'application/json'
  },
  body: JSON.stringify({
    private_key: '...',
    message: 'Hello, Cyberspace!'
  })
});
const {signature} = await signResp.json();
```

### Curl Examples

```bash
# Search library
curl -H "Authorization: Capability $TOKEN" \
  http://localhost:8080/library/search?q=merkle

# Generate Lamport keypair
curl -X POST -H "Authorization: Capability $TOKEN" \
  -H "Content-Type: application/json" \
  -d '{"bits": 256}' \
  http://localhost:8080/crypto/lamport/keygen

# Create capability
curl -X POST -H "Authorization: Capability $TOKEN" \
  -H "Content-Type: application/json" \
  -d '{"object_id": "doc1", "rights": ["read"], "expiry": 3600}' \
  http://localhost:8080/crypto/capabilities/create
```

## Future Enhancements

**Phase 1: Core API** (MVP)
- [x] API design
- [ ] HTTP server
- [ ] /library endpoints
- [ ] /crypto endpoints
- [ ] Capability-based auth

**Phase 2: Advanced Features**
- [ ] WebSocket support (real-time updates)
- [ ] Streaming responses (large papers)
- [ ] GraphQL interface
- [ ] gRPC support

**Phase 3: Distributed**
- [ ] Federation (multiple Cyberspace nodes)
- [ ] Gossip protocol (capability distribution)
- [ ] IPFS integration (distributed storage)
- [ ] Merkle-based sync

**Phase 4: Production**
- [ ] Docker container
- [ ] Kubernetes deployment
- [ ] Monitoring (Prometheus)
- [ ] Logging (structured JSON)
- [ ] Documentation (Swagger/OpenAPI)

## Security Considerations

**1. Capability Security**
- ✓ Unforgeable tokens (HMAC-signed)
- ✓ Time-limited (expiry timestamps)
- ✓ Attenuatable (delegate subset of rights)
- ✓ No ambient authority (must present capability)

**2. Transport Security**
- ✓ TLS 1.3 with ChaCha20-Poly1305
- ✓ Certificate pinning (optional)
- ✓ HSTS headers

**3. Input Validation**
- ✓ JSON schema validation
- ✓ Hex string validation (keys, nonces)
- ✓ Length limits (prevent DoS)
- ✓ Type checking

**4. Rate Limiting**
- ✓ Per-capability limits
- ✓ Sliding window
- ✓ Adaptive based on load

**5. Logging**
- ✓ Structured logging (JSON)
- ✓ No secrets in logs
- ✓ Audit trail (who accessed what)

## Performance

**Expected throughput:**
- Library search: 100 req/s
- Crypto operations: 1000 req/s (ChaCha20, Poly1305 are fast!)
- Lamport sign/verify: 10 req/s (slower due to many hashes)

**Optimization strategies:**
- In-memory caching (library metadata)
- Connection pooling
- Async I/O (SRFI-18 threads)

## Testing

**Test coverage:**
- Unit tests for each endpoint
- Integration tests for auth flow
- Load tests (wrk, ab)
- Security tests (fuzzing, timing attacks)

## License

Public domain. Based on foundational research from Lamport, Lampson, Bernstein, Merkle, and others.

---

**"An API that demonstrates the principles it serves."**

- Capability-based authentication (Lampson 1971)
- ChaCha20-Poly1305 AEAD (Bernstein 2005-2008)
- Merkle proofs (Merkle 1979)
- Lamport signatures (Lamport 1979)

**Research → Practice → API**
