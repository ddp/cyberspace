# Cyberspace API

**RESTful HTTP API for the Library of Cyberspace**

Provides programmatic access to research papers, cryptographic implementations, and distributed systems tools.

## Philosophy

> "Rough consensus, cryptography, trusted systems and running code."

The Cyberspace API demonstrates **research → practice** by:
- Exposing implemented cryptographic primitives as API endpoints
- Using capability-based authentication (Lampson 1971, 1992)
- Providing ChaCha20-Poly1305 AEAD for transport security
- Serving as integration point for distributed agent architecture

## Quick Start

### Start the Server

```bash
cd /Users/ddp/cyberspace/api
./server.scm
```

The server will start on `http://localhost:8080`

### Test the API

```bash
# Health check
curl http://localhost:8080/health

# Login and get capability token
curl -X POST http://localhost:8080/auth/login \
  -H "Content-Type: application/json" \
  -d '{"username":"alice","password":"secret"}'

# Search library
curl "http://localhost:8080/library/search?q=lamport"

# Get library catalog
curl http://localhost:8080/library/catalog
```

### Run Test Suite

```bash
./test-api.sh
```

## API Endpoints

### Health Check

**GET /health**

Check server status.

**Response:**
```json
{
  "status": "healthy",
  "version": "1.0.0",
  "timestamp": 1234567890
}
```

### Authentication

**POST /auth/login**

Authenticate and receive capability token.

**Request:**
```json
{
  "username": "alice",
  "password": "secret"
}
```

**Response:**
```json
{
  "capability": "user123:read-library,use-crypto:secret:1234567890:signature",
  "expires": 3600,
  "rights": ["read-library", "use-crypto"]
}
```

**POST /auth/verify**

Verify capability token.

**Request:**
```json
{
  "capability": "user123:read-library,use-crypto:..."
}
```

**Response:**
```json
{
  "valid": true,
  "rights": ["read-library", "use-crypto"]
}
```

### Library

**GET /library/search?q=<query>**

Search papers by keyword, author, topic.

**Parameters:**
- `q` - Search query string

**Response:**
```json
{
  "query": "lamport",
  "results": [
    {
      "id": "lamport-1979-signatures",
      "title": "Constructing Digital Signatures from a One-Way Function",
      "category": "cryptographers",
      "year": "1979",
      "path": "cryptographers/lamport-1979-signatures.pdf"
    }
  ],
  "count": 1
}
```

**GET /library/catalog**

List all papers in library.

**Response:**
```json
{
  "catalog": [
    {
      "id": "lamport-1979-signatures",
      "title": "Constructing Digital Signatures from a One-Way Function",
      "category": "cryptographers",
      "year": "1979",
      "path": "cryptographers/lamport-1979-signatures.pdf"
    }
  ],
  "count": 42
}
```

**GET /library/papers/<paper-id>**

Retrieve paper metadata.

**Response:**
```json
{
  "id": "lamport-1979-signatures",
  "title": "Constructing Digital Signatures from a One-Way Function",
  "category": "cryptographers",
  "year": "1979",
  "path": "cryptographers/lamport-1979-signatures.pdf",
  "full_path": "/Users/ddp/cyberspace/library/cryptographers/lamport-1979-signatures.pdf"
}
```

### Cryptography

**POST /crypto/lamport/keygen**

Generate Lamport signature keypair.

**Request:**
```json
{
  "bits": 256
}
```

**Response:**
```json
{
  "private_key": "...",
  "public_key": "...",
  "bits": 256
}
```

**POST /crypto/lamport/sign**

Sign message with Lamport signature.

**Request:**
```json
{
  "private_key": "...",
  "message": "Hello, Cyberspace!"
}
```

**Response:**
```json
{
  "signature": "...",
  "warning": "Lamport keypair now used - do not reuse!"
}
```

**POST /crypto/lamport/verify**

Verify Lamport signature.

**Request:**
```json
{
  "public_key": "...",
  "message": "Hello, Cyberspace!",
  "signature": "..."
}
```

**Response:**
```json
{
  "valid": true
}
```

**POST /crypto/chacha20/encrypt**

Encrypt with ChaCha20 stream cipher.

**Request:**
```json
{
  "key": "0000000000000000000000000000000000000000000000000000000000000000",
  "nonce": "000000000000000000000000",
  "plaintext": "Hello, Cyberspace!"
}
```

**Response:**
```json
{
  "ciphertext": "3edd8cc1cfdd1dd3..."
}
```

**POST /crypto/chacha20/decrypt**

Decrypt with ChaCha20 stream cipher.

**Request:**
```json
{
  "key": "0000000000000000000000000000000000000000000000000000000000000000",
  "nonce": "000000000000000000000000",
  "ciphertext": "3edd8cc1cfdd1dd3..."
}
```

**Response:**
```json
{
  "plaintext": "Hello, Cyberspace!"
}
```

**POST /crypto/merkle/build**

Build Merkle tree.

**Request:**
```json
{
  "items": ["alice", "bob", "carol", "dave"]
}
```

**Response:**
```json
{
  "root": "abc123...",
  "tree": {...}
}
```

**POST /crypto/merkle/prove**

Generate inclusion proof.

**Request:**
```json
{
  "tree": {...},
  "item": "bob"
}
```

**Response:**
```json
{
  "proof": [...],
  "root": "abc123..."
}
```

**POST /crypto/merkle/verify**

Verify inclusion proof.

**Request:**
```json
{
  "root": "abc123...",
  "item": "bob",
  "proof": [...]
}
```

**Response:**
```json
{
  "valid": true
}
```

### Implementations

**GET /impl/list**

List all implementations.

**Response:**
```json
{
  "implementations": [
    {
      "name": "lamport-otp",
      "status": "complete",
      "description": "Hash-chain authentication",
      "paper": "Lamport 1981"
    },
    {
      "name": "merkle-tree",
      "status": "complete",
      "description": "Authenticated data structures",
      "paper": "Merkle 1979"
    }
  ],
  "count": 5
}
```

**GET /impl/<name>/info**

Get implementation details.

**Response:**
```json
{
  "name": "lamport-otp",
  "status": "complete",
  "description": "Hash-chain authentication from Lamport 1981",
  "path": "/Users/ddp/cyberspace/implementations/lamport-otp",
  "readme": "... README content ..."
}
```

**POST /impl/<name>/demo**

Run implementation demo.

**Request:**
```json
{
  "demo": "basic",
  "args": {...}
}
```

**Response:**
```json
{
  "output": "... demo output ..."
}
```

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

## Client Examples

### Python

```python
import requests

# Login
resp = requests.post('http://localhost:8080/auth/login',
                     json={'username': 'alice', 'password': 'secret'})
capability = resp.json()['capability']

# Search library
resp = requests.get('http://localhost:8080/library/search?q=lamport',
                    headers={'Authorization': f'Capability {capability}'})
papers = resp.json()['results']

# Encrypt with ChaCha20
resp = requests.post('http://localhost:8080/crypto/chacha20/encrypt',
                     headers={'Authorization': f'Capability {capability}'},
                     json={
                         'key': '00' * 32,
                         'nonce': '00' * 12,
                         'plaintext': 'Hello, Cyberspace!'
                     })
ciphertext = resp.json()['ciphertext']
```

### JavaScript

```javascript
// Login
const loginResp = await fetch('http://localhost:8080/auth/login', {
  method: 'POST',
  headers: {'Content-Type': 'application/json'},
  body: JSON.stringify({username: 'alice', password: 'secret'})
});
const {capability} = await loginResp.json();

// Search library
const searchResp = await fetch('http://localhost:8080/library/search?q=merkle', {
  headers: {'Authorization': `Capability ${capability}`}
});
const {results} = await searchResp.json();
```

### Curl

```bash
# Login
TOKEN=$(curl -X POST http://localhost:8080/auth/login \
  -H "Content-Type: application/json" \
  -d '{"username":"alice","password":"secret"}' | jq -r '.capability')

# Search library
curl -H "Authorization: Capability $TOKEN" \
  "http://localhost:8080/library/search?q=lamport"

# Generate Lamport keypair
curl -X POST -H "Authorization: Capability $TOKEN" \
  -H "Content-Type: application/json" \
  -d '{"bits": 256}' \
  http://localhost:8080/crypto/lamport/keygen
```

## Development

### Project Structure

```
api/
├── server.scm              # Main HTTP server
├── routes/
│   ├── library.scm         # Library endpoints
│   ├── crypto.scm          # Crypto endpoints
│   ├── impl.scm            # Implementation endpoints
│   └── auth.scm            # Authentication endpoints
├── guards/
│   ├── auth.scm            # Capability verification
│   ├── rate-limit.scm      # Rate limiting
│   └── logging.scm         # Request logging
├── test-api.sh             # Test suite
└── README.md               # This file
```

### Dependencies

**Chicken Scheme Eggs:**
- `spiffy` - HTTP server
- `intarweb` - HTTP request/response handling
- `uri-common` - URI parsing
- `medea` - JSON parsing

**Install:**
```bash
chicken-install spiffy intarweb uri-common medea
```

### Running the Server

```bash
# Start server
./server.scm

# Start on custom port
PORT=3000 ./server.scm
```

### Testing

```bash
# Run test suite
./test-api.sh

# Manual testing
curl http://localhost:8080/health
```

## Security

**Capability-Based Security:**
- ✓ Unforgeable tokens (HMAC-signed)
- ✓ Time-limited (expiry timestamps)
- ✓ Attenuatable (delegate subset of rights)
- ✓ No ambient authority (must present capability)

**Transport Security:**
- ✓ TLS 1.3 with ChaCha20-Poly1305 (planned)
- ✓ CORS headers for browser access
- ✓ Input validation

**Rate Limiting:**
- Per-capability limits (planned)
- Adaptive based on load (planned)

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
│  │ - catalog    │  │ - merkle/build      │ │
│  └──────────────┘  │ - capabilities/     │ │
│                    │   create            │ │
│  ┌──────────────┐  └─────────────────────┘ │
│  │    /impl     │                           │
│  │              │  ┌─────────────────────┐ │
│  │ - list       │  │       /auth         │ │
│  │ - demo       │  │                     │ │
│  │ - info       │  │ - login             │ │
│  └──────────────┘  │ - verify            │ │
│                    └─────────────────────┘ │
└─────────────────────────────────────────────┘
```

## License

Public domain. Based on foundational research from Lamport, Lampson, Bernstein, Merkle, and others.

---

**"An API that demonstrates the principles it serves."**

- Capability-based authentication (Lampson 1971)
- ChaCha20-Poly1305 AEAD (Bernstein 2005-2008)
- Merkle proofs (Merkle 1979)
- Lamport signatures (Lamport 1979)

**Research → Practice → API**
