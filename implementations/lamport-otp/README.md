# Lamport One-Time Password System

**Practical implementation of Leslie Lamport's 1981 hash-chain authentication**

From the paper: *"Password Authentication with Insecure Communication"*
Source: `~/cyberspace/library/cryptographers/nrl-one-time-passwords/lamport-password-authentication-1981.pdf`

## The Concept

Lamport's elegant solution to authentication over insecure channels:

```
Seed → H(seed) → H²(seed) → H³(seed) → ... → Hⁿ(seed)
         ↑          ↑          ↑                 ↑
       Pass 3     Pass 2    Pass 1          Server stores

Use passwords in REVERSE order (most-hashed first)
```

**Security Properties:**
- ✓ **One-time use**: Each password valid only once
- ✓ **Forward secure**: Old passwords don't reveal future ones
- ✓ **Eavesdrop resistant**: Captured passwords can't be reused
- ✗ **Finite**: Chain exhausts after N uses (must regenerate)

## Quick Start

```bash
# Generate 100 passwords for alice
./lamport.scm generate alice "my-secret-seed-xyz" 100

# This creates:
#   alice.lamport          (server-side chain state)
#   alice-passwords.txt    (printable password book for client)

# Verify a password (server-side)
./lamport.scm verify alice 5f4dcc3b5aa765d61d8327deb882cf99...

# Check how many passwords remain
./lamport.scm status alice
```

## How It Works

### 1. Chain Generation (Client)

```scheme
seed = "my-secret-phrase"
N = 100

chain[0]   = H¹⁰⁰(seed)  ; Most hashed
chain[1]   = H⁹⁹(seed)
chain[2]   = H⁹⁸(seed)
...
chain[99]  = H¹(seed)    ; Least hashed
```

### 2. Authentication Flow

```
Client                          Server
------                          ------
                               Stores: H(password[0])

Login with password[0] ─────→  Verifies: H(received) = stored
                               ✓ Match!
                               Updates: stored = received

Login with password[1] ─────→  Verifies: H(received) = stored
                               ✓ Match!
                               Updates: stored = received
```

### 3. Security Against Eavesdropper

```
Attacker captures: password[5] = H⁹⁵(seed)

Can compute:
  ✓ H(password[5])   = H⁹⁶(seed) = password[4] (already used)
  ✓ H²(password[5])  = H⁹⁷(seed) = password[3] (already used)

Cannot compute:
  ✗ H⁻¹(password[5]) = H⁹⁴(seed) = password[6] (hash not reversible!)
```

**Result:** Attacker cannot derive future passwords from captured ones.

## Use Cases

### 1. Remote Access to Untrusted Terminals

```bash
# Generate passwords at home on trusted machine
./lamport.scm generate alice "secret" 50

# Print password book, carry in wallet
cat alice-passwords.txt

# At internet cafe (untrusted keyboard/network):
# Use password 0, cross it off
# Even if keylogger captures it, can't reuse or compute next password
```

### 2. Low-Entropy Shared Secrets

```bash
# Seed can be simple phrase both parties remember
./lamport.scm generate bob "pizza-2pm-tuesday" 100

# No need to securely distribute complex keys
# Just agree on a seed phrase in person
```

### 3. Limited-Duration Access

```bash
# Grant contractor 20 logins
./lamport.scm generate contractor "temp-access" 20

# When chain exhausts, access automatically revoked
# No need to remember to disable account
```

## File Formats

### Server State (`username.lamport`)

```scheme
((username . "alice")
 (length . 100)
 (current . 5)      ; Next password index to use
 (chain . ((0 "a8f3b...") (1 "9c2d4...") ...)))
```

### Password Book (`username-passwords.txt`)

```
╔═══════════════════════════════════════════════════════════════════╗
║           LAMPORT ONE-TIME PASSWORD BOOK                          ║
╠═══════════════════════════════════════════════════════════════════╣
║  User: alice                                                      ║
║  Passwords: 100                                                   ║
╠═══════════════════════════════════════════════════════════════════╣
║  USE PASSWORDS IN ORDER FROM TOP TO BOTTOM                        ║
║  Each password can only be used ONCE                              ║
╚═══════════════════════════════════════════════════════════════════╝

  0: a8f3b2c1d9e4f5a6b7c8d9e0f1a2b3c4d5e6f7a8b9c0d1e2f3a4b5c6d7e8
  1: 9c2d4e6f8a0b2c4d6e8f0a2b4c6d8e0f2a4b6c8d0e2f4a6b8c0d2e4f6a8b
  2: 7e1f3a5b7c9d0e2f4a6b8c0d2e4f6a8b0c2d4e6f8a0b2c4d6e8f0a2b4c6
  ...
```

## Comparison to Other OTP Systems

| System | Hash Chain | Shared Secret | Time-Based | Hardware Token |
|--------|-----------|---------------|------------|----------------|
| Lamport (1981) | ✓ | Seed phrase | ✗ | ✗ |
| S/KEY (Bellcore 1995) | ✓ | Passphrase | ✗ | ✗ |
| OPIE (NRL 1995) | ✓ | Passphrase | ✗ | ✗ |
| TOTP (Google Auth) | ✗ | Shared key | ✓ | Optional |
| HOTP (RFC 4226) | ✗ | Shared key | ✗ (counter) | Usually |

**Lamport Advantages:**
- Simplest concept (just hash repeatedly)
- No clock synchronization
- No special hardware needed
- Can compute entire chain offline

**Lamport Disadvantages:**
- Finite (chain exhausts)
- Need to carry password list
- No mutual authentication

## Implementation Notes

### Hash Function

Currently uses SHA-256 via OpenSSL:

```bash
echo -n "text" | openssl dgst -sha256 -hex
```

**Why SHA-256?**
- Cryptographically secure (collision-resistant)
- Widely available
- Standardized (NIST FIPS 180-4)
- Fast enough for chain generation

**Lamport's original paper** suggested using DES in a one-way mode. Modern practice uses SHA-2 or SHA-3 family hashes.

### Performance

On modern hardware:
- **100 password chain**: ~1 second
- **1000 password chain**: ~10 seconds

Parallelizable: Each hash in chain independent until final composition.

## Security Considerations

### ✓ Secure Against

1. **Passive eavesdropping**: Captured passwords useless
2. **Replay attacks**: Each password one-time use
3. **Dictionary attacks on captured passwords**: Hash is one-way
4. **Compromised server**: Doesn't reveal future passwords

### ✗ Vulnerable To

1. **Active man-in-the-middle**: Can manipulate challenges/responses
2. **Stolen password book**: If attacker gets physical book, game over
3. **Seed compromise**: If seed revealed, entire chain compromised
4. **Server impersonation**: No mutual authentication

### Mitigations

- Use strong seed (high entropy)
- Protect password book physically
- Use with TLS for transport security
- Combine with server certificates for mutual auth

## Extensions & Improvements

### S/KEY (1995)

Bellcore's improvement over Lamport:
- Uses dictionary words instead of hex hashes
- 6 short words easier to type than 64-character hex
- Example: "RIFT COOK ADAM MILK BEAD SANG"

### OPIE (1995)

NRL's implementation:
- Compatible with S/KEY
- Multiple hash algorithms
- Better seed generation
- Integrated with Unix login

See: `~/cyberspace/library/cryptographers/nrl-one-time-passwords/`

## Research Lineage

```
Lamport (1981)
"Password Authentication with Insecure Communication"
    ↓
Haller (1994)
S/KEY: Bellcore implementation
    ↓
NRL (1995)
OPIE: One-time Passwords In Everything
    ↓
IETF RFC 1938 (1996)
S/KEY standardization
    ↓
IETF RFC 2289 (1998)
Generic OTP specification
```

**40+ years** of hash-chain authentication research and deployment.

## Educational Value

This implementation demonstrates:

1. **Cryptographic Hash Properties**
   - One-way functions
   - Collision resistance
   - Avalanche effect

2. **Security Protocol Design**
   - Challenge-response authentication
   - Forward security
   - Replay attack prevention

3. **Practical Cryptography**
   - Key management
   - Usability vs security tradeoffs
   - Offline computation

## Modern Relevance

While TOTP (Time-based OTP) has largely replaced hash-chain OTPs for 2FA, Lamport's concepts live on:

- **Blockchain**: Hash chains for immutability
- **Git**: Commit chains are hash chains
- **Merkle Trees**: Generalization of hash chaining
- **Certificate Transparency**: Hash-based append-only logs

**The idea that inspired 40 years of research.**

## Files

```
lamport-otp/
├── README.md          (this file)
├── lamport.scm        (implementation)
└── examples/          (usage examples)
```

## Dependencies

- Chicken Scheme 5.x
- OpenSSL (for SHA-256)

## License

Public domain. Based on Lamport's 1981 paper (foundational research).

---

**"Simple ideas, profound impact."**
—The essence of Lamport's contribution to cryptography
