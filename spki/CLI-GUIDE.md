# SPKI CLI Tools: Game Night Quick Start

**Use SPKI certificates for peer-to-peer authorization without hierarchical CAs.**

## Installation

```bash
cd ~/cyberspace/spki
make install
```

This installs four commands to `~/bin/`:
- `spki-keygen` - Generate keypair
- `spki-cert` - Create and sign certificates
- `spki-verify` - Verify certificate chains
- `spki-show` - Display certificates in human-readable format

## Quick Workflow: D&D Session 0

### 1. Everyone Generates Keys

```bash
# At game night, each player generates their keypair
spki-keygen --name alice
# Output:
#   Generating SPKI keypair...
#   Public key hash: 8QVbRG6SV3FKb7FU7I8okdqN+8VT2qL9VhRVSJoV5bg=
#   Private key saved to: alice.private
#   Public key saved to: alice.public
```

**Share your public key hash with the group** (write it down, QR code it, etc.)

### 2. Alice Delegates to Bob

```bash
# Alice wants to let Bob read her research library
spki-cert --issuer alice.private \
          --subject bob.public \
          --tag '(read (path /Users/alice/library/lamport-papers))' \
          --not-before 2026-01-01T00:00:00Z \
          --not-after 2027-01-01T00:00:00Z \
          --output alice-to-bob.cert

# Output: Certificate saved to: alice-to-bob.cert
```

### 3. Verify Bob Has Permission

```bash
# Anyone can verify the certificate chain
spki-verify --root alice.public \
            --chain alice-to-bob.cert \
            --tag '(read (path /Users/alice/library/lamport-papers))'

# Output:
#   Verifying certificate chain...
#   ✓ VALID: Certificate chain grants authorization
```

### 4. Inspect Certificates

```bash
# Human-readable display
spki-show alice-to-bob.cert

# Output:
#   SPKI Certificate
#   ================
#
#   Issuer:     Key (hash: 8QVbRG6SV3FKb7FU7I8okdqN+8VT2qL9VhRVSJoV5bg=)
#   Subject:    Key (hash: SZMDHbSUswbHSUsXXmGE2ACK8JINh8Zwg98Sw8xg9mg=)
#   Tag:        (read (path /Users/alice/library/lamport-papers))
#   Validity:   2026-01-01T00:00:00Z to 2027-01-01T00:00:00Z
#   Propagate:  no
```

## Example Tags

Authorization tags are s-expressions describing capabilities:

```lisp
; Read access
(read (path /library/lamport-papers))

; Write access
(write (path /shared/notes))

; Spawn agents
(spawn-agent (max-count 5))

; SSH access
(ssh (host moria.eludom.net) (user alice))

; All permissions (use carefully!)
(*)
```

## Delegation Chains

Alice can delegate to Bob, who can delegate to Carol:

```bash
# Alice to Bob (with propagate)
spki-cert --issuer alice.private \
          --subject bob.public \
          --tag '(read (path /data))' \
          --propagate \
          --output alice-to-bob.cert

# Bob to Carol (no propagate - chain ends here)
spki-cert --issuer bob.private \
          --subject carol.public \
          --tag '(read (path /data))' \
          --output bob-to-carol.cert

# Verify Carol has permission via chain
spki-verify --root alice.public \
            --chain alice-to-bob.cert \
            --chain bob-to-carol.cert \
            --tag '(read (path /data))'
```

## Security Notes

### Keep Private Keys Secret
- `*.private` files contain your signing authority
- Don't share them, don't commit them to git
- Store them encrypted if possible

### Share Public Keys Freely
- `*.public` files are meant to be shared
- Verify key hashes in person at game night
- Exchange via QR code, USB stick, or secure messaging

### Certificate Files
- `*.cert` files are signed authorizations
- They can be shared publicly
- Anyone can verify them (human-readable s-expressions)

## File Organization

Suggested directory structure for your enclave:

```
~/spki-keys/
├── alice.private          # Your private key (SECRET)
├── alice.public           # Your public key (share freely)
├── friends/
│   ├── bob.public
│   ├── carol.public
│   └── dave.public
└── certs/
    ├── alice-to-bob.cert
    ├── alice-to-carol.cert
    └── bob-to-carol.cert
```

## Troubleshooting

**"dune not found"**
```bash
opam init
opam install dune cryptokit base64 alcotest
```

**"Invalid signature"**
- Check that issuer and subject keys match
- Verify certificate wasn't modified after signing
- Ensure you're using the correct public key for verification

**"Chain break: issuer doesn't match"**
- In a chain, each cert's subject must match the next cert's issuer
- Order matters: `alice→bob→carol`, not `alice→carol→bob`

## Advanced: Integration with SSH

You can use SPKI certs to authorize SSH access:

```bash
# Alice delegates SSH access to Bob
spki-cert --issuer alice.private \
          --subject bob.public \
          --tag '(ssh (host moria.eludom.net) (user alice))' \
          --output ssh-alice-to-bob.cert

# In ~/.ssh/authorized_keys wrapper script:
# #!/bin/bash
# spki-verify --root trusted-keys/alice.public \
#             --chain certs/ssh-alice-to-bob.cert \
#             --tag "(ssh (host $(hostname)) (user $USER))"
# if [ $? -eq 0 ]; then
#   # Allow SSH connection
#   cat alice-authorized-keys
# fi
```

## Philosophy

**SPKI is designed for small groups with direct trust relationships.**

- **No CAs**: You don't need a certificate authority
- **Peer-to-peer**: Direct delegation between friends
- **Human-readable**: All certificates are s-expressions you can inspect
- **Authorization-centric**: Certificates say "what you can do", not "who you are"
- **Decentralized**: No single point of control or failure

Perfect for D&D groups, maker spaces, research collaborations, and intentional communities.

---

**Part of the Cyberspace Project**
**Peace for All Mankind: Cooperative Computing Without Enclosure**

*Questions? Check SPKI RFC 2693 or the main README.md*
