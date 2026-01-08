# RFC-040: Cyberspace Security Architecture

**Status:** Draft
**Date:** January 2026
**Author:** Derrell Piper <ddp@eludom.net>
**Requires:** RFC-004 (SPKI Authorization), RFC-007 (Threshold Governance), RFC-037 (Node Roles)

---

## Abstract

This document defines how cyberspace protects itself. The model is simple: **capabilities all the way down**. Objects are content. Authorization flows through signed certificates. No labels, no ACLs, no ambient authority. You hold a capability or you don't.

We use the rigor of TCSEC B2 as a lens - particularly for covert channel analysis - but cyberspace is its own thing. This is our security architecture, in our language.

---

## The Axioms

```
A1. No Ambient Authority
    You have nothing until someone gives you something.
    Every access requires presenting a capability.

A2. Capabilities Are Unforgeable
    Ed25519 signatures. No exceptions.
    Create by origin or delegation. No other path.

A3. Capabilities Only Attenuate
    Delegation can reduce rights, never amplify.
    What you give cannot exceed what you hold.

A4. Objects Are Immutable Content
    SHA-512 hash IS identity.
    No metadata. No labels. No ACLs.
    Objects don't know who can access them.
```

---

## The Realm

A realm is your place in cyberspace. It is sovereign.

```
┌─────────────────────────────────────────────────────────────┐
│                        YOUR REALM                            │
│                                                              │
│   Principal: ed25519:a1b2c3...  (this is you)               │
│                                                              │
│   ┌──────────────────────────────────────────────────────┐  │
│   │                      VAULT                            │  │
│   │  Objects:     content-addressed, signed               │  │
│   │  Capabilities: certificates you hold                  │  │
│   │  Audit:       what happened here                      │  │
│   └──────────────────────────────────────────────────────┘  │
│                                                              │
│   Trust boundary: your signing key                          │
│   You decide: what to store, who to trust, what to share    │
└─────────────────────────────────────────────────────────────┘
```

Your realm is local-first. Federation is optional. When you federate, realms overlap - objects flow according to capability chains. But your realm remains yours.

---

## Capabilities

### The Certificate

```scheme
(spki-cert
  (issuer "ed25519:alice...")        ; Who grants
  (subject "ed25519:bob...")         ; Who receives
  (tag (read "sha512:doc..."))       ; What: read this object
  (valid (not-after 1736400000))     ; When: expires in 24h
  (propagate #f)                     ; Bob cannot delegate
  (signature "ed25519:..."))         ; Alice's signature
```

### Access Check

```
Can Bob read sha512:doc?

1. Does Bob hold a cert granting (read "sha512:doc")?
2. Is the signature valid?
3. Is it expired?
4. Is it revoked?
5. Does the chain trace to someone who could grant it?

All yes? Access granted.
Any no?  Access denied.
```

### Delegation

Alice can give Bob read access:
```scheme
(spki-cert
  (issuer "ed25519:alice...")
  (subject "ed25519:bob...")
  (tag (read "sha512:doc..."))
  (propagate #t))                    ; Bob CAN delegate
```

Bob can give Carol read access (because Alice allowed propagation):
```scheme
(spki-cert
  (issuer "ed25519:bob...")
  (subject "ed25519:carol...")
  (tag (read "sha512:doc..."))
  (propagate #f))                    ; Carol cannot delegate further
```

Carol cannot give anyone else access. The chain stops.

---

## Classification Without Labels

Traditional MAC puts labels on objects: UNCLASSIFIED, SECRET, TOP SECRET.

In cyberspace, classification is a capability you hold:

```scheme
;; Security officer grants SECRET clearance
(spki-cert
  (issuer "ed25519:security-officer...")
  (subject "ed25519:analyst...")
  (tag (clearance secret))
  (valid (not-after 1767225600)))    ; Annual renewal

;; Program manager grants compartment access
(spki-cert
  (issuer "ed25519:program-manager...")
  (subject "ed25519:engineer...")
  (tag (compartment "project-atlas")))
```

Access to a classified object requires:
1. Capability to read the object itself
2. Appropriate clearance capability
3. All required compartment capabilities

The object has no labels. The policy lives in the certificates.

---

## The Trusted Core

What must work correctly for security to hold:

| Component | What It Does | What We Trust |
|-----------|--------------|---------------|
| Ed25519 | Signatures | libsodium, math |
| SHA-512 | Object identity | libsodium, math |
| Capability verifier | Chain validation | Our code |
| Vault storage | Object integrity | Local filesystem |
| Audit chain | What happened | Hash chain, signatures |

The core is small. Objects are dumb content. Policy lives in certificates. Verification is stateless computation.

---

## Covert Channels

This is where we get serious.

A covert channel is information flow that violates policy - a way to leak data that bypasses the capability model. They exist in every system. We analyze ours.

### Storage Channels

| Channel | How It Works | Bandwidth | Mitigation |
|---------|-------------|-----------|------------|
| Object existence | Create/don't create object as 1/0 | ~1 bit/op | Bloom filter noise |
| Object size | Encode in padding | ~10 bits/obj | Size quantization |
| Object count | Number of objects in namespace | ~4 bits/ns | Rate limiting |

### Timing Channels

| Channel | How It Works | Bandwidth | Mitigation |
|---------|-------------|-----------|------------|
| Verification time | Slow/fast response as 1/0 | ~1 bit/100ms | Constant-time ops |
| Network latency | Delay patterns | ~10 bits/sec | Batching, Tor |
| Audit write time | When entries appear | ~1 bit/sec | Async, batched |

### Federation Channels

| Channel | How It Works | Bandwidth | Mitigation |
|---------|-------------|-----------|------------|
| Sync timing | When objects replicate | ~1 bit/sync | Random delays |
| Peer selection | Which realms to contact | ~4 bits/conn | Randomized peers |
| Gossip patterns | Propagation paths | ~2 bits/round | Epidemic flooding |

### Analysis

**Scenario:** Alice has SECRET access. Bob has UNCLASSIFIED. Alice wants to leak to Bob.

**Via storage:**
Alice creates/deletes objects Bob can see. Each operation signals one bit. Rate: maybe 1 bit/second with careful timing.

**Via timing:**
Alice influences verification time of requests Bob makes. Bob measures. Rate: maybe 0.1 bit/second, noisy.

**Via federation:**
Alice causes sync events Bob can observe. Rate: depends on federation config, maybe 0.01 bit/second.

**Assessment:**
Total covert bandwidth: ~1-2 bits/second under ideal conditions. Not enough for bulk data. Enough for short signals. Acceptable residual risk for our threat model.

### Mitigation Principles

```
1. Add noise where practical (bloom filters, random delays)
2. Quantize where observable (object sizes, batch windows)
3. Rate limit where controllable (operations per time)
4. Accept what remains (document it, move on)
```

---

## Audit

Everything important gets logged.

```scheme
(audit-entry
  (sequence 12345)
  (timestamp 1736300000)
  (lamport 67890)
  (type capability-exercise)
  (actor "ed25519:subject...")
  (action (read "sha512:object..."))
  (capability "sha512:cert...")
  (previous "sha512:prev-entry...")
  (signature "ed25519:auditor..."))
```

**Properties:**
- Hash-chained: tamper-evident
- Signed: non-repudiable
- Monotonic: gaps detected
- Distributed: witnesses replicate

**What gets logged:**
- Capability creation
- Capability exercise (access)
- Capability revocation
- Access denials
- Object creation
- Realm events (role changes, federation)

---

## Trusted Path

When it matters, talk directly to the core.

```
┌──────────────────────────────────────┐
│           HUMAN OPERATOR              │
└─────────────────┬────────────────────┘
                  │ Local terminal, no network
┌─────────────────▼────────────────────┐
│          CYBERSPACE REPL              │
│    ╔═════════════════════════════╗   │
│    ║  TRUSTED PATH ACTIVE        ║   │
│    ╚═════════════════════════════╝   │
└─────────────────┬────────────────────┘
                  │
┌─────────────────▼────────────────────┐
│           TRUSTED CORE                │
└──────────────────────────────────────┘
```

Operations requiring trusted path:
- `(ed25519-keypair)` - key generation
- `(node-role 'coordinator)` - role assignment
- `(seal-release "1.0.0")` - signing releases
- Key ceremony (RFC-022)

---

## Threats

### What We Handle

| Threat | Defense |
|--------|---------|
| Unauthorized access | No capability = no access |
| Capability forgery | Ed25519 signatures |
| Replay attacks | Timestamps, nonces, Lamport clocks |
| Stale capabilities | Expiration, revocation |
| Delegation abuse | Attenuation, propagation flags |
| Content tampering | SHA-512 content addressing |
| Origin spoofing | Object signatures |
| Audit tampering | Hash chain, distribution |

### What We Don't Handle

| Threat | Why |
|--------|-----|
| Compromised signing key | Fundamental limit. Mitigate: threshold, rotation. |
| Endpoint compromise | Your realm, your problem. |
| Physical access | Out of scope for software. |
| Covert channels > 1 bit/sec | Residual risk, documented above. |
| Availability attacks | Focus on integrity/confidentiality. |
| Quantum computing | Ed25519 vulnerable. Migration path planned. |
| Coercion | Math doesn't help if you're forced to sign. |

---

## The Invariants

These must always hold:

```
I1. No access without valid capability
    access(s,o,r) → ∃c: valid_chain(s,o,r,c)

I2. Delegation cannot amplify
    delegated(c₂,c₁) → rights(c₂) ⊆ rights(c₁)

I3. Object identity is content hash
    id(o) = sha512(content(o))

I4. Audit is ordered
    sequence(e₁) < sequence(e₂) → time(e₁) ≤ time(e₂)

I5. Revocation is permanent
    revoked(c,t) → ∀t' > t: ¬valid(c,t')

I6. No ambient authority
    ¬∃c: grants(c,*,*)
```

---

## References

1. Ellison, C. et al., SPKI Certificate Theory, RFC 2693, 1999
2. Dennis, J. & Van Horn, E., Programming Semantics for Multiprogrammed Computations, 1966
3. Miller, M., Robust Composition, 2006
4. Lampson, B., A Note on the Confinement Problem, 1973
5. DoD 5200.28-STD (Orange Book), 1985 - for the covert channel lens

---

## Changelog

- 2026-01-08 - Initial draft
