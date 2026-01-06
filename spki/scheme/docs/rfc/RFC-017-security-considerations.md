# RFC-017: Security Considerations

**Status:** Active
**Date:** January 2026
**Author:** Derrell Piper <ddp@eludom.net>

---

## Abstract

This RFC documents security considerations for the Library of Cyberspace, including threat models, trust boundaries, auditable events, and security-critical operations. This is a living document that accumulates security-relevant information as the system evolves.

---

## Trust Boundaries

### Trusted Computing Base (TCB)

The TCB is minimal and implemented in OCaml (RFC-014):

```
┌─────────────────────────────────────────┐
│              TRUSTED                     │
│  ┌─────────────────────────────────┐    │
│  │  Ed25519 signatures (libsodium) │    │
│  │  SHA-512 hashing (libsodium)    │    │
│  │  Signature chain verification   │    │
│  └─────────────────────────────────┘    │
│           ~1000 lines OCaml              │
└─────────────────────────────────────────┘
              │
              │ FFI boundary
              ▼
┌─────────────────────────────────────────┐
│            UNTRUSTED                     │
│  Everything else (Chicken Scheme)       │
│  - Vault operations                     │
│  - Replication                          │
│  - Directory system                     │
│  - User interface                       │
└─────────────────────────────────────────┘
```

### Trust Model by Component

| Component | Trust Level | Notes |
|-----------|-------------|-------|
| libsodium | High | Audited, widely deployed |
| OCaml TCB | High | Verified (Coq extraction) |
| Scheme FFI | Medium | Small, auditable |
| Vault operations | Medium | Scheme, type-checked |
| Network transport | Low | Assume adversarial |
| User input | Low | Validate everything |
| Peer nodes | Configurable | SPKI certificates |

---

## Auditable Events

All security-relevant operations must be recorded in the audit trail.

### Category: Cryptographic Operations

| Event | Severity | Data Recorded |
|-------|----------|---------------|
| `key-generate` | HIGH | Public key hash, algorithm, timestamp |
| `key-import` | HIGH | Public key hash, source, timestamp |
| `key-export` | CRITICAL | Public key hash, destination, authorization |
| `signature-create` | MEDIUM | Document hash, signer, timestamp |
| `signature-verify` | LOW | Document hash, signer, result, timestamp |
| `hash-compute` | LOW | Input length, algorithm, output hash |

### Category: Vault Operations

| Event | Severity | Data Recorded |
|-------|----------|---------------|
| `seal-commit` | MEDIUM | Commit hash, author, message, files changed |
| `seal-release` | HIGH | Version, commit hash, signer, signature |
| `seal-rollback` | HIGH | From version, to version, reason, authorizer |
| `seal-archive` | MEDIUM | Version, format, output path, hash |
| `seal-restore` | HIGH | Archive path, verification status, target |
| `seal-verify` | LOW | Version, verification result, verifier key |

### Category: Replication

| Event | Severity | Data Recorded |
|-------|----------|---------------|
| `seal-publish` | HIGH | Version, remote, archive hash, result |
| `seal-subscribe` | MEDIUM | Remote, versions received, verification status |
| `seal-synchronize` | HIGH | Remote, direction, versions exchanged |
| `sync` | LOW | Master node, status, commits synced |

### Category: Authorization

| Event | Severity | Data Recorded |
|-------|----------|---------------|
| `cert-create` | HIGH | Issuer, subject, tag, validity, propagate |
| `cert-sign` | HIGH | Certificate hash, signer |
| `cert-verify` | MEDIUM | Certificate hash, result, verifier |
| `chain-verify` | MEDIUM | Chain length, root key, target tag, result |
| `threshold-sign` | HIGH | Script hash, signer, threshold progress |
| `threshold-verify` | HIGH | Script hash, threshold, signers, result |

### Category: Cluster Operations

| Event | Severity | Data Recorded |
|-------|----------|---------------|
| `peer-register` | MEDIUM | Peer URI, public key, trust level |
| `peer-remove` | MEDIUM | Peer URI, reason |
| `lazy-push` | LOW | Peer, versions pushed |
| `lazy-pull` | LOW | Peer, versions received |
| `conflict-detect` | HIGH | Version, local hash, remote hash |
| `conflict-resolve` | HIGH | Version, resolution method, authorizer |

### Category: Administrative

| Event | Severity | Data Recorded |
|-------|----------|---------------|
| `vault-init` | HIGH | Root path, signing key configured |
| `config-change` | MEDIUM | Key, old value hash, new value hash |
| `audit-export` | LOW | Format, output path, entry count |
| `audit-verify` | LOW | Entry range, verification result |

---

## Audit Entry Format

```scheme
(audit-entry
  (type <event-type>)
  (severity <HIGH|MEDIUM|LOW|CRITICAL>)
  (timestamp "2026-01-06 15:30:45")
  (epoch 1736178645)
  (actor #${public-key} or "system")
  (action (<verb> <object> <parameters>...))
  (context
    (motivation "Human-readable reason")
    (relates-to <previous-entry-id>))
  (result <success|failure|partial>)
  (details ...)
  (seal
    (algorithm "ed25519-sha512")
    (hash "sha512:...")
    (signature "...")))
```

---

## Threat Model

### Adversary Capabilities

**Assumed capabilities:**
- Network eavesdropping
- Network message injection
- Compromised peer nodes (up to f in 3f+1)
- Physical access to storage (offline)
- Unlimited computation (for brute force)

**Not assumed:**
- Quantum computers (Ed25519 vulnerable)
- Compromise of all threshold signers
- Compromise of TCB implementation

### Attack Vectors

#### 1. Key Compromise

**Threat:** Attacker obtains private key.

**Mitigations:**
- Shamir secret sharing (RFC-008)
- Threshold signatures (RFC-007)
- Key rotation procedures
- Hardware key storage

**Detection:**
- Unauthorized signatures in audit trail
- Unexpected certificate issuance

#### 2. Signature Forgery

**Threat:** Attacker creates valid signature without key.

**Mitigations:**
- Ed25519 security (128-bit equivalent)
- libsodium implementation

**Detection:**
- N/A (would break Ed25519)

#### 3. Replay Attacks

**Threat:** Attacker replays old valid messages.

**Mitigations:**
- Timestamps in all messages
- Sequence numbers in audit trail
- Nonces in protocol messages

**Detection:**
- Duplicate sequence numbers
- Out-of-order timestamps

#### 4. Rollback Attacks

**Threat:** Attacker forces system to old vulnerable state.

**Mitigations:**
- Forward rollback (history preserved)
- Threshold authorization for rollback
- Protected version list
- Audit trail of all rollbacks

**Detection:**
- `seal-rollback` events in audit
- Version regression alerts

#### 5. Man-in-the-Middle

**Threat:** Attacker intercepts and modifies communications.

**Mitigations:**
- All messages signed
- Certificate pinning for peers
- Hash verification of archives

**Detection:**
- Signature verification failures
- Hash mismatches

#### 6. Sybil Attacks

**Threat:** Attacker creates many fake identities.

**Mitigations:**
- SPKI admission control
- Reputation systems
- Threshold requirements

**Detection:**
- Unusual peer registration patterns
- Correlated behavior across "different" peers

#### 7. Denial of Service

**Threat:** Attacker exhausts resources.

**Mitigations:**
- Rate limiting
- Resource quotas
- Peer reputation

**Detection:**
- Abnormal request rates
- Resource exhaustion alerts

---

## Security-Critical Code Paths

### Path 1: Signature Verification

```
User input → Parse → Verify signature → Accept/Reject
                         │
                         ▼
                    TCB (OCaml)
```

**Invariants:**
- Never accept without verification
- Verification in TCB only
- No short-circuits

### Path 2: Certificate Chain

```
Root key → Cert[0] → Cert[1] → ... → Cert[n] → Tag
              │          │              │
              ▼          ▼              ▼
           Verify     Verify         Verify
```

**Invariants:**
- Every link verified
- Propagation checked
- Tag implication checked

### Path 3: Threshold Authorization

```
Script → Collect signatures → Count valid ≥ K → Execute
              │                    │
              ▼                    ▼
         Verify each          Threshold check
```

**Invariants:**
- Each signature independently verified
- K-1 signatures always rejected
- No execution before threshold met

---

## Operational Security

### Key Ceremony

For root key generation:

1. Air-gapped machine
2. Multiple witnesses
3. Shamir split immediately
4. Distribute shares geographically
5. Destroy original key
6. Audit entry for ceremony

### Incident Response

On suspected compromise:

1. Isolate affected systems
2. Preserve audit trail
3. Identify scope via audit analysis
4. Rotate affected keys
5. Issue revocations
6. Post-mortem and RFC update

### Secure Defaults

- `verify-before-accept: #t`
- `require-signature: #t`
- `trust-on-first-use: #f`
- `auto-sync: #f` (manual approval)

---

## Cryptographic Agility

Current algorithms:
- Signatures: Ed25519
- Hashing: SHA-512
- Key derivation: Argon2 (if needed)

Future migration path:
- Algorithm identifiers in all structures
- Version fields in protocols
- Parallel verification during transition

---

## Compliance Notes

### Data Protection

- No PII in audit trails (keys only)
- Encrypted archives available
- Geographic distribution via federation

### Audit Requirements

- Immutable audit trail (hash chain)
- Signed entries (non-repudiation)
- Exportable formats (S-expression, human-readable)

---

## References

1. RFC-003: Cryptographic Audit Trail
2. RFC-004: SPKI Authorization
3. RFC-007: Threshold Signature Governance
4. RFC-008: Shamir Secret Sharing
5. RFC-011: Byzantine Consensus
6. RFC-014: Coq Extraction for TCB
7. OWASP Security Guidelines
8. NIST SP 800-57: Key Management

---

## Changelog

- **2026-01-06** - Initial specification with auditable events catalog

---

**Document Status:** Living document - updated as security considerations evolve
**Last Security Review:** 2026-01-06
**Next Review Due:** Upon significant system changes
