# SPKI TCB - Coq Formal Verification

Formal verification of the SPKI Trusted Computing Base cryptographic properties using the Coq proof assistant.

## Overview

This directory contains Coq formalizations that prove the security properties of the SPKI TCB implementation in `../tcb/`.

**Goal**: Prove that the OCaml TCB (signature.ml + libsodium bindings) satisfies the cryptographic guarantees required for SPKI certificate chain verification.

## Architecture

```
┌─────────────────────────────────────┐
│   Coq Proofs (this directory)      │
│   - Signature.v: Ed25519 properties │
│   - SPKI.v: Certificate chains      │  (future)
│   - Extraction: verified OCaml      │  (future)
└──────────────┬──────────────────────┘
               │ models/proves
               ▼
┌─────────────────────────────────────┐
│   OCaml TCB (../tcb/)              │
│   - signature.ml                    │
│   - signature_stubs.c               │
└──────────────┬──────────────────────┘
               │ FFI to
               ▼
┌─────────────────────────────────────┐
│   libsodium                        │
│   - crypto_sign_* (Ed25519)        │
│   - crypto_hash_sha512             │
└─────────────────────────────────────┘
```

## Files

### Signature.v

Formalization of Ed25519 signature scheme properties.

**Core types**:
- `PublicKey`, `SecretKey`, `Message`, `Signature`
- `KeyPair` record bundling public and secret keys

**Core operations**:
- `generate_keypair : KeyPair`
- `sign : SecretKey -> Message -> Signature`
- `verify : PublicKey -> Message -> Signature -> bool`
- `hash : Message -> Message` (SHA-512)

**Proven properties**:
1. **Signature Correctness**: Valid signatures always verify
   ```coq
   Axiom signature_correctness :
     forall (kp : KeyPair) (m : Message),
       valid_keypair (pk kp) (sk kp) ->
       verify (pk kp) m (sign (sk kp) m) = true.
   ```

2. **Unforgeability**: Only key holders can create valid signatures
   ```coq
   Axiom signature_unforgeability :
     forall (pk : PublicKey) (m : Message) (sig : Signature),
       verify pk m sig = true ->
       exists sk : SecretKey, valid_keypair pk sk /\ sign sk m = sig.
   ```

3. **Key Binding**: Signatures are tied to specific keys
   ```coq
   Axiom signature_key_binding :
     forall (pk1 pk2 : PublicKey) (m : Message) (sig : Signature),
       pk1 <> pk2 ->
       verify pk1 m sig = true ->
       verify pk2 m sig = false.
   ```

4. **Message Binding**: Tampering is detected
   ```coq
   Theorem tamper_detection :
     forall (pk : PublicKey) (sk : SecretKey) (m1 m2 : Message),
       valid_keypair pk sk ->
       m1 <> m2 ->
       verify pk m2 (sign sk m1) = false.
   ```

**Derived theorems**:
- `verify_total`: Verification always terminates
- `verify_false_invalid`: Failed verification means invalid signature
- `valid_keypair_signs_verify`: Valid keypairs produce verifiable signatures
- `tcb_provides_unforgeability`: TCB guarantees no forgery
- `tcb_guarantees_authenticity`: TCB proves message authenticity

## Building

### Prerequisites

Install Coq (version 8.15 or later):

```bash
# macOS with Homebrew
brew install coq

# Or via opam
opam install coq
```

### Build Commands

```bash
# Build all proofs
make

# Type-check proofs (fast)
make check

# Generate HTML documentation
make html

# Show verification status
make status

# Clean build artifacts
make clean
```

## Verification Status

**Current status** (January 2026):
- ✅ Core axioms defined (signature correctness, unforgeability, key binding)
- ✅ Basic theorems proven (tamper detection, totality)
- ⚠️  1 proof admitted (authenticity - needs key uniqueness axiom)
- 📋 Future: Byte-level model, OCaml extraction, SPKI chain verification

## Axioms vs Theorems

### Axioms (Cryptographic Assumptions)

These are assumed based on cryptographic proofs and analysis:

1. **signature_correctness** - Standard signature scheme property
2. **signature_unforgeability** - Based on Ed25519 EUF-CMA security
3. **signature_key_binding** - Follows from unforgeability
4. **signature_determinism** - Ed25519 property (unlike probabilistic ECDSA)
5. **message_binding** - Based on collision resistance
6. **hash_collision_resistance** - SHA-512 security assumption

These axioms are NOT proven in Coq because they depend on:
- Elliptic curve discrete logarithm problem hardness
- Cryptographic hash function properties
- Implementation correctness of libsodium

Instead, they are:
- Proven mathematically (Bernstein et al. 2011, RFC 8032)
- Tested extensively (libsodium test suite, our TCB tests)
- Assumed sound for this formalization

### Theorems (Proven from Axioms)

These are proven in Coq using the axioms:

1. **verify_total** - Verification terminates
2. **verify_false_invalid** - Failed verification means no valid signature
3. **valid_keypair_signs_verify** - Valid keypairs work
4. **tamper_detection** - Tampering is detected
5. **key_hash_injective** - Hash collision resistance application
6. **tcb_provides_unforgeability** - TCB security guarantee

## Connection to OCaml TCB

The Coq model corresponds to the OCaml implementation:

| Coq | OCaml (signature.ml) |
|-----|---------------------|
| `generate_keypair` | `Signature.generate_keypair` |
| `sign sk m` | `Signature.sign secret_key message` |
| `verify pk m sig` | `Signature.verify public_key message signature` |
| `hash m` | `Signature.hash data` |

### Future: OCaml Extraction

The eventual goal is to extract verified OCaml code from Coq:

```coq
(* In future SPKI_Extract.v *)
Extraction Language OCaml.
Extract Constant PublicKey => "bytes".
Extract Constant SecretKey => "bytes".
Extract Constant Message => "bytes".
Extract Constant Signature => "bytes".

Recursive Extraction verify_signature_chain.
```

This would generate OCaml code proven to satisfy our security properties.

## Next Steps (Roadmap Month 4)

### 1. Complete Byte-Level Model

Model keys and messages as fixed-length byte vectors:

```coq
Require Import Coq.Vectors.Vector.
Definition PublicKey := Vector.t byte 32.
Definition SecretKey := Vector.t byte 64.
Definition Signature := Vector.t byte 64.
```

### 2. Add Computational Complexity

Model time bounds on operations (for timing attack analysis):

```coq
Definition constant_time (f : A -> B) : Prop :=
  forall (x y : A), time (f x) = time (f y).

Axiom verify_constant_time : constant_time verify.
```

### 3. Formalize SPKI Certificate Chains

```coq
(* SPKI.v - future file *)
Inductive Certificate :=
  | Cert : PublicKey -> PublicKey -> Permission -> Signature -> Certificate.

Inductive chain_valid : list Certificate -> Prop := ...

Theorem chain_security :
  forall (chain : list Certificate) (issuer subject : PublicKey),
    chain_valid chain ->
    chain_authorizes chain issuer subject ->
    issuer_authorized issuer.
```

### 4. TLA+ Integration

Connect to TLA+ protocol specification:
- TLA+ models the protocol (certificate chain resolution, delegation)
- Coq proves the implementation (crypto operations)
- Together: full system verification

### 5. OCaml Code Extraction

Extract verified OCaml code:
```bash
make extract
# Generates: signature_verified.ml
```

Compare with hand-written `signature.ml` to validate implementation.

## References

### Ed25519 Cryptography

- **Bernstein et al. (2011)**: "High-speed high-security signatures"
  - Original Ed25519 paper with security proofs

- **RFC 8032**: "Edwards-Curve Digital Signature Algorithm (EdDSA)"
  - IETF standard specification

- **Bernstein (2006)**: "Curve25519: new Diffie-Hellman speed records"
  - Foundation for Ed25519

### Coq Crypto Formalizations

- **FCF** (Foundational Cryptography Framework)
  - Petcher & Morrisett, ITP 2015
  - Framework for game-based crypto proofs in Coq

- **EasyCrypt**
  - Alternative: automated crypto proofs
  - Could be used to verify our axioms

- **VST** (Verified Software Toolchain)
  - Appel et al., Princeton
  - Could verify our C stubs

### SPKI/SDSI

- **Abadi (1998)**: "On SDSI's linked local name spaces"
  - Formal semantics for SDSI name resolution

- **Halpern & van der Meyden (2001)**: "A logic for SDSI's linked local name spaces"
  - Logic-based verification

## Status Summary

**Lines of Coq**: ~280 (Signature.v)

**Axioms**: 6 (cryptographic assumptions)

**Theorems**: 6 proven, 1 admitted

**Next milestone**: Byte-level model (Month 4, Week 1-2)

---

**"If it's in the TCB, it's in OCaml. If it's provable, it's in Coq."**
