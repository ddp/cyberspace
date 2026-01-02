# SPKI/SDSI Reference Implementation

**Simple Public Key Infrastructure** with **Simple Distributed Security Infrastructure**

This is a reference implementation of SPKI/SDSI in OCaml, providing s-expression based certificates, direct trust delegation, and authorization chain verification.

## Philosophy

**No hierarchical CAs. Keys are principals. Human-readable certificates. Math, not authority.**

### Why SPKI?

**X.509 Problems:**
- Binary ASN.1/DER encoding (opaque blobs)
- Hierarchical CAs (centralized trust)
- "Who you are" not "what you can do"
- Requires `openssl x509 -text` just to read a certificate

**SPKI Advantages:**
- S-expression encoding (human-readable, trivially parseable)
- Decentralized trust (direct delegation, no CA hierarchy)
- Authorization-centric (certificates grant capabilities)
- Keys ARE principals (identity IS the public key)

## Architecture

**Layer 1: S-Expressions** (`sexp.ml`)
- Lisp-style s-expression parser/printer
- Supports atoms, lists, and binary data in `|base64|` notation
- Trivial recursive descent parser
- Pretty-printing with indentation

**Layer 2: SPKI Types** (`spki.ml`)
- `principal`: Key or KeyHash
- `tag`: Authorization capability (what you can do)
- `cert`: Certificate linking issuer → subject with tag
- `signed_cert`: Certificate + cryptographic signature

**Layer 3: Crypto** (`crypto.ml`)
- Key generation (currently RSA, should be Ed25519)
- SHA-256 hashing
- Signing and verification
- **TODO**: Replace with proper Ed25519 (via sodium or mirage-crypto-ec)

**Layer 4: Operations** (`operations.ml`)
- Certificate creation
- Signing certificates
- Verifying signatures
- Delegation chain verification

## Example Certificate

```lisp
((cert
  (issuer |YWxpY2VfcHVi|)
  (subject |Ym9iX3B1Yg==|)
  (tag (read (path /data/secrets)))
  (valid
    (not-before 2026-01-01T00:00:00Z)
    (not-after 2027-01-01T00:00:00Z)))
 (signature
  (hash sha256 |aGFzaA==|)
  |c2lnbmF0dXJl|))
```

Human-readable. Self-documenting. Mathematically verifiable.

## Usage

### Build

```bash
opam install . --deps-only
dune build
```

### Run Example

```bash
dune exec examples/simple_delegation.exe
```

### Run Tests

```bash
dune runtest
```

## Example: Simple Delegation

```ocaml
(* Generate keys *)
let alice_keys = Crypto.generate_keypair () in
let bob_keys = Crypto.generate_keypair () in

(* Define read permission *)
let read_tag = Tag (Sexp.List [
  Sexp.Atom "read";
  Sexp.List [Sexp.Atom "path"; Sexp.Atom "/data/secrets"]
]) in

(* Alice creates certificate for Bob *)
let cert = Operations.create_cert
  ~issuer:(Key alice_keys.public)
  ~subject:(Key bob_keys.public)
  ~tag:read_tag
  ~propagate:false
  () in

(* Alice signs it *)
let signed_cert = Operations.sign_cert cert alice_keys.private_key in

(* Verify Bob has permission *)
let authorized = Operations.verify_chain
  alice_keys.public [signed_cert] read_tag in
(* authorized = true *)
```

## Delegation Chains

SPKI supports transitive authorization:

```
Alice --[read /data]--> Bob --[read /data]--> Carol
```

If Alice trusts Bob, and Bob delegates to Carol, and both certificates allow propagation, then Carol can read `/data` via the chain.

```ocaml
let alice_to_bob = create_cert ~propagate:true ... in
let bob_to_carol = create_cert ~propagate:false ... in

(* Verify Carol has permission via chain *)
verify_chain alice_keys.public [alice_to_bob; bob_to_carol] read_tag
```

## Design Principles

### 1. Human-Readable by Default
- S-expressions for all structured data
- No binary blobs except encrypted payloads
- Diffs are meaningful to humans
- "View source" for certificates

### 2. Verifiable Without Trust
- Crypto proofs for all assertions
- Delegation chains auditable by inspection
- No "trust the CA" assumptions
- Math doesn't require authority

### 3. Decentralized Security
- No hierarchical CAs
- Peer-to-peer trust delegation
- Keys are principals (no global namespace)
- SDSI local names: `alice/engineering/bob`

### 4. Authorization-Centric
- Certificates grant capabilities
- Tags describe permissions, not identities
- "What you can do" not "who you are"
- Least-privilege by default

## Roadmap

**Phase 1: Foundation** ✓
- [x] S-expression parser
- [x] SPKI data types
- [x] Basic crypto (placeholder RSA)
- [x] Certificate creation
- [x] Signature verification
- [x] Chain verification
- [x] Example code
- [x] Tests

**Phase 2: Production Crypto**
- [ ] Replace RSA with Ed25519
- [ ] Use sodium or mirage-crypto-ec
- [ ] Proper key serialization
- [ ] Constant-time signature comparison

**Phase 3: Advanced Features**
- [ ] SDSI local names (alice/engineering/bob)
- [ ] Threshold signatures (Shamir)
- [ ] Tag intersection/subset semantics
- [ ] Validity period checking (time-based expiration)
- [ ] Certificate revocation

**Phase 4: Tools & Integration**
- [ ] Command-line tool (keygen, sign, verify)
- [ ] Certificate storage/retrieval
- [ ] Integration with distributed agent architecture
- [ ] Gossip protocol for certificate distribution

## References

- **RFC 2693**: SPKI Certificate Theory (Ellison, et al.)
- **RFC 2692**: SPKI Requirements
- Rivest & Lampson, "SDSI - A Simple Distributed Security Infrastructure" (1996)

## License

MIT

---

**Part of the Cyberspace Project**
**Peace for All Mankind: Cooperative Computing Without Enclosure**

*Architect*: ddp@eludom.net / derrell@mit.edu
*Generated*: 2026-01-01 by Librarian (Claude Code)
