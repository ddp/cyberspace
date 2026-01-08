(** Cryptographic operations for SPKI

    This module wraps the TCB's Ed25519 implementation.
    All cryptographic operations delegate to spki_tcb which
    uses libsodium for constant-time, audited crypto.
*)

(** Hash bytes using SHA-256 *)
let sha256 data =
  Spki_tcb.sha256_hash data

(** Hash bytes using SHA-512 *)
let sha512 data =
  Spki_tcb.sha512_hash data

(** Ed25519 keypair *)
type keypair = {
  public: bytes;
  private_key: bytes;
}

(** Generate Ed25519 keypair *)
let generate_keypair () =
  let (public, secret) = Spki_tcb.ed25519_keypair () in
  { public; private_key = secret }

(** Sign data with Ed25519 private key *)
let sign private_key data =
  Spki_tcb.ed25519_sign private_key data

(** Verify Ed25519 signature *)
let verify public_key data signature =
  Spki_tcb.ed25519_verify public_key data signature

(** Compute hash of public key (principal identity) *)
let hash_public_key public_key =
  Spki_tcb.sha512_hash public_key

(** Initialize crypto subsystem *)
let init () =
  Spki_tcb.init ()
