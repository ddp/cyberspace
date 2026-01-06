(** SPKI TCB - Signature Operations

    Trusted Computing Base: Only cryptographic primitives.

    This module provides:
    - Ed25519 signature creation/verification via libsodium
    - SHA-256 hashing
    - Public key operations

    Everything else (s-expressions, certificates, chains, policy) is in Scheme.

    TCB guarantees:
    - If verify() returns true, the signature was created by holder of private key
    - No forgery possible without private key
    - Constant-time operations (no timing attacks)
*)

external sodium_init : unit -> int = "caml_sodium_init"
external ed25519_keypair : unit -> (bytes * bytes) = "caml_ed25519_keypair"
external ed25519_sign : bytes -> bytes -> bytes = "caml_ed25519_sign"
external ed25519_verify : bytes -> bytes -> bytes -> bool = "caml_ed25519_verify"
external sha512_hash : bytes -> bytes = "caml_sha512_hash"

(** Initialize libsodium - MUST be called before any crypto operations *)
let init () =
  let result = sodium_init () in
  if result < 0 then
    failwith "Failed to initialize libsodium"
  else
    ()

(** Ed25519 key pair *)
type keypair = {
  public_key: bytes;   (* 32 bytes *)
  secret_key: bytes;   (* 64 bytes: seed + public key *)
}

(** Generate Ed25519 keypair *)
let generate_keypair () =
  let (pk, sk) = ed25519_keypair () in
  { public_key = pk; secret_key = sk }

(** Sign message with Ed25519 private key

    @param secret_key 64-byte Ed25519 secret key
    @param message Message to sign
    @return 64-byte signature
*)
let sign secret_key message =
  ed25519_sign secret_key message

(** Verify Ed25519 signature

    @param public_key 32-byte Ed25519 public key
    @param message Message that was signed
    @param signature 64-byte signature
    @return true if signature is valid, false otherwise

    TCB Guarantee: If this returns true, the signature was created by
    holder of the corresponding private key. No forgery possible.
*)
let verify public_key message signature =
  ed25519_verify public_key message signature

(** Compute SHA-512 hash

    @param data Data to hash
    @return 64-byte hash
*)
let hash data =
  sha512_hash data

(** Compute SHA-512 hash of public key (for key hashes) *)
let hash_public_key public_key =
  sha512_hash public_key

(**
   TCB Properties (provable in Coq):

   1. Signature correctness:
      ∀ keypair message, verify(keypair.public_key, message, sign(keypair.secret_key, message)) = true

   2. Unforgeability:
      If verify(public_key, message, sig) = true, then
      ∃ secret_key such that sign(secret_key, message) = sig
      AND keypair(public_key, secret_key) is valid

   3. Non-malleability:
      Cannot modify signature without invalidating it
*)
