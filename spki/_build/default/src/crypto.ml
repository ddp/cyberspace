(** Cryptographic operations for SPKI *)

(**
   NOTE: This is a simplified implementation using CryptoKit.
   Production SPKI should use Ed25519 (via sodium or mirage-crypto-ec).
   This implementation uses RSA for demonstration purposes.
*)

open Cryptokit

(** Hash bytes using SHA-256 *)
let sha256 data =
  let h = Hash.sha256 () in
  h#add_string (Bytes.to_string data);
  Bytes.of_string (h#result)

(** RSA keypair (placeholder for Ed25519) *)
type keypair = {
  public: bytes;
  private_key: bytes;
}

(** Generate RSA keypair (placeholder - should be Ed25519) *)
let generate_keypair () =
  let rsa = RSA.new_key 2048 in
  (* Serialize keys as s-expressions for storage *)
  let pub_n = rsa.RSA.n in
  let _pub_e = rsa.RSA.e in
  let priv_d = rsa.RSA.d in

  (* Simple serialization: just use the numbers as bytes *)
  (* In real implementation, use proper encoding *)
  {
    public = Bytes.of_string pub_n;
    private_key = Bytes.of_string (pub_n ^ "|" ^ priv_d);
  }

(** Sign data with private key (placeholder - should be Ed25519) *)
let sign private_key data =
  (* Hash the data first *)
  let hash = sha256 data in

  (* In real Ed25519: ed25519_sign(private_key, data) *)
  (* Here we just hash with private key material mixed in *)
  let combined = Bytes.cat private_key hash in
  sha256 combined

(** Verify signature (placeholder - should be Ed25519) *)
let verify _public_key _data signature =
  (* In real Ed25519: ed25519_verify(public_key, data, signature) *)
  (* Placeholder: just check signature format *)
  try
    (* Simplified verification - just check signature length *)
    Bytes.length signature = 32
  with _ -> false

(** Compute hash of public key *)
let hash_public_key public_key =
  sha256 public_key

(**
   TODO for production:
   1. Replace with proper Ed25519 implementation
   2. Use sodium library or mirage-crypto-ec
   3. Proper key serialization (not just bytes)
   4. Constant-time comparison for signatures
*)
