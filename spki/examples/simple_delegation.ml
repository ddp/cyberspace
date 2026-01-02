(** Simple SPKI delegation example *)

module Types = Spki.Types
module Operations = Spki.Operations
module Sexp = Spki.Sexp
module Crypto = Spki.Crypto

open Types
open Operations

let () =
  Printf.printf "SPKI/SDSI Simple Delegation Example\n";
  Printf.printf "====================================\n\n";

  (* Generate keys for Alice and Bob *)
  Printf.printf "1. Generating keypairs...\n";
  let alice_keys = Crypto.generate_keypair () in
  let bob_keys = Crypto.generate_keypair () in
  Printf.printf "   Alice public key hash: %s\n"
    (Base64.encode_exn (Bytes.to_string (Crypto.hash_public_key alice_keys.public)));
  Printf.printf "   Bob public key hash: %s\n\n"
    (Base64.encode_exn (Bytes.to_string (Crypto.hash_public_key bob_keys.public)));

  (* Define a read permission tag *)
  Printf.printf "2. Creating authorization tag...\n";
  let read_tag = Tag (Sexp.List [
    Sexp.Atom "read";
    Sexp.List [Sexp.Atom "path"; Sexp.Atom "/data/secrets"]
  ]) in
  Printf.printf "   Tag: %s\n\n" (Sexp.to_string (tag_to_sexp read_tag));

  (* Alice creates a certificate delegating read permission to Bob *)
  Printf.printf "3. Alice creates certificate for Bob...\n";
  let cert = create_cert
    ~issuer:(Key alice_keys.public)
    ~subject:(Key bob_keys.public)
    ~tag:read_tag
    ~validity:(Some {
      not_before = "2026-01-01T00:00:00Z";
      not_after = "2027-01-01T00:00:00Z";
    })
    ~propagate:false  (* Bob cannot re-delegate *)
    () in
  Printf.printf "   Certificate created\n\n";

  (* Alice signs the certificate *)
  Printf.printf "4. Alice signs the certificate...\n";
  let signed_cert = sign_cert cert alice_keys.private_key in
  let sig_b64 = Base64.encode_exn (Bytes.to_string signed_cert.signature.sig_bytes) in
  Printf.printf "   Signature: %s...\n\n" (String.sub sig_b64 0 32);

  (* Display the full signed certificate *)
  Printf.printf "5. Signed certificate (s-expression):\n";
  Printf.printf "%s\n\n" (signed_cert_to_string signed_cert);

  (* Verify the certificate *)
  Printf.printf "6. Verifying signature...\n";
  let valid = verify_signed_cert signed_cert alice_keys.public in
  Printf.printf "   Signature valid: %b\n\n" valid;

  (* Verify Bob has the read permission via the chain *)
  Printf.printf "7. Verifying delegation chain...\n";
  (try
    let authorized = verify_chain alice_keys.public [signed_cert] read_tag in
    Printf.printf "   Chain valid: %b\n" authorized;
    Printf.printf "   Bob is authorized to read /data/secrets\n\n"
  with Failure msg ->
    Printf.printf "   Chain verification failed: %s\n\n" msg);

  (* Try with a different permission (should fail) *)
  Printf.printf "8. Testing unauthorized access...\n";
  let write_tag = Tag (Sexp.List [
    Sexp.Atom "write";
    Sexp.List [Sexp.Atom "path"; Sexp.Atom "/data/secrets"]
  ]) in
  (try
    let _ = verify_chain alice_keys.public [signed_cert] write_tag in
    Printf.printf "   ERROR: Bob should NOT be authorized to write\n"
  with Failure msg ->
    Printf.printf "   Correctly denied: %s\n\n" msg);

  Printf.printf "Demo complete!\n"
