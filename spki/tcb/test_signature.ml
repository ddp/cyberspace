(** Test SPKI TCB signature operations
 *
 * Verifies that Ed25519 via libsodium works correctly:
 * 1. Initialize libsodium
 * 2. Generate keypair
 * 3. Sign a message
 * 4. Verify the signature
 * 5. Verify that tampering fails
 *)

open Spki_tcb

let () =
  (* Initialize libsodium *)
  print_endline "Initializing libsodium...";
  Signature.init ();
  print_endline "✓ libsodium initialized";

  (* Generate keypair *)
  print_endline "\nGenerating Ed25519 keypair...";
  let keypair = Signature.generate_keypair () in
  Printf.printf "✓ Generated keypair (pk: %d bytes, sk: %d bytes)\n"
    (Bytes.length keypair.public_key)
    (Bytes.length keypair.secret_key);

  (* Sign a message *)
  let message = Bytes.of_string "The Library of Cyberspace" in
  print_endline "\nSigning message...";
  let signature = Signature.sign keypair.secret_key message in
  Printf.printf "✓ Generated signature (%d bytes)\n" (Bytes.length signature);

  (* Verify the signature *)
  print_endline "\nVerifying signature...";
  let valid = Signature.verify keypair.public_key message signature in
  if valid then
    print_endline "✓ Signature verified successfully"
  else
    failwith "CRITICAL: Valid signature failed verification!";

  (* Test tampering detection *)
  print_endline "\nTesting tampering detection...";
  let tampered_message = Bytes.of_string "The Library of Cyberspace!" in  (* added '!' *)
  let tampered_valid = Signature.verify keypair.public_key tampered_message signature in
  if not tampered_valid then
    print_endline "✓ Tampered message correctly rejected"
  else
    failwith "CRITICAL: Tampered message accepted!";

  (* Test wrong public key *)
  print_endline "\nTesting wrong public key detection...";
  let wrong_keypair = Signature.generate_keypair () in
  let wrong_key_valid = Signature.verify wrong_keypair.public_key message signature in
  if not wrong_key_valid then
    print_endline "✓ Wrong public key correctly rejected"
  else
    failwith "CRITICAL: Signature verified with wrong key!";

  (* Test hash function *)
  print_endline "\nTesting SHA-512 hash...";
  let hash = Signature.hash message in
  Printf.printf "✓ SHA-512 hash (%d bytes)\n" (Bytes.length hash);

  print_endline "\n=== All TCB tests passed ===";
  print_endline "TCB guarantees verified:";
  print_endline "  1. Signature correctness: sign/verify round-trip works";
  print_endline "  2. Unforgeability: tampered message rejected";
  print_endline "  3. Key binding: wrong key rejected";
