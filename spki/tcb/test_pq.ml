(** Test Post-Quantum Signatures in TCB
 *
 * Verifies that ML-DSA-65 and SLH-DSA-SHAKE-256s work correctly
 * in the OCaml TCB without OpenSSL dependency.
 *)

open Spki_tcb

let test_mldsa () =
  Printf.printf "=== Testing ML-DSA-65 ===\n";

  (* Get sizes *)
  let (pk_size, sk_size, sig_size) = mldsa_sizes () in
  Printf.printf "  Public key:  %d bytes\n" pk_size;
  Printf.printf "  Secret key:  %d bytes\n" sk_size;
  Printf.printf "  Signature:   %d bytes\n" sig_size;

  (* Generate keypair *)
  let (pk, sk) = mldsa_keypair () in
  assert (Bytes.length pk = pk_size);
  assert (Bytes.length sk = sk_size);
  Printf.printf "  ✓ Keypair generated\n";

  (* Sign message *)
  let msg = Bytes.of_string "Harvest now, forge later? Not with ML-DSA!" in
  let sig_bytes = mldsa_sign sk msg in
  assert (Bytes.length sig_bytes = sig_size);
  Printf.printf "  ✓ Message signed\n";

  (* Verify signature *)
  let valid = mldsa_verify pk msg sig_bytes in
  assert valid;
  Printf.printf "  ✓ Signature verified\n";

  (* Test invalid signature *)
  let bad_msg = Bytes.of_string "Different message" in
  let invalid = mldsa_verify pk bad_msg sig_bytes in
  assert (not invalid);
  Printf.printf "  ✓ Invalid signature rejected\n";

  Printf.printf "ML-DSA-65: PASS\n\n"

let test_slhdsa () =
  Printf.printf "=== Testing SLH-DSA-SHAKE-256s ===\n";

  (* Get sizes *)
  let (pk_size, sk_size, sig_size) = slhdsa_sizes () in
  Printf.printf "  Public key:  %d bytes\n" pk_size;
  Printf.printf "  Secret key:  %d bytes\n" sk_size;
  Printf.printf "  Signature:   %d bytes\n" sig_size;

  (* Generate keypair *)
  let (pk, sk) = slhdsa_keypair () in
  assert (Bytes.length pk = pk_size);
  assert (Bytes.length sk = sk_size);
  Printf.printf "  ✓ Keypair generated\n";

  (* Sign message *)
  let msg = Bytes.of_string "Hash-based signatures resist quantum attacks" in
  let sig_bytes = slhdsa_sign sk msg in
  assert (Bytes.length sig_bytes = sig_size);
  Printf.printf "  ✓ Message signed\n";

  (* Verify signature *)
  let valid = slhdsa_verify pk msg sig_bytes in
  assert valid;
  Printf.printf "  ✓ Signature verified\n";

  (* Test invalid signature *)
  let bad_msg = Bytes.of_string "Tampered message" in
  let invalid = slhdsa_verify pk bad_msg sig_bytes in
  assert (not invalid);
  Printf.printf "  ✓ Invalid signature rejected\n";

  Printf.printf "SLH-DSA-SHAKE-256s: PASS\n\n"

let test_ed25519_still_works () =
  Printf.printf "=== Testing Ed25519 (Classical) ===\n";

  let (pk, sk) = ed25519_keypair () in
  let msg = Bytes.of_string "Classical crypto still works" in
  let sig_bytes = ed25519_sign sk msg in
  let valid = ed25519_verify pk msg sig_bytes in
  assert valid;

  Printf.printf "  ✓ Ed25519 signatures still work\n";
  Printf.printf "Ed25519: PASS\n\n"

let () =
  Printf.printf "\n╔═══════════════════════════════════════════════════╗\n";
  Printf.printf "║  SPKI TCB Post-Quantum Signature Tests           ║\n";
  Printf.printf "║  TCB Dependencies: libsodium + liboqs             ║\n";
  Printf.printf "╚═══════════════════════════════════════════════════╝\n\n";

  (* Initialize TCB *)
  init ();
  Printf.printf "✓ TCB initialized (libsodium + liboqs)\n\n";

  (* Run tests *)
  test_mldsa ();
  test_slhdsa ();
  test_ed25519_still_works ();

  (* Cleanup *)
  pq_cleanup ();

  Printf.printf "╔═══════════════════════════════════════════════════╗\n";
  Printf.printf "║  ✓ All post-quantum tests PASSED                 ║\n";
  Printf.printf "║                                                   ║\n";
  Printf.printf "║  The TCB now defends against:                    ║\n";
  Printf.printf "║  • Harvest-now-decrypt-later (KEX)               ║\n";
  Printf.printf "║  • Harvest-now-forge-later (signatures)          ║\n";
  Printf.printf "║                                                   ║\n";
  Printf.printf "║  No OpenSSL dependency required.                 ║\n";
  Printf.printf "╚═══════════════════════════════════════════════════╝\n"
