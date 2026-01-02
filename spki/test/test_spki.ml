(** SPKI test suite *)

module Types = Spki.Types
module Operations = Spki.Operations
module Sexp = Spki.Sexp
module Crypto = Spki.Crypto

open Types
open Operations

let test_sexp_roundtrip () =
  let original = Sexp.List [
    Sexp.Atom "cert";
    Sexp.List [Sexp.Atom "tag"; Sexp.Atom "read"];
    Sexp.Bytes (Bytes.of_string "test")
  ] in
  let str = Sexp.to_string original in
  let parsed = Sexp.of_string str in
  Alcotest.(check bool) "S-exp roundtrip" true (original = parsed)

let test_cert_roundtrip () =
  let read_tag = Tag (Sexp.List [Sexp.Atom "read"]) in
  let cert = {
    issuer = Key (Bytes.of_string "alice_pub");
    subject = Key (Bytes.of_string "bob_pub");
    tag = read_tag;
    validity = None;
    propagate = false;
  } in
  let sexp = cert_to_sexp cert in
  let cert' = cert_of_sexp sexp in
  Alcotest.(check bool) "Cert roundtrip" true (cert = cert')

let test_signature () =
  let keys = Crypto.generate_keypair () in
  let data = Bytes.of_string "test data" in
  let signature = Crypto.sign keys.private_key data in
  let valid = Crypto.verify keys.public data signature in
  Alcotest.(check bool) "Signature verification" true valid

let test_simple_chain () =
  let alice_keys = Crypto.generate_keypair () in
  let bob_keys = Crypto.generate_keypair () in

  let read_tag = Tag (Sexp.List [Sexp.Atom "read"]) in
  let cert = create_cert
    ~issuer:(Key alice_keys.public)
    ~subject:(Key bob_keys.public)
    ~tag:read_tag
    ~propagate:false
    () in

  let signed_cert = sign_cert cert alice_keys.private_key in

  (* Should verify *)
  let valid = verify_chain alice_keys.public [signed_cert] read_tag in
  Alcotest.(check bool) "Simple chain valid" true valid

let () =
  let open Alcotest in
  run "SPKI" [
    "s-expressions", [
      test_case "Roundtrip" `Quick test_sexp_roundtrip;
    ];
    "certificates", [
      test_case "Cert roundtrip" `Quick test_cert_roundtrip;
    ];
    "crypto", [
      test_case "Signature" `Quick test_signature;
    ];
    "chains", [
      test_case "Simple chain" `Quick test_simple_chain;
    ];
  ]
