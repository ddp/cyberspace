(** SPKI certificate operations: create, sign, verify, check chains *)

open Types

(** Create a new certificate *)
let create_cert ~issuer ~subject ~tag ?(validity=None) ?(propagate=false) () =
  { issuer; subject; tag; validity; propagate }

(** Sign a certificate *)
let sign_cert cert private_key =
  (* Convert cert to canonical s-expression *)
  let cert_sexp = cert_to_sexp cert in
  let canonical = Sexp.to_string cert_sexp in
  let cert_bytes = Bytes.of_string canonical in

  (* Hash the certificate *)
  let cert_hash = Crypto.sha256 cert_bytes in

  (* Sign the hash *)
  let sig_bytes = Crypto.sign private_key cert_hash in

  (* Create signed certificate *)
  {
    cert;
    signature = {
      hash_alg = SHA256;
      cert_hash;
      sig_bytes;
    }
  }

(** Verify a signed certificate *)
let verify_signed_cert signed_cert public_key =
  (* Recompute certificate hash *)
  let cert_sexp = cert_to_sexp signed_cert.cert in
  let canonical = Sexp.to_string cert_sexp in
  let cert_bytes = Bytes.of_string canonical in
  let computed_hash = Crypto.sha256 cert_bytes in

  (* Check hash matches *)
  if computed_hash <> signed_cert.signature.cert_hash then
    false
  else
    (* Verify signature *)
    Crypto.verify public_key computed_hash signed_cert.signature.sig_bytes

(** Check if tag1 implies tag2 (tag1 >= tag2) *)
let tag_implies tag1 tag2 =
  match tag1, tag2 with
  | AllPerms, _ -> true  (* AllPerms grants everything *)
  | _, AllPerms -> false (* Nothing but AllPerms grants AllPerms *)
  | Tag t1, Tag t2 ->
      (* Simple equality check for now *)
      (* Production should support tag intersection/subset semantics *)
      t1 = t2

(** Verify a delegation chain.
    Verifies that:
    1. Each cert is signed by its issuer
    2. Each cert's issuer matches previous cert's subject
    3. Tags are properly delegated (each tag implies the next)
    4. Final cert grants target_tag
    5. All certs allow propagation (except possibly the last)
*)
let verify_chain root_key certs target_tag =
  let rec verify_links current_principal remaining_certs current_tag =
    match remaining_certs with
    | [] ->
        (* End of chain: check if current tag implies target *)
        if tag_implies current_tag target_tag then
          true
        else
          failwith "Tag not granted by certificate chain"

    | signed_cert :: rest ->
        let cert = signed_cert.cert in

        (* Check issuer matches current principal *)
        (match current_principal, cert.issuer with
         | Key k1, Key k2 when k1 = k2 -> ()
         | KeyHash h1, KeyHash h2 when h1.hash = h2.hash -> ()
         | _ -> failwith "Chain break: issuer doesn't match");

        (* Verify signature *)
        let issuer_key = match current_principal with
          | Key k -> k
          | KeyHash _ -> failwith "Cannot verify with key hash (need actual key)"
        in
        if not (verify_signed_cert signed_cert issuer_key) then
          failwith "Invalid signature";

        (* Check tag delegation *)
        if not (tag_implies current_tag cert.tag) then
          failwith "Tag not properly delegated";

        (* Check propagation allowed (except for last cert) *)
        if rest <> [] && not cert.propagate then
          failwith "Delegation not allowed (propagate=false)";

        (* Continue with next link *)
        verify_links cert.subject rest cert.tag
  in

  (* Start with root key and AllPerms *)
  verify_links (Key root_key) certs AllPerms

(**
   Example usage:

   (* Generate keys *)
   let alice_keys = Crypto.generate_keypair () in
   let bob_keys = Crypto.generate_keypair () in

   (* Alice delegates read permission to Bob *)
   let read_tag = Tag (Sexp.List [Sexp.Atom "read"; Sexp.Atom "/data"]) in
   let cert = create_cert
     ~issuer:(Key alice_keys.public)
     ~subject:(Key bob_keys.public)
     ~tag:read_tag
     ~propagate:false
     () in

   let signed_cert = sign_cert cert alice_keys.private_key in

   (* Verify Bob has read permission *)
   let can_read = verify_chain alice_keys.public [signed_cert] read_tag in
*)
