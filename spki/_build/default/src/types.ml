(** SPKI/SDSI certificate types and operations *)

(** Hash algorithm *)
type hash_alg = SHA256

(** Public key (Ed25519) *)
type public_key = bytes

(** Private key (Ed25519) *)
type private_key = bytes

(** Hash of a public key *)
type key_hash = {
  alg: hash_alg;
  hash: bytes;
}

(** Principal: either a key or a hash of a key *)
type principal =
  | Key of public_key
  | KeyHash of key_hash

(** Authorization tag: what the subject is authorized to do *)
type tag =
  | Tag of Sexp.t  (** Generic tag as s-expression *)
  | AllPerms       (** Grants all permissions (use carefully!) *)

(** Time validity *)
type validity = {
  not_before: string;  (** ISO 8601 timestamp *)
  not_after: string;   (** ISO 8601 timestamp *)
}

(** SPKI Certificate *)
type cert = {
  issuer: principal;
  subject: principal;
  tag: tag;
  validity: validity option;
  propagate: bool;  (** Can subject re-delegate? *)
}

(** Signature *)
type signature = {
  hash_alg: hash_alg;
  cert_hash: bytes;  (** Hash of canonical cert s-expression *)
  sig_bytes: bytes;  (** Ed25519 signature *)
}

(** Signed certificate *)
type signed_cert = {
  cert: cert;
  signature: signature;
}

(** Convert hash algorithm to string *)
let hash_alg_to_string = function
  | SHA256 -> "sha256"

(** Convert hash algorithm from string *)
let hash_alg_of_string = function
  | "sha256" -> SHA256
  | s -> failwith ("Unknown hash algorithm: " ^ s)

(** Convert principal to s-expression *)
let principal_to_sexp = function
  | Key k -> Sexp.Bytes k
  | KeyHash { alg; hash } ->
      Sexp.List [
        Sexp.Atom "hash";
        Sexp.Atom (hash_alg_to_string alg);
        Sexp.Bytes hash
      ]

(** Convert s-expression to principal *)
let principal_of_sexp = function
  | Sexp.Bytes k -> Key k
  | Sexp.List [Sexp.Atom "hash"; Sexp.Atom alg_str; Sexp.Bytes h] ->
      KeyHash { alg = hash_alg_of_string alg_str; hash = h }
  | _ -> failwith "Invalid principal s-expression"

(** Convert tag to s-expression *)
let tag_to_sexp = function
  | Tag sexp -> sexp
  | AllPerms -> Sexp.List [Sexp.Atom "*"]

(** Convert s-expression to tag *)
let tag_of_sexp = function
  | Sexp.List [Sexp.Atom "*"] -> AllPerms
  | sexp -> Tag sexp

(** Convert validity to s-expression *)
let validity_to_sexp { not_before; not_after } =
  Sexp.List [
    Sexp.Atom "valid";
    Sexp.List [Sexp.Atom "not-before"; Sexp.Atom not_before];
    Sexp.List [Sexp.Atom "not-after"; Sexp.Atom not_after]
  ]

(** Convert s-expression to validity *)
let validity_of_sexp = function
  | Sexp.List [Sexp.Atom "valid"; before; after] ->
      let not_before = match before with
        | Sexp.List [Sexp.Atom "not-before"; Sexp.Atom ts] -> ts
        | _ -> failwith "Invalid not-before"
      in
      let not_after = match after with
        | Sexp.List [Sexp.Atom "not-after"; Sexp.Atom ts] -> ts
        | _ -> failwith "Invalid not-after"
      in
      { not_before; not_after }
  | _ -> failwith "Invalid validity s-expression"

(** Convert certificate to s-expression *)
let cert_to_sexp { issuer; subject; tag; validity; propagate } =
  let base = [
    Sexp.Atom "cert";
    Sexp.List [Sexp.Atom "issuer"; principal_to_sexp issuer];
    Sexp.List [Sexp.Atom "subject"; principal_to_sexp subject];
    Sexp.List [Sexp.Atom "tag"; tag_to_sexp tag];
  ] in
  let with_validity = match validity with
    | None -> base
    | Some v -> base @ [validity_to_sexp v]
  in
  let with_propagate =
    if propagate then
      with_validity @ [Sexp.List [Sexp.Atom "propagate"]]
    else
      with_validity
  in
  Sexp.List with_propagate

(** Convert s-expression to certificate *)
let cert_of_sexp sexp =
  match sexp with
  | Sexp.List (Sexp.Atom "cert" :: fields) ->
      let issuer = ref None in
      let subject = ref None in
      let tag = ref None in
      let validity = ref None in
      let propagate = ref false in

      List.iter (function
        | Sexp.List [Sexp.Atom "issuer"; p] -> issuer := Some (principal_of_sexp p)
        | Sexp.List [Sexp.Atom "subject"; p] -> subject := Some (principal_of_sexp p)
        | Sexp.List [Sexp.Atom "tag"; t] -> tag := Some (tag_of_sexp t)
        | Sexp.List [Sexp.Atom "valid"; _; _] as v -> validity := Some (validity_of_sexp v)
        | Sexp.List [Sexp.Atom "propagate"] -> propagate := true
        | _ -> ()
      ) fields;

      (match !issuer, !subject, !tag with
       | Some i, Some s, Some t ->
           { issuer = i; subject = s; tag = t; validity = !validity; propagate = !propagate }
       | _ -> failwith "Missing required certificate fields")
  | _ -> failwith "Invalid certificate s-expression"

(** Convert signature to s-expression *)
let signature_to_sexp { hash_alg; cert_hash; sig_bytes } =
  Sexp.List [
    Sexp.Atom "signature";
    Sexp.List [Sexp.Atom "hash"; Sexp.Atom (hash_alg_to_string hash_alg); Sexp.Bytes cert_hash];
    Sexp.Bytes sig_bytes
  ]

(** Convert signed certificate to s-expression *)
let signed_cert_to_sexp { cert; signature } =
  Sexp.List [
    cert_to_sexp cert;
    signature_to_sexp signature
  ]

(** Convert signed cert to canonical string (for display/storage) *)
let signed_cert_to_string sc =
  Sexp.to_string_indent "" (signed_cert_to_sexp sc)

(** Parse signed certificate from string *)
let signed_cert_of_string s =
  let sexp = Sexp.of_string s in
  match sexp with
  | Sexp.List [cert_sexp; Sexp.List (Sexp.Atom "signature" :: sig_fields)] ->
      let cert = cert_of_sexp cert_sexp in
      let hash_alg = ref SHA256 in
      let cert_hash = ref (Bytes.empty) in
      let sig_bytes = ref (Bytes.empty) in

      List.iter (function
        | Sexp.List [Sexp.Atom "hash"; Sexp.Atom alg_str; Sexp.Bytes h] ->
            hash_alg := hash_alg_of_string alg_str;
            cert_hash := h
        | Sexp.Bytes s -> sig_bytes := s
        | _ -> ()
      ) sig_fields;

      { cert; signature = { hash_alg = !hash_alg; cert_hash = !cert_hash; sig_bytes = !sig_bytes } }
  | _ -> failwith "Invalid signed certificate s-expression"
