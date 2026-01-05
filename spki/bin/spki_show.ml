(** spki-show: Display SPKI certificate in human-readable format *)

open Spki

let usage = "Usage: spki-show [FILE]\n\
             Display an SPKI certificate or key in human-readable format.\n\
             \n\
             If FILE is omitted, reads from stdin.\n\
             \n\
             --help              Show this help\n"

let read_file filename =
  let ic = if filename = "-" then stdin else open_in filename in
  let content = really_input_string ic (in_channel_length ic) in
  if filename <> "-" then close_in ic;
  content

let show_key_hash hash =
  Base64.encode_string (Bytes.to_string hash)

let show_principal = function
  | Types.Key k ->
      let hash = Crypto.hash_public_key k in
      Printf.sprintf "Key (hash: %s)" (show_key_hash hash)
  | Types.KeyHash { Types.alg; hash } ->
      Printf.sprintf "KeyHash (%s: %s)"
        (Types.hash_alg_to_string alg)
        (show_key_hash hash)

let show_tag = function
  | Types.Tag sexp -> Sexp.to_string sexp
  | Types.AllPerms -> "(*)"

let show_validity = function
  | None -> "No expiration"
  | Some { Types.not_before; not_after } ->
      Printf.sprintf "%s to %s" not_before not_after

let show_cert cert =
  Printf.printf "SPKI Certificate\n";
  Printf.printf "================\n\n";
  Printf.printf "Issuer:     %s\n" (show_principal cert.Types.issuer);
  Printf.printf "Subject:    %s\n" (show_principal cert.Types.subject);
  Printf.printf "Tag:        %s\n" (show_tag cert.Types.tag);
  Printf.printf "Validity:   %s\n" (show_validity cert.Types.validity);
  Printf.printf "Propagate:  %s\n" (if cert.Types.propagate then "yes" else "no");
  Printf.printf "\n"

let show_signed_cert signed_cert =
  show_cert signed_cert.Types.cert;
  Printf.printf "Signature\n";
  Printf.printf "---------\n";
  Printf.printf "Algorithm:  %s\n"
    (Types.hash_alg_to_string signed_cert.Types.signature.hash_alg);
  Printf.printf "Cert hash:  %s\n"
    (show_key_hash signed_cert.Types.signature.cert_hash);
  Printf.printf "Signature:  %s...\n"
    (String.sub
      (show_key_hash signed_cert.Types.signature.sig_bytes)
      0
      (min 32 (Bytes.length signed_cert.Types.signature.sig_bytes)));
  Printf.printf "\n";
  Printf.printf "S-Expression\n";
  Printf.printf "------------\n";
  Printf.printf "%s\n" (Types.signed_cert_to_string signed_cert)

let show_key key is_private =
  let key_type = if is_private then "Private" else "Public" in
  let hash = Crypto.hash_public_key key in
  Printf.printf "SPKI %s Key\n" key_type;
  Printf.printf "================\n\n";
  Printf.printf "Key hash: %s\n" (show_key_hash hash);
  if is_private then
    Printf.printf "\n⚠  This is a PRIVATE key - keep it secret!\n"

let main () =
  let filename = ref "-" in

  let args = [
    ("--help", Arg.Unit (fun () -> print_endline usage; exit 0), "Show help");
  ] in

  Arg.parse args (fun f -> filename := f) usage;

  (* Read content *)
  let content = read_file !filename in

  (* Try to parse as different types *)
  try
    let sexp = Sexp.of_string content in
    match sexp with
    | Sexp.List [Sexp.Atom "spki-private-key"; Sexp.Bytes key] ->
        show_key key true
    | Sexp.List [Sexp.Atom "spki-public-key"; Sexp.Bytes key] ->
        show_key key false
    | _ ->
        (* Try to parse as signed cert *)
        let signed_cert = Types.signed_cert_of_string content in
        show_signed_cert signed_cert
  with
  | e ->
      Printf.eprintf "Error parsing input: %s\n" (Printexc.to_string e);
      exit 1

let () = main ()
