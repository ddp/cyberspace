(** spki-keygen: Generate SPKI keypair *)

open Spki

let usage = "Usage: spki-keygen [--output-dir DIR]\n\
             Generates an SPKI keypair and saves to files.\n\
             \n\
             Options:\n\
             --output-dir DIR    Directory to save keys (default: current directory)\n\
             --name NAME         Base name for key files (default: spki-key)\n\
             --help              Show this help\n"

let main () =
  let output_dir = ref "." in
  let key_name = ref "spki-key" in

  let args = [
    ("--output-dir", Arg.Set_string output_dir, "Directory for key files");
    ("--name", Arg.Set_string key_name, "Base name for keys");
    ("--help", Arg.Unit (fun () -> print_endline usage; exit 0), "Show help");
  ] in

  Arg.parse args (fun _ -> ()) usage;

  (* Generate keypair *)
  Printf.printf "Generating SPKI keypair...\n";
  let keypair = Crypto.generate_keypair () in

  (* Compute key hash for display *)
  let key_hash = Crypto.hash_public_key keypair.public in
  let hash_b64 = Base64.encode_string (Bytes.to_string key_hash) in
  Printf.printf "Public key hash: %s\n" hash_b64;

  (* Save private key *)
  let priv_file = Filename.concat !output_dir (!key_name ^ ".private") in
  let priv_sexp = Sexp.List [
    Sexp.Atom "spki-private-key";
    Sexp.Bytes keypair.private_key
  ] in
  let priv_content = Sexp.to_string_indent "" priv_sexp in
  let oc = open_out priv_file in
  output_string oc priv_content;
  close_out oc;
  Printf.printf "Private key saved to: %s\n" priv_file;

  (* Save public key *)
  let pub_file = Filename.concat !output_dir (!key_name ^ ".public") in
  let pub_sexp = Sexp.List [
    Sexp.Atom "spki-public-key";
    Sexp.Bytes keypair.public
  ] in
  let pub_content = Sexp.to_string_indent "" pub_sexp in
  let oc = open_out pub_file in
  output_string oc pub_content;
  close_out oc;
  Printf.printf "Public key saved to: %s\n" pub_file;

  Printf.printf "\nKeypair generation complete!\n";
  Printf.printf "Share your public key hash with friends: %s\n" hash_b64

let () = main ()
