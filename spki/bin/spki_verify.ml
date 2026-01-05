(** spki-verify: Verify SPKI certificate chain *)

open Spki

let usage = "Usage: spki-verify --root KEYFILE --chain CERTFILE [--chain CERTFILE ...] --tag TAG\n\
             Verify an SPKI certificate delegation chain.\n\
             \n\
             Required:\n\
             --root FILE         Root public key file\n\
             --chain FILE        Certificate file (can specify multiple)\n\
             --tag TAG           Tag to verify (s-expression)\n\
             \n\
             --help              Show this help\n\
             \n\
             Example:\n\
             spki-verify --root alice.public \\\n\
                         --chain alice-to-bob.cert \\\n\
                         --chain bob-to-carol.cert \\\n\
                         --tag '(read (path /data))'\n"

let read_key_file filename =
  let ic = open_in filename in
  let content = really_input_string ic (in_channel_length ic) in
  close_in ic;
  let sexp = Sexp.of_string content in
  match sexp with
  | Sexp.List [Sexp.Atom "spki-public-key"; Sexp.Bytes key] -> key
  | _ -> failwith ("Invalid public key file: " ^ filename)

let read_cert_file filename =
  let ic = open_in filename in
  let content = really_input_string ic (in_channel_length ic) in
  close_in ic;
  Types.signed_cert_of_string content

let main () =
  let root_file = ref "" in
  let cert_files = ref [] in
  let tag_str = ref "" in

  let args = [
    ("--root", Arg.Set_string root_file, "Root public key");
    ("--chain", Arg.String (fun f -> cert_files := !cert_files @ [f]), "Certificate file");
    ("--tag", Arg.Set_string tag_str, "Tag to verify");
    ("--help", Arg.Unit (fun () -> print_endline usage; exit 0), "Show help");
  ] in

  Arg.parse args (fun _ -> ()) usage;

  (* Validate arguments *)
  if !root_file = "" || !cert_files = [] || !tag_str = "" then begin
    prerr_endline "Error: --root, --chain, and --tag are required";
    prerr_endline usage;
    exit 1
  end;

  (* Read root key *)
  let root_key = read_key_file !root_file in

  (* Read certificate chain *)
  let certs = List.map read_cert_file !cert_files in

  (* Parse target tag *)
  let tag_sexp = Sexp.of_string !tag_str in
  let target_tag = Types.Tag tag_sexp in

  (* Verify chain *)
  Printf.printf "Verifying certificate chain...\n";
  Printf.printf "Root key: %s\n" !root_file;
  Printf.printf "Chain length: %d certificates\n" (List.length certs);
  Printf.printf "Target tag: %s\n" !tag_str;
  Printf.printf "\n";

  try
    let result = Operations.verify_chain root_key certs target_tag in
    if result then begin
      Printf.printf "✓ VALID: Certificate chain grants authorization\n";
      exit 0
    end else begin
      Printf.printf "✗ INVALID: Certificate chain does not grant authorization\n";
      exit 1
    end
  with
  | Failure msg ->
      Printf.eprintf "✗ VERIFICATION FAILED: %s\n" msg;
      exit 1
  | e ->
      Printf.eprintf "✗ ERROR: %s\n" (Printexc.to_string e);
      exit 1

let () = main ()
