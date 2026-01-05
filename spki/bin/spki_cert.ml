(** spki-cert: Create and sign SPKI certificate *)

open Spki

let usage = "Usage: spki-cert --issuer KEYFILE --subject KEYFILE --tag TAG [OPTIONS]\n\
             Create and sign an SPKI authorization certificate.\n\
             \n\
             Required:\n\
             --issuer FILE       Issuer's private key file\n\
             --subject FILE      Subject's public key file\n\
             --tag TAG           Authorization tag (s-expression)\n\
             \n\
             Optional:\n\
             --propagate         Allow subject to re-delegate (default: false)\n\
             --not-before TIME   Validity start time (ISO 8601)\n\
             --not-after TIME    Validity end time (ISO 8601)\n\
             --output FILE       Output file (default: stdout)\n\
             --help              Show this help\n\
             \n\
             Example tags:\n\
             '(read (path /library/lamport-papers))'\n\
             '(spawn-agent (max-count 5))'\n\
             '(write (path /shared/notes))'\n"

let read_key_file filename =
  let ic = open_in filename in
  let content = really_input_string ic (in_channel_length ic) in
  close_in ic;
  let sexp = Sexp.of_string content in
  match sexp with
  | Sexp.List [Sexp.Atom "spki-private-key"; Sexp.Bytes key] ->
      (key, true)  (* private key *)
  | Sexp.List [Sexp.Atom "spki-public-key"; Sexp.Bytes key] ->
      (key, false)  (* public key *)
  | _ -> failwith ("Invalid key file format: " ^ filename)

let main () =
  let issuer_file = ref "" in
  let subject_file = ref "" in
  let tag_str = ref "" in
  let propagate = ref false in
  let not_before = ref "" in
  let not_after = ref "" in
  let output_file = ref "" in

  let args = [
    ("--issuer", Arg.Set_string issuer_file, "Issuer private key");
    ("--subject", Arg.Set_string subject_file, "Subject public key");
    ("--tag", Arg.Set_string tag_str, "Authorization tag");
    ("--propagate", Arg.Set propagate, "Allow re-delegation");
    ("--not-before", Arg.Set_string not_before, "Validity start");
    ("--not-after", Arg.Set_string not_after, "Validity end");
    ("--output", Arg.Set_string output_file, "Output file");
    ("--help", Arg.Unit (fun () -> print_endline usage; exit 0), "Show help");
  ] in

  Arg.parse args (fun _ -> ()) usage;

  (* Validate required arguments *)
  if !issuer_file = "" || !subject_file = "" || !tag_str = "" then begin
    prerr_endline "Error: --issuer, --subject, and --tag are required";
    prerr_endline usage;
    exit 1
  end;

  (* Read keys *)
  let (issuer_key, issuer_is_private) = read_key_file !issuer_file in
  let (subject_key, _) = read_key_file !subject_file in

  if not issuer_is_private then begin
    prerr_endline "Error: issuer key must be a private key";
    exit 1
  end;

  (* Parse tag *)
  let tag_sexp = Sexp.of_string !tag_str in
  let tag = Types.Tag tag_sexp in

  (* Parse validity if provided *)
  let validity =
    if !not_before <> "" && !not_after <> "" then
      Some { Types.not_before = !not_before; not_after = !not_after }
    else
      None
  in

  (* Create certificate *)
  let cert = Operations.create_cert
    ~issuer:(Types.Key issuer_key)
    ~subject:(Types.Key subject_key)
    ~tag
    ~validity
    ~propagate:!propagate
    ()
  in

  (* Extract public key from issuer's private key for signing *)
  (* In the placeholder implementation, we need the private key bytes *)
  let signed_cert = Operations.sign_cert cert issuer_key in

  (* Output certificate *)
  let cert_str = Types.signed_cert_to_string signed_cert in

  if !output_file = "" then
    print_endline cert_str
  else begin
    let oc = open_out !output_file in
    output_string oc cert_str;
    close_out oc;
    Printf.eprintf "Certificate saved to: %s\n" !output_file
  end

let () = main ()
