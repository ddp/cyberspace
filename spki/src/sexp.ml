(** S-expression types and operations for SPKI certificates *)

(** S-expression AST *)
type t =
  | Atom of string
  | List of t list
  | Bytes of bytes  (** Binary data in |base64| notation *)

(** Convert bytes to base64 string *)
let bytes_to_b64 b =
  Base64.encode_exn (Bytes.to_string b)

(** Convert base64 string to bytes *)
let b64_to_bytes s =
  try
    Bytes.of_string (Base64.decode_exn s)
  with _ ->
    failwith ("Invalid base64: " ^ s)

(** Pretty-print s-expression *)
let rec to_string = function
  | Atom s -> s
  | Bytes b -> "|" ^ bytes_to_b64 b ^ "|"
  | List [] -> "()"
  | List xs ->
      "(" ^ String.concat " " (List.map to_string xs) ^ ")"

(** Pretty-print with indentation *)
let rec to_string_indent indent = function
  | Atom s -> s
  | Bytes b -> "|" ^ bytes_to_b64 b ^ "|"
  | List [] -> "()"
  | List (Atom head :: rest) ->
      (* Special case: (atom ...) on one line if short, multi-line if long *)
      let one_line = "(" ^ head ^ " " ^ String.concat " " (List.map to_string rest) ^ ")" in
      if String.length one_line < 60 then
        one_line
      else
        let new_indent = indent ^ "  " in
        "(" ^ head ^ "\n" ^
        String.concat "\n" (List.map (fun x -> new_indent ^ to_string_indent new_indent x) rest) ^
        ")"
  | List xs ->
      let new_indent = indent ^ "  " in
      "(\n" ^
      String.concat "\n" (List.map (fun x -> new_indent ^ to_string_indent new_indent x) xs) ^
      "\n" ^ indent ^ ")"

(** Tokenize input string *)
type token =
  | LParen
  | RParen
  | TAtom of string
  | TBytes of bytes

let tokenize s =
  let len = String.length s in
  let rec loop i acc =
    if i >= len then List.rev acc
    else
      let c = s.[i] in
      match c with
      | ' ' | '\t' | '\n' | '\r' -> loop (i + 1) acc
      | '(' -> loop (i + 1) (LParen :: acc)
      | ')' -> loop (i + 1) (RParen :: acc)
      | '|' ->
          (* Base64 bytes literal: |...| *)
          let rec find_end j =
            if j >= len then failwith "Unterminated bytes literal"
            else if s.[j] = '|' then j
            else find_end (j + 1)
          in
          let end_pos = find_end (i + 1) in
          let b64_str = String.sub s (i + 1) (end_pos - i - 1) in
          let bytes = b64_to_bytes b64_str in
          loop (end_pos + 1) (TBytes bytes :: acc)
      | _ ->
          (* Atom: read until whitespace or paren *)
          let rec read_atom j =
            if j >= len then j
            else
              let c = s.[j] in
              match c with
              | ' ' | '\t' | '\n' | '\r' | '(' | ')' -> j
              | _ -> read_atom (j + 1)
          in
          let end_pos = read_atom i in
          let atom = String.sub s i (end_pos - i) in
          loop end_pos (TAtom atom :: acc)
  in
  loop 0 []

(** Parse tokens into s-expression *)
let parse_tokens tokens =
  let rec parse_list acc = function
    | [] -> failwith "Unexpected end of input"
    | RParen :: rest -> (List.rev acc, rest)
    | LParen :: rest ->
        let (inner, rest') = parse_list [] rest in
        parse_list (List inner :: acc) rest'
    | TAtom s :: rest -> parse_list (Atom s :: acc) rest
    | TBytes b :: rest -> parse_list (Bytes b :: acc) rest
  in
  let parse tokens =
    match tokens with
    | [] -> failwith "Empty input"
    | LParen :: rest ->
        let (sexp, rest') = parse_list [] rest in
        if rest' <> [] then failwith "Unexpected tokens after s-expression"
        else List sexp
    | TAtom s :: rest ->
        if rest <> [] then failwith "Unexpected tokens after s-expression"
        else Atom s
    | TBytes b :: rest ->
        if rest <> [] then failwith "Unexpected tokens after s-expression"
        else Bytes b
    | RParen :: _ -> failwith "Unexpected closing paren"
  in
  parse tokens

(** Parse string into s-expression *)
let of_string s =
  s |> tokenize |> parse_tokens

(** Helper: extract atom value *)
let as_atom = function
  | Atom s -> Some s
  | _ -> None

(** Helper: extract bytes value *)
let as_bytes = function
  | Bytes b -> Some b
  | _ -> None

(** Helper: extract list *)
let as_list = function
  | List xs -> Some xs
  | _ -> None

(** Helper: find tagged value in list *)
let find_tag tag sexp =
  match sexp with
  | List items ->
      List.find_opt (function
        | List (Atom t :: _) when t = tag -> true
        | _ -> false) items
  | _ -> None

(** Helper: extract value after tag *)
let get_tag_value tag sexp =
  match find_tag tag sexp with
  | Some (List (_ :: value :: _)) -> Some value
  | _ -> None
