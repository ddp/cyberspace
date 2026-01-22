(** Spki_tcb - Bridge module for Coq extraction

    This module provides the interface expected by spki_tcb_extracted.ml.
    It converts between Coq's representation (int list) and OCaml's
    native bytes type, then calls the real libsodium-backed implementations.

    Type mapping:
      Coq bytes (list nat) = int list in OCaml
      OCaml bytes = native bytes type
*)

(* ==============================================================
   FFI to real libsodium implementations (from parent directory)
   ============================================================== *)

external sodium_init : unit -> int = "caml_sodium_init"
external ed25519_keypair : unit -> (bytes * bytes) = "caml_ed25519_keypair"
external ed25519_sign_native : bytes -> bytes -> bytes = "caml_ed25519_sign"
external ed25519_verify_native : bytes -> bytes -> bytes -> bool = "caml_ed25519_verify"
external sha512_hash_native : bytes -> bytes = "caml_sha512_hash"
external constant_time_compare_native : bytes -> bytes -> bool = "caml_constant_time_compare"

let _ =
  if sodium_init () < 0 then
    failwith "libsodium init failed"

(* ==============================================================
   Conversion utilities
   ============================================================== *)

(** Convert int list (Coq bytes) to native bytes *)
let bytes_of_int_list (l : int list) : bytes =
  let len = List.length l in
  let b = Bytes.create len in
  List.iteri (fun i v -> Bytes.set b i (Char.chr (v land 0xFF))) l;
  b

(** Convert native bytes to int list (Coq bytes) *)
let int_list_of_bytes (b : bytes) : int list =
  let len = Bytes.length b in
  let rec loop i acc =
    if i < 0 then acc
    else loop (i - 1) (Char.code (Bytes.get b i) :: acc)
  in
  loop (len - 1) []

(* ==============================================================
   Functions expected by spki_tcb_extracted.ml
   ============================================================== *)

(** Constant-time comparison for Coq bytes *)
let constant_time_compare (b1 : int list) (b2 : int list) : bool =
  constant_time_compare_native (bytes_of_int_list b1) (bytes_of_int_list b2)

(** SHA-512 hash for Coq bytes *)
let sha512_hash (data : int list) : int list =
  int_list_of_bytes (sha512_hash_native (bytes_of_int_list data))

(** Ed25519 sign for Coq bytes *)
let ed25519_sign (sk : int list) (msg : int list) : int list =
  int_list_of_bytes (ed25519_sign_native (bytes_of_int_list sk) (bytes_of_int_list msg))

(** Ed25519 verify for Coq bytes *)
let ed25519_verify (pk : int list) (msg : int list) (sig_ : int list) : bool =
  ed25519_verify_native (bytes_of_int_list pk) (bytes_of_int_list msg) (bytes_of_int_list sig_)

(* ==============================================================
   For testing: expose conversion utilities
   ============================================================== *)

let bytes_of_string s =
  let b = Bytes.of_string s in
  int_list_of_bytes b

let string_of_bytes l =
  Bytes.to_string (bytes_of_int_list l)
