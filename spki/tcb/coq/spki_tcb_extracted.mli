
val negb : bool -> bool

val length : 'a1 list -> int

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

module Nat :
 sig
  val eqb : int -> int -> bool

  val leb : int -> int -> bool

  val max : int -> int -> int
 end

module Pos :
 sig
  val compare_cont : comparison -> int -> int -> comparison

  val compare : int -> int -> comparison

  val eqb : int -> int -> bool
 end

val last : 'a1 list -> 'a1 -> 'a1

val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list

val existsb : ('a1 -> bool) -> 'a1 list -> bool

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

val find : ('a1 -> bool) -> 'a1 list -> 'a1 option

module Z :
 sig
  val compare : int -> int -> comparison

  val leb : int -> int -> bool

  val eqb : int -> int -> bool

  val max : int -> int -> int

  val min : int -> int -> int
 end

val eqb0 : char list -> char list -> bool

val filter_map : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 list

type bytes = int list

val bytes_eq : bytes -> bytes -> bool

val sha512 : bytes -> bytes

val ed25519_verify : bytes -> bytes -> bytes -> bool

type principal =
| Key of bytes
| KeyHash of bytes

val principal_of_key : bytes -> principal

val principal_equal : principal -> principal -> bool

type tag =
| TagAll
| TagSet of char list list
| TagPrefix of char list * tag
| TagRange of int * int
| TagThreshold of int * tag list

val tag_intersect : tag -> tag -> tag option

val string_list_eq : char list list -> char list list -> bool

val tag_list_eq_aux : (tag -> tag -> bool) -> tag list -> tag list -> bool

val tag_eq : tag -> tag -> bool

val tag_subset : tag -> tag -> bool

type validity =
| ValidAlways
| ValidNotBefore of int
| ValidNotAfter of int
| ValidBetween of int * int

type cert = { issuer : principal; subject : principal; cert_tag : tag;
              valid : validity; propagate : bool }

type signed_cert = { the_cert : cert; signature : bytes; cert_hash : bytes }

val dummy_cert : cert

val dummy_signed_cert : signed_cert

val cert_valid_now : signed_cert -> int -> bool

val verify_cert_signature : signed_cert -> bytes -> bool

type chain_result =
| ChainValid of tag
| ChainInvalid of char list

val find_key : principal -> bytes list -> bytes option

val verify_chain_step :
  signed_cert list -> principal -> tag -> bytes list -> int -> chain_result

val verify_chain : signed_cert list -> bytes list -> int -> chain_result

type auth_request = { requester : principal; action : char list;
                      resource : char list; chain : signed_cert list }

type auth_result =
| Authorized of tag
| Denied of char list

val authorize : auth_request -> bytes list -> int -> auth_result
