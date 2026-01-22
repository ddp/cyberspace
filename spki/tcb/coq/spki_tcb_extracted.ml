
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _::l' -> succ (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a::l1 -> a::(app l1 m)

type comparison =
| Eq
| Lt
| Gt

module Nat =
 struct
  (** val eqb : int -> int -> bool **)

  let rec eqb n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> true)
        (fun _ -> false)
        m)
      (fun n' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> false)
        (fun m' -> eqb n' m')
        m)
      n

  (** val leb : int -> int -> bool **)

  let rec leb n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> true)
      (fun n' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> false)
        (fun m' -> leb n' m')
        m)
      n

  (** val max : int -> int -> int **)

  let rec max n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun n' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> n)
        (fun m' -> succ (max n' m'))
        m)
      n
 end

module Pos =
 struct
  (** val compare_cont : comparison -> int -> int -> comparison **)

  let rec compare_cont = fun c x y -> if x=y then c else if x<y then Lt else Gt

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val eqb : int -> int -> bool **)

  let rec eqb p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> eqb p0 q0)
        (fun _ -> false)
        (fun _ -> false)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun q0 -> eqb p0 q0)
        (fun _ -> false)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        q)
      p
 end

(** val last : 'a1 list -> 'a1 -> 'a1 **)

let rec last l d =
  match l with
  | [] -> d
  | a::l0 -> (match l0 with
              | [] -> a
              | _::_ -> last l0 d)

(** val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list **)

let rec flat_map f = function
| [] -> []
| x::t -> app (f x) (flat_map f t)

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f = function
| [] -> false
| a::l0 -> (||) (f a) (existsb f l0)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x::l0 -> if f x then x::(filter f l0) else filter f l0

(** val find : ('a1 -> bool) -> 'a1 list -> 'a1 option **)

let rec find f = function
| [] -> None
| x::tl -> if f x then Some x else find f tl

module Z =
 struct
  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val leb : int -> int -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val eqb : int -> int -> bool **)

  let eqb x y =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> true)
        (fun _ -> false)
        (fun _ -> false)
        y)
      (fun p ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun q -> Pos.eqb p q)
        (fun _ -> false)
        y)
      (fun p ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun _ -> false)
        (fun q -> Pos.eqb p q)
        y)
      x

  (** val max : int -> int -> int **)

  let max = Stdlib.max

  (** val min : int -> int -> int **)

  let min = Stdlib.min
 end

(** val eqb0 : char list -> char list -> bool **)

let rec eqb0 s1 s2 =
  match s1 with
  | [] -> (match s2 with
           | [] -> true
           | _::_ -> false)
  | c1::s1' ->
    (match s2 with
     | [] -> false
     | c2::s2' -> if (=) c1 c2 then eqb0 s1' s2' else false)

(** val filter_map : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 list **)

let rec filter_map f = function
| [] -> []
| x::xs ->
  (match f x with
   | Some y -> y::(filter_map f xs)
   | None -> filter_map f xs)

type bytes = int list

(** val bytes_eq : bytes -> bytes -> bool **)

let bytes_eq = Spki_tcb.constant_time_compare

(** val sha512 : bytes -> bytes **)

let sha512 = Spki_tcb.sha512_hash

(** val ed25519_verify : bytes -> bytes -> bytes -> bool **)

let ed25519_verify = Spki_tcb.ed25519_verify

type principal =
| Key of bytes
| KeyHash of bytes

(** val principal_of_key : bytes -> principal **)

let principal_of_key pk =
  KeyHash (sha512 pk)

(** val principal_equal : principal -> principal -> bool **)

let principal_equal p1 p2 =
  match p1 with
  | Key k ->
    (match p2 with
     | Key k2 -> bytes_eq k k2
     | KeyHash h -> bytes_eq (sha512 k) h)
  | KeyHash h ->
    (match p2 with
     | Key k -> bytes_eq h (sha512 k)
     | KeyHash h2 -> bytes_eq h h2)

type tag =
| TagAll
| TagSet of char list list
| TagPrefix of char list * tag
| TagRange of int * int
| TagThreshold of int * tag list

(** val tag_intersect : tag -> tag -> tag option **)

let rec tag_intersect t1 t2 =
  match t1 with
  | TagAll -> Some t2
  | TagSet s1 ->
    (match t2 with
     | TagAll -> Some t1
     | TagSet s2 ->
       let common = filter (fun x -> existsb (eqb0 x) s2) s1 in
       (match common with
        | [] -> None
        | _::_ -> Some (TagSet common))
     | _ -> None)
  | TagPrefix (n1, sub1) ->
    (match t2 with
     | TagAll -> Some t1
     | TagPrefix (n2, sub2) ->
       if eqb0 n1 n2
       then (match tag_intersect sub1 sub2 with
             | Some sub -> Some (TagPrefix (n1, sub))
             | None -> None)
       else None
     | _ -> None)
  | TagRange (lo1, hi1) ->
    (match t2 with
     | TagAll -> Some t1
     | TagRange (lo2, hi2) ->
       let lo = Z.max lo1 lo2 in
       let hi = Z.min hi1 hi2 in
       if Z.leb lo hi then Some (TagRange (lo, hi)) else None
     | _ -> None)
  | TagThreshold (k1, tags1) ->
    (match t2 with
     | TagAll -> Some t1
     | TagThreshold (k2, tags2) ->
       let k = Nat.max k1 k2 in
       let merged =
         flat_map (fun t3 -> filter_map (tag_intersect t3) tags2) tags1
       in
       if Nat.leb k (length merged)
       then Some (TagThreshold (k, merged))
       else None
     | _ -> None)

(** val string_list_eq : char list list -> char list list -> bool **)

let rec string_list_eq l1 l2 =
  match l1 with
  | [] -> (match l2 with
           | [] -> true
           | _::_ -> false)
  | s1::rest1 ->
    (match l2 with
     | [] -> false
     | s2::rest2 -> (&&) (eqb0 s1 s2) (string_list_eq rest1 rest2))

(** val tag_list_eq_aux :
    (tag -> tag -> bool) -> tag list -> tag list -> bool **)

let rec tag_list_eq_aux teq l1 l2 =
  match l1 with
  | [] -> (match l2 with
           | [] -> true
           | _::_ -> false)
  | t1::r1 ->
    (match l2 with
     | [] -> false
     | t2::r2 -> (&&) (teq t1 t2) (tag_list_eq_aux teq r1 r2))

(** val tag_eq : tag -> tag -> bool **)

let rec tag_eq t1 t2 =
  match t1 with
  | TagAll -> (match t2 with
               | TagAll -> true
               | _ -> false)
  | TagSet s1 ->
    (match t2 with
     | TagSet s2 -> string_list_eq s1 s2
     | _ -> false)
  | TagPrefix (n1, sub1) ->
    (match t2 with
     | TagPrefix (n2, sub2) -> (&&) (eqb0 n1 n2) (tag_eq sub1 sub2)
     | _ -> false)
  | TagRange (lo1, hi1) ->
    (match t2 with
     | TagRange (lo2, hi2) -> (&&) (Z.eqb lo1 lo2) (Z.eqb hi1 hi2)
     | _ -> false)
  | TagThreshold (k1, tags1) ->
    (match t2 with
     | TagThreshold (k2, tags2) ->
       (&&) (Nat.eqb k1 k2) (tag_list_eq_aux tag_eq tags1 tags2)
     | _ -> false)

(** val tag_subset : tag -> tag -> bool **)

let tag_subset t1 t2 =
  match tag_intersect t1 t2 with
  | Some result -> tag_eq result t1
  | None -> false

type validity =
| ValidAlways
| ValidNotBefore of int
| ValidNotAfter of int
| ValidBetween of int * int

type cert = { issuer : principal; subject : principal; cert_tag : tag;
              valid : validity; propagate : bool }

type signed_cert = { the_cert : cert; signature : bytes; cert_hash : bytes }

(** val dummy_cert : cert **)

let dummy_cert =
  { issuer = (Key []); subject = (Key []); cert_tag = TagAll; valid =
    ValidAlways; propagate = false }

(** val dummy_signed_cert : signed_cert **)

let dummy_signed_cert =
  { the_cert = dummy_cert; signature = []; cert_hash = [] }

(** val cert_valid_now : signed_cert -> int -> bool **)

let cert_valid_now sc now =
  match sc.the_cert.valid with
  | ValidAlways -> true
  | ValidNotBefore t -> Z.leb t now
  | ValidNotAfter t -> Z.leb now t
  | ValidBetween (t1, t2) -> (&&) (Z.leb t1 now) (Z.leb now t2)

(** val verify_cert_signature : signed_cert -> bytes -> bool **)

let verify_cert_signature sc pk =
  ed25519_verify pk sc.cert_hash sc.signature

type chain_result =
| ChainValid of tag
| ChainInvalid of char list

(** val find_key : principal -> bytes list -> bytes option **)

let find_key p roots =
  match p with
  | Key pk -> if existsb (bytes_eq pk) roots then Some pk else None
  | KeyHash h -> find (fun pk -> bytes_eq (sha512 pk) h) roots

(** val verify_chain_step :
    signed_cert list -> principal -> tag -> bytes list -> int -> chain_result **)

let rec verify_chain_step certs current_principal current_tag roots now =
  match certs with
  | [] -> ChainValid current_tag
  | sc::rest ->
    if negb (principal_equal sc.the_cert.issuer current_principal)
    then ChainInvalid
           ('i'::('s'::('s'::('u'::('e'::('r'::(' '::('m'::('i'::('s'::('m'::('a'::('t'::('c'::('h'::[])))))))))))))))
    else (match find_key sc.the_cert.issuer roots with
          | Some pk ->
            if negb (verify_cert_signature sc pk)
            then ChainInvalid
                   ('s'::('i'::('g'::('n'::('a'::('t'::('u'::('r'::('e'::(' '::('i'::('n'::('v'::('a'::('l'::('i'::('d'::[])))))))))))))))))
            else if negb (cert_valid_now sc now)
                 then ChainInvalid
                        ('c'::('e'::('r'::('t'::(' '::('e'::('x'::('p'::('i'::('r'::('e'::('d'::[]))))))))))))
                 else if (&&) (negb sc.the_cert.propagate)
                           (negb (match rest with
                                  | [] -> true
                                  | _::_ -> false))
                      then ChainInvalid
                             ('d'::('e'::('l'::('e'::('g'::('a'::('t'::('i'::('o'::('n'::(' '::('n'::('o'::('t'::(' '::('p'::('e'::('r'::('m'::('i'::('t'::('t'::('e'::('d'::[]))))))))))))))))))))))))
                      else (match tag_intersect current_tag
                                    sc.the_cert.cert_tag with
                            | Some new_tag ->
                              verify_chain_step rest sc.the_cert.subject
                                new_tag roots now
                            | None ->
                              ChainInvalid
                                ('n'::('o'::(' '::('c'::('o'::('m'::('m'::('o'::('n'::(' '::('c'::('a'::('p'::('a'::('b'::('i'::('l'::('i'::('t'::('i'::('e'::('s'::[])))))))))))))))))))))))
          | None ->
            ChainInvalid
              ('u'::('n'::('k'::('n'::('o'::('w'::('n'::(' '::('i'::('s'::('s'::('u'::('e'::('r'::[])))))))))))))))

(** val verify_chain :
    signed_cert list -> bytes list -> int -> chain_result **)

let verify_chain chain0 roots now =
  match chain0 with
  | [] ->
    ChainInvalid
      ('e'::('m'::('p'::('t'::('y'::(' '::('c'::('h'::('a'::('i'::('n'::[])))))))))))
  | first::_ ->
    let root_principal = first.the_cert.issuer in
    (match find_key root_principal roots with
     | Some _ -> verify_chain_step chain0 root_principal TagAll roots now
     | None ->
       ChainInvalid
         ('r'::('o'::('o'::('t'::(' '::('n'::('o'::('t'::(' '::('t'::('r'::('u'::('s'::('t'::('e'::('d'::[])))))))))))))))))

type auth_request = { requester : principal; action : char list;
                      resource : char list; chain : signed_cert list }

type auth_result =
| Authorized of tag
| Denied of char list

(** val authorize : auth_request -> bytes list -> int -> auth_result **)

let authorize req roots now =
  match verify_chain req.chain roots now with
  | ChainValid t ->
    (match req.chain with
     | [] -> Denied ('n'::('o'::(' '::('c'::('h'::('a'::('i'::('n'::[]))))))))
     | _::_ ->
       let leaf = last req.chain dummy_signed_cert in
       if negb (principal_equal leaf.the_cert.subject req.requester)
       then Denied
              ('r'::('e'::('q'::('u'::('e'::('s'::('t'::('e'::('r'::(' '::('n'::('o'::('t'::(' '::('a'::('u'::('t'::('h'::('o'::('r'::('i'::('z'::('e'::('d'::[]))))))))))))))))))))))))
       else let action_tag = TagSet (req.action::[]) in
            (match tag_intersect t action_tag with
             | Some _ -> Authorized t
             | None ->
               Denied
                 ('a'::('c'::('t'::('i'::('o'::('n'::(' '::('n'::('o'::('t'::(' '::('p'::('e'::('r'::('m'::('i'::('t'::('t'::('e'::('d'::[]))))))))))))))))))))))
  | ChainInvalid reason -> Denied reason
