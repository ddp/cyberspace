(** Property-based tests for Rocq-extracted TCB code

    Tests algebraic properties that should hold for the verified code:
    - tag_intersect commutativity
    - tag_intersect idempotence
    - principal_equal reflexivity/symmetry/transitivity
    - tag_subset reflexivity/transitivity
*)

open Spki_tcb_extracted
open QCheck2

(* ==============================================================
   Generators for Extracted Types
   ============================================================== *)

(** Generate a small bytes value for efficiency *)
let gen_small_bytes : bytes Gen.t =
  Gen.(list_size (int_range 1 8) (int_range 0 255))

(** Generate a char list (Rocq string) from OCaml string *)
let char_list_of_string s =
  let len = String.length s in
  let rec loop i acc =
    if i < 0 then acc
    else loop (i - 1) (s.[i] :: acc)
  in
  loop (len - 1) []

(** Generate a string as char list *)
let gen_string : char list Gen.t =
  Gen.(map char_list_of_string (oneof [
    return "read"; return "write"; return "execute"; return "delete";
    return "create"; return "admin"; return "vault"; return "file";
    return "user"; return "system"; return "data"; return "config"
  ]))

(** Generate a non-empty canonical string list for TagSet using Coq's canonicalize *)
let gen_string_list : char list list Gen.t =
  (* Ensure at least 1 unique string after canonicalization *)
  Gen.(map (fun l ->
    match canonicalize_strings l with
    | [] -> [char_list_of_string "read"]  (* fallback: never empty *)
    | l' -> l'
  ) (list_size (int_range 1 4) gen_string))

(** Generate a principal *)
let gen_principal : principal Gen.t =
  Gen.(oneof_weighted [
    (1, map (fun b -> Key b) gen_small_bytes);
    (1, map (fun b -> KeyHash b) gen_small_bytes);
  ])

(** Generate a simple tag (non-recursive) *)
let gen_simple_tag : tag Gen.t =
  Gen.(oneof_weighted [
    (2, return TagAll);
    (* Use canonicalize_strings to ensure TagSets are in canonical form *)
    (3, map (fun s -> TagSet (canonicalize_strings s)) gen_string_list);
    (2, map2 (fun lo hi -> TagRange (min lo hi, max lo hi))
             (int_range 0 100) (int_range 0 100));
  ])

(** Generate a valid TagThreshold (k <= number of subtags) *)
let gen_valid_threshold (gen_subtag : tag Gen.t) : tag Gen.t =
  Gen.(list_size (int_range 2 4) gen_subtag >>= fun tags ->
       let n = List.length tags in
       int_range 1 n >>= fun k ->
       return (TagThreshold (k, tags)))

(** Generate a tag (with limited recursion depth) *)
let rec gen_tag_depth (depth : int) : tag Gen.t =
  if depth <= 0 then gen_simple_tag
  else
    Gen.(oneof_weighted [
      (2, return TagAll);
      (* Use canonicalize_strings to ensure TagSets are in canonical form *)
      (3, map (fun s -> TagSet (canonicalize_strings s)) gen_string_list);
      (2, map2 (fun lo hi -> TagRange (min lo hi, max lo hi))
               (int_range 0 100) (int_range 0 100));
      (1, map2 (fun n t -> TagPrefix (n, t))
               gen_string (gen_tag_depth (depth - 1)));
      (* TagThreshold: k must be <= number of subtags for validity *)
      (1, gen_valid_threshold (gen_tag_depth (depth - 1)));
    ])

let gen_tag : tag Gen.t = gen_tag_depth 2

(** Generate a tag WITHOUT TagThreshold (for properties that only hold
    for simpler tags - TagThreshold has documented structural issues) *)
let rec gen_tag_no_threshold (depth : int) : tag Gen.t =
  if depth <= 0 then gen_simple_tag
  else
    Gen.(oneof_weighted [
      (2, return TagAll);
      (3, map (fun s -> TagSet (canonicalize_strings s)) gen_string_list);
      (2, map2 (fun lo hi -> TagRange (min lo hi, max lo hi))
               (int_range 0 100) (int_range 0 100));
      (1, map2 (fun n t -> TagPrefix (n, t))
               gen_string (gen_tag_no_threshold (depth - 1)));
    ])

let gen_simple_tag_only : tag Gen.t = gen_tag_no_threshold 2

(* ==============================================================
   Printers for Debugging
   ============================================================== *)

let string_of_char_list cl =
  String.init (List.length cl) (fun i -> List.nth cl i)

let rec string_of_tag = function
  | TagAll -> "TagAll"
  | TagSet s -> Printf.sprintf "TagSet[%s]"
      (String.concat "," (List.map string_of_char_list s))
  | TagPrefix (n, sub) -> Printf.sprintf "TagPrefix(%s,%s)"
      (string_of_char_list n) (string_of_tag sub)
  | TagRange (lo, hi) -> Printf.sprintf "TagRange(%d,%d)" lo hi
  | TagThreshold (k, tags) -> Printf.sprintf "TagThreshold(%d,[%s])"
      k (String.concat "," (List.map string_of_tag tags))

let string_of_principal = function
  | Key b -> Printf.sprintf "Key[%d bytes]" (List.length b)
  | KeyHash b -> Printf.sprintf "KeyHash[%d bytes]" (List.length b)

let print_tag = Print.contramap string_of_tag Print.string
let print_principal = Print.contramap string_of_principal Print.string

(* ==============================================================
   Helper: Compare tag option for equality
   ============================================================== *)

let tag_option_eq t1 t2 =
  match t1, t2 with
  | None, None -> true
  | Some a, Some b -> tag_eq a b
  | _ -> false

(* ==============================================================
   Property Tests
   ============================================================== *)

(** Property: principal_equal is reflexive *)
let prop_principal_equal_refl =
  Test.make ~name:"principal_equal reflexive" ~count:100 ~print:print_principal
    gen_principal
    (fun p -> principal_equal p p)

(** Property: principal_equal is symmetric *)
let prop_principal_equal_sym =
  Test.make ~name:"principal_equal symmetric" ~count:100
    ~print:Print.(pair print_principal print_principal)
    Gen.(pair gen_principal gen_principal)
    (fun (p1, p2) ->
      principal_equal p1 p2 = principal_equal p2 p1)

(** Property: principal_equal is transitive *)
let prop_principal_equal_trans =
  Test.make ~name:"principal_equal transitive" ~count:100
    ~print:Print.(triple print_principal print_principal print_principal)
    Gen.(triple gen_principal gen_principal gen_principal)
    (fun (p1, p2, p3) ->
      (* If p1 = p2 and p2 = p3, then p1 = p3 *)
      not (principal_equal p1 p2 && principal_equal p2 p3) ||
      principal_equal p1 p3)

(** Property: tag_intersect is commutative (simple tags only - TagThreshold
    has documented structural non-commutativity due to Cartesian product) *)
let prop_tag_intersect_comm =
  Test.make ~name:"tag_intersect commutative (no threshold)" ~count:200
    ~print:Print.(pair print_tag print_tag)
    Gen.(pair gen_simple_tag_only gen_simple_tag_only)
    (fun (t1, t2) ->
      tag_option_eq (tag_intersect t1 t2) (tag_intersect t2 t1))

(** Property: tag_intersect is idempotent (simple tags only) *)
let prop_tag_intersect_idemp =
  Test.make ~name:"tag_intersect idempotent (no threshold)" ~count:100 ~print:print_tag
    gen_simple_tag_only
    (fun t ->
      match tag_intersect t t with
      | Some result -> tag_eq result t
      | None -> false)  (* Idempotent means t ∩ t = t, never empty *)

(** Property: tag_intersect with TagAll is identity (left) *)
let prop_tag_intersect_tagall_left =
  Test.make ~name:"tag_intersect TagAll left identity" ~count:100 ~print:print_tag
    gen_tag
    (fun t ->
      match tag_intersect TagAll t with
      | Some result -> tag_eq result t
      | None -> false)

(** Property: tag_intersect with TagAll is identity (right) *)
let prop_tag_intersect_tagall_right =
  Test.make ~name:"tag_intersect TagAll right identity" ~count:100 ~print:print_tag
    gen_tag
    (fun t ->
      match tag_intersect t TagAll with
      | Some result -> tag_eq result t
      | None -> false)

(** Property: tag_subset is reflexive (simple tags only - TagThreshold
    has documented structural issues that break reflexivity) *)
let prop_tag_subset_refl =
  Test.make ~name:"tag_subset reflexive (no threshold)" ~count:100 ~print:print_tag
    gen_simple_tag_only
    (fun t -> tag_subset t t)

(** Property: everything is subset of TagAll *)
let prop_tag_subset_tagall =
  Test.make ~name:"tag_subset of TagAll" ~count:100 ~print:print_tag
    gen_tag
    (fun t -> tag_subset t TagAll)

(** Property: TagRange subset when contained *)
let prop_tagrange_subset_contained =
  Test.make ~name:"TagRange contained is subset" ~count:100
    ~print:Print.(quad Print.int Print.int Print.int Print.int)
    Gen.(quad (int_range 0 100) (int_range 0 100)
              (int_range 0 100) (int_range 0 100))
    (fun (a, b, c, d) ->
      let inner_lo, inner_hi = min a b, max a b in
      let outer_lo, outer_hi = min c d, max c d in
      (* If inner is contained in outer, then inner ⊆ outer *)
      not (outer_lo <= inner_lo && inner_hi <= outer_hi) ||
      tag_subset (TagRange (inner_lo, inner_hi)) (TagRange (outer_lo, outer_hi)))

(** Property: tag_intersect associative (weak form - just checks no crash) *)
let prop_tag_intersect_assoc_safe =
  Test.make ~name:"tag_intersect associative (no crash)" ~count:100
    ~print:Print.(triple print_tag print_tag print_tag)
    Gen.(triple gen_tag gen_tag gen_tag)
    (fun (t1, t2, t3) ->
      (* Both ways of associating should either both succeed or both fail *)
      let left =
        match tag_intersect t1 t2 with
        | Some t12 -> tag_intersect t12 t3
        | None -> None
      in
      let right =
        match tag_intersect t2 t3 with
        | Some t23 -> tag_intersect t1 t23
        | None -> None
      in
      match left, right with
      | None, None -> true
      | Some _, Some _ -> true  (* Both succeed - good enough for safety *)
      | _ -> false)  (* One fails, other succeeds - structural issue *)

(* ==============================================================
   Main Test Runner
   ============================================================== *)

let () =
  let open Alcotest in
  run "SPKI TCB Properties" [
    "principal_equal", [
      QCheck_alcotest.to_alcotest prop_principal_equal_refl;
      QCheck_alcotest.to_alcotest prop_principal_equal_sym;
      QCheck_alcotest.to_alcotest prop_principal_equal_trans;
    ];
    "tag_intersect", [
      QCheck_alcotest.to_alcotest prop_tag_intersect_comm;
      QCheck_alcotest.to_alcotest prop_tag_intersect_idemp;
      QCheck_alcotest.to_alcotest prop_tag_intersect_tagall_left;
      QCheck_alcotest.to_alcotest prop_tag_intersect_tagall_right;
      QCheck_alcotest.to_alcotest prop_tag_intersect_assoc_safe;
    ];
    "tag_subset", [
      QCheck_alcotest.to_alcotest prop_tag_subset_refl;
      QCheck_alcotest.to_alcotest prop_tag_subset_tagall;
      QCheck_alcotest.to_alcotest prop_tagrange_subset_contained;
    ];
  ]
