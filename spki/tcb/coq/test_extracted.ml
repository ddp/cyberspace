(** Test harness for Rocq-extracted TCB code *)

open Spki_tcb_extracted

(* ==============================================================
   Test Infrastructure
   ============================================================== *)

let test_count = ref 0
let pass_count = ref 0
let fail_count = ref 0

let test name f =
  incr test_count;
  try
    f ();
    incr pass_count;
    Printf.printf "  [PASS] %s\n" name
  with e ->
    incr fail_count;
    Printf.printf "  [FAIL] %s: %s\n" name (Printexc.to_string e)

let assert_true msg b =
  if not b then failwith msg

let assert_false msg b =
  if b then failwith msg

(* ==============================================================
   Helper functions to work with extracted types
   ============================================================== *)

(* Convert OCaml string to char list (Rocq string) *)
let char_list_of_string s =
  let len = String.length s in
  let rec loop i acc =
    if i < 0 then acc
    else loop (i - 1) (s.[i] :: acc)
  in
  loop (len - 1) []

(* ==============================================================
   Principal Tests (from extracted code)
   ============================================================== *)

let test_principal () =
  Printf.printf "\n=== Extracted Principal Tests ===\n";

  test "principal_equal reflexive (KeyHash)" (fun () ->
    let hash = [1; 2; 3; 4; 5] in
    let p = KeyHash hash in
    assert_true "p = p" (principal_equal p p)
  );

  test "principal_equal symmetric" (fun () ->
    let hash = [1; 2; 3; 4; 5] in
    let p1 = KeyHash hash in
    let p2 = KeyHash hash in
    assert_true "p1 = p2" (principal_equal p1 p2);
    assert_true "p2 = p1" (principal_equal p2 p1)
  );

  test "different principals not equal" (fun () ->
    let p1 = KeyHash [1; 2; 3] in
    let p2 = KeyHash [4; 5; 6] in
    assert_false "different principals should not be equal" (principal_equal p1 p2)
  );

  test "Key vs KeyHash comparison" (fun () ->
    let key = [1; 2; 3; 4] in
    let p1 = Key key in
    let p2 = principal_of_key key in
    (* p2 should be KeyHash of sha512(key) *)
    assert_true "Key and its KeyHash should be equal" (principal_equal p1 p2)
  )

(* ==============================================================
   Tag Intersection Tests (THE critical security property)
   ============================================================== *)

let test_tag_intersection () =
  Printf.printf "\n=== Extracted Tag Intersection Tests ===\n";

  test "TagAll is identity (left)" (fun () ->
    let read = char_list_of_string "read" in
    let write = char_list_of_string "write" in
    let t = TagSet [read; write] in
    match tag_intersect TagAll t with
    | Some result ->
      (match result with
       | TagSet _ -> ()
       | _ -> failwith "expected TagSet")
    | None -> failwith "expected Some"
  );

  test "TagAll is identity (right)" (fun () ->
    let read = char_list_of_string "read" in
    let t = TagSet [read] in
    match tag_intersect t TagAll with
    | Some _ -> ()
    | None -> failwith "expected Some"
  );

  test "TagSet intersection - common elements" (fun () ->
    let read = char_list_of_string "read" in
    let write = char_list_of_string "write" in
    let execute = char_list_of_string "execute" in
    let t1 = TagSet [read; write] in
    let t2 = TagSet [read; execute] in
    match tag_intersect t1 t2 with
    | Some (TagSet common) ->
      assert_true "should have one common element" (List.length common = 1)
    | Some _ -> failwith "expected TagSet"
    | None -> failwith "expected Some with common element"
  );

  test "TagSet intersection - disjoint" (fun () ->
    let read = char_list_of_string "read" in
    let write = char_list_of_string "write" in
    let t1 = TagSet [read] in
    let t2 = TagSet [write] in
    match tag_intersect t1 t2 with
    | None -> ()
    | Some _ -> failwith "expected None for disjoint sets"
  );

  test "TagRange intersection - overlapping" (fun () ->
    let t1 = TagRange (0, 100) in
    let t2 = TagRange (50, 150) in
    match tag_intersect t1 t2 with
    | Some (TagRange (lo, hi)) ->
      assert_true "lo = 50" (lo = 50);
      assert_true "hi = 100" (hi = 100)
    | Some _ -> failwith "expected TagRange"
    | None -> failwith "expected Some"
  );

  test "TagRange intersection - non-overlapping" (fun () ->
    let t1 = TagRange (0, 50) in
    let t2 = TagRange (60, 100) in
    match tag_intersect t1 t2 with
    | None -> ()
    | Some _ -> failwith "expected None for non-overlapping"
  );

  test "TagPrefix intersection - same name" (fun () ->
    let vault = char_list_of_string "vault" in
    let read = char_list_of_string "read" in
    let write = char_list_of_string "write" in
    let delete = char_list_of_string "delete" in
    let t1 = TagPrefix (vault, TagSet [read; write]) in
    let t2 = TagPrefix (vault, TagSet [read; delete]) in
    match tag_intersect t1 t2 with
    | Some (TagPrefix (_, TagSet common)) ->
      assert_true "common = [read]" (List.length common = 1)
    | Some _ -> failwith "expected TagPrefix with TagSet"
    | None -> failwith "expected Some"
  );

  test "TagPrefix intersection - different names" (fun () ->
    let vault1 = char_list_of_string "vault1" in
    let vault2 = char_list_of_string "vault2" in
    let t1 = TagPrefix (vault1, TagAll) in
    let t2 = TagPrefix (vault2, TagAll) in
    match tag_intersect t1 t2 with
    | None -> ()
    | Some _ -> failwith "expected None for different prefix names"
  );

  test "intersection is idempotent" (fun () ->
    let read = char_list_of_string "read" in
    let t = TagSet [read] in
    match tag_intersect t t with
    | Some _ -> ()
    | None -> failwith "expected Some for idempotent case"
  )

(* ==============================================================
   Tag Subset Tests (derived from intersection)
   ============================================================== *)

let test_tag_subset () =
  Printf.printf "\n=== Extracted Tag Subset Tests ===\n";

  test "everything is subset of TagAll" (fun () ->
    let read = char_list_of_string "read" in
    let t = TagSet [read] in
    assert_true "any ⊆ (*)" (tag_subset t TagAll)
  );

  test "TagRange subset" (fun () ->
    let t1 = TagRange (25, 75) in
    let t2 = TagRange (0, 100) in
    assert_true "[25,75] ⊆ [0,100]" (tag_subset t1 t2)
  )

(* ==============================================================
   Chain Validation Tests
   ============================================================== *)

let test_chain_validation () =
  Printf.printf "\n=== Extracted Chain Validation Tests ===\n";

  test "empty chain fails" (fun () ->
    match verify_chain [] [] 0 with
    | ChainInvalid _ -> ()
    | ChainValid _ -> failwith "empty chain should fail"
  )

(* ==============================================================
   Main
   ============================================================== *)

let () =
  Printf.printf "SPKI TCB Extracted Code Tests\n";
  Printf.printf "==============================\n";
  Printf.printf "(Testing Rocq-extracted authorization logic)\n";

  (* Run tests *)
  test_principal ();
  test_tag_intersection ();
  test_tag_subset ();
  test_chain_validation ();

  (* Summary *)
  Printf.printf "\n==============================\n";
  Printf.printf "Tests: %d | Pass: %d | Fail: %d\n"
    !test_count !pass_count !fail_count;

  if !fail_count > 0 then exit 1 else exit 0
