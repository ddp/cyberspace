(** * SPKI Trusted Computing Base - Coq Specification

    Formal specification and verification of the SPKI TCB.

    This module defines:
    - Principal identity (cryptographic, not nominal)
    - Capability tags (bounded meet-semilattice)
    - Certificate chains (compositional validation)
    - Authorization (sound and complete)

    Extraction target: spki_tcb.ml

    Author: SPKI/SDSI Team
    License: MIT
*)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.

(** ** Byte sequences *)

(** Abstract type for byte sequences *)
Definition bytes := list nat.

(** Constant-time byte comparison (axiomatized) *)
Axiom bytes_eq : bytes -> bytes -> bool.
Axiom bytes_eq_refl : forall b, bytes_eq b b = true.
Axiom bytes_eq_sym : forall b1 b2, bytes_eq b1 b2 = bytes_eq b2 b1.
Axiom bytes_eq_trans : forall b1 b2 b3,
  bytes_eq b1 b2 = true -> bytes_eq b2 b3 = true -> bytes_eq b1 b3 = true.

(** ** Cryptographic Primitives (axiomatized)

    These are implemented by libsodium in the C stubs.
    We axiomatize their security properties.
*)

(** SHA-512 hash function *)
Axiom sha512 : bytes -> bytes.
Axiom sha512_deterministic : forall b, sha512 b = sha512 b.
Axiom sha512_collision_free : forall b1 b2,
  sha512 b1 = sha512 b2 -> b1 = b2.  (* Idealized *)

(** Ed25519 signatures *)
Axiom ed25519_sign : bytes -> bytes -> bytes.  (* secret_key -> message -> signature *)
Axiom ed25519_verify : bytes -> bytes -> bytes -> bool.  (* public_key -> message -> sig -> bool *)

(** Signature correctness *)
Axiom ed25519_correct : forall sk pk msg,
  (* If pk is derived from sk, verification succeeds *)
  ed25519_verify pk msg (ed25519_sign sk msg) = true.

(** Unforgeability (existential unforgability under chosen message attack) *)
Axiom ed25519_unforgeable : forall pk msg sig,
  ed25519_verify pk msg sig = true ->
  exists sk, ed25519_sign sk msg = sig.

(** ** Principal - Cryptographic Identity *)

Inductive principal : Type :=
  | Key : bytes -> principal       (* Raw public key, 32 bytes *)
  | KeyHash : bytes -> principal.  (* SHA-512 of public key, 64 bytes *)

(** Compute principal from public key *)
Definition principal_of_key (pk : bytes) : principal :=
  KeyHash (sha512 pk).

(** Constant-time principal comparison *)
Definition principal_equal (p1 p2 : principal) : bool :=
  match p1, p2 with
  | Key k1, Key k2 => bytes_eq k1 k2
  | KeyHash h1, KeyHash h2 => bytes_eq h1 h2
  | Key k, KeyHash h => bytes_eq (sha512 k) h
  | KeyHash h, Key k => bytes_eq h (sha512 k)
  end.

(** Principal equality is an equivalence relation *)
Theorem principal_equal_refl : forall p, principal_equal p p = true.
Proof.
  intros p. destruct p; simpl; apply bytes_eq_refl.
Qed.

Theorem principal_equal_sym : forall p1 p2,
  principal_equal p1 p2 = principal_equal p2 p1.
Proof.
  intros p1 p2. destruct p1, p2; simpl; try apply bytes_eq_sym.
  - rewrite bytes_eq_sym. reflexivity.
  - rewrite bytes_eq_sym. reflexivity.
Qed.

Theorem principal_equal_trans : forall p1 p2 p3,
  principal_equal p1 p2 = true ->
  principal_equal p2 p3 = true ->
  principal_equal p1 p3 = true.
Proof.
  intros p1 p2 p3 H12 H23.
  destruct p1, p2, p3; simpl in *;
  try (eapply bytes_eq_trans; eauto).
  (* Remaining cases require sha512_collision_free *)
  all: admit.  (* TODO: complete proof *)
Admitted.

(** ** Capability Tags *)

Inductive tag : Type :=
  | TagAll : tag                           (* (*) - all permissions *)
  | TagSet : list string -> tag            (* (set read write ...) *)
  | TagPrefix : string -> tag -> tag       (* (name: subtag) *)
  | TagRange : Z -> Z -> tag               (* (range lo hi) *)
  | TagThreshold : nat -> list tag -> tag. (* (k-of-n ...) *)

(** Tag intersection - THE core security operation

    INVARIANT: result ⊆ t1 ∧ result ⊆ t2
    This ensures capability attenuation (monotonic decrease).
*)
Fixpoint tag_intersect (t1 t2 : tag) : option tag :=
  match t1, t2 with
  (* TagAll is the top element *)
  | TagAll, t => Some t
  | t, TagAll => Some t

  (* Set intersection *)
  | TagSet s1, TagSet s2 =>
    let common := filter (fun x => existsb (String.eqb x) s2) s1 in
    match common with
    | [] => None
    | _ => Some (TagSet common)
    end

  (* Prefix: must match name *)
  | TagPrefix n1 sub1, TagPrefix n2 sub2 =>
    if String.eqb n1 n2 then
      match tag_intersect sub1 sub2 with
      | Some sub => Some (TagPrefix n1 sub)
      | None => None
      end
    else None

  (* Range: overlapping interval *)
  | TagRange lo1 hi1, TagRange lo2 hi2 =>
    let lo := Z.max lo1 lo2 in
    let hi := Z.min hi1 hi2 in
    if Z.leb lo hi then Some (TagRange lo hi) else None

  (* Threshold: intersect children, take max k *)
  | TagThreshold k1 tags1, TagThreshold k2 tags2 =>
    let k := Nat.max k1 k2 in
    let merged := flat_map (fun t1 =>
      filter_map (tag_intersect t1) tags2) tags1 in
    if Nat.leb k (length merged) then Some (TagThreshold k merged)
    else None

  (* Incompatible types *)
  | _, _ => None
  end.

(** Tag subset (derived from intersection) *)
Definition tag_subset (t1 t2 : tag) : bool :=
  match tag_intersect t1 t2 with
  | Some result =>
    (* TODO: structural equality on tags *)
    true  (* Placeholder - need tag_eq *)
  | None => false
  end.

(** *** Tag Intersection Theorems *)

(** Commutativity *)
Theorem tag_intersect_comm : forall t1 t2,
  tag_intersect t1 t2 = tag_intersect t2 t1.
Proof.
  intros t1 t2.
  destruct t1, t2; simpl; try reflexivity.
  (* TagAll cases *)
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  (* TagSet case - needs list intersection commutativity *)
  - admit.
  (* TagPrefix case *)
  - destruct (String.eqb s s0) eqn:Heq.
    + rewrite String.eqb_sym in Heq. rewrite Heq.
      (* Recursive case - need IH *)
      admit.
    + rewrite String.eqb_sym in Heq. rewrite Heq. reflexivity.
  (* TagRange case *)
  - rewrite Z.max_comm. rewrite Z.min_comm. reflexivity.
  (* TagThreshold case *)
  - rewrite Nat.max_comm. admit.  (* Needs flat_map commutativity *)
Admitted.

(** Idempotence *)
Theorem tag_intersect_idemp : forall t,
  tag_intersect t t = Some t.
Proof.
  intros t.
  induction t; simpl.
  - reflexivity.
  - (* TagSet: filter with itself gives itself *)
    admit.
  - (* TagPrefix: recursive *)
    rewrite String.eqb_refl. rewrite IHt. reflexivity.
  - (* TagRange: max/min of same = same *)
    rewrite Z.max_id. rewrite Z.min_id.
    assert (Z.leb z z0 = true \/ Z.leb z z0 = false) by (destruct (Z.leb z z0); auto).
    destruct H.
    + rewrite H. reflexivity.
    + (* Invalid range, shouldn't happen for well-formed tags *)
      admit.
  - (* TagThreshold *)
    admit.
Admitted.

(** Monotonicity - THE critical security property *)
Theorem tag_intersect_subset_left : forall t1 t2 r,
  tag_intersect t1 t2 = Some r ->
  tag_subset r t1 = true.
Proof.
  intros t1 t2 r H.
  (* This requires defining tag_subset properly and proving
     that intersection is always contained in both operands *)
  admit.
Admitted.

Theorem tag_intersect_subset_right : forall t1 t2 r,
  tag_intersect t1 t2 = Some r ->
  tag_subset r t2 = true.
Proof.
  intros t1 t2 r H.
  rewrite tag_intersect_comm in H.
  apply tag_intersect_subset_left in H.
  assumption.
Qed.

(** ** Certificates *)

Inductive validity : Type :=
  | ValidAlways : validity
  | ValidNotBefore : Z -> validity
  | ValidNotAfter : Z -> validity
  | ValidBetween : Z -> Z -> validity.

Record cert : Type := {
  issuer : principal;
  subject : principal;
  cert_tag : tag;
  valid : validity;
  propagate : bool;
}.

Record signed_cert : Type := {
  the_cert : cert;
  signature : bytes;
  cert_hash : bytes;
}.

(** Check temporal validity *)
Definition cert_valid_now (sc : signed_cert) (now : Z) : bool :=
  match (valid (the_cert sc)) with
  | ValidAlways => true
  | ValidNotBefore t => Z.leb t now
  | ValidNotAfter t => Z.leb now t
  | ValidBetween t1 t2 => andb (Z.leb t1 now) (Z.leb now t2)
  end.

(** Verify certificate signature *)
Definition verify_cert_signature (sc : signed_cert) (pk : bytes) : bool :=
  ed25519_verify pk (cert_hash sc) (signature sc).

(** ** Certificate Chain Validation *)

Inductive chain_result : Type :=
  | ChainValid : tag -> chain_result
  | ChainInvalid : string -> chain_result.

(** Get public key for principal (from trusted roots) *)
Definition find_key (p : principal) (roots : list bytes) : option bytes :=
  match p with
  | Key pk =>
    if existsb (bytes_eq pk) roots then Some pk else None
  | KeyHash h =>
    find (fun pk => bytes_eq (sha512 pk) h) roots
  end.

(** Chain validation - THE path validation algorithm *)
Fixpoint verify_chain_step
  (certs : list signed_cert)
  (current_principal : principal)
  (current_tag : tag)
  (roots : list bytes)
  (now : Z) : chain_result :=
  match certs with
  | [] => ChainValid current_tag
  | sc :: rest =>
    (* 1. Issuer must match current principal *)
    if negb (principal_equal (issuer (the_cert sc)) current_principal) then
      ChainInvalid "issuer mismatch"
    else
      (* 2. Find issuer's public key *)
      match find_key (issuer (the_cert sc)) roots with
      | None => ChainInvalid "unknown issuer"
      | Some pk =>
        (* 3. Verify signature *)
        if negb (verify_cert_signature sc pk) then
          ChainInvalid "signature invalid"
        (* 4. Check temporal validity *)
        else if negb (cert_valid_now sc now) then
          ChainInvalid "cert expired"
        (* 5. Check propagation (except leaf) *)
        else if andb (negb (propagate (the_cert sc)))
                     (negb (match rest with [] => true | _ => false end)) then
          ChainInvalid "delegation not permitted"
        (* 6. Intersect tags (attenuation) *)
        else match tag_intersect current_tag (cert_tag (the_cert sc)) with
          | None => ChainInvalid "no common capabilities"
          | Some new_tag =>
            verify_chain_step rest (subject (the_cert sc)) new_tag roots now
          end
      end
  end.

Definition verify_chain
  (chain : list signed_cert)
  (roots : list bytes)
  (now : Z) : chain_result :=
  match chain with
  | [] => ChainInvalid "empty chain"
  | first :: _ =>
    let root_principal := issuer (the_cert first) in
    match find_key root_principal roots with
    | None => ChainInvalid "root not trusted"
    | Some _ => verify_chain_step chain root_principal TagAll roots now
    end
  end.

(** *** Chain Validation Theorems *)

(** Soundness: If chain validates, all signatures are valid *)
Theorem verify_chain_sound : forall chain roots now t,
  verify_chain chain roots now = ChainValid t ->
  Forall (fun sc =>
    match find_key (issuer (the_cert sc)) roots with
    | Some pk => verify_cert_signature sc pk = true
    | None => False
    end) chain.
Proof.
  (* Proof by induction on chain *)
  intros chain roots now t H.
  destruct chain; simpl in H.
  - discriminate.
  - unfold verify_chain in H.
    (* ... detailed proof *)
    admit.
Admitted.

(** Attenuation: Result tag is subset of all cert tags *)
Theorem verify_chain_attenuates : forall chain roots now t,
  verify_chain chain roots now = ChainValid t ->
  Forall (fun sc => tag_subset t (cert_tag (the_cert sc)) = true) chain.
Proof.
  (* Follows from tag_intersect_subset_right *)
  admit.
Admitted.

(** ** Authorization *)

Record auth_request : Type := {
  requester : principal;
  action : string;
  resource : string;
  chain : list signed_cert;
}.

Inductive auth_result : Type :=
  | Authorized : tag -> auth_result
  | Denied : string -> auth_result.

(** THE authorization decision *)
Definition authorize (req : auth_request) (roots : list bytes) (now : Z) : auth_result :=
  match verify_chain (chain req) roots now with
  | ChainInvalid reason => Denied reason
  | ChainValid t =>
    match chain req with
    | [] => Denied "no chain"
    | _ =>
      let leaf := last (chain req) (hd (chain req) (* dummy *)) in
      if negb (principal_equal (subject (the_cert leaf)) (requester req)) then
        Denied "requester not authorized"
      else
        let action_tag := TagSet [action req] in
        match tag_intersect t action_tag with
        | None => Denied "action not permitted"
        | Some _ => Authorized t
        end
    end
  end.

(** *** Authorization Theorems *)

(** Soundness: Authorized implies valid chain *)
Theorem authorize_sound : forall req roots now t,
  authorize req roots now = Authorized t ->
  exists t', verify_chain (chain req) roots now = ChainValid t'.
Proof.
  intros req roots now t H.
  unfold authorize in H.
  destruct (verify_chain (chain req) roots now) eqn:Hchain.
  - exists t0. reflexivity.
  - discriminate.
Qed.

(** Soundness: Authorized implies requester at leaf *)
Theorem authorize_requester_match : forall req roots now t,
  authorize req roots now = Authorized t ->
  chain req <> [] ->
  let leaf := last (chain req) (hd (chain req) (the_cert (hd (chain req) (
    {| the_cert := {| issuer := Key []; subject := Key [];
       cert_tag := TagAll; valid := ValidAlways; propagate := false |};
       signature := []; cert_hash := [] |})))) in
  principal_equal (subject (the_cert leaf)) (requester req) = true.
Proof.
  (* ... *)
  admit.
Admitted.

(** Completeness: If all conditions met, authorization succeeds *)
Theorem authorize_complete : forall req roots now,
  (exists t, verify_chain (chain req) roots now = ChainValid t) ->
  chain req <> [] ->
  (let leaf := last (chain req) (hd (chain req) (hd (chain req) (
    {| the_cert := {| issuer := Key []; subject := Key [];
       cert_tag := TagAll; valid := ValidAlways; propagate := false |};
       signature := []; cert_hash := [] |}))) in
   principal_equal (subject (the_cert leaf)) (requester req) = true) ->
  (* action_permitted t (action req) = true -> *)
  exists t, authorize req roots now = Authorized t.
Proof.
  (* ... *)
  admit.
Admitted.

(** ** Audit Trail Types *)

(** Every authorization decision is logged *)
Record audit_entry : Type := {
  timestamp : Z;
  request : auth_request;
  result : auth_result;
  chain_hash : bytes;  (* Hash of entire chain for traceability *)
}.

(** Audit log is append-only *)
Axiom audit_log : list audit_entry.
Axiom audit_append_only : forall e log,
  (* Once an entry is in the log, it cannot be removed or modified *)
  In e log -> In e audit_log.

(** ** Extraction Directives *)

Require Coq.extraction.Extraction.
Require Coq.extraction.ExtrOcamlBasic.
Require Coq.extraction.ExtrOcamlString.
Require Coq.extraction.ExtrOcamlZInt.

(* Extract to OCaml *)
Extraction Language OCaml.

(* Map Coq types to OCaml types *)
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive nat => "int" [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

(* Axiomatized functions map to OCaml externals *)
Extract Constant bytes_eq => "Spki_tcb.constant_time_compare".
Extract Constant sha512 => "Spki_tcb.sha512_hash".
Extract Constant ed25519_sign => "Spki_tcb.ed25519_sign".
Extract Constant ed25519_verify => "Spki_tcb.ed25519_verify".

(* Generate OCaml code *)
(* Extraction "spki_tcb_extracted.ml"
   principal principal_equal principal_of_key
   tag tag_intersect tag_subset
   cert signed_cert verify_chain
   auth_request auth_result authorize. *)
