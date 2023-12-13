From refinedrust Require Import base util.

(** ** op_types and mem_casts *)

(** [memcast_compat_type] describes how a type can transfered via a
mem_cast (see also [ty_memcast_compat] below):
- MCNone: The type cannot be transferred across a mem_cast.
- MCCopy: The value type can be transferred to a mem_casted value.
- MCId: mem_cast on a value of this type is the identity.

MCId implies the other two and MCCopy implies MCNone.
  *)
Inductive memcast_compat_type : Set :=
| MCNone | MCCopy | MCId.

Definition is_int_ot (ot : op_type) (it : int_type) : Prop :=
  match ot with
    | IntOp it' => it = it' ∧ (ly_size it ≤ MaxInt isize_t)%Z
    | UntypedOp ly => ly = it_layout it ∧ (ly_size it ≤ MaxInt isize_t)%Z
    | _ => False
  end.
Definition is_bool_ot (ot : op_type) : Prop :=
  match ot with | BoolOp => True | UntypedOp ly => ly = it_layout u8 | _ => False end.
Definition is_char_ot (ot : op_type) : Prop :=
  match ot with | CharOp => True | UntypedOp ly => ly = it_layout u32 | _ => False end.
Definition is_ptr_ot (ot : op_type) : Prop :=
  match ot with | PtrOp => True | UntypedOp ly => ly = void* | _ => False end.
Definition is_unit_ot (ot : op_type) : Prop :=
  match ot with | StructOp sl ots => sl = unit_sl ∧ ots = [] | UntypedOp ly => ly = unit_sl | _ => False end.

Lemma is_int_ot_layout it ot:
  is_int_ot ot it → ot_layout ot = it_layout it.
Proof.
  destruct ot => //=; naive_solver.
Qed.
Lemma is_int_ot_size ot it :
  is_int_ot ot it → (ly_size it ≤ MaxInt isize_t)%Z.
Proof.
  destruct ot; try done; intros []; done.
Qed.

Lemma is_bool_ot_layout ot :
  is_bool_ot ot → ot_layout ot = it_layout u8.
Proof. destruct ot => //. Qed.

Lemma is_char_ot_layout ot :
  is_char_ot ot → ot_layout ot = it_layout u32.
Proof. destruct ot => //. Qed.

Lemma is_ptr_ot_layout ot:
  is_ptr_ot ot → ot_layout ot = void*.
Proof. by destruct ot => //= ->. Qed.

Lemma is_unit_ot_layout ot :
  is_unit_ot ot → ot_layout ot = unit_sl.
Proof.
  destruct ot => //=. by intros [-> ->].
Qed.

Section optypes.
  Context `{refinedcG Σ}.
  Lemma mem_cast_compat_id (P : val → iProp Σ) v ot st mt:
    (P v ⊢ ⌜mem_cast_id v ot⌝) →
    (P v ⊢ match mt with | MCNone => True | MCCopy => P (mem_cast v ot st) | MCId => ⌜mem_cast_id v ot⌝ end).
  Proof. iIntros (HP) "HP". iDestruct (HP with "HP") as %Hm. rewrite Hm. by destruct mt. Qed.

  Lemma mem_cast_compat_Untyped (P : val → iProp Σ) v ot st mt:
    ((if ot is UntypedOp _ then False else True) → ⊢ P v -∗ match mt with | MCNone => True | MCCopy => P (mem_cast v ot st) | MCId => ⌜mem_cast_id v ot⌝ end) →
    ⊢ P v -∗ match mt with | MCNone => True | MCCopy => P (mem_cast v ot st) | MCId => ⌜mem_cast_id v ot⌝ end.
  Proof. move => Hot. destruct ot; try by apply: Hot. apply bi.entails_wand'. apply: mem_cast_compat_id. by iIntros "?". Qed.

  Lemma mem_cast_compat_int (P : val → iProp Σ) v ot it:
    is_int_ot ot it →
    (P v ⊢ ⌜∃ z, val_to_Z v it = Some z⌝) →
    (P v ⊢ ⌜mem_cast_id v ot⌝).
  Proof.
    destruct ot => //; simplify_eq/=.
    - intros [<- ?].  etrans; [done|]. iPureIntro => -[??]. by apply: mem_cast_id_int.
    - intros [-> ?]. etrans; [done|]. iPureIntro => -[??]. simpl. done.
  Qed.

  Lemma mem_cast_compat_bool (P : val → iProp Σ) v ot :
    is_bool_ot ot →
    (P v ⊢ ⌜∃ b, val_to_bool v = Some b⌝) →
    (P v ⊢ ⌜mem_cast_id v ot⌝).
  Proof.
    destruct ot => //; simplify_eq/=.
    - intros _.  etrans; [done|]. iPureIntro => -[??]. by apply: mem_cast_id_bool.
    - intros ->. etrans; [done|]. iPureIntro => -[??]. simpl. done.
  Qed.

  Lemma mem_cast_compat_char (P : val → iProp Σ) v ot :
    is_char_ot ot →
    (P v ⊢ ⌜∃ b, val_to_char v = Some b⌝) →
    (P v ⊢ ⌜mem_cast_id v ot⌝).
  Proof.
    destruct ot => //; simplify_eq/=.
    - intros ->. etrans; [done|]. iPureIntro => -[??]. simpl. done.
    - intros _.  etrans; [done|]. iPureIntro => -[??]. by apply: mem_cast_id_char.
  Qed.

  Lemma mem_cast_compat_loc (P : val → iProp Σ) v ot :
    is_ptr_ot ot →
    (P v ⊢ ⌜∃ l, v = val_of_loc l⌝) →
    (P v ⊢ ⌜mem_cast_id v ot⌝).
  Proof.
    destruct ot => //; simplify_eq/=.
    - intros _. etrans; [done|]. iPureIntro => -[? ->]. by apply: mem_cast_id_loc.
    - intros ->. etrans; [done|]. iPureIntro => -[? ->]. done.
  Qed.

  Lemma mem_cast_compat_unit (P : val → iProp Σ) v ot :
    is_unit_ot ot →
    (P v ⊢ ⌜v = zst_val⌝) →
    (P v ⊢ ⌜mem_cast_id v ot⌝).
  Proof.
    destruct ot => //; simplify_eq/=.
    - intros [-> ->]. etrans; first done. iIntros "->" => //.
    - intros ->. etrans; first done. iIntros "->" => //.
  Qed.
End optypes.

Definition is_memcast_val (v : val) (ot : op_type) (v' : val) : Prop :=
  v' = v ∨ ∃ st, v' = mem_cast v ot st.

Lemma is_memcast_val_memcast v ot v' st :
  v `has_layout_val` (ot_layout ot) →
  op_type_wf ot →
  is_memcast_val v ot v' →
  is_memcast_val v ot (mem_cast v' ot st).
Proof.
  intros ?? [-> | [st' ->]].
  - right. eauto.
  - right. exists st'. rewrite mem_cast_idemp; done.
Qed.

Lemma is_memcast_val_untyped_inv v v' ly :
  is_memcast_val v (UntypedOp ly) v' → v = v'.
Proof.
  intros [-> | (st & ->)]; done.
Qed.

Lemma has_layout_val_mem_cast v ly ot st :
  v `has_layout_val` ly →
  mem_cast v ot st `has_layout_val` ly.
Proof.
  rewrite /has_layout_val mem_cast_length //.
Qed.

Lemma is_memcast_val_has_layout_val v v' ot ly :
  is_memcast_val v ot v' →
  v `has_layout_val` ly →
  v' `has_layout_val` ly.
Proof.
  intros [-> | (st & ->)] Hb; first done.
  by apply has_layout_val_mem_cast.
Qed.
Lemma is_memcast_val_has_layout_val' v v' ot ly :
  is_memcast_val v ot v' →
  v' `has_layout_val` ly →
  v `has_layout_val` ly.
Proof.
  intros [-> | (st & ->)]; first done.
  rewrite /has_layout_val mem_cast_length//.
Qed.
Lemma is_memcast_val_length v v' ot :
  is_memcast_val v ot v' →
  length v = length v'.
Proof.
  intros [-> | (st & ->)]; first done.
  rewrite mem_cast_length//.
Qed.

Lemma mem_cast_UntypedOp v ly st :
  mem_cast v (UntypedOp ly) st = v.
Proof. done. Qed.
Lemma is_memcast_val_untyped_app ly1 ly2 ly3 v1 v2 v1' v2' :
  ly_size ly3 = ly_size ly1 + ly_size ly2 →
  is_memcast_val v1 (UntypedOp ly1) v1' →
  is_memcast_val v2 (UntypedOp ly2) v2' →
  is_memcast_val (v1 ++ v2) (UntypedOp ly3) (v1' ++ v2').
Proof.
  intros Hsz H1 H2.
  destruct H1 as [->  | (st1 & ->)]; destruct H2 as [-> | (st2 & ->)]; simpl;
      try rewrite !mem_cast_UntypedOp; by left.
Qed.


(* Q:
    does the syntactical type alone determine the memcast_compat_type?

   In principle, I might imagine that some type uses a syntactic struct type just to have some space, and all ops on it just treat it as a raw byte sequence (UntypedOp). In that case, I should be able to say that  the type is MCNone: if I interpret it as a struct where the padding bytes are poison, something will go wrong.
    On the other hand, has_op_type should always be defined for UntypedOp, at least for MCId (because mem_casts are always identity for UntypedOp). But: because a syn_type does not only have UntypedOp, this does not tell us that that is so for all ots valid for it.
    => In the semantic type interpretation, I should be able to influence how it is memcastable, because that is a semantic property.
      But the syntactic type can determine which op_type it has.

    TODO there might be some interdependency now, in the case of structs, of the syn_type_has_op_type on the mt that is actually allowed by the sematnic type?
      or rather, checking the mt part in case of structs will require a similar recursion as getting the op for a synty. So maybe there is a smart setup for combining it?
        - well, actually. the op_type thiong goes very deep.
          but in the semantic interpretation, we just need to put on top: that the component types match , and that the components are similarly memcasteable [this puts an indirection on the recursion, so we are not really recursive the same way as for the syn_types}


 *)

(*
  - ot is fully determined by the synty
  - mt is determined by the semty
  - for the memcast_compat property of semtys, require
      syn_type_has_op_type ty_syn_ty ot →
      ty_has_memcast_type mt →
      ty_own_val v -∗
      match mt with
      | MCNone => True
      | MCCopy => ty_own_val (mem_cast v ot st)
      | MCId => ⌜mem_cast_id v ot⌝
      end

    for structs: how to define ty_has_memcast_type?
      => well, this depends on the optype with which we access!
          - in general, the components need to have the same memcast_type
          - For StructOp, it can't be id in general, because of padding.
            For UntypedOp, we don't care further.

    so instead:
      define ty_has_op_type ot mt => this is quite similar to RefinedC
        - usually, this will be defined in terms of synty
      and require: ty_has_op_type ot mt → syn_type_has_op_type ty_syn_type ot
        - Do we need this property for anything specific?
          Probably no. But conceptually, the optype should just be fully determined by that.


    => For now, just settle with defining that in terms of semantic types.
        This doesn't quite seem right from a conceptual perspective, because the op_type should already be determined by the syntactic type, but it makes the setup easier.
 *)

(*

(* The op_type of a semantic type should solely depend on its syntactic type and the layout algorithm *)
Fixpoint syn_type_has_op_type `{!LayoutAlg} (synty : syn_type) (ot : op_type) (mt : memcast_compat_type) {struct synty} : Prop :=
  match synty with
  | IntSynType it =>
      is_int_ot ot it
  | BoolSynType => is_bool_ot ot
  | PtrSynType => is_ptr_ot ot
  | FnPtrSynType => is_ptr_ot ot
  | StructSynType sn fields =>
      (* this should match the definition of is_struct_ot *)
      match ot with
      | StructOp sl ots =>
          (* must agree with what the layout alg specifies *)
          use_struct_layout_alg (mk_sls sn fields) = Some sl ∧
          (* check that all the ots are compatible with the field's types *)
          length ots = length fields ∧
          (* TODO the termination checker is not happy about this. possibly because of zip *)
          (*foldr (λ '((_, fty), fot) acc, and (syn_type_has_op_type fty fot) acc) True (zip fields ots)*)
          True
      (* TODO untypedop *)
      | _ => False
      end
  end.

Lemma syn_type_has_op_type_layout_stable `{!LayoutAlg} synty ot ly :
  syn_type_has_op_type synty ot →
  syn_type_has_layout synty ly →
  ot_layout ot = ly.
Proof.
  (* this is a property that should definitely hold. *)
Admitted.

(* options for getting the def through
  - use equations (boo)
  - try a custom fused-foldr-zip (foldr2?). problem: I may need a third list to relate to sl.(sl_fields).
  - don't define this via syn_types, but on types (so that we get it via indirection)
*)

(*Definition is_struct_ot *)

(* TODO *)
 *)

(*
Definition is_struct_ot (sl : struct_layout) (tys : list syn_type) (ot : op_type) :=
  length (field_names sl.(sl_members)) = length tys ∧
  match ot with
  | StructOp sl' ots => sl' = sl ∧ mt ≠ MCId ∧ length ots = length tys ∧
    foldr (λ x, and (x.1.1.(ty_has_op_type) x.2 mt ∧ ot_layout x.2 = x.1.2.2))
          True (zip (zip tys (field_members sl.(sl_members)) ) ots)
  | UntypedOp ly => ly = sl ∧
    foldr (λ x, and (x.1.(ty_has_op_type) (UntypedOp x.2.2) mt))
          True (zip tys (field_members sl.(sl_members)) )
  | _ => False
  end.

Lemma is_struct_ot_layout sl tys ot mt:
  is_struct_ot sl tys ot mt → ot_layout ot = sl.
Proof. move => [?]. destruct ot => //; naive_solver. Qed.
 *)




(* field accesses refer to the layout we quantify over to get the offset -- this is anyways already the case in Caesium


  - in the interpretation of types, we should be able to directly reason about the symbolic offset of a field, for the concrete (existentially quantified) layout that the alg gave us.
      -> how does this nest?
       interp [box inner] v :=
        ∃ l ly,
          use_layout_alg inner.lys = Some ly ∗
          v = val_of_loc l ∗ l `loc_has_layout` ly ∗
          ∃ w, l ↦ w ∗ inner.own w

        interp (struct sls) v :=
          ∃ sl,
            use_struct_layout_alg sls = Some sl ∗
            v `has_layout_val` sl ∗
            [∗ list] field ∈ sl.fields, ...


    types have:
    - syn_type
       require:
       - ty.own v -∗ ∃ ly, use_layout_alg ty.(syn_type) = Some ly ∗ v `has_layout_val` ly
       - has_op_type: can be directly defined in terms of the syn_type
       -
        for the resulting concrete thing, require compatibility with layouts and memcasts similarly to currently.
        essentially, it is just deferred/ behind the ALG abstraction.
 *)

(*
   Maybe we should also, similarly, treat usize/isize and other implementation-defined things like endianness, pointer size?
 *)
