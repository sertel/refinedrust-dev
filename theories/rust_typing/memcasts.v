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
