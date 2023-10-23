From caesium Require Export base layout.
Set Default Proof Using "Type".

(** * Representation of locations. *)

(** ** Definitions. *)

Declare Scope loc_scope.
Delimit Scope loc_scope with L.
Global Open Scope loc_scope.

(** Physical address. *)
Notation addr := Z (only parsing).

(** Allocation identifier (unique to an allocation), see [heap.v]. *)
Notation alloc_id := Z (only parsing).
Definition dummy_alloc_id : alloc_id := 0.

(** Provenances *)
Inductive prov :=
| ProvNull
| ProvAlloc (aid : option alloc_id)
| ProvFnPtr.
Global Instance prov_inhabited : Inhabited prov := populate ProvNull.
Global Instance prov_eq_dec : EqDecision prov.
Proof. solve_decision. Qed.
Global Instance prov_countable : Countable prov.
Proof.
  refine (inj_countable'
    (λ prov,
     match prov with
     | ProvNull => inl (inl tt)
     | ProvAlloc aid => inl (inr aid)
     | ProvFnPtr => inr tt
     end
    )
    (λ prov,
     match prov with
     | inl (inl _) => ProvNull
     | inl (inr aid) => ProvAlloc aid
     | inr _ => ProvFnPtr
     end) _); abstract by intros [].
Defined.

Definition prov_alloc_id (p : prov) : option alloc_id :=
  if p is ProvAlloc aid then aid else None.

(** Memory location. *)
Definition loc : Set := prov * addr.
Bind Scope loc_scope with loc.

Definition fn_loc (a : addr) : loc := (ProvFnPtr, a).
Definition NULL_loc : loc := (ProvNull, 0).
Global Typeclasses Opaque NULL_loc fn_loc.

(** Shifts location [l] by offset [z]. *)
Definition shift_loc (l : loc) (z : Z) : loc := (l.1, l.2 + z).
Notation "l +ₗ z" := (shift_loc l%L z%Z)
  (at level 50, left associativity) : loc_scope.
Global Typeclasses Opaque shift_loc.

(** Shift a location by [z] times the size of [ly]. *)
Definition offset_loc (l : loc) (ly : layout) (z : Z) : loc := (l +ₗ ly.(ly_size) * z).
Notation "l 'offset{' ly '}ₗ' z" := (offset_loc l%L ly z%Z)
  (at level 50, format "l  'offset{' ly '}ₗ'  z", left associativity) : loc_scope.
Global Typeclasses Opaque offset_loc.

(** Proposition stating that location [l] is aligned to [n] *)
Definition aligned_to (l : loc) (n : nat) : Prop := if caesium_config.enforce_alignment then (n | l.2) else True.
Notation "l `aligned_to` n" := (aligned_to l n) (at level 50) : stdpp_scope.
Arguments aligned_to : simpl never.
Global Typeclasses Opaque aligned_to.

(** Proposition stating that location [l] has the right alignment for layout [ly]. *)
Definition has_layout_loc (l : loc) (ly : layout) : Prop := l `aligned_to` ly_align ly.
Notation "l `has_layout_loc` n" := (has_layout_loc l n) (at level 50) : stdpp_scope.
Arguments has_layout_loc : simpl never.
Global Typeclasses Opaque has_layout_loc.

(** ** Properties of [shift_loc]. *)

Lemma shift_loc_assoc l n1 n2 : l +ₗ n1 +ₗ n2 = l +ₗ (n1 + n2).
Proof. rewrite /shift_loc /=. f_equal. lia. Qed.

Lemma shift_loc_0 l : l +ₗ 0 = l.
Proof. destruct l as [??]. by rewrite /shift_loc Z.add_0_r. Qed.

Lemma shift_loc_assoc_nat l (n1 n2 : nat) : l +ₗ n1 +ₗ n2 = l +ₗ (n1 + n2)%nat.
Proof. rewrite /shift_loc /=. f_equal. lia. Qed.

Lemma shift_loc_0_nat l : l +ₗ 0%nat = l.
Proof. have: Z.of_nat 0%nat = 0 by lia. move => ->. apply shift_loc_0. Qed.

Lemma shift_loc_S l n: l +ₗ S n = (l +ₗ 1%nat +ₗ n).
Proof. by rewrite shift_loc_assoc_nat. Qed.

Lemma shift_loc_inj1 l1 l2 n : l1 +ₗ n = l2 +ₗ n → l1 = l2.
Proof. destruct l1, l2. case => -> ?. f_equal. lia. Qed.

Global Instance shift_loc_inj2 l : Inj (=) (=) (shift_loc l).
Proof. destruct l as [b o]; intros n n' [=?]; lia. Qed.

Lemma shift_loc_block l n : (l +ₗ n).1 = l.1.
Proof. done. Qed.

(** ** Properties of [offset_locs]. *)

Lemma offset_loc_0 l ly : l offset{ly}ₗ 0 = l.
Proof. by rewrite /offset_loc Z.mul_0_r shift_loc_0. Qed.

Lemma offset_loc_S l ly n : l offset{ly}ₗ S n = (l offset{ly}ₗ 1) offset{ly}ₗ n.
Proof. destruct l. rewrite /offset_loc /shift_loc /=. f_equal. lia. Qed.

Lemma offset_loc_1 l ly : l offset{ly}ₗ 1%nat = (l +ₗ ly.(ly_size)).
Proof. destruct l. rewrite /offset_loc /shift_loc /=. f_equal. lia. Qed.

Lemma offset_loc_sz1 ly l n : ly.(ly_size) = 1%nat → l offset{ly}ₗ n = l +ₗ n.
Proof. rewrite /offset_loc => ->. f_equal. lia. Qed.

Lemma offset_loc_offset_loc l ly n1 n2 : l offset{ly}ₗ n1 offset{ly}ₗ n2 = l offset{ly}ₗ (n1 + n2).
Proof. destruct l. rewrite /offset_loc /shift_loc /=. f_equal. lia. Qed.

(** ** Properties about alignment. *)

Lemma ly_with_align_aligned_to l m n:
  l `aligned_to` n →
  is_power_of_two n →
  l `has_layout_loc` ly_with_align m n.
Proof.
  rewrite /has_layout_loc/aligned_to. move => ??. case_match => //.
  by rewrite ly_align_ly_with_align keep_factor2_is_power_of_two.
Qed.

Lemma has_layout_loc_trans l ly1 ly2 :
  l `has_layout_loc` ly2 →
  (ly1.(ly_align_log) ≤ ly2.(ly_align_log))%nat →
  l `has_layout_loc` ly1.
Proof.
  rewrite /has_layout_loc/aligned_to => Hl ?. case_match => //.
  etrans;[|by apply Hl]. by apply Zdivide_nat_pow.
Qed.

Lemma has_layout_loc_trans' l ly1 ly2 :
  l `has_layout_loc` ly2 →
  (ly_align ly1 ≤ ly_align ly2)%nat →
  l `has_layout_loc` ly1.
Proof.
  rewrite -ly_align_log_ly_align_le_iff.
  by apply: has_layout_loc_trans.
Qed.

Lemma has_layout_loc_1 l ly:
  ly_align ly = 1%nat →
  l `has_layout_loc` ly.
Proof.
  rewrite /has_layout_loc/aligned_to => ->. case_match => //. by apply Z.divide_1_l.
Qed.

Lemma has_layout_loc_shift_loc l ly i :
  l `has_layout_loc` ly →
  (ly_align ly | i)%Z →
  (l +ₗ i) `has_layout_loc` ly.
Proof.
  rewrite /has_layout_loc /aligned_to.
  case_match => //.
  simpl. apply Z.divide_add_r.
Qed.
Lemma has_layout_loc_shift_loc_nat l ly i :
  l `has_layout_loc` ly →
  (ly_align ly | i)%nat →
  (l +ₗ i) `has_layout_loc` ly.
Proof.
  rewrite -Nat2Z.divide. apply has_layout_loc_shift_loc.
Qed.

Lemma has_layout_ly_offset l (n : nat) ly:
  l `has_layout_loc` ly →
  (l +ₗ n) `has_layout_loc` ly_offset ly n.
Proof.
  rewrite/has_layout_loc/aligned_to. case_match => //. move => Hl. apply Z.divide_add_r.
  - etrans;[|by apply Hl]. apply Zdivide_nat_pow. rewrite {1}/ly_align_log/=. destruct n; lia.
  - rewrite/ly_offset. destruct n;[by subst;apply Z.divide_0_r|].
    etrans;[apply Zdivide_nat_pow, Nat.le_min_r|]. by apply factor2_divide.
Qed.

Lemma has_layout_loc_ly_mult_offset l ly n:
  layout_wf ly →
  l `has_layout_loc` ly_mult ly (S n) →
  (l +ₗ ly_size ly) `has_layout_loc` ly_mult ly n.
Proof. rewrite /ly_mult/has_layout_loc/aligned_to. case_match => //. move => ??. by apply Z.divide_add_r. Qed.

Lemma has_layout_loc_offset_loc l i ly:
  layout_wf ly →
  l `has_layout_loc` ly →
  (l offset{ly}ₗ i) `has_layout_loc` ly.
Proof.
  rewrite/has_layout_loc/aligned_to. case_match => //.
  move => Hwf Hl. apply Z.divide_add_r; [done|]. etrans; [by apply: Hwf|].
  apply: Z.divide_factor_l.
Qed.

Lemma aligned_to_offset l n off :
  l `aligned_to` n → (n | off) → (l +ₗ off) `aligned_to` n.
Proof. rewrite /aligned_to. case_match => //. apply Z.divide_add_r. Qed.

Lemma aligned_to_add l (n : nat) x:
  (l +ₗ x * n) `aligned_to` n ↔ l `aligned_to` n.
Proof.
  unfold aligned_to. case_match => //. destruct l => /=. rewrite Z.add_comm. split.
  - apply: Z.divide_add_cancel_r. by apply Z.divide_mul_r.
  - apply Z.divide_add_r. by apply Z.divide_mul_r.
Qed.

Lemma aligned_to_mult_eq l n1 n2 off:
  caesium_config.enforce_alignment = true → l `aligned_to` n2 → (l +ₗ off) `aligned_to` (n1 * n2) → (n2 | off).
Proof.
  unfold aligned_to. move => ->. destruct l => /= ??. apply: Z.divide_add_cancel_r => //.
  apply: (Zdivide_mult_l _ n1). by rewrite Z.mul_comm -Nat2Z.inj_mul.
Qed.

#[export] Instance aligned_to_dec l n : Decision (l `aligned_to` n).
Proof. rewrite /aligned_to. case_match; [|apply _]. apply Znumtheory.Zdivide_dec. Qed.
