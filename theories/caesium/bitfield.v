From stdpp.unstable Require Import bitblast.
From lithium Require Import simpl_classes definitions.
From caesium Require Import base int_type builtins_specs.

(* raw bit vector constructors *)

Definition bf_nil : Z := 0.

Definition bf_cons (a k x : Z) (l : Z) :=
  Z.lor (x ≪ a) l.

Definition bf_mask_cons (a k : Z) (l : Z) : Z :=
  Z.lor (Z.ones k ≪ a) l.

Definition bf_slice (a k : Z) (bv : Z) : Z :=
  Z.land (bv ≫ a) (Z.ones k).

Definition bf_update (a k x : Z) (bv : Z) : Z :=
  Z.lor (Z.land bv (Z.lnot (Z.ones k ≪ a))) (x ≪ a).

(* singleton list *)

Lemma bf_shr_singleton a k x :
  0 ≤ a → (bf_cons a k x bf_nil) ≫ a = x.
Proof.
  rewrite /bf_cons /bf_nil => ?.
  bitblast.
Qed.

Lemma bf_cons_singleton_z_iff a k x :
  0 ≤ a →
  bf_cons a k x bf_nil = 0 ↔ x = 0.
Proof.
  move => ?. rewrite /bf_cons /bf_nil Z.lor_0_r.
  by apply Z.shiftl_eq_0_iff.
Qed.

Lemma bf_cons_singleton_nz_iff a k x :
  0 ≤ a →
  bf_cons a k x bf_nil ≠ 0 ↔ x ≠ 0.
Proof.
  move => ?. by apply not_iff_compat, bf_cons_singleton_z_iff.
Qed.

Lemma bf_cons_bool_singleton_false_iff a b :
  0 ≤ a →
  bf_cons a 1 (bool_to_Z b) bf_nil = 0 ↔ b = false.
Proof.
  move => ?. rewrite bf_cons_singleton_z_iff; last done.
  by destruct b.
Qed.

Lemma bf_cons_bool_singleton_true_iff a b :
  0 ≤ a →
  bf_cons a 1 (bool_to_Z b) bf_nil ≠ 0 ↔ b = true.
Proof.
  move => ?. rewrite bf_cons_singleton_nz_iff; last done.
  by destruct b.
Qed.

Lemma bf_mask_cons_singleton a k :
  bf_mask_cons a k bf_nil = (Z.ones k) ≪ a.
Proof.
  rewrite /bf_mask_cons /bf_nil.
  bitblast.
Qed.

Lemma bf_mask_cons_singleton_nonempty a k :
  0 ≤ a → 0 < k → bf_mask_cons a k bf_nil > 0.
Proof.
  intros.
  rewrite bf_mask_cons_singleton Z.ones_equiv Z.shiftl_mul_pow2; last lia.
  apply Zmult_gt_0_compat.
  - suff : 2 ^ 0 < 2 ^ k by lia.
    apply Z.pow_lt_mono_r. all: lia.
  - suff : 0 < 2 ^ a by lia.
    by apply Z.pow_pos_nonneg.
Qed.

(* Rewriting rules *)

Lemma bf_land_nil bv :
  Z.land bv bf_nil = bf_nil.
Proof.
  by rewrite Z.land_0_r.
Qed.

Lemma bf_land_mask_cons bv a k l :
  0 ≤ a → 0 ≤ k →
  Z.land bv (bf_mask_cons a k l) = bf_cons a k (bf_slice a k bv) (Z.land bv l).
Proof.
  rewrite /bf_cons /bf_mask_cons /bf_slice => ??.
  bitblast.
Qed.

Lemma bf_land_mask_flip bv a k N :
  0 ≤ a → 0 ≤ k → a + k ≤ N →
  0 ≤ bv < 2 ^ N →
  Z.land bv (Z_lunot N (bf_mask_cons a k bf_nil)) = bf_update a k 0 bv.
Proof.
  rewrite /bf_mask_cons /bf_update /bf_nil /Z_lunot => ????.
  bitblast.
Qed.

Lemma bf_lor_nil_l bv :
  Z.lor bf_nil bv = bv.
Proof. done. Qed.

Lemma bf_lor_nil_r bv :
  Z.lor bv bf_nil = bv.
Proof.
  by rewrite Z.lor_0_r.
Qed.

Lemma bf_lor_update a k x x' dl1 dl2 :
  0 ≤ a → 0 ≤ k →
  x = 0 →
  Z.lor (bf_cons a k x dl1) (bf_cons a k x' dl2) = bf_cons a k x' (Z.lor dl1 dl2).
Proof.
  move => ? ? ->.
  rewrite /bf_cons.
  bitblast.
Qed.

Lemma bf_lor_update_ne a1 k1 x1 a2 k2 x2 dl1 dl2 :
  0 ≤ a1 → 0 ≤ k1 → 0 ≤ a2 → 0 ≤ k2 →
  (a1 + k1 ≤ a2 ∨ a2 + k2 ≤ a1) →
  Z.lor (bf_cons a1 k1 x1 dl1) (bf_cons a2 k2 x2 dl2) = bf_cons a1 k1 x1 (Z.lor dl1 (bf_cons a2 k2 x2 dl2)).
Proof.
  rewrite /bf_cons => ?????.
  bitblast.
Qed.

Lemma bf_lor_mask_cons_l a k x dl1 dl2 :
  0 ≤ a → 0 ≤ k →
  x = 0 →
  Z.lor (bf_mask_cons a k dl1) (bf_cons a k x dl2) = bf_cons a k (Z.ones k) (Z.lor dl1 dl2).
Proof.
  move => ? ? ->.
  rewrite /bf_cons /bf_mask_cons.
  bitblast.
Qed.

Lemma bf_lor_mask_cons_ne_l a1 k1 x1 a2 k2 dl1 ml :
  0 ≤ a1 → 0 ≤ k1 → 0 ≤ a2 → 0 ≤ k2 →
  (a1 + k1 ≤ a2 ∨ a2 + k2 ≤ a1) →
  Z.lor (bf_mask_cons a1 k1 ml) (bf_cons a2 k2 x1 dl1) = bf_cons a2 k2 x1 (Z.lor dl1 (bf_mask_cons a1 k1 ml)).
Proof.
  rewrite /bf_cons /bf_mask_cons => ?????.
  bitblast.
Qed.

Lemma bf_lor_mask_cons_r a k x dl1 dl2 :
  0 ≤ a → 0 ≤ k →
  x = 0 →
  Z.lor (bf_cons a k x dl1) (bf_mask_cons a k dl2) = bf_cons a k (Z.ones k) (Z.lor dl1 dl2).
Proof.
  move => ? ? ->.
  rewrite /bf_cons /bf_mask_cons.
  bitblast.
Qed.

Lemma bf_lor_mask_cons a1 k1 dl1 a2 k2 dl2 :
  0 ≤ a1 → 0 ≤ k1 → 0 ≤ a2 → 0 ≤ k2 →
  (a1 + k1 ≤ a2 ∨ a2 + k2 ≤ a1) →
  Z.lor (bf_mask_cons a1 k1 dl1) (bf_mask_cons a2 k2 dl2) = bf_mask_cons a1 k1 (Z.lor dl1 (bf_mask_cons a2 k2 dl2)).
Proof.
  rewrite /bf_cons /bf_mask_cons => ?????.
  bitblast.
Qed.

Lemma bf_lor_mask_cons_ne_r a1 k1 x1 a2 k2 dl1 ml :
  0 ≤ a1 → 0 ≤ k1 → 0 ≤ a2 → 0 ≤ k2 →
  (a1 + k1 ≤ a2 ∨ a2 + k2 ≤ a1) →
  Z.lor (bf_cons a1 k1 x1 dl1) (bf_mask_cons a2 k2 ml) = bf_cons a1 k1 x1 (Z.lor dl1 (bf_mask_cons a2 k2 ml)).
Proof.
  rewrite /bf_cons /bf_mask_cons => ?????.
  bitblast.
Qed.

Lemma bf_slice_nil a k :
  bf_slice a k bf_nil = 0.
Proof.
  rewrite /bf_slice /bf_nil.
  bitblast.
Qed.

Definition bf_range_empty a k bv : Prop :=
  ∀ i, a ≤ i < a + k → Z.testbit bv i = false.

Lemma bf_range_empty_nil a k :
  bf_range_empty a k bf_nil.
Proof.
  rewrite /bf_range_empty /bf_nil => i ?.
  by rewrite Z.bits_0.
Qed.

Lemma bf_range_empty_cons a k x l a' k' :
  0 ≤ a → 0 ≤ k → 0 ≤ a' → 0 ≤ k' →
  0 ≤ x < 2^k →
  (a + k ≤ a' ∨ a' + k' ≤ a) →
  bf_range_empty a' k' (bf_cons a k x l) ↔ bf_range_empty a' k' l.
Proof.
  rewrite /bf_range_empty /bf_cons => ???? [??] Hor.
  split.
  - move => Hl i [??]. by bitblast Hl with i.
  - move => Hl i [??]. bitblast. apply Hl. lia.
Qed.

Lemma bf_slice_cons a k x l :
  0 ≤ a → 0 ≤ k →
  0 ≤ x < 2^k →
  bf_range_empty a k l →
  bf_slice a k (bf_cons a k x l) = x.
Proof.
  rewrite /bf_slice /bf_cons => ??? Hi.
  bitblast.
  rewrite Hi; [by simpl_bool | lia].
Qed.

Lemma bf_slice_cons_ne a k x a' k' l :
  0 ≤ a → 0 ≤ k → 0 ≤ a' → 0 ≤ k' →
  0 ≤ x < 2^k →
  (a + k ≤ a' ∨ a' + k' ≤ a) →
  bf_slice a' k' (bf_cons a k x l) = bf_slice a' k' l.
Proof.
  rewrite /bf_slice /bf_cons => ????? [?|?].
  all: bitblast.
Qed.

Lemma bf_update_nil a k x :
  bf_update a k x bf_nil = bf_cons a k x bf_nil.
Proof.
  rewrite /bf_update /bf_nil /bf_cons.
  bitblast.
Qed.

Lemma bf_update_cons a k x x' dl :
  0 ≤ a → 0 ≤ k →
  0 ≤ x < 2^k →
  bf_range_empty a k dl →
  bf_update a k x' (bf_cons a k x dl) = bf_cons a k x' dl.
Proof.
  rewrite /bf_update /bf_nil /bf_cons => ??? Hi.
  bitblast.
  rewrite Hi; [by simpl_bool | lia].
Qed.

Lemma bf_update_cons_ne a k x a' k' x' dl :
  0 ≤ a → 0 ≤ k → 0 ≤ a' → 0 ≤ k' →
  0 ≤ x < 2^k →
  (a + k ≤ a' ∨ a' + k' ≤ a) →
  bf_update a' k' x' (bf_cons a k x dl) = bf_cons a k x (bf_update a' k' x' dl).
Proof.
  rewrite /bf_update /bf_nil /bf_cons => ????? [?|?].
  all: bitblast.
Qed.

(* rewrite & simpl rules *)
Create HintDb bitfield_rewrite discriminated.

#[export] Hint Rewrite bf_land_nil : bitfield_rewrite.
#[export] Hint Rewrite bf_land_mask_cons using can_solve : bitfield_rewrite.
#[export] Hint Rewrite bf_land_mask_flip using can_solve : bitfield_rewrite.

#[export] Hint Rewrite bf_lor_nil_l : bitfield_rewrite.
#[export] Hint Rewrite bf_lor_nil_r : bitfield_rewrite.
#[export] Hint Rewrite bf_lor_update using lia : bitfield_rewrite.
#[export] Hint Rewrite bf_lor_update_ne using lia : bitfield_rewrite.
#[export] Hint Rewrite bf_lor_mask_cons_l using lia : bitfield_rewrite.
#[export] Hint Rewrite bf_lor_mask_cons_ne_l using lia : bitfield_rewrite.
#[export] Hint Rewrite bf_lor_mask_cons_r using lia : bitfield_rewrite.
#[export] Hint Rewrite bf_lor_mask_cons_ne_r using lia : bitfield_rewrite.
#[export] Hint Rewrite bf_lor_mask_cons using lia : bitfield_rewrite.

#[export] Hint Rewrite bf_slice_nil : bitfield_rewrite.
#[export] Hint Rewrite bf_slice_cons using can_solve : bitfield_rewrite.
#[export] Hint Rewrite bf_slice_cons_ne using lia : bitfield_rewrite.

#[export] Hint Rewrite bf_update_nil : bitfield_rewrite.
#[export] Hint Rewrite bf_update_cons using can_solve : bitfield_rewrite.
#[export] Hint Rewrite bf_update_cons_ne using lia : bitfield_rewrite.

(* Tactic to normalize a bitfield *)
Ltac normalize_bitfield :=
  autorewrite with bitfield_rewrite; exact: eq_refl.

(* enable using normalize_bitfield with tactic_hint *)
Definition normalize_bitfield {Σ} (bv : Z) (T : Z → iProp Σ) : iProp Σ := T bv.
Global Typeclasses Opaque normalize_bitfield.

Program Definition li_normalize_bitfield {Σ} bv norm :
  bv = norm →
  LiTactic (normalize_bitfield (Σ:=Σ) bv) := λ H, {|
    li_tactic_P T := T norm;
|}.
Next Obligation. move => ??? -> ?. unfold normalize_bitfield. iIntros "$". Qed.

Global Hint Extern 10 (LiTactic (normalize_bitfield _)) =>
  eapply li_normalize_bitfield; normalize_bitfield : typeclass_instances.

(* enable using normalize_bitfield in function call specifications
where one cannot use tactic_hint *)
(* TODO: figure out how to make the following unnecessary *)
Definition normalize_bitfield_eq (bv norm : Z) : Prop := bv = norm.
Global Typeclasses Opaque normalize_bitfield_eq.

Class NormalizeBitfield (bv norm : Z) : Prop :=
  normalize_bitfield_proof : bv = norm.

Global Instance simpl_and_normalize_bitfield bv norm `{!NormalizeBitfield bv norm'} `{!IsProtected norm} :
  SimplAnd (normalize_bitfield_eq bv norm) (λ T, norm' = norm ∧ T).
Proof. erewrite normalize_bitfield_proof. done. Qed.

Global Hint Extern 10 (NormalizeBitfield _ _) =>
  normalize_bitfield : typeclass_instances.


(* Side cond: ∀ i ∈ I, Z.testbit bv i = false. *)
Global Instance bf_range_empty_nil_inst a k :
  SimplAnd (bf_range_empty a k bf_nil) (λ T, T).
Proof.
  have ? := bf_range_empty_nil.
  split; naive_solver.
Qed.

Global Instance bf_range_empty_cons_inst a k x l a' k'
  `{!CanSolve (0 ≤ a ∧ 0 ≤ k ∧ 0 ≤ a' ∧ 0 ≤ k')}
  `{!CanSolve (0 ≤ x < 2^k)}
  `{!CanSolve (a + k ≤ a' ∨ a' + k' ≤ a)} :
  SimplAnd (bf_range_empty a' k' (bf_cons a k x l)) (λ T, bf_range_empty a' k' l ∧ T).
Proof.
  unfold CanSolve in *.
  have ? := bf_range_empty_cons.
  split; naive_solver.
Qed.

(* Simplify singleton data list =/≠ 0 *)

Global Instance bf_cons_singleton_z a k x `{!CanSolve (0 ≤ a)} :
  SimplBothRel (=) 0 (bf_cons a k x bf_nil) (x = 0).
Proof.
  have := (bf_cons_singleton_z_iff a k x).
  split; naive_solver.
Qed.

Global Instance bf_cons_singleton_nz_1 a k x `{!CanSolve (0 ≤ a)} :
  SimplBoth (bf_cons a k x bf_nil ≠ 0) (x ≠ 0).
Proof.
  have := (bf_cons_singleton_nz_iff a k x).
  split; naive_solver.
Qed.
Global Instance bf_cons_singleton_nz_2 a k x `{!CanSolve (0 ≤ a)} :
  SimplBoth (0 ≠ bf_cons a k x bf_nil) (x ≠ 0).
Proof.
  have := (bf_cons_singleton_nz_iff a k x).
  split; naive_solver.
Qed.

(* Simplify data list eq *)

Global Instance bf_cons_eq a k x1 l1 x2 l2 :
  SimplAndUnsafe (bf_cons a k x1 l1 = bf_cons a k x2 l2) (λ T, x1 = x2 ∧ l1 = l2 ∧ T).
Proof.
  unfold CanSolve, SimplAndUnsafe in *.
  naive_solver.
Qed.

(* Linux macros for bits *)

Lemma Z_shl_bound a k x N :
  0 ≤ a → 0 ≤ k → a + k ≤ N →
  0 ≤ x < 2 ^ a →
  x ≤ x ≪ k ≤ 2 ^ N - 1.
Proof.
  intros. rewrite Z.shiftl_mul_pow2; last lia.
  destruct (decide (x = 0)) as [->|].
  - rewrite Z.mul_0_l.
    have ? : 0 < 2 ^ N. { apply Z.pow_pos_nonneg. all: lia. }
    lia.
  - split.
    + apply Z.le_mul_diag_r; first lia.
      suff : 0 < 2 ^ k by lia.
      by apply Z.pow_pos_nonneg.
    + suff : (x * 2 ^ k) < 2 ^ N by lia.
      apply Z.log2_lt_cancel.
      rewrite Z.log2_mul_pow2 ?Z.log2_pow2; [|lia..].
      have ? : Z.log2 x < a. { apply Z.log2_lt_pow2. all: lia. }
      lia.
Qed.

Lemma Z_shiftl_1_range i N :
  0 ≤ i < N → 1 ≤ 1 ≪ i ≤ 2 ^ N - 1.
Proof.
  intros.
  apply (Z_shl_bound 1 _ _ _). all: lia.
Qed.

Lemma bf_mask_bit i :
  1 ≪ i = bf_mask_cons i 1 bf_nil.
Proof.
  rewrite /bf_mask_cons /bf_nil.
  bitblast.
Qed.

Lemma bf_mask_high N k :
  0 ≤ k ≤ N → 2 ^ N - 1 - 1 ≪ k + 1 = bf_mask_cons k (N - k) bf_nil.
Proof.
  intros.
  rewrite bf_mask_cons_singleton Z.ones_equiv !Z.shiftl_mul_pow2; [|lia..].
  rewrite Z.mul_pred_l -Z.pow_add_r ?Z.sub_add; lia.
Qed.

Lemma bf_mask_gen h l N :
  0 ≤ l → l < h < N →
  Z.land (2 ^ N - 1 - 1 ≪ l + 1) ((2 ^ N - 1) ≫ (N - 1 - h)) = bf_mask_cons l (h - l + 1) bf_nil.
Proof.
  intros.
  rewrite bf_mask_high /bf_mask_cons /bf_nil; last lia.
  have -> : 2 ^ N - 1 = Z.pred (2 ^ N) by lia.
  rewrite -Z.ones_equiv.
  bitblast.
Qed.

Lemma Z_least_significant_one_nonempty_mask (a k : Z) :
  0 ≤ a → 0 < k →
  Z_least_significant_one (bf_mask_cons a k bf_nil) = a.
Proof.
  intros.
  apply Z_least_significant_one_sound => //.
  rewrite bf_mask_cons_singleton.
  split; intros; bitblast.
Qed.

Lemma bf_slice_shl a k x :
  0 ≤ a → 0 < k →
  0 ≤ x < 2^k →
  bf_slice a k (x ≪ a) = x.
Proof.
  rewrite /bf_slice => ???.
  bitblast.
Qed.

(* opaque *)
Global Opaque bf_nil bf_cons bf_mask_cons bf_slice bf_update.
