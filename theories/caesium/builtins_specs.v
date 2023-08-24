From stdpp.unstable Require Import bitblast.
From caesium Require Import base int_type.

(* least significant 1-bit *)

Definition is_least_significant_one (k n : Z) : Prop :=
  Z.testbit n k = true ∧ ∀ i, 0 ≤ i < k → Z.testbit n i = false.

Definition Z_least_significant_one (n : Z) : Z :=
  if bool_decide (n = 0) then -1 else Z.log2 (Z.land n (-n)).

Lemma Z_least_significant_one_sound k n :
  0 ≤ k →
  is_least_significant_one k n →
  Z_least_significant_one n = k.
Proof.
  rewrite /is_least_significant_one /Z_least_significant_one => ? [Heq Hlt].
  case_bool_decide. { subst. by bitblast Heq. }
  suff : Z.land n (- n) = 1 ≪ k.
  { move => ->. rewrite Z.shiftl_1_l Z.log2_pow2; lia. }
  bitblast as n'.
  - have ? : n' = k by lia. subst. rewrite Z_bits_opp_z ?Heq //. bitblast. apply Hlt; lia.
  - destruct (decide (n' < k)); [by rewrite Hlt|].
    rewrite Z_bits_opp_nz ?andb_negb_r // => Hn. bitblast Hn with k as Hn'. congruence.
Qed.

Lemma Z_least_significant_one_lower_bound_pos n :
   0 < n →
   0 ≤ Z_least_significant_one n.
Proof.
  rewrite /Z_least_significant_one => ?.
  case_bool_decide; [lia|].
  apply Z.log2_nonneg.
Qed.

Lemma Z_least_significant_one_lower_bound n :
  -1 ≤ Z_least_significant_one n.
Proof.
  rewrite /Z_least_significant_one.
  case_bool_decide; [done|].
  trans 0; [done|]. apply Z.log2_nonneg.
Qed.

Lemma Z_land_neg_pos n :
  0 < n →
  0 < Z.land n (- n).
Proof.
  move => Hn.
  suff : Z.land n (- n) ≠ 0. { move => ?. have := Z.land_nonneg n (-n). naive_solver lia. }
  destruct n as [|p|p]; [lia| |lia]. clear Hn.
  elim: p.
  - move => p ?.
    have ->: (- Z.pos p~1 = Z.lnot (Z.pos p~1) + 1) by rewrite -Z.opp_lnot; lia.
    rewrite Z.add_nocarry_lor. 2: bitblast.
    move => Hx. by bitblast Hx with 0.
  - move => p Hp.
    have -> : - Z.pos p~0 = (- Z.pos p) ≪ 1 by [].
    contradict Hp. bitblast as i. by bitblast Hp with (i + 1).
  - done.
Qed.

Lemma Z_least_significant_one_xH :
  Z_least_significant_one (Z.pos 1) = 0.
Proof. done. Qed.

Lemma Z_least_significant_one_xO p :
  Z_least_significant_one (Z.pos (p~0)) = Z_least_significant_one (Z.pos p) + 1.
Proof.
  rewrite /Z_least_significant_one. do 2 (case_bool_decide; [lia|]).
  rewrite -Z.log2_shiftl; [..|lia].
  2: { apply Z_land_neg_pos. lia. }
  f_equal. have -> : - Z.pos p~0 = (- Z.pos p) ≪ 1 by [].
  bitblast.
Qed.

Lemma Z_least_significant_one_xI p :
  Z_least_significant_one (Z.pos (p~1)) = 0.
Proof.
  rewrite /Z_least_significant_one. case_bool_decide; [lia|].
  have ->: (- Z.pos p~1 = Z.lnot (Z.pos p~1) + 1) by rewrite -Z.opp_lnot; lia.
  apply (Z.log2_unique' _ _ 0); [lia..|]. rewrite Z.add_0_r.
  rewrite Z.add_nocarry_lor.
  - bitblast.
  - bitblast.
Qed.

Lemma Z_least_significant_one_is_least_significant_one n :
  0 < n →
  is_least_significant_one (Z_least_significant_one n) n.
Proof.
  destruct n as [|p|p]; [lia| |lia] => _.
  elim: p.
  - move => p IH. rewrite Z_least_significant_one_xI.
    split; [done|lia].
  - move => p [IH1 IH2]. rewrite Z_least_significant_one_xO.
    split.
    + bitblast. have := Z_least_significant_one_lower_bound_pos (Z.pos p). lia.
    + move => i ?. bitblast. apply IH2. lia.
  - rewrite Z_least_significant_one_xH. split; [done|lia].
Qed.

Lemma Z_least_significant_one_upper_bound n m :
  0 ≤ n < 2 ^ m →
  Z_least_significant_one n < m.
Proof.
  move => [Hn Hnm].
  have ? : 0 ≤ m. { have := Z.pow_neg_r 2 m. lia. }
  destruct (decide (n = 0)).
  { subst. rewrite /Z_least_significant_one => //=. lia. }
  set (x := Z_least_significant_one n).
  assert (Hx : is_least_significant_one x n).
  { unfold x. apply Z_least_significant_one_is_least_significant_one; lia. }
  destruct (decide (m ≤ x)) as [Hxm|]; [|lia].
  apply (Z.pow_le_mono_r 2) in Hxm; try lia.
  apply (Z.lt_le_trans _ _ _ Hnm) in Hxm.
  destruct Hx as [Htestbit _].
  rewrite Z.testbit_true in Htestbit; last by apply Z_least_significant_one_lower_bound_pos; lia.
  rewrite Z.div_small in Htestbit; [done| lia].
Qed.
