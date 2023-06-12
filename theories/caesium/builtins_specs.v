From lithium Require Import Z_bitblast.
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

Lemma Z_least_significant_one_lower_bound n :
  -1 ≤ Z_least_significant_one n.
Proof.
  rewrite /Z_least_significant_one.
  case_bool_decide; [done|].
  trans 0; [done|].
  apply Z.log2_nonneg.
Qed.
