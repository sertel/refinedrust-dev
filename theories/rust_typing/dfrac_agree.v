From iris.algebra Require Export dfrac agree updates local_updates.
From iris.algebra Require Import proofmode_classes.
From iris.prelude Require Import options.

Definition dfrac_agreeR (A : ofe) : cmra := prodR dfracR (agreeR A).

Definition to_dfrac_agree {A : ofe} (dq : dfrac) (a : A) : dfrac_agreeR A :=
  (dq, to_agree a).

Section lemmas.
  Context {A : ofe}.
  Implicit Types (dq : dfrac) (q : Qp) (a : A).

  Global Instance to_dfrac_agree_ne dq : NonExpansive (@to_dfrac_agree A dq).
  Proof. solve_proper. Qed.
  Global Instance to_dfrac_agree_proper dq : Proper ((≡) ==> (≡)) (@to_dfrac_agree A dq).
  Proof. solve_proper. Qed.

  Global Instance to_dfrac_agree_exclusive a : Exclusive (to_dfrac_agree (DfracOwn 1) a).
  Proof. apply _. Qed.
  Global Instance to_dfrac_discrete a : Discrete a → Discrete (to_dfrac_agree (DfracOwn 1) a).
  Proof. apply _. Qed.
  Global Instance to_frac_injN n : Inj2 (dist n) (dist n) (dist n) (@to_dfrac_agree A).
  Proof. by intros dq1 a1 dq2 a2 [??%(inj to_agree)]. Qed.
  Global Instance to_dfrac_inj : Inj2 (≡) (≡) (≡) (@to_dfrac_agree A).
  Proof. by intros dq1 a1 dq2 a2 [??%(inj to_agree)]. Qed.

  Lemma dfrac_agree_own_op q1 q2 a :
    to_dfrac_agree (DfracOwn (q1 + q2)) a ≡ to_dfrac_agree (DfracOwn q1) a ⋅ to_dfrac_agree (DfracOwn q2) a.
  Proof. rewrite /to_dfrac_agree -pair_op agree_idemp //. Qed.

  Lemma dfrac_agree_own_op_valid q1 a1 q2 a2 :
    ✓ (to_dfrac_agree (DfracOwn q1) a1 ⋅ to_dfrac_agree (DfracOwn q2) a2) →
    (q1 + q2 ≤ 1)%Qp ∧ a1 ≡ a2.
  Proof.
    intros [Hq Ha]%pair_valid. simpl in *. split; first done.
    apply to_agree_op_inv. done.
  Qed.
  Lemma dfrac_agree_own_op_valid_L `{!LeibnizEquiv A} q1 a1 q2 a2 :
    ✓ (to_dfrac_agree (DfracOwn q1) a1 ⋅ to_dfrac_agree (DfracOwn q2) a2) →
    (q1 + q2 ≤ 1)%Qp ∧ a1 = a2.
  Proof. unfold_leibniz. apply dfrac_agree_own_op_valid. Qed.
  Lemma dfrac_agree_own_op_validN q1 a1 q2 a2 n :
    ✓{n} (to_dfrac_agree (DfracOwn q1) a1 ⋅ to_dfrac_agree (DfracOwn q2) a2) →
    (q1 + q2 ≤ 1)%Qp ∧ a1 ≡{n}≡ a2.
  Proof.
    intros [Hq Ha]%pair_validN. simpl in *. split; first done.
    apply to_agree_op_invN. done.
  Qed.
  Lemma dfrac_agree_own_op_valid1 q1 a1 dq2 a2 : 
    ✓ (to_dfrac_agree (DfracOwn q1) a1 ⋅ to_dfrac_agree dq2 a2) →
    (q1 < 1)%Qp ∧ a1 ≡ a2.
  Proof.
    intros [Hq Ha]%pair_valid. simpl in *. 
    specialize (to_agree_op_inv _ _ Ha) as Heq. split; last done.
    by eapply dfrac_valid_own_l.
  Qed.
  Lemma dfrac_agree_own_op_valid1_L `{!LeibnizEquiv A} q1 a1 dq2 a2 : 
    ✓ (to_dfrac_agree (DfracOwn q1) a1 ⋅ to_dfrac_agree dq2 a2) →
    (q1 < 1)%Qp ∧ a1 = a2.
  Proof. unfold_leibniz. apply dfrac_agree_own_op_valid1. Qed.
  Lemma dfrac_agree_op_valid dq1 a1 dq2 a2 : 
    ✓ (to_dfrac_agree dq1 a1 ⋅ to_dfrac_agree dq2 a2) → a1 ≡ a2.
  Proof.
    intros [Hq Ha]%pair_valid. simpl in *. 
    specialize (to_agree_op_inv _ _ Ha) as Heq. done.
  Qed.
  Lemma dfrac_agree_op_valid_L `{!LeibnizEquiv A} dq1 a1 dq2 a2 : 
    ✓ (to_dfrac_agree dq1 a1 ⋅ to_dfrac_agree dq2 a2) → a1 = a2.
  Proof. unfold_leibniz. apply dfrac_agree_op_valid. Qed.

  Lemma dfrac_agree_own_included q1 a1 q2 a2 :
    to_dfrac_agree (DfracOwn q1) a1 ≼ to_dfrac_agree (DfracOwn q2) a2 ↔
    (q1 < q2)%Qp ∧ a1 ≡ a2.
  Proof. by rewrite pair_included dfrac_own_included to_agree_included. Qed.
  Lemma dfrac_agree_own_included_L `{!LeibnizEquiv A} q1 a1 q2 a2 :
    to_dfrac_agree (DfracOwn q1) a1 ≼ to_dfrac_agree (DfracOwn q2) a2 ↔
    (q1 < q2)%Qp ∧ a1 = a2.
  Proof. unfold_leibniz. apply dfrac_agree_own_included. Qed.
  Lemma dfrac_agree_own_includedN q1 a1 q2 a2 n :
    to_dfrac_agree (DfracOwn q1) a1 ≼{n} to_dfrac_agree (DfracOwn q2) a2 ↔
    (q1 < q2)%Qp ∧ a1 ≡{n}≡ a2.
  Proof.
    by rewrite pair_includedN -cmra_discrete_included_iff
               dfrac_own_included to_agree_includedN.
  Qed.
  Lemma dfrac_agree_discarded_included a1 a2 : 
    to_dfrac_agree DfracDiscarded a1 ≼ to_dfrac_agree DfracDiscarded a2 ↔ a1 ≡ a2.
  Proof. 
    rewrite pair_included to_agree_included; split; 
      naive_solver eauto using dfrac_discarded_included. 
  Qed.

  (** No frame-preserving update lemma needed -- use [cmra_update_exclusive] with
  the above [Exclusive] instance. *)
  Lemma dfrac_agree_discard_update dq a : 
    to_dfrac_agree dq a ~~> to_dfrac_agree DfracDiscarded a.
  Proof. 
    apply prod_update; last done.
    apply dfrac_discard_update. 
  Qed.
End lemmas.

Global Typeclasses Opaque to_dfrac_agree.
