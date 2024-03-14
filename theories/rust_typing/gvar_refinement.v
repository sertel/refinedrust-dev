From iris.bi Require Export fractional.
From refinedrust Require Export base.
From refinedrust Require Export ghost_var_dfrac.

(** * Borrow variables *)

Section sigma.
  Record RT : Type := RT_into {
    RT_rt : Type;
    RT_r : RT_rt;
    }.
  Global Arguments RT_into {_}.

  Import EqNotations.
  Lemma RT_rt_eq (x y : RT) :
    x = y → RT_rt x = RT_rt y.
  Proof.
    inversion 1. done.
  Qed.
  Lemma RT_r_eq (x y : RT) (Heq : x = y) :
    rew Heq in RT_r x = RT_r y.
  Proof.
    inversion Heq. subst. done.
  Qed.

  Lemma RT_into_inj T (x y : T) :
    RT_into x = RT_into y → x = y.
  Proof.
    revert x y.
    enough (∀ a b : RT, a = b → ∀ Heq' : RT_rt a = RT_rt b, rew [id] Heq' in RT_r a = RT_r b) as H.
    { intros x y Heq. by specialize (H _ _ Heq eq_refl). }
    intros a b Heq. destruct Heq. intros Heq.
    specialize (UIP_t _ _ _ Heq eq_refl) as ->. done.
  Qed.

End sigma.

Section ghost_variables.
  Context `{!ghost_varG Σ RT} {T : Type}.
  Implicit Types (γ : gname) (t : T).

  Definition gvar_auth γ t := ghost_var γ (DfracOwn (1/2)) (RT_into t).
  Definition gvar_obs γ t := ghost_var γ (DfracOwn (1/2)) (RT_into t).
  Definition gvar_pobs γ t := ghost_var γ DfracDiscarded (RT_into t).

  Global Instance gvar_pobs_persistent γ t : Persistent (gvar_pobs γ t).
  Proof. apply _. Qed.

  Lemma gvar_alloc t :
    ⊢ |==> ∃ γ, gvar_auth γ t ∗ gvar_obs γ t.
  Proof.
    iMod (ghost_var_alloc (RT_into t)) as "(%γ & (? & ?))".
    iModIntro. iExists γ. iFrame.
  Qed.

  Lemma gvar_update {γ t1 t2} t :
    gvar_auth γ t1 -∗ gvar_obs γ t2 ==∗ gvar_auth γ t ∗ gvar_obs γ t.
  Proof. iApply ghost_var_update_halves. Qed.

  Lemma gvar_obs_persist γ t :
    gvar_obs γ t ==∗ gvar_pobs γ t.
  Proof. iApply ghost_var_discard. Qed.

  Lemma gvar_auth_persist γ t :
    gvar_auth γ t ==∗ gvar_pobs γ t.
  Proof. iApply ghost_var_discard. Qed.

  Lemma gvar_agree γ t1 t2:
    gvar_auth γ t1 -∗ gvar_obs γ t2 -∗ ⌜t1 = t2⌝.
  Proof.
    iIntros "H1 H2".
    iPoseProof (ghost_var_agree with "H1 H2") as "%Heq".
    apply RT_into_inj  in Heq. done.
  Qed.

  Lemma gvar_pobs_agree γ t1 t2:
    gvar_auth γ t1 -∗ gvar_pobs γ t2 -∗ ⌜t1 = t2⌝.
  Proof.
    iIntros "H1 H2".
    iPoseProof (ghost_var_agree with "H1 H2") as "%Heq".
    apply RT_into_inj  in Heq. done.
  Qed.
  Lemma gvar_pobs_agree_2 γ t1 t2:
    gvar_pobs γ t1 -∗ gvar_pobs γ t2 -∗ ⌜t1 = t2⌝.
  Proof.
    iIntros "H1 H2".
    iPoseProof (ghost_var_agree with "H1 H2") as "%Heq".
    apply RT_into_inj  in Heq. done.
  Qed.

  Definition Rel2 (γ1 γ2 : gname) (R : T → T → Prop) : iProp Σ :=
    ∃ v1 v2, gvar_pobs γ1 v1 ∗ gvar_obs γ2 v2 ∗ ⌜R v1 v2⌝.

  Lemma Rel2_use_pobs γ1 γ2 R v1 :
    gvar_pobs γ1 v1 -∗ Rel2 γ1 γ2 R -∗ ∃ v2, gvar_obs γ2 v2 ∗ ⌜R v1 v2⌝.
  Proof.
    iIntros "Hobs1 (%v1' & %v2 & Hauth1 & Hobs2 & %HR)".
    iPoseProof (gvar_pobs_agree_2 with "Hauth1 Hobs1") as "->".
    eauto with iFrame.
  Qed.

  Lemma Rel2_use_obs γ1 γ2 R v1 :
    gvar_obs γ1 v1 -∗ Rel2 γ1 γ2 R -∗ ∃ v2, gvar_obs γ2 v2 ∗ gvar_obs γ1 v1 ∗ gvar_pobs γ1 v1 ∗ ⌜R v1 v2⌝.
  Proof.
    iIntros "Hobs1 (%v1' & %v2 & Hauth1 & Hobs2 & %HR)".
    iDestruct (gvar_pobs_agree with "Hobs1 Hauth1") as %<-.
    eauto with iFrame.
  Qed.

  Lemma Rel2_use_trivial γ1 γ2 R :
    Rel2 γ1 γ2 R -∗ ∃ v2, gvar_obs γ2 v2.
  Proof.
    iIntros "(%v1' & %v2 & Hauth1 & Hobs2 & %HR)".
    eauto with iFrame.
  Qed.

  Global Instance Rel2_timeless γ1 γ2 R : Timeless (Rel2 γ1 γ2 R).
  Proof. apply _. Qed.
End ghost_variables.

Lemma gvar_update_strong `{!ghost_varG Σ RT} {T1 T2 : Type} {γ} {t1 t2 : T1} (t : T2) :
  gvar_auth γ t1 -∗ gvar_obs γ t2 ==∗ gvar_auth γ t ∗ gvar_obs γ t.
Proof. iApply ghost_var_update_halves. Qed.
