From iris.proofmode Require Import tactics.
From iris.base_logic Require Import ghost_map.
From iris.bi.lib Require Export fractional.
From iris.algebra Require Import frac.
From iris Require Import prelude options.
Set Default Proof Using "Type".

(** * Ghost state for turning fractional permissions into counting permissions, used by our lifetime contexts *)


Class fraction_mapG Σ := {
  fraction_map_ghost_inG :: ghost_mapG Σ nat frac;
}.
#[export] Hint Mode fraction_mapG - : typeclass_instances.
Definition fraction_mapΣ := #[ghost_mapΣ nat frac].
Global Instance subG_fraction_mapΣ Σ :
  subG (fraction_mapΣ) Σ → fraction_mapG Σ.
Proof. solve_inG. Qed.

Local Definition sum_frac_cod (M : list (nat * Qp)) : option frac :=
  foldr (λ (p : nat * Qp) (acc : option Qp) ,
    let '(_, q) := p in
    match acc with | Some acc_q => Some (acc_q + q)%Qp | _ => Some q end) None M.

Local Definition remaining_frac (M : list (nat * frac)) : option Qp :=
  match sum_frac_cod M with
  | None => Some 1%Qp
  | Some q => (1-q)%Qp
  end.

Section defs.
  Context `{fraction_mapG Σ}.

  Definition fraction_map_auth_def (γ : gname) (Φ : Qp → iProp Σ) (q : frac) (n : nat) : iProp Σ :=
    ∃ (M : gmap nat frac) (next_fresh : nat),
      ghost_map_auth γ q M ∗ ⌜size (dom M) = n⌝ ∗
      (* track the next fresh id ready for use *)
      ⌜∀ i q, M !! i = Some q → i < next_fresh⌝ ∗
      (* have the remaining fraction here *)
      ∃ qr, ⌜remaining_frac (map_to_list M) = Some qr⌝ ∗ Φ (q * qr)%Qp.
  Definition fraction_map_auth_aux : seal (@fraction_map_auth_def). Proof. by eexists. Qed.
  Definition fraction_map_auth := fraction_map_auth_aux.(unseal).
  Definition fraction_map_auth_eq : @fraction_map_auth = @fraction_map_auth_def := fraction_map_auth_aux.(seal_eq).

  Definition fraction_map_elem_def (γ : gname) (Φ : Qp → iProp Σ) : iProp Σ :=
    ∃ q, Φ q ∗ ∃ k, ghost_map_elem γ k (DfracOwn 1) q.
  Definition fraction_map_elem_aux : seal (@fraction_map_elem_def). Proof. by eexists. Qed.
  Definition fraction_map_elem := fraction_map_elem_aux.(unseal).
  Definition fraction_map_elem_eq : @fraction_map_elem = @fraction_map_elem_def := fraction_map_elem_aux.(seal_eq).
End defs.

Section laws.
  Context `{fraction_mapG Σ} (Φ : Qp → iProp Σ) `{Hfrac: !Fractional Φ}.

  Instance sum_frac_cod_permutation_invariant :
    Proper ((≡ₚ) ==> eq) sum_frac_cod.
  Proof.
    intros M1 M2.
    induction 1 as [ | [] ??? IH| [] [] ?| ???? IH1 ? IH2]; simpl.
    - done.
    - rewrite IH. destruct (sum_frac_cod _); done.
    - destruct (sum_frac_cod _); f_equiv.
      + rewrite -!assoc. rewrite [(q+_)%Qp]comm. done.
      + rewrite [(q+_)%Qp]comm. done.
    - rewrite IH1 IH2. done.
  Qed.

  Local Lemma sum_frac_cod_cons n q a :
    sum_frac_cod ((n, q) :: a) =
      match sum_frac_cod a with
      | Some qacc => Some (qacc + q)%Qp
      | None => Some q
      end.
  Proof. done. Qed.

  Instance remaining_frac_permutation_invariant :
    Proper ((≡ₚ) ==> eq) remaining_frac.
  Proof.
    intros M1 M2 Hperm. rewrite /remaining_frac.
    rewrite (sum_frac_cod_permutation_invariant _ M2); done.
  Qed.

  Local Lemma remaining_frac_nil :
    remaining_frac [] = Some 1%Qp.
  Proof. done. Qed.

  Lemma fraction_map_elem_acc γ :
    fraction_map_elem γ Φ -∗ ∃ q, Φ q ∗ (Φ q -∗ fraction_map_elem γ Φ).
  Proof.
    rewrite fraction_map_elem_eq.
    iIntros "(%q & Hf & Ha)". iExists q. iFrame.
    iIntros "Hf". iExists q. iFrame.
  Qed.

  Lemma fraction_map_auth_alloc :
    Φ 1 -∗ |==> ∃ γ, fraction_map_auth γ Φ 1 0.
  Proof.
    iIntros "Hfull".
    iMod (ghost_map_alloc_empty) as "(%γ & Hauth)".
    iModIntro. iExists γ. rewrite fraction_map_auth_eq.
    iExists ∅, 0. iFrame.
    rewrite dom_empty_L size_empty. iSplitR; first done.
    iSplitR. { iPureIntro. intros ?? []%lookup_empty_Some. }
    iExists 1%Qp. rewrite Qp.mul_1_l. iFrame.
    done.
  Qed.

  Global Instance fraction_map_auth_fractional γ n :
    Fractional (λ q, fraction_map_auth γ Φ q n).
  Proof using Type*.
    iIntros (q1 q2). rewrite fraction_map_auth_eq. iSplit.
    - iIntros "(%M & %nf & [Ha1 Ha2] & % & % & %qr & % & Hf)".
      rewrite Qp.mul_add_distr_r. rewrite fractional. iDestruct "Hf" as "(Hf1 & Hf2)".
      iSplitL "Ha1 Hf1"; iExists M, nf; eauto 8 with iFrame.
    - iIntros "((%M1 & %nf1 & Ha1 & % & %Hf1 & %qr1 & %Hrem1 & Hf1) & (%M2 & %nf2 & Ha2 & % & %Hf2 & %qr2 & %Hrem2 & Hf2))".
      iDestruct (ghost_map_auth_agree with "Ha1 Ha2") as %<-.
      iExists M1, (min nf1 nf2). rewrite ghost_map_auth_fractional. iFrame.
      iSplitR; first done. iSplitR.
      { iPureIntro. intros ?? Hlook. specialize (Hf1 _ _ Hlook). specialize (Hf2 _ _ Hlook). lia. }
      rewrite Hrem2 in Hrem1. injection Hrem1 as ->. iExists qr1.
      rewrite Qp.mul_add_distr_r fractional. eauto with iFrame.
  Qed.

  (** get the remaining fraction *)
  Lemma fraction_map_auth_access' γ q n :
    fraction_map_auth γ Φ q n -∗
    ∃ q' q'', Φ q' ∗ fraction_map_auth γ Φ q'' n ∗
      (Φ q' -∗ fraction_map_auth γ Φ q'' n -∗ fraction_map_auth γ Φ q n).
  Proof using Type*.
    rewrite fraction_map_auth_eq.
    iIntros "(%M & %next_fresh & Hauth & %Hsz & %Hfresh & %qr & %Hrem & Hprop)".
    iExists ((q/2) * qr)%Qp, (q/2)%Qp.
    rewrite -{1 2}(Qp.div_2 (q)) Qp.mul_add_distr_r.
    rewrite ghost_map_auth_fractional. iDestruct "Hauth" as "(Hauth' & Hauth)".
    rewrite Hfrac. iDestruct "Hprop" as "($ & Hprop)".
    iSplitL "Hauth' Hprop".
    { iExists _, _. iFrame. iSplitR; first done. iSplitR; first done.
      iExists qr. iSplitR; done.
    }
    iIntros "Hprop Hauth'".
    iDestruct "Hauth'" as "(%M' & %next_fresh' & Hauth' & _ & _ & %qr' & % & Hfrac)".
    iExists M, next_fresh. iDestruct (ghost_map_auth_agree with "Hauth Hauth'") as %<-.
    iCombine "Hauth Hauth'" as "$".
    iSplitR; first done. iSplitR; first done. iExists qr. iSplitR; first done.
    assert (qr = qr') as <- by congruence.
    iCombine "Hprop Hfrac" as "Hprop". by rewrite -Hfrac -Qp.mul_add_distr_r Qp.div_2.
  Qed.
  Lemma fraction_map_auth_access γ q n :
    fraction_map_auth γ Φ q n -∗
    ∃ q', Φ q' ∗ fraction_map_auth γ Φ q' n ∗
      (Φ q' -∗ fraction_map_auth γ Φ q' n -∗ fraction_map_auth γ Φ q n).
  Proof using Type*.
    iIntros "Hauth".
    iPoseProof (fraction_map_auth_access' with "Hauth") as "(%q' & %q'' & Hprop & Hauth & Hcl)".
    destruct (Qp.lower_bound q' q'') as (q0 & q1 & q2 & -> & ->).
    rewrite Hfrac fraction_map_auth_fractional. iExists q0.
    iDestruct "Hprop" as "($ & Hprop)". iDestruct "Hauth" as "($ & Hauth)".
    iIntros "Hprop' Hauth'". iApply ("Hcl" with "[$] [$]").
  Qed.

  (** obtain a new fraction *)
  Lemma fraction_map_auth_increase γ n :
    fraction_map_auth γ Φ 1 n ==∗
    fraction_map_auth γ Φ 1 (S n) ∗ fraction_map_elem γ Φ.
  Proof using Type*.
    rewrite fraction_map_auth_eq fraction_map_elem_eq.
    iIntros "(%M & %next_fresh & Hauth & %Hsz & %Hfresh & %q' & %Hrem & Hprop)".
    rewrite Qp.mul_1_l.
    rewrite -{1}(Qp.div_2 q') fractional. iDestruct "Hprop" as "[Hprop1 Hprop]".
    assert (M !! next_fresh = None) as Hfresh'.
    { destruct (M !! next_fresh) eqn:Heq; last done.
      apply Hfresh in Heq. lia.
    }
    iMod (ghost_map_insert next_fresh (q'/2)%Qp with "Hauth") as "(Hauth & He)"; first done.
    iSplitR "He Hprop1"; first last. { iExists (q'/2)%Qp. eauto with iFrame. }
    iModIntro. iExists _, (S next_fresh). iFrame "Hauth".
    iSplitR. {
      rewrite dom_insert_L size_union.
      2: { apply disjoint_singleton_l. intros (? & ?%Hfresh)%elem_of_dom. lia. }
      by rewrite size_singleton Hsz.
    }
    iSplitR. { iPureIntro. intros i q. rewrite lookup_insert_Some. intros [(<- & <-) | (Hneq & ?%Hfresh)]; lia. }
    iExists (q'/2)%Qp. rewrite Qp.mul_1_l. iFrame. iPureIntro.
    rewrite map_to_list_insert; last done.
    unfold remaining_frac in Hrem. unfold remaining_frac. rewrite sum_frac_cod_cons.
    destruct (sum_frac_cod _).
    - apply Qp.sub_Some in Hrem. rewrite Hrem.
      rewrite -{1}(Qp.div_2 q') Qp.add_assoc Qp.add_comm Qp.add_sub. done.
    - injection Hrem as <-.
      rewrite -{1}Qp.half_half Qp.add_sub. done.
  Qed.

  (** access a full fraction when the count is 0 *)
  Lemma fraction_map_auth_acc_0 γ :
    fraction_map_auth γ Φ 1 0 -∗ Φ 1 ∗ (Φ 1 -∗ fraction_map_auth γ Φ 1 0).
  Proof.
    rewrite fraction_map_auth_eq.
    iIntros "(%M & %nf & Hauth & %Hsz & %Hfresh & %q' & %Hrem & Hprop)".
    rewrite Qp.mul_1_l. apply size_empty_inv in Hsz. apply dom_empty_inv in Hsz. subst M.
    rewrite map_to_list_empty remaining_frac_nil in Hrem.
    injection Hrem as <-. iFrame. iIntros "Hprop".
    iExists ∅, 0. iFrame.
    iSplitR. { by rewrite dom_empty_L size_empty. }
    iSplitR. { iPureIntro. intros ? ? []%lookup_empty_Some. }
    iExists 1%Qp. rewrite Qp.mul_1_l. iFrame.
    rewrite map_to_list_empty remaining_frac_nil. done.
  Qed.

  Lemma fraction_map_auth_decrease γ n :
    fraction_map_auth γ Φ 1 n -∗
    fraction_map_elem γ Φ ==∗
    fraction_map_auth γ Φ 1 (n - 1).
  Proof using Type*.
    rewrite fraction_map_auth_eq fraction_map_elem_eq.
    iIntros "(%M & %nf & Hauth & %Hsz & %Hfresh & %q' & %Hrem & Hprop) (%q & Hprop' & %k & Helem)".
    iPoseProof (ghost_map_lookup with "Hauth Helem") as "%Hlook".
    iMod (ghost_map_delete with "Hauth Helem") as "Hauth".
    iModIntro. iExists (delete k M), nf. iFrame.
    iSplitR. { iPureIntro.
      rewrite dom_delete_L size_difference.
      2: { apply singleton_subseteq_l. apply elem_of_dom. eauto. }
      rewrite Hsz size_singleton. done.
    }
    iSplitR. { iPureIntro. intros ?? [_ ?%Hfresh]%lookup_delete_Some. done. }
    iExists (q' + q)%Qp. rewrite !Qp.mul_1_l. rewrite fractional. iFrame.
    iPureIntro.
    rewrite -map_to_list_delete in Hrem; last apply Hlook.
    unfold remaining_frac in Hrem. rewrite sum_frac_cod_cons in Hrem.
    unfold remaining_frac. destruct (sum_frac_cod _).
    - apply Qp.sub_Some in Hrem. rewrite Hrem.
      rewrite Qp.add_comm [(_ + q)%Qp]Qp.add_comm Qp.add_assoc Qp.add_sub. done.
    - apply Qp.sub_Some in Hrem. rewrite Hrem. rewrite Qp.add_comm. done.
  Qed.
End laws.
