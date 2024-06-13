From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.evenint.generated Require Import generated_code_evenint generated_specs_evenint generated_template_EvenInt_new_2.

Set Default Proof Using "Type".

Section proof.
Context `{!refinedrustGS Σ}.

Lemma EvenInt_new_2_proof (π : thread_id) :
  EvenInt_new_2_lemma π.
Proof.
  EvenInt_new_2_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { unsafe_unfold_common_caesium_defs; simpl. lia. }
  { apply Zeven_ex_iff.
    setoid_rewrite <-Z.mul_comm.
    apply Z.rem_divide; done. }
  { unsafe_unfold_common_caesium_defs; simpl. lia. }
  { revert select (i `rem` 2 ≠ 0).
    rewrite Z.rem_mod_eq_0; last done.
    rewrite Zmod_odd. intros Hne.
    apply Zeven_Sn, Zodd_bool_iff.
    destruct Z.odd; done. }
  { revert select (i `rem` 2 ≠ 0).
    rewrite Z.rem_mod_eq_0; last done.
    rewrite Zmod_odd. intros Hne.
    apply Zeven_pred, Zodd_bool_iff.
    destruct Z.odd; done. }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
