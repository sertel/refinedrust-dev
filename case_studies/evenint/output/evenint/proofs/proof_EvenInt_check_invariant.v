From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.evenint.generated Require Import generated_code_evenint generated_specs_evenint generated_template_EvenInt_check_invariant.

Set Default Proof Using "Type".

Section proof.
Context `{!refinedrustGS Σ}.

Lemma EvenInt_check_invariant_proof (π : thread_id) :
  EvenInt_check_invariant_lemma π.
Proof.
  EvenInt_check_invariant_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { unsafe_unfold_common_caesium_defs. simpl. lia. }
  { revert select (Zeven z). revert select (z `rem` 2 ≠ 0).
    rewrite Zeven_ex_iff Z.rem_divide; last done.
    setoid_rewrite Z.mul_comm; done. }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
