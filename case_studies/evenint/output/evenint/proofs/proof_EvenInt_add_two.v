From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.evenint.generated Require Import generated_code_evenint generated_specs_evenint generated_template_EvenInt_add_two.

Set Default Proof Using "Type".

Section proof.
Context `{!refinedrustGS Σ}.

Lemma EvenInt_add_two_proof (π : thread_id) :
  EvenInt_add_two_lemma π.
Proof.
  EvenInt_add_two_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { rewrite -Z.add_assoc. apply Zeven_plus_Zeven; done. }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
