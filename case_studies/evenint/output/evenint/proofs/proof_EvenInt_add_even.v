From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.evenint.generated Require Import generated_code_evenint generated_specs_evenint generated_template_EvenInt_add_even.

Set Default Proof Using "Type".

Section proof.
Context `{!refinedrustGS Σ}.

Lemma EvenInt_add_even_proof (π : thread_id) :
  EvenInt_add_even_lemma π.
Proof.
  EvenInt_add_even_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { by apply Zeven_plus_Zeven. }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
