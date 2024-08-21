From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.minivec.generated Require Import generated_code_minivec generated_specs_minivec.
From refinedrust.examples.minivec.generated Require Import generated_template_client_get_mut_client.

Set Default Proof Using "Type".

Section proof.
Context `{!refinedrustGS Σ}.
Lemma client_get_mut_client_proof (π : thread_id) :
  client_get_mut_client_lemma π.
Proof.
  client_get_mut_client_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: unsafe_unfold_common_caesium_defs; solve_goal.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
