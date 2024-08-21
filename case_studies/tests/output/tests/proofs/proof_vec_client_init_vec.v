From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.tests.generated Require Import generated_code_tests generated_specs_tests.
From refinedrust.examples.tests.generated Require Import generated_template_vec_client_init_vec.

Set Default Proof Using "Type".

Section proof.
Context `{!refinedrustGS Σ}.
Lemma vec_client_init_vec_proof (π : thread_id) :
  vec_client_init_vec_lemma π.
Proof.
  vec_client_init_vec_prelude.

  repeat liRStep; liShow.
  
  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
