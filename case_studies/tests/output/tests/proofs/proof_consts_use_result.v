From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.tests.generated Require Import generated_code_tests generated_specs_tests generated_template_consts_use_result.

Set Default Proof Using "Type".

Section proof.
Context `{!refinedrustGS Σ}.

Lemma consts_use_result_proof (π : thread_id) :
  consts_use_result_lemma π.
Proof.
  consts_use_result_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  all: unsafe_unfold_common_caesium_defs; simpl; lia.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
