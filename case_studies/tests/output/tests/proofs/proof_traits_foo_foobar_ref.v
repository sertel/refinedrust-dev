From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.tests.generated Require Import generated_code_tests generated_specs_tests generated_template_traits_foo_foobar_ref.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma traits_foo_foobar_ref_proof (π : thread_id) :
  traits_foo_foobar_ref_lemma π.
Proof.
  traits_foo_foobar_ref_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
