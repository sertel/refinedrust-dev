From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.tests.generated Require Import generated_code_tests generated_specs_tests generated_template_traits_foo_foobar_ref3.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma traits_foo_foobar_ref3_proof (π : thread_id) :
  traits_foo_foobar_ref3_lemma π.
Proof.
  traits_foo_foobar_ref3_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  (* TODO: look at these *)
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
