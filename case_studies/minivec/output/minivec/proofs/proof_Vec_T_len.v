From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.minivec.generated Require Import generated_code_minivec generated_specs_minivec.
From refinedrust.examples.minivec.generated Require Import generated_template_Vec_T_len.

Set Default Proof Using "Type".

Section proof.
Context `{!typeGS Σ}.
Lemma Vec_T_len_proof (π : thread_id) :
  Vec_T_len_lemma π.
Proof.
  Vec_T_len_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  rewrite Hlen_eq project_vec_els_length. lia. 
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
