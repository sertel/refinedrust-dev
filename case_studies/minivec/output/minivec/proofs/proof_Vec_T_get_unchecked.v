From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.minivec.generated Require Import generated_code_minivec generated_specs_minivec.
From refinedrust.examples.minivec.generated Require Import generated_template_Vec_T_get_unchecked.

Set Default Proof Using "Type".

Section proof.
Context `{!typeGS Σ}.
Lemma Vec_T_get_unchecked_proof (π : thread_id) :
  Vec_T_get_unchecked_lemma π.
Proof.
  Vec_T_get_unchecked_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { move: _Hsz Hi Hcap. 
    rewrite ly_size_mk_array_layout.
    clear. nia. } 
  { move: Hi Hcap. clear. nia. }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
