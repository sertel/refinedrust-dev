From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.minivec.generated Require Import generated_code_minivec generated_specs_minivec.
From refinedrust.examples.minivec.generated Require Import generated_template_RawVec_T_grow.

Set Default Proof Using "Type".

Section proof.
Context `{!typeGS Σ}.
Lemma RawVec_T_grow_proof (π : thread_id) :
  RawVec_T_grow_lemma π.
Proof.
  RawVec_T_grow_prelude.

  rep <-! liRStep; liShow.
  (* Manual step to extract the array value before the call to realloc *)
  apply_update (updateable_extract_value l).
  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { 
    move: Hsz Hnot_sz.
    match goal with H : MaxInt isize_t < MaxInt usize_t |- _ => move: H end.
    rewrite /size_of_array_in_bytes; simplify_layout_goal.
    clear. solve_goal with nia.
  }
  
  all: solve_goal with nia.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
