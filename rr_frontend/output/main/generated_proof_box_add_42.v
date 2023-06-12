From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.main Require Import generated_code_main generated_specs_main extra_proofs_main.
Set Default Proof Using "Type".

Section proof.
Context `{typeGS Σ}.
Lemma box_add_42_proof   (π : thread_id) :
  ⊢ typed_function π (box_add_42_def ) [PtrSynType; IntSynType I32] (type_of_box_add_42 ).
Proof.
  intros.
  iStartProof.
  start_function "box_add_42" ( [] ) (  x ).
  set (loop_map := BB_INV_MAP (PolyNil)).
  intros arg_x local___0 local___2.
  prepare_parameters ( x ).
  init_lfts (∅ ).
  init_tyvars ( ∅ ).
  repeat liRStep; liShow.
  all: print_typesystem_goal "box_add_42".
  Unshelve. all: li_unshelve_sidecond; sidecond_hook.
  Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; try (unfold_common_defs; solve_goal); unsolved_sidecond_hook.
  Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "box_add_42".
Qed.
End proof.