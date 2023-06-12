From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.main Require Import generated_code_main generated_specs_main extra_proofs_main.
Set Default Proof Using "Type".

Section proof.
Context `{typeGS Σ}.
Lemma mut_ref_add_client_proof  (mut_ref_add_42_loc : loc) (π : thread_id) :
  mut_ref_add_42_loc ◁ᵥ{π} mut_ref_add_42_loc @ function_ptr [PtrSynType] (type_of_mut_ref_add_42 ) -∗
  typed_function π (mut_ref_add_client_def mut_ref_add_42_loc) [UnitSynType; IntSynType I32; UnitSynType; PtrSynType; PtrSynType; UnitSynType; BoolSynType; BoolSynType; IntSynType I32; UnitSynType] (type_of_mut_ref_add_client ).
Proof.
  intros.
  iStartProof.
  start_function "mut_ref_add_client" ( [] ) ( ? ).
  set (loop_map := BB_INV_MAP (PolyNil)).
  intros local___0 local_z local___2 local___3 local___4 local___5 local___6 local___7 local___8 local___9.
  prepare_parameters ( ).
  init_lfts (∅ ).
  init_tyvars ( ∅ ).
  repeat liRStep; liShow.
  all: print_typesystem_goal "mut_ref_add_client".
  Unshelve. all: li_unshelve_sidecond; sidecond_hook.
  Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; try (unfold_common_defs; solve_goal); unsolved_sidecond_hook.
  Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "mut_ref_add_client".
Qed.
End proof.