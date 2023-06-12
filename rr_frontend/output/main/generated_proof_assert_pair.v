From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.main Require Import generated_code_main generated_specs_main extra_proofs_main.
Set Default Proof Using "Type".

Section proof.
Context `{typeGS Σ}.
Lemma assert_pair_proof   (π : thread_id) :
  syn_type_is_layoutable ((syn_type_of_sls ((tuple2_sls (IntSynType I32) (IntSynType I32))))) →
  syn_type_is_layoutable ((syn_type_of_sls ((tuple2_sls (IntSynType I32) (IntSynType I32))))) →
  syn_type_is_layoutable ((syn_type_of_sls ((tuple2_sls (IntSynType I32) (IntSynType I32))))) →
  syn_type_is_layoutable ((syn_type_of_sls ((tuple2_sls (IntSynType I32) (IntSynType I32))))) →
  syn_type_is_layoutable ((syn_type_of_sls ((tuple2_sls (IntSynType I32) (IntSynType I32))))) →
  syn_type_is_layoutable ((syn_type_of_sls ((tuple2_sls (IntSynType I32) (IntSynType I32))))) →
  ⊢ typed_function π (assert_pair_def ) [UnitSynType; (syn_type_of_sls ((tuple2_sls (IntSynType I32) (IntSynType I32)))); PtrSynType; UnitSynType; BoolSynType; BoolSynType; BoolSynType; IntSynType I32; BoolSynType; IntSynType I32; UnitSynType] (type_of_assert_pair ).
Proof.
  intros.
  iStartProof.
  start_function "assert_pair" ( [] ) ( ? ).
  set (loop_map := BB_INV_MAP (PolyNil)).
  intros local___0 local_x local_xr local___3 local___4 local___5 local___6 local___7 local___8 local___9 local___10.
  prepare_parameters ( ).
  init_lfts (∅ ).
  init_tyvars ( ∅ ).
  repeat liRStep; liShow.
  all: print_typesystem_goal "assert_pair".
  Unshelve. all: li_unshelve_sidecond; sidecond_hook.
  Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; try (unfold_common_defs; solve_goal); unsolved_sidecond_hook.
  Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "assert_pair".
Qed.
End proof.