From caesium Require Import lang notation.
From refinedrust Require Import typing.
From refinedrust.examples.minivec_patched Require Import generated_code_minivec generated_specs_minivec.
Set Default Proof Using "Type".

Section proof.
Context `{typeGS Σ}.
Lemma RawVec_T_ptr_proof (T_rt : Type) (T_st : syn_type)  (π : thread_id) :
  syn_type_is_layoutable (T_st) →
  syn_type_is_layoutable ((syn_type_of_sls ((RawVec_sls (T_st))))) →
  ⊢ typed_function π (RawVec_T_ptr_def T_st) [PtrSynType; PtrSynType] (type_of_RawVec_T_ptr T_rt T_st).
Proof.
  intros.
  iStartProof.
  start_function "RawVec_T_ptr" ( [ [] ulft__] ) ( [ [  l cap ] T_ty ] ).
  set (loop_map := BB_INV_MAP (PolyNil)).
  intros arg_self local___0 local___2.
  prepare_parameters ( l cap T_ty ).
  init_lfts ( named_lft_update "ulft__" ulft__ $ ∅ ).
  init_tyvars ( <[ "T" := existT _ (T_ty) ]>%E $ ∅ ).
  repeat liRStep; liShow.
  all: print_typesystem_goal "RawVec_T_ptr".
  Unshelve. all: unshelve_sidecond; sidecond_hook.
  Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; try (unfold_common_defs; solve_goal); unsolved_sidecond_hook.
  Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "RawVec_T_ptr".
Qed.
End proof.
