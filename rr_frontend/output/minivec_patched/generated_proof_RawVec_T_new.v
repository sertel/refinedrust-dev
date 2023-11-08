From caesium Require Import lang notation.
From refinedrust Require Import typing.
From refinedrust.examples.minivec_patched Require Import generated_code_minivec generated_specs_minivec.
Set Default Proof Using "Type".

Section proof.
Context `{typeGS Σ}.
Lemma RawVec_T_new_proof (T_rt : Type) (T_st : syn_type) (ptr_dangling_T_loc : loc) (std_mem_size_of_T_loc : loc) (π : thread_id) :
  syn_type_is_layoutable (T_st) →
  syn_type_is_layoutable ((syn_type_of_sls ((RawVec_sls (T_st))))) →
  ptr_dangling_T_loc ◁ᵥ{π} ptr_dangling_T_loc @ function_ptr [] (type_of_ptr_dangling T_rt T_st) -∗
  std_mem_size_of_T_loc ◁ᵥ{π} std_mem_size_of_T_loc @ function_ptr [] (type_of_mem_size_of T_rt T_st) -∗
  typed_function π (RawVec_T_new_def ptr_dangling_T_loc std_mem_size_of_T_loc T_st) [(syn_type_of_sls ((RawVec_sls (T_st)))); IntSynType USize; BoolSynType; IntSynType USize; PtrSynType; PtrSynType; IntSynType USize; UnitSynType] (type_of_RawVec_T_new T_rt T_st).
Proof.
  intros.
  iStartProof.
  start_function "RawVec_T_new" ( [] ) (  T_ty ).
  set (loop_map := BB_INV_MAP (PolyNil)).
  intros local___0 local_cap local___2 local___3 local___4 local___5 local___6 local___7.
  prepare_parameters ( T_ty ).
  init_lfts ( ∅ ).
  init_tyvars ( <[ "T" := existT _ (T_ty) ]>%E $ ∅ ).
  repeat liRStep; liShow.
  all: print_typesystem_goal "RawVec_T_new".
  Unshelve. all: unshelve_sidecond; sidecond_hook.
  Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; try (unfold_common_defs; solve_goal); unsolved_sidecond_hook.
  Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "RawVec_T_new".
Qed.
End proof.
