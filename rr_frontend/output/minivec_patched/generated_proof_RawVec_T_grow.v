From caesium Require Import lang notation.
From refinedrust Require Import typing.
From refinedrust.examples.minivec_patched Require Import generated_code_minivec generated_specs_minivec.
Set Default Proof Using "Type".

Section proof.
Context `{typeGS Σ}.
Lemma RawVec_T_grow_proof (T_rt : Type) (T_st : syn_type) (check_array_layoutable_T_loc : loc) (realloc_array_T_loc : loc) (alloc_array_T_loc : loc) (std_mem_size_of_T_loc : loc) (π : thread_id) :
  syn_type_is_layoutable (T_st) →
  syn_type_is_layoutable ((syn_type_of_sls ((RawVec_sls (T_st))))) →
  check_array_layoutable_T_loc ◁ᵥ{π} check_array_layoutable_T_loc @ function_ptr [IntSynType USize] (type_of_check_array_layoutable T_rt T_st) -∗
  realloc_array_T_loc ◁ᵥ{π} realloc_array_T_loc @ function_ptr [IntSynType USize; PtrSynType; IntSynType USize] (type_of_realloc_array T_rt T_st) -∗
  alloc_array_T_loc ◁ᵥ{π} alloc_array_T_loc @ function_ptr [IntSynType USize] (type_of_alloc_array T_rt T_st) -∗
  std_mem_size_of_T_loc ◁ᵥ{π} std_mem_size_of_T_loc @ function_ptr [] (type_of_mem_size_of T_rt T_st) -∗
  typed_function π (RawVec_T_grow_def check_array_layoutable_T_loc realloc_array_T_loc alloc_array_T_loc std_mem_size_of_T_loc T_st) [UnitSynType; UnitSynType; BoolSynType; BoolSynType; IntSynType USize; UnitSynType; IntSynType USize; BoolSynType; IntSynType USize; IntSynType USize; IntSynType USize; UnitSynType; BoolSynType; BoolSynType; IntSynType USize; UnitSynType; PtrSynType; BoolSynType; IntSynType USize; IntSynType USize; PtrSynType; IntSynType USize; PtrSynType; PtrSynType; IntSynType USize; PtrSynType; PtrSynType; IntSynType USize] (type_of_RawVec_T_grow T_rt T_st).
Proof.
  intros.
  iStartProof.
  start_function "RawVec_T_grow" ( [ [] ulft__] ) ( [ [ [ [  l xs ] cap ] γ ] T_ty ] ).
  set (loop_map := BB_INV_MAP (PolyNil)).
  intros arg_self local___0 local___2 local___3 local___4 local___5 local___6 local_new_cap local___8 local___9 local___11 local___12 local___13 local___14 local___15 local___16 local___17 local_new_ptr local___19 local___20 local___21 local_old_ptr local___23 local___24 local___25 local___26 local___27 local___28 local___29.
  prepare_parameters ( l xs cap γ T_ty ).
  init_lfts ( named_lft_update "ulft__" ulft__ $ ∅ ).
  init_tyvars ( <[ "T" := existT _ (T_ty) ]>%E $ ∅ ).
  repeat liRStep; liShow.

  all: print_typesystem_goal "RawVec_T_grow".
  Unshelve. all: unshelve_sidecond; sidecond_hook.
  Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; try (unfold_common_defs; solve_goal); unsolved_sidecond_hook.
  all: solve_goal with nia.
  Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "RawVec_T_grow".
Qed.
End proof.
