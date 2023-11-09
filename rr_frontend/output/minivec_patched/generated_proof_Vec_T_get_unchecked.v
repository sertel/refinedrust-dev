From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.minivec_patched Require Import generated_code_minivec generated_specs_minivec extra_proofs_minivec.
Set Default Proof Using "Type".

Section proof.
Context `{typeGS Σ}.
Lemma Vec_T_get_unchecked_proof (T_rt : Type) `{Inhabited T_rt} (T_st : syn_type) (Vec_T_ptr_T_loc : loc) (ptr_add_T_loc : loc) (π : thread_id) :
  syn_type_is_layoutable (T_st) →
  syn_type_is_layoutable ((syn_type_of_sls ((Vec_sls (T_st))))) →
  Vec_T_ptr_T_loc ◁ᵥ{π} Vec_T_ptr_T_loc @ function_ptr [PtrSynType] (type_of_Vec_T_ptr (T_rt) (T_st)) -∗
  ptr_add_T_loc ◁ᵥ{π} ptr_add_T_loc @ function_ptr [PtrSynType; IntSynType USize] (type_of_ptr_add (T_rt) (T_st)) -∗
  typed_function π (Vec_T_get_unchecked_def Vec_T_ptr_T_loc ptr_add_T_loc T_st) [PtrSynType; IntSynType USize; PtrSynType; PtrSynType; PtrSynType; IntSynType USize; PtrSynType] (type_of_Vec_T_get_unchecked T_rt T_st).
Proof.
  intros.
  iStartProof.
  start_function "Vec_T_get_unchecked" ( [ [] ulft__] ) ( [ [  xs i ] T_ty ] ).
  set (loop_map := BB_INV_MAP (PolyNil)).
  intros arg_self arg_index local___0 local___3 local_p local___5 local___6 local___7 local_ret.
  prepare_parameters ( xs i T_ty ).
  init_lfts (named_lft_update "ulft__" ulft__ $ ∅ ).
  init_tyvars ( <[ "T" := existT _ (T_ty) ]>%E $ ∅ ).
  repeat liRStep; liShow.
  all: print_typesystem_goal "Vec_T_get_unchecked".
  Unshelve. all: unshelve_sidecond; sidecond_hook.
  Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; try (unfold_common_defs; solve_goal); unsolved_sidecond_hook.

  all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal with nia. 

  Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "Vec_T_get_unchecked".
Qed.
End proof.
