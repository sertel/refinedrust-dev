From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.minivec_patched Require Import generated_code_minivec generated_specs_minivec extra_proofs_minivec.
Set Default Proof Using "Type".

Section proof.
Context `{typeGS Σ}.

Lemma Vec_T_get_proof (T_rt : Type) `{Inhabited T_rt} (T_st : syn_type) (Vec_T_len_T_loc : loc) (Vec_T_get_unchecked_T_loc : loc) (π : thread_id) :
  syn_type_is_layoutable (T_st) →
  syn_type_is_layoutable ((syn_type_of_sls ((Vec_sls (T_st))))) →
  syn_type_is_layoutable ((syn_type_of_els ((std_option_Option_els (PtrSynType))))) →
  Vec_T_len_T_loc ◁ᵥ{π} Vec_T_len_T_loc @ function_ptr [PtrSynType] (type_of_Vec_T_len (T_rt) (T_st)) -∗
  Vec_T_get_unchecked_T_loc ◁ᵥ{π} Vec_T_get_unchecked_T_loc @ function_ptr [PtrSynType; IntSynType USize] (type_of_Vec_T_get_unchecked (T_rt) (T_st)) -∗
  typed_function π (Vec_T_get_def Vec_T_len_T_loc Vec_T_get_unchecked_T_loc T_st) [(syn_type_of_els ((std_option_Option_els (PtrSynType)))); BoolSynType; IntSynType USize; IntSynType USize; PtrSynType; PtrSynType; PtrSynType; PtrSynType; IntSynType USize] (type_of_Vec_T_get T_rt T_st).
Proof.
  intros.
  iStartProof.
  start_function "Vec_T_get" ( [ [] ulft__] ) ( [ [  xs i ] T_ty ] ).
  set (loop_map := BB_INV_MAP (PolyNil)).
  intros arg_self arg_index local___0 local___3 local___4 local___5 local___6 local___7 local___8 local___9 local___10.
  prepare_parameters ( xs i T_ty ).
  init_lfts (named_lft_update "ulft__" ulft__ $ ∅ ).
  init_tyvars ( <[ "T" := existT _ (T_ty) ]>%E $ ∅ ).

  repeat liRStep; liShow.

  all: print_typesystem_goal "Vec_T_get".
  Unshelve. 

  all: unshelve_sidecond; sidecond_hook.
  Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; try (unfold_common_defs; solve_goal); unsolved_sidecond_hook.
  Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "Vec_T_get".
Qed.
End proof.
