From caesium Require Import lang notation.
From refinedrust Require Import typing.
From refinedrust.examples.minivec_patched Require Import generated_code_minivec generated_specs_minivec.
From refinedrust.examples.minivec_patched Require Import extra_proofs_minivec.
Set Default Proof Using "Type".

Section proof.
Context `{typeGS Σ}.
Lemma Vec_T_get_unchecked_mut_proof (T_rt : Type) `{!Inhabited T_rt} (T_st : syn_type) (Vec_T_ptr_T_loc : loc) (ptr_add_T_loc : loc) (π : thread_id) :
  syn_type_is_layoutable (T_st) →
  syn_type_is_layoutable ((syn_type_of_sls ((Vec_sls (T_st))))) →
  Vec_T_ptr_T_loc ◁ᵥ{π} Vec_T_ptr_T_loc @ function_ptr [PtrSynType] (type_of_Vec_T_ptr T_rt T_st) -∗
  ptr_add_T_loc ◁ᵥ{π} ptr_add_T_loc @ function_ptr [PtrSynType; IntSynType USize] (type_of_ptr_add T_rt T_st) -∗
  typed_function π (Vec_T_get_unchecked_mut_def Vec_T_ptr_T_loc ptr_add_T_loc T_st) [PtrSynType; PtrSynType; PtrSynType; PtrSynType; PtrSynType; PtrSynType; IntSynType USize; IntSynType USize; PtrSynType] (type_of_Vec_T_get_unchecked_mut T_rt T_st).
Proof.
  intros.
  iStartProof.
  start_function "Vec_T_get_unchecked_mut" ( [ [] ulft__] ) ( [ [ [  xs γ ] i ] T_ty ] ).
  set (loop_map := BB_INV_MAP (PolyNil)).
  intros arg_self arg_index local___0 local___3 local___4 local_p local___6 local___7 local___8 local_ret.
  prepare_parameters ( xs γ i T_ty ).
  init_lfts ( named_lft_update "ulft__" ulft__  ∅ ).
  init_tyvars ( <[ "T" := existT _ (T_ty) ]>%E $ ∅ ).
  repeat liRStep; liShow.

  all: print_typesystem_goal "Vec_T_get_unchecked_mut".
  Unshelve. all: unshelve_sidecond; sidecond_hook.
  Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; try (unfold_common_defs; solve_goal); unsolved_sidecond_hook.

  all: try (rewrite project_vec_els_insert_lt /=; [|lia]; normalize_and_simpl_goal).
  (* NOTE: ideally, I'd like to assert this as an inline lemma or so *)
  all: assert (length xs ≤ length x2); first (rewrite -(fmap_length PlaceIn xs); revert select (PlaceIn <$> xs = _) => ->; rewrite project_vec_els_length; lia).
  all: normalize_and_simpl_goal; try solve_goal with lia.

  { solve_goal with nia. }
  { solve_goal with nia. }
  { apply list_lookup_insert_Some'. 
    split; normalize_and_simpl_goal.
    { lia. }
    { revert select (PlaceIn <$> xs = _) => ->.
      normalize_and_simpl_goal.
      lia. }
  }
  { by revert select (PlaceIn <$> xs = _) => ->. }

  Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "Vec_T_get_unchecked_mut".
Qed.
End proof.
