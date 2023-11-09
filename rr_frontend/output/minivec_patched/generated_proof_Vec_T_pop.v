From caesium Require Import lang notation.
From refinedrust Require Import typing.
From refinedrust.examples.minivec_patched Require Import generated_code_minivec generated_specs_minivec.
From refinedrust.examples.minivec_patched Require Import extra_proofs_minivec.
Set Default Proof Using "Type".

Section proof.
Context `{typeGS Σ}.

Lemma Vec_T_pop_proof (T_rt : Type) `{!Inhabited T_rt} (T_st : syn_type) (Vec_T_ptr_T_loc : loc) (std_ptr_read_T_loc : loc) (ptr_add_T_loc : loc) (π : thread_id) :
  syn_type_is_layoutable (T_st) →
  syn_type_is_layoutable ((syn_type_of_sls ((Vec_sls (T_st))))) →
  syn_type_is_layoutable ((syn_type_of_els ((std_option_Option_els T_st)))) →
  Vec_T_ptr_T_loc ◁ᵥ{π} Vec_T_ptr_T_loc @ function_ptr [PtrSynType] (type_of_Vec_T_ptr T_rt T_st) -∗
  std_ptr_read_T_loc ◁ᵥ{π} std_ptr_read_T_loc @ function_ptr [PtrSynType] (type_of_ptr_read T_rt T_st) -∗
  ptr_add_T_loc ◁ᵥ{π} ptr_add_T_loc @ function_ptr [PtrSynType; IntSynType USize] (type_of_ptr_add T_rt T_st) -∗
  typed_function π (Vec_T_pop_def Vec_T_ptr_T_loc std_ptr_read_T_loc ptr_add_T_loc T_st) [(syn_type_of_els ((std_option_Option_els (T_st)))); BoolSynType; IntSynType USize; IntSynType USize; T_st; PtrSynType; PtrSynType; PtrSynType; PtrSynType; IntSynType USize] (type_of_Vec_T_pop T_rt T_st).
Proof.
  intros.
  iStartProof.
  start_function "Vec_T_pop" ( [ [] ulft__] ) ( [ [  xs γ ] T_ty ] ).
  set (loop_map := BB_INV_MAP (PolyNil)).
  intros arg_self local___0 local___2 local___3 local___4 local___5 local___6 local___7 local___8 local___9 local___10.
  prepare_parameters ( xs γ T_ty ).
  init_lfts (named_lft_update "ulft__" ulft__ $ ∅ ).
  init_tyvars ( <[ "T" := existT _ (T_ty) ]>%E $ ∅ ).

  repeat liRStep; liShow.

  all: print_typesystem_goal "Vec_T_pop".
  Unshelve. all: unshelve_sidecond; sidecond_hook.
  Unshelve. 
  all: prepare_sideconditions; normalize_and_simpl_goal; (try solve_goal with lia); try (unfold_common_defs; solve_goal with lia); unsolved_sidecond_hook.
  all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal with (nia).

  all: revert select (PlaceIn <$> xs = _) => Hxs; specialize (project_vec_els_length' _ _ _ Hxs) as ?.
  { 
    revert select (PlaceIn <$> xs = _) => ->.
    rewrite project_vec_els_insert_ge; [|lia].
    erewrite project_vec_els_lookup_mono; [solve_goal|lia|done].
  }
  { apply list_lookup_insert_Some'. split; solve_goal. }
  { solve_goal. }
  {
    rewrite last_lookup list_lookup_lookup_total_lt /=; [|lia].
    eexists _. split; [done|].
    do 3 f_equal. lia.
  }
  {
    rewrite project_vec_els_insert_ge; [|lia].
    rewrite fmap_take. revert select (PlaceIn <$> xs = _) => ->.
    rewrite project_vec_els_take. f_equal. lia.
  }

  Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "Vec_T_pop".
Qed.
End proof.
