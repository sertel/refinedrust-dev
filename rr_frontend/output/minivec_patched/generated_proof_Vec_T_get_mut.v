From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.minivec_patched Require Import generated_code_minivec generated_specs_minivec extra_proofs_minivec.
Set Default Proof Using "Type".

Section proof.
Context `{typeGS Σ}.



Lemma Vec_T_get_mut_proof (T_rt : Type) `{Inhabited T_rt} (T_st : syn_type) (Vec_T_get_unchecked_mut_T_loc : loc) (Vec_T_len_T_loc : loc) (π : thread_id) :
  syn_type_is_layoutable (T_st) →
  syn_type_is_layoutable ((syn_type_of_sls ((Vec_sls (T_st))))) →
  syn_type_is_layoutable ((syn_type_of_els ((std_option_Option_els (PtrSynType))))) →
  Vec_T_get_unchecked_mut_T_loc ◁ᵥ{π} Vec_T_get_unchecked_mut_T_loc @ function_ptr [PtrSynType; IntSynType USize] (type_of_Vec_T_get_unchecked_mut T_rt T_st) -∗
  Vec_T_len_T_loc ◁ᵥ{π} Vec_T_len_T_loc @ function_ptr [PtrSynType] (type_of_Vec_T_len T_rt T_st) -∗
  typed_function π (Vec_T_get_mut_def Vec_T_get_unchecked_mut_T_loc Vec_T_len_T_loc T_st) [(syn_type_of_els ((std_option_Option_els (PtrSynType)))); BoolSynType; IntSynType USize; IntSynType USize; PtrSynType; PtrSynType; PtrSynType; PtrSynType; IntSynType USize] (type_of_Vec_T_get_mut T_rt T_st).
Proof.
  intros.
  iStartProof.
  start_function "Vec_T_get_mut" ( [ [] ulft__] ) ( [ [ [  xs γ ] i ] T_ty ] ).
  set (loop_map := BB_INV_MAP (PolyNil)).
  intros arg_self arg_index local___0 local___3 local___4 local___5 local___6 local___7 local___8 local___9 local___10.
  prepare_parameters ( xs γ i T_ty ).
  init_lfts (named_lft_update "ulft__" ulft__ $ ∅ ).
  init_tyvars ( <[ "T" := existT _ (T_ty) ]>%E $ ∅ ).

  repeat liRStep; liShow.
  { rewrite decide_True; last solve_goal.
    repeat liRStep;liShow.

    iRename select (Inherit κ0 _ _) into "Hinh1".
    iRename select (Inherit κ1 _ _) into "Hinh2".
    rewrite decide_True; last solve_goal.
    iApply (prove_with_subtype_inherit_manual with "Hinh1 []"); first shelve_sidecond.
    { liInst Hevar1 γ0. iIntros "$". }
    repeat liRStep; liShow.
    liInst Hevar0 x'.
    repeat liRStep; liShow.
    rewrite decide_True; last solve_goal.
    iApply (prove_with_subtype_inherit_manual with "Hinh2 []"); first shelve_sidecond.
    { iIntros "$". }
    repeat liRStep; liShow. 
  }

  { 
    rewrite decide_False; last by solve_goal.
    repeat liRStep; liShow.
    rewrite decide_False; last by solve_goal.
    repeat liRStep; liShow.
    liInst Hevar1 γ.
    repeat liRStep; liShow.
    rewrite decide_False; last by solve_goal.
    repeat liRStep; liShow.
    rewrite decide_False; last by solve_goal.
    repeat liRStep; liShow.
  }

  all: print_typesystem_goal "Vec_T_get_mut".
  Unshelve.
  all: unshelve_sidecond; sidecond_hook.
  Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; try (unfold_common_defs; solve_goal); unsolved_sidecond_hook.
  { (* TODO: currently not handled by the solver *)
    apply Forall_forall.
    rewrite /ty_lfts/=.
    rewrite {2}/ty_lfts/=. rewrite app_nil_r.
    intros κe Hlft.
    eapply (lctx_lft_alive_incl ϝ); first sidecond_hook.
    apply lctx_lft_incl_external.
    apply elem_of_cons; right.
    apply elem_of_cons; right.
    apply elem_of_app; right.
    apply elem_of_app; left.
    unfold_opaque @ty_outlives_E.
    rewrite /lfts_outlives_E.
    rewrite elem_of_list_fmap.
    eexists. split; done. }
  { rewrite decide_True; solve_goal. }
  { rewrite decide_True; solve_goal. }

  Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "Vec_T_get_mut".
Qed.
End proof.
