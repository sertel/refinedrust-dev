From caesium Require Import lang notation.
From refinedrust Require Import typing.
From refinedrust.examples.minivec_patched Require Import generated_code_minivec generated_specs_minivec.
From refinedrust.examples.minivec_patched Require Import extra_proofs_minivec.
Set Default Proof Using "Type".

Section proof.
Context `{typeGS Σ}.

Lemma Vec_T_push_proof (T_rt : Type) (T_st : syn_type) (Vec_T_cap_T_loc : loc) (Vec_T_ptr_T_loc : loc) (ptr_add_T_loc : loc) (std_ptr_write_T_loc : loc) (RawVec_T_grow_T_loc : loc) (π : thread_id) :
  syn_type_is_layoutable (T_st) →
  syn_type_is_layoutable ((syn_type_of_sls ((RawVec_sls (T_st))))) →
  syn_type_is_layoutable ((syn_type_of_sls ((Vec_sls (T_st))))) →
  Vec_T_cap_T_loc ◁ᵥ{π} Vec_T_cap_T_loc @ function_ptr [PtrSynType] (type_of_Vec_T_cap T_rt T_st) -∗
  Vec_T_ptr_T_loc ◁ᵥ{π} Vec_T_ptr_T_loc @ function_ptr [PtrSynType] (type_of_Vec_T_ptr T_rt T_st) -∗
  ptr_add_T_loc ◁ᵥ{π} ptr_add_T_loc @ function_ptr [PtrSynType; IntSynType USize] (type_of_ptr_add T_rt T_st) -∗
  std_ptr_write_T_loc ◁ᵥ{π} std_ptr_write_T_loc @ function_ptr [PtrSynType; T_st] (type_of_ptr_write T_rt T_st) -∗
  RawVec_T_grow_T_loc ◁ᵥ{π} RawVec_T_grow_T_loc @ function_ptr [PtrSynType] (type_of_RawVec_T_grow T_rt T_st) -∗
  typed_function π (Vec_T_push_def Vec_T_cap_T_loc Vec_T_ptr_T_loc ptr_add_T_loc std_ptr_write_T_loc RawVec_T_grow_T_loc T_st) [UnitSynType; UnitSynType; BoolSynType; IntSynType USize; IntSynType USize; PtrSynType; UnitSynType; PtrSynType; UnitSynType; UnitSynType; PtrSynType; PtrSynType; PtrSynType; IntSynType USize; T_st; IntSynType USize] (type_of_Vec_T_push T_rt T_st).
Proof.
  intros.
  iStartProof.
  start_function "Vec_T_push" ( [ [] ulft__] ) ( [ [ [  xs γ ] x ] T_ty ] ).
  set (loop_map := BB_INV_MAP (PolyNil)).
  intros arg_self arg_elem local___0 local___3 local___4 local___5 local___6 local___7 local___8 local___9 local___10 local___11 local___12 local___13 local___14 local___15 local___16 local___17.
  prepare_parameters ( xs γ x T_ty ).
  init_lfts ( named_lft_update "ulft__" ulft__ ∅ ).
  init_tyvars ( <[ "T" := existT _ (T_ty) ]>%E $ ∅ ).
  repeat liRStep; liShow.

  all: print_typesystem_goal "Vec_T_push".
  Unshelve. all: unshelve_sidecond; sidecond_hook.

  Unshelve.
  all: rename select (length (project_vec_els _ _) < _) into Hels.
  all: match type of Hels with (Z.of_nat (length (project_vec_els ?len2 ?xs2)) < _)%Z => rename len2 into len; rename xs2 into xs end.
  all: rewrite project_vec_els_length in Hels.
  all: rename select (size_of_array_in_bytes (ty_syn_type T_ty) _ ≤ MaxInt isize_t) into Hsz.
  all: rename select (∀ i: nat, (0 <= i < len)%nat → _) into Hlook_1.
  all: rename select (∀ i: nat, (len <= i < _)%nat → _) into Hlook_2.

  Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal.
  all: try solve_goal with (lia).
  all: try (unfold_common_defs; solve_goal with (lia)).

  {
    move: Hsz. rewrite /size_of_array_in_bytes.
    rewrite project_vec_els_length.
    lia.
  }

  {
    rewrite project_vec_els_insert_lt /=; [|lia].
    apply list_lookup_insert_Some'.
    split;normalize_and_simpl_goal.
    1: lia.
    erewrite project_vec_els_lookup_mono; [solve_goal|lia|].
    rewrite lookup_app_l; [done|lia].
  }
  {
    rewrite project_vec_els_insert_lt /=; [|lia].
    apply (list_eq_split (length xs)).
    - rewrite take_insert; [|lia]. rewrite take_app_alt ?project_vec_els_length; [|lia].
      rewrite project_vec_els_take project_vec_els_take_r. f_equal; [lia|].
      rewrite take_app_le; [|lia]. rewrite take_ge; [done|lia].
    - rewrite drop_insert_le; [|lia]. rewrite drop_app_alt ?project_vec_els_length; [|lia].
      rewrite project_vec_els_drop. apply list_eq_singleton. split; solve_goal.
  }
  { move: Hsz. rewrite /size_of_array_in_bytes. rewrite project_vec_els_length. simplify_layout_goal. nia. }
  { nia. }
  {
    (* TODO *)
    assert (len < length xs) as ?.
    { specialize (Hlook_2 len ltac:(lia)).
      apply lookup_lt_Some in Hlook_2.
      lia. }

    rewrite project_vec_els_insert_lt /=; [|lia].
    apply list_lookup_insert_Some'. split; normalize_and_simpl_goal.
    { lia. }
    erewrite project_vec_els_lookup_mono; [solve_goal|lia|done].
  }
  {
    (* TODO should get this in a different way *)
    assert (len < length xs) as ?.
    { specialize (Hlook_2 len ltac:(lia)).
      apply lookup_lt_Some in Hlook_2.
      lia. }
    nia. }
  {
    (* TODO we should get this in a different way *)
    assert (len < length xs) as ?.
    { specialize (Hlook_2 len ltac:(lia)).
      apply lookup_lt_Some in Hlook_2.
      lia. }
    (* I guess I want to know  that len < length xs. *)
    rewrite project_vec_els_insert_lt /=; [|lia].
    apply (list_eq_split len).
    - rewrite take_insert; [|lia]. rewrite take_app_alt ?project_vec_els_length; [|lia].
      rewrite project_vec_els_take. f_equal. lia.
    - rewrite drop_insert_le; [|lia]. rewrite drop_app_alt ?project_vec_els_length; [|lia].
      rewrite project_vec_els_drop.
      apply list_eq_singleton. split; first solve_goal.
      normalize_and_simpl_goal. solve_goal.
  }


  Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "Vec_T_push".
Qed.
End proof.
