From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.minivec_patched Require Import generated_code_minivec generated_specs_minivec extra_proofs_minivec.
Set Default Proof Using "Type".

Section proof.
Context `{typeGS Σ}.


Lemma get_mut_client_proof  (Vec_T_new_i32_loc : loc) (Vec_T_push_i32_loc : loc) (Vec_T_get_mut_i32_loc : loc) (std_option_Option_unwrap_def_muti32_loc : loc) (π : thread_id) :
  syn_type_is_layoutable ((syn_type_of_sls ((RawVec_sls (IntSynType I32))))) →
  syn_type_is_layoutable ((syn_type_of_sls ((Vec_sls (IntSynType I32))))) →
  syn_type_is_layoutable ((syn_type_of_els ((std_option_Option_els (PtrSynType))))) →
  Vec_T_new_i32_loc ◁ᵥ{π} Vec_T_new_i32_loc @ function_ptr [] (type_of_Vec_T_new (Z) (IntSynType I32)) -∗
  Vec_T_push_i32_loc ◁ᵥ{π} Vec_T_push_i32_loc @ function_ptr [PtrSynType; IntSynType I32] (type_of_Vec_T_push (Z) (IntSynType I32)) -∗
  Vec_T_get_mut_i32_loc ◁ᵥ{π} Vec_T_get_mut_i32_loc @ function_ptr [PtrSynType; IntSynType USize] (type_of_Vec_T_get_mut (Z) (IntSynType I32)) -∗
  std_option_Option_unwrap_def_muti32_loc ◁ᵥ{π} std_option_Option_unwrap_def_muti32_loc @ function_ptr [(syn_type_of_els ((std_option_Option_els (PtrSynType))))] (type_of_std_option_Option_T_unwrap (((place_rfn Z) * gname)%type) (PtrSynType)) -∗
  typed_function π (get_mut_client_def Vec_T_new_i32_loc Vec_T_push_i32_loc Vec_T_get_mut_i32_loc std_option_Option_unwrap_def_muti32_loc) [UnitSynType; (syn_type_of_sls ((Vec_sls (IntSynType I32)))); UnitSynType; PtrSynType; UnitSynType; PtrSynType; UnitSynType; PtrSynType; PtrSynType; (syn_type_of_els ((std_option_Option_els (PtrSynType)))); PtrSynType; UnitSynType; BoolSynType; BoolSynType; IntSynType I32; UnitSynType; UnitSynType; BoolSynType; BoolSynType; IntSynType I32; PtrSynType; (syn_type_of_els ((std_option_Option_els (PtrSynType)))); PtrSynType; UnitSynType] (type_of_get_mut_client ).
Proof.
  intros.
  iStartProof.
  start_function "get_mut_client" ( [] ) ( ? ).
  set (loop_map := BB_INV_MAP (PolyNil)).
  intros local___0 local_x local___2 local___3 local___4 local___5 local___6 local___7 local_xr local___9 local___10 local___11 local___12 local___13 local___14 local___15 local___16 local___17 local___18 local___19 local___20 local___21 local___22 local___23.
  prepare_parameters ( ).
  init_lfts (∅ ).
  init_tyvars ( ∅ ).

  repeat liRStep; liShow.
  liInst Hevar (int i32).
  repeat liRStep; liShow.

  all: print_typesystem_goal "get_mut_client".
  Unshelve. all: unshelve_sidecond; sidecond_hook.
  Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; try (unfold_common_defs; solve_goal); unsolved_sidecond_hook.
  Unshelve. all: unsafe_unfold_common_caesium_defs; solve_goal.
  Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "get_mut_client".
Qed.
End proof.
