From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.minivec.generated Require Import generated_code_minivec generated_specs_minivec.
From refinedrust.examples.minivec.generated Require Import generated_template_Vec_T_get_mut.

Set Default Proof Using "Type".

Section proof.
Context `{!typeGS Σ}.
Lemma Vec_T_get_mut_proof (π : thread_id) :
  Vec_T_get_mut_lemma π.
Proof.
  Vec_T_get_mut_prelude.

  repeat liRStep; liShow.
  {
    iRename select (Inherit κ0 _ _) into "Hinh1".
    iRename select (Inherit κ1 _ _) into "Hinh2".
    liInst Hevar1 γ0. repeat liRStep; liShow.
    iApply (prove_with_subtype_inherit_manual with "Hinh1 []"); [shelve_sidecond | iIntros "$" | ].
    repeat liRStep; liShow.
    iApply (prove_with_subtype_inherit_manual with "Hinh2 []"); [shelve_sidecond | iIntros "$" | ].
    repeat liRStep; liShow.
  }
  {
    liInst Hevar1 γ.
    repeat liRStep; liShow.
  }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { (* TODO: currently not handled by the solver *)
    apply Forall_forall.
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
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
