From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.minivec.generated Require Import generated_code_minivec generated_specs_minivec.
From refinedrust.examples.minivec.generated Require Import generated_template_Vec_T_push.

Set Default Proof Using "Type".

Section proof.
Context `{!typeGS Σ}.
Lemma Vec_T_push_proof (π : thread_id) :
  Vec_T_push_lemma π.
Proof.
  Vec_T_push_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.

  all: match type of Hlen_cap with (Z.of_nat (length (project_vec_els ?len2 ?xs2)) < _)%Z => rename len2 into len; rename xs2 into xs end.
  all: rewrite project_vec_els_length in Hlen_cap.

  Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal.
  all: try solve_goal with (lia).
  all: try (unfold_common_defs; solve_goal with (lia)).

  { rewrite project_vec_els_length in Hlen_eq. solve_goal. }
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
  { move: Hcap. clear. nia. }

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

  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
