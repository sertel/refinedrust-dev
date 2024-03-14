From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.minivec.generated Require Import generated_code_minivec generated_specs_minivec.
From refinedrust.examples.minivec.generated Require Import generated_template_Vec_T_pop.

Set Default Proof Using "Type".

Section proof.
Context `{!typeGS Σ}.
Lemma Vec_T_pop_proof (π : thread_id) :
  Vec_T_pop_lemma π.
Proof.
  Vec_T_pop_prelude.

  rep liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal with (nia).

  all: revert select (<#> _ = _) => Hxs; specialize (project_vec_els_length' _ _ _ Hxs) as ?.
  {
    rewrite Hxs project_vec_els_insert_ge; [|lia].
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
    rewrite fmap_take. rewrite Hxs.
    rewrite project_vec_els_take. f_equal. lia.
  }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
