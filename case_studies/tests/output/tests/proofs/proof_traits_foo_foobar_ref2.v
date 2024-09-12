From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.tests.generated Require Import generated_code_tests generated_specs_tests generated_template_traits_foo_foobar_ref2.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Ltac multirepeat tac :=
  match goal with
  | |- _ => tac
  | _ => fail 1000
  end.

Lemma traits_foo_foobar_ref2_proof (π : thread_id) :
  traits_foo_foobar_ref2_lemma π.
Proof.
  traits_foo_foobar_ref2_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { (* TODO: augment the lft alive solver to handle symbolic cases *)
    admit.
    }
  { solve_elctx_sat.
  notypeclasses refine (tac_elctx_app_ty_outlives_E _ _ _ _ _ _).
         solve_elctx_submseteq. 
    refine (tac_lctx_lft_incl_init_list _ _ _ _ _).

  (*Ltac multirepeat tac ::=*)
  (*lazymatch goal with*)
  (*| |- ?H => idtac H; tac; tac; first [solve [fail] | multirepeat tac]*)
  (*| |- _ => fail*)
  (*end.*)


    (* TODO: 
       problem here:
       - see the notes on the elctx rule in the inclusion solver.
       - the same lifetime can appear multiple times on the LHS of the elctx
       - there may be cycles
       - So expanding/following an inclusion isn't always safe and may get us into cycles or deadlocks.


       Can we normalize the context before to fix this?
       Can we convert to multiinclusions that are always safe? e.g. left-ro-right or right-to-left?

       In principle, we could follow inclusions on both sides, but always include all candidates.
       Then we use an exists- exists interpretation, i.e., we need to find a match on both sides.
       Problem: this can quickly explode
     *)

    (*list_find_tac*)
    (*
    Ltac list_find_tac_noindex' cont l ::=
  multimatch l with
  | [] => fail
  | ?h :: ?l => (cont h)
  | ?h :: ?l => (list_find_tac_noindex' cont l)
  | _ ++ ?l => list_find_tac_noindex' cont l
  end.
multimatch goal with
| |- lctx_lft_incl_list ?E ?L ?κs1 ?κs2 =>
        let find_in_elctx j κ :=
         list_find_tac_noindex
          ltac:(fun el =>
                  multimatch el with
                  | κ ⊑ₑ ?κ' =>
                      notypeclasses refine
                       (tac_lctx_lft_incl_list_augment_external E L κ κ' κs1
                          κs2 j _ _ _);
                       [ elctx_list_elem_solver | reflexivity | simpl;
                           match goal with 
                           | |- ?H2 => idtac H2
                            end ]
                  | _ => fail
                  end) E
        in
        list_find_tac find_in_elctx κs1;
        solve_lft_incl_list_step

end.
notypeclasses refine (tac_lctx_lft_incl_list_augment_external _ _ ϝ0 κ _ _ 0 _ _ _);
                    [ elctx_list_elem_solver | reflexivity | simpl ];
                        solve_lft_incl_list_step.

solve_lft_incl_list_step;
solve_lft_incl_list_step; solve[fail].
  multirepeat solve_lft_incl_list_step.

    match goal with
         first [ solve_lft_incl_list_step | done].
      (* TODO: here, the solver gets misled and should backtrack *)
    solve_elctx_sat_step.
     *)

  (* TODO look at these *)
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
