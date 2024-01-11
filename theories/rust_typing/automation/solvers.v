From iris.proofmode Require Import coq_tactics reduction string_ident.
From refinedrust Require Export type ltypes hlist.
From lithium Require Export all.
From lithium Require Import hooks.
From refinedrust.automation Require Import ident_to_string lookup_definition proof_state.
From refinedrust Require Import int programs program_rules functions uninit references products value arrays.
Set Default Proof Using "Type".


(** * Automation for solving sideconditions *)

(* TODO sometimes this diverges, so we put a timeout on it.
      Should really fix the refined_solver though. *)
Ltac hammer :=
  first [timeout 4 lia | timeout 4 nia | timeout 4 refined_solver lia].
Ltac solve_goal_final_hook ::= refined_solver lia.

(* Reduced version of simplify_eq *)
Ltac subst_with Heq :=
  (* TODO: better implementation? *)
  try match type of Heq with
  | ?a = ?b =>
      is_var a;
      subst a
  | ?a = ?b =>
      is_var b;
      subst b
  end.



(** The main hook for solving sideconditions, will be re-defined later. *)
Ltac sidecond_hook := idtac.
Ltac unsolved_sidecond_hook := idtac.

Tactic Notation "unfold_opaque" constr(c) := with_strategy 0 [c] (unfold c).

(** ** interpret_rust_type solver *)

(** Since [lookup_definition] will give us a term that requires us to
   explicitly give all implicit arguments, we need some hackery to
   apply the arguments of literal type terms that would usually be implicit.
   Basically, we handle the case that the literal term expects a [typeGS] assumption
   and then a number of [Type]s that are later determined by the parameters we instantiate. *)
Ltac count_in_term' term acc :=
  match type of term with
  | ∀ _ : Type, _ =>
      count_in_term' constr:(term nat) constr:(S acc)
  | _ => acc
  end.
Ltac count_in_term term :=
  count_in_term' term constr:(0).
Ltac instantiate_universal_evars term count :=
  match count with
  | 0 => uconstr:(term)
  | S ?n =>
      instantiate_universal_evars uconstr:(term _) constr:(n)
  end.
Ltac instantiate_benign_universals term :=
  lazymatch type of term with
  | ∀ (_ : gFunctors) (_ : typeGS _), _ =>
      instantiate_benign_universals uconstr:(term _ _)
  | ∀ _ : typeGS _, _ =>
      instantiate_benign_universals uconstr:(term ltac:(refine _))
  | _ =>
      constr:(term)
  end.
Ltac instantiate_universals term :=
  let term := instantiate_benign_universals term in
  let count := count_in_term term in
  instantiate_universal_evars term count.
Ltac apply_term_het term apps :=
  match apps with
  | +[] => constr:(term)
  | ?app +:: ?apps =>
      apply_term_het uconstr:(term app) apps
  end.
Ltac apply_term_het_evar term apps :=
  let term := instantiate_universals term in
  apply_term_het term apps.

(** This interprets syntactic Rust types used in some annotations into semantic RefinedRust types *)
(* NOTE: Be REALLY careful with this. The Ltac2 for looking up definitions will easily go haywire, and we cannot properly handle the exceptions here or show them.
   In particular, if this fails for some unknown reason, make sure that there are NO other definitions with the same name in scope, even below other modules! *)
Ltac interpret_rust_type_core lfts env ty := idtac.
Ltac interpret_rust_type_list lfts env tys :=
  match tys with
  | [] => exact +[]
  | ?ty :: ?tys =>
      refine (_ +:: _);
      [ interpret_rust_type_core lfts env ty
      | interpret_rust_type_list lfts env tys ]
  end.
Ltac interpret_rust_type_core lfts env ty ::=
  lazymatch ty with
  | RSTTyVar ?name =>
      let sty := eval vm_compute in (env !! name) in
      match sty with
      | Some (existT _ ?sty) =>
          exact sty
      | None =>
          fail 3 "Failed to find type variable " name " in the context"
      end
  | RSTLitType ?name ?apps =>
      (* interpret the arguments *)
      let Ha := fresh in
      refine (let Ha : hlist type _ := ltac:(interpret_rust_type_list lfts env apps) in _);
      let Hb := eval hnf in Ha in

      (* CAVEAT: This only works if a unique identifier can be found! *)
      lookup_definition
        ltac:(fun term =>
          let applied_term := apply_term_het_evar term Hb in
          exact applied_term
        )
        name || fail 1000 "definition lookup for " name " failed"
  | RSTInt ?it =>
      exact (int (IntType_to_it it))
  | RSTBool =>
      exact bool_t
  | RSTUnit =>
      exact unit_t
  | RSTStruct ?sls ?tys =>
      refine (struct_t sls ltac:(interpret_rust_type_list lfts env tys))
  | RSTArray ?len ?ty =>
      fail 2 "not implemented"
  | RSTRef ?mut ?κ ?ty =>
      (* TODO not great *)
      let κ := eval vm_compute in (lfts !! κ) in
      match κ with
      | Some ?κ =>
        match mut with
        | Mut =>
            refine (mut_ref _ κ); interpret_rust_type_core lfts env ty
        | Shr =>
            refine (shr_ref _ κ); interpret_rust_type_core lfts env ty
        end
      | None =>
          fail 3 "did not find lifetime"
      end
  end.
Tactic Notation "interpret_rust_type" constr(lfts) constr(env) constr(ty) :=
  interpret_rust_type_core lfts env ty .

Ltac solve_interpret_rust_type ::=
  match goal with
  | |- interpret_rust_type_pure_goal ?lfts ?st ?ty =>
      match goal with
      | H : TYVAR_MAP ?M |- _ =>
          let Hc := fresh in
          refine (let Hc := ltac:(interpret_rust_type lfts M st) in _);
          assert (ty = Hc) by reflexivity;
          exact I
      end
  end.


(** ** lifetime inclusion solver *)
(* relevant lemmas : lctx_lft_incl_refl, lctx_lft_incl_preorder  *)
(*
  Note: we _need_ to be able to deal with the case that the the lhs and rhs are intersections.
    (consider the case of subtyping annotations for instance)
    (but these intersections will always be intersections of "atomic" lifetimes or external lifetimes)

  strategy here: convert intersection to list of lifetimes.
  We need to dispatch all lifetimes on the RHS by finding a matching lifetime on the LHS, essentially.
  use the following rules in the given order:
   - if the LHS or RHS contains static, remove it [static is implicit]
   - if a LHS lifetime is also contained on the LHS, remove it from the LHS.
   - if there is a LHS lifetime on the LHS of a ⊑ₗ, remove it from the LHS and put the RHS of the inclusion there. [this is terminating since there are no cycles here, see below]
   - if there is a LHS lifetime on the LHS of a ⊑ₑ, put the RHS of the inclusion there, if it is not already there. [this ensures that we do not run into cycles]
   - fail with an error.

   [[[- if an RHS lifetime is on the RHS of a ⊑ₗ, reduce to the LHS. [problem: introduces a disjunction if there are multiple such inclusions.] ]]]

  alternative formulation of this:
    in a graph-based representation of the lifetimes, this question reduces to: is every conjunct of the RHS reachable from one conjunct of the LHS?
    but implementing that in a certified way seems quite annoying.
  -> can this graph have cycles?
      -> no for the local context. the atomic lifetimes in the local context should automatically break cycles.
      -> it can have cycles in the external context -> we must not carelessly propagate along external edges.


  Slightly problematic point here: lifetime intersection is not idempotent.
  this means: I cannot use the same element on the LHS twice.

  Note: this solver relies on the fact that each lifetime can only be contained once on the lhs in the local lifetime context.
*)

Section incl_tac.
  Context `{typeGS Σ}.
  Definition lctx_lft_incl_list (E : elctx) (L : llctx) (κs1 κs2 : list lft) :=
    lctx_lft_incl E L (lft_intersect_list κs1) (lft_intersect_list κs2).

  Lemma tac_lctx_lft_incl_init_list E L κ1 κ2 :
    lctx_lft_incl_list E L [κ1] [κ2] → lctx_lft_incl E L κ1 κ2.
  Proof.
    rewrite /lctx_lft_incl_list /=.
    by rewrite !lft_intersect_right_id.
  Qed.

  Lemma tac_lctx_lft_incl_list_nil_r E L κs1 :
    lctx_lft_incl_list E L κs1 [].
  Proof.
    rewrite /lctx_lft_incl_list /=.
    iIntros (?) "HL !> HE".
    iApply lft_incl_static.
  Qed.

  (* should be applied by automation only if κ2 cannot be decomposed further *)
  Lemma tac_lctx_lft_incl_list_intersect_l E L κ1 κ2 κs1 κs2 :
    lctx_lft_incl_list E L (κ1 :: κ2 :: κs1) κs2 →
    lctx_lft_incl_list E L (κ1 ⊓ κ2 :: κs1) κs2.
  Proof.
    rewrite /lctx_lft_incl_list /=.
    by rewrite lft_intersect_assoc.
  Qed.
  Lemma tac_lctx_lft_incl_list_intersect_r E L κ1 κ2 κs1 κs2 :
    lctx_lft_incl_list E L κs1 (κ1 :: κ2 :: κs2) →
    lctx_lft_incl_list E L κs1 (κ1 ⊓ κ2 :: κs2).
  Proof.
    rewrite /lctx_lft_incl_list /=.
    by rewrite lft_intersect_assoc.
  Qed.

  (* used for normalizing the head *)
  Lemma tac_lctx_lft_incl_list_head_assoc_l E L κ1 κ2 κ3 κs1 κs2 :
    lctx_lft_incl_list E L ((κ1 ⊓ κ2) ⊓ κ3 :: κs1) κs2 →
    lctx_lft_incl_list E L (κ1 ⊓ (κ2 ⊓ κ3) :: κs1) κs2.
  Proof. by rewrite lft_intersect_assoc. Qed.
  Lemma tac_lctx_lft_incl_list_head_assoc_r E L κ1 κ2 κ3 κs1 κs2 :
    lctx_lft_incl_list E L κs1 ((κ1 ⊓ κ2) ⊓ κ3 :: κs2) →
    lctx_lft_incl_list E L κs1 (κ1 ⊓ (κ2 ⊓ κ3) :: κs2).
  Proof. by rewrite lft_intersect_assoc. Qed.
  Lemma tac_lctx_lft_incl_list_head_static_l E L κ1 κs1 κs2 :
    lctx_lft_incl_list E L (κ1 :: κs1) κs2 →
    lctx_lft_incl_list E L (κ1 ⊓ static :: κs1) κs2.
  Proof. rewrite lft_intersect_right_id //. Qed.
  Lemma tac_lctx_lft_incl_list_head_static_r E L κ1 κs1 κs2 :
    lctx_lft_incl_list E L κs1 (κ1 :: κs2) →
    lctx_lft_incl_list E L κs1 (κ1 ⊓ static :: κs2).
  Proof. rewrite lft_intersect_right_id //. Qed.
  Lemma tac_lctx_lft_incl_list_static_l E L κs1 κs2 :
    lctx_lft_incl_list E L κs1 κs2 →
    lctx_lft_incl_list E L (static :: κs1) κs2.
  Proof. rewrite /lctx_lft_incl_list /= lft_intersect_left_id //. Qed.
  Lemma tac_lctx_lft_incl_list_static_r E L κs1 κs2 :
    lctx_lft_incl_list E L κs1 κs2 →
    lctx_lft_incl_list E L κs1 (static :: κs2).
  Proof. rewrite /lctx_lft_incl_list /= lft_intersect_left_id //. Qed.

  (* applied when a matching lifetime is found on left and right *)
  Lemma tac_lctx_lft_incl_list_dispatch_r E L i j κ κs1 κs2 :
    κs1 !! i = Some κ →
    κs2 !! j = Some κ →
    lctx_lft_incl_list E L (delete i κs1) (delete j κs2) →
    lctx_lft_incl_list E L κs1 κs2.
  Proof.
    rewrite /lctx_lft_incl_list /=.
    rewrite !delete_take_drop.
    intros H1 H2.
    rewrite -{3}(take_drop_middle κs1 _ _ H1).
    rewrite -{3}(take_drop_middle κs2 _ _ H2).
    rewrite !lft_intersect_list_app. simpl. intros Ha.
    rewrite !lft_intersect_assoc.
    rewrite ![lft_intersect_list _ ⊓ κ]lft_intersect_comm.
    rewrite -!lft_intersect_assoc.
    apply lctx_lft_incl_intersect; done.
  Qed.

  (* augment lhs with a local inclusion *)
  Lemma tac_lctx_lft_incl_list_augment_local_owned E L κs1 κs2 κ κs i j c :
    L !! j = Some (κ ⊑ₗ{c} κs) →
    κs1 !! i = Some κ →
    lctx_lft_incl_list E L (κs ++ delete i κs1) κs2 →
    lctx_lft_incl_list E L κs1 κs2.
  Proof.
    rewrite /lctx_lft_incl_list /=.
    rewrite !delete_take_drop.
    intros HL%elem_of_list_lookup_2 H1. rewrite -{3}(take_drop_middle κs1 _ _ H1).
    rewrite !lft_intersect_list_app. simpl. intros Ha.
    rewrite lft_intersect_assoc. rewrite [lft_intersect_list _ ⊓ κ]lft_intersect_comm.
    rewrite -lft_intersect_assoc.
    eapply lctx_lft_incl_local_owned_full; done.
  Qed.

  Lemma tac_lctx_lft_incl_list_augment_local_alias E L κs1 κs2 κ κs i j :
    L !! j = Some (κ ≡ₗ κs) →
    κs1 !! i = Some κ →
    lctx_lft_incl_list E L (κs ++ delete i κs1) κs2 →
    lctx_lft_incl_list E L κs1 κs2.
  Proof.
    rewrite /lctx_lft_incl_list /=.
    rewrite !delete_take_drop.
    intros HL%elem_of_list_lookup_2 H1. rewrite -{3}(take_drop_middle κs1 _ _ H1).
    rewrite !lft_intersect_list_app. simpl. intros Ha.
    rewrite lft_intersect_assoc. rewrite [lft_intersect_list _ ⊓ κ]lft_intersect_comm.
    rewrite -lft_intersect_assoc.
    eapply lctx_lft_incl_local_alias_full; done.
  Qed.

  (* For direct equivalences in the local context, just also rewrite on the RHS. *)
  Lemma tac_lctx_lft_incl_list_augment_local_alias_rhs E L κs1 κs2 κ κ' i j :
    L !! j = Some (κ ≡ₗ [κ']) →
    κs2 !! i = Some κ →
    lctx_lft_incl_list E L (κs1) (κ' :: delete i κs2) →
    lctx_lft_incl_list E L κs1 κs2.
  Proof.
    rewrite /lctx_lft_incl_list /=.
    rewrite !delete_take_drop.
    intros HL%elem_of_list_lookup_2 H1. rewrite -{3}(take_drop_middle κs2 _ _ H1).
    rewrite !lft_intersect_list_app. simpl. intros Ha.
    rewrite lft_intersect_assoc. rewrite [lft_intersect_list _ ⊓ κ]lft_intersect_comm.
    rewrite -lft_intersect_assoc.
    etrans; first apply Ha.
    eapply lctx_lft_incl_intersect; last done.
    eapply lctx_lft_incl_local_alias_reverse; [done.. | ].
    simpl. rewrite right_id. done.
  Qed.

  (* augment lhs with an external inclusion *)
  Lemma tac_lctx_lft_incl_list_augment_external E L κ1 κ2 κs1 κs2 i :
    (κ1 ⊑ₑ κ2) ∈ E →
    κs1 !! i = Some κ1 →
    lctx_lft_incl_list E L (κ2 :: delete i κs1) κs2 →
    lctx_lft_incl_list E L κs1 κs2.
  Proof.
    rewrite /lctx_lft_incl_list /=.
    rewrite !delete_take_drop.
    intros HE H1. rewrite -{3}(take_drop_middle κs1 _ _ H1).
    rewrite !lft_intersect_list_app. simpl. intros Ha.
    rewrite lft_intersect_assoc. rewrite [lft_intersect_list _ ⊓ κ1]lft_intersect_comm.
    rewrite -lft_intersect_assoc.
    eapply lctx_lft_incl_external_full; done.
  Qed.

  (*Lemma tac_lctx_lft_incl_list_augment_external E L κ1 κs κs1 κs2 i j :*)
    (*E !! j = Some (κ1 ⊑ₑ κs) →*)
    (*κs1 !! i = Some κ1 →*)
    (*lctx_lft_incl_list E L (κs ++ delete i κs1) κs2 →*)
    (*lctx_lft_incl_list E L κs1 κs2.*)
  (*Proof.*)
    (*rewrite /lctx_lft_incl_list /=.*)
    (*rewrite !delete_take_drop.*)
    (*intros HE%elem_of_list_lookup_2 H1. rewrite -{3}(take_drop_middle κs1 _ _ H1).*)
    (*rewrite !foldr_app. simpl. intros Ha.*)
    (*rewrite foldr_lft_intersect_shift_eq.*)
    (*rewrite -lft_intersect_assoc. rewrite -foldr_lft_intersect_shift_eq.*)
    (*eapply lctx_lft_incl_external_full; first done.*)
    (*revert Ha.*)
    (*rewrite foldr_lft_intersect_shift_eq.*)
    (*rewrite lft_intersect_comm. done.*)
  (*Qed.*)

End incl_tac.

(* Execute an ltac tactical [cont] for each element of a list [l].
  [cont] gets the elements of the list as argument.
  Breaks if [cont] succeeds.
 *)
Ltac list_find_tac' cont l i :=
  match l with
  | [] => fail
  | ?h :: ?l => first [cont i h | list_find_tac' cont l constr:(S i)]
  end.
Ltac list_find_tac cont l := list_find_tac' cont l constr:(0).

Ltac list_find_tac_noindex' cont l :=
  match l with
  | [] => fail
  | ?h :: ?l => first [cont h | list_find_tac_noindex' cont l]
  | _ ++ ?l => list_find_tac_noindex' cont l
  end.
Ltac list_find_tac_noindex cont l := list_find_tac_noindex' cont l.

(* Very simple list containment solver, tailored for the goals we usually get around external lifetime contexts. *)
Ltac elctx_list_elem_solver :=
  repeat lazymatch goal with
  | |- ?a ∈ ?a :: ?L =>
      apply elem_of_cons; by left
  | |- ?a ∈ _ :: ?L =>
      apply elem_of_cons; right
  | |- ?a ∈ _ ++ ?L =>
      apply elem_of_app; right
  end.

(** Basic algorithm: Want to eliminate the RHS to [], so that the inclusion to [static] holds trivially.
  For that, expand inclusions on the LHS, until we can eliminate one lifetime on the RHS *)
Ltac solve_lft_incl_list_step :=
  match goal with
  (* normalize the head if it is an intersection *)
  | |- lctx_lft_incl_list ?E ?L ((?κ1 ⊓ (?κ2 ⊓ ?κ3)) :: ?κs1) ?κs2 =>
      notypeclasses refine (tac_lctx_lft_incl_list_head_assoc_l E L _ _ _ κs1 κs2 _)
  | |- lctx_lft_incl_list ?E ?L ?κs1 ((?κ1 ⊓ (?κ2 ⊓ ?κ3)) :: ?κs2) =>
      notypeclasses refine (tac_lctx_lft_incl_list_head_assoc_r E L _ _ _ κs1 κs2 _)
  (* remove the atomic rhs static of an intersection *)
  | |- lctx_lft_incl_list ?E ?L (?κ1 ⊓ static :: ?κs1) ?κs2 =>
      notypeclasses refine (tac_lctx_lft_incl_list_head_static_l E L _ κs1 κs2 _)
  | |- lctx_lft_incl_list ?E ?L ?κs1 (?κ1 ⊓ static :: ?κs2) =>
      notypeclasses refine (tac_lctx_lft_incl_list_head_static_r E L _ κs1 κs2 _)
  (* shift the atomic rhs conjunct of an intersection *)
  | |- lctx_lft_incl_list ?E ?L (?κ1 ⊓ ?κ2 :: ?κs1) ?κs2 =>
      is_var κ2;
      notypeclasses refine (tac_lctx_lft_incl_list_intersect_l E L _ _ κs1 κs2 _)
  | |- lctx_lft_incl_list ?E ?L ?κs1 (?κ1 ⊓ ?κ2 :: ?κs2) =>
      is_var κ2;
      notypeclasses refine (tac_lctx_lft_incl_list_intersect_r E L _ _ κs1 κs2 _)
  (* eliminate static at the head *)
  | |- lctx_lft_incl_list ?E ?L (static :: ?κs1) ?κs2 =>
      notypeclasses refine (tac_lctx_lft_incl_list_static_l E L κs1 κs2 _)
  | |- lctx_lft_incl_list ?E ?L ?κs1 (static :: ?κs2) =>
      notypeclasses refine (tac_lctx_lft_incl_list_static_r E L κs1 κs2 _)
  (* goal is solved if RHS is empty *)
  | |- lctx_lft_incl_list ?E ?L ?κs1 [] =>
      notypeclasses refine (tac_lctx_lft_incl_list_nil_r E L κs1)

  (* Normalize a direct local equivalence [κ ≡ₗ [κ']] on the RHS *)
  (* TODO this is a hack and doesn't work in all cases, because we don't use any other (external) inclusions on the RHS.
      Really, the proper way to do this would be to eliminate all such equivalences before starting the solver on a normalized goal + lifetime context. *)
  | |- lctx_lft_incl_list ?E ?L ?κs1 ?κs2 =>
      let find_in_llctx := fun j κ =>
        list_find_tac ltac:(fun i el =>
          match el with
          | κ ≡ₗ [?κ'] =>
              notypeclasses refine (tac_lctx_lft_incl_list_augment_local_alias_rhs E L κs1 κs2 κ κ' j i _ _ _);
              [ reflexivity | reflexivity | simpl ]
          | _ => fail
          end
        ) L
      in
      list_find_tac find_in_llctx κs2

  (* eliminate a lifetime on the RHS that also occurs on the LHS *)
  | |- lctx_lft_incl_list ?E ?L ?κs1 ?κs2 =>
      let check_equality := fun j κ2 => ltac:(fun i κ1 =>
        first [unify κ1 κ2;
          notypeclasses refine (tac_lctx_lft_incl_list_dispatch_r E L i j κ1 κs1 κs2 _ _ _);
            [reflexivity | reflexivity | simpl ]
        | fail ]
      ) in
      let check_left := (fun j κ2 => list_find_tac ltac:(check_equality j κ2) κs1) in
      list_find_tac check_left κs2

  (* Expand a local lifetime on the LHS *)
  | |- lctx_lft_incl_list ?E ?L ?κs1 ?κs2 =>
      let find_in_llctx := fun j κ =>
        list_find_tac ltac:(fun i el =>
          match el with
          | κ ⊑ₗ{_} ?κs =>
              (* only do this if the RHS is non-empty---otherwise, this cannot serve to make progress *)
              assert_fails (unify κs (@nil lft));
              notypeclasses refine (tac_lctx_lft_incl_list_augment_local_owned E L κs1 κs2 κ κs j i _ _ _ _);
              [ reflexivity | reflexivity | simpl ]
          | κ ≡ₗ ?κs =>
              (* only do this if the RHS is non-empty---otherwise, this cannot serve to make progress *)
              assert_fails (unify κs (@nil lft));
              notypeclasses refine (tac_lctx_lft_incl_list_augment_local_alias E L κs1 κs2 κ κs j i _ _ _);
              [ reflexivity | reflexivity | simpl ]
          | _ => fail
          end
        ) L
      in
      list_find_tac find_in_llctx κs1


  (* expand an external lifetime on the LHS *)
  (* TODO: we cannot always make this expansion safely and may need backtracking (there might be multiple possible expansions);
      alternatively, think about representing the elctx similar to llctx (with unique LHS).
      [works, but would cause problems in the procedure for lctx_lft_alive below...]
    also, this might loop, since there can be cycles in the elctx. we need to keep track of that.
  *)
  | |- lctx_lft_incl_list ?E ?L ?κs1 ?κs2 =>
      let find_in_elctx := fun j κ =>
        list_find_tac_noindex ltac:(fun el =>
          match el with
          | κ ⊑ₑ ?κ' =>
              notypeclasses refine (tac_lctx_lft_incl_list_augment_external E L κ κ' κs1 κs2 j _ _ _);
              [ elctx_list_elem_solver | reflexivity | simpl ]
          | _ => fail
          end
        ) E
      in
      list_find_tac find_in_elctx κs1
  end.
Ltac solve_lft_incl_list := repeat solve_lft_incl_list_step.
Ltac solve_lft_incl :=
  match goal with
  | |- lctx_lft_incl ?E ?L ?κ1 ?κ2 =>
      first [unify κ1 κ2; refine (lctx_lft_incl_refl E L κ1) |
            refine (tac_lctx_lft_incl_init_list E L κ1 κ2 _);
            solve_lft_incl_list
            ]
  end.

(** lifetime alive solver *)
(*
  desired invariant:
  - every lifetime on the lhs of ⊑ₗ should be alive (because we should end lifetimes in a well-nested way, ending (and removing) shorter lifetimes first.
    -> if we can find a lifetime on the lhs in the local context, it should always be safe to apply [lctx_lft_alive_local] and reduce to smaller subgoals.
  - if a lifetime is external, it should be alive, because it outlives the local function lifetime, which should always be in the local context.
    -> if we can find a lifetime on the RHS of a ⊑ₑ, it should always be safe to apply [lctx_lft_alive_external]
  - for intersections, we should split to both sides. This should always be safe as the lifetime contexts should only contain atoms on the LHS.
 *)

Section alive_tac.
  Context `{typeGS Σ}.


  Lemma tac_lctx_lft_alive_intersect E L κ κ' :
    lctx_lft_alive E L κ →
    lctx_lft_alive E L κ' →
    lctx_lft_alive E L (κ ⊓ κ').
  Proof. apply lctx_lft_alive_intersect. Qed.

  Lemma tac_lctx_lft_alive_local_owned E L κ κs i c :
    L !! i = Some (κ ⊑ₗ{c} κs) →
    Forall_cb (lctx_lft_alive E L) κs →
    lctx_lft_alive E L κ.
  Proof.
    intros ?%elem_of_list_lookup_2 ?%Forall_Forall_cb.
    by eapply lctx_lft_alive_local_owned.
  Qed.

  Lemma tac_lctx_lft_alive_local_alias E L κ κs i :
    L !! i = Some (κ ≡ₗ κs) →
    Forall_cb (lctx_lft_alive E L) κs →
    lctx_lft_alive E L κ.
  Proof.
    intros ?%elem_of_list_lookup_2 ?%Forall_Forall_cb.
    by eapply lctx_lft_alive_local_alias.
  Qed.

  (* This weakens the elctx by removing the inclusion we used.
    This should ensure termination of the solver without making goals unprovable.
    (once we need to prove liveness of an external lifetime, the only local lifetime we should
      need is ϝ)
  *)
  Lemma tac_lctx_lft_alive_external E L κ κ' i :
    E !! i = Some (κ' ⊑ₑ κ) →
    lctx_lft_alive (delete i E) L κ' →
    lctx_lft_alive E L κ.
  Proof.
    intros ?%elem_of_list_lookup_2 H'.
    eapply lctx_lft_alive_external; first done.
    iIntros (F ??) "#HE HL".
    iApply H'; [ done | | done].
    iApply (big_sepL_submseteq with "HE").
    apply submseteq_delete.
  Qed.
End alive_tac.

Ltac solve_lft_alive :=
  repeat match goal with
  | |- Forall (lctx_lft_alive ?E ?L) ?κs =>
      notypeclasses refine (proj2 (Forall_Forall_cb _ _) _);
        simpl; first [exact I | split_and! ]
  | |- lctx_lft_alive ?E ?L static =>
      notypeclasses refine (lctx_lft_alive_static E L)
  | |- lctx_lft_alive ?E ?L (?κ ⊓ ?κ') =>
      notypeclasses refine (tac_lctx_lft_alive_intersect _ _ _ _ _ _);
        [solve_lft_alive | solve_lft_alive]
  | |- lctx_lft_alive ?E ?L ?κ =>
      list_find_tac ltac:(fun i el =>
        match el with
        | κ ⊑ₗ{_} ?κs =>
            notypeclasses refine (tac_lctx_lft_alive_local_owned E L κ κs i _ _ _);
              [ reflexivity | simpl; first [exact I | split_and! ] ]
        | κ ≡ₗ ?κs =>
            notypeclasses refine (tac_lctx_lft_alive_local_alias E L κ κs i _ _);
              [ reflexivity | simpl; first [exact I | split_and! ] ]
        | _ => fail
        end) L
  | |- lctx_lft_alive ?E ?L ?κ =>
      list_find_tac ltac:(fun i el =>
        match el with
        | ?κ' ⊑ₑ κ =>
            notypeclasses refine (tac_lctx_lft_alive_external E L κ κ' i _ _);
            [reflexivity | simpl; solve[solve_lft_alive]]
        | _ => fail
        end) E
  end; fast_done.

(** simplify_elctx *)

Global Arguments ty_lfts : simpl never.
Global Arguments ty_wf_E : simpl never.
Global Arguments ty_outlives_E : simpl never.
(*Global Arguments tyl_outlives_E : simpl never.*)
(*Global Arguments tyl_wf_E : simpl never.*)

(* Otherwise [simpl] will unfold too much despite [simpl never], breaking the solver *)
Global Opaque ty_outlives_E.

Section tac.
  Context `{!typeGS Σ}.
  Lemma simplify_app_head_tac (E1 E1' E2 E : elctx) :
    E1 = E1' →
    E1' ++ E2 = E →
    E1 ++ E2 = E.
  Proof.
    intros <- <-. done.
  Qed.

  Lemma simplify_app_head_init_tac (E E' : elctx) :
    E ++ [] = E' →
    E = E'.
  Proof.
    rewrite app_nil_r. done.
  Qed.

  Lemma lfts_outlives_cons κ1 κs2 κ :
    lfts_outlives_E (κ1 :: κs2) κ = lfts_outlives_E [κ1] κ ++ lfts_outlives_E κs2 κ.
  Proof.
    rewrite /lfts_outlives_E fmap_cons//.
  Qed.
  Lemma lfts_outlives_app κs1 κs2 κ :
    lfts_outlives_E (κs1 ++ κs2) κ = lfts_outlives_E κs1 κ ++ lfts_outlives_E κs2 κ.
  Proof.
    rewrite /lfts_outlives_E fmap_app//.
  Qed.
  Lemma lfts_outlives_nil κ :
    lfts_outlives_E [] κ = [].
  Proof. done. Qed.
  Lemma lfts_outlives_singleton κ2 κ :
    lfts_outlives_E [κ2] κ = [κ ⊑ₑ κ2].
  Proof. done. Qed.
  Lemma ty_outlives_E_eq {rt} (ty : type rt) κ :
    ty_outlives_E ty κ = lfts_outlives_E (ty_lfts ty) κ.
  Proof.
    unfold_opaque @ty_outlives_E. done.
  Qed.
End tac.

Ltac simplify_elctx_subterm :=
  match goal with
  | |- ty_wf_E ?ty = _ =>
      assert_fails (is_var ty);
      rewrite [ty_wf_E ty]/ty_wf_E/=;
      cbn;
      reflexivity
      (*autounfold with tyunfold; cbn*)
  | |- ty_outlives_E ?ty _ = _ =>
      assert_fails (is_var ty);
      unfold_opaque (@ty_outlives_E);
      rewrite [ty_outlives_E ty]/ty_outlives_E/=;
      first [rewrite lfts_outlives_app | autounfold with tyunfold; rewrite /ty_lfts ]; cbn;
      reflexivity
  | |- lfts_outlives_E (ty_lfts ?ty) _ = _ =>
      (*(is_var ty);*)
      (*rewrite [ty_outlives_E ty]/ty_outlives_E/=;*)
      first [is_var ty | rewrite lfts_outlives_app | autounfold with tyunfold; rewrite /ty_lfts ]; cbn;
      reflexivity
  | |- lfts_outlives_E [?κ2] _ = _ =>
      rewrite lfts_outlives_singleton;
      reflexivity
  | |- lfts_outlives_E (?κs1 ++ ?κs2) _ = _ =>
      (*assert_fails (is_var κs);*)
      rewrite lfts_outlives_app; cbn;
      reflexivity
  | |- lfts_outlives_E (?κ1 :: ?κs2) _ = _ =>
      (*assert_fails (is_var κs);*)
      rewrite lfts_outlives_cons; cbn;
      reflexivity
  (*| |- lfts_outlives_E (ty_lfts ?ty) _ = _ =>*)
      (*idtac*)
  end.

Ltac simplify_elctx_step :=
cbn;
rewrite -?app_assoc;
match goal with
| |- ty_wf_E ?ty ++ _ = _ =>
    assert_fails (is_var ty);
    refine (simplify_app_head_tac _ _ _ _ _ _);
    [ simplify_elctx_subterm | ]
| |- ty_wf_E ?ty ++ _ = _ =>
    is_var ty; f_equiv
| |- ty_outlives_E ?ty _ ++ _ = _ =>
    assert_fails (is_var ty);
    unfold_opaque (@ty_outlives_E);
    refine (simplify_app_head_tac _ _ _ _ _ _);
    [ simplify_elctx_subterm | ]
| |- ty_outlives_E ?ty _ ++ _ = _ =>
    is_var ty; f_equiv
| |- lfts_outlives_E (ty_lfts ?T) ?κ ++ _ = _ =>
    is_var T;
    (*fold (ty_outlives_E T κ);*)
    rewrite -(ty_outlives_E_eq T κ);
    f_equiv
| |- lfts_outlives_E [] _ ++ _ = _ =>
    rewrite lfts_outlives_nil
| |- lfts_outlives_E ?κs _ ++ _ = _ =>
    assert_fails (is_var κs);
    refine (simplify_app_head_tac _ _ _ _ _ _);
    [ simplify_elctx_subterm | ]
| |- _ :: _ = _ =>
    f_equiv
| |- [] = _ =>
    reflexivity
end.

Ltac simplify_elctx :=
  match goal with
  | |- ?E = ?E' =>
    is_evar E';
    (* Unfold here. Important: do not use [simpl] after that, because it will unfold too much so that stuff breaks. *)
    (*unfold_opaque (@ty_outlives_E);*)
    cbn;
    refine (simplify_app_head_init_tac _ _ _);
    rewrite -?app_assoc;
    repeat simplify_elctx_step
  end.

(** Reordering an [elctx] so that all the opaque inclusions from generics are at the tail,
   while directly known inclusions appear at the head. This makes life easier for the lifetime solvers. *)
Section reorder_elctx.
  Context `{!typeGS Σ}.

  Lemma reorder_elctx_tac π E E' L s fn R ϝ :
    E ≡ₚ E' →
    typed_stmt π (E') L s fn R ϝ -∗
    typed_stmt π E L s fn R ϝ.
  Proof.
    iIntros (HP) "Hs".
    rewrite /typed_stmt.
    iIntros (?) "#CTX #HE HL Hcont".
    iApply ("Hs" with "CTX [] HL Hcont").
    iApply elctx_interp_permut; done.
  Qed.

  Lemma reorder_elctx_init_tac (E E0 E' E'' : elctx) :
    E ≡ₚ E' ++ E'' →
    E0 = E' ++ E'' →
    E ≡ₚ E0.
  Proof.
    intros -> ->. done.
  Qed.

  Lemma reorder_elctx_shuffle_left_tac E E' E1' E'' κ1 κ2 :
    E' = (κ1 ⊑ₑ κ2) :: E1' →
    E ≡ₚ E1' ++ E'' →
    (κ1 ⊑ₑ κ2) :: E ≡ₚ E' ++ E''.
  Proof.
    intros -> Hp. simpl. f_equiv. done.
  Qed.

  Lemma reorder_elctx_shuffle_right_tac (E E' E1'' E'' E0 : elctx) :
    E'' = E0 ++ E1'' →
    E ≡ₚ E' ++ E1'' →
    E0 ++ E ≡ₚ E' ++ E''.
  Proof.
    intros -> ->.
    rewrite [E0 ++ _]assoc [E0 ++ _]comm - [(E' ++ E0) ++ E1'']assoc.
    done.
  Qed.
End reorder_elctx.

(** The invariant is that we shuffle all the opaque parts into [E''],
  while the concrete parts get shuffled into [E']. *)
Ltac reorder_elctx_step :=
  match goal with
  | |- ?E ≡ₚ ?E' ++ ?E'' =>
      match E with
      | _ :: ?E =>
          refine (reorder_elctx_shuffle_left_tac E E' _ E'' _ _ _ _);
          [reflexivity | ]
      | ?E0 ++ ?E =>
          refine (reorder_elctx_shuffle_right_tac E E' _ E'' E0 _ _);
          [reflexivity | ]
      | [] => unify E' ([] : elctx); unify E'' ([] : elctx); reflexivity
      | ?E =>
          unify E' ([] : elctx); unify E'' (E); reflexivity
      end
  end.

Ltac reorder_elctx :=
  match goal with
  | |- ?E ≡ₚ ?E' =>
      is_evar E';
      refine (reorder_elctx_init_tac E E' _ _ _ _);
      [ solve [repeat reorder_elctx_step]
      | rewrite ?app_nil_r; reflexivity ]
  end.

(** elctx_sat solver *)
Section elctx_sat.
  Context `{typeGS Σ}.

  Lemma tac_elctx_sat_cons_r E E' L κ κ' i :
    E !! i = Some (κ ⊑ₑ κ') →
    elctx_sat E L (E') →
    elctx_sat E L ((κ ⊑ₑ κ') :: E').
  Proof.
    intros ?%elem_of_list_lookup_2 Hr.
    eapply (elctx_sat_app _ _ [_]); last done.
    eapply elctx_sat_submseteq.
    by apply singleton_submseteq_l.
  Qed.

  Lemma tac_elctx_sat_simpl E1 E2 L E1' E2' :
    (E1 = E1') →
    (E2 = E2') →
    elctx_sat E1' L E2' →
    elctx_sat E1 L E2.
  Proof.
    intros -> ->. done.
  Qed.

  Lemma tac_elctx_app_ty_wf_E E1 L {rt} (ty : type rt) :
    ty_wf_E ty ⊆+ E1 →
    elctx_sat E1 L (ty_wf_E ty).
  Proof.
    intros Hsub Hsat.
    apply elctx_sat_submseteq; done.
  Qed.

  Lemma tac_elctx_app_ty_outlives_E E1 L κ κ' {rt} (ty : type rt) :
    ty_outlives_E ty κ' ⊆+ E1 →
    lctx_lft_incl E1 L κ κ' →
    elctx_sat E1 L (ty_outlives_E ty κ).
  Proof.
    intros Houtl Hincl.
    eapply (elctx_sat_submseteq _ _ L) in Houtl.
    iIntros (qL) "HL".
    iPoseProof (Hincl with "HL") as "#Hincl".
    iPoseProof (Houtl with "HL") as "#Houtl".
    iModIntro. iIntros "#HE".
    iPoseProof ("Hincl" with "HE") as "Hincl'".
    iPoseProof ("Houtl" with "HE") as "Houtl'".
    iClear "Hincl Houtl HE".
    unfold_opaque @ty_outlives_E.
    rewrite /ty_outlives_E /lfts_outlives_E.
    generalize (ty_lfts ty) => κs. clear.
    iInduction κs as [ | κ0 κs] "IH"; simpl; first done.
    rewrite /elctx_interp. simpl.
    iDestruct "Houtl'" as "(Ha & Houtl)".
    iPoseProof ("IH" with "Houtl") as "$".
    rewrite /elctx_elt_interp/=.
    iApply lft_incl_trans; done.
  Qed.

  Lemma tac_submseteq_skip_app_r {A} (K E0 E1 : list A) :
    K ⊆+ E1 →
    K ⊆+ (E0 ++ E1).
  Proof.
    intros ?. apply submseteq_app_r.
    exists [], K. split_and!; [done | | done].
    apply submseteq_nil_l.
  Qed.

  Lemma tac_submseteq_find_app_r {A} (K E0 E1 : list A) :
    K = E0 →
    K ⊆+ (E0 ++ E1).
  Proof.
    intros ->. apply submseteq_app_r.
    eexists E0, []. rewrite app_nil_r.
    split_and!; [done.. | ]. apply submseteq_nil_l.
  Qed.

  Lemma tac_submseteq_init {A} (K E : list A) :
    K ⊆+ E ++ [] →
    K ⊆+ E.
  Proof.
    rewrite app_nil_r//.
  Qed.
End elctx_sat.

Ltac solve_elctx_submseteq_step :=
  simpl;
  lazymatch goal with
  | |- _ ⊆+ _ :: _ =>
      notypeclasses refine (submseteq_cons _ _ _ _)
  | |- _ ⊆+ (_ ++ _) ++ _ =>
      rewrite -app_assoc
  | |- ty_outlives_E ?ty ?κ ⊆+ (ty_outlives_E ?ty' ?κ') ++ ?E =>
      first [
        unify ty ty';
        notypeclasses refine (tac_submseteq_find_app_r _ _ _ _); reflexivity
      | notypeclasses refine (tac_submseteq_skip_app_r  _ _ _ _)
      ]
  | |- ty_wf_E ?ty ⊆+ (ty_wf_E ?ty') ++ ?E =>
      first [
        unify ty ty';
        notypeclasses refine (tac_submseteq_find_app_r _ _ _ _); reflexivity
      | notypeclasses refine (tac_submseteq_skip_app_r  _ _ _ _)
      ]
  | |- _ ⊆+ _ ++ _ =>
        notypeclasses refine (tac_submseteq_skip_app_r _ _ _ _)
  end.
Ltac solve_elctx_submseteq :=
  notypeclasses refine (tac_submseteq_init _ _ _);
  repeat solve_elctx_submseteq_step.

Ltac solve_elctx_sat_step :=
  match goal with
  | |- elctx_sat ?E ?L [] =>
      notypeclasses refine (elctx_sat_nil _ _)
  | |- elctx_sat ?E ?L ?E =>
      notypeclasses refine (elctx_sat_refl _ _)
  | |- elctx_sat ?E ?L (?E1 ++ ?E2) =>
      notypeclasses refine (elctx_sat_app E L E1 E2 _ _)
  (* dispatch as many elements as possible via direct inclusion *)
  | |- elctx_sat ?E ?L ((?κ ⊑ₑ ?κ') :: ?E') =>
      list_find_tac ltac:(fun i el =>
        match el with
        | (κ ⊑ₑ κ') =>
            notypeclasses refine (tac_elctx_sat_cons_r E L κ κ' i _ _);
            [reflexivity | ]
        | _ => fail
        end) E
  (* dispatch remaining elements via lifetime inclusion solving *)
  | |- elctx_sat ?E ?L ((?κ ⊑ₑ ?κ') :: ?E') =>
        notypeclasses refine (elctx_sat_lft_incl E L E' κ κ' _ _);
        [solve_lft_incl | ]
  (* dispatch assumptions for generic type parameters *)
  | |- elctx_sat ?E ?L (ty_wf_E ?ty) =>
      notypeclasses refine (tac_elctx_app_ty_wf_E E L ty _);
      solve_elctx_submseteq
  | |- elctx_sat ?E ?L (ty_outlives_E ?ty ?κ) =>
      notypeclasses refine (tac_elctx_app_ty_outlives_E E L κ _ ty _ _);
      [ solve_elctx_submseteq | solve_lft_incl ]
  end.

Ltac solve_elctx_sat :=
  (* first unfold stuff is commonly included in these conditions *)
  (*let esimpl := (unfold ty_outlives_E, tyl_outlives_E; simpl; notypeclasses refine eq_refl) in*)
  lazymatch goal with
  | |- elctx_sat ?E ?L ?E' =>
      notypeclasses refine (tac_elctx_sat_simpl _ _ _ _ _ _ _ _);
      [ simplify_elctx | simplify_elctx | ]
  end;
  repeat solve_elctx_sat_step
  .

(** lctx_bor_kind_alive solver *)
Section bor_kind_alive_tac.
  Context `{typeGS Σ}.

  Lemma tac_lctx_bor_kind_alive_simpl E L b b' :
    (∀ (b'':=b'), b = b'') →
    lctx_bor_kind_alive E L b' →
    lctx_bor_kind_alive E L b.
  Proof.
    intros ->. done.
  Qed.

  Lemma tac_lctx_bor_kind_alive_shared E L κ:
    lctx_lft_alive E L κ →
    lctx_bor_kind_alive E L (Shared κ).
  Proof. done. Qed.

  Lemma tac_lctx_bor_kind_alive_uniq E L κ γ :
    lctx_lft_alive E L κ →
    lctx_bor_kind_alive E L (Uniq κ γ).
  Proof. done. Qed.

  Lemma tac_lctx_bor_kind_alive_owned E L wl :
    lctx_bor_kind_alive E L (Owned wl).
  Proof. done. Qed.
End bor_kind_alive_tac.

Global Arguments lctx_bor_kind_alive : simpl never.
Ltac solve_bor_kind_alive :=
  (* first compute [bor_kind_min] *)
  let simp_min := let x := fresh in intros x; unfold bor_kind_min; simpl; unfold x; notypeclasses refine eq_refl in
  match goal with
  | |- lctx_bor_kind_alive ?E ?L ?b =>
      refine (tac_lctx_bor_kind_alive_simpl _ _ _ _ _ _);
      [ simp_min
      | ]
  | |- _ =>
      fail 1000 "solve_bor_kind_alive: not an lctx_bor_kind_alive"
  end;
  match goal with
  | |- lctx_bor_kind_alive ?E ?L (Uniq _ _) =>
      refine (tac_lctx_bor_kind_alive_uniq _ _ _ _ _); [solve_lft_alive]
  | |- lctx_bor_kind_alive ?E ?L (Shared _) =>
      refine (tac_lctx_bor_kind_alive_shared _ _ _ _); [solve_lft_alive]
  | |- lctx_bor_kind_alive ?E ?L (Owned _) =>
      refine (tac_lctx_bor_kind_alive_owned _ _ _); solve[fail]
  | |- lctx_bor_kind_alive _ _ _ =>
      fail 1000 "solve_bor_kind_alive: cannot determine bor_kind shape"
  end.

(** lctx_bor_kind_incl solver *)
(* this essentially reduces to solve_lft_incl *)
Section bor_kind_incl_tac.
  Context `{typeGS Σ}.

  Lemma tac_lctx_bor_kind_incl_simpl E L b1 b1' b2 b2' :
    (∀ (b1'':=b1'), b1 = b1'') →
    (∀ (b2'':=b2'), b2 = b2'') →
    lctx_bor_kind_incl E L b1' b2' →
    lctx_bor_kind_incl E L b1 b2.
  Proof.
    intros -> ->. done.
  Qed.

  Lemma tac_lctx_bor_kind_incl_any_owned E L b wl :
    lctx_bor_kind_incl E L b (Owned wl).
  Proof.
    iIntros (?) "HL !> HE". destruct b; done.
  Qed.

  Lemma tac_lctx_bor_kind_incl_uniq_uniq E L κ γ κ' γ' :
    lctx_lft_incl E L κ κ' →
    lctx_bor_kind_incl E L (Uniq κ γ) (Uniq κ' γ').
  Proof.
    iIntros (Hincl ?) "HL". iPoseProof (Hincl with "HL") as "#Hincl".
    iIntros "!> HE". iDestruct ("Hincl" with "HE") as "#Hincl'".
    done.
  Qed.

  Lemma tac_lctx_bor_kind_incl_uniq_shared E L κ γ κ' :
    lctx_lft_incl E L κ κ' →
    lctx_bor_kind_incl E L (Uniq κ γ) (Shared κ').
  Proof.
    iIntros (Hincl ?) "HL". iPoseProof (Hincl with "HL") as "#Hincl".
    iIntros "!> HE". iDestruct ("Hincl" with "HE") as "#Hincl'".
    done.
  Qed.

  Lemma tac_lctx_bor_kind_incl_shared_shared E L κ κ' :
    lctx_lft_incl E L κ κ' →
    lctx_bor_kind_incl E L (Shared κ) (Shared κ').
  Proof.
    iIntros (Hincl ?) "HL". iPoseProof (Hincl with "HL") as "#Hincl".
    iIntros "!> HE". iDestruct ("Hincl" with "HE") as "#Hincl'".
    done.
  Qed.
End bor_kind_incl_tac.
Ltac solve_bor_kind_incl :=
  (* first compute [bor_kind_min] *)
  let simp_min := let x := fresh in intros x; unfold bor_kind_min; simpl; unfold x; notypeclasses refine eq_refl in
  match goal with
  | |- lctx_bor_kind_incl ?E ?L ?b1 ?b2 =>
      refine (tac_lctx_bor_kind_incl_simpl _ _ _ _ _ _ _ _ _);
      [ simp_min
      | simp_min
      | ]
  | |- _ =>
      fail 1000 "solve_bor_kind_incl: not an lctx_bor_kind_incl"
  end;
  match goal with
  | |- lctx_bor_kind_incl ?E ?L _ (Owned _) =>
      refine (tac_lctx_bor_kind_incl_any_owned _ _ _ _); solve[fail]
  | |- lctx_bor_kind_incl ?E ?L (Uniq _ _) (Uniq _ _) =>
      refine (tac_lctx_bor_kind_incl_uniq_uniq _ _ _ _ _ _ _); [solve_lft_incl]
  | |- lctx_bor_kind_incl ?E ?L (Uniq _ _) (Shared _) =>
      refine (tac_lctx_bor_kind_incl_uniq_shared _ _ _ _ _ _); [solve_lft_incl]
  | |- lctx_bor_kind_incl ?E ?L (Shared _) (Shared _) =>
      refine (tac_lctx_bor_kind_incl_shared_shared _ _ _ _ _); [solve_lft_incl]
  | |- lctx_bor_kind_incl ?E ?L ?b1 ?b2 =>
      fail 1000 "solve_bor_kind_incl: unable to solve inclusion"
  end.

(** llctx_bor_kind_direct_incl solver *)
Section bor_kind_direct_incl_tac.
  Context `{typeGS Σ}.

  Lemma tac_lctx_bor_kind_direct_incl_simpl E L b1 b2 b1' b2' :
    (∀ (b1'':=b1'), b1 = b1'') →
    (∀ (b2'':=b2'), b2 = b2'') →
    lctx_bor_kind_direct_incl E L b1' b2' →
    lctx_bor_kind_direct_incl E L b1 b2.
  Proof.
    intros -> ->. done.
  Qed.

  Lemma tac_lctx_bor_kind_direct_incl_owned_owned E L wl :
    lctx_bor_kind_direct_incl E L (Owned wl) (Owned wl).
  Proof.
    iIntros (?) "HL !> HE". done.
  Qed.

  Lemma tac_lctx_bor_kind_direct_incl_uniq_uniq E L κ γ κ' :
    lctx_lft_incl E L κ κ' →
    lctx_bor_kind_direct_incl E L (Uniq κ γ) (Uniq κ' γ).
  Proof.
    iIntros (Hincl ?) "HL". iPoseProof (Hincl with "HL") as "#Hincl".
    iIntros "!> HE". iDestruct ("Hincl" with "HE") as "#Hincl'".
    iSplitR; done.
  Qed.

  Lemma tac_lctx_bor_kind_direct_incl_shared_shared E L κ κ' :
    lctx_lft_incl E L κ κ' →
    lctx_bor_kind_direct_incl E L (Shared κ) (Shared κ').
  Proof.
    iIntros (Hincl ?) "HL". iPoseProof (Hincl with "HL") as "#Hincl".
    iIntros "!> HE". iDestruct ("Hincl" with "HE") as "#Hincl'".
    done.
  Qed.
End bor_kind_direct_incl_tac.
Ltac solve_bor_kind_direct_incl :=
  (* first compute [bor_kind_min] *)
  let simp_min := let x := fresh in intros x; unfold bor_kind_min; simpl; unfold x; notypeclasses refine eq_refl in
  match goal with
  | |- lctx_bor_kind_direct_incl ?E ?L ?b1 ?b2 =>
      refine (tac_lctx_bor_kind_direct_incl_simpl _ _ _ _ _ _ _ _ _);
      [ simp_min
      | simp_min
      | ]
  | |- _ =>
      fail 1000 "solve_bor_kind_direct_incl: not an lctx_bor_kind_direct_incl"
  end;
  match goal with
  | |- lctx_bor_kind_direct_incl ?E ?L (Owned _) (Owned _) =>
      refine (tac_lctx_bor_kind_direct_incl_owned_owned _ _ _); solve[fail]
  | |- lctx_bor_kind_direct_incl ?E ?L (Uniq _ _) (Uniq _ _) =>
      refine (tac_lctx_bor_kind_direct_incl_uniq_uniq _ _ _ _ _ _); [solve_lft_incl]
  | |- lctx_bor_kind_direct_incl ?E ?L (Shared _) (Shared _) =>
      refine (tac_lctx_bor_kind_direct_incl_shared_shared _ _ _ _ _); [solve_lft_incl]
  | |- lctx_bor_kind_direct_incl ?E ?L ?b1 ?b2 =>
      fail 1000 "solve_bor_kind_direct_incl: unable to solve inclusion"
  end.

(** lctx_lft_alive_count *)
Section alive_tac.
  Context `{typeGS Σ}.

  Lemma tac_lctx_lft_alive_count_local_owned i c κs E L κ κs' κs'' L' L'' :
    lctx_lft_alive_count_iter E L κs κs' L' →
    L' !! i = Some (κ ⊑ₗ{c} κs) →
    κs'' = κ :: κs' →
    L'' = (<[i:=κ ⊑ₗ{ S c} κs]> L') →
    lctx_lft_alive_count E L κ κs'' L''.
  Proof.
    intros ? ? -> ->. by eapply lctx_lft_alive_count_local_owned.
  Qed.

  Lemma tac_lctx_lft_alive_count_local_alias i κs E L κ κs' L' :
    lctx_lft_alive_count_iter E L κs κs' L' →
    L !! i = Some (κ ≡ₗ κs) →
    lctx_lft_alive_count E L κ κs' L'.
  Proof.
    intros ? ?. eapply lctx_lft_alive_count_local_alias; last done.
    by eapply elem_of_list_lookup_2.
  Qed.

  Lemma tac_lctx_lft_alive_count_iter_cons E L κ κs κs1 κs2 κs3 L1 L2 :
    lctx_lft_alive_count E L κ κs1 L1 →
    lctx_lft_alive_count_iter E L1 κs κs2 L2 →
    κs3 = κs1 ++ κs2 →
    lctx_lft_alive_count_iter E L (κ :: κs) κs3 L2.
  Proof.
    intros ? ? ->. simpl. eexists _, _, _. done.
  Qed.
  Lemma tac_lctx_lft_alive_count_iter_nil E L :
    lctx_lft_alive_count_iter E L [] [] L.
  Proof. done. Qed.

  Lemma tac_lctx_lft_alive_count_intersect E L κ κ' κs1 κs2 κs3 L1 L2 :
    lctx_lft_alive_count E L κ κs1 L1 →
    lctx_lft_alive_count E L1 κ' κs2 L2 →
    κs3 = κs1 ++ κs2 →
    lctx_lft_alive_count E L (κ ⊓ κ') κs3 L2.
  Proof. intros ?? ->. by eapply lctx_lft_alive_count_intersect. Qed.

  (* This weakens the elctx by removing the inclusion we used.
    This should ensure termination of the solver without making goals unprovable.
    (once we need to prove liveness of an external lifetime, the only local lifetime we should
      need is ϝ)
  *)
  Lemma tac_lctx_lft_alive_count_external i E L κ κ' κs L' :
    E !! i = Some (κ' ⊑ₑ κ) →
    lctx_lft_alive_count (delete i E) L κ' κs L' →
    lctx_lft_alive_count E L κ κs L'.
  Proof.
    intros ?%elem_of_list_lookup_2 H'.
    eapply lctx_lft_alive_count_external; first done.
    iIntros (F ?) "#HE HL".
    iApply H'; [ done | | done].
    iApply (big_sepL_submseteq with "HE").
    apply submseteq_delete.
  Qed.

End alive_tac.

(* redefined below *)
Ltac solve_lft_alive_count_iter :=
  idtac.

Ltac solve_lft_alive_count ::=
  repeat match goal with
  | |- lctx_lft_alive_count ?E ?L static _ _ =>
      notypeclasses refine (lctx_lft_alive_count_static E L)
  | |- lctx_lft_alive_count ?E ?L (?κ ⊓ ?κ') _ _ =>
      notypeclasses refine (tac_lctx_lft_alive_count_intersect E L κ κ' _ _ _ _ _ _ _ _);
        [solve_lft_alive_count | solve_lft_alive_count | simpl; reflexivity ]
  (* local inclusion *)
  | |- lctx_lft_alive_count ?E ?L ?κ _ _ =>
      (** Here, the solver relies on the fact that the indices of lifetimes should not change when increasing the counts. *)
      list_find_tac ltac:(fun i el =>
        match el with
        | κ ⊑ₗ{?c} ?κs =>
            notypeclasses refine (tac_lctx_lft_alive_count_local_owned i c κs E L κ _ _ _ _ _ _ _ _);
              [ solve_lft_alive_count_iter
              | simpl; reflexivity
              | simpl; reflexivity
              | simpl; reflexivity ]
        | κ ≡ₗ?κs =>
            notypeclasses refine (tac_lctx_lft_alive_count_local_alias i κs E L κ _ _ _ _);
              [ solve_lft_alive_count_iter
              | simpl; reflexivity ]
        | _ => fail
        end) L
  (* external inclusion *)
  | |- lctx_lft_alive_count ?E ?L ?κ _ _ =>
      list_find_tac ltac:(fun i el =>
        match el with
        | ?κ' ⊑ₑ κ =>
            notypeclasses refine (tac_lctx_lft_alive_count_external i E L κ κ' _ _ _ _);
            [reflexivity | simpl; solve[solve_lft_alive_count]]
        | _ => fail
        end) E
  end; fast_done.

Ltac solve_lft_alive_count_iter ::=
  match goal with
  | |- lctx_lft_alive_count_iter ?E ?L [] _ _ =>
    notypeclasses refine (tac_lctx_lft_alive_count_iter_nil E L)
  | |- lctx_lft_alive_count_iter ?E ?L (?κ :: ?κs) _ _ =>
      notypeclasses refine (tac_lctx_lft_alive_count_iter_cons E L κ κs _ _ _ _ _ _ _ _);
      [ solve_lft_alive_count
      | solve_lft_alive_count_iter
      | simpl; reflexivity ]
  end.

Section return_tac.
  Context `{!invGS Σ, !lctxGS Σ, !lftGS Σ lft_userE}.

  Lemma tac_llctx_release_toks_nil L :
    llctx_release_toks L [] L.
  Proof. done. Qed.

  Lemma tac_llctx_release_toks_cons i c κs' L κ κs L1 L2 :
    L !! i = Some (κ ⊑ₗ{c} κs') →
    L1 = <[i := κ ⊑ₗ{pred c} κs']> L →
    llctx_release_toks L1 κs L2 →
    llctx_release_toks L (κ :: κs) L2.
  Proof.
    intros ? -> ?. simpl. left. eexists _, _, _. done.
  Qed.

  Lemma tac_llctx_release_toks_cons_skips κ κs L1 L2 :
    llctx_release_toks L1 κs L2 →
    llctx_release_toks L1 (κ :: κs) L2.
  Proof.
    intros ?. simpl. right. done.
  Qed.
End return_tac.

Ltac solve_llctx_release_toks ::=
  match goal with
  | |- llctx_release_toks ?L [] _ =>
      notypeclasses refine (tac_llctx_release_toks_nil L)
  | |- llctx_release_toks ?L (?κ :: ?κs) _ =>
      first [list_find_tac ltac:(fun i el =>
        match el with
        | κ ⊑ₗ{?c} ?κs' =>
            notypeclasses refine (tac_llctx_release_toks_cons i c κs' L κ κs _ _ _ _ _);
              [ simpl; reflexivity
              | simpl; reflexivity
              | solve_llctx_release_toks ]
        | _ => fail
        end) L
      | notypeclasses refine (tac_llctx_release_toks_cons_skips κ κs _ _ _);
        solve_llctx_release_toks ]
  end.


(** llctx_find_llft *)
Section llctx_lft_split.
  Lemma tac_llctx_find_llft_solve_step_skip L L' κ κ' κs κs' oc key :
    llctx_find_llft L κ' key κs' L' →
    llctx_find_llft ((oc, κ, κs) :: L) κ' key κs' ((oc, κ, κs) :: L').
  Proof.
    intros (A & B & ? & -> & -> & ?).
    eexists ((oc, κ, κs) :: A), B, _. done.
  Qed.

  Lemma tac_llctx_find_llft_solve_step_find L κ κs κs' key oc :
    llctx_find_lft_key_interp key κ oc →
    κs' = κs →
    llctx_find_llft ((oc, κ, κs) :: L) κ key κs' L.
  Proof.
    intros ? ->.
    eexists [], L, _. split; first done. done.
  Qed.
End llctx_lft_split.

Ltac solve_llctx_find_llft ::=
  repeat match goal with
  | |- llctx_find_llft ((?oc, ?κ, ?κs) :: ?L) ?κ ?key ?κs' ?L' =>
      (notypeclasses refine (tac_llctx_find_llft_solve_step_find L κ κs κs' key oc _ _);
      [first [done | eexists _; done] | done]) || fail 1000 "llctx_find_llft_solver: cannot find lifetime " κ " because there are still " oc " open tokens"
  | |- llctx_find_llft ((?oc, ?κ, ?κs) :: ?L) ?κ' ?key ?κs' ?L' =>
      refine (tac_llctx_find_llft_solve_step_skip L _ κ κ' κs κs' oc key _)
  end.


(** solve_map_lookup *)
(* this extends the Lithium solver with support for goals where the lookup is None *)
Ltac compute_map_lookup :=
  unfold_opaque @named_lft_delete;
  unfold_opaque @named_lft_update;
  lazymatch goal with
  | |- ?Q !! _ = Some _ => try (is_var Q; unfold Q)
  | |- ?Q !! _ = ?e => idtac
  | _ => fail "unknown goal for compute_map_lookup"
  end; (solve
   [ repeat
      lazymatch goal with
      | |- <[?x:=?s]> ?Q !! ?y = ?res =>
            lazymatch x with
            | y => change_no_check (Some s = res); reflexivity
            | _ => change_no_check (Q !! y = res)
            end
      | |- ∅ !! _ = ?res =>
         change_no_check (None = res); reflexivity
      end ]).
Ltac solve_compute_map_lookup ::=
  compute_map_lookup.
Ltac solve_compute_map_lookup_nofail ::=
  compute_map_lookup.

Lemma compute_map_lookups_cons_tac (M : gmap string lft) (ns : list string) (n : string) (κs κs' : list lft) κ :
  M !! n = Some κ →
  Forall2 (λ x y, M !! x = Some y) ns κs' →
  κs = κ :: κs' →
  Forall2 (λ x y, M !! x = Some y) (n :: ns) κs.
Proof.
  intros Hlook Hall ->.
  econstructor; done.
Qed.

Ltac compute_map_lookups :=
  lazymatch goal with
  | |- Forall2 _ [] ?out =>
        unify out (@nil lft); by apply (Forall2_nil)
  | |- Forall2 _ (?x :: ?xs) ?out =>
      refine (compute_map_lookups_cons_tac _ xs x _ _ _ _ _ _);
      [ compute_map_lookup | compute_map_lookups | reflexivity]
  end.
Ltac solve_compute_map_lookups_nofail ::=
  compute_map_lookups.


(** solve_simplify_map *)

Section simplify_gmap.
  Context `{!typeGS Σ}.

  Lemma simplify_gmap_tac `{Countable K} {V} (M M' E : gmap K V) :
    map_to_list M' = map_to_list M →
    M' = E →
    M = E.
  Proof.
    intros Heq <-.
    eapply map_to_list_inj. rewrite Heq. done.
  Qed.

  Lemma simplify_lft_map_tac `{Countable K} {V} (M M' E : gmap K V) :
    E = M' →
    opaque_eq M E.
  Proof.
    Local Transparent opaque_eq.
    rewrite /opaque_eq. done.
  Qed.
End simplify_gmap.

(* keeps the invariant that the term contains no deletes *)
Ltac simplify_gmap M :=
  lazymatch M with
  (* push down deletes *)
  | delete ?x (<[?y := ?s]> ?Q) =>
      lazymatch x with
      | y =>
          simplify_gmap constr:(Q)
      | _ =>
          let M' := simplify_gmap constr:(delete x Q) in
          uconstr:(<[y := s]> M')
      end
  (* skip over inserts without deletes *)
  | <[?y := ?s]> ?Q =>
      let M' := simplify_gmap constr:(Q) in
      uconstr:(<[y := s]> M')
  (* remove a delete from an empty map *)
  | delete _ ∅ =>
      uconstr:(∅)
  | _ =>
      constr:(M)
  end.
Ltac solve_simplify_gmap ::=
  match goal with
  | |- ?Q = ?e => try (is_var Q; unfold Q); is_evar e
  | |- ?e = ?Q => try (is_var Q; unfold Q); is_evar e; symmetry
  | _ => fail "unknown goal for simplify_gmap"
  end;
  lazymatch goal with
  | |- ?Q = ?e =>
      let Q' := simplify_gmap constr:(Q) in
      (* NOTE: this relies on the simplification being order-preserving *)
      refine (simplify_gmap_tac Q Q' e _ _);
      [abstract (vm_compute; reflexivity) | reflexivity ]
  end.

Ltac simplify_lft_map M :=
  lazymatch M with
  (* push down deletes *)
  | named_lft_delete ?x (named_lft_update ?y ?s ?Q) =>
      lazymatch x with
      | y =>
          simplify_lft_map constr:(Q)
      | _ =>
          let M' := simplify_lft_map constr:(named_lft_delete x Q) in
          uconstr:(named_lft_update y s M')
      end
  (* skip over inserts without deletes *)
  | named_lft_update ?y ?s ?Q =>
      let M' := simplify_lft_map constr:(Q) in
      uconstr:(named_lft_update y s M')
  (* remove a delete from an empty map *)
  | named_lft_delete _ ∅ =>
      uconstr:(∅)
  | _ =>
      constr:(M)
  end.
Ltac solve_simplify_lft_map ::=
  match goal with
  | |- opaque_eq ?Q ?e => try (is_var Q; unfold Q); is_evar e
  | |- opaque_eq ?e ?Q => try (is_var Q; unfold Q); is_evar e; change_no_check (opaque_eq Q e)
      (*symmetry*)
  | _ => fail "unknown goal for simplify_lft_map"
  end;
  lazymatch goal with
  | |- opaque_eq ?Q ?e =>
      let Q' := simplify_lft_map constr:(Q) in
      refine (simplify_lft_map_tac Q Q' e _);
      [reflexivity ]
  end.

(** ** Layout sidecondition solver *)
Section solve_layout_alg_tac.
  Context `{!LayoutAlg}.

  Lemma use_layout_alg'_layout_tac st ly :
    syn_type_has_layout st ly → use_layout_alg' st = ly.
  Proof.
    rewrite /syn_type_has_layout /use_layout_alg'.
    move => -> //.
  Qed.

  Lemma syn_type_is_layoutable_layout_tac st ly :
    syn_type_has_layout st ly →
    syn_type_is_layoutable st.
  Proof. intros. eexists. done. Qed.

  Lemma use_layout_alg_layout_tac st ly :
    syn_type_has_layout st ly → use_layout_alg st = Some ly.
  Proof. done. Qed.

  Local Definition syn_type_has_layout_multi_pred : (var_name * syn_type) → (var_name * layout) → Prop :=
    λ '(field_name, field_spec) res,
      ∃ field_name2 field_ly,
      syn_type_has_layout field_spec field_ly ∧ field_name = field_name2 ∧ res = (field_name2, field_ly).

  (* structs *)
  Lemma syn_type_has_layout_struct_tac name fields fields' repr ly ly' :
    Forall2 syn_type_has_layout_multi_pred fields fields' →
    struct_layout_alg name fields' repr = Some ly' →
    ly = layout_of ly' →
    syn_type_has_layout (StructSynType name fields repr) ly.
  Proof.
    intros Ha Hb ->.
    eapply syn_type_has_layout_struct; last done.
    eapply Forall2_impl; first apply Ha.
    intros [] [] (? & ? & ? & -> & [= -> ->]). eauto.
  Qed.
  Lemma struct_layout_spec_has_layout_tac (sls : struct_layout_spec) fields' (sl sl' : struct_layout) :
    Forall2 syn_type_has_layout_multi_pred sls.(sls_fields) fields' →
    struct_layout_alg sls.(sls_name) fields' sls.(sls_repr) = Some sl' →
    sl = sl' →
    struct_layout_spec_has_layout sls sl.
  Proof.
    intros Ha Hb ->.
    eapply use_struct_layout_alg_Some; last done.
    eapply Forall2_impl; first apply Ha.
    intros [] [] (? & ? & ? & -> & [= -> ->]). eauto.
  Qed.
  Lemma use_struct_layout_alg_layout_tac (sls : struct_layout_spec) (sl : struct_layout) :
    struct_layout_spec_has_layout sls sl → use_struct_layout_alg sls = Some sl.
  Proof. done. Qed.

  (* enums *)
  Lemma syn_type_has_layout_enum_tac name variants variants' (it : IntType) ly ul sl repr struct_repr union_repr :
    Forall2 syn_type_has_layout_multi_pred variants variants' →
    union_repr = union_repr_of_enum_repr repr →
    struct_repr = struct_repr_of_enum_repr repr →
    union_layout_alg name variants' union_repr = Some ul →
    struct_layout_alg name [("discriminant", it_layout it); ("data", ul : layout)] struct_repr = Some sl →
    ly = layout_of sl →
    syn_type_has_layout (EnumSynType name it variants repr) ly.
  Proof.
    intros Ha -> -> Hb Hc ->.
    eapply syn_type_has_layout_enum; [ | done..].
    eapply Forall2_impl; first apply Ha.
    intros [] [] (? & ? & ? & -> & [= -> ->]). eauto.
  Qed.
  Lemma enum_layout_spec_has_layout_tac (els : enum_layout_spec) variants' (ul : union_layout) (sl sl' : struct_layout) struct_repr union_repr :
    Forall2 syn_type_has_layout_multi_pred els.(els_variants) variants' →
    union_repr = union_repr_of_enum_repr els.(els_repr) →
    struct_repr = struct_repr_of_enum_repr els.(els_repr) →
    union_layout_alg els.(els_name) variants' union_repr = Some ul →
    struct_layout_alg els.(els_name) [("discriminant", it_layout els.(els_tag_it)); ("data", ul : layout)] struct_repr = Some sl' →
    sl = sl' →
    enum_layout_spec_has_layout els sl.
  Proof.
    intros Ha -> -> Hb Hc ->.
    eapply use_enum_layout_alg_Some; [ | done..].
    eapply Forall2_impl; first apply Ha.
    intros [] [] (? & ? & ? & -> & [= -> ->]). eauto.
  Qed.
  Lemma use_enum_layout_alg_layout_tac (els : enum_layout_spec) (el : struct_layout) :
    enum_layout_spec_has_layout els el → use_enum_layout_alg els = Some el.
  Proof. done. Qed.

  (* unions *)
  Lemma syn_type_has_layout_union_tac name variants variants' ly ul repr :
    Forall2 syn_type_has_layout_multi_pred variants variants' →
    union_layout_alg name variants' repr = Some ul →
    ly = ul_layout ul →
    syn_type_has_layout (UnionSynType name variants repr) ly.
  Proof.
    intros Ha Hb ->.
    eapply syn_type_has_layout_union; [ | done..].
    eapply Forall2_impl; first apply Ha.
    intros [] [] (? & ? & ? & -> & [= -> ->]). eauto.
  Qed.
  Lemma union_layout_spec_has_layout_tac (uls : union_layout_spec) variants' (ul ul' : union_layout) :
    Forall2 syn_type_has_layout_multi_pred uls.(uls_variants) variants' →
    union_layout_alg uls.(uls_name) variants' uls.(uls_repr) = Some ul' →
    ul = ul' →
    union_layout_spec_has_layout uls ul.
  Proof.
    intros Ha Hb ->.
    eapply use_union_layout_alg_Some; [ | done..].
    eapply Forall2_impl; first apply Ha.
    intros [] [] (? & ? & ? & -> & [= -> ->]). eauto.
  Qed.
  Lemma use_union_layout_alg_layout_tac (uls : union_layout_spec) (ul : union_layout) :
    union_layout_spec_has_layout uls ul → use_union_layout_alg uls = Some ul.
  Proof. done. Qed.

  Lemma syn_type_has_layout_untyped_alg_tac st ly ly' :
    ly = ly' →
    syn_type_has_layout st ly →
    syn_type_has_layout (UntypedSynType (use_layout_alg' st)) ly'.
  Proof.
    intros <- Hst. eapply (syn_type_has_layout_make_untyped st).
    - rewrite /use_layout_alg' Hst //.
    - rewrite /use_layout_alg' Hst//.
  Qed.
  Lemma syn_type_has_layout_untyped_struct_alg_tac (sls : struct_layout_spec) sl ly' :
    ly' = sl →
    syn_type_has_layout sls sl →
    syn_type_has_layout (UntypedSynType (use_struct_layout_alg' sls)) ly'.
  Proof.
    intros -> Hst.
    rewrite /use_struct_layout_alg'.
    specialize (use_layout_alg_struct_Some_inv _ _  Hst) as (sl' & -> & <-).
    eapply (syn_type_has_layout_make_untyped sls); done.
  Qed.
End solve_layout_alg_tac.

Section simplify_layout_tac.
  Context `{!LayoutAlg}.

  Lemma simplify_use_layout_alg' T_st T_ly :
    use_layout_alg T_st = Some T_ly →
    use_layout_alg' T_st = T_ly.
  Proof.
    rewrite /use_layout_alg' => -> //.
  Qed.

  Lemma simplify_use_struct_layout_alg' sls sl :
    use_struct_layout_alg sls = Some sl →
    use_struct_layout_alg' sls = sl.
  Proof.
    rewrite /use_struct_layout_alg' => -> //.
  Qed.

  Lemma simplify_use_enum_layout_alg' els el :
    use_enum_layout_alg els = Some el →
    use_enum_layout_alg' els = el.
  Proof.
    rewrite /use_enum_layout_alg' => -> //.
  Qed.

  Lemma simplify_use_union_layout_alg' uls ul :
    use_union_layout_alg uls = Some ul →
    use_union_layout_alg' uls = ul.
  Proof.
    rewrite /use_union_layout_alg' => -> //.
  Qed.

  Lemma simplify_ot_layout ot ot' :
    ot = ot' →
    ot_layout ot = (ot_layout ot').
  Proof.
    intros ->; done.
  Qed.

  Lemma simplify_ot_layout_var T_st ly :
    use_layout_alg T_st = Some ly →
    ot_layout (use_op_alg' T_st) = ly.
  Proof.
    intros Hst.
    rewrite /use_op_alg'.
    apply syn_type_has_layout_op_alg in Hst as (ot & -> & <-).
    done.
  Qed.
End simplify_layout_tac.

(** Solve goals of the forms
  - [use_layout_alg st = Some ?ly]
  - [use_layout_alg' st = ?ly]
  - [syn_type_has_layout st ?ly]
  where [ly] may or may not be an evar.
  *)
(* Declaration, definition is below. *)
Ltac solve_layout_alg := idtac.

Ltac solve_ot_eq := idtac.

(* We assume a let-binding [H_ly] has been introduced into the context in which we can rewrite *)
Ltac simplify_layout' H_ly :=
  repeat match type of H_ly with
  | _ = use_layout_alg' ?st =>
      erewrite (simplify_use_layout_alg' st) in H_ly;
      [ | solve_layout_alg]
  | _ = use_struct_layout_alg' ?sls =>
      erewrite (simplify_use_struct_layout_alg' sls) in H_ly;
      [ | solve_layout_alg]
  | _ = use_enum_layout_alg' ?els =>
      erewrite (simplify_use_enum_layout_alg' els) in H_ly;
      [ | solve_layout_alg]
  | _ = use_union_layout_alg' ?uls =>
      erewrite (simplify_use_union_layout_alg' uls) in H_ly;
      [ | solve_layout_alg]
  | _ = ot_layout (use_op_alg' ?st) =>
      match st with
      | ty_syn_type ?ty =>
          is_var ty;
          erewrite (simplify_ot_layout_var st) in H_ly;
          [ | solve_layout_alg ]
      | _ =>
          erewrite (simplify_ot_layout (use_op_alg' st)) in H_ly;
          [ | solve_ot_eq ]
      end
  | _ => idtac
  end.
(** Simplify a layout [ly] in the goal. *)
Ltac simplify_layout_go ly :=
  let Hly := fresh in
  let ly_term := fresh in
  remember ly as ly_term eqn:Hly;
  simplify_layout' Hly;
  subst ly_term.
Ltac simplify_layout ly :=
  match ly with
  | ?ly => is_var ly
  | layout_of (?sl) => is_var sl
  | ul_layout ?ul => is_var ul
  | it_layout ?it => idtac
  | _ => simplify_layout_go ly
  end.

Ltac maybe_simplify_layout ly :=
  match ly with
  | use_layout_alg' _ => simplify_layout_go ly
  | use_struct_layout_alg' _ => simplify_layout_go ly
  | use_enum_layout_alg' _ => simplify_layout_go ly
  | use_union_layout_alg' _ => simplify_layout_go ly
  | ot_layout _ => simplify_layout_go ly
  end.
Ltac simplify_layout_goal :=
  repeat match goal with
  | |- context[?ly] =>
      match type of ly with
      | layout => maybe_simplify_layout ly
      end
  end.
Ltac simplify_layout_assum :=
  repeat match goal with
  | H: context[?ly] |- _ =>
      assert_is_not_cached H;
      match type of ly with
      | layout => maybe_simplify_layout ly
      end
  end.

(** Solve goals of the form [layout_wf ly]. *)
Section layout.
  Lemma layout_wf_unit :
    layout_wf unit_sl.
  Proof.
    rewrite /layout_wf/ly_align/ly_size/=.
    apply Z.divide_0_r.
  Qed.
  Lemma layout_wf_ptr :
    layout_wf void*.
  Proof.
    rewrite /layout_wf/ly_align/ly_size/=.
    rewrite /bytes_per_addr/bytes_per_addr_log/=.
    done.
  Qed.
  Lemma layout_wf_bool :
    layout_wf bool_layout.
  Proof.
    rewrite /layout_wf/ly_align/ly_size/=.
    done.
  Qed.
End layout.
Ltac solve_layout_wf :=
  unfold_no_enrich;
  match goal with
  | |- layout_wf ?ly =>
      simplify_layout ly
  end;
  match goal with
  | |- layout_wf ?ly =>
      is_var ly;
      refine (use_layout_alg_wf _ _ _);
      [solve_layout_alg]
  | |- layout_wf (it_layout ?it) =>
      refine (int_type_layout_wf it)
  | |- layout_wf (mk_array_layout _ _) =>
      refine (array_layout_wf _ _ _);
      solve_layout_wf
  | |- layout_wf (layout_of unit_sl) =>
      notypeclasses refine layout_wf_unit
  | |- layout_wf void* =>
      notypeclasses refine layout_wf_ptr
  | |- layout_wf bool_layout =>
      notypeclasses refine layout_wf_bool
  | |- _ =>
      (* TODO *)
      try done
  end.

Ltac solve_ly_align_ib :=
  unfold_no_enrich;
  match goal with
  | |- ly_align_in_bounds ?ly =>
      simplify_layout ly
  end;
  match goal with
  | |- ly_align_in_bounds ?ly =>
      is_var ly;
      refine (use_layout_alg_align _ _ _);
      [solve_layout_alg]
  | |- _ => idtac
  end;
  try first [eassumption | done ].

(** Solve equalities and inequalities involving [ly_size]. *)
Ltac solve_layout_size :=
  unfold_no_enrich;
  (* unfold [size_of_st] in the context *)
  repeat match goal with
  | H : context[size_of_st ?st] |- _ =>
      rewrite /size_of_st in H;
      simplify_layout (use_layout_alg' st)
  end;
  (* unfold [size_of_st] in the goal *)
  rewrite /size_of_st;
  (* simplify layouts by abstracting them into variables *)
  repeat match goal with
         | |- context[ly_size ?ly] =>
              assert_fails (is_var ly);
              let Hly := fresh in
              let ly_term := fresh in
              remember ly as ly_term eqn:Hly;
              simplify_layout' Hly
          end;
  (* substitute the equalities again as lia can't deal with that *)
  subst;
  (* simplify simple layout sizes *)
  simpl;
  (* call into lia *)
  try lia.

Global Arguments ly_size : simpl nomatch.

(** Solve goals of the form [Forall2 syn_type_has_layout_multi_pred xs ?fields], by instantiating [?fields]. *)
(* Definition below. *)
Ltac solve_layout_alg_forall :=
  idtac.

(** Solve goals of the form [ly1 = ly2]. *)
Ltac solve_layout_eq :=
  unfold_no_enrich;
  (* simplify both sides *)
  match goal with
  | |- ?ly1 = ?ly2 =>
      simplify_layout ly1;
      simplify_layout ly2
  end;
  (* TODO *)
  try reflexivity.

Global Arguments enum_layout_spec_is_layoutable : simpl never.
Global Arguments struct_layout_spec_is_layoutable : simpl never.
Global Arguments union_layout_spec_is_layoutable : simpl never.

Ltac solve_layout_alg_prepare :=
  try match goal with
  | |- syn_type_has_layout ?st ?ly =>
      simplify_layout ly
  end;
  unfold_no_enrich;
  (* normalize goal *)
  lazymatch goal with
  | |- syn_type_is_layoutable ?st => refine (syn_type_is_layoutable_layout_tac st _ _)
  | |- use_layout_alg ?st = Some ?ly => refine (use_layout_alg_layout_tac st ly _)
  | |- use_layout_alg' ?st = ?ly => refine (use_layout_alg'_layout_tac st ly)
  | |- syn_type_has_layout ?st ?ly => idtac
  (* structs *)
  | |- use_struct_layout_alg ?sls = ?Some ?sl => refine (use_struct_layout_alg_layout_tac _ _ _)
  | |- struct_layout_spec_has_layout ?sls ?sl => idtac
  | |- struct_layout_spec_is_layoutable ?sls => eexists; refine (use_struct_layout_alg_layout_tac _ _ _)
  (* enums *)
  | |- use_enum_layout_alg ?els = ?Some ?el => refine (use_enum_layout_alg_layout_tac _ _ _)
  | |- enum_layout_spec_has_layout ?els ?el => idtac
  | |- enum_layout_spec_is_layoutable ?els => eexists; refine (use_enum_layout_alg_layout_tac _ _ _)
  (* unions *)
  | |- use_union_layout_alg ?uls = ?Some ?ul => refine (use_union_layout_alg_layout_tac _ _ _)
  | |- union_layout_spec_has_layout ?uls ?ul => idtac
  | |- union_layout_spec_is_layoutable ?uls => eexists; refine (use_union_layout_alg_layout_tac _ _ _)
  end.

Ltac solve_layout_alg_core_step :=
  (* For primitive goals for which we have an assumption in the context *)
  try eassumption;
  (* Simplify *)
  try match goal with
  | |- syn_type_has_layout ?st ?ly =>
      let st_eval := eval hnf in st in
      change_no_check st with st_eval
  | |- Forall2 syn_type_has_layout_multi_pred ?fields ?fields' =>
      let fields_eval := eval hnf in fields in
      change_no_check fields with fields_eval
  end;
  (* match on st *)
  lazymatch goal with
  | |- Forall2 syn_type_has_layout_multi_pred [] ?fields' =>
      econstructor
  | |- Forall2 syn_type_has_layout_multi_pred (?f :: ?fields) ?fields' =>
    econstructor;
    [ eexists _, _; split_and!; [ | refine eq_refl | refine eq_refl] | ]
  | |- syn_type_has_layout (IntSynType ?it) ?ly =>
      notypeclasses refine (syn_type_has_layout_int _ _ _ _);
      [ solve_layout_eq | solve_layout_size; shelve ]
  | |- syn_type_has_layout BoolSynType ?ly =>
      notypeclasses refine (syn_type_has_layout_bool _ _);
      [solve_layout_eq ]
  | |- syn_type_has_layout CharSynType ?ly =>
      notypeclasses refine (syn_type_has_layout_char _ _);
      [solve_layout_eq ]
  | |- syn_type_has_layout PtrSynType ?ly =>
      notypeclasses refine (syn_type_has_layout_ptr _ _);
      [solve_layout_eq ]
  | |- syn_type_has_layout FnPtrSynType ?ly =>
      notypeclasses refine (syn_type_has_layout_fnptr _ _);
      [solve_layout_eq ]
  | |- syn_type_has_layout (StructSynType ?name ?fields ?repr) ?ly =>
      notypeclasses refine (syn_type_has_layout_struct_tac name fields _ repr _ _  _ _ _);
      [| | solve_layout_eq]
  | |- struct_layout_spec_has_layout ?sls ?sl =>
      notypeclasses refine (struct_layout_spec_has_layout_tac sls _ sl _ _ _ _);
      [| | solve_layout_eq]
  | |- syn_type_has_layout UnitSynType ?ly =>
      notypeclasses refine (syn_type_has_layout_unit _ _);
      [solve_layout_eq ]
  | |- syn_type_has_layout (ArraySynType ?st ?len) ?ly =>
      notypeclasses refine (syn_type_has_layout_array st len _ ly _ _ _);
      [ solve_layout_eq | | solve_layout_size; shelve ]
  | |- syn_type_has_layout (UnsafeCell ?st) ?ly =>
      notypeclasses refine (syn_type_has_layout_unsafecell st ly _);
      []
  | |- syn_type_has_layout (UntypedSynType ?ly) ?ly' =>
      lazymatch ly with
      | use_layout_alg' ?st' =>
          notypeclasses refine (syn_type_has_layout_untyped_alg_tac st' _ ly' _ _);
            [solve_layout_eq | ]
      | use_struct_layout_alg' ?sls' =>
          notypeclasses refine (syn_type_has_layout_untyped_struct_alg_tac sls' _ ly' _ _);
            [solve_layout_eq | ]
      | _ =>
          notypeclasses refine (syn_type_has_layout_untyped ly ly' _ _ _ _);
            [solve_layout_eq | solve_layout_wf; shelve | solve_layout_size; shelve | solve_ly_align_ib; shelve ]
      end
  | |- syn_type_has_layout (EnumSynType ?name ?it ?variants ?repr) ?ly =>
      notypeclasses refine (syn_type_has_layout_enum_tac name variants _ it _ _ _ _ _ _ _ _ _ _ _ _ );
      [| refine eq_refl | refine eq_refl | | | solve_layout_eq]
  | |- enum_layout_spec_has_layout ?els ?el =>
      notypeclasses refine (enum_layout_spec_has_layout_tac els _ _ _ _ _ _ _ _ _ _ _ _ );
      [| refine eq_refl | refine eq_refl | | | solve_layout_eq]
  | |- syn_type_has_layout (UnionSynType ?name ?variants ?repr) ?ly =>
      notypeclasses refine (syn_type_has_layout_union_tac name variants _ _ _ _ _ _ _ );
      [| | solve_layout_eq]
  | |- union_layout_spec_has_layout ?uls ?ul =>
      notypeclasses refine (union_layout_spec_has_layout_tac uls _ _ _ _ _ _);
      [| | solve_layout_eq]
  end.

Ltac solve_layout_alg_core :=
  repeat solve_layout_alg_core_step.
Ltac solve_layout_alg ::=
  solve_layout_alg_prepare;
  solve[solve_layout_alg_core].

Ltac solve_layout_alg_forall ::=
  unfold_no_enrich;
  simpl;
  solve_layout_alg_core
  .

Ltac solve_compute_layout ::=
  unfold_no_enrich;
  open_cache;
  first [eassumption | progress solve_layout_alg; shelve].

Ltac solve_compute_struct_layout ::=
  unfold_no_enrich;
  open_cache;
  first [eassumption | progress solve_layout_alg; shelve].

(** syn_type_compat solver *)
Section syntype_compat.
  Context `{!LayoutAlg}.
  Lemma syn_type_compat_refl st :
    syn_type_compat st st.
  Proof. left. done. Qed.

  Lemma syn_type_compat_untyped_r st ly ly' :
    syn_type_has_layout st ly' →
    ly = ly' →
    syn_type_compat st (UntypedSynType ly).
  Proof. intros ? ->. right. eauto. Qed.
End syntype_compat.
Global Arguments syn_type_compat : simpl never.

Ltac solve_syn_type_compat :=
  unfold_no_enrich;
  lazymatch goal with
  | |- syn_type_compat ?st ?st =>
      refine (syn_type_compat_refl _)
  | |- syn_type_compat ?st1 (UntypedSynType ?ly2) =>
      refine (syn_type_compat_untyped_r _ _ _ _ _);
      [solve_layout_alg | solve_layout_eq ]
  end.


(** ** Op-alg solver *)

Section opalg.
  Context `{!typeGS Σ}.

  Lemma use_op_alg'_ot_tac st ot :
    use_op_alg st = Some ot → use_op_alg' st = ot.
  Proof. rewrite /use_op_alg' => -> //. Qed.

  (* Use for tyvars *)
  Lemma use_op_alg_tyvar_tac st ot :
    syn_type_is_layoutable st →
    ot = use_op_alg' st →
    use_op_alg st = Some ot.
  Proof.
    intros (ly & Hly%syn_type_has_layout_op_alg) ->.
    destruct Hly as (ot & Hot & <-).
    rewrite /use_op_alg' Hot //.
  Qed.

  Lemma simplify_use_op_alg' T_st T_ly :
    use_op_alg T_st = Some T_ly →
    use_op_alg' T_st = T_ly.
  Proof.
    rewrite /use_op_alg' => -> //.
  Qed.
End opalg.

Ltac solve_op_alg := idtac.

(* We assume a let-binding [H_ly] has been introduced into the context in which we can rewrite *)
Ltac simplify_optype' H_ly :=
  repeat match type of H_ly with
  | _ = use_op_alg' ?st =>
      erewrite (simplify_use_op_alg' st) in H_ly;
      [ | solve_op_alg]
  | _ => idtac
  end.
(** Simplify a layout [ly] in the goal. *)
Ltac simplify_optype_go ly :=
  let Hly := fresh in
  let ly_term := fresh in
  remember ly as ly_term eqn:Hly;
  simplify_optype' Hly;
  subst ly_term.
Ltac simplify_optype ly :=
  match ly with
  | ?ly => is_var ly
  | _ => simplify_optype_go ly
  end.

(** Solve goals of the form [ot1 = ot2]. *)
Ltac solve_ot_eq ::=
  unfold_no_enrich;
  (* simplify both sides *)
  try match goal with
  | |- ?ot1 = ?ot2 =>
      assert_fails (is_evar ot1);
      assert_fails (is_evar ot2);
      simplify_optype ot1;
      simplify_optype ot2
  end;
  (* TODO? *)
  try reflexivity.

(** Solve goals of the form [Forall2 _ xs ?fields], by instantiating [?fields]. *)
Ltac assert_is_atomic_st st :=
  first [is_var st | match st with | ty_syn_type ?T => is_var T end].
Ltac assert_is_atomic_sls sls :=
  is_var sls.
Ltac assert_is_atomic_els els :=
  is_var els.
Ltac assert_is_atomic_uls uls :=
  is_var uls.

(* Definition below. *)
Ltac solve_op_alg_forall :=
  idtac.

Ltac solve_op_alg_prepare :=
  (* normalize goal *)
  lazymatch goal with
  | |- use_op_alg ?st = Some ?ot => idtac
  | |- use_op_alg' ?st = ?ot => refine (use_op_alg'_ot_tac st ot _)
  end.

Ltac solve_op_alg_core_step :=
  (* TODO: needed? *)
  try eassumption;
  (* Revert to deriving it from layout algorithms for atomics *)
  try lazymatch goal with
    | |- use_op_alg ?st = Some ?ot =>
      assert_is_atomic_st st;
      refine (use_op_alg_tyvar_tac st _ _ _);
      [solve_layout_alg | solve_ot_eq]
  end;
  (* Unfold *)
  try lazymatch goal with
  | |- Forall2 use_op_alg_struct_pred ?fields ?fields' =>
      let fields_eval := eval hnf in fields in
      change_no_check fields with fields_eval
  | |- use_op_alg ?st = Some ?op =>
      let st_eval := eval hnf in st in
      change_no_check st with st_eval
  end;
  (* match on st *)
  lazymatch goal with
  | |- Forall2 use_op_alg_struct_pred [] ?fields' =>
      econstructor
  | |- Forall2 use_op_alg_struct_pred (?f :: ?fields) ?fields' =>
    econstructor; [ unfold use_op_alg_struct_pred | ]
  | |- use_op_alg (IntSynType ?it) = Some ?ot =>
      notypeclasses refine (use_op_alg_int _ _ _);
      [ solve_ot_eq ]
  | |- use_op_alg BoolSynType = Some ?ot =>
      notypeclasses refine (use_op_alg_bool _ _);
      [solve_ot_eq ]
  | |- use_op_alg CharSynType = Some ?ot =>
      notypeclasses refine (use_op_alg_char _ _);
      [solve_ot_eq ]
  | |- use_op_alg PtrSynType = Some ?ot =>
      notypeclasses refine (use_op_alg_ptr _ _);
      [solve_ot_eq ]
  | |- use_op_alg FnPtrSynType = Some ?ot =>
      notypeclasses refine (use_op_alg_fnptr _ _);
      [solve_ot_eq ]
  | |- use_op_alg (StructSynType ?name ?fields ?repr) = Some ?ot =>
      notypeclasses refine (use_op_alg_struct name fields _ _ _ _  _ _ _);
      [ | solve_layout_alg | solve_ot_eq ]
  | |- use_op_alg UnitSynType = Some ?ot =>
      notypeclasses refine (use_op_alg_unit _ _);
      [solve_ot_eq ]
  | |- use_op_alg (ArraySynType ?st ?len) = Some ?ot =>
      fail 1000 "implement solve_op_alg for ArraySynType"
  | |- use_op_alg (UnsafeCell ?st) = Some ?ot =>
      notypeclasses refine (use_op_alg_unsafecell st _ _);
      [ ]
  | |- use_op_alg (UntypedSynType ?ly) = Some ?ot =>
      simplify_layout ly;
      notypeclasses refine (use_op_alg_untyped _ ot _);
      [solve_ot_eq ]
  | |- use_op_alg (EnumSynType ?name ?it ?fields ?repr) = Some ?ot =>
      notypeclasses refine (use_op_alg_enum _ _ _ _ _ _ _ _);
      [solve_layout_alg | solve_ot_eq]
  | |- use_op_alg (UnionSynType ?name ?fields ?repr) = Some ?ot =>
      notypeclasses refine (use_op_alg_union _ _ _ _ _ _ _);
      [solve_layout_alg | solve_ot_eq]
  | |- use_op_alg (ty_syn_type _) = Some ?ot =>
      notypeclasses refine (use_op_alg_tyvar_tac (ty_syn_type _) ot _ _);
      [solve_layout_alg | solve_ot_eq]
  | |- use_op_alg ?st = Some ?ot =>
      is_var st;
      notypeclasses refine (use_op_alg_tyvar_tac st ot _ _);
      [solve_layout_alg | solve_ot_eq]
  end.

Ltac solve_op_alg_core :=
  repeat solve_op_alg_core_step.
Ltac solve_op_alg ::=
  solve_op_alg_prepare;
  solve_op_alg_core.

Ltac solve_op_alg_forall ::=
  simpl;
  lazymatch goal with
  | |- Forall2 use_op_alg_struct_pred [] ?fields' =>
      econstructor
  | |- Forall2 use_op_alg_struct_pred (?f :: ?fields) ?fields' =>
    econstructor;
    [ simpl; solve_op_alg_core
    | solve_op_alg_forall]
  end.


(** ** Solver for goals of the form [ty_has_op_type] *)
Section tac.
  Context `{!typeGS Σ}.

  Lemma ty_has_op_type_simplify_tac {rt} (ty : type rt) ot ot2 mt :
    ot = ot2 →
    ty_has_op_type ty ot2 mt →
    ty_has_op_type ty ot mt.
  Proof. intros ->; done. Qed.
End tac.

Ltac simplify_ot :=
  simpl;
  match goal with
  | |- (use_op_alg' ?st) = ?ot =>
      solve_op_alg
  | |- ?ot = use_op_alg' ?st =>
      symmetry; solve_op_alg
  | |- _ => reflexivity
  end.
Arguments is_value_ot : simpl never.
Arguments is_array_ot : simpl never.
Arguments is_struct_ot : simpl never.
Ltac solve_ty_has_op_type_core_step :=
  first [
    match goal with
    | |- ∃ _, _ => eexists
    end
  | split_and!; simpl
  | done
  | sidecond_hook
  | shelve
  ].
Ltac solve_ty_has_op_type_core :=
  repeat solve_ty_has_op_type_core_step.

Ltac solve_ty_has_op_type_prepare :=
  lazymatch goal with
  | |- ty_has_op_type ?ty ?ot ?mc =>
      (* simplify op_type *)
      refine (ty_has_op_type_simplify_tac ty ot _ mc _ _);
      [simplify_ot| ];
      (* unfold *)
      first [ assert_fails (is_var ty); rewrite ty_has_op_type_unfold/_ty_has_op_type/= | idtac];
      (* specific handling for a few cases *)
      lazymatch goal with
      | |- is_value_ot ?st (use_op_alg' ?st) ?mc =>
          refine (is_value_ot_use_op_alg _ _ _ _ _); [done | solve_layout_alg]
      | |- is_value_ot _ _ _ => rewrite /is_value_ot; eexists _
      | |- _ =>
           (*otherwise unfold *)
          hnf
      end
  end.
Ltac solve_ty_has_op_type :=
  solve_ty_has_op_type_prepare;
  solve_ty_has_op_type_core.

(** Solver for goals of the form [ty_allows_reads ?ty] and [ty_allows_writes ?ty] *)
Ltac solve_ty_allows :=
  lazymatch goal with
  | |- ty_allows_reads ?ty =>
      unfold ty_allows_reads
  | |- ty_allows_writes ?ty =>
      unfold ty_allows_writes
  end;
  solve_ty_has_op_type.


(** ** [bor_kind] solvers *)
Section bor_kind_outlives.
  Context `{!typeGS Σ}.

  Lemma lctx_bor_kind_outlives_owned E L wl κ :
    lctx_bor_kind_outlives E L (Owned wl) κ.
  Proof.
    iIntros (?) "HL HE". done.
  Qed.

  Lemma lctx_bor_kind_outlives_uniq E L κ γ κ' :
    lctx_lft_incl E L κ' κ →
    lctx_bor_kind_outlives E L (Uniq κ γ) κ'.
  Proof.
    iIntros (Hincl ?) "HL HE".
    iPoseProof (Hincl with "HL") as "#Ha".
    by iApply "Ha".
  Qed.

  Lemma lctx_bor_kind_outlives_shared E L κ κ' :
    lctx_lft_incl E L κ' κ →
    lctx_bor_kind_outlives E L (Shared κ) κ'.
  Proof.
    iIntros (Hincl ?) "HL HE".
    iPoseProof (Hincl with "HL") as "#Ha".
    by iApply "Ha".
  Qed.
End bor_kind_outlives.

Ltac solve_bor_kind_outlives :=
  lazymatch goal with
  | |- lctx_bor_kind_outlives ?E ?L (Owned _) ?κ =>
      refine (lctx_bor_kind_outlives_owned E L _ _)
  | |- lctx_bor_kind_outlives ?E ?L (Uniq _ _) _ =>
      refine (lctx_bor_kind_outlives_uniq E L _ _ _ _); solve_lft_incl
  | |- lctx_bor_kind_outlives ?E ?L (Shared _) _ =>
      refine (lctx_bor_kind_outlives_shared _ _ _ _ _); solve_lft_incl
  end.

(** ** Augment the context with commonly needed facts. *)
Section augment.
  Lemma MaxInt_isize_lt_usize : (MaxInt isize_t < MaxInt usize_t)%Z.
  Proof. rewrite !MaxInt_eq. apply max_int_isize_lt_usize. Qed.
  Lemma MaxInt_ge_127 (it : int_type) : (127 ≤ MaxInt it)%Z.
  Proof. rewrite MaxInt_eq. apply max_int_ge_127. Qed.
  Lemma MinInt_le_n128_signed (it : int_type) :
    it_signed it = true → (MinInt it ≤ -128)%Z.
  Proof. rewrite MinInt_eq. apply min_int_le_n128_signed. Qed.
  Lemma MinInt_unsigned_0 (it : int_type) :
    it_signed it = false → (MinInt it = 0)%Z.
  Proof. rewrite MinInt_eq. apply min_int_unsigned_0. Qed.
  Lemma bytes_per_addr_eq :
    bytes_per_addr = 8%nat.
  Proof. done. Qed.
End augment.


Ltac init_cache :=
  (*specialize (bytes_per_addr_eq) as ?;*)
  specialize_cache (MaxInt_isize_lt_usize);
  specialize_cache (MaxInt_ge_127 i8);
  specialize_cache (MaxInt_ge_127 u8);
  specialize_cache (MaxInt_ge_127 i16);
  specialize_cache (MaxInt_ge_127 u16);
  specialize_cache (MaxInt_ge_127 i32);
  specialize_cache (MaxInt_ge_127 u32);
  specialize_cache (MaxInt_ge_127 i64);
  specialize_cache (MaxInt_ge_127 u64);
  specialize_cache (MaxInt_ge_127 i128);
  specialize_cache (MaxInt_ge_127 u128);
  specialize_cache (MaxInt_ge_127 isize_t);
  specialize_cache (MaxInt_ge_127 usize_t);
  specialize_cache (MinInt_le_n128_signed i8 eq_refl);
  specialize_cache (MinInt_le_n128_signed i16 eq_refl);
  specialize_cache (MinInt_le_n128_signed i32 eq_refl);
  specialize_cache (MinInt_le_n128_signed i64 eq_refl);
  specialize_cache (MinInt_le_n128_signed i128 eq_refl);
  specialize_cache (MinInt_le_n128_signed isize_t eq_refl);
  specialize_cache (MinInt_unsigned_0 u8 eq_refl);
  specialize_cache (MinInt_unsigned_0 u16 eq_refl);
  specialize_cache (MinInt_unsigned_0 u32 eq_refl);
  specialize_cache (MinInt_unsigned_0 u64 eq_refl);
  specialize_cache (MinInt_unsigned_0 u128 eq_refl);
  specialize_cache (MinInt_unsigned_0 usize_t eq_refl)
  (*specialize (layout_wf_unit) as ?;*)
  (*specialize (layout_wf_ptr) as ?*)
.


(** * Tactics for inverting layout assumptions *)
Global Arguments use_layout_alg : simpl never.

(** Check for already solved cached results for layout alg applications *)
Section remove_duplicates.
  Context `{!LayoutAlg}.
  Lemma enter_cache_resolve_layout_alg_dup st ly1 ly2 :
    use_layout_alg st = Some ly1 →
    CACHED (use_layout_alg st = Some ly2) →
    ly1 = ly2.
  Proof.
    intros. open_cache. by eapply syn_type_has_layout_inj.
  Qed.

  Lemma enter_cache_resolve_struct_layout_alg_dup sls ly1 ly2 :
    use_struct_layout_alg sls = Some ly1 →
    CACHED (use_struct_layout_alg sls = Some ly2) →
    ly1 = ly2.
  Proof.
    intros H1 H2. open_cache.
    rewrite H1 in H2. naive_solver.
  Qed.
  Lemma enter_cache_resolve_enum_layout_alg_dup els ly1 ly2 :
    use_enum_layout_alg els = Some ly1 →
    CACHED (use_enum_layout_alg els = Some ly2) →
    ly1 = ly2.
  Proof.
    intros H1 H2. open_cache.
    rewrite H1 in H2. naive_solver.
  Qed.
  Lemma enter_cache_resolve_union_layout_alg_dup uls ly1 ly2 :
    use_union_layout_alg uls = Some ly1 →
    CACHED (use_union_layout_alg uls = Some ly2) →
    ly1 = ly2.
  Proof.
    intros H1 H2. open_cache.
    rewrite H1 in H2. naive_solver.
  Qed.
End remove_duplicates.

Ltac check_for_cached_layout H :=
  lazymatch type of H with
    | use_layout_alg ?st = Some ?ly1 =>
        lazymatch goal with
        | H2: CACHED (use_layout_alg st = Some ?ly2) |- _ =>
          let Heq := fresh "Heq" in
          specialize (enter_cache_resolve_layout_alg_dup _ _ _ H H2) as Heq;
          subst_with Heq;
          clear H
        end
    | use_struct_layout_alg ?sls = Some ?ly1 =>
        lazymatch goal with
        | H2: CACHED (use_struct_layout_alg sls = Some ?ly2) |- _ =>
          let Heq := fresh "Heq" in
          specialize (enter_cache_resolve_struct_layout_alg_dup _ _ _ H H2) as Heq;
          subst_with Heq;
          clear H
        end
    | use_enum_layout_alg ?els = Some ?ly1 =>
        lazymatch goal with
        | H2: CACHED (use_enum_layout_alg els = Some ?ly2) |- _ =>
          let Heq := fresh "Heq" in
          specialize (enter_cache_resolve_enum_layout_alg_dup _ _ _ H H2) as Heq;
          subst_with Heq;
          clear H
        end
    | use_union_layout_alg ?uls = Some ?ly1 =>
        lazymatch goal with
        | H2: CACHED (use_union_layout_alg uls = Some ?ly2) |- _ =>
          let Heq := fresh "Heq" in
          specialize (enter_cache_resolve_union_layout_alg_dup _ _ _ H H2) as Heq;
          subst_with Heq;
          clear H
        end
  end.

Ltac simplify_layout_alg := fail "impl simplify_layout_alg".
Ltac inv_multi_fields_rec Hrec :=
  simpl in Hrec;
  match type of Hrec with
  | Forall2 _ (?x :: ?L1) (?L2) =>
      let Harg := fresh in
      let Hrec2 := fresh "Hrec" in
      let Heq := fresh "Heq" in
      let Hnameeq := fresh "Heq" in
      apply Forall2_cons_inv_l in Hrec as ([] & ? & [Hnameeq Harg] & Hrec2 & Heq);
      subst_with Hnameeq;
      subst_with Heq;
      inv_multi_fields_rec Hrec2;
      simplify_layout_alg Harg
  | Forall2 _ [] _ =>
      apply Forall2_nil_inv_l in Hrec as ->
  end.
Ltac inv_multi_fields Hrec :=
  simpl in Hrec; inv_multi_fields_rec Hrec.


From iris.proofmode Require Import string_ident.
Ltac rename_layouts_core H cont :=
  lazymatch type of H with
  | struct_layout_alg ?name ?fields ?repr = Some ?sl =>
      let Hfields := fresh in
      apply struct_layout_alg_has_fields in H as Hfields;
      enter_cache Hfields;

      let sl_name := eval cbv in (append name "_sl") in
      let fields_name := eval cbv in (append name "_fields") in
      let H_name := eval cbv in (append name "_salg") in
      string_to_ident_cps sl_name ltac:(fun sl_n =>
      string_to_ident_cps fields_name ltac:(fun fields_n =>
      string_to_ident_cps H_name ltac:(fun H_n =>
      try rename sl into sl_n;
      try rename Hfields into fields_N;
      first [rename H into H_n; cont H_n | cont H]
      )))
  | union_layout_alg ?name ?variants ?repr = Some ?ul =>
      let Hvariants := fresh in
      apply union_layout_alg_has_variants in H as Hvariants;
      enter_cache Hvariants;

      let ul_name := eval cbv in (append name "_ul") in
      let variants_name := eval cbv in (append name "_variants") in
      let H_name := eval cbv in (append name "_ualg") in
      string_to_ident_cps ul_name ltac:(fun ul_n =>
      string_to_ident_cps variants_name ltac:(fun variants_n =>
      string_to_ident_cps H_name ltac:(fun H_n =>
      try rename ul into ul_n;
      try rename Hvariants into variants_n;
      first [rename H into H_n; cont H_n | cont H]
      )))
  | use_layout_alg ?T = Some ?ly =>
      assert_is_atomic_st T;
      is_var ly;
      first [
        is_var T;
        let st_name := constr:(ident_to_string! T) in
        let ly_name := eval cbv in (append st_name "_ly") in
        let H_name := eval cbv in (append st_name "_alg") in
        string_to_ident_cps ly_name ltac:(fun ly_n =>
        string_to_ident_cps H_name ltac:(fun H_n =>
        try rename ly into ly_n;
        rename H into H_n; cont H_n))
      | cont H]
  end.
Tactic Notation "rename_layouts" "in" hyp(H) "with" tactic(cont) :=
  rename_layouts_core H cont.
Tactic Notation "rename_layouts" "in" hyp(H) :=
  rename_layouts in H with (fun x => idtac).

Ltac is_duplicate H :=
  match type of H with
  | use_layout_alg ?st = Some _ =>
      match goal with
      | H2 : NO_ENRICH (use_layout_alg st = Some _) |- _ =>
          idtac
      end
  | struct_layout_alg ?name ?fields ?repr = Some _ =>
      match goal with
      | H2 : NO_ENRICH (struct_layout_alg name fields repr = Some _) |- _ =>
          idtac
      end
  | union_layout_alg ?name ?variants ?repr = Some _ =>
      match goal with
      | H2 : NO_ENRICH (union_layout_alg name variants repr = Some _) |- _ =>
          idtac
      end
  end.

Section handle_duplicate.
  Context `{!LayoutAlg}.

  Lemma handle_duplicate_use_layout_alg_tac st ly0 ly1 :
    use_layout_alg st = Some ly0 →
    CACHED (use_layout_alg st = Some ly1) →
    ly0 = ly1.
  Proof.
    rewrite /CACHED.
    intros ??. by eapply syn_type_has_layout_inj.
  Qed.

  Lemma handle_duplicate_struct_layout_alg_tac name fields repr sl0 sl1 :
    struct_layout_alg name fields repr = Some sl0 →
    CACHED (struct_layout_alg name fields repr = Some sl1) →
    sl0 = sl1.
  Proof.
    rewrite /CACHED.
    intros ??. by simplify_eq.
  Qed.

  Lemma handle_duplicate_union_layout_alg_tac name variants repr ul0 ul1 :
    union_layout_alg name variants repr = Some ul0 →
    CACHED (union_layout_alg name variants repr = Some ul1) →
    ul0 = ul1.
  Proof.
    rewrite /CACHED.
    intros ??. by simplify_eq.
  Qed.

End handle_duplicate.

Ltac postprocess_new_struct_assum H Halg :=
  lazymatch type of Halg with
  | struct_layout_alg ?name ?field_lys ?repr = Some _ =>
    first [
      (* if this is a duplicate, remove it *)
      lazymatch goal with
      | H2 : CACHED (struct_layout_alg name field_lys repr = Some _) |- _ =>
        let Heq := fresh "_Heq" in
        specialize (handle_duplicate_struct_layout_alg_tac _ _ _ _ _ Halg H2) as Heq;
        subst_with Heq;
        clear Halg
      end
    |
      (* derive some information from the original assumption *)
      lazymatch type of H with
      | use_layout_alg _ = Some _  =>
        specialize_cache (use_layout_alg_wf _ _ H);
        specialize_cache (use_layout_alg_size _  _ H);
        specialize_cache (use_layout_alg_align _  _ H)
      | use_struct_layout_alg _ = Some _ =>
        specialize_cache (use_struct_layout_alg_wf _ _ H);
        specialize_cache (use_struct_layout_alg_size _  _ H)
      | use_enum_layout_alg _ = Some _ =>
        specialize_cache (use_enum_layout_alg_wf _ _ H);
        specialize_cache (use_enum_layout_alg_size _  _ H)
      end;
      rename_layouts in Halg with (fun Halg => enter_cache_unsafe Halg)
    ]
  end.
Ltac postprocess_new_union_assum H Halg :=
  lazymatch type of Halg with
  | union_layout_alg ?name ?variant_lys ?repr = Some _ =>
    first [
      (* if this is a duplicate, remove it *)
      lazymatch goal with
      | H2 : CACHED (union_layout_alg name variant_lys repr = Some _) |- _ =>
        let Heq := fresh "_Heq" in
        specialize (handle_duplicate_union_layout_alg_tac _ _ _ _ _ Halg H2) as Heq;
        subst_with Heq;
        clear Halg
      end
    |
      (* derive some information from the original assumption *)
      lazymatch type of H with
      | use_layout_alg _ = Some _ =>
        specialize_cache (use_layout_alg_wf _ _ H);
        specialize_cache (use_layout_alg_size _  _ H);
        specialize_cache (use_layout_alg_align _  _ H)
      | use_union_layout_alg _ = Some _ =>
        specialize_cache (use_union_layout_alg_wf _ _ H);
        specialize_cache (use_union_layout_alg_size _ _ H)
      end;
      rename_layouts in Halg with (fun Halg => enter_cache_unsafe Halg)
    ]
  end.


Ltac simplify_layout_alg_prepare H :=
  simpl in H;
  try lazymatch type of H with
  | syn_type_has_layout ?spec _ =>
      rewrite /syn_type_has_layout in H
  | struct_layout_spec_has_layout _ _ =>
      rewrite /struct_layout_spec_has_layout in H
  | union_layout_spec_has_layout _ _ =>
      rewrite /union_layout_spec_has_layout in H
  | enum_layout_spec_has_layout _ _ =>
      rewrite /enum_layout_spec_has_layout in H
  end;
  try lazymatch type of H with
  | use_layout_alg ?spec = Some _ =>
      unfold syn_type_of_sls, syn_type_of_els, syn_type_of_uls in H
  end.

Ltac simplify_layout_alg H ::=
  simplify_layout_alg_prepare H;
  (* simplify head *)
  try lazymatch type of H with
  | use_layout_alg ?spec = Some _ =>
      first [assert_is_atomic_st spec
      | let spec_eval := eval hnf in spec in
        change_no_check spec with spec_eval in H ]
  | use_struct_layout_alg ?spec = Some _ =>
      let spec_eval := eval hnf in spec in
      change_no_check spec with spec_eval in H
      (*is_var spec; rewrite /spec in H*)
  | use_union_layout_alg ?spec = Some _ =>
      let spec_eval := eval hnf in spec in
      change_no_check spec with spec_eval in H
  | use_enum_layout_alg ?spec = Some _ =>
      let spec_eval := eval hnf in spec in
      change_no_check spec with spec_eval in H
  end;
  first
  [
    (* Check for cached applications *)
    check_for_cached_layout H
  |
    (* Handle atomic alg applications *)
    lazymatch type of H with
    | use_layout_alg (ty_syn_type ?ty) = Some _ =>
        is_var ty;
        enter_cache H
    | use_layout_alg ?st = Some _ =>
        (*assert_is_atomic_st st;*)
        is_var st;
        specialize_cache (use_layout_alg_size _ _ H);
        specialize_cache (use_layout_alg_wf _ _ H);
        specialize_cache (use_layout_alg_align _ _ H);
        (* stop exploiting this further to prevent divergence *)
        rename_layouts in H with (fun H_n => enter_cache_unsafe H_n)
    end
  |
    (* Handle non-atomic alg applications *)
    lazymatch type of H with
    | use_struct_layout_alg ?sls = Some _ =>
        first [
          (* don't do anything *)
          assert_is_atomic_sls sls;
          specialize_cache (use_struct_layout_alg_size _ _ H);
          specialize_cache (use_struct_layout_alg_wf _ _ H);
          rename_layouts in H with (fun H_n => enter_cache H_n)
        |
          let Hrec := fresh "_Hrec" in
          let Halg := fresh "_Halg" in
          specialize (use_struct_layout_alg_inv _ _ H) as (? & Halg & Hrec);
          simpl in Halg;
          inv_multi_fields Hrec;
          postprocess_new_struct_assum H Halg;
          enter_cache H
        ]

    | use_enum_layout_alg ?els = Some _ =>
        first [
          (* don't do anything *)
          assert_is_atomic_els els;
          specialize_cache (use_enum_layout_alg_size _ _ H);
          specialize_cache (use_enum_layout_alg_wf _ _ H);
          (* stop exploiting this further to prevent divergence *)
          rename_layouts in H with (fun H_n => enter_cache H_n)
        |
          let Hrec := fresh "_Hrec" in
          let Halg_ul := fresh "_Halg" in
          let Halg_sl := fresh "_Halg" in
          specialize (use_enum_layout_alg_inv _ _ H) as (? & ? & Halg_ul & Halg_sl & Hrec);
          simpl in Halg_ul, Halg_sl;
          inv_multi_fields Hrec;
          postprocess_new_union_assum H Halg_ul;
          postprocess_new_struct_assum H Halg_sl;
          enter_cache H
        ]

    | use_union_layout_alg ?uls = Some _ =>
        first [
          (* don't do anything *)
          assert_is_atomic_uls uls;
          specialize_cache (use_union_layout_alg_size _ _ H);
          specialize_cache (use_union_layout_alg_wf _ _ H);
          rename_layouts in H with (fun H_n => enter_cache H_n)
        |
          let Hrec := fresh "_Hrec" in
          let Halg_ul := fresh "_Halg" in
          specialize (use_union_layout_alg_inv _ _ H) as (? & Halg_ul & Hrec);
          simpl in Halg_ul;
          inv_multi_fields Hrec;
          postprocess_new_union_assum H Halg_ul;
          enter_cache H
        ]

    | use_layout_alg (IntSynType ?it) = Some _ =>
        let Heq := fresh "_Heq" in
        apply syn_type_has_layout_int_inv in H as (Heq & ?);
        subst_with Heq
    | use_layout_alg (BoolSynType) = Some _ =>
        apply syn_type_has_layout_bool_inv in H;
        subst_with H
    | use_layout_alg (CharSynType) = Some _ =>
        apply syn_type_has_layout_char_inv in H;
        subst_with H
    | use_layout_alg PtrSynType = Some _ =>
        apply syn_type_has_layout_ptr_inv in H;
        subst_with H
    | use_layout_alg FnPtrSynType = Some _ =>
        apply syn_type_has_layout_fnptr_inv in H;
        subst_with H

    | use_layout_alg (StructSynType _ ?fields ?repr) = Some _ =>
        let Hrec := fresh "_Hrec" in
        let Halg := fresh "_Halg" in
        let Heq := fresh "_Heq" in
        specialize (syn_type_has_layout_struct_inv _ _ _ _ H) as (? & ? & Heq & Halg & Hrec);
        simpl in Halg;
        inv_multi_fields Hrec;
        subst_with Heq;

        postprocess_new_struct_assum H Halg;
        enter_cache H

    | use_layout_alg UnitSynType = Some _ =>
        apply syn_type_has_layout_unit_inv in H;
        subst_with H

    | use_layout_alg (ArraySynType ?st ?len) = Some _ =>
        let ly' := fresh "ly" in let H' := fresh "H" in
        let Heq := fresh "_Heq" in
        let Hsz := fresh "_Hsz" in
        apply syn_type_has_layout_array_inv in H as (ly' & H' & Heq & Hsz);
        subst_with Heq;
        enter_cache Hsz;
        simplify_layout_alg H'

    | use_layout_alg (UnsafeCell ?st) = Some _ =>
        apply syn_type_has_layout_unsafecell in H;
        simplify_layout_alg H
    | use_layout_alg (UntypedSynType ?ly) = Some _ =>
        let Heq := fresh "_Heq" in
        let Hwf := fresh "_Hwf" in
        let Hsz := fresh "_Hsz" in
        let Hib := fresh "_Hib" in
        apply syn_type_has_layout_untyped_inv in H as (Heq & Hwf & Hsz & Hib);
        subst_with Heq;
        enter_cache Hwf;
        enter_cache Hsz;
        enter_cache Hib

    | use_layout_alg (EnumSynType _ ?it ?variants ?repr) = Some ?ly =>
        let Hrec := fresh "_Hrec" in
        let Halg_ul := fresh "_Halg" in
        let Halg_sl := fresh "_Halg" in
        let Heq := fresh "_Heq" in
        specialize (syn_type_has_layout_enum_inv _ _ _ _ _ H) as (? & ? & ? & Halg_ul & Halg_sl & Heq & Hrec);
        simpl in Halg_ul, Halg_sl;
        inv_multi_fields Hrec;
        subst_with Heq;
        postprocess_new_union_assum H Halg_ul;
        postprocess_new_struct_assum H Halg_sl;
        enter_cache H

    | use_layout_alg (UnionSynType _ ?variants ?repr) = Some _ =>
        let Hrec := fresh "_Hrec" in
        let Halg_ul := fresh "_Halg" in
        let Heq := fresh "_Heq" in
        specialize (syn_type_has_layout_union_inv _ _ _ _ H) as (? & ? & Heq & Halg_ul & Hrec);
        simpl in Halg_ul;
        inv_multi_fields Hrec;
        subst_with Heq;
        postprocess_new_union_assum H Halg_ul;
        enter_cache H
    | use_layout_alg ?st = Some _ =>
        fail 1000 "Unimplemented case in simplify_layout_alg"
    end
  ].

(* TODO: we currently need this because we introduce syn_type equalities on generic args in preconditions of functions and not before, so we may get duplicates.
  Once this is fixed, we can remove this hack *)
Section remove_duplicates.
  Lemma remove_generic_layout_duplicate `{!typeGS Σ} {T_rt} (T_ty : type T_rt) ly1 ly2 :
    CACHED (use_layout_alg (ty_syn_type T_ty) = Some ly1) →
    CACHED (use_layout_alg (ty_syn_type T_ty) = Some ly2) →
    ly2 = ly1.
  Proof.
    intros Ha Hb. by eapply syn_type_has_layout_inj.
  Qed.
End remove_duplicates.

Ltac remove_duplicate_layout_assumptions :=
  repeat match goal with
  | H : CACHED (use_layout_alg (ty_syn_type ?T_ty) = Some ?Hly1),
      H2 : CACHED (use_layout_alg (ty_syn_type ?T_ty) = Some ?Hly2) |- _ =>
    is_var Hly1;
    is_var Hly2;
    is_var T_ty;
    let Heq := fresh "_Heq" in
    specialize (remove_generic_layout_duplicate _ _ _ H H2) as Heq;
    subst_with Heq;
    clear H2
  end.


Ltac inv_layout_alg :=
  repeat match goal with
  | H : syn_type_has_layout ?st ?ly |- _ =>
      change_no_check (use_layout_alg st = Some ly) in H
  | H : syn_type_is_layoutable _ |- _ =>
      let st := fresh "_st" in
      destruct H as [st H]
  | H : use_layout_alg _ = Some _ |- _ =>
      progress (simplify_layout_alg H)
  (* struct *)
  | H : struct_layout_spec_is_layoutable _ |- _ =>
      let st := fresh "_st" in
      destruct H as [st H]
  | H : struct_layout_spec_has_layout ?sls ?sl |- _ =>
      change_no_check (use_struct_layout_alg sls = Some sl) in H
  | H : use_struct_layout_alg _ = Some _ |- _ =>
      progress (simplify_layout_alg H)
  (* enum *)
  | H : enum_layout_spec_is_layoutable _ |- _ =>
      let st := fresh "_st" in
      destruct H as [st H]
  | H : enum_layout_spec_has_layout ?els ?el |- _ =>
      change_no_check (use_enum_layout_alg els = Some el) in H
  | H : use_enum_layout_alg _ = Some _ |- _ =>
      progress (simplify_layout_alg H)
  (* union *)
  | H : union_layout_spec_is_layoutable _ |- _ =>
      let st := fresh "_st" in
      destruct H as [st H]
  | H : union_layout_spec_has_layout ?uls ?ul |- _ =>
      change_no_check (use_union_layout_alg uls = Some ul) in H
  | H : use_union_layout_alg _ = Some _ |- _ =>
      progress (simplify_layout_alg H)
  end;
  remove_duplicate_layout_assumptions.
Global Arguments syn_type_has_layout : simpl never.

(** Solve [Inhabited] instances for inductives, used for enum declarations.
   We assume that arguments of inductive constructors have already been proved inhabited. *)
Ltac solve_inhabited :=
  repeat match goal with
  | |- Inhabited ?X =>
      first [apply _ | refine (populate _); econstructor; eapply inhabitant]
  end.
