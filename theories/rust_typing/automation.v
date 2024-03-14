From iris.proofmode Require Import coq_tactics reduction string_ident.
From refinedrust Require Export type.
From lithium Require Export all.
From lithium Require Import hooks.
From refinedrust.automation Require Import ident_to_string lookup_definition.
From refinedrust Require Import int programs program_rules functions references products arrays enum.
(* Important: import proof_state last as it overrides some Lithium tactics *)
From refinedrust.automation Require Export simpl solvers proof_state.
Set Default Proof Using "Type".


(** * Registering extensions to Lithium *)
(** More automation for modular arithmetics. *)
Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

Global Hint Transparent ly_size : solve_protected_eq_db.
Ltac solve_protected_eq_hook ::=
  lazymatch goal with
  (* unfold constants for function types *)
  | |- @eq (_ → fn_params) ?a (λ x, _) =>
    lazymatch a with
    | (λ x, _) => idtac
    | _ =>
      let h := get_head a in
      unfold h;
      (* necessary to reduce after unfolding because of the strict
      opaqueness settings for unification *)
      liSimpl
    end
  (* Try to simplify as much as possible *)
  (*| |- pcons _ _ = pcons _ _ => *)
      (*repeat f_equiv;*)
      (*match goal with *)
      (*| |- @pnil _ _ = @pnil _ _ => reflexivity*)
      (*| |- _ => idtac*)
      (*end*)

  (* don't fail if nothing matches *)
  | |- _ => idtac
  end.

Ltac can_solve_hook ::= first [
  match goal with
  | |- _ ≠ _ => discriminate
  end | open_cache; solve_goal].

Ltac liTrace_hook info ::=
  add_case_distinction_info info.

Ltac rep_check_backtrack_point ::=
  lazymatch goal with
  | |- BACKTRACK_POINT ?P => idtac
  | |- envs_entails _ ?P =>
      lazymatch P with
      | typed_stmt _ _ _ _ _ _ _ => idtac
      | typed_val_expr _ _ _ _ _ => idtac
      | typed_call _ _ _ _ _ _ _ _ _ => idtac
      (* TODO maybe also typed_assert etc *)
      end
  end.

Ltac liExtensible_to_i2p_hook P bind cont ::=
  lazymatch P with
  | subsume_full ?E ?L ?step ?P ?Q ?T =>
      cont uconstr:(((_ : SubsumeFull E L step P Q) T))
  | relate_list ?E ?L ?ig ?l1 ?l2 ?i0 ?R ?T =>
      cont uconstr:(((_ : RelateList E L ig l1 l2 i0 R) T))
  | relate_hlist ?E ?L ?ig ?Xs ?l1 ?l2 ?i0 ?R ?T =>
      cont uconstr:(((_ : RelateHList E L ig Xs l1 l2 i0 R) T))
  | fold_list ?E ?L ?ig ?l ?i0 ?P ?T =>
      cont uconstr:(((_ : FoldList E L ig l i0 P) T))
  | typed_value ?v ?π ?T =>
      cont uconstr:(((_ : TypedValue v π) T))
  | typed_bin_op ?π ?E ?L ?v1 ?ty1 ?v2 ?ty2 ?o ?ot1 ?ot2 ?T =>
      cont uconstr:(((_ : TypedBinOp π E L v1 ty1 v2 ty2 o ot1 ot2) T))
  | typed_un_op ?π ?E ?L ?v ?ty ?o ?ot ?T =>
      cont uconstr:(((_ : TypedUnOp π E L v ty o ot) T))
  | typed_call ?π ?E ?L ?eκs ?v ?P ?vl ?tys ?T =>
      cont uconstr:(((_ : TypedCall π E L eκs v P vl tys) T))
  | typed_place ?π ?E ?L ?l ?lt ?r ?bmin0 ?b ?P ?T =>
      cont uconstr:(((_ : TypedPlace E L π l lt r bmin0 b P) T))
  | typed_if ?E ?L ?v ?P ?T1 ?T2 =>
      cont uconstr:(((_ : TypedIf E L v P) T1 T2))
  | typed_switch ?π ?E ?L ?v ?rt ?ty ?r ?it ?m ?ss ?def ?fn ?R =>
      cont uconstr:(((_ : TypedSwitch π E L v rt ty r it) m ss def fn R))
  | typed_assert ?π ?E ?L ?v ?ty ?r ?s ?fn ?R ?ϝ =>
      cont uconstr:(((_ : TypedAssert π E L v ty r) s fn R ϝ))
  | typed_read_end ?π ?E ?L ?l ?ty ?r ?b2 ?bmin ?br ?ot ?T =>
      cont uconstr:(((_ : TypedReadEnd π E L l ty r b2 bmin br ot) T))
  | typed_write_end ?π ?E ?L ?ot ?v1 ?ty1 ?r1 ?b2 ?bmin ?br ?l2 ?lt2 ?r2 ?T =>
      cont uconstr:(((_ : TypedWriteEnd π E L ot v1 ty1 r1 b2 bmin br l2 lt2 r2) T))
  | typed_borrow_mut_end ?π ?E ?L ?κ ?l ?ty ?r ?b2 ?bmin ?T =>
      cont uconstr:(((_ : TypedBorrowMutEnd π E L κ l ty r b2 bmin) T))
  | typed_borrow_shr_end ?π ?E ?L ?κ ?l ?ty ?r ?b2 ?bmin ?T =>
      cont uconstr:(((_ : TypedBorrowShrEnd π E L κ l ty r b2 bmin) T))
  | typed_addr_of_mut_end ?π ?E ?L ?l ?lt ?r ?b2 ?bmin ?T =>
      cont uconstr:(((_ : TypedAddrOfMutEnd π E L l lt r b2 bmin) T))
  | cast_ltype_to_type ?E ?L ?lt ?T =>
      cont uconstr:(((_ : CastLtypeToType E L lt) T))
  | typed_context_fold ?AI ?π ?E ?L ?m ?tctx ?acc ?T =>
      cont uconstr:(((_ : TypedContextFold AI π E L m tctx acc) T))
  | typed_context_fold_step ?AI ?π ?E ?L ?m ?l ?lt ?r ?tctx ?acc ?T =>
      cont uconstr:(((_ : TypedContextFoldStep AI π E L m l lt r tctx acc) T))
  | typed_annot_expr ?π ?E ?L ?n ?a ?v ?P ?T =>
      cont uconstr:(((_ : TypedAnnotExpr π E L n a v P) T))
  | prove_with_subtype ?E ?L ?step ?pm ?P ?T =>
      cont uconstr:(((_ : ProveWithSubtype E L step pm P) T))
  | owned_subtype ?π ?E ?L ?pers ?r1 ?r2 ?ty1 ?ty2 ?T =>
      cont uconstr:((_ : OwnedSubtype π E L pers r1 r2 ty1 ty2) T)
  | owned_subltype_step ?π ?E ?L ?l ?r1 ?r2 ?lt1 ?lt2 ?T =>
      cont uconstr:((_ : OwnedSubltypeStep π E L l r1 r2 lt1 lt2) T)
  | weak_subtype ?E ?L ?r1 ?r2 ?ty1 ?ty2 ?T =>
      cont uconstr:((_ : Subtype E L r1 r2 ty1 ty2) T)
  | weak_subltype ?E ?L ?k ?r1 ?r2 ?lt1 ?lt2 ?T =>
      cont uconstr:((_ : SubLtype E L k r1 r2 lt1 lt2) T)
  | mut_subtype ?E ?L ?ty1 ?ty2 ?T =>
      cont uconstr:((_ : MutSubtype E L ty1 ty2) T)
  | mut_eqtype ?E ?L ?ty1 ?ty2 ?T =>
      cont uconstr:((_ : MutEqtype E L ty1 ty2) T)
  | mut_subltype ?E ?L ?lt1 ?lt2 ?T =>
      cont uconstr:((_ : MutSubLtype E L lt1 lt2) T)
  | mut_eqltype ?E ?L ?lt1 ?lt2 ?T =>
      cont uconstr:((_ : MutEqLtype E L lt1 lt2) T)
  | stratify_ltype ?π ?E ?L ?mu ?mdu ?ma ?ml ?l ?lt ?r ?b ?T =>
      cont uconstr:(((_ : StratifyLtype π E L mu mdu ma ml l lt r b) T))
  | stratify_ltype_unblock ?π ?E ?L ?ma ?l ?lt ?r ?b ?T =>
      cont uconstr:(((_ : StratifyLtype π E L _ _ _ StratifyUnblockOp l lt r b) T))
  | stratify_ltype_extract ?π ?E ?L ?Ma ?l ?lt ?r ?b ?κ ?T =>
      cont uconstr:(((_ : StratifyLtype π E L _ _ _ (StratifyExtractOp κ) l lt r b) T))
  | stratify_ltype_post_hook ?π ?E ?L ?ml ?l ?lt ?r ?b ?T =>
      cont uconstr:(((_ : StratifyLtypePostHook π E L ml l lt r b) T))
  | resolve_ghost ?π ?E ?L ?m ?lb ?l ?lt ?b ?r ?T =>
      cont uconstr:(((_ : ResolveGhost π E L m lb l lt b r) T))
  | find_observation ?rt ?γ ?mode ?T =>
      cont uconstr:(((_ : FindObservation rt γ mode) T))
  | typed_on_endlft ?π ?E ?L ?κ ?worklist ?T =>
      cont uconstr:(((_ : TypedOnEndlft π E L κ worklist) T))
  | typed_on_endlft_trigger ?E ?L ?key ?P ?T =>
      cont uconstr:(((_ : TypedOnEndlftTrigger E L key P) T))
  | introduce_with_hooks ?E ?L ?P ?T =>
      cont uconstr:(((_ : IntroduceWithHooks E L P) T))
  | prove_place_cond ?E ?L ?b ?lt1 ?lt2 ?T =>
      cont uconstr:(((_ : ProvePlaceCond E L b lt1 lt2) T))
  | prove_place_rfn_cond ?b ?b1 ?r1 ?r2 ?T =>
      cont uconstr:(((_ : ProvePlaceRfnCond b b1 r1 r2) T))
  | typed_option_map ?o ?Φ ?d ?T =>
      cont uconstr:(((_ : TypedOptionMap o Φ d) T))
  | stratify_ltype_array_iter ?π ?E ?L ?mu ?mdu ?ma ?ml ?l ?ig ?def ?len ?iml ?rs ?bk ?T =>
      cont uconstr:(((_ : StratifyLtypeArrayIter π E L mu mdu ma ml l ig def len iml rs bk) T))
  | typed_array_access ?π ?E ?L ?base ?offset ?st ?lt ?r ?k ?T =>
      cont uconstr:(((_ : TypedArrayAccess π E L base offset st lt r k) T))
  | resolve_ghost_iter ?π ?E ?L ?rm ?lb ?l ?st ?lts ?b ?rs ?ig ?i0 ?T =>
      cont uconstr:(((_ : ResolveGhostIter π E L rm lb l st lts b rs ig i0) T))
  end.


(** * Loopy stuff *)
(* using our own list type here in order to be able to put iProp's in it (universe troubles) *)
#[universes(polymorphic)]
Inductive poly_list (T : Type) : Type :=
  | PolyNil
  | PolyCons (x : T) (l : poly_list T).
Arguments PolyNil {_}.
Arguments PolyCons {_}.

#[universes(polymorphic)]
Inductive poly_option (T : Type) : Type :=
  | PolyNone
  | PolySome (x : T).
Arguments PolyNone {_}.
Arguments PolySome {_}.

(* Wrapper to store predicates of arbitrary arity. *)
Definition wrap_inv {T} (x : T) := existT (P := id) _ x.
(* Type of loop invariants: a predicate on the refinements, and a predicate on the lifetime contexts *)
Definition bb_inv_t := (sigT (@id Type) * sigT (@id Type))%type.
(* Type of the loop invariant map we keep in the context *)
Definition bb_inv_map_t := poly_list (var_name * bb_inv_t)%type.
Inductive bb_inv_map_marker : bb_inv_map_t → Type :=
  BB_INV_MAP (M : bb_inv_map_t) : bb_inv_map_marker M.

(** Given a [runtime_function] [rfn], get the list of stack locations as a [constr]. *)
Ltac gather_locals rfn :=
  match rfn with
  | Build_runtime_function ?fn ?l =>
    eval simpl in (map fst l)
  end.

(** Find the invariant for basic block [loop_bb] in the invariant map [loop_inv_map].
  Returns a uconstr option with the result. *)
Ltac find_bb_inv loop_inv_map loop_bb :=
  match loop_inv_map with
  | PolyCons (loop_bb, ?inv) _ =>
    constr:(PolySome inv)
  | PolyCons (_, _) ?loop_inv_map2 =>
    find_bb_inv loop_inv_map2 loop_bb
  | PolyNil =>
    constr:(@PolyNone bb_inv_t)
  end.

(** Find the type assignment for the location [loc] in the [env : env], and return it as a [constr]. *)
Ltac find_type_assign_in_env loc env :=
  lazymatch env with
  | Enil => fail 10 "find_type_assign_in_env: no " loc " in env"
  | Esnoc ?env2 _ (loc ◁ₗ[?π, ?b] ?r @ ?lt)%I =>
      constr:((loc ◁ₗ[π, b] r @ lt)%I)
  | Esnoc ?env2 _ _ => find_type_assign_in_env loc env2
  end.

(** Making strings from numbers *)
Definition digit_to_ascii (n : nat) : ascii :=
  match n with
  | 0 => Ascii false false false false true true false false
  | 1 => Ascii true false false false true true false false
  | 2 => Ascii false true false false true true false false
  | 3 => Ascii true true false false true true false false
  | 4 => Ascii false false true false true true false false
  | 5 => Ascii true false true false true true false false
  | 6 => Ascii false true true false true true false false
  | 7 => Ascii true true true false true true false false
  | 8 => Ascii false false false true true true false false
  | 9 => Ascii true false false true true true false false
  | _ => Ascii false false false false true true false false
  end.
Definition nat_to_string (n : nat) : string.
Proof.
  refine (string_rev _).
  refine (lt_wf_rec n (λ _, string) _).
  intros m rec.
  refine (match m as m' return m = m' → _ with
          | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9  => λ _, String (digit_to_ascii m) EmptyString
          | _ => λ Heq, _
          end eq_refl).
  refine (String (digit_to_ascii (m `mod` 10)) (rec (m `div` 10) _)).
  abstract(apply Nat.div_lt; lia).
Defined.

(** Generates [count] successive fresh identifiers as Coq strings with prefix [prefix].
  Returns a Coq list [list string]. *)
(* TODO: potentially take a list of suffix strings, so that we can we also get the variable names for the refinements, e.g. x, y? *)
Ltac get_idents_rec prefix count acc :=
  match count with
  | 0%nat => constr:(acc)
  | (S ?n)%nat =>
      (* need to prefix with some symbol because just a number is not a valid ident *)
      let count_str := eval cbv in (append "_" (nat_to_string n)) in
      string_to_ident_cps count_str ltac:(fun count_ident =>
      (* make a fresh identifier *)
      let Hident := fresh prefix count_ident in
      (* convert to string so we can store it *)
      let Hident_str := constr:(ident_to_string! Hident) in
      let acc := constr:(Hident_str :: acc) in
      get_idents_rec prefix constr:(n) constr:(acc))
  end.

(** Finds the type assignments for the locations [local_locs] in the spatial context [spatial_env],
  and abstracts their refinements to existentials [x_1, ..., x_n] whose names get picked from the list [ex_names : list string].
  It needs to hold that [length ex_names ≥ length local_locs = n].
  [base_app] is the name of a context item which will be specialized with the existentially abstracted refinements, to result in a fully applied term [base_app_specialized = base_app x_1 ... x_n] of type [iProp].
  [base] is a term of type [iProp].

  The tactic instantiates the current goal with the proposition claiming ownership of the locals, [base_app_specialized], and [base], with the existentials quantified in the term.

  The implementation of this is currently quite hacky, mainly to work around Ltac's bad support for working with open terms. *)
Ltac build_local_sepconj local_locs spatial_env ex_names base base_app :=
  lazymatch local_locs with
  | nil =>
      exact ((base ∗ base_app)%I)
  | cons ?local ?local_locs2 =>
      let own_prop := find_type_assign_in_env local spatial_env in

      (* get the name for this *)
      lazymatch ex_names with
      | nil => fail 10 "not enough names provided"
      | ?name :: ?ex_names2 =>
        string_to_ident_cps name ltac:(fun ident =>

        (* create the type with existentially abstracted refinement *)
        let abstracted_prop :=
          lazymatch own_prop with
          | (?loc ◁ₗ[?π, ?b] ?r @ ?lt)%I =>
              (* crucial: we specialize a hypothesis _below_ the binder here in order to work around Ltac's restrictions for working with open terms *)
              constr:((∃ ident, loc ◁ₗ[π, b] ident @ lt ∗
                ltac:(specialize (base_app ident); build_local_sepconj local_locs2 spatial_env ex_names2 base base_app))%I)
          end
        in
        exact (abstracted_prop))
    end
  end.

(** Composes the loop invariant from the invariant [inv : bb_inv_t] (a constr),
  the runtime function [FN : runtime_function], the current Iris environment [env : env],
  and the current contexts [current_E : elctx], [current_L : llctx],
  and poses it with the identifier [Hinv]. *)
Ltac pose_loop_invariant Hinv FN inv envs current_E current_L :=
  (* find Σ *)
  let Σ :=
    let tgs := constr:(_ : typeGS _) in
    match type of tgs with
    | typeGS ?Σ => Σ
    end
  in
  (* get spatial env *)
  let envs := eval hnf in envs in
  let spatial_env :=
    match envs with
    | Envs _ ?spatial _ => spatial
    | _ => fail 10 "infer_loop_invariant: could not determine spatial env"
    end
  in

  (* extract the invariants *)
  let functional_inv := match inv with
                       | (wrap_inv ?inv, _) => uconstr:(inv)
                       end
  in
  let llctx_inv := match inv with
                   | (_, wrap_inv ?inv) => uconstr:(inv)
                   end
  in

  (* find the locals in the context *)
  let FN := eval hnf in FN in
  let local_locs := gather_locals FN in
  (* generate names for the existentially abstracted refinements *)
  let num_locs := eval cbv in (length local_locs) in
  let names := get_idents_rec ident:(r) constr:(num_locs) constr:(@nil string) in

  pose (Hinv :=
    λ (E : elctx) (L : llctx),
    ltac:(
      (* specialize the lifetime ctx invariant *)
      let HEL := fresh "Hel" in

      (*pose (HEL := llctx_inv);*)
      (*specialize (HEL E L);*)

      pose (HEL := (E = current_E ∧ L = current_L));

      (* pose the loop invariant as a local hypothesis so we can specialize it while building the term *)
      let Ha := fresh "Hinv" in
      pose (Ha := functional_inv);

      build_local_sepconj local_locs spatial_env names constr:(((True ∗ ⌜HEL⌝)%I: iProp Σ)) Ha
  ));
  (* get rid of all the lets we introduced *)
  simpl in Hinv.


(** * Main automation tactics *)
Section automation.
  Context `{!typeGS Σ}.

  Lemma tac_simpl_subst E L π xs s fn R ϝ :
    typed_stmt π E L (W.to_stmt (W.subst_stmt xs s)) fn R ϝ -∗
    typed_stmt π E L (subst_stmt xs (W.to_stmt s)) fn R ϝ.
  Proof. rewrite W.to_stmt_subst. auto. Qed.

  Lemma tac_trigger_tc {A} (a : A) (H : A → Prop) (HP : H a) (T : A → iProp Σ) :
    T a ⊢ trigger_tc H T.
  Proof. iIntros "HT". iExists a. iFrame. done. Qed.
End automation.

Ltac liRIntroduceLetInGoal :=
  lazymatch goal with
  | |- @envs_entails ?PROP ?Δ ?P =>
    let H := fresh "GOAL" in
    lazymatch P with
    | @bi_wand ?PROP ?Q ?T =>
      pose H := (LET_ID T); change_no_check (@envs_entails PROP Δ (@bi_wand PROP Q H))
    | @typed_val_expr ?Σ ?tG ?π ?E ?L ?e ?T =>
      pose (H := LET_ID T); change_no_check (@envs_entails PROP Δ (@typed_val_expr Σ tG π E L e H))
    | @typed_write ?Σ ?tG ?π ?E ?L ?e ?ot ?v ?rt ?ty ?r ?T =>
      pose (H := LET_ID T); change_no_check (@envs_entails PROP Δ (@typed_write Σ tG π E L e ot v rt ty r H))
    (* NOTE: these two guys really hurt Qed performance. Not a good idea at all! *)
    (*| @typed_place ?Σ ?tG ?π ?E ?L ?l ?rto ?lt ?r ?b ?bmin ?P ?T =>*)
      (*pose (H := LET_ID T); change_no_check (@envs_entails PROP Δ (@typed_place Σ tG π E L l rto lt r b bmin P H))*)
    (*| @typed_context_fold ?Σ ?tG ?Acc ?P ?M ?π ?E ?L ?m ?tcx ?acc ?T =>*)
      (*pose (H := LET_ID T);*)
      (*change_no_check (@envs_entails PROP Δ (@typed_context_fold Σ tG Acc P M π E L m tcx acc H))*)
    | @typed_bin_op ?Σ ?tG ?π ?E ?L ?v1 ?P1 ?v2 ?P2 ?op ?ot1 ?ot2 ?T =>
      pose (H := LET_ID T); change_no_check (@envs_entails PROP Δ (@typed_bin_op Σ tG π E L v1 P1 v2 P2 op ot1 ot2 H))
    end
  end.

Ltac liRInstantiateEvars_hook := idtac.
Ltac liRInstantiateEvars :=
  liRInstantiateEvars_hook;
  lazymatch goal with
  | |- (_ < protected ?H)%nat ∧ _ =>
    (* We would like to use [liInst H (S (protected (EVAR_ID _)))],
      but this causes a Error: No such section variable or assumption
      at Qed. time. Maybe this is related to https://github.com/coq/coq/issues/9937 *)
    instantiate_protected H ltac:(fun H => instantiate (1:=((S (protected (EVAR_ID _))))) in (value of H))
  (* For some reason [solve_protected_eq] will sometimes not manage to do this.. *)
  | |- (protected ?a = ?b +:: ?c) ∧ _ =>
    instantiate_protected a ltac:(fun H =>  instantiate (1:= (protected (EVAR_ID _) +:: protected (EVAR_ID _))) in (value of H))
    (* NOTE: Important: We create new evars, instead of instantiating directly with [b] or [c].
        If [b] or [c] contains another evar, the let-definition for that will not be in scope, which can create trouble at Qed. time *)
  | |- (protected ?a = ?b -:: ?c) ∧ _ =>
    instantiate_protected a ltac:(fun H =>  instantiate (1:= (protected (EVAR_ID _) -:: protected (EVAR_ID _))) in (value of H))
  (* in this case, we do not want it to instantiate the evar for [a], but rather directly instantiate it with the only possible candidate.
     (if the other side also contains an evar, we would be instantiating less than we could otherwise) *)
  | |- (@eq (hlist _ []) _ (protected ?a)) ∧ _ =>
      instantiate_protected a ltac:(fun H => instantiate (1:= +[]) in (value of H))
      (*liInst a (+[])*)
  | |- (@eq (hlist _ []) (protected ?a) _) ∧ _ =>
      instantiate_protected a ltac:(fun H => instantiate (1 := +[]) in (value of H))
      (*liInst a (+[])*)

  (* TODO why is this sometimes not done automatically by Lithium? *)
  (*| |- (protected ?H = ?bla) ∧ _ =>*)
      (*liInst H bla*)

    (* TODO: figure out how/when to instantiate evars  *)
  | |- envs_entails _ (subsume (_ ◁ₗ[?π, ?b] ?r @ ?lt) (_ ◁ₗ[_, _] _ @ (protected ?H)) _) => liInst H lt
  | |- envs_entails _ (subsume (_ ◁ₗ[?π, ?b] ?r @ ?lt) (_ ◁ₗ[_, protected ?H] _ @ _) _) => liInst H b
  end.

(** Goto [goto_bb] *)
Ltac liRGoto goto_bb :=
  lazymatch goal with
  | |- envs_entails ?Δ (typed_stmt ?π ?E ?L (Goto _) ?fn ?R ?ϝ) =>
      first [
        (* try to find an inductive hypothesis we obtained previously *)
        notypeclasses refine (tac_fast_apply (type_goto_precond E L π _ _ fn R ϝ) _);
        progress liFindHyp FICSyntactic
      | (* if we jump to a loop head, initiate Löb induction *)
        lazymatch goal with
        | H : bb_inv_map_marker ?LOOP_INV_MAP |- _ =>
            let loop_inv_map := eval hnf in LOOP_INV_MAP in
            (* find the loop invariant *)
            let inv := find_bb_inv loop_inv_map goto_bb in
            let inv := match inv with
            | PolySome ?inv => inv
            | PolyNone =>
                (* we are not jumping to a loop head *)
                fail 1 "infer_loop_invariant: no loop invariant found"
            end in
            (* pose the composed loop invariant *)
            string_to_ident_cps goto_bb ltac:(fun bb_ident =>
            let Hinv := fresh "Hinv_" bb_ident in
            pose_loop_invariant Hinv fn inv Δ E L;
            (* finally initiate Löb *)
            notypeclasses refine (tac_fast_apply (typed_goto_acc _ _ _ _ _ Hinv goto_bb _ _ _) _);
              [unfold_code_marker_and_compute_map_lookup| ]
            )
        end
      | (* do a direct jump *)
        notypeclasses refine (tac_fast_apply (type_goto E L π _ fn R _ ϝ _) _);
          [unfold_code_marker_and_compute_map_lookup|]
      ]
  end.

Ltac liRStmt :=
  lazymatch goal with
  | |- envs_entails ?Δ (typed_stmt ?π ?E ?L ?s ?fn ?R ?ϝ) =>
    lazymatch s with
    | subst_stmt ?xs ?s =>
      let s' := W.of_stmt s in
      change (subst_stmt xs s) with (subst_stmt xs (W.to_stmt s'));
      refine (tac_fast_apply (tac_simpl_subst E L π _ _ fn R ϝ) _); simpl; unfold W.to_stmt, W.to_expr
    | _ =>
      let s' := W.of_stmt s in
      lazymatch s' with
      | W.AssignSE _ _ _ _ _ => notypeclasses refine (tac_fast_apply (type_assign E L π _ _ _ _ fn R _ ϝ) _)
      | W.Return _ => notypeclasses refine (tac_fast_apply (type_return E L π _ fn R ϝ) _)
      | W.IfS _ _ _ _ _ => notypeclasses refine (tac_fast_apply (type_if E L π _ _ _ fn R _ ϝ) _)
      | W.Switch _ _ _ _ _ => notypeclasses refine (tac_fast_apply (type_switch E L π _ _ _ _ _ fn R ϝ) _)
      | W.Assert _ _ _ => notypeclasses refine (tac_fast_apply (type_assert E L _ _ fn π R ϝ) _)
      | W.Goto ?bid => liRGoto bid
      | W.ExprS _ _ => notypeclasses refine (tac_fast_apply (type_exprs E L _ _ fn R π ϝ) _)
      | W.SkipS _ => notypeclasses refine (tac_fast_apply (type_skips' E L _ fn R π ϝ) _)
      | W.StuckS => exfalso
      | W.AnnotStmt _ (StartLftAnnot ?κ ?κs) _ => notypeclasses refine (tac_fast_apply (type_startlft E L κ κs _ fn R π ϝ) _)
      | W.AnnotStmt _ (AliasLftAnnot ?κ ?κs) _ => notypeclasses refine (tac_fast_apply (type_alias_lft E L κ κs _ fn R π ϝ) _)
      | W.AnnotStmt _ (EndLftAnnot ?κ) _ => notypeclasses refine (tac_fast_apply (type_endlft E L π κ _ fn R ϝ) _)
      | W.AnnotStmt _ (StratifyContextAnnot) _ => notypeclasses refine (tac_fast_apply (type_stratify_context_annot E L π _ fn R ϝ) _)
      | W.AnnotStmt _ (CopyLftNameAnnot ?n1 ?n2) _ => notypeclasses refine (tac_fast_apply (type_copy_lft_name π E L n1 n2 _ fn R ϝ) _)
      | W.AnnotStmt _ (DynIncludeLftAnnot ?n1 ?n2) _ => notypeclasses refine (tac_fast_apply (type_dyn_include_lft π E L n1 n2 _ fn R ϝ) _)
      | W.AnnotStmt _ (ExtendLftAnnot ?κ) _ => notypeclasses refine (tac_fast_apply (type_extendlft E L π κ _ fn R ϝ) _)
      | _ => fail "do_stmt: unknown stmt" s
      end
    end
  end.

Ltac liRIntroduceTypedStmt :=
  lazymatch goal with
  | |- @envs_entails ?PROP ?Δ (introduce_typed_stmt ?π ?E ?L ?ϝ ?fn ?lsa ?lsv ?lya ?lyv ?R) =>
    iEval (rewrite /introduce_typed_stmt /to_runtime_function /subst_function !fmap_insert fmap_empty; simpl_subst);
      lazymatch goal with
      | |- @envs_entails ?PROP ?Δ (@typed_stmt ?Σ ?tG ?π ?E ?L ?s ?fn ?R ?ϝ) =>
        let Hfn := fresh "FN" in
        let HR := fresh "R" in
        pose (Hfn := (CODE_MARKER fn));
        pose (HR := (RETURN_MARKER R));
        change_no_check (@envs_entails PROP Δ (@typed_stmt Σ tG π E L s Hfn HR ϝ));
        iEval (simpl) (* To simplify f_init *)
        (*notypeclasses refine (tac_fast_apply (tac_simplify_elctx _ _ _ _ _ _ _ _ _) _); [simplify_elctx | ]*)
      end
  end.

Ltac liRExpr :=
  lazymatch goal with
  | |- envs_entails ?Δ (typed_val_expr ?π ?E ?L ?e ?T) =>
    let e' := W.of_expr e in
    lazymatch e' with
    | W.Val _ => notypeclasses refine (tac_fast_apply (type_val E L _ π T) _)
    | W.Loc _ => notypeclasses refine (tac_fast_apply (type_val E L _ π T) _)
    | W.Use _ _ true _ => notypeclasses refine (tac_fast_apply (type_use E L _ T _ _ π) _)
    | W.Borrow Mut _ _ _ => notypeclasses refine (tac_fast_apply (type_mut_bor E L T _ π _ _) _)
    | W.Borrow Shr _ _ _ => notypeclasses refine (tac_fast_apply (type_shr_bor E L T _ π _ _) _)
    | W.AddrOf _ _ => notypeclasses refine (tac_fast_apply (type_mut_addr_of π E L _ T) _)
    | W.BinOp _ _ _ _ _ => notypeclasses refine (tac_fast_apply (type_bin_op E L _ _ _ _ _ π T) _)
    | W.UnOp _ _ _ => notypeclasses refine (tac_fast_apply (type_un_op E L _ _ _ π T) _)
    | W.Call _ _ _ => notypeclasses refine (tac_fast_apply (type_call E L π T _ _ _) _)
    | W.AnnotExpr _ ?a _ => notypeclasses refine (tac_fast_apply (type_annot_expr E L _ a _ π T) _)
    | W.StructInit ?sls ?init => notypeclasses refine (tac_fast_apply (type_struct_init π E L sls _ T) _)
    | W.EnumInit ?els ?variant ?rsty ?init => notypeclasses refine (tac_fast_apply (type_enum_init π E L els variant rsty _ T) _)
    | W.IfE _ _ _ _ => notypeclasses refine (tac_fast_apply (type_ife E L _ _ _ π T) _)
    | W.LogicalAnd _ _ _ _ _ => notypeclasses refine (tac_fast_apply (type_logical_and E L _ _ _ _ π T) _)
    | W.LogicalOr _ _ _ _ _ => notypeclasses refine (tac_fast_apply (type_logical_or E L _ _ _ _ π T) _)
    | _ => fail "do_expr: unknown expr" e
    end
  end.

(* Initialize context folding by gathering up the type context. *)
Ltac gather_location_list env :=
  match env with
  | Enil => uconstr:([])
  | Esnoc ?env' _ ?p =>
      let rs := gather_location_list env' in
      lazymatch p with
      | (?l ◁ₗ[?π, Owned false] ?r @ ?lty)%I =>
          uconstr:(l :: rs)
      | _ => uconstr:(rs)
      end
  end.
Ltac liRContextStratifyInit :=
  lazymatch goal with
  | |- envs_entails ?envs (typed_pre_context_fold ?π ?E ?L (CtxFoldStratifyAllInit) ?T) =>
      let envs := eval hnf in envs in
      match envs with
      | Envs _ ?spatial _ =>
          let tctx := gather_location_list spatial in
          notypeclasses refine (tac_fast_apply (typed_context_fold_stratify_init tctx π E L T) _)
      | _ => fail 1000 "gather_tctx: cannot determine Iris context"
      end
  end.
Ltac liRContextStratifyStep :=
  lazymatch goal with
  | |- envs_entails _ (typed_context_fold_step ?AI ?π ?E ?L (CtxFoldStratifyAll) ?l ?lt ?r ?tctx ?acc ?T) =>
    notypeclasses refine (tac_fast_apply (typed_context_fold_step_stratify π E L l lt r tctx _ _ T) _)
  end.

Ltac liRContextExtractInit :=
  lazymatch goal with
  | |- envs_entails ?envs (typed_pre_context_fold ?π ?E ?L (CtxFoldExtractAllInit ?κ) ?T) =>
      let envs := eval hnf in envs in
      match envs with
      | Envs _ ?spatial _ =>
          let tctx := gather_location_list spatial in
          notypeclasses refine (tac_fast_apply (typed_context_fold_extract_init tctx π E L κ T) _)
      | _ => fail 1000 "gather_tctx: cannot determine Iris context"
      end
  end.
Ltac liRContextExtractStep :=
  lazymatch goal with
  | |- envs_entails _ (typed_context_fold_step ?AI ?π ?E ?L (CtxFoldExtractAll ?κ) ?l ?lt ?r ?tctx ?acc ?T) =>
    notypeclasses refine (tac_fast_apply (typed_context_fold_step_extract π E L l lt r tctx _ _ κ T) _)
  end.

(** Endlft trigger automation for [Inherit] context items *)
Ltac gather_on_endlft_worklist κ env :=
  match env with
  | Enil => uconstr:([])
  | Esnoc ?env' _ ?p =>
      let rs := gather_on_endlft_worklist κ env' in
      lazymatch p with
      | (Inherit κ ?key ?P)%I =>
          uconstr:(((existT _ key : sigT (@id Type)), P) :: rs)
      | _ => uconstr:(rs)
      end
  end.
Ltac liROnEndlftTriggerInit :=
  lazymatch goal with
  | |- envs_entails ?envs (typed_on_endlft_pre ?π ?E ?L ?κ ?T) =>
      let envs := eval hnf in envs in
      match envs with
      | Envs _ ?spatial _ =>
          let worklist := gather_on_endlft_worklist κ spatial in
          notypeclasses refine (tac_fast_apply (typed_on_endlft_pre_init worklist π E L κ T) _)
      | _ => fail 1000 "liROnEndlftTriggerInit: cannot determine Iris context"
      end
  end.

Ltac liRJudgement :=
  lazymatch goal with
    (* place finish *)
    | |- envs_entails _ (typed_place_finish ?π ?E ?L _ _ _ _ _ _ _ _ _ ?T) =>
      (* simplify eqcasts and the match on strong/weak branch *)
      cbn
    (* write *)
    | |- envs_entails _ (typed_write ?π ?E ?L _ _ _ ?ty ?r ?T) =>
        notypeclasses refine (tac_fast_apply (type_write E L T _ _ _ _ _ ty r π _) _); [ solve [refine _ ] |]
    (* read *)
    | |- envs_entails _ (typed_read ?π ?E ?L _ _ ?T) =>
        notypeclasses refine (tac_fast_apply (type_read π E L T _ _ _ _) _); [ solve [refine _ ] |]
    (* borrow mut *)
    | |- envs_entails _ (typed_borrow_mut ?π ?E ?L _ _ _ ?T) =>
        notypeclasses refine (tac_fast_apply (type_borrow_mut E L T _ _ _ π _ _) _); [solve [refine _] |]
    (* borrow shr *)
    | |- envs_entails _ (typed_borrow_shr ?π ?E ?L _ _ _ ?T) =>
        notypeclasses refine (tac_fast_apply (type_borrow_shr E L T _ _ _ _ π _) _); [solve [refine _] |]
    (* addr_of mut *)
    | |- envs_entails _ (typed_addr_of_mut ?π ?E ?L _ ?T) =>
        notypeclasses refine (tac_fast_apply (type_addr_of_mut π E L _ T _ _) _); [solve [refine _] |]
    (* end context folding *)
    | |- envs_entails _ (typed_context_fold_end ?AI ?π ?E ?L ?acc ?T) =>
        notypeclasses refine (tac_fast_apply (type_context_fold_end AI E L π acc T) _)
    (* initialize context folding *)
    | |- envs_entails _ (typed_pre_context_fold ?π ?E ?L (CtxFoldStratifyAllInit) ?T) =>
        liRContextStratifyInit
    (* unblocking step *)
    | |- envs_entails _ (typed_context_fold_step ?AI ?π ?E ?L (CtxFoldStratifyAll) ?l ?lt ?r ?tctx ?acc ?T) =>
        liRContextStratifyStep
    (* initialize context folding *)
    | |- envs_entails _ (typed_pre_context_fold ?π ?E ?L (CtxFoldExtractAllInit ?κ) ?T) =>
        liRContextExtractInit
    (* unblocking step *)
    | |- envs_entails _ (typed_context_fold_step ?AI ?π ?E ?L (CtxFoldExtractAll ?κ) ?l ?lt ?r ?tctx ?acc ?T) =>
        liRContextExtractStep
    (* initialize OnEndlft triggers *)
    | |- envs_entails _ (typed_on_endlft_pre ?π ?E ?L ?κ ?T) =>
        liROnEndlftTriggerInit
    (* trigger tc search *)
    | |- envs_entails _ (trigger_tc ?H ?T) =>
        notypeclasses refine (tac_fast_apply (tac_trigger_tc _ _ _ _) _); [solve [refine _] | ]
    (* stratification for structs *)
    | |- envs_entails _ (@stratify_ltype_struct_iter _ _ ?π ?E ?L ?mu ?mdu ?ma _ ?m ?l ?i ?sls ?rts ?lts ?rs ?k ?T) =>
        match rts with
        | [] =>
          notypeclasses refine (tac_fast_apply (stratify_ltype_struct_iter_nil π E L mu mdu ma m l sls k i T) _)
        | _ :: _ =>
          notypeclasses refine (tac_fast_apply (stratify_ltype_struct_iter_cons π E L mu mdu ma m l sls i _ _ _ k _) _)
        end
  end.

(* TODO Maybe this should rather be a part of Lithium? *)
Ltac unfold_introduce_direct :=
  lazymatch goal with
  | |- envs_entails ?E ?G =>
    let E' := eval unfold introduce_direct in E in
    change_no_check (envs_entails E' G)
  end.

(* This does everything *)
Ltac liRStep :=
 liEnsureInvariant;
 try liRIntroduceLetInGoal;
 (* TODO these are all hacks right now *)
 simp_ltypes;
 simplify_layout_goal;
 first [
   liRInstantiateEvars (* must be before do_side_cond and do_extensible_judgement *)
 | liRStmt
 | liRIntroduceTypedStmt
 | liRExpr
 | liRJudgement
 | liStep
 | lazymatch goal with | |- BACKTRACK_POINT ?P => change_no_check P end
]; try unfold_introduce_direct; liSimpl.

Tactic Notation "liRStepUntil" open_constr(id) :=
  repeat lazymatch goal with
         | |- @environments.envs_entails _ _ ?P =>
           lazymatch P with
           | id _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => fail
           | id _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => fail
           | id _ _ _ _ _ _ _ _ _ _ _ _ _ _ => fail
           | id _ _ _ _ _ _ _ _ _ _ _ _ _ => fail
           | id _ _ _ _ _ _ _ _ _ _ _ _ => fail
           | id _ _ _ _ _ _ _ _ _ _ _ => fail
           | id _ _ _ _ _ _ _ _ _ _ => fail
           | id _ _ _ _ _ _ _ _ _ => fail
           | id _ _ _ _ _ _ _ _ => fail
           | id _ _ _ _ _ _ _ => fail
           | id _ _ _ _ _ _ => fail
           | id _ _ _ _ _ => fail
           | id _ _ _ _ => fail
           | id _ _ => fail
           | id _ => fail
           | id => fail
           | _  => liRStep
           end
         | _ => liRStep
  end; liShow.

(** * Tactics for starting a function *)
(* Recursively destruct a product in hypothesis H, using the given name as template. *)
Ltac destruct_product_hypothesis name H :=
  match goal with
  | H : _ * _ |- _ => let tmp1 := fresh "tmp" in
                      let tmp2 := fresh "tmp" in
                      destruct H as [tmp1 tmp2];
                      destruct_product_hypothesis name tmp1;
                      destruct_product_hypothesis name tmp2
  |           |- _ => let id := fresh name in
                      rename H into id
  end.

Ltac prepare_initial_coq_context :=
  (* The automation assumes that all products in the context are destructed, see liForall *)
  repeat lazymatch goal with
  | H : _ * _ |- _ => destruct_product_hypothesis H H
  (*| H : named_binder ?n |- _ =>*)
                      (*let temp := fresh "tmp" in*)
                      (*destruct H as [tmp];*)
                      (*rename_by_string tmp n*)
  | H : unit |- _ => destruct H
  end.

Ltac inv_arg_ly_rec Harg_ly :=
  match type of Harg_ly with
  | Forall2 _ (?x:: ?L1) (?y :: ?L2) =>
      let H1 := fresh in let H2 := fresh in
      apply Forall2_cons_inv in Harg_ly as [H1 Harg_ly];
      inv_arg_ly_rec Harg_ly
  | Forall2 _ [] [] =>
      clear Harg_ly
  end.
Ltac inv_arg_ly Harg_ly :=
  simpl in Harg_ly; unfold fn_arg_layout_assumptions in Harg_ly; inv_arg_ly_rec Harg_ly; simplify_eq.

Ltac inv_local_ly_rec Harg_ly :=
  match type of Harg_ly with
  | Forall2 _ (?x:: ?L1) (?y :: ?L2) =>
      let H1 := fresh in let H2 := fresh in
      apply Forall2_cons_inv in Harg_ly as [H1 Harg_ly];
      inv_local_ly_rec Harg_ly
  | Forall2 _ [] [] =>
      clear Harg_ly
  end.
Ltac inv_local_ly Harg_ly :=
  simpl in Harg_ly; unfold fn_local_layout_assumptions in Harg_ly; inv_local_ly_rec Harg_ly; simplify_eq.

Section tac.
  Context `{!typeGS Σ}.

  Lemma intro_typed_function {A} (n : nat) π (fn : function) (local_sts : list syn_type) (fp : prod_vec lft n → A → fn_params) :
    (∀ κs x (ϝ : lft),
      □ (
      let lya := fn.(f_args).*2 in
      let lyv := fn.(f_local_vars).*2 in
      ⌜fn_arg_layout_assumptions (fp κs x).(fp_atys) lya⌝ -∗
      ⌜fn_local_layout_assumptions local_sts lyv⌝ -∗
      ∀ (lsa : vec loc (length (fp κs x).(fp_atys))) (lsv : vec loc (length fn.(f_local_vars))),
        let Qinit :=
          ([∗list] l;t∈lsa;(fp κs x).(fp_atys), let '(existT rt (ty, r)) := t in l ◁ₗ[π, Owned false] PlaceIn r @ (◁ ty)) ∗
          ([∗list] l;p∈lsv;local_sts, (l ◁ₗ[π, Owned false] (PlaceIn ()) @ (◁ (uninit p)))) ∗
          (fp κs x).(fp_Pa) π in
      let E := ((fp κs x).(fp_elctx) ϝ) in
      let L := [ϝ ⊑ₗ{0} []] in
      ∃ E' E'', ⌜E = E'⌝ ∗ ⌜E' ≡ₚ E''⌝ ∗
      (credit_store 0 0 -∗ introduce_with_hooks E'' L (Qinit) (λ L2,
        introduce_typed_stmt π E'' L2 ϝ fn lsa lsv lya lyv (
        λ v L2,
            prove_with_subtype E L2 false ProveDirect (fn_ret_prop π (fp κs x).(fp_fr) v) (λ L3 _ R3,
            introduce_with_hooks E L3 R3 (λ L4,
            (* we don't really kill it here, but just need to find it in the context *)
            li_tactic (llctx_find_llft_goal L4 ϝ LlctxFindLftFull) (λ _,
            find_in_context FindCreditStore (λ _, True)
          )))
        ))))) -∗
    typed_function π fn local_sts fp.
  Proof.
    iIntros "#Ha".
    rewrite /typed_function.
    iIntros (???) "!# Hx1 Hx2".
    iIntros (lsa lsv) "(Hstore & Hinit)".
    rewrite /introduce_typed_stmt /typed_stmt.
    iIntros (?) "#CTX #HE HL Hna Hcont".
    iApply fupd_wps.
    iPoseProof ("Ha" with "Hx1 Hx2") as "HT".
    iDestruct ("HT" $! lsa lsv) as "(%E' & %E'' & <- & %Heq & HT)".
    iPoseProof (elctx_interp_permut with "HE") as "HE'". { symmetry. apply Heq. }
    rewrite /introduce_with_hooks.
    iMod ("HT" with "Hstore [] HE' HL Hinit") as "(%L2 & HL & HT)"; first done.
    by iApply ("HT" with "CTX HE' HL Hna").
  Qed.
End tac.

(* IMPORTANT: We need to make sure to never call simpl while the code
(fn) is part of the goal, because simpl seems to take exponential time
in the number of blocks! *)
(* TODO: don't use i... tactics here *)
Tactic Notation "start_function" constr(fnname) "(" simple_intropattern(κs) ")" "(" simple_intropattern(x) ")" :=
  intros;
  inv_layout_alg;
  repeat iIntros "#?";
  iApply (intro_typed_function);
  iIntros ( κs x ϝ ) "!#";
  let Harg_ly := fresh "Harg_ly" in
  let Hlocal_ly := fresh "Hlocal_ly" in
  iIntros (_ _);
  let lsa := fresh "lsa" in let lsv := fresh "lsv" in
  iIntros (lsa lsv);
  prepare_initial_coq_context;
  iExists _, _; iSplitR;
  [iPureIntro; solve [simplify_elctx] | ];
  iSplitR; [iPureIntro; solve[reorder_elctx] | ];
  inv_vec lsv; inv_vec lsa;
  init_cache
.

Tactic Notation "prepare_parameters" "(" ident_list(i) ")" :=
  revert i; repeat liForall.


Ltac liRSplitBlocksIntro :=
  repeat (
      liEnsureInvariant;
      first [
          liSep
        | liWand
        | liImpl
        | liForall
        | liExist true
        | liUnfoldLetGoal]; liSimpl);
  liShow.


Ltac sidecond_hook_list :=
  notypeclasses refine (proj2 (Forall_Forall_cb _ _) _); simpl; (first
          [ exact I | split_and ! ]);
  sidecond_hook.

(* TODO : more sideconditions *)
Ltac sidecond_hook ::=
  unfold_no_enrich;
  open_cache;
  intros;
  match goal with
  | |- Forall ?P ?l =>
      sidecond_hook_list
  | |- lctx_lft_alive ?E ?L ?κ =>
      solve_lft_alive
  | |- lctx_lft_incl ?E ?L ?κ1 ?κ2 =>
      solve_lft_incl
  | |- lctx_bor_kind_incl ?E ?L ?b1 ?b2 =>
      solve_bor_kind_incl
  | |- lctx_bor_kind_alive ?E ?L ?b =>
      solve_bor_kind_alive
  | |- lctx_bor_kind_direct_incl ?E ?L ?b1 ?b2 =>
      solve_bor_kind_direct_incl
  | |- elctx_sat ?E ?L ?E' =>
      solve_elctx_sat
  | |- fn_arg_layout_assumptions ?L1 ?L2 =>
      repeat first [constructor | done]
  | |- lctx_bor_kind_outlives ?E ?L ?b ?κ =>
      solve_bor_kind_outlives
  | |- ty_has_op_type _ _ _ =>
      solve_ty_has_op_type
  | |- layout_wf _ =>
      solve_layout_wf
  | |- syn_type_compat _ _ =>
      solve_syn_type_compat
  | |- ty_allows_reads _ =>
      solve_ty_allows
  | |- ty_allows_writes _ =>
      solve_ty_allows
  | |- _ =>
      try solve_layout_alg;
      try solve_op_alg;
      try solve_layout_eq
      (*try solve [solve_layout_size | solve_layout_eq | solve_op_alg];*)
      (*try solve_layout_alg*)
  end.


(** ** Hints for automation *)
Global Hint Extern 0 (LayoutSizeEq _ _) => rewrite /LayoutSizeEq; solve_layout_size : typeclass_instances.
Global Hint Extern 0 (LayoutSizeLe _ _) => rewrite /LayoutSizeLe; solve_layout_size : typeclass_instances.

(* This should instead be solved by [solve_ty_has_op_type]. *)
Global Arguments ty_has_op_type : simpl never.

(* Simplifying this can lead to problems in some cases when used in specifications. *)
Global Arguments replicate : simpl never.
(* We don't want this to simplify away the zero case, as that can be a valuable hint. *)
Global Arguments freeable_nz : simpl never.

(* should not be visible for automation *)
Global Typeclasses Opaque ty_shr.
Global Typeclasses Opaque ty_own_val.
Global Typeclasses Opaque ty_has_op_type.

(* We get performance problems if discriminate (as part of done) or simpl try to look into this. *)
(* TODO: maybe properly seal? *)
Global Opaque ty_has_op_type.

Global Typeclasses Opaque find_in_context.

Global Arguments ty_lfts : simpl nomatch.
Global Arguments ty_wf_E : simpl nomatch.

Global Arguments layout_of : simpl never.
(*Global Arguments ly_size : simpl never.*)

Global Arguments plist : simpl never.

Global Typeclasses Opaque Rel2.
Global Arguments Rel2 : simpl never.

Global Hint Unfold OffsetLocSt : core.

#[global] Typeclasses Opaque layout_wf.

(* In my experience, this has led to more problems with [normalize_autorewrite] rewriting below definitions too eagerly. *)
Export Unset Keyed Unification.

Create HintDb unfold_tydefs.

(** Lithium hook *)
Ltac normalize_hook ::=
  rewrite /size_of_st;
  (*simplify_layout_goal;*)
  normalize_autorewrite.

Ltac after_intro_hook ::=
  try match goal with
  | H : enter_cache_hint ?P |- _ =>
      unfold enter_cache_hint in H;
      try simplify_layout_alg H;
      enter_cache H
  end;
  inv_layout_alg
.


Ltac enter_cache_hook H cont ::=
  first [
    check_for_cached_layout H
  |
    lazymatch type of H with
    | ?ty =>
        lazymatch goal with
        | H2 : CACHED ty |- _ =>
            clear H
        end
    end
  | cont H].

(** Lithium hooks for [solve_goal]: called for remaining sideconditions *)
Lemma unfold_int_elem_of_it (z : Z) (it : int_type) :
  z ∈ it = (MinInt it ≤ z ∧ z ≤ MaxInt it)%Z.
Proof. done. Qed.

Ltac unfold_common_defs :=
  unfold_common_caesium_defs;
  unfold num_cred in *;
  unfold unit_sl in *.

Ltac solve_goal_normalized_prepare_hook ::=
  try rewrite -> unfold_int_elem_of_it in *;
  autounfold in *;
  simplify_layout_assum;
  simplify_layout_goal;
  open_cache;
  unfold_no_enrich;
  simpl in *;
  (*rewrite /ly_size/ly_align_log //= in **)
  idtac
.


(** User facing tactic calls *)
Ltac sidecond_hammer_it := 
  prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; try (unfold_common_defs; solve_goal); unsolved_sidecond_hook.
Ltac sidecond_hammer :=
  unshelve sidecond_hammer_it; sidecond_hammer_it
.
Ltac sidecond_solver :=
  unshelve_sidecond; sidecond_hook.

Ltac print_remaining_goal :=
  match goal with
  | H := FUNCTION_NAME ?s |- _ =>
    print_typesystem_goal s
  end.
Ltac print_remaining_sidecond :=
  try done; try apply: inhabitant;
  match goal with
  | H := FUNCTION_NAME ?s |- _ =>
    print_remaining_shelved_goal s
  end.
