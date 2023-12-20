From iris.proofmode Require Import coq_tactics reduction.
From lithium Require Export base.
From lithium Require Import hooks definitions simpl_classes normalize proof_state solvers syntax.
Set Default Proof Using "Type".

(** This file contains the main Lithium interpreter. *)

(** * General proof state management tactics  *)
Tactic Notation "liInst" hyp(H) open_constr(c) :=
  instantiate_protected H c.

Ltac liShow := li_unfold_lets_in_context; try liToSyntaxGoal.

Ltac liSimpl :=
  (* simpl inserts a cast even if it does not do anything
     (see https://coq.zulipchat.com/#narrow/stream/237656-Coq-devs.20.26.20plugin.20devs/topic/exact_no_check.2C.20repeated.20casts.20in.20proof.20terms/near/259371220 ) *)
  try progress simpl.

Ltac liUnfoldLetGoal :=
  let do_unfold P :=
    let H := get_head P in
    is_var H;
    unfold LET_ID in H;
    liUnfoldLetGoal_hook H;
    (* This unfold inserts a cast but that is not too bad for
       performance since the goal is small at this point. *)
    unfold H;
    try clear H
  in
  lazymatch goal with
  | |- envs_entails _ (?P ∗ _) => do_unfold P
  | |- envs_entails _ ?P => do_unfold P
  end.

Ltac liUnfoldSyntax :=
  lazymatch goal with
  | |- envs_entails _ (li.all _) => liFromSyntax
  | |- envs_entails _ (li.exist _) => liFromSyntax
  | |- envs_entails _ (li.done) => liFromSyntax
  | |- envs_entails _ (li.false) => liFromSyntax
  | |- envs_entails _ (li.and _ _) => liFromSyntax
  | |- envs_entails _ (li.and_map _ _) => liFromSyntax
  | |- envs_entails _ (li.case_if _ _ _) => liFromSyntax
  | |- envs_entails _ (li.ret) => liFromSyntax
  | |- envs_entails _ (li.bind0 _ _) => liFromSyntax
  | |- envs_entails _ (li.bind1 _ _) => liFromSyntax
  | |- envs_entails _ (li.bind2 _ _) => liFromSyntax
  | |- envs_entails _ (li.bind3 _ _) => liFromSyntax
  | |- envs_entails _ (li.bind4 _ _) => liFromSyntax
  | |- envs_entails _ (li.bind5 _ _) => liFromSyntax
  end.

Ltac liEnsureInvariant :=
  unfold_instantiated_evars; try let_bind_envs; try liUnfoldSyntax.

Section coq_tactics.
  Context {Σ : gFunctors}.

  Lemma tac_fast_apply {Δ} {P1 P2 : iProp Σ} :
    (P1 ⊢ P2) → envs_entails Δ P1 → envs_entails Δ P2.
  Proof. by rewrite envs_entails_unseal => -> HP. Qed.
End coq_tactics.

(** * Main lithium tactics *)

(** ** [liExtensible] *)
Section coq_tactics.
  Context {Σ : gFunctors}.

  (* For some reason, replacing tac_fast_apply with more specialized
  versions gives a 1-2% performance boost, see
  https://coq-speed.mpi-sws.org/d/1QE_dqjiz/coq-compare?orgId=1&var-project=refinedc&var-branch1=master&var-commit1=05a3e8862ae4ab0041af67d1c02c552f99c4f35c&var-config1=build-coq.8.14.0-timing&var-branch2=master&var-commit2=998704f2a571385c65edfdd36332f6c3d014ec59&var-config2=build-coq.8.14.0-timing&var-metric=instructions&var-group=().*
  TODO: investigate this more
*)
  Lemma tac_apply_i2p {Δ} {P : iProp Σ} (P' : iProp_to_Prop P) :
    envs_entails Δ P'.(i2p_P) → envs_entails Δ P.
  Proof. apply tac_fast_apply. apply i2p_proof. Qed.
End coq_tactics.

Ltac liExtensible_to_i2p P bind cont :=
  lazymatch P with
  | subsume ?P1 ?P2 ?T =>
      bind T ltac:(fun H => uconstr:(subsume P1 P2 H));
      cont uconstr:(((_ : Subsume _ _) _))
  | subsume_list ?A ?ig ?l1 ?l2 ?f ?T =>
      bind T ltac:(fun H => uconstr:(subsume_list A ig l1 l2 f H));
      cont uconstr:(((_ : SubsumeList _ _ _ _ _) _))
  | _ => liExtensible_to_i2p_hook P bind cont
  end.
Ltac liExtensible :=
  lazymatch goal with
  | |- envs_entails ?Δ ?P =>
      liExtensible_to_i2p P
        ltac:(fun T tac => li_let_bind T (fun H => let X := tac H in constr:(envs_entails Δ X)))
        ltac:(fun converted =>
          simple notypeclasses refine (tac_apply_i2p converted _); [solve [refine _] |];
          liExtensible_hook)
  end.

(** ** [liTrue] *)
Section coq_tactics.
  Context {Σ : gFunctors}.

  Lemma tac_true Δ :
    envs_entails Δ (True%I : iProp Σ).
  Proof. rewrite envs_entails_unseal. by iIntros "_". Qed.
End coq_tactics.

Ltac liTrue :=
  lazymatch goal with
  | |- envs_entails _ True => notypeclasses refine (tac_true _)
  end.

(** ** [liFalse] *)
Ltac liFalse :=
  lazymatch goal with
  | |- envs_entails _ False => exfalso; shelve_sidecond
  | |- False => shelve_sidecond
  end.

(** ** [liForall] *)
Section coq_tactics.
  Context {Σ : gFunctors}.

  Lemma tac_do_forall A Δ (P : A → iProp Σ) :
    (∀ x, envs_entails Δ (P x)) → envs_entails Δ (∀ x : A, P x).
  Proof.
    rewrite envs_entails_unseal. intros HP. by apply bi.forall_intro.
  Qed.

  Lemma tac_do_exist_wand A Δ (P : A → iProp Σ) Q :
    (∀ x, envs_entails Δ (P x -∗ Q)) → envs_entails Δ ((∃ x : A, P x) -∗ Q).
  Proof.
    rewrite envs_entails_unseal. iIntros (HP) "Henv". iDestruct 1 as (x) "HP".
    by iApply (HP with "Henv HP").
  Qed.
End coq_tactics.

Ltac liForall :=
  (* n tells us how many quantifiers we should introduce with this name *)
  let rec do_intro n name :=
    lazymatch n with
    | S ?n' =>
      lazymatch goal with
      (* relying on the fact that unification variables cannot contain
         dependent variables to distinguish between dependent and non dependent forall *)
      | |- ?P -> ?Q =>
          lazymatch type of P with
          | Prop => fail "implication, not forall"
          | _ => (* just some unused variable, discard *) move => _
          end
      | |- forall _ : ?A, _ =>
        (* When changing this, also change [prepare_initial_coq_context] in automation.v *)
        lazymatch A with
        | (prod _ _) => case; do_intro (S (S O)) name
        | unit => case
        | _ =>
            first [
                (* We match again since having e in the context when
                calling fresh can mess up names. *)
                lazymatch goal with
                | |- forall e : ?A, @?P e =>
                    let sn := open_constr:(_ : nat) in
                    let p := constr:(_ : SimplForall A sn P _) in
                    refine (@simpl_forall_proof _ _ _ _ p _);
                    do_intro sn name
                end
              | let H := fresh name in intro H
              ]
        end
      end;
      do_intro n' name
    | O => idtac
    end
  in
  lazymatch goal with
  | |- envs_entails _ (bi_forall (λ name, _)) =>
      notypeclasses refine (tac_do_forall _ _ _ _); do_intro (S O) name
  | |- envs_entails _ (bi_wand (bi_exist (λ name, _)) _) =>
      notypeclasses refine (tac_do_exist_wand _ _ _ _ _); do_intro (S O) name
  | |- (∃ name, _) → _ =>
      case; do_intro (S O) name
  | |- forall name, _ =>
      do_intro (S O) name
  | _ => fail "liForall: unknown goal"
  end.

(** ** [liExist] *)
Section coq_tactics.
  Context {Σ : gFunctors}.

  Lemma tac_do_exist A Δ (P : A → iProp Σ) :
    (∃ x, envs_entails Δ (P x)) → envs_entails Δ (∃ x : A, P x).
  Proof.
    rewrite envs_entails_unseal. intros [x HP]. by rewrite -(bi.exist_intro x).
  Qed.

  Lemma tac_exist_prod A B (P : _ → Prop):
    (∃ x1 x2, P (x1, x2)) → @ex (A * B) P.
  Proof. move => [?[??]]. eauto. Qed.

  Lemma tac_exist_sigT A f (P : _ → Prop):
    (∃ (a : A) (x : f a), P (existT a x)) → @ex (sigT f) P.
  Proof. move => [?[??]]. eauto. Qed.
End coq_tactics.

Ltac liExist protect :=
  lazymatch goal with
  | |- envs_entails _ (bi_exist _) => notypeclasses refine (tac_do_exist _ _ _ _)
  | _ => idtac
  end;
  lazymatch goal with
  | |- @ex ?A ?P =>
    first [
        liExist_hook A protect
      | lazymatch A with
        | TCForall2 _ _ _ => eexists _
        | @eq ?B ?x _ => exists (@eq_refl B x)
        | prod _ _ => apply: tac_exist_prod
        | sigT _ => apply: tac_exist_sigT
        | unit => exists tt
        | _ =>
            first [
                let p := constr:(_ : SimplExist A P _) in
                refine (@simpl_exist_proof _ _ _ p _)
              |
                lazymatch protect with
                | true => let Hevar := create_protected_evar A in exists (protected Hevar)
                | false => eexists _
                end
              ]
        end ]
  | _ => fail "liExist: unknown goal"
  end.

Tactic Notation "liExist" constr(c) := liExist c.
Tactic Notation "liExist" := liExist true.

(** ** [liImpl] *)
Ltac liImpl :=
  (* We pass false since [(∃ name, _) → _] is handled by [liForall]. *)
  normalize_and_simpl_impl false.

(** ** [liSideCond] *)
Ltac liSideCond :=
  try lazymatch goal with
  | |- (name_hint _ ?P) ∧ ?Q =>
      change_no_check (P ∧ Q)
  end;
  lazymatch goal with
  | |- ?P ∧ ?Q =>
    lazymatch P with
    | shelve_hint _ => split; [ unfold shelve_hint; shelve_sidecond |]
    | _ =>
      first [
        lazymatch P with
        | context [protected _] => fail
        | _ => split; [splitting_fast_done|]
        end
      | progress normalize_goal_and
      | lazymatch P with
        | context [protected _] => first [
            split; [ solve_protected_eq |]; unfold_instantiated_evars
          | notypeclasses refine (@simpl_and_unsafe P _ _ Q _); [solve [refine _] |]
            (* no simpl here because there is liSimpl after each tactic *)
          ]
         (* We use done instead of fast_done here because solving more
         sideconditions here is a bigger performance win than the overhead
         of done. *)
        | _ => split; [ first [ done | shelve_sidecond ] | ]
        end
      ]
    end
  | _ => fail "liSideCond: unknown goal"
  end.

(** ** [liFindInContext] *)
Section coq_tactics.
  Context {Σ : gFunctors}.

  Lemma tac_sep_true Δ (P : iProp Σ) :
    envs_entails Δ P → envs_entails Δ (True ∗ P).
  Proof. rewrite envs_entails_unseal => ->. by apply bi.True_sep_2. Qed.

  Lemma tac_find_hyp_equal key (Q P P' R : iProp Σ) Δ `{!FindHypEqual key Q P P'}:
    envs_entails Δ (P' ∗ R) →
    envs_entails Δ (P ∗ R).
  Proof. by revert select (FindHypEqual _ _ _ _) => ->. Qed.

  Lemma tac_find_hyp Δ i p R (P : iProp Σ) :
    envs_lookup i Δ = Some (p, P) →
    envs_entails (envs_delete false i p Δ) R → envs_entails Δ (P ∗ R).
  Proof.
    rewrite envs_entails_unseal. intros ? HQ.
    rewrite (envs_lookup_sound' _ false) // bi.intuitionistically_if_elim.
      by apply bi.sep_mono_r.
  Qed.

  Lemma tac_find_in_context {Δ} {fic} {T : _ → iProp Σ} key (F : FindInContext fic key) :
    envs_entails Δ (F T).(i2p_P) → envs_entails Δ (find_in_context fic T).
  Proof. rewrite envs_entails_unseal. etrans; [done|]. apply i2p_proof. Qed.
End coq_tactics.

Ltac liFindHyp key :=
  let rec go P Hs :=
    lazymatch Hs with
    | Esnoc ?Hs2 ?id ?Q => first [
      lazymatch key with
      | FICSyntactic =>
          (* We try to unify using the opaquenes hints of
             typeclass_instances. Directly doing exact: eq_refl
             sometimes takes 30 seconds to fail (e.g. when trying
             to unify GetMemberLoc for the same struct but with
             different names.) TODO: investigate if constr_eq
             could help even more
             https://coq.inria.fr/distrib/current/refman/proof-engine/tactics.html#coq:tacn.constr-eq*)
          unify Q P with typeclass_instances
      | _ =>
          notypeclasses refine (tac_find_hyp_equal key Q _ _ _ _ _); [solve [refine _]|];
          lazymatch goal with
          | |- envs_entails _ (?P' ∗ _) =>
              unify Q P' with typeclass_instances
          end
      end;
      notypeclasses refine (tac_find_hyp _ id _ _ _ _ _); [li_pm_reflexivity | li_pm_reduce]
      | go P Hs2 ]
    end in
  lazymatch goal with
  | |- envs_entails _ (?P ∗ _) =>
    (* we don't want to try to unify if the goal contains protected
    evars as this can take very long to fail *)
    lazymatch P with
    | context [protected _] => fail "cannot find hyp if it contains protected"
    | _ => idtac
    end;
    let P := li_pm_reduce_val P in
    let run_go P Hs Hi := first [go P Hs | go P Hi] in
    lazymatch goal with
    | |- envs_entails (Envs ?Hi ?Hs _) _ => run_go P Hs Hi
    | H := (Envs ?Hi ?Hs _) |- _ => run_go P Hs Hi
    end
  end.

Ltac liFindHypOrTrue key :=
  first [
      notypeclasses refine (tac_sep_true _ _ _)
    | progress liFindHyp key
  ].

Ltac liFindInContext :=
  lazymatch goal with
  | |- envs_entails _ (find_in_context ?fic ?T) =>
    let key := open_constr:(_) in
    (* We exploit that [typeclasses eauto] is multi-success to enable
    multiple implementations of [FindInContext]. They are tried in the
    order of their priorities.
    See https://coq.zulipchat.com/#narrow/stream/237977-Coq-users/topic/Multi-success.20TC.20resolution.20from.20ltac.3F/near/242759123 *)
    once (simple notypeclasses refine (tac_find_in_context key _ _);
      [ shelve | typeclasses eauto | simpl; repeat liExist false; liFindHypOrTrue key ])
  end.

(** ** [liSep] *)
Section coq_tactics.
  Context {Σ : gFunctors}.

  Lemma tac_sep_sep_assoc Δ (P Q R : iProp Σ) :
    envs_entails Δ (P ∗ Q ∗ R) → envs_entails Δ ((P ∗ Q) ∗ R).
  Proof. apply tac_fast_apply. iIntros "($&$&$)". Qed.

  Lemma tac_sep_emp Δ (P : iProp Σ) :
    envs_entails Δ P → envs_entails Δ (emp ∗ P).
  Proof. apply tac_fast_apply. by apply bi.emp_sep_1. Qed.

  Lemma tac_sep_exist_assoc {A} Δ (Φ : A → iProp Σ) (Q : iProp Σ):
    envs_entails Δ (∃ a : A, Φ a ∗ Q) → envs_entails Δ ((∃ a : A, Φ a) ∗ Q).
  Proof. by rewrite bi.sep_exist_r. Qed.

  Lemma tac_do_intro_pure_and Δ (P : Prop) (Q : iProp Σ) :
    (P ∧ (envs_entails Δ Q)) → envs_entails Δ (⌜P⌝ ∗ Q).
  Proof.
    rewrite envs_entails_unseal => [[HP HΔ]].
    iIntros "HΔ".  iSplit => //. by iApply HΔ.
  Qed.

  Lemma tac_do_intro_intuit_sep Δ (P Q : iProp Σ) :
    envs_entails Δ (□ (P ∗ True) ∧ Q) → envs_entails Δ (□ P ∗ Q).
  Proof. apply tac_fast_apply. iIntros "[#[$ _] $]". Qed.

  Lemma tac_do_simplify_goal Δ (n : N) (P : iProp Σ) T {SG : SimplifyGoal P (Some n)} :
    envs_entails Δ (SG T).(i2p_P) → envs_entails Δ (P ∗ T).
  Proof. apply tac_fast_apply. iIntros "HP". by iApply (i2p_proof with "HP"). Qed.

  Lemma tac_intro_subsume_related Δ P T {Hrel : RelatedTo P}:
    envs_entails Δ (find_in_context Hrel.(rt_fic) (λ x,
      subsume (Σ:=Σ) (Hrel.(rt_fic).(fic_Prop) x) P T)) →
    envs_entails Δ (P ∗ T).
  Proof. apply tac_fast_apply. iDestruct 1 as (x) "[HP HT]". by iApply "HT". Qed.
End coq_tactics.

Ltac liSep :=
  lazymatch goal with
  | |- envs_entails ?Δ (bi_sep ?P ?Q) =>
    assert_fails (has_evar P);
    lazymatch P with
    | bi_sep _ _ => notypeclasses refine (tac_sep_sep_assoc _ _ _ _ _)
    | bi_exist _ => notypeclasses refine (tac_sep_exist_assoc _ _ _ _)
    | bi_emp => notypeclasses refine (tac_sep_emp _ _ _)
    | (⌜_⌝)%I => notypeclasses refine (tac_do_intro_pure_and _ _ _ _)
    | (□ ?P)%I => notypeclasses refine (tac_do_intro_intuit_sep _ _ _ _)
    | match ?x with _ => _ end => fail "should not have match in sep"
    | ?P => first [
               progress liFindHyp FICSyntactic
             | simple notypeclasses refine (tac_do_simplify_goal _ 0%N _ _ _); [solve [refine _] |]
             | simple notypeclasses refine (tac_intro_subsume_related _ _ _ _); [solve [refine _] |];
               simpl; liFindInContext
             | simple notypeclasses refine (tac_do_simplify_goal _ _ _ _ _); [| solve [refine _] |]
             | fail "do_sep: unknown sidecondition" P
      ]
    end
  end.

(** ** [liWand] *)
Section coq_tactics.
  Context {Σ : gFunctors}.

  Lemma tac_do_intro_pure Δ (P : Prop) (Q : iProp Σ) :
    (P → envs_entails Δ Q) → envs_entails Δ (⌜P⌝ -∗ Q).
  Proof.
    rewrite envs_entails_unseal => HP. iIntros "HΔ %".  by iApply HP.
  Qed.

  Lemma tac_do_simplify_hyp (P : iProp Σ) (SH: SimplifyHyp P (Some 0%N)) Δ T :
    envs_entails Δ (SH T).(i2p_P) →
    envs_entails Δ (P -∗ T).
  Proof.
    rewrite envs_entails_unseal => HP. iIntros "Henv Hl".
    iDestruct (HP with "Henv") as "HP".
    iDestruct (i2p_proof with "HP Hl") as "$".
  Qed.

  Lemma tac_do_intro i n' (P : iProp Σ) n Γs Γp T :
    env_lookup i Γs = None →
    env_lookup i Γp = None →
    envs_entails (Envs Γp (Esnoc Γs i P) n') T →
    envs_entails (Envs Γp Γs n) (P -∗ T).
  Proof.
    rewrite envs_entails_unseal => Hs Hp HP. iIntros "Henv Hl".
    rewrite (envs_app_sound (Envs Γp Γs n) (Envs Γp (Esnoc Γs i P) n) false (Esnoc Enil i P)) //; simplify_option_eq => //.
    iApply HP. iApply "Henv". iFrame.
  Qed.

  Lemma tac_do_intro_intuit i n' (P P' : iProp Σ) T n Γs Γp (Hpers : IntroPersistent P P') :
    env_lookup i Γs = None →
    env_lookup i Γp = None →
    envs_entails (Envs (Esnoc Γp i P') Γs n') T →
    envs_entails (Envs Γp Γs n) (P -∗ T).
  Proof.
    rewrite envs_entails_unseal => Hs Hp HP. iIntros "Henv HP".
    iDestruct (@ip_persistent _ _ _ Hpers with "HP") as "#HP'".
    rewrite (envs_app_sound (Envs Γp Γs n) (Envs (Esnoc Γp i P') Γs n) true (Esnoc Enil i P')) //; simplify_option_eq => //.
    iApply HP. iApply "Henv".
    iModIntro. by iSplit.
  Qed.

  Lemma tac_wand_sep_assoc Δ (P Q R : iProp Σ) :
    envs_entails Δ (P -∗ Q -∗ R) → envs_entails Δ ((P ∗ Q) -∗ R).
  Proof. by rewrite bi.wand_curry. Qed.

  Lemma tac_wand_emp Δ (P : iProp Σ) :
    envs_entails Δ P → envs_entails Δ (emp -∗ P).
  Proof. apply tac_fast_apply. by iIntros "$". Qed.
End coq_tactics.

Ltac liWand :=
  let wand_intro P :=
    first [
      let SH := constr:(_ : SimplifyHyp P (Some 0%N)) in
      simple notypeclasses refine (tac_do_simplify_hyp P SH _ _ _)
    | let P' := open_constr:(_) in
      let ip := constr:(_ : IntroPersistent P P') in
      let n := lazymatch goal with | [ H := Envs _ _ ?n |- _ ] => n end in
      let H := constr:(IAnon n) in
      let n' := eval vm_compute in (Pos.succ n) in
      simple notypeclasses refine (tac_do_intro_intuit H n' P P' _ _ _ _ ip _ _ _); [li_pm_reflexivity..|]
    | let n := lazymatch goal with | [ H := Envs _ _ ?n |- _ ] => n end in
      let H := constr:(IAnon n) in
      let n' := eval vm_compute in (Pos.succ n) in
      simple notypeclasses refine (tac_do_intro H n' P _ _ _ _ _ _ _); [li_pm_reflexivity..|]
    ] in
  lazymatch goal with
  | |- envs_entails ?Δ (bi_wand ?P ?T) =>
      lazymatch P with
      | bi_sep _ _ =>
          li_let_bind T (fun H => constr:(envs_entails Δ (bi_wand P H)));
          notypeclasses refine (tac_wand_sep_assoc _ _ _ _ _)
      | bi_exist _ => fail "handled by liForall"
      | bi_emp => notypeclasses refine (tac_wand_emp _ _ _)
      | bi_pure _ => notypeclasses refine (tac_do_intro_pure _ _ _ _)
      | match ?x with _ => _ end => fail "should not have match in wand"
      | _ => wand_intro P
      end
  end.

(** ** [liAnd] *)
Section coq_tactics.
  Context {Σ : gFunctors}.

  Lemma tac_do_split Δ (P1 P2 : iProp Σ):
    envs_entails Δ P1 →
    envs_entails Δ P2 →
    envs_entails Δ (P1 ∧ P2).
  Proof. rewrite envs_entails_unseal => HP1 HP2. by apply bi.and_intro. Qed.

  Lemma tac_big_andM_insert Δ {A B} `{Countable A} (m : gmap A B) i n (Φ : _ → _→ iProp Σ) :
    envs_entails Δ (⌜m !! i = None⌝ ∗ (Φ i n ∧ [∧ map] k↦v∈m, Φ k v)) →
    envs_entails Δ ([∧ map] k↦v∈<[i:=n]>m, Φ k v).
  Proof. apply tac_fast_apply. iIntros "[% HT]". by rewrite big_andM_insert. Qed.

  Lemma tac_big_andM_empty Δ {A B} `{Countable A} (Φ : _ → _→ iProp Σ) :
    envs_entails Δ ([∧ map] k↦v∈(∅ : gmap A B), Φ k v).
  Proof. rewrite envs_entails_unseal. iIntros "_". by rewrite big_andM_empty. Qed.
End coq_tactics.

Ltac liAnd :=
  lazymatch goal with
  | |- envs_entails _ (bi_and ?P _) =>
    notypeclasses refine (tac_do_split _ _ _ _ _)
  | |- envs_entails _ ([∧ map] _↦_∈<[_:=_]>_, _) =>
    notypeclasses refine (tac_big_andM_insert _ _ _ _ _ _)
  | |- envs_entails _ ([∧ map] _↦_∈∅, _) =>
    notypeclasses refine (tac_big_andM_empty _ _)
  end.

(** ** [liPersistent] *)
Section coq_tactics.
  Context {Σ : gFunctors}.

  Lemma tac_persistent Δ (P : iProp Σ) :
    envs_entails (envs_clear_spatial Δ) P → envs_entails Δ (□ P).
  Proof.
    rewrite envs_entails_unseal => HP. iIntros "Henv".
    iDestruct (envs_clear_spatial_sound with "Henv") as "[#Henv _]".
    iModIntro. iApply (HP with "Henv").
  Qed.
End coq_tactics.

Ltac liPersistent :=
  lazymatch goal with
  | |- envs_entails ?Δ (bi_intuitionistically ?P) =>
      notypeclasses refine (tac_persistent _ _ _); li_pm_reduce
  end.

(** ** [liCase] *)
Section coq_tactics.
  Context {Σ : gFunctors}.

  Lemma tac_case_if Δ (P : Prop) T1 T2 :
    (P → envs_entails Δ T1) →
    (¬ P → envs_entails Δ T2) →
    envs_entails Δ (@case_if Σ P T1 T2).
  Proof.
    rewrite envs_entails_unseal => HT1 HT2.
    iIntros "Henvs". iSplit; iIntros (?).
    - by iApply HT1.
    - by iApply HT2.
  Qed.

  Lemma tac_case_destruct_bool_decide Δ (P : Prop) `{!Decision P} T:
    (P → envs_entails Δ (T true true)) →
    (¬ P → envs_entails Δ (T false true)) →
    envs_entails Δ (@case_destruct Σ bool (bool_decide P) T).
  Proof.
    rewrite envs_entails_unseal => HP HnotP.
    iIntros "Henvs". iExists true. case_bool_decide.
    - by iApply HP.
    - by iApply HnotP.
  Qed.

  Lemma tac_case_destruct {A} (b : bool) Δ a T:
    envs_entails Δ (T a b) →
    envs_entails Δ (@case_destruct Σ A a T).
  Proof. apply tac_fast_apply. iIntros "?". iExists _. iFrame. Qed.
End coq_tactics.

(* This tactic checks if destructing x would lead to multiple
non-trivial subgoals. The main reason for it is that we don't want to
destruct constructors like true as this would not be useful. *)
Ltac non_trivial_destruct x :=
  first [
      have : (const False x); [ clear; case_eq x; intros => //; (*
      check if there is only one goal remaining *) [ idtac ]; fail 1 "trivial destruct" |]
    | idtac
  ].

Ltac liCase :=
  lazymatch goal with
  | |- @envs_entails ?PROP ?Δ (case_if ?P ?T1 ?T2) =>
      notypeclasses refine (tac_case_if _ _ _ _ _ _)
  | |- @envs_entails ?PROP ?Δ (case_destruct (@bool_decide ?P ?b) ?T) =>
      notypeclasses refine (tac_case_destruct_bool_decide _ _ _ _ _)
      (* notypeclasses refine (tac_case_destruct true _ _ _ _); *)
      (* let H := fresh "H" in destruct_decide (@bool_decide_reflect P b) as H; revert H *)
  | |- @envs_entails ?PROP ?Δ (case_destruct ?x ?T) =>
      tryif (non_trivial_destruct x) then
        notypeclasses refine (tac_case_destruct true _ _ _ _);
        case_eq x
      else (
        notypeclasses refine (tac_case_destruct false _ _ _ _)
      )
  end;
  (* It is important that we prune branches this way because this way
  we don't need to do normalization and simplification of hypothesis
  that we introduce twice, which has a big impact on performance. *)
  repeat (liForall || liImpl); try by [exfalso; can_solve].

(** ** [liTactic] *)
Section coq_tactics.
  Context {Σ : gFunctors}.

  Lemma tac_li_tactic {A} Δ t (th : LiTactic t) (Q : A → iProp Σ):
    envs_entails Δ (th.(li_tactic_P) Q) →
    envs_entails Δ (li_tactic t Q).
  Proof. rewrite envs_entails_unseal => ?. etrans; [done|]. apply li_tactic_proof. Qed.
End coq_tactics.

Ltac liTactic :=
  lazymatch goal with
  | |- envs_entails _ (li_tactic _ _) =>
      simple notypeclasses refine (tac_li_tactic _ _ _ _ _); [ solve [refine _] |]
  end.

(** ** [liAccu] *)
Section coq_tactics.
  Context {Σ : gFunctors}.

  Lemma tac_do_accu Δ (f : iProp Σ → iProp Σ):
    envs_entails (envs_clear_spatial Δ) (f (env_to_prop (env_spatial Δ))) →
    envs_entails Δ (accu f).
  Proof.
    rewrite envs_entails_unseal => Henv. iIntros "Henv".
    iDestruct (envs_clear_spatial_sound with "Henv") as "[#Henv Hs]".
    iExists (env_to_prop (env_spatial Δ)).
    rewrite -env_to_prop_sound. iFrame. iModIntro. by iApply (Henv with "Henv").
  Qed.
End coq_tactics.

Ltac liAccu :=
  lazymatch goal with
  | |- envs_entails _ (accu _) =>
    notypeclasses refine (tac_do_accu _ _ _); li_pm_reduce
  end.

(** ** [liTrace] *)
Ltac liTrace :=
  lazymatch goal with
  | |- @envs_entails ?PROP ?Δ (li_trace ?info ?T) =>
    change_no_check (@envs_entails PROP Δ T);
    liTrace_hook info
  end.

(** ** [liStep] *)
Ltac liStep :=
  first [
      liExtensible
    | liSep
    | liAnd
    | liWand
    | liExist
    | liImpl
    | liForall
    | liSideCond
    | liFindInContext
    | liCase
    | liTrace
    | liTactic
    | liPersistent
    | liTrue
    | liFalse
    | liAccu
    | liUnfoldLetGoal
    ].
