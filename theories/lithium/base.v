From Coq Require Export ssreflect.
From stdpp Require Export sorting.
From iris.algebra Require Export big_op.
From Coq.ZArith Require Import Znumtheory.
From stdpp Require Import gmap list.
From iris.program_logic Require Import weakestpre.
From iris.bi Require Import bi.
From iris.proofmode Require Import proofmode.
From stdpp Require Import natmap.
From stdpp.unstable Require Import bitblast.
From RecordUpdate Require Export RecordSet.
Export RecordSetNotations.

Set Default Proof Using "Type".

Export Unset Program Cases.
Export Set Keyed Unification.

(* We always annotate hints with locality ([Global] or [Local]). This enforces
that at least global hints are annotated. *)
Export Set Warnings "+deprecated-hint-without-locality".
Export Set Warnings "+deprecated-hint-rewrite-without-locality".
Export Set Warnings "+deprecated-typeclasses-transparency-without-locality".

Export Set Default Goal Selector "!".

(* ensure that set from RecordUpdate simplifies when it is applied to a concrete value *)
Global Arguments set _ _ _ _ _ !_ /.

Global Typeclasses Opaque is_Some.
(* This is necessary since otherwise keyed unification unfolds these definitions *)
Global Opaque rotate_nat_add rotate_nat_sub.

Global Typeclasses Opaque Z.divide Z.modulo Z.div Z.shiftl Z.shiftr.
Global Arguments min : simpl nomatch.

Global Arguments Z.testbit : simpl never.
Global Arguments Z.shiftl : simpl never.
Global Arguments Z.shiftr : simpl never.
Global Arguments N.shiftl : simpl never.
Global Arguments N.shiftr : simpl never.
Global Arguments Pos.shiftl : simpl never.
Global Arguments Pos.shiftr : simpl never.
Global Opaque Z.shiftl Z.shiftr.

(* TODO: upstream to stdpp? *)
Notation "'[@{' A '}' x ; y ; .. ; z ]" :=  (@cons A x (@cons A y .. (@cons A z (@nil A)) ..)) (only parsing) : list_scope.
Notation "'[@{' A '}' x ]" := (@cons A x nil) (only parsing) : list_scope.
Notation "'[@{' A '}' ]" := (@nil A) (only parsing) : list_scope.

(** More automation for modular arithmetics. *)
Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

(** * tactics *)
Lemma rel_to_eq {A} (R : A → A → Prop) `{!Reflexive R} x y:
  x = y → R x y.
Proof. move => ->. reflexivity. Qed.

Ltac fast_reflexivity :=
  notypeclasses refine (rel_to_eq _ _ _ _); [solve [refine _] |];
  lazymatch goal with
  | |- ?x = ?y => lazymatch x with | y => exact: (eq_refl x) end
  end.

Ltac get_head e :=
  lazymatch e with
  | ?h _ => get_head constr:(h)
  | _    => constr:(e)
  end.

(** A version of fast_done that splits conjunctions. *)
Ltac splitting_fast_done :=
  solve
  [ repeat first
    [ fast_done
    (* All the tactics below will introduce themselves anyway, or make no sense
       for goals of product type. So this is a good place for us to do it. *)
    | progress intros
    | split ]
  ].

Ltac assert_is_trivial P :=
  assert_succeeds (assert (P) as _;[splitting_fast_done|]).
Ltac assert_is_not_trivial P :=
  assert_fails (assert (P) as _;[splitting_fast_done|]).

Tactic Notation "reduce_closed" constr(x) :=
  is_closed_term x;
  let r := eval vm_compute in x in
  change_no_check x with r in *
.

(* from https://mattermost.mpi-sws.org/iris/pl/dcktjjjpsiycmrieyh74bzoagr *)
Ltac solve_sep_entails :=
  try (apply (anti_symm _));
  iIntros;
  repeat iMatchHyp (fun H P =>
    lazymatch P with
    | (_ ∗ _)%I => iDestruct H as "[??]"
    | (∃ _, _)%I => iDestruct H as (?) "?"
    end);
  eauto with iFrame.

Lemma tac_evar_safe_vm_compute {A} (x y : A):
  (∀ z, y = z → x = z) →
  x = y.
Proof. naive_solver. Qed.
(* vm_compute likes to mess with evars that it find in the goal so
evar_safe_vm_compute hides them. *)
Ltac evar_safe_vm_compute :=
  apply tac_evar_safe_vm_compute;
  let H := fresh in
  intros ? H;
  vm_compute;
  apply H.

(* see https://github.com/coq/coq/issues/15768#issuecomment-1380773542 *)
(* TODO: This must be called as [unfold_opaque @x]. Is there a way to
get rid of the @? *)
Tactic Notation "unfold_opaque" constr(c) := with_strategy 0 [c] (unfold c).

(*
The following tactics are currently not used.

(* TODO: This tactic is quite inefficient (it calls unification for
every subterm in the goal and hyps). Can we do something about this? *)
Tactic Notation "select" "subterm" open_constr(pat) tactic3(tac) :=
  match goal with
  | |- context H [?x]       => unify x pat; tac x
  | _ : context H [?x] |- _ => unify x pat; tac x
  end.

Tactic Notation "reduce" "pattern" open_constr(pat) :=
  repeat select subterm pat (fun x => reduce_closed x).

(* TODO: This tactic is quite inefficient (it calls unification for
every subterm in the goal and hyps). Can we do something about this? *)
Tactic Notation "select" "closed" "subterm" "of" "type" constr(T) tactic3(tac) :=
  match goal with
  | |- context H [?x]       => let ty := type of x in unify ty T; check_closed x; tac x
  | _ : context H [?x] |- _ => let ty := type of x in unify ty T; check_closed x; tac x
  end.

Ltac evalZ :=
  repeat select closed subterm of type Z (fun x => progress reduce_closed x).
 *)


Create HintDb simplify_length discriminated.
Global Hint Rewrite rev_length app_length @take_length @drop_length @cons_length @nil_length : simplify_length.
Global Hint Rewrite @insert_length : simplify_length.
Ltac simplify_length :=
  autorewrite with simplify_length.

Ltac saturate_list_lookup :=
  repeat match goal with
         | H : @lookup _ _ _ list_lookup ?l ?i = Some _ |- _ =>
             let H' := fresh "H" in
             pose proof (lookup_lt_Some _ _ _ H) as H';
             tactic simplify_length in H';
             lazymatch type of H' with
             | ?T => assert_fails (clear H'; assert T by lia)
             end
      end.

Ltac list_lia :=
  simplify_length; lia.

Lemma list_eq_split {A} i (l1 l2 : list A):
  take i l1 = take i l2 →
  drop i l1 = drop i l2 →
  l1 = l2.
Proof. move => ??. rewrite -(take_drop i l1) -(take_drop i l2). congruence. Qed.


(** * typeclasses *)
Inductive TCOneIsSome {A} : option A → option A → Prop :=
| tc_one_is_some_left n1 o2 : TCOneIsSome (Some n1) o2
| tc_one_is_some_right o1 n2 : TCOneIsSome o1 (Some n2).
Existing Class TCOneIsSome.
Global Existing Instance tc_one_is_some_left.
Global Existing Instance tc_one_is_some_right.

Inductive TCOneIsSome3 {A} : option A → option A → option A → Prop :=
| tc_one_is_some3_left n1 o2 o3 : TCOneIsSome3 (Some n1) o2 o3
| tc_one_is_some3_middle o1 n2 o3 : TCOneIsSome3 o1 (Some n2) o3
| tc_one_is_some3_right o1 o2 n3 : TCOneIsSome3 o1 o2 (Some n3).
Existing Class TCOneIsSome3.
Global Existing Instance tc_one_is_some3_left.
Global Existing Instance tc_one_is_some3_middle.
Global Existing Instance tc_one_is_some3_right.

Class TCDone (P : Prop) : Prop := done_proof : P.
Global Hint Extern 1 (TCDone ?P) => (change P; done) : typeclass_instances.

(** [AssumeInj] is a hint that automation should treat f as if it were
injective, even though the injectivity might not be provable. *)
Class AssumeInj {A B} (R : relation A) (S : relation B) (f : A → B) : Prop := assume_inj : True.
Global Instance assume_inj_inj A B R S (f : A → B) `{!Inj R S f} : AssumeInj R S f.
Proof. done. Qed.

Class IsVar {A} (x : A) : Set := {}.
Global Hint Extern 0 (IsVar ?x) => (is_var x; constructor) : typeclass_instances.
Global Hint Mode IsVar + + : typeclass_instances.

Definition exists_dec_unique {A} (x : A) (P : _ → Prop) : (∀ y, P y → P x) → Decision (P x) → Decision (∃ y, P y).
Proof.
  intros Hx Hdec.
  refine (cast_if (decide (P x))).
  - abstract by eexists _.
  - abstract naive_solver.
Defined.

(** * bool *)
Lemma bool_to_Z_neq_0_bool_decide b :
  bool_decide (bool_to_Z b ≠ 0) = b.
Proof. by destruct b. Qed.

Lemma bool_to_Z_eq_0_bool_decide b :
  bool_decide (bool_to_Z b = 0) = negb b.
Proof. by destruct b. Qed.

Lemma Is_true_eq (b : bool) : b ↔ b = true.
Proof. by case: b. Qed.

Lemma bool_decide_eq_x_x_true {A} (x : A) `{!Decision (x = x)} :
  bool_decide (x = x) = true.
Proof. by case_bool_decide.  Qed.
Lemma if_bool_decide_eq_branches {A} P `{!Decision P} (x : A) :
  (if bool_decide P then x else x) = x.
Proof. by case_bool_decide. Qed.
Lemma negb_bool_decide_eq {A} (x y : A) `{!EqDecision A} :
  negb (bool_decide (x = y)) = bool_decide (x ≠ y).
Proof. by repeat case_bool_decide. Qed.

(** * apply_dfun *)
(* TODO: does something like this exist in Iris? *)
Definition apply_dfun {A B} (f : A -d> B) (x : A) : B := f x.
Global Arguments apply_dfun : simpl never.

Global Instance apply_dfun_ne A B n:
  Proper ((dist n) ==> (=) ==> (dist n)) (@apply_dfun A B).
Proof. intros ?? H1 ?? ->. rewrite /apply_dfun. apply H1. Qed.

Global Instance apply_dfun_proper A B :
  Proper ((≡) ==> (=) ==> (≡)) (@apply_dfun A B).
Proof. intros ?? H1 ?? ->. rewrite /apply_dfun. apply H1. Qed.

Global Instance discrete_fn_proper A B `{LeibnizEquiv A} (f : A -d> B):
  Proper ((≡) ==> (≡)) f.
Proof. by intros ?? ->%leibniz_equiv. Qed.

(** * list *)
Lemma zip_fmap_r {A B C} (l1 : list A) (l2 : list B) (f : B → C) :
  zip l1 (f <$> l2) = (λ x, (x.1, f x.2)) <$>  zip l1 l2.
Proof. rewrite zip_with_fmap_r zip_with_zip. by apply: list_fmap_ext => // ? []. Qed.

Lemma zip_with_nil_inv' {A B C : Type} (f : A → B → C) (l1 : list A) (l2 : list B) :
  length l1 = length l2 → zip_with f l1 l2 = [] → l1 = [] ∧ l2 = [].
Proof.
  move => Hlen /zip_with_nil_inv [] H; rewrite H /= in Hlen;
  split => //; by apply nil_length_inv.
Qed.

Lemma list_find_Some' A (l : list A) x P `{!∀ x, Decision (P x)}:
  list_find P l = Some x ↔ l !! x.1 = Some x.2 ∧ P x.2 ∧ ∀ y, y ∈ take x.1 l → ¬P y.
Proof.
  destruct x => /=. rewrite list_find_Some. do 2 f_equiv. setoid_rewrite elem_of_take.
  split => ?; [naive_solver..|].
  move => j ? ?. have [|??]:= lookup_lt_is_Some_2 l j. { by apply: lookup_lt_Some. }
  set_solver.
Qed.

Lemma replicate_O {A} (x : A) n:
  n = 0%nat -> replicate n x = [].
Proof. by move => ->. Qed.

Global Instance set_unfold_replicate A (x y : A) n:
  SetUnfoldElemOf x (replicate n y) (x = y ∧ n ≠ 0%nat).
Proof. constructor. apply elem_of_replicate. Qed.

Lemma list_elem_of_insert1 {A} (l : list A) i (x1 x2 : A) :
  x1 ∈ <[i:=x2]> l → x1 = x2 ∨ x1 ∈ l.
Proof.
  destruct (decide (i < length l)%nat). 2: rewrite list_insert_ge; naive_solver lia.
  move => /(elem_of_list_lookup_1 _ _)[i' ].
  destruct (decide (i = i')); subst.
  - rewrite list_lookup_insert // => -[]. naive_solver.
  - rewrite list_lookup_insert_ne // elem_of_list_lookup. naive_solver.
Qed.

Lemma list_elem_of_insert2 {A} (l : list A) i (x1 x2 x3 : A) :
  l !! i = Some x3 → x1 ∈ l → x1 ∈ <[i:=x2]> l ∨ x1 = x3.
Proof.
  destruct (decide (i < length l)%nat). 2: rewrite list_insert_ge; naive_solver lia.
  move => ? /(elem_of_list_lookup_1 _ _)[i' ?].
  destruct (decide (i = i')); simplify_eq; first naive_solver.
  left. apply elem_of_list_lookup. exists i'. by rewrite list_lookup_insert_ne.
Qed.
Lemma list_elem_of_insert2' {A} (l : list A) i (x1 x2 x3 : A) :
  l !! i = Some x3 → x1 ∈ l → x1 ≠ x3 → x1 ∈ <[i:=x2]> l.
Proof. move => ???. efeed pose proof (list_elem_of_insert2 (A:=A)) as Hi; naive_solver. Qed.

Lemma list_fmap_ext' {A B} f (g : A → B) (l1 l2 : list A) :
    (∀ x, x ∈ l1 → f x = g x) → l1 = l2 → f <$> l1 = g <$> l2.
Proof. intros ? <-. induction l1; f_equal/=; set_solver. Qed.

Lemma imap_fst_NoDup {A B C} l (f : nat → A → B) (g : nat → C):
  Inj eq eq g →
  NoDup (imap (λ i o, (g i, f i o)) l).*1.
Proof.
  move => ?. rewrite fmap_imap (imap_ext _ (λ i o, g i)%nat) // imap_seq_0.
    by apply NoDup_fmap, NoDup_ListNoDup, seq_NoDup.
Qed.
Global Instance set_unfold_imap A B f (l : list A) (x : B):
  SetUnfoldElemOf x (imap f l) (∃ i y, x = f i y ∧ l !! i = Some y).
Proof.
  constructor.
  elim: l f => /=; [set_solver|]. set_unfold. move => ? ? IH f.
  rewrite IH {IH}. split; [case|].
  - move => ->. set_solver.
  - move => [n [v [-> ?]]]. exists (S n), v => /=. set_solver.
  - move => [[|n] /= [v [-> ?]]]; simplify_eq; [by left | right].
    naive_solver.
Qed.

Lemma list_insert_fold {A} l i (x : A) :
  list_insert i x l = <[i := x]> l.
Proof. done. Qed.

Lemma default_last_cons {A} (x1 x2 y : A) l :
  default x1 (last (y :: l)) = default x2 (last (y :: l)).
Proof. elim: l y => //=. Qed.

Lemma list_lookup_length_default_last {A} (x : A) (l : list A) :
  (x :: l) !! length l = Some (default x (last l)).
Proof. elim: l x => //= a l IH x. rewrite IH. f_equal. destruct l => //=. apply default_last_cons. Qed.

Lemma filter_nil_inv {A} P `{!∀ x, Decision (P x)} (l : list A):
  filter P l = [] ↔ (∀ x : A, x ∈ l → ¬ P x).
Proof.
  elim: l. 1: by rewrite filter_nil; set_solver.
  move => x l IH. rewrite filter_cons. case_decide; set_solver.
Qed.

Lemma length_filter_gt {A} P `{!∀ x, Decision (P x)} (l : list A) x:
  x ∈ l → P x →
  (0 < length (filter P l))%nat.
Proof. elim; move => *; rewrite filter_cons; case_decide; naive_solver lia. Qed.

Lemma length_filter_insert {A} P `{!∀ x, Decision (P x)} (l : list A) i x x':
  l !! i = Some x' →
  length (filter P (<[i:=x]>l)) =
  (length (filter P l) + (if bool_decide (P x) then 1 else 0) - (if bool_decide (P x') then 1 else 0))%nat.
Proof.
  elim: i l.
  - move => [] //=??[->]. rewrite !filter_cons. by repeat (case_decide; case_bool_decide) => //=; lia.
  - move => i IH [|? l]//=?. rewrite !filter_cons. case_decide => //=; rewrite IH // Nat.sub_succ_l //.
    repeat case_bool_decide => //; try lia. feed pose proof (length_filter_gt P l x') => //; try lia.
    by apply: elem_of_list_lookup_2.
Qed.

Lemma length_filter_replicate_True {A} P `{!∀ x, Decision (P x)} (x : A) len:
  P x → length (filter P (replicate len x)) = len.
Proof. elim: len => //=???. rewrite filter_cons. case_decide => //=. f_equal. naive_solver. Qed.

Lemma reshape_app {A} (ln1 ln2 : list nat) (l : list A) :
  reshape (ln1 ++ ln2) l = reshape ln1 (take (sum_list ln1) l) ++ reshape ln2 (drop (sum_list ln1) l).
Proof. elim: ln1 l => //= n ln1 IH l. rewrite take_take skipn_firstn_comm IH drop_drop. repeat f_equal; lia. Qed.
Lemma omap_app {A B} (f : A → option B) (s1 s2 : list A):
  omap f (s1 ++ s2) = omap f s1 ++ omap f s2.
Proof. elim: s1 => //. csimpl => ?? ->. case_match; naive_solver. Qed.
Lemma sum_list_with_take {A} f (l : list A) i:
   (sum_list_with f (take i l) ≤ sum_list_with f l)%nat.
Proof. elim: i l => /=; [lia|]. move => ? IH [|? l2] => //=. move: (IH l2). lia.  Qed.

Lemma omap_length_eq {A B C} (f : A → option B) (g : A → option C) (l : list A):
  (∀ i x, l !! i = Some x → const () <$> (f x) = const () <$> (g x)) →
  length (omap f l) = length (omap g l).
Proof.
  elim: l => //; csimpl => x ? IH Hx. move: (Hx O x ltac:(done)) => /=?.
  do 2 case_match => //=; rewrite IH // => i ??; by apply: (Hx (S i)).
Qed.

Lemma join_length {A} (l : list (list A)) :
  length (mjoin l) = sum_list (length <$> l).
Proof. elim: l => // ?? IH; csimpl. rewrite app_length IH //. Qed.

Lemma sum_list_eq l1 l2:
  Forall2 eq l1 l2 →
  sum_list l1 = sum_list l2.
Proof. by elim => // ???? -> /= ? ->. Qed.

Lemma reshape_join {A} szs (ls : list (list A)) :
  Forall2 (λ l sz, length l = sz) ls szs →
  reshape szs (mjoin ls) = ls.
Proof.
  revert ls. induction szs as [|sz szs IH]; simpl; intros ls; [by inversion 1|].
  intros (?&?&?&?&?)%Forall2_cons_inv_r; simplify_eq/=. rewrite take_app drop_app. f_equal.
  naive_solver.
Qed.

Lemma lookup_eq_app_r {A} (l1 l2 suffix : list A) (i : nat) :
  length l1 = length l2 →
  l1 !! i = l2 !! i ↔ (l1 ++ suffix) !! i = (l2 ++ suffix) !! i.
Proof.
  move => Hlen. destruct (l1 !! i) as [v|] eqn:HEq.
  + rewrite lookup_app_l; last by eapply lookup_lt_Some.
    rewrite lookup_app_l; first by rewrite -HEq.
    apply lookup_lt_Some in HEq. by rewrite -Hlen.
  + rewrite lookup_app_r; last by apply lookup_ge_None.
    apply lookup_ge_None in HEq. rewrite Hlen in HEq.
    apply lookup_ge_None in HEq. rewrite HEq.
    split => [_|]//. rewrite lookup_app_r; first by rewrite Hlen.
    by apply lookup_ge_None.
Qed.

Lemma StronglySorted_lookup_le {A} R (l : list A) i j x y:
  StronglySorted R l → l !! i = Some x → l !! j = Some y → (i ≤ j)%nat → x = y ∨ R x y.
Proof.
  move => Hsorted. elim: Hsorted i j => // z {}l ? IH Hall [|?] [|?]//=???; simplify_eq; try lia.
  - by left.
  - right. by apply: (Forall_lookup_1 _ _ _ _ Hall).
  - apply: IH => //. lia.
Qed.

Lemma StronglySorted_lookup_lt {A} R (l : list A) i j x y:
  StronglySorted R l → l !! i = Some x → l !! j = Some y → ¬ R y x → x ≠ y → (i < j)%nat.
Proof.
  move => Hs Hi Hj HR Hneq. elim: Hs j i Hj Hi => // z {}l _ IH /Forall_forall Hall.
  case => /=.
  - case; first naive_solver. move => n [?]/= /(elem_of_list_lookup_2 _ _ _)?; subst. naive_solver.
  - move => n. case; first lia. move => n2 /= ??. apply->Nat.succ_lt_mono. naive_solver.
Qed.

(* TODO: Is it possible to make this lemma more general and add it as an instance? *)
Lemma list_fmap_Forall2_proper {A B} (R : relation B) :
  Proper (pointwise_relation A R ==> (=) ==> Forall2 R) fmap.
Proof.
  move => ?? Hf ?? ->. apply Forall2_fmap.
  apply Forall_Forall2_diag, Forall_true => *.
  eapply Hf.
Qed.
(* TODO: Can one make this an instance? *)
Lemma default_proper {A} (R : relation A) :
  Proper (R ==> option_Forall2 R ==> R) default.
Proof. move => ?? ? [?|] [?|] //= Hopt; by inversion Hopt. Qed.

Global Instance head_proper {A} (R : relation A): Proper (Forall2 R ==> option_Forall2 R) head.
Proof. move => ?? [] * /=; by constructor. Qed.

(** * vec *)
Lemma vec_cast {A} n (v : vec A n) m:
  n = m → ∃ v' : vec A m, vec_to_list v = vec_to_list v'.
Proof.
  elim: v m => [|??? IH] [|m']// ?.
  - by eexists vnil.
  - have [|??]:= IH m'. { lia. }
    eexists (vcons _ _) => /=. by f_equal.
Qed.

(** * map *)

Section theorems.
Context `{FinMap K M}.

Lemma partial_alter_self_alt' {A} (m : M A) i f:
  m !! i = f (m !! i) → partial_alter f i m = m.
Proof using Type*.
  intros. apply map_eq. intros ii. by destruct (decide (i = ii)) as [->|];
    rewrite ?lookup_partial_alter ?lookup_partial_alter_ne.
Qed.

Lemma partial_alter_to_insert {A} x (m : M A) f k:
    f (m !! k) = Some x →
    partial_alter f k m = <[k := x]> m.
Proof using Type*. move => ?. by apply: partial_alter_ext => ? <-. Qed.

End theorems.

(** * option  *)
Lemma apply_default {A B} (f : A → B) (d : A) (o : option A) :
  f (default d o) = default (f d) (f <$> o).
Proof. by destruct o. Qed.

(** * list_subequiv *)
Definition list_subequiv {A} (ignored : list nat) (l1 l2 : list A) : Prop :=
  ∀ i, length l1 = length l2 ∧ (i ∉ ignored → l1 !! i = l2 !! i).
Section list_subequiv.
  Context {A : Type}.
  Implicit Type l : list A.

  Global Instance list_subequiv_equiv ig : Equivalence (list_subequiv (A:=A) ig).
  Proof.
    unfold list_subequiv. split => //.
    - move => ?? H i. move: (H i) => [-> ?]. split; first done. symmetry. naive_solver.
    - move => ??? H1 H2 i. move: (H1 i) => [-> H1i]. move: (H2 i) => [-> H2i].
      split; first done. etrans; first exact: H1i. naive_solver.
  Qed.

  Lemma list_subequiv_nil_l l ig:
    list_subequiv ig [] l ↔ l = [].
  Proof. split => Hs; destruct l => //. by move: (Hs 0) => [??]. Qed.

  Lemma list_subequiv_nil_r l ig:
    list_subequiv ig l [] ↔ l = [].
  Proof. split => Hs; destruct l => //. by move: (Hs 0) => [??]. Qed.

  Lemma list_subequiv_insert_in_l l1 l2 j x ig:
    j ∈ ig →
    list_subequiv ig (<[j := x]>l1) l2 ↔ list_subequiv ig l1 l2.
  Proof.
    unfold list_subequiv. move => ?. split => Hs i; move: (Hs i) => [<- H].
    - split; first by rewrite insert_length. move => ?.
      rewrite -H; last done. rewrite list_lookup_insert_ne; naive_solver.
    - split; first by rewrite insert_length. move => ?.
      rewrite list_lookup_insert_ne; naive_solver.
  Qed.

  Lemma list_subequiv_insert_in_r l1 l2 j x ig:
    j ∈ ig →
    list_subequiv ig l1 (<[j := x]>l2) ↔ list_subequiv ig l1 l2.
  Proof.
    move => ?.
    rewrite (symmetry_iff (list_subequiv _)) [in X in _ ↔ X](symmetry_iff (list_subequiv _)).
      by apply list_subequiv_insert_in_l.
  Qed.

  Lemma list_subequiv_insert_ne_l l1 l2 j x ig:
    (j < length l1)%nat → j ∉ ig →
    list_subequiv ig (<[j := x]>l1) l2 ↔ l2 !! j = Some x ∧ list_subequiv (j :: ig) l1 l2.
  Proof.
    move => ??. unfold list_subequiv. split.
    - move => Hs. move: (Hs j) => [<- <-]//. rewrite list_lookup_insert //. split => // i.
      rewrite insert_length. split => // Hi. move: (Hs i) => [? <-];[|set_solver].
      rewrite list_lookup_insert_ne //. set_solver.
    - rewrite insert_length. move => [? Hs] i. split; first by move: (Hs 0) => [? _]//.
      case: (decide (i = j)) => [->|?].
      + by rewrite list_lookup_insert.
      + rewrite list_lookup_insert_ne//. move: (Hs i) => [? H]// ?. apply H. set_solver.
  Qed.

  Lemma list_subequiv_app_r l1 l2 l3 ig:
    list_subequiv ig (l1 ++ l3) (l2 ++ l3) ↔ list_subequiv ig l1 l2.
  Proof.
  rewrite /list_subequiv. split => H i; move: (H i) => [Hlen Hlookup].
  - rewrite app_length app_length in Hlen. split; first by lia.
    move => /Hlookup. apply lookup_eq_app_r. by lia.
  - split; first by rewrite app_length app_length Hlen.
    move => /Hlookup. apply lookup_eq_app_r. by lia.
  Qed.

  Lemma list_subequiv_fmap {B} ig l1 l2 (f : A → B):
    list_subequiv ig l1 l2 →
    list_subequiv ig (f <$> l1) (f <$> l2).
  Proof.
    move => Hs i. move: (Hs 0%nat) => [Hlen _].
    do 2 rewrite fmap_length. split => // ?. rewrite !list_lookup_fmap.
    f_equal. move: (Hs i) => [_ ?]. naive_solver.
  Qed.

  Lemma list_insert_subequiv l1 l2 j x1 :
    (j < length l1)%nat →
    <[j:=x1]>l1 = l2 ↔ l2 !! j = Some x1 ∧ list_subequiv [j] l1 l2.
  Proof.
    move => ?. split.
    - move => <-. rewrite list_lookup_insert // list_subequiv_insert_in_r //. set_solver.
    - move => [? Hsub]. apply list_eq => i. case: (decide (i = j)) => [->|?].
      + by rewrite list_lookup_insert.
      + rewrite list_lookup_insert_ne//. apply Hsub. set_solver.
  Qed.

  Lemma list_subequiv_split l1 l2 i :
    length l1 = length l2 →
    list_subequiv [i] l1 l2 ↔
    take i l1 = take i l2 ∧ drop (S i) l1 = drop (S i) l2.
  Proof.
    move => Hlen. split.
    - move => Hsub. split; apply list_eq => n; move: (Hsub n) => Hn; set_unfold.
      + destruct (decide (n < i)%nat).
        * rewrite !lookup_take; by naive_solver lia.
        * rewrite !lookup_ge_None_2 // take_length; lia.
      + rewrite !lookup_drop. apply Hsub. set_unfold. lia.
    - move => [Ht Hd] n. split; first done.
      move => ?. have ? : (n ≠ i) by set_solver.
      destruct (decide (n < i)%nat).
      + by rewrite -(lookup_take l1 i) // -(lookup_take l2 i) // Ht.
      + have ->:(n = (S i) + (n - (S i)))%nat by lia.
        by rewrite -!lookup_drop Hd.
  Qed.
End list_subequiv.
Global Typeclasses Opaque list_subequiv.
Global Opaque list_subequiv.

(** * big_op *)
Section big_op.
Context {PROP : bi}.
Implicit Types P Q : PROP.
Implicit Types Ps Qs : list PROP.
Implicit Types A : Type.

(** ** Big ops over lists *)
Section sep_list.
  Context {A : Type}.
  Implicit Types l : list A.
  Implicit Types Φ Ψ : nat → A → PROP.

  Lemma big_sepL_insert l i x Φ:
    (i < length l)%nat →
    (([∗ list] k↦v ∈ <[i:=x]> l, Φ k v) ⊣⊢ Φ i x ∗ ([∗ list] k↦v ∈ l, if decide (k = i) then emp else Φ k v)).
  Proof.
    intros Hl.
    destruct (lookup_lt_is_Some_2 l i Hl) as [y Hy].
    rewrite big_sepL_delete; [| by apply list_lookup_insert].
    rewrite insert_take_drop // -{3}(take_drop_middle l i y) // !big_sepL_app /=.
    do 3 f_equiv. rewrite take_length. case_decide => //. lia.
  Qed.

Lemma big_sepL_impl' {B} Φ (Ψ : _ → B → _) (l1 : list A) (l2 : list B) :
    length l1 = length l2 →
    ([∗ list] k↦x ∈ l1, Φ k x) -∗
    □ (∀ k x1 x2, ⌜l1 !! k = Some x1⌝ -∗ ⌜l2 !! k = Some x2⌝ -∗ Φ k x1 -∗ Ψ k x2) -∗
    [∗ list] k↦x ∈ l2, Ψ k x.
  Proof.
    iIntros (Hlen) "Hl #Himpl".
    iInduction l1 as [|x1 l1] "IH" forall (Φ Ψ l2 Hlen); destruct l2 => //=; simpl in *.
    iDestruct "Hl" as "[Hx1 Hl]". iSplitL "Hx1"; [by iApply "Himpl"|].
    iApply ("IH" $! (Φ ∘ S) (Ψ ∘ S) l2 _ with "[] Hl").
    iIntros "!>" (k y1 y2 ?) "Hl2 /= ?".
    by iApply ("Himpl" with "[] [Hl2]").
    Unshelve. lia.
  Qed.
End sep_list.

  Lemma big_sepL2_impl' {A B C D} (Φ : _ → _ → _ → PROP) (Ψ : _ → _ → _ → _) (l1 : list A) (l2 : list B) (l1' : list C) (l2' : list D)  `{!BiAffine PROP} :
    length l1 = length l1' → length l2 = length l2' →
    ([∗ list] k↦x;y ∈ l1; l2, Φ k x y) -∗
    □ (∀ k x1 x2 y1 y2, ⌜l1 !! k = Some x1⌝ -∗ ⌜l2 !! k = Some x2⌝ -∗ ⌜l1' !! k = Some y1⌝ -∗  ⌜l2' !! k = Some y2⌝ -∗ Φ k x1 x2 -∗ Ψ k y1 y2) -∗
    [∗ list] k↦x;y ∈ l1';l2', Ψ k x y.
  Proof.
    iIntros (Hlen1 Hlen2) "Hl #Himpl".
    rewrite !big_sepL2_alt. iDestruct "Hl" as (Hl1) "Hl".
    iSplit. { iPureIntro. congruence. }
    iApply (big_sepL_impl' with "Hl"). { rewrite !zip_with_length. lia. }
    iIntros "!>" (k [x1 x2] [y1 y2]).
    rewrite !lookup_zip_with_Some.
    iDestruct 1 as %(?&?&?&?).
    iDestruct 1 as %(?&?&?&?). simplify_eq. destruct_and!.
    by iApply "Himpl".
  Qed.
End big_op.

(** * power_of_two and factor2  *)
Definition is_power_of_two (n : nat) := ∃ m : nat, n = (2^m)%nat.
Global Arguments is_power_of_two : simpl never.
Global Typeclasses Opaque is_power_of_two.

Fixpoint Pos_factor2 (p : positive) : nat :=
  match p with
  | xO p => S (Pos_factor2 p)
  | _ => 0%nat
  end.

Definition factor2' (n : nat) : option nat :=
  match N.of_nat n with
  | N0 => None
  | Npos p => Some (Pos_factor2 p)
  end.
Definition factor2 (n : nat) (def : nat) : nat :=
  default def (factor2' n).

Definition keep_factor2 (n : nat) (def : nat) : nat :=
  default def (Nat.pow 2 <$> factor2' n).

Lemma Pos_pow_add_r a b c:
  (a ^ (b + c) = a ^ b * a ^ c)%positive.
Proof. zify. rewrite Z.pow_add_r; lia. Qed.

Lemma Pos_factor2_mult_xI a b:
  Pos_factor2 (a~1 * b) = Pos_factor2 b.
Proof.
  move: a. elim b => // p IH a. rewrite /= -/Pos.mul. f_equal.
  rewrite Pos.mul_xO_r [X in Pos_factor2 (_ + xO X) = _]Pos.mul_comm.
  rewrite -Pos.mul_xI_r Pos.mul_comm. apply IH.
Qed.

Lemma Pos_factor2_mult a b:
  Pos_factor2 (a * b) = (Pos_factor2 a + Pos_factor2 b)%nat.
Proof.
  elim: a b => // p IH b.
  - by rewrite Pos_factor2_mult_xI.
  - by rewrite Pos.mul_comm Pos.mul_xO_r /= Pos.mul_comm IH.
Qed.

Lemma Pos_factor2_pow n:
  Pos_factor2 (2^n)%positive = Pos.to_nat n.
Proof.
  elim: n => // p IH; rewrite ?Pos.xI_succ_xO -(Pos.add_diag p) -?Pos.add_succ_r -?Pos.add_1_r !Pos_pow_add_r !Pos_factor2_mult !IH /=; lia.
Qed.

Lemma Zdivide_mult_l n1 n2 a :
  ((n1 * n2 | a) → (n1 | a))%Z.
Proof. move => [? ->]. by apply Z.divide_mul_r, Z.divide_mul_l. Qed.

Lemma Zdivide_nat_pow a b c:
  ((b ≤ c)%nat → ((a ^ b)%nat | (a ^ c)%nat))%Z.
Proof.
  move => ?. apply: (Zdivide_mult_l _ (a^(c - b))%nat).
  by rewrite -Nat2Z.inj_mul -Nat.pow_add_r Nat.add_comm Nat.sub_add.
Qed.

Lemma Pos_factor2_divide p :
  ((2 ^ Pos_factor2 p)%nat | Z.pos p)%Z.
Proof.
  elim: p => //=. 1: by move => *; apply Z.divide_1_l.
  move => p IH. rewrite -plus_n_O Pos2Z.inj_xO Nat2Z.inj_add Z.add_diag. by apply Z.mul_divide_mono_l.
Qed.

Lemma factor2_divide n x :
  ((2 ^ factor2 n x)%nat | n)%Z.
Proof.
  rewrite /factor2/factor2'. rewrite -(nat_N_Z n). case_match => /=; first by apply Z.divide_0_r.
  apply Pos_factor2_divide.
Qed.

Lemma factor2'_pow n:
  factor2' (2^n)%nat = Some n.
Proof.
  rewrite /factor2'. destruct (N.of_nat (2 ^ n)) eqn:H.
  - exfalso. elim: n H => // /=. lia.
  - f_equal. move: p H. induction n as [|n IH].
    + move => p /= Hp. destruct p => //.
    + move => p Hp. destruct p.
      * exfalso. zify. rewrite Nat.pow_succ_r' in Hp. lia.
      * rewrite /=. f_equal. apply IH.
        zify. rewrite Nat.pow_succ_r' in Hp. lia.
      * exfalso. zify. rewrite Nat.pow_succ_r' in Hp. lia.
Qed.

Lemma factor2_pow n x:
  factor2 (2^n)%nat x = n.
Proof. by rewrite /factor2 factor2'_pow. Qed.

Lemma keep_factor2_0 n:
  keep_factor2 0 n = n.
Proof. done. Qed.

Lemma keep_factor2_mult n m o:
  n ≠ 0 → m ≠ 0 →
  keep_factor2 (m * n) o = keep_factor2 m o * keep_factor2 n o.
Proof.
  rewrite /keep_factor2 /factor2' => ??. destruct n,m => //=.
  rewrite -Nat.pow_add_r -Pos_factor2_mult. do 2 f_equal. lia.
Qed.

Lemma keep_factor2_neq_0 n x:
  n ≠ 0 →
  keep_factor2 n x ≠ 0.
Proof. move => ?. destruct n => //. rewrite /keep_factor2 /=. by apply Nat.pow_nonzero. Qed.

Lemma keep_factor2_is_power_of_two n x:
  is_power_of_two n →
  keep_factor2 n x = n.
Proof. move => [? ->]. by rewrite /keep_factor2 factor2'_pow. Qed.

Lemma keep_factor2_leq (n m : nat):
  is_power_of_two n → (n | m) →
  n ≤ keep_factor2 m n.
Proof.
  move => ? [o ->]. destruct (decide (o = 0)); first by subst; rewrite keep_factor2_0; lia.
  destruct (decide (n = 0)); first lia.
  rewrite keep_factor2_mult // (keep_factor2_is_power_of_two n) //.
  have ?: keep_factor2 o n ≠ 0 by apply keep_factor2_neq_0.
  destruct (keep_factor2 o n); lia.
Qed.

Lemma keep_factor2_min_eq (n m : nat):
  is_power_of_two n → (n | m) →
  (n `min` keep_factor2 m n) = n.
Proof. move => ??. apply: Nat.min_l. by apply: keep_factor2_leq. Qed.

Lemma keep_factor2_min_1 n:
  1 `min` keep_factor2 n 1 = 1.
Proof.
  rewrite /keep_factor2 /factor2'. destruct (N.of_nat n) => // /=.
  apply Nat.min_l. generalize (Pos_factor2 p) => k. induction k as [|k IH] => //.
  rewrite Nat.pow_succ_r'. lia.
Qed.

Lemma keep_factor2_twice n m:
  (keep_factor2 n (keep_factor2 n m)) = (keep_factor2 n m).
Proof. by destruct n. Qed.

(* Lemma mult_is_one_Z n m : 0 ≤ n → 0 ≤ m → n * m = 1 → n = 1 ∧ m = 1. *)
(* Proof. *)
(*   intros Hn Hm. *)
(*   move: (Z_of_nat_complete n Hn) => [i ->]. *)
(*   move: (Z_of_nat_complete m Hm) => [j ->]. *)
(*   move => HZ. assert (i * j = 1)%nat as H by lia. *)
(*   apply mult_is_one in H. lia. *)
(* Qed. *)

(* Lemma mult_is_mult_of_pow2_Z n1 n2 (m : nat): *)
(*   0 ≤ n1 → 0 ≤ n2 → n1 * n2 = 2 ^ m → ∃ (m1 m2 : nat), n1 = 2 ^ m1 ∧ n2 = 2 ^ m2. *)
(* Proof. *)
(*   revert n1 n2. induction m as [|m IH] => n1 n2 Hn1 Hn2. *)
(*   - rewrite Z.pow_0_r. move => /(mult_is_one_Z _ _ Hn1 Hn2) [-> ->]. by exists 0%nat, 0%nat. *)
(*   - assert (Z.of_nat (S m) = Z.succ m) as -> by lia. rewrite Z.pow_succ_r; last by lia. *)
(*     move => H. assert (2 | n1 * n2) as Hdiv. { rewrite H. apply Z.divide_mul_l, Z.divide_refl. } *)
(*     apply prime_mult in Hdiv; last by apply prime_2. *)
(*     destruct Hdiv as [Hdiv|Hdiv]; destruct Hdiv as [k ->]. *)
(*     + assert (k * 2 * n2 = 2 * (k * n2)) as Htmp by lia; rewrite Htmp in H; clear Htmp. *)
(*       apply Z.mul_cancel_l in H => //. apply IH in H; [ .. | lia | lia ]. *)
(*       destruct H as [m1 [m2 [-> ->]]]. exists (S m1), m2. split => //. *)
(*       rewrite Z.mul_comm -Z.pow_succ_r; last by lia. f_equal. lia. *)
(*     + assert (n1 * (k * 2) = 2 * (n1 * k)) as Htmp by lia; rewrite Htmp in H; clear Htmp. *)
(*       apply Z.mul_cancel_l in H => //. apply IH in H; [ .. | lia | lia ]. *)
(*       destruct H as [m1 [m2 [-> ->]]]. exists m1, (S m2). split => //. *)
(*       rewrite Z.mul_comm -Z.pow_succ_r; last by lia. f_equal. lia. *)
(* Qed. *)

Lemma divide_mult_2 n1 n2 : divide 2 (n1 * n2) → divide 2 n1 ∨ divide 2 n2.
  move => /Nat2Z.divide. rewrite Nat2Z.inj_mul. move => /(prime_mult _ prime_2).
  move => [H|H]; [left | right]; apply Z2Nat.divide in H; try lia.
  - rewrite Nat2Z.id in H. assert (Z.to_nat 2 = 2) as Heq by lia. by rewrite Heq in H.
  - rewrite Nat2Z.id in H. assert (Z.to_nat 2 = 2) as Heq by lia. by rewrite Heq in H.
Qed.

Lemma is_power_of_two_mult n1 n2:
  (is_power_of_two (n1 * n2)) ↔ (is_power_of_two n1 ∧ is_power_of_two n2).
Proof.
  rewrite /is_power_of_two. split.
  - move => [m Hm]. move: n1 n2 Hm. elim: m.
    + move => /= ?? /Nat.eq_mul_1 [->->]. split; by exists 0.
    + move => n IH n1 n2 H. rewrite Nat.pow_succ_r' in H.
      assert (divide 2 (n1 * n2)) as Hdiv. { exists (2 ^ n). lia. }
      apply divide_mult_2 in Hdiv as [[k ->]|[k ->]].
      * assert (k * n2 = 2 ^ n) as Hkn2 by lia.
        apply IH in Hkn2 as [[m ->] Hn2]. split => //.
        exists (S m). by rewrite Nat.mul_comm -Nat.pow_succ_r'.
      * assert (n1 * k = 2 ^ n) as Hn1k by lia.
        apply IH in Hn1k as [Hn1 [m ->]]. split => //.
        exists (S m). by rewrite Nat.mul_comm -Nat.pow_succ_r'.
  - move => [[m1 ->] [m2 ->]]. exists (m1 + m2). by rewrite Nat.pow_add_r.
Qed.

Lemma Z_distr_mul_sub_1 a b:
  (a * b - b = (a - 1) * b)%Z.
Proof. nia. Qed.

Lemma mul_le_mono_r_1 m p:
  (1 ≤ m)%nat → (p ≤ m * p)%nat.
Proof. nia. Qed.

(** * shifts *)
Section shifts.
Local Open Scope Z_scope.
Lemma Z_shiftl_le_mono_l n a b:
  0 ≤ n →
  a ≤ b →
  a ≪ n ≤ b ≪ n.
Proof.
  move => ??. rewrite !Z.shiftl_mul_pow2 //.
  apply Z.mul_le_mono_nonneg_r => //. by apply: Z.pow_nonneg.
Qed.
Lemma Z_shiftr_le_mono_l n a b:
  0 ≤ n →
  a ≤ b →
  a ≫ n ≤ b ≫ n.
Proof.
  move => ??. rewrite !Z.shiftr_div_pow2 //.
  apply: Z.div_le_mono => //. by apply: Z.pow_pos_nonneg.
Qed.
Lemma Z_shiftl_lt_mono_l n a b:
  0 ≤ n →
  a < b →
  a ≪ n < b ≪ n.
Proof.
  move => ??.
  rewrite !Z.shiftl_mul_pow2 //. apply Z.mul_lt_mono_pos_r; [|done].
    by apply: Z.pow_pos_nonneg.
Qed.
Lemma Z_shiftr_lt_mono_l n a b:
  0 ≤ n →
  a < b →
  Z.land b (Z.ones n) = 0 →
  a ≫ n < b ≫ n.
Proof.
  move => ???.
  have ?:= Z.pow_pos_nonneg 2 n.
  rewrite !Z.shiftr_div_pow2 //.
  apply: Z.div_lt_upper_bound; [lia|].
  rewrite -Z_div_exact_2 //; [lia|]. rewrite -Z.land_ones => //.
Qed.
Lemma Z_shiftr_shiftl_0 a n :
  0 ≤ n →
  (a ≪ n) ≫ n = a.
Proof. move => ?. by rewrite Z.shiftr_shiftl_l // Z.sub_diag Z.shiftl_0_r. Qed.
Lemma Z_shiftl_shiftr_0 a n :
  0 ≤ n →
  Z.land a (Z.ones n) = 0 →
  (a ≫ n) ≪ n = a.
Proof. move => ? Hland. bitblast as i. by bitblast Hland with i. Qed.
Lemma Z_shiftl_distr_add a b c:
  0 ≤ c →
  (a + b) ≪ c = (a ≪ c + b ≪ c).
Proof. move => ?. rewrite !Z.shiftl_mul_pow2 //. lia. Qed.
End shifts.

(** Z.lnot (bitwise negation) for unsigned integers with [bits] bits. *)
Definition Z_lunot (bits n : Z) :=
  (Z.lnot n `mod` 2 ^ bits)%Z.
Global Typeclasses Opaque Z_lunot.

Lemma Z_lunot_spec bits n k:
  (0 ≤ k < bits)%Z → Z.testbit (Z_lunot bits n) k = negb (Z.testbit n k).
Proof.
  move => [? ?].
  by rewrite Z.mod_pow2_bits_low ?Z.lnot_spec.
Qed.

Lemma Z_lunot_spec_high bits n k:
  (0 ≤ bits ≤ k)%Z → Z.testbit (Z_lunot bits n) k = false.
Proof.
  move => ?. by rewrite Z.mod_pow2_bits_high.
Qed.

Lemma Z_lunot_range bits n:
  (0 ≤ bits → 0 ≤ Z_lunot bits n < 2 ^ bits)%Z.
Proof.
  move => ?.
  apply: Z.mod_pos_bound.
  by apply: Z.pow_pos_nonneg.
Qed.

Lemma bitblast_lunot bits z n b:
  Bitblast z n b →
  Bitblast (Z_lunot bits z) n
    ((bool_decide ((bits < 0 ≤ n)%Z) || (bool_decide ((0 ≤ bits)%Z) && bool_decide ((0 ≤ n < bits)%Z))) && negb b).
Proof.
  move => [<-]. constructor.
  case_bool_decide.
  - rewrite orb_true_l andb_true_l /Z_lunot.
    destruct H as [LE GT].
    have -> : (2 ^ bits)%Z = 0 by apply Z.pow_neg_r.
    by rewrite Zmod_0_r -Z.lnot_spec //=.
  - rewrite orb_false_l.
    case_bool_decide; last first.
    + apply Z.testbit_neg_r. lia.
    + case_bool_decide => //=.
      *  rewrite Z.mod_pow2_bits_low; [| lia].
         rewrite -Z.lnot_spec //. lia.
      * destruct (decide (0 ≤ n)%Z).
        -- rewrite Z.mod_pow2_bits_high //=. lia.
        -- apply Z.testbit_neg_r. lia.
Qed.
Global Hint Resolve bitblast_lunot | 10 : bitblast.

(* bits for `- n` *)
Lemma Z_bits_opp_z n i :
  (0 ≤ i)%Z →
  (n `mod` 2 ^ i = 0)%Z →
  Z.testbit (- n) i = Z.testbit n i.
Proof.
  intros.
  rewrite !Z.testbit_eqb; [|lia..].
  have ? : (0 < 2 ^ i)%Z by apply Z.pow_pos_nonneg; lia.
  rewrite Z.div_opp_l_z; lia.
Qed.

Lemma Z_bits_opp_nz n i :
  (0 ≤ i)%Z →
  (n `mod` 2 ^ i ≠ 0)%Z →
  Z.testbit (-n) i = negb (Z.testbit n i).
Proof.
  intros.
  rewrite !Z.testbit_eqb; [|lia..].
  rewrite Z.div_opp_l_nz; lia.
Qed.

Lemma Z_mod_pow2_zero_iff n k :
  (0 ≤ k)%Z →
  (n `mod` 2 ^ k = 0)%Z ↔ ∀ i, (0 ≤ i < k)%Z → Z.testbit n i = false.
Proof.
  intros. split.
  - move => Hb i ?. by bitblast Hb with i.
  - move => Hf. bitblast. by apply Hf.
Qed.

(** bitblast for pos *)
Lemma bitblast_pos_xO p n b :
  Bitblast (Z.pos p) (n - 1) b →
  Bitblast (Z.pos p~0) n b.
Proof.
  move => [<-]. constructor.
  destruct (decide (0 ≤ n)%Z). 2: { rewrite !Z.testbit_neg_r //; lia. }
  destruct (decide (n = 0)%Z). { subst. done. }
  destruct n; try lia.
  rewrite !Z_testbit_pos_testbit /=; [|lia..].
  f_equal. lia.
Qed.
(* lower priority than rule for constants *)
Global Hint Resolve bitblast_pos_xO | 15 : bitblast.

Lemma bitblast_pos_xI p n b :
  Bitblast (Z.pos p) (n - 1) b →
  Bitblast (Z.pos p~1) n (bool_decide (n = 0) || b).
Proof.
  move => [<-]. constructor.
  destruct (decide (0 ≤ n)%Z).
  2: { rewrite bool_decide_false; [|lia]. rewrite !Z.testbit_neg_r //; lia. }
  case_bool_decide. { subst. done. }
  destruct n; try lia.
  rewrite !Z_testbit_pos_testbit /=; [|lia..].
  f_equal. lia.
Qed.
(* lower priority than rule for constants *)
Global Hint Resolve bitblast_pos_xI | 15 : bitblast.

(** rep

 The [rep] tactic is an alternative to the [repeat] and [do] tactics
 that supports left-biased depth-first branching with optional
 backtracking on failure. *)

(* A backtrack point marker *)
Definition BACKTRACK_POINT {A} (P : A) : A := P.
Arguments BACKTRACK_POINT : simpl never.
Global Typeclasses Opaque BACKTRACK_POINT.

(* Check whether the current goal is a backtracking point.
  By default, this is the case for [BACKTRACK_POINT], but this behavior can be overridden. *)
Ltac rep_check_backtrack_point :=
  match goal with
    | |- BACKTRACK_POINT ?P =>
      idtac
  end.

Module Rep.
  Import Ltac2.
  Import Ltac2.Printf.

  (* Check whether the current goal is a backtracking point *)
  Ltac2 rep_check_backtrack_point (x : unit) : bool :=
    let tac_res := Control.focus 1 1 (fun _ => Control.case (fun _ => ltac1:(rep_check_backtrack_point))) in
    match tac_res with
    | Err _ => false
    | Val _ => true
    end.

  (* Backtracking mode:
     - NoBacktrack: don't backtrack
     - BacktrackSteps n: backtrack to n steps before failure
     - BacktrackPoint n: go back to the n-th last goal for which [rep_check_backtrack_point] succeeded *)
  Ltac2 Type backtrack_mode := [ NoBacktrack | BacktrackSteps (int) | BacktrackPoint (int) ].

  (* Exception to signal how many more steps should be backtracked*)
  Ltac2 Type exn ::= [ RepBacktrack (backtrack_mode) ].

  (* calls [tac] [n] times (n = None means infinite) on the first goal
  under focus, stops on failure of [tac] and then backtracks according to [nback]. *)
  Ltac2 rec rep (n : int option) (nback : backtrack_mode) (tac : (unit -> unit)) : int :=
    (* if there are no goals left, we are done *)
    match Control.case (fun _ => Control.focus 1 1 (fun _ => ())) with
    | Err _ => 0
    | Val _ =>
      (* check if we should do another repetition *)
      let do_rep := match n with | None => true | Some n => Int.gt n 0 end in
      match do_rep with
      | false => 0
      | true =>
        (* maybe we should match on the goal here *)
        let is_backtrack_point := Control.focus 1 1 (fun _ => rep_check_backtrack_point ()) in
        (* backtracking point *)
        let res := Control.case (fun _ =>
          (* run tac on the first goal *)
          let tac_res := Control.focus 1 1 (fun _ => Control.case tac) in
          match tac_res  with
          | Err _ =>
              (* if tac failed, start the backtracking *)
              Control.zero (RepBacktrack nback)
          | Val _ =>
              (* compute new n and recurse *)
              let new_n :=
                match n with | None => None | Some n => Some (Int.sub n 1) end in
              let n_steps := rep new_n nback tac in
              Int.add n_steps 1
          end) in
        match res with
        | Err e =>
            match e with
            (* check if we have to backtrack *)
            | RepBacktrack m =>
                match m with
                | BacktrackSteps n =>
                  (* either rethrow it with one less or return 0 *)
                  match Int.gt n 0 with
                  | true => Control.zero (RepBacktrack (BacktrackSteps (Int.sub n 1)))
                  | false => 0
                  end
                | BacktrackPoint n =>
                    match Int.gt n 0 with
                    | true =>
                      (* check if we are at the last backtracking point or rethrow it *)
                      match is_backtrack_point with
                      | true =>
                        match Int.gt n 1 with
                        | true =>
                          Control.zero (RepBacktrack (BacktrackPoint (Int.sub n 1)))
                        | false => 0
                        end
                      | false => Control.zero (RepBacktrack (BacktrackPoint n))
                      end
                    | false => 0
                    end
                | NoBacktrack => 0
                end
            | _ => Control.zero e
            end
        | Val (r, _) => r
        end
      end
    end.

  Ltac2 print_steps (n : int) :=
    printf "Did %i steps." n.

  Ltac2 rec pos_to_ltac2_int (n : constr) : int :=
    lazy_match! n with
    | xH => 1
    | xO ?n => Int.mul (pos_to_ltac2_int n) 2
    | xI ?n => Int.add (Int.mul (pos_to_ltac2_int n) 2) 1
    end.

  Ltac2 rec z_to_ltac2_int (n : constr) : int :=
    lazy_match! n with
    | Z0 => 0
    | Z.pos ?n => pos_to_ltac2_int n
    | Z.neg ?n => Int.neg (pos_to_ltac2_int n)
    end.

  (* TODO: use a mutable record field, see Janno's message *)

  (* Calls tac on a new subgoal of type Z and converts the resulting Z
  to an int. *)
  Ltac2 int_from_z_subgoal (tac : unit -> unit) : int :=
    let x := Control.focus 1 1 (fun _ =>
      let x := open_constr:(_ : Z) in
      match Constr.Unsafe.kind x with
      | Constr.Unsafe.Cast x _ _ =>
          match Constr.Unsafe.kind x with
          | Constr.Unsafe.Evar e _ =>
              Control.new_goal e;
              x
          | _ => Control.throw Assertion_failure
          end
      | _ => Control.throw Assertion_failure
      end) in
    (* new goal has index 2 because it was added after goal number 1 *)
    Control.focus 2 2 (fun _ =>
      tac ();
      (* check that the goal is closed *)
      Control.enter (fun _ => Control.throw Assertion_failure));
    Control.focus 1 1 (fun _ =>
      let x := Std.eval_vm None x in
      z_to_ltac2_int x).

  (* Necessary because Some and None cannot be used in ltac2: quotations. *)
  Ltac2 some (n : int) : int option := Some n.
  Ltac2 none : int option := None.
End Rep.

(** rep repeatedly applies tac to the goal in a depth-first manner. In
particular, if tac generates multiple subgoals, the process continues
with the first subgoal and only looks at the second subgoal if the
first subgoal (and all goals spawed from it) are solved. If [tac]
fails, the complete process stops (unlike [repeat] which continues
with other subgoals).

[rep n tac] iterates this process at most n times.
[rep <- n tac] backtracks n steps on failure.
[rep <-! tac] backtracks to the last backtracking point on failure.
 (See the comment on [rep_check_backtrack_point] above to see what a backtracking point is)
[rep <-? n tac] backtracks to the n-th last backtracking point on failure.
*)
Tactic Notation "rep" tactic3(tac) :=
  let r := ltac2:(tac |-
    Rep.print_steps (Rep.rep Rep.none Rep.NoBacktrack (fun _ => Ltac1.run tac))) in
  r tac.

(* rep is carefully written such that all goals are passed to Ltac2
and rep can apply tac in a depth-first manner to only the first goal.
In particular, the behavior of [all: rep 10 tac.] is equivalent to
[all: rep 5 tac. all: rep 5 tac.], even if the first call spawns new
subgoals. (See also the tests.) *)
Tactic Notation "rep" int(n) tactic3(tac) :=
  let ntac := do n (refine (1 + _)%Z); refine 0%Z in
  let r := ltac2:(ntac tac |-
    let n := Rep.int_from_z_subgoal (fun _ => Ltac1.run ntac) in
    Rep.print_steps (Rep.rep (Rep.some n) Rep.NoBacktrack (fun _ => Ltac1.run tac))) in
  r ntac tac.

Tactic Notation "rep" "<-" int(n) tactic3(tac) :=
  let ntac := do n (refine (1 + _)%Z); refine 0%Z in
  let r := ltac2:(ntac tac |-
     let n := Rep.int_from_z_subgoal (fun _ => Ltac1.run ntac) in
     Rep.print_steps (Rep.rep (Rep.none) (Rep.BacktrackSteps n) (fun _ => Ltac1.run tac))) in
  r ntac tac.

Tactic Notation "rep" "<-!" tactic3(tac) :=
  let r := ltac2:(tac |-
    Rep.print_steps (Rep.rep Rep.none (Rep.BacktrackPoint 1) (fun _ => Ltac1.run tac))) in
  r tac.

Tactic Notation "rep" "<-?" int(n) tactic3(tac) :=
  let ntac := do n (refine (1 + _)%Z); refine 0%Z in
  let r := ltac2:(ntac tac |-
     let n := Rep.int_from_z_subgoal (fun _ => Ltac1.run ntac) in
     Rep.print_steps (Rep.rep (Rep.none) (Rep.BacktrackPoint n) (fun _ => Ltac1.run tac))) in
  r ntac tac.

Module RepTest.
  Definition DELAY (P : Prop) : Prop := P.

  Ltac DELAY_test_tac :=
    first [
        lazymatch goal with | |- DELAY ?P => change P end |
        exact eq_refl |
        split |
        lazymatch goal with | |- BACKTRACK_POINT ?P => change P end
      ].

  Goal ∃ x, Nat.iter 10 DELAY (x = 1) ∧ Nat.iter 6 DELAY (x = 2). simpl. eexists.
    all: rep DELAY_test_tac.
    1: lazymatch goal with | |- 1 = 2 => idtac | |- _ => fail "unexpected goal" end.
  Abort.

  Goal ∃ x, Nat.iter 10 DELAY (x = 1) ∧ Nat.iter 6 DELAY (x = 2). simpl. eexists.
    all: rep 5 DELAY_test_tac.
    1: lazymatch goal with | |- DELAY (DELAY (DELAY (DELAY (DELAY (DELAY (_ = 1)))))) => idtac | |- _ => fail "unexpected goal" end.
    2: lazymatch goal with | |- DELAY (DELAY (DELAY (DELAY (DELAY (DELAY (_ = 2)))))) => idtac | |- _ => fail "unexpected goal" end.
    (* This should only apply tac to the first subgoal. *)
    all: rep 5 DELAY_test_tac.
    1: lazymatch goal with | |- DELAY (_ = 1) => idtac | |- _ => fail "unexpected goal" end.
    2: lazymatch goal with | |- DELAY (DELAY (DELAY (DELAY (DELAY (DELAY (_ = 2)))))) => idtac | |- _ => fail "unexpected goal" end.
    (* This finishes the first subgoal and use the remaining steps on
    the second subgoal. *)
    all: rep 5 DELAY_test_tac.
    1: lazymatch goal with | |- DELAY (DELAY (DELAY (1 = 2))) => idtac | |- _ => fail "unexpected goal" end.
  Abort.

  Goal ∃ x, Nat.iter 10 DELAY (x = 1) ∧ Nat.iter 6 DELAY (x = 2). simpl. eexists.
    repeat DELAY_test_tac.
    (* Same as rep above. *)
  Abort.

  Goal ∃ x, Nat.iter 10 DELAY (x = 1) ∧ Nat.iter 6 DELAY (x = 2). simpl. eexists.
    do 5? (DELAY_test_tac).
    (* Notice the difference to [rep] above: [do] also applies the
    steps to the second subgoal. *)
  Abort.

  Goal ∃ x, Nat.iter 10 DELAY (x ≤ 1) ∧ Nat.iter 6 DELAY (x = 2). simpl. eexists.
    rep <-3 DELAY_test_tac.
    1: lazymatch goal with | |- DELAY (DELAY (DELAY (_ ≤ 1))) => idtac | |- _ => fail "unexpected goal" end.
    2: lazymatch goal with | |- DELAY (DELAY (DELAY (DELAY (DELAY (DELAY (_ = 2)))))) => idtac | |- _ => fail "unexpected goal" end.
  Abort.

  Goal ∃ x, Nat.iter 10 DELAY (x ≤ 1) ∧ Nat.iter 6 DELAY (x = 2). simpl. eexists.
    repeat DELAY_test_tac.
    (* Notice the difference to [rep] above: [repeat] continues with
    the second subgoal on failure. *)
  Abort.

  Goal BACKTRACK_POINT (Nat.iter 10 DELAY (BACKTRACK_POINT (BACKTRACK_POINT (Nat.iter 10 DELAY (1 = 2))))). simpl.
    all: rep <-! DELAY_test_tac.
    all: do 11 DELAY_test_tac.
    1: lazymatch goal with | |- 1 = 2 => idtac | |- _ => fail "unexpected goal" end.
  Abort.

  Goal BACKTRACK_POINT (Nat.iter 10 DELAY (BACKTRACK_POINT (BACKTRACK_POINT (Nat.iter 10 DELAY (1 = 2))))). simpl.
    all: rep <-? 3 DELAY_test_tac.
    all: do 23 DELAY_test_tac.
    1: lazymatch goal with | |- 1 = 2 => idtac | |- _ => fail "unexpected goal" end.
  Abort.

End RepTest.
