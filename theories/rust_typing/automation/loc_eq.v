(** Adapted from RefinedC *)
From lithium Require Import all.
From caesium Require Import base lang.
From refinedrust Require Import solvers programs program_rules automation.

(** This file contains a solver for location (semantic) equality based on [lia]
and an [autorewrite] hint database [refinedrust_loc_eq_rewrite] that the user can
extend with more rewriting rules. *)

(** * Hint database *)

Create HintDb refinedrust_loc_eq_rewrite discriminated.

(** Rules to inject [nat] operations in to [Z]. *)
#[export] Hint Rewrite Nat2Z.inj_mul : refinedrust_loc_eq_rewrite.
#[export] Hint Rewrite Nat2Z.inj_add : refinedrust_loc_eq_rewrite.
#[export] Hint Rewrite Nat2Z.inj_sub using lia : refinedrust_loc_eq_rewrite.
#[export] Hint Rewrite Z2Nat.id using lia : refinedrust_loc_eq_rewrite.

(** Rule to eliminate [Z.shiftl]. *)
#[export] Hint Rewrite Z.shiftl_mul_pow2 using lia : refinedrust_loc_eq_rewrite.

(** * Tactics *)

Lemma eq_loc (l1 l2 : loc): l1.1 = l2.1 → l1.2 = l2.2 → l1 = l2.
Proof. destruct l1, l2 => /= -> -> //. Qed.

Ltac simplify_layout_goal_noshelve :=
  unshelve simplify_layout_goal;
  [ unfold_common_defs; solve_goal.. | ].

(** Turns an equality over locations into an equality over physical addresses
(in type [Z]) that has been simplified with [autorewrite]. This tactics only
succeeds if the compared locations have convertible allocation ids. *)
Ltac prepare_loc_eq :=
  (* Sanity check on the goal. *)
  lazymatch goal with
  | |- @eq val (val_of_loc _) (val_of_loc _) => f_equal
  | |- @eq ?A _ _ => unify A loc
  | |- @eq _ _ _  => fail "[simpl_loc_eq]: goal not an equality between locations"
  | |- _          => fail "[simpl_loc_eq]: goal not an equality"
  end;
  (* Remove all [offset_loc] and [shift_loc]. *)
  rewrite ?/offset_loc ?shift_loc_assoc; rewrite ?/shift_loc;
  (* Unfold OffsetLocSt *)
  (*GetMemberLocSt*)
  (*GetMemberUnionLocSt*)
  (*GetEnumDataLocSt*)
  (*GetEnumDiscriminantLocSt*)
  rewrite /OffsetLocSt;
  (* Checking that both sides have the same [alloc_id]. *)
  notypeclasses refine (eq_loc _ _ _ _); [ reflexivity | simpl ];
  (* Rewrite with the hints. *)
  autorewrite with refinedrust_loc_eq_rewrite;
  (* Simplify layout terms *)
  simplify_layout_goal_noshelve; simpl.

(** Solver for location equality. *)
Ltac solve_loc_eq :=
  (* We try [reflexivity] first since it very often suffices. *)
  first [ reflexivity | prepare_loc_eq; lia ].


Section test.
  Context `{!LayoutAlg}.
  Context (l : loc).
  Context (id : prov).
  Context (a : addr).
  Context (n n1 n2 n3 : Z).
  Context (i j : nat).
  Context (PAGE_SIZE : Z := 4096).

  Goal (l = l)%Z.
  solve_loc_eq. Qed.

  Goal (@eq loc (id, a) (id, a))%Z.
  solve_loc_eq. Qed.

  Goal ((l.1, l.2) = l)%Z.
  solve_loc_eq. Qed.

  Goal ((l.1, l.2 + n)%Z = l +ₗ n)%Z.
  solve_loc_eq. Qed.

  Goal ((l +ₗ n1 +ₗ n2) = (l +ₗ (n1 + n2)))%Z.
  solve_loc_eq. Qed.

  Goal ((l +ₗ 0%nat * n) = l)%Z.
  solve_loc_eq. Qed.

  Goal ((id, a + n1 + n2) = (id, a + (n1 + n2)))%Z.
  solve_loc_eq. Qed.

  Goal ((l +ₗ (n + (i + j)%nat)) = (l +ₗ (n + i + j)))%Z.
  solve_loc_eq. Qed.

  Goal ((l +ₗ (n * PAGE_SIZE + i ≪ 12)) = (l +ₗ (n + i) * PAGE_SIZE))%Z.
  solve_loc_eq. Qed.

  Goal ((l +ₗ (n1 + 0%nat) * n2) = (l +ₗ (n1 * n2)))%Z.
  solve_loc_eq. Qed.

  Goal ((l +ₗ (n1 + (i + j)%nat) * n2) = (l +ₗ (n1 + i + j) * n2))%Z.
  solve_loc_eq. Qed.

  Goal (l = (l.1, l.2 * 1))%Z.
  solve_loc_eq. Qed.

  Goal (l offsetst{IntSynType u8}ₗ n1) = l +ₗ (ly_size u8 * n1).
  init_cache; solve_loc_eq. Qed.

  Goal (l offsetst{IntSynType usize_t}ₗ n1) = l +ₗ (ly_size usize_t * n1).
  init_cache; solve_loc_eq. Qed.

  (*Goal (l +ₗ offset) = l +ₗ (len * size_of  *)
End test.

(** ** Typing rules using the semantic equality solver*)
Inductive FICLocSemantic : Set :=.
Lemma tac_solve_loc_eq `{!typeGS Σ} π {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) k1 k2 l1 l2 r1 r2 :
  l1 = l2 →
  FindHypEqual FICLocSemantic (l1 ◁ₗ[π, k1] r1 @ lt1) (l2 ◁ₗ[π, k2] r2 @ lt2) (l1 ◁ₗ[π, k2] r2 @ lt2).
Proof. by move => ->. Qed.

Global Hint Extern 10 (FindHypEqual FICLocSemantic (_ ◁ₗ[_, _] _ @ _) (_ ◁ₗ[_, _] _ @ _) _) =>
  (notypeclasses refine (tac_solve_loc_eq _ _ _ _ _ _ _ _ _ _); solve_loc_eq) : typeclass_instances.

Lemma tac_loc_in_bounds_solve_loc_eq `{!typeGS Σ} l1 l2 pre1 pre2 suf1 suf2:
  l1 = l2 →
  FindHypEqual FICLocSemantic (loc_in_bounds l1 pre1 suf1) (loc_in_bounds l2 pre2 suf2) (loc_in_bounds l1 pre2 suf2).
Proof. by move => ->. Qed.

Global Hint Extern 10 (FindHypEqual FICLocSemantic (loc_in_bounds _ _ _) (loc_in_bounds _ _ _) _) =>
  (notypeclasses refine (tac_loc_in_bounds_solve_loc_eq _ _ _ _ _ _ _); solve_loc_eq) : typeclass_instances.

Global Instance find_in_context_type_loc_semantic_inst `{!typeGS Σ} π l :
  FindInContext (FindLoc l π) FICLocSemantic | 20 :=
  λ T, i2p (find_in_context_type_loc_id l π T).
Global Instance find_in_context_type_locp_semantic_inst `{!typeGS Σ} π l :
  FindInContext (FindLocP l π) FICLocSemantic | 20 :=
  λ T, i2p (find_in_context_type_locp_loc l π T).
Global Instance find_in_context_type_loc_with_rt_semantic_inst `{!typeGS Σ} rt π l :
  FindInContext (FindLocWithRt rt l π) FICLocSemantic | 20 :=
  λ T, i2p (find_in_context_type_loc_with_rt_id l π T).

(*
Global Instance find_in_context_type_val_P_loc_semantic_inst `{!typeG Σ} (l : loc) :
  FindInContext (FindValP l) FICLocSemantic | 20 :=
  λ T, i2p (find_in_context_type_val_P_loc_id l T).
Global Instance find_in_context_loc_in_bounds_semantic_inst `{!typeG Σ} l :
  FindInContext (FindLocInBounds l) FICLocSemantic | 20 :=
  λ T, i2p (find_in_context_loc_in_bounds l T).
Global Instance find_in_context_loc_in_bounds_type_semantic_inst `{!typeG Σ} l :
  FindInContext (FindLocInBounds l) FICLocSemantic | 30 :=
  λ T, i2p (find_in_context_loc_in_bounds_loc l T).

 *)
