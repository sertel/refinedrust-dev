From lithium Require Import base infrastructure.

Ltac can_solve_tac := fail "provide a can_solve_tac!".
Global Hint Extern 10 (CanSolve ?P) => (change P; can_solve_tac) : typeclass_instances.

Ltac sidecond_hook := idtac.
Ltac unsolved_sidecond_hook := idtac.

(* There can be some goals where one should not call injection on an
hypothesis that is introduced. The [check_injection_tac] hook is called
before injection and allows the client to customize this. *)
Ltac check_injection_tac := idtac.

(** * general normalization infrastructure *)
Ltac normalize_tac := fail "provide a normalize_tac!".
Lemma tac_normalize_goal (P1 P2 : Prop):
  P2 = P1 → P1 → P2.
Proof. by move => ->. Qed.
Lemma tac_normalize_goal_and (P1 P2 T : Prop):
  P2 = P1 → P1 ∧ T → P2 ∧ T.
Proof. by move => ->. Qed.
Lemma tac_normalize_goal_impl (P1 P2 T : Prop):
  P2 = P1 → (P1 → T) → (P2 → T).
Proof. by move => ->. Qed.

Ltac normalize_goal :=
  notypeclasses refine (tac_normalize_goal _ _ _ _); [normalize_tac|].
Ltac normalize_goal_and :=
  notypeclasses refine (tac_normalize_goal_and _ _ _ _ _); [normalize_tac|].
Ltac normalize_goal_impl :=
  notypeclasses refine (tac_normalize_goal_impl _ _ _ _ _); [normalize_tac|].
