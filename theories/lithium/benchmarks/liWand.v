Require Import iris.base_logic.lib.iprop.
Require Import iris.proofmode.proofmode.
Require Import lithium.base.
Require Import lithium.all.

Axiom falso : False.
Goal ∀ Σ (P : nat → iProp Σ),
    ltac:(let x := eval simpl in ([∗ list] i ∈ seq 0 100, P i)%I in exact x) -∗
    ltac:(let x := eval simpl in ([∗ list] i ∈ seq 0 100, P i)%I in exact x).
  intros Σ P. iStartProof.
  (* Set Ltac Profiling. *)
  (* Reset Ltac Profile. *)
  time "liWand" repeat (liEnsureInvariant; liWand).
  (* Show Ltac Profile. *)
  destruct falso.
Time Qed.
