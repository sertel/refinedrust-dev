From lithium Require Import base.

Class SimplExist (T : Type) (e : T → Prop) (Q: Prop) := simpl_exist_proof : Q → ∃ x, e x.
Class SimplForall (T : Type) (n : nat) (e : T → Prop) (Q: Prop) := simpl_forall_proof : Q → ∀ x, e x.

Class SimplImplUnsafe (changed : bool) (P : Prop) (Ps : Prop → Prop) := simpl_impl_unsafe T: (Ps T) → (P → T).
Class SimplAndUnsafe (changed : bool) (P : Prop) (Ps : Prop → Prop) := simpl_and_unsafe T: (Ps T) → (P ∧ T).
Global Instance simplimpl_unsafe_id (P : Prop) : SimplImplUnsafe false P (λ T, P → T) | 1000.
Proof. by move => ?. Qed.
Global Instance simpland_unsafe_id (P : Prop) : SimplAndUnsafe false P (λ T, P ∧ T) | 1000.
Proof. by move => ?. Qed.

Global Instance simpland_unsafe_not_neq {A} (x y : A) :
  SimplAndUnsafe true (¬ (x ≠ y)) (λ T, x = y ∧ T) | 1000.
Proof. move => T [? ?]. by eauto. Qed.

(* safe variants which ensure that no information is lost *)
(* changed = false can be used to prevent infinite loops when adding
additional information. See below for more an example. It only makes sense for Impl *)
Class SimplImpl (changed : bool) (P : Prop) (Ps : Prop → Prop) := simpl_impl T: (Ps T) ↔ (P → T).
Class SimplAnd (P : Prop) (Ps : Prop → Prop) := simpl_and T: (Ps T) ↔ (P ∧ T).
Global Instance simplimpl_simplunsafe c P Ps {Hi: SimplImpl c P Ps} :
  SimplImplUnsafe c P Ps.
Proof. unfold SimplImpl, SimplImplUnsafe in *. naive_solver. Qed.
Global Instance simpland_simplunsafe P Ps {Hi: SimplAnd P Ps} :
  SimplAndUnsafe true P Ps.
Proof. unfold SimplAnd, SimplAndUnsafe in *. naive_solver. Qed.

Class SimplImplRel {A} (R : relation A) (changed : bool) (x1 x2 : A) (Ps : Prop → Prop)
  := simpl_impl_eq T: (Ps T) ↔ (R x1 x2 → T).
Class SimplAndRel {A} (R : relation A) (x1 x2 : A) (Ps : Prop → Prop)
  := simpl_and_eq T: (Ps T) ↔ (R x1 x2 ∧ T).
Global Instance simpl_impl_rel_inst1 {A} c R (x1 x2 : A) Ps `{!SimplImplRel R c x1 x2 Ps} :
  SimplImpl c (R x1 x2) Ps.
Proof. unfold SimplImplRel, SimplImpl in *. naive_solver. Qed.
Global Instance simpl_impl_rel_inst2 {A} c R (x1 x2 : A) Ps `{!SimplImplRel R c x2 x1 Ps} `{!Symmetric R} :
  SimplImpl c (R x1 x2) Ps.
Proof. unfold SimplImplRel, SimplImpl in *. naive_solver. Qed.
Global Instance simpl_and_rel_inst1 {A} R (x1 x2 : A) Ps `{!SimplAndRel R x1 x2 Ps} :
  SimplAnd (R x1 x2) Ps.
Proof. unfold SimplAndRel, SimplAnd in *. naive_solver. Qed.
Global Instance simpl_and_rel_inst2 {A} R (x1 x2 : A) Ps `{!SimplAndRel R x2 x1 Ps} `{!Symmetric R} :
  SimplAnd (R x1 x2) Ps.
Proof. unfold SimplAndRel, SimplAnd in *. naive_solver. Qed.

Class SimplBoth (P1 P2 : Prop) := simpl_both: P1 ↔ P2.
Global Instance simpl_impl_both_inst P1 P2 {Hboth : SimplBoth P1 P2}:
  SimplImpl true P1 (λ T, P2 → T).
Proof. unfold SimplBoth in Hboth. split; naive_solver. Qed.
Global Instance simpl_and_both_inst P1 P2 {Hboth : SimplBoth P1 P2}:
  SimplAnd P1 (λ T, P2 ∧ T).
Proof. unfold SimplBoth in Hboth. split; naive_solver. Qed.

Class SimplBothRel {A} (R : relation A) (x1 x2 : A) (P2 : Prop) := simpl_both_eq: R x1 x2 ↔ P2.
Global Instance simpl_both_rel_inst1 {A} R (x1 x2 : A) P2 `{!SimplBothRel R x1 x2 P2}:
  SimplBoth (R x1 x2) P2.
Proof. unfold SimplBothRel, SimplBoth in *. naive_solver. Qed.
Global Instance simpl_both_rel_inst2 {A} R (x1 x2 : A) P2 `{!SimplBothRel R x2 x1 P2} `{!Symmetric R}:
  SimplBoth (R x1 x2) P2.
Proof. unfold SimplBothRel, SimplBoth in *. naive_solver. Qed.

Lemma apply_simpl_impl b P Ps T {Himpl: SimplImplUnsafe b P Ps} :
  (b = b → Ps T) → (P → T).
Proof. move => ?. apply Himpl. eauto. Qed.
Lemma apply_simpl_and b P Ps T {Himpl: SimplAndUnsafe b P Ps} :
  (b = b → Ps T) → (P ∧ T).
Proof. move => ?. apply Himpl. eauto. Qed.
