From lithium Require Export base.
From lithium Require Import hooks.

(** This file contains the pure definitions that are used by the
automation. *)

(** * [protected] *)
(** [protected] is wrapped around evars to prevent them from being
accidentally instantiated. *)
Definition protected_def {A} (a : A) : A := a.
Definition protected_aux {A} (a : A) : seal (@protected_def A a). by eexists. Qed.
Definition protected {A} (a : A) : A := (protected_aux a).(unseal).
Definition protected_eq {A} (a : A) : protected a = a := (protected_aux a).(seal_eq).
(** We make [protected] Typeclasses Opaque to tell typeclasses eauto
it can use discrimination nets for it. *)
Global Typeclasses Opaque protected.

Class ContainsProtected {A} (x : A) : Set := contains_protected: ().
Class IsProtected {A} (x : A) : Set := is_protected: ().
Global Hint Extern 0 (ContainsProtected ?x) => (match x with | context [protected _] => exact: tt end) : typeclass_instances.
Global Hint Extern 0 (IsProtected (protected _) ) => (exact: tt) : typeclass_instances.

(** * [CanSolve] *)
(** Exposes the general purpose solver in [can_solve_hook] (see
 hooks.v) as the [can_solve] tactic and via the [CanSolve] typeclass. *)
Tactic Notation "can_solve" := can_solve_hook.
Class CanSolve (P : Prop) : Prop := can_solve_proof: P.
Global Hint Extern 10 (CanSolve ?P) => (change P; can_solve) : typeclass_instances.

(** * [shelve_hint] *)
(** [shelve_hint P] tells the automation it should shelve [P] even if
it contains evars. *)
Definition shelve_hint (P : Prop) : Prop := P.
Global Typeclasses Opaque shelve_hint.
Arguments shelve_hint : simpl never.

(** * [name_hint] *)
(** [name_hint H P] tells the automation to give a name [H] to [P] upon introduction. *)
Require Import Coq.Strings.String.
Definition name_hint (n : string) (P : Prop) : Prop := P.
Global Typeclasses Opaque name_hint.
Arguments name_hint : simpl never.
