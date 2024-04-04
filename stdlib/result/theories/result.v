From refinedrust Require Import typing.

Notation Ok x := (inl x) (only parsing).
Notation Err x := (inr x) (only parsing).

Notation result A B := (sum A B) (only parsing).

(*Notation "'<#>' x" := (fmap (M := list) PlaceIn x) (at level 30).*)
(*Notation "'<#>@{' A '}' x" := (fmap (M := A) PlaceIn x) (at level 30).*)
Notation "'<#>@{' 'result' '}' x" := (sum_map PlaceIn PlaceIn x) (at level 30).

Definition is_Ok {A B} (x : result A B) :=
  ∃ y : A, x = Ok y.
Global Instance is_Ok_dec {A B} (x : result A B) : Decision (is_Ok x).
Proof.
  destruct x.
  - left. eexists _. done.
  - right. intros [y Hx]. naive_solver.
Defined.

Definition is_Err {A B} (x : result A B) :=
  ∃ y : B, x = Err y.
Global Instance is_Err_dec {A B} (x : result A B) : Decision (is_Err x).
Proof.
  destruct x.
  - right. intros [y Hx]. naive_solver.
  - left. eexists _. done.
Defined.


Definition if_Ok {A B} (x : result A B) (ϕ : A → Prop) : Prop :=
  match x with
  | Ok x => ϕ x
  | _ => True
  end.
Definition if_Err {A B} (x : result A B) (ϕ : B → Prop) : Prop :=
  match x with
  | Err x => ϕ x
  | _ => True
  end.

(** The same for Iris *)
Section iris.
Context `{!typeGS Σ}.

Definition if_iOk {A B} (x : result A B) (ϕ : A → iProp Σ) : iProp Σ :=
  match x with
  | Ok x => ϕ x
  | _ => True
  end.
Definition if_iErr {A B} (x : result A B) (ϕ : B → iProp Σ) : iProp Σ :=
  match x with
  | Err x => ϕ x
  | _ => True
  end.
End iris.

Definition map_inl {A A' B} (f : A → A') : A + B -> A' + B :=
  sum_map f id.
Definition map_inr {A B B'} (f : B → B') : A + B -> A + B' :=
  sum_map id f.
