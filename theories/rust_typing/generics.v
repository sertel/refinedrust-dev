From refinedrust Require Import type.
From refinedrust Require Import programs.
Set Default Proof Using "Type".

Definition prod_vec (A : Type) (n : nat) := plist id (replicate n A).
Definition list_to_tup {A} (l : list A) : prod_vec A (length l) := list_to_plist A l.

(** ** Operations for partially instantiating the type parameters of a spec and introducing new lifetime/type parameters *)
(** We carefully setup these lemmas and definitions such that the equality rewrites reduce to eq_refl for any concrete application *)
Definition list_insert_shift {A} (l : list A) (n : nat) (x : A) :=
  take n l ++ [x] ++ drop n l.
Lemma list_insert_shift_delete_insert {A} (l : list A) (n : nat) (x : A) :
  Nat.leb (S n) (length l) = true →
  list_insert_shift (delete n l) n x = <[n := x]> l.
Proof.
  intros Hlen.
  rewrite /list_insert_shift.
  induction n as [ | n IH] in l, Hlen |-*; simpl; destruct l; simpl.
  - done.
  - done.
  - done.
  - by rewrite IH.
Defined.
Lemma list_insert_lookup_total {A} `{Inhabited A} (xs : list A) i :
  <[i := xs !!! i ]> xs = xs.
Proof.
  induction i as [ | i IH] in xs |-*; destruct xs; simpl; [done.. | ].
  by rewrite IH.
Defined.

Definition plist_insert_shift {X : Type} {F : X → Type} (Xl : list X) (pl : plist F Xl) (i : nat) (x : X) (fx : F x) : plist F (list_insert_shift Xl i x) :=
  papp (ptake _ pl i) (pcons fx (pdrop _ pl i)).
Import EqNotations.
Definition plist_replace {X : Type} {F : X → Type} (Xl : list X) (i : nat) (Hi : Nat.ltb i (length Xl) = true)
  (pl : plist F (delete i Xl)) (x : X) (fx : F x) : plist F (<[i := x]> Xl) :=
  rew (list_insert_shift_delete_insert _ _ _ Hi) in plist_insert_shift _ pl i x fx.
Definition plist_replace_here {X : Type} `{!Inhabited X} {F : X → Type} (Xl : list X) (i : nat) (Hi : Nat.ltb i (length Xl) = true)
  (pl : plist F (delete i Xl)) (fx : F (Xl !!! i)) : plist F Xl :=
  rew (list_insert_lookup_total _ _) in plist_replace Xl i Hi pl _ fx.

Local Instance inh_Type : Inhabited Type.
Proof. refine (populate _). exact (nat : Type). Qed.

(** Instantiate a given type parameter *)
Definition spec_instantiate_typaram `{!typeGS Σ} {SPEC} {lfts : nat} (rts : list Type)
  (n : nat)
  (Hn : Nat.ltb n (length rts) = true)
  (ty : type (rts !!! n))
  (F : prod_vec lft lfts → plist type rts → SPEC) :
  prod_vec lft lfts → plist type (delete n rts) → SPEC :=
  λ κs tys,
  F κs (plist_replace_here rts n Hn tys ty).

Definition spec_instantiate_typaram_fst `{!typeGS Σ} {SPEC} {lfts : nat} (rt : Type) (rts : list Type)
  (ty : type rt)
  (F : prod_vec lft lfts → plist type (rt :: rts) → SPEC) :
  prod_vec lft lfts → plist type rts → SPEC :=
  λ κs tys,
  F κs (plist_replace_here (rt :: rts) 0 eq_refl tys ty).

(** Instantiate a given lifetime *)
Lemma replicate_length_transparent {A} (x : A) n :
  length (replicate n x) = n.
Proof.
  induction n as [ | n IH]; simpl; first done.
  by rewrite IH.
Defined.

Definition spec_instantiate_lft_fst `{!typeGS Σ} {SPEC} {lfts : nat} (rts : list Type)
  (κ : lft)
  (F : prod_vec lft (S lfts) → plist type rts → SPEC) :
  prod_vec lft lfts → plist type rts → SPEC :=
  λ κs tys,
  F (κ -:: κs) tys.

(** Add a new type parameter *)
Definition spec_add_typaram `{!typeGS Σ} {SPEC} {lfts : nat} (rts : list Type)
  (rt : Type) (st : syn_type)
  (F : type rt → prod_vec lft lfts → plist type rts → SPEC) :
  prod_vec lft lfts → plist type (rt :: rts) → SPEC :=
  λ κs '(ty *:: tys),
  F ty κs tys.


(** Collapse two levels of specification parameters *)
Lemma take_replicate_add_transparent {A} (x : A) n1 n2 :
  take n1 (replicate (n1 + n2) x) = replicate n1 x.
Proof.
  induction n1 as [ | n1 IH]; simpl; first done.
  by rewrite IH.
Defined.
Lemma take_app_transparent {A} (xs ys : list A) :
  take (length xs) (xs ++ ys) = xs.
Proof.
  induction xs as [ | x xs IH]; simpl; first done.
  by rewrite IH.
Defined.
Lemma drop_replicate_add_transparent {A} (x : A) n1 n2 :
  drop n1 (replicate (n1 + n2) x) = replicate n2 x.
Proof.
  induction n1 as [ | n1 IH]; simpl; first done.
  by rewrite IH.
Defined.
Lemma drop_app_transparent {A} (xs ys : list A) :
  drop (length xs) (xs ++ ys) = ys.
Proof.
  induction xs as [ | x xs IH]; simpl; first done.
  by rewrite IH.
Defined.

Definition spec_collapse_params `{!typeGS Σ} {SPEC} {lfts1 lfts2 : nat} (rts1 rts2 : list Type)
  (F : prod_vec lft lfts1 → plist type rts1 → prod_vec lft lfts2 → plist type rts2 → SPEC) :
  prod_vec lft (lfts1 + lfts2) → plist type (rts1 ++ rts2) → SPEC :=
  λ κs tys,
  F
    (rew (take_replicate_add_transparent _ lfts1 lfts2) in ptake _ κs lfts1)
    (rew (take_app_transparent rts1 rts2) in ptake _ tys (length rts1))
    (rew (drop_replicate_add_transparent _ lfts1 lfts2) in pdrop _ κs lfts1 )
    (rew (drop_app_transparent rts1 rts2) in pdrop _ tys (length rts1)).


Definition spec_instantiated `{!typeGS Σ} {SPEC : Type} (F : prod_vec lft 0 → plist type [] → SPEC) : SPEC :=
  F -[] -[].
Definition spec_with `{!typeGS Σ} (lfts : nat) (rts : list Type) (SPEC : Type) :=
  prod_vec lft lfts → plist type rts → SPEC.
Arguments spec_with {_ _} / _ _ .

Notation "x '<TY>' T" := (spec_instantiate_typaram_fst _ _ T x) (left associativity, at level 81, only printing) : stdpp_scope.
Notation "x '<TY>@{' n '}' T" := (spec_instantiate_typaram _ n _ T x) (left associativity, at level 81, only printing) : stdpp_scope.
Notation "x '<LFT>' T" := (spec_instantiate_lft_fst _ T x) (left associativity, at level 81, only printing) : stdpp_scope.
Notation "x '<INST!>'" := (spec_instantiated x) (left associativity, at level 81) : stdpp_scope.
Notation "x '<MERGE!>'" := (spec_collapse_params _ _ x) (left associativity, at level 181, only printing) : stdpp_scope.


Notation "x '<TY>' T" := (
  ltac:(
    match type of x%function with
    | prod_vec _ _ → plist type ?rt → _ =>
        let rts := eval simpl in rt in
        match rts with
        | (?rt :: ?rts) =>
          refine (spec_instantiate_typaram_fst rt rts T x)
        end
    | spec_with _ ?rt _ =>
        let rts := eval simpl in rt in
        match rts with
        | (?rt :: ?rts) =>
          refine (spec_instantiate_typaram_fst rt rts T x)
        end
    | ?ty => idtac "<TY> failed with " ty
    end))
     (left associativity, at level 81, only parsing) : stdpp_scope.

Notation "x '<TY>@{' n '}' T" := (
  ltac:(
    match type of x%function with
    | prod_vec _ _ → plist type ?rt → _ =>
        refine (spec_instantiate_typaram rt n eq_refl T x)
    | spec_with _ ?rt _ =>
        refine (spec_instantiate_typaram rt n eq_refl T x)
    | ?ty => idtac "<TY> failed with " ty
    end))
     (left associativity, at level 81, only parsing) : stdpp_scope.

Notation "x '<LFT>' T" := (
  ltac:(
    match type of x%function with
    | prod_vec _ _ → plist type ?rts → _ =>
        refine (spec_instantiate_lft_fst rts T x)
    | spec_with _ ?rts _ =>
        refine (spec_instantiate_lft_fst rts T x)
    end))
     (left associativity, at level 81, only parsing) : stdpp_scope.

Notation "x '<MERGE!>'" := (
  ltac:(
    match type of x%function with
    | prod_vec _ _ → plist type ?rts1 → prod_vec _ _ → plist type ?rts2 → _ =>
        refine (spec_collapse_params rts1 rts2 x)
    | spec_with _ ?rts1 (prod_vec _ _ → plist type ?rts2 → _) =>
        refine (spec_collapse_params rts1 rts2 x)
    | prod_vec _ _ → plist type ?rts1 → (spec_with _ ?rts2 _) =>
        refine (spec_collapse_params rts1 rts2 x)
    | spec_with _ ?rts1 (spec_with _ ?rts2 _) =>
        refine (spec_collapse_params rts1 rts2 x)
    end))
     (left associativity, at level 181, only parsing) : stdpp_scope.

Notation "<SIMPL> x" := (ltac:(let __x := eval simpl in (x) in refine __x)) (right associativity, at level 180, only parsing) : stdpp_scope.

Notation "'spec!' κs ':' n '|' tys ':' rts ',' S" :=
  ((fun κs tys => S) : prod_vec lft n → plist type rts → _) (at level 99, S at level 180, κs pattern, tys pattern) : stdpp_scope.
