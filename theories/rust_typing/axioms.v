Require Import Coq.Logic.ProofIrrelevance.
From Equations Require Import Equations.
From stdpp Require Import base.
From iris Require Import prelude.
Require Import Coq.Logic.EqdepFacts.

(** We assume proof irrelevance. *)

Lemma proof_irrelevance (P : Prop) (p1 p2 : P) : p1 = p2.
Proof. apply proof_irrelevance. Qed.

(* TODO: we currently require ProofIrrelevance only for getting the ltype induction principle.
  We might be able to get by without it however and just require UIP. *)

(* Equations seems to change the arguments for eq_refl, restore *)
Global Arguments eq_refl {A}%type_scope {x}, [_] _.

(* Uniqueness of identity proofs *)
(*Axiom (UIP_t : ∀ T, UIP_ T).*)

Lemma UIP_t T : UIP_ T.
Proof.
  intros a b -> Heq.
  rewrite (proof_irrelevance _ Heq eq_refl).
  done.
Qed.

Lemma UIP_refl : ∀ (X : Type) (x : X) (Heq : x = x), Heq = eq_refl x.
Proof.
  intros X x Heq. apply UIP_t.
Qed.

(* Instance for Equations to find. *)
Global Instance UIP_inst X : UIP X.
Proof. apply UIP_t. Qed.
Global Set Equations With UIP.

Import EqNotations.
Lemma existT_inj {X P} (p : X) (x y : P p) :
  existT p x = existT p y → x = y.
Proof.
  revert x y.
  enough (∀ a b, a = b → ∀ Heq' : projT1 a = projT1 b, rew [P] Heq' in projT2 a = projT2 b) as H.
  { intros x y Heq. by specialize (H _ _ Heq eq_refl). }
  intros a b Heq. destruct Heq. intros Heq.
  specialize (UIP_t _ _ _ Heq eq_refl) as ->. done.
Qed.

Section eq.
  (* TODO move *)
  Lemma rew_invert {X Y} {F : Type → Type} (Heq : X = Y) (z : F X):
    rew <-[F] Heq in (rew [F] Heq in z) = z.
  Proof.
    destruct Heq. done.
  Qed.
  Lemma rew_invert' {X Y} {F : Type → Type} (Heq : Y = X) (z : F X):
    rew [F] Heq in (rew <-[F] Heq in z) = z.
  Proof.
    destruct Heq. done.
  Qed.

  Lemma elim_id_cast_l {A} C a (Ha : a = a) (x : C a) :
    @eq_rect A a C x _  Ha = x.
  Proof.
    rewrite (UIP_refl _ _ Ha).
    done.
  Qed.
  Lemma elim_id_cast_r {A} C a (Ha : a = a) (x : C a) :
    x = @eq_rect A a C x _  Ha.
  Proof.
    rewrite (UIP_refl _ _ Ha).
    done.
  Qed.
  Lemma rew_swap' {A} (P : A → Type) (x1 x2 : A) (Hx : x1 = x2) y1 y2 :
    y2 = rew [P] Hx in y1 →
    rew <-[P] Hx in y2 = y1.
  Proof.
    subst. done.
  Qed.

  Lemma rew_UIP {X} (F : Type → Type) (Heq : X = X) (z : F X) :
    rew [F] Heq in z = z.
  Proof. rewrite (UIP_refl _ _ Heq). done. Qed.
  Lemma rew_UIP' {X} (F : Type → Type) (Heq : X = X) (z : F X) :
    rew <-[F] Heq in z = z.
  Proof. rewrite (UIP_refl _ _ Heq). done. Qed.

End eq.
