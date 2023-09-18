From lithium Require Export base.
From caesium.config Require Export config.
Set Default Proof Using "Type".

Global Unset Program Cases.
Global Set Keyed Unification.
Global Open Scope Z_scope.

(* TODO move *)
Definition flip3 {A B C D} (f : A → B → C → D) : C → A → B → D :=
  λ c a b, f a b c.
Lemma Forall3_flip3 {A B C} (P : A → B → C → Prop) l1 l2 l3 :
  Forall3 P l1 l2 l3 ↔ Forall3 (flip3 P) l3 l1 l2.
Proof.
  induction l1 as [ | x l1 IH] in l2, l3 |-*; destruct l2 as [ | y l2]; destruct l3 as [ | z l3]; simpl;
    split; inversion 1; subst; econstructor; naive_solver.
Qed.
Lemma Forall3_Forall2_impl {A B C} (P : A → B → C → Prop) (Q : B → C → Prop) l1 l2 l3 :
  (∀ x y z, P x y z → Q y z) →
  Forall3 P l1 l2 l3 →
  Forall2 Q l2 l3.
Proof.
  intros Hi. induction l1 as [ | x l1 IH] in l2, l3 |-*; destruct l2 as [ | y l2]; destruct l3 as [ | z l3]; simpl;
    inversion 1; econstructor; naive_solver.
Qed.
Lemma Forall2_Forall_impl {A B} (P : A → B → Prop) (Q : B → Prop) l1 l2 :
  (∀ x y, P x y → Q y) →
  Forall2 P l1 l2 →
  Forall Q l2.
Proof.
  intros Hi. induction l1 as [ | x l1 IH] in l2 |-*; destruct l2 as [ | y l2]; simpl;
    inversion 1; econstructor; naive_solver.
Qed.

Lemma Forall2_cons_inv {A B} (P : A → B → Prop) l r x y :
  Forall2 P (x :: l) (y :: r) →
  P x y ∧ Forall2 P l r.
Proof.
  inversion 1; subst. done.
Qed.


(* TODO Move *)
Lemma drop_app' {A} (l k : list A) n :
  length l = n → drop n (l ++ k) = k.
Proof. intros <-. apply drop_app. Qed.
Lemma take_app' {A} (l k : list A) n :
  length l = n → take n (l ++ k) = l.
Proof. intros <-. apply take_app. Qed.


(* TODO move *)
Lemma list_to_map_lookup_fst {A B} `{Countable A} (l : list (A * B)) k : 
  k ∈ l.*1 →
  NoDup (l.*1) →
  ∃ v, list_to_map (M := gmap A B) l !! k = Some v.
Proof.
  induction l as [ | [k1 v1] l IH]; simpl.
  { intros []%elem_of_nil. }
  intros [-> | Ha]%elem_of_cons Hnodup.
  { exists v1. apply lookup_insert. }
  inversion Hnodup as [ | ? ? Hnel Hnodup']; subst.
  efeed pose proof IH as Hb; [done | done | ].
  destruct Hb as (v & Hlook). exists v.
  rewrite lookup_insert_ne; first done.
  intros ->. apply Hnel. done.
Qed.




(* TODO move *)
Definition list_map_option {X Y} (f : X → option Y) (l : list X) : option (list Y) :=
  foldr (λ (x : X) (y : option (list Y)),
    y ← y;
    h ← f x;
    Some (h :: y)) (Some ([] : list Y)) l.
Lemma list_map_option_Some_length {X Y} (f : X → option Y) l l2 :
  list_map_option f l = Some l2 →
  length l = length l2.
Proof.
  induction l in l2 |-*; simpl; intros Heq; simplify_option_eq; naive_solver.
Qed.
Lemma list_map_option_alt {X Y} (f : X → option Y) xs ys :
  list_map_option f xs = Some ys ↔ Forall2 (λ x y, f x = Some y) xs ys.
Proof.
  induction xs as [ | x xs IH] in ys |-*; simpl.
  - split.
    + intros [= <-]. constructor.
    + inversion 1; done.
  - split.
    + intros (ys' & Hrec & Ha)%bind_Some.
      eapply bind_Some in Ha as (y & ? & [= <-]).
      constructor; first done. by eapply IH.
    + intros(y & ys' & Ha & Hrec & ->)%Forall2_cons_inv_l.
      erewrite (proj2 (IH _)); last done. rewrite Ha; done.
Qed.
Lemma list_map_option_lookup {X Y} (f : X → option Y) l l2 i x :
  list_map_option f l = Some l2 →
  l !! i = Some x →
  ∃ y, l2 !! i = Some y ∧ Some y = f x.
Proof.
  induction l as [ | a l IH] in l2, i |-*; simpl.
  - intros [= <-]. done.
  - intros Heq. apply bind_Some in Heq as (acc & Ha & Hx).
    apply bind_Some in Hx as (y & Hx & [= <-]).
    destruct i as [ | i]; simpl. { intros. simplify_option_eq. eauto. }
    intros Hb. eapply IH in Hb; last done. done.
Qed.
Lemma list_map_option_nil_inv_r {X Y} (f : X → option Y) l :
  list_map_option f l = Some [] → l = [].
Proof.
  destruct l as [ | x l]; first done.
  simpl. destruct (list_map_option f l); last done.
  simpl. destruct (f x); done.
Qed.
Lemma list_map_option_nil_inv_l {X Y} (f : X → option Y) l :
  list_map_option f [] = Some l → l = [].
Proof.
  simpl. injection 1 as [= <-]. done.
Qed.
Lemma list_map_option_cons_inv_r {X Y} (f : X → option Y) xs ys y :
  list_map_option f xs = Some (y :: ys) →
  ∃ x xs', xs = x :: xs' ∧ f x = Some y ∧ list_map_option f xs' = Some ys.
Proof.
  destruct xs as [ | x xs']; first done.
  simpl.
  destruct (list_map_option f xs') eqn:Heq; last done.
  simpl. destruct (f x) eqn:Heq2; last done.
  simpl. injection 1 as [= -> ->]. eauto.
Qed.
Lemma list_map_option_cons_inv_l {X Y} (f : X → option Y) x xs ys :
  list_map_option f (x :: xs) = Some ys →
  ∃ y ys', ys = y :: ys' ∧ f x = Some y ∧ list_map_option f xs = Some ys'.
Proof.
  simpl. destruct (list_map_option f xs) eqn:Heq; last done.
  simpl. destruct (f x) eqn:Heq2; last done.
  simpl. intros [= <-]. eauto.
Qed.
