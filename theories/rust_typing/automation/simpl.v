From refinedrust Require Export base hlist type ltypes.
From lithium Require Export all.
Set Default Proof Using "Type".

(** ** Additional Simpl instances *)
Global Instance simpl_eq_hlist_cons A {F} (X : A) (XS : list A) (x : F X) (y : F X) (xs ys : hlist F XS) :
  SimplAnd ((x +:: xs) = (y +:: ys)) (λ T, x = y ∧ xs = ys ∧ T).
Proof.
  split.
  - intros (-> & -> & HT). done.
  - intros (Heq & HT). injection Heq.
    intros ->%existT_inj ->%existT_inj. done.
Qed.

Global Instance simpl_eq_plist_cons A {F} (X : A) (XS : list A) (x : F X) (y : F X) (xs ys : plist F XS) :
  SimplAnd ((x -:: xs) = (y -:: ys)) (λ T, x = y ∧ xs = ys ∧ T).
Proof.
  split.
  - intros (-> & -> & HT). done.
  - intros (Heq & HT). injection Heq. done.
Qed.

Global Instance simpl_eq_phd {A} {F : A → Type} (Xs : list A) (X : A) (xs : plist F (X :: Xs)) (x : F X)   :
  SimplBothRel (eq) (x) (phd xs) (∃ c : plist F Xs, xs = pcons x c).
Proof.
  split.
  - intros ->. destruct xs as [? ?]. eauto.
  - intros (c & ->). done.
Qed.
Global Instance simpl_eq_ptl {A} {F : A → Type} (Xs : list A) (X : A) (xs : plist F (X :: Xs)) (xs' : plist F Xs)   :
  SimplBothRel (eq) (xs') (ptl xs) (∃ c : F X, xs = pcons c xs').
Proof.
  split.
  - intros ->. destruct xs as [? ?]. eauto.
  - intros (c & ->). done.
Qed.

Global Instance simpl_hmap_nil {A} {F G : A → Type} (f : ∀ x : A, F x → G x) (l : hlist F []) (l2 : hlist G []) :
  SimplBothRel eq (f +<$> l) l2 (l = +[] ∧ l2 = +[]).
Proof.
  split.
  - inv_hlist l; done.
  - intros [-> ->]; done.
Qed.
Global Instance simpl_hmap_cons_impl {A} {F G : A → Type} (f : ∀ x : A, F x → G x) (X : A) (Xs : list A) (x : G X) (l2 : hlist G Xs) (l : hlist F (X :: Xs)) :
  SimplImplRel eq true (f +<$> l) (x +:: l2) (λ T : Prop,
    ∀ (x' : F X) (l2' : hlist F Xs), l = x' +:: l2' → f _ x' = x → f +<$> l2'  = l2 → T).
Proof.
  intros T. split.
  - inv_hlist l => x0 xl0 Hf /=.
    injection 1 => Heq1 Heq2.
    apply existT_inj in Heq1. apply existT_inj in Heq2. subst.
    eapply Hf; reflexivity.
  - intros Hf x' l2' -> <- <-. apply Hf. done.
Qed.
Global Instance simpl_hmap_cons_and {A} {F G : A → Type} (f : ∀ x : A, F x → G x) (X : A) (Xs : list A) (x : G X) (l2 : hlist G Xs) (l : hlist F (X :: Xs)) :
  SimplAndRel eq (f +<$> l) (x +:: l2) (λ T : Prop,
    ∃ (x' : F X) (l2' : hlist F Xs), l = x' +:: l2' ∧ f _ x' = x ∧ f +<$> l2'  = l2 ∧ T).
Proof.
  intros T. split.
  - intros (x' & l2' & -> & <- & <- & HT). done.
  - intros (Ha & HT). inv_hlist l => x0 xl0 Ha.
    injection Ha => Heq1 Heq2. apply existT_inj in Heq1. apply existT_inj in Heq2. subst.
    eexists _, _. done.
Qed.

Global Instance simpl_and_list_lookup_total_unsafe {A} `{!Inhabited A} (l : list A) i (x : A) :
  SimplAndUnsafe (l !!! i = x) (λ T, l !! i = Some x ∧ T).
Proof.
  intros T [Hlook HT]. split; last done. by apply list_lookup_total_correct.
Qed.

Global Instance simpl_exist_hlist_nil {X} (F : X → Type) Q : 
  SimplExist (hlist F []) Q (Q +[]).
Proof.
  rewrite /SimplExist. naive_solver.
Qed.
Global Instance simpl_exist_plist_nil {X} (F : X → Type) Q : 
  SimplExist (plist F []) Q (Q -[]).
Proof.
  rewrite /SimplExist. naive_solver.
Qed.


(** Try to find a lookup proof with some abstract condition [P] *)
Lemma simpl_list_lookup_assum {A} {P : nat → Prop} {E : nat → A} (l : list A) j x :
  (∀ i, P i → l !! i = Some (E i)) →
  CanSolve (P j) →
  SimplBothRel (=) (l !! j) (Some x) (x = E j).
Proof.
  unfold SimplBothRel, CanSolve, TCDone in *; subst.
  intros HL HP.
  apply HL in HP. rewrite HP. naive_solver.
Qed.
Global Hint Extern 50 (SimplBothRel (=) (?l !! ?j) (Some ?x) (_)) =>
  (* Important: we backtrack in case there are multiple matching facts in the context. *)
  match goal with
  | H : ∀ i, _ → l !! i = Some _ |- _ =>
      notypeclasses refine (simpl_list_lookup_assum l j x H _);
      apply _
  end : typeclass_instances.

Global Instance simpl_eq_PlaceIn {rt} (n m : rt) : SimplBothRel (=) (A := place_rfn rt) (#n) (#m) (n = m).
Proof. split; naive_solver. Qed.
Global Instance simpl_eq_PlaceGhost {rt} (γ1 γ2 : gname) : SimplBothRel (=) (A := place_rfn rt) (PlaceGhost γ1) (PlaceGhost γ2) (γ1 = γ2).
Proof. split; naive_solver. Qed.

Global Instance simpl_replicate_eq' {A} (x x' : A) n n' :
  SimplAndUnsafe (replicate n x = replicate n' x') (λ b, n = n' ∧ x = x' ∧ b).
Proof.
  intros ? (-> & -> & ?). done.
Qed.

Global Instance simpl_eq_OffsetSt `{!LayoutAlg} st i i' x : SimplAndUnsafe (x offsetst{st}ₗ i = x offsetst{st}ₗ i') (λ T, i = i' ∧ T).
Proof.
  intros T [-> ?]. done.
Qed.



Global Instance simpl_and_unsafe_apply_evar_right {A B} (f g : A → B) (a y : A) `{!IsProtected y} : 
  SimplAndUnsafe (f a = g y) (λ T, a = y ∧ f = g ∧ T) | 1000.
Proof.
  rewrite /SimplAndUnsafe.
  intros T (<- & <- & HT). 
  done.
Qed.
Global Instance simpl_and_unsafe_apply_evar_left {A B} (f g : A → B) (a y : A) `{!IsProtected y} : 
  SimplAndUnsafe (f y = g a) (λ T, a = y ∧ f = g ∧ T) | 1000.
Proof.
  rewrite /SimplAndUnsafe.
  intros T (<- & <- & HT). 
  done.
Qed.

(** ** Additional normalization instances *)
#[export] Hint Rewrite Nat.add_sub : lithium_rewrite.
