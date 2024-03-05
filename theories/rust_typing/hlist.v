From iris.algebra Require Import ofe.
From iris.proofmode Require Import tactics.
From refinedrust Require Import axioms base.
Require Import Coq.Program.Equality.
Local Set Universe Polymorphism.

(** * Heterogeneous lists *)
(** This file is copied and extended from Yusuke Matsushita's RustHornBelt project
  https://gitlab.mpi-sws.org/iris/lambda-rust/-/tree/masters/rusthornbelt?ref_type=heads
*)

(** List.nth with better pattern matching *)
Fixpoint lnth {A} (d: A) (xl: list A) (i: nat) : A :=
  match xl with
  | [] => d
  | x :: xl' => match i with 0 => x | S j => lnth d xl' j end
  end.
Notation lnthe := (lnth ∅).

Lemma lnth_default {A} D (xl : list A) i :
  length xl <= i → D = lnth D xl i.
Proof.
  generalize dependent xl.
  induction i; destruct xl; simpl; intros; auto with lia.
Qed.

Lemma lookup_lnth {X} (l : list X) x i (d : X) :
  l !! i = Some x → lnth d l i = x.
Proof.
  induction l as [ | y l IH] in i |-*; simpl; first done.
  destruct i as [ | i]; simpl.
  - intros [= ->]. done.
  - intros Ha%IH; done.
Qed.


Class Inj3 {A B C D} (R1: relation A) (R2: relation B) (R3: relation C)
    (S: relation D) (f: A → B → C → D) : Prop :=
  inj3 x1 x2 x3 y1 y2 y3 :
    S (f x1 x2 x3) (f y1 y2 y3) → R1 x1 y1 ∧ R2 x2 y2 ∧ R3 x3 y3.

Global Arguments inj3 {_ _ _ _ _ _ _ _} _ {_} _ _ _ _ _ _ _ : assert.


(** * Heterogeneous List *)

(* TODO: we probably want to define a separate polymorphic list type here to avoid problems with [list]'s template polymorphism... *)
(* TODO try *)
Local Unset Universe Minimization ToSet.
#[universes(polymorphic)]
Inductive hlist {A} (F: A → Type) : list A → Type :=
| hnil: hlist F []
| hcons {X Xl} : F X → hlist F Xl → hlist F (X :: Xl).
Notation "+[ ]" := (hnil _) (at level 1, format "+[ ]").
Notation "+[ ]@{ F }" := (hnil F) (at level 1, only parsing).
Infix "+::" := (hcons _) (at level 60, right associativity).
Infix "+::@{ F }" := (hcons F) (at level 60, right associativity, only parsing).
Notation "+[ x ; .. ; z ]" := (x +:: .. (z +:: +[]) ..)
  (at level 1, format "+[ x ;  .. ;  z ]").
Notation "+[ x ; .. ; z ]@{ F }" := (x +:: .. (z +:: +[]@{F}) ..)
  (at level 1, only parsing).

Global Instance inhabited_hlist_nil {A} (F : A → Type) :
  Inhabited (hlist F []).
Proof. constructor. exact +[]. Qed.
Global Instance inhabited_hlist {A} (F : A → Type) (l : list A):
  TCTForall (λ T, Inhabited (F T)) l →
  Inhabited (hlist F l).
Proof.
  intros Ha. induction l as [ | x l IH]; simpl.
  - econstructor. econstructor.
  - inversion Ha as [ | ? ? [] HF]; subst. apply IH in HF as [].
    econstructor. constructor; done.
Qed.

Section hlist.
Set Universe Polymorphism.
Context {A: Type} {F: A → Type}.

Definition hlist_nil_inv (P: hlist F [] → Type) (H: P +[]) (xl : hlist F []) : P xl :=
  match xl with +[] => H end.

Definition hlist_cons_inv {X Xl'}
  (P: hlist F (X :: Xl') → Type) (H: ∀x xl', P (x +:: xl')) (xl : hlist F (X :: Xl')): P xl.
Proof.
  move: P H. refine match xl with x +:: xl' => λ _ H, H x xl' end.
Defined.

Fixpoint happ {Xl Yl} (xl: hlist F Xl) (yl: hlist F Yl) : hlist F (Xl ++ Yl) :=
  match xl with +[] => yl | x +:: xl' => x +:: happ xl' yl end.

Fixpoint hmap {G} (f: ∀ X, F X → G X) {Xl} (xl: hlist F Xl) : hlist G Xl :=
  match xl with +[] => +[] | x +:: xl' => f _ x +:: hmap f xl' end.

(* constant map *)
Fixpoint hcmap {Y} (f: ∀ X, F X → Y) {Xl} (xl: hlist F Xl) : list Y :=
  match xl with +[] => [] | x +:: xl' => f _ x :: hcmap f xl' end.

(* get the nth element *)
Fixpoint hnth {Xl D} (d: F D) (xl: hlist F Xl)
  : ∀i, F (lnth D Xl i) :=
  match xl with
  | +[] => λ _, d
  | x +:: xl' =>
    λ i, match i with 0 => x | S j => hnth d xl' j end
  end.

Fixpoint hrepeat {X} (x: F X) n : hlist F (repeat X n) :=
  match n with 0 => +[] | S m => x +:: hrepeat x m end.

Fixpoint max_hlist_with {Xl} (f: ∀ X, F X → nat) (xl: hlist F Xl) : nat :=
  match xl with +[] => 0 | x +:: xl' => f _ x `max` max_hlist_with f xl' end.

Fixpoint happly {Y Xl} (fl: hlist (λ X, Y → F X) Xl) (x: Y)
  : hlist F Xl :=
  match fl with +[] => +[] | f +:: fl' => f x +:: happly fl' x end.

Lemma hnth_default `{EqDecision A} {D Xl} (d : F D) (l : hlist F Xl) i :
  ∀ (H : D = lnth D Xl i),
    length Xl <= i →
    hnth d l i = eq_rect D _ d _ H.
Proof.
  generalize dependent i. induction l.
  - move => /= ? H. by rewrite (proof_irrel H eq_refl).
  - move => /= [|?] *; auto with lia.
Qed.
End hlist.

Ltac inv_hlist xl := let A := type of xl in
  match eval hnf in A with hlist _ ?Xl =>
    match eval hnf in Xl with
    | [] => revert dependent xl;
        match goal with |- ∀xl, @?P xl => apply (hlist_nil_inv P) end
    | _ :: _ => revert dependent xl;
        match goal with |- ∀xl, @?P xl => apply (hlist_cons_inv P) end;
        (* Try going on recursively. *)
        try (let x := fresh "x" in intros x xl; inv_hlist xl; revert x)
    end
  end.

Section lemmas.
  Context {A} {F : A → Type}.

  Lemma hnth_apply {Xl Y D} (g: Y → F D)
    (fl: hlist (λ X, Y → F X) Xl) (x: Y) i :
    hnth (g x) (happly fl x) i = hnth g fl i x.
  Proof. move: i. elim fl; [done|]=> > ?. by case. Qed.


  Lemma hcmap_length {Y} (f : ∀ X, F X → Y) {Xl} (xl : hlist F Xl) :
    length (hcmap f xl) = length Xl.
  Proof.
    induction Xl as [ | X Xl IH]; simpl.
    - inv_hlist xl. done.
    - inv_hlist xl. intros x xl' => /=. rewrite IH. done.
  Qed.

  Lemma fmap_hcmap {Y Z} (f : ∀ X, F X → Y) (g : Y → Z) {Xl} (xl : hlist F Xl) :
    fmap g (hcmap f xl) = hcmap (λ _ x, g (f _ x)) xl.
  Proof.
    induction Xl as [ | X Xl IH]; simpl.
    - inv_hlist xl. done.
    - inv_hlist xl. intros x xl'.
      simpl. f_equiv. apply IH.
  Qed.

  Lemma hcmap_ext {Y} (f g : ∀ X, F X → Y) {Xl} (xl : hlist F Xl) :
    (∀ X x, f X x = g X x) →
    hcmap f xl = hcmap g xl.
  Proof.
    intros Heq. induction Xl as [ | X Xl IH]; simpl.
    - inv_hlist xl. done.
    - inv_hlist xl. intros x xl'.
      simpl. rewrite Heq IH //.
  Qed.

  Lemma hcmap_hmap {G Y} (f : ∀ X, F X → G X) (g : ∀ X, G X → Y) {Xl} (xl : hlist F Xl) :
    hcmap g (hmap f xl) = hcmap (λ _ x, g _ (f _ x)) xl.
  Proof.
    induction xl as [ | X Xl x xl IH]; first done.
    simpl. f_equiv. apply IH.
  Qed.
End lemmas.

Infix "h++" := happ (at level 60, right associativity).
Infix "+<$>" := hmap (at level 61, left associativity).
Infix "+c<$>" := hcmap (at level 61, left associativity).
Infix "+$" := happly (at level 61, left associativity).
Notation "( fl +$.)" := (happly fl) (only parsing).

(** * Passive Heterogeneous List *)
(** Defined as nested pairs *)
Inductive nil_unit: Set := nil_tt: nil_unit.
Record cons_prod (A B: Type) : Type := cons_pair { phd' : A; ptl' : B }.
Arguments cons_pair {_ _} _ _.
Arguments phd' {_ _} _.
Arguments ptl' {_ _} _.

Section plist.
  Context {A} {F : A → Type}.
  #[universes(polymorphic)]
  Fixpoint plist (Xl: list A) : Type :=
    match Xl with [] => nil_unit | X :: Xl' => cons_prod (F X) (plist Xl') end.
End plist.

Definition pcons {A} {F : A → Type} {a X} (hd : F a) (tl : plist X) : plist (a :: X) :=
  cons_pair hd tl.
Definition pnil {A} {F : A → Type} : plist (F := F) [] := nil_tt.

Definition phd {A : Type} {F : A → Type} {X Xs} (pl : plist (X :: Xs)) : F X := phd' pl.
Definition ptl {A : Type} {F : A → Type} {X Xs} (pl : plist (X :: Xs)) : plist (F := F) Xs := ptl' pl.

Notation "-[ ]" := pnil (at level 1, format "-[ ]").
Infix "-::" := pcons (at level 60, right associativity).
Notation "(-::)" := pcons (only parsing).
Notation "-[ x ; .. ; z ]" := (x -:: .. (z -:: -[]) ..)
  (at level 1, format "-[ x ;  .. ;  z ]").

(* Different notation for matching on it *)
Notation "'*[' ']'" := nil_tt (at level 1, format "*[ ]").
Infix "*::" := cons_pair (at level 60, right associativity).
Notation "*[ x ; .. ; z ]" := (x *:: .. (z *:: *[]) ..)
  (at level 1, format "*[ x ;  .. ;  z ]").


Inductive TCTForall {A} (P : A → Type) : list A → Type :=
  | TCTForall_nil : TCTForall P []
  | TCTForall_cons x xs : P x → TCTForall P xs → TCTForall P (x :: xs).
Existing Class TCTForall.
Global Existing Instance TCTForall_nil.
Global Existing Instance TCTForall_cons.
Global Hint Mode TCTForall ! ! ! : typeclass_instances.

Global Instance inhabited_plist_nil {A} (F : A → Type) :
  Inhabited (plist (F:=F) []).
Proof. constructor. exact -[]. Qed.
Global Instance inhabited_plist {A} (F : A → Type) (l : list A):
  TCTForall (λ T, Inhabited (F T)) l →
  Inhabited (plist (F:=F) l).
Proof.
  intros Ha. induction l as [ | x l IH]; simpl.
  - econstructor. exact nil_tt.
  - inversion Ha as [ | ? ? [] HF]; subst. apply IH in HF as [].
    econstructor. constructor; done.
Qed.

Section plist.
Context {A: Type} {F: A → Type}.
Set Universe Polymorphism.

Notation plist := (plist (F:=F)).

Fixpoint papp {Xl Yl} (xl: plist Xl) (yl: plist Yl) : plist (Xl ++ Yl) :=
  match Xl, xl with [], _ => yl | _::_, cons_pair x xl' => x -:: papp xl' yl end.

Fixpoint psepl {Xl Yl} (xl: plist (Xl ++ Yl)) : plist Xl :=
  match Xl, xl with [], _ => -[] | _::_, cons_pair x xl' => x -:: psepl xl' end.
Fixpoint psepr {Xl Yl} (xl: plist (Xl ++ Yl)) : plist Yl :=
  match Xl, xl with [], _ => xl | _::_, cons_pair _ xl' => psepr xl' end.

Lemma papp_sepl {Xl Yl} (xl: plist Xl) (yl: plist Yl) : psepl (papp xl yl) = xl.
Proof. move: xl yl. elim Xl; [by case|]=>/= > IH [??]?. simpl. by rewrite IH. Qed.
Lemma papp_sepr {Xl Yl} (xl: plist Xl) (yl: plist Yl) : psepr (papp xl yl) = yl.
Proof. move: xl yl. elim Xl; [by case|]=>/= > IH [??]?. simpl. by rewrite IH. Qed.

Lemma psep_app {Xl Yl} (xl: plist (Xl ++ Yl)) : papp (psepl xl) (psepr xl) = xl.
Proof. move: xl. elim Xl; [done|]=>/= > IH [??]. simpl. by rewrite IH. Qed.
Lemma papp_ex {Xl Yl} (xl: plist (Xl ++ Yl)) :
  ∃(yl: plist Xl) (zl: plist Yl), xl = papp yl zl.
Proof. exists (psepl xl), (psepr xl). by rewrite psep_app. Qed.

Fixpoint pnth {Xl D} (d: F D) (xl: plist Xl) : ∀i, F (lnth D Xl i) :=
  match Xl, xl with
  | [], _ => λ _, d
  | _::_, cons_pair x xl' => λ i, match i with 0 => x | S j => pnth d xl' j end
  end.

Fixpoint hlist_to_plist {Xl} (xl: hlist F Xl) : plist Xl :=
  match xl with +[] => -[] | x +:: xl' => x -:: hlist_to_plist xl' end.
Fixpoint plist_to_hlist {Xl} (xl: plist Xl) : hlist F Xl :=
  match Xl, xl with [], _ => +[] | _::_, cons_pair x xl' => x +:: plist_to_hlist xl' end.

Fixpoint vec_to_plist {X n} (xl: vec (F X) n) : plist (replicate n X) :=
  match xl with [#] => -[] | x ::: xl' => x -:: vec_to_plist xl' end.
Fixpoint plist_to_vec {X n} (xl: plist (replicate n X)) : vec (F X) n :=
  match n, xl with 0, _ => [#] | S _, cons_pair x xl' => x ::: plist_to_vec xl' end.
End plist.

Arguments plist {_} _ _.

Infix "-++" := papp (at level 60, right associativity).
Notation psep := (λ xl, (psepl xl, psepr xl)).

Lemma plist_nil_inv {A} {F : A → Type} (P: plist F [] → Type) (H: P -[]) (xl : plist F []) : P xl.
Proof.
  destruct xl. apply H.
Defined.

Definition plist_cons_inv {A} {F : A → Type} {X Xl'}
  (P: plist F (X :: Xl') → Type) (H: ∀ x (xl' : plist F Xl'), P (x -:: xl')) (xl : plist F (X :: Xl')): P xl.
Proof.
  destruct xl as [x xl].
  apply H.
Defined.

Fixpoint pmap {A} {F G : A → Type} (f: ∀X, F X → G X) {Xl} : plist F Xl → plist G Xl :=
  match Xl with [] => id | _::_ => λ '(cons_pair x xl'), f _ x -:: pmap f xl' end.
Infix "-<$>" := pmap (at level 61, left associativity).

Fixpoint pcmap {A B} {F : A → Type} (f : ∀ X, F X → B) {Xl} : plist F Xl → list B :=
  match Xl with
  | [] => λ _, []
  | _ :: _ =>
      λ '(cons_pair x xl'), f _ x :: pcmap f xl'
  end.

Lemma pmap_app {A} {F G : A → Type} {Xl Yl} (f: ∀X, F X → G X)
      (xl: plist F Xl) (yl: plist F Yl) :
  f -<$> (xl -++ yl) = (f -<$> xl) -++ (f -<$> yl).
Proof. move: xl. elim Xl; [done|]=>/= ?? IH [??]. simpl. by rewrite IH. Qed.

Fixpoint papply {A} {F : A → Type} {B Xl}
         (fl: plist (λ X, B → F X) Xl) (x: B) : plist F Xl :=
  match Xl, fl with
  | [], _ => -[]
  | _::_, cons_pair f fl' => f x -:: papply fl' x
  end.
Infix "-$" := papply (at level 61, left associativity).
Notation "( fl -$.)" := (papply fl) (only parsing).

Lemma papply_app {A} {F: A → Type} {B Xl Yl}
  (fl: plist (λ X, B → F X) Xl) (gl: plist (λ X, B → F X) Yl) (x: B) :
  (fl -++ gl) -$ x = (fl -$ x) -++ (gl -$ x).
Proof. move: fl. elim Xl; [done|]=>/= ?? IH [??]. simpl. by rewrite IH. Qed.

Fixpoint hzip_with {A} {F G H: A → Type} {Xl} (f: ∀X, F X → G X → H X)
  (xl: hlist F Xl) (yl: plist G Xl) : hlist H Xl :=
  match xl, yl with
  | +[], _ => +[]
  | x +:: xl', cons_pair y yl' => f _ x y +:: hzip_with f xl' yl'
  end.
Notation hzip := (hzip_with (λ _, pair)).

Fixpoint pzip_with {A} {F G H: A → Type} {Xl} (f: ∀X, F X → G X → H X)
  (xl: plist F Xl) (yl: plist G Xl) : plist H Xl :=
  match Xl, xl, yl with
  | [], _, _ => -[]
  | _::_, cons_pair x xl', cons_pair y yl' => f _ x y -:: pzip_with f xl' yl'
  end.
Notation pzip := (pzip_with (λ _, pair)).

Lemma plist_fmap_shift {A B : Type} (F : B → Type) (f : A → B) (l : list A) :
  plist (F ∘ f) l = plist F (fmap f l).
Proof.
  induction l; simpl; first done. f_equiv. done.
Qed.

(* We don't use [∘] here because [∘] is universe-monomorphic
  and thus causes universe inconsistency *)
Fixpoint ptrans {A B} {F: A → B} {G Xl} (xl: plist (λ X, G (F X)) Xl)
    : plist G (map F Xl) :=
  match Xl, xl with [], _ => -[] | _::_, cons_pair x xl' => x -:: ptrans xl' end.

Fixpoint hlist_to_list {T A Xl} (xl: @hlist T (const A) Xl) : list A :=
  match xl with +[] => [] | x +:: xl' => x :: hlist_to_list xl' end.

Fixpoint list_to_hlist {T A Xl} (xl: list A) : option (hlist (λ _: T,  A) Xl) :=
  match xl, Xl with
  | [], [] => mret +[]
  | x :: xl',  X :: Xl' => list_to_hlist xl' ≫= λ tl, mret (x +:: tl)
  | _, _ => None
  end.

Lemma list_to_hlist_length {A T Xl} (l : list A) (l' : hlist (λ _: T, A) Xl) :
  list_to_hlist l = Some l' →
  length l = length Xl.
Proof.
  revert l'. generalize dependent Xl.
  induction l => - [|? ?] //= ?.
  destruct (list_to_hlist (Xl := _) _) eqn: X; rewrite ?(IHl _ h) //.
Qed.

Lemma list_to_hlist_hnth_nth {A T Xl} (t: T) (d : A) i
    (l : list A) (l' : hlist (λ _: T, A) Xl) :
  list_to_hlist l = Some l' →
  hnth (D := t) d l' i = nth i l d.
Proof.
  generalize dependent Xl. revert i.
  induction l => i [| ? Xl] ? //=.
  - case: i => [|?] [= <-] //=.
  - destruct (list_to_hlist (Xl := _) _) eqn:X, i => //= [= <-] //=. auto.
Qed.

(** Some eqcasting facts *)
Import EqNotations.
Lemma plist_cons_rew1 {X Y} {G : Y → Type} {F : X → Type} (x : X) (y : Y) (Xl : list X) (Yl : list Y) (l : plist F (Xl)) (fx : F x)
    (Heq : plist F (x :: Xl) = plist G (y :: Yl)) (Heq1 : F x = G y) (Heq2 : plist F Xl = plist G Yl) :
  rew [id] Heq in (cons_pair fx l) = cons_pair (rew [id] Heq1 in fx) (rew [id] Heq2 in l).
Proof.
  move : l fx Heq Heq1 Heq2. simpl.
  generalize ( F x) as T.
  generalize (plist F Xl) as T2.
  intros T2 T l fx Heq -> ->.
  simpl. rewrite (UIP_refl _ _ Heq). done.
Qed.
Lemma plist_cons_rew {X Y} {G : Y → Type} {F : X → Type} (x : X) (y : Y) (Xl : list X) (Yl : list Y) (l : plist F (Xl)) (fx : F x)
    (Heq : plist F (x :: Xl) = plist G (y :: Yl)) (Heq1 : F x = G y) (Heq2 : plist F Xl = plist G Yl) :
  rew [id] Heq in (fx -:: l) = pcons (F := G) (rew [id] Heq1 in fx) (rew [id] Heq2 in l).
Proof.
  rewrite /pcons. rewrite plist_cons_rew1. done.
Qed.

Lemma plist_cons_rew1' {X Y} {G : Y → Type} {F : X → Type} (x : X) (y : Y) (Xl : list X) (Yl : list Y) (l : plist F (Xl)) (fx : F x)
    (Heq : plist G (y :: Yl) = plist F (x :: Xl)) Heq1 (Heq2 : plist G Yl = plist F Xl) :
  rew <- [id] Heq in (cons_pair fx l) = cons_pair (rew <- [id] Heq1 in fx) (rew <-[id] Heq2 in l).
Proof.
  move : l fx Heq Heq1 Heq2. simpl.
  generalize ( F x) as T.
  generalize (plist F Xl) as T2.
  intros T2 T l fx Heq <- <-.
  simpl. rewrite (UIP_refl _ _ Heq). done.
Qed.
Lemma plist_cons_rew' {X Y} {G : Y → Type} {F : X → Type} (x : X) (y : Y) (Xl : list X) (Yl : list Y) (l : plist F (Xl)) (fx : F x)
    (Heq : plist G (y :: Yl) = plist F (x :: Xl)) Heq1 (Heq2 : plist G Yl = plist F Xl) :
  rew <- [id] Heq in (fx -:: l) = pcons (F := G) (rew <- [id] Heq1 in fx) (rew <-[id] Heq2 in l).
Proof.
  rewrite /pcons. rewrite plist_cons_rew1' //.
Qed.

Lemma phd_rew_commute {X Y} {G : Y → Type} {F : X → Type} (x : X) (y : Y) (Xl : list X) (Yl : list Y) (l : plist F (x :: Xl)) (Heq1 : plist F (x :: Xl) = plist G (y :: Yl)) (Heq2 : F x = G y) (Heq3 : plist F Xl = plist G Yl) :
  phd (rew [id] Heq1 in l) = rew [id] Heq2 in (phd l).
Proof.
  destruct l as [fx l].
  simpl. unshelve erewrite (plist_cons_rew1 _ _ _ _ _ _ Heq1); done.
Qed.

Lemma ptl_rew_commute {X Y} {G : Y → Type} {F : X → Type} (x : X) (y : Y) (Xl : list X) (Yl : list Y) (l : plist F (x :: Xl)) (Heq1 : plist F (x :: Xl) = plist G (y :: Yl)) (Heq2 : F x = G y) (Heq3 : plist F Xl = plist G Yl) :
  ptl (rew [id] Heq1 in l) = rew [id] Heq3 in (ptl l).
Proof.
  destruct l as [fx l].
  simpl. unshelve erewrite (plist_cons_rew1 _ _ _ _ _ _ Heq1); done.
Qed.

(** * Forall *)

Section fa.
Context {A} {F: A → Type}.

Inductive HForall (Φ: ∀X, F X → Prop) : ∀{Xl}, hlist F Xl → Prop :=
| HForall_nil: HForall Φ +[]
| HForall_cons {X Xl} (x: _ X) (xl: _ Xl) :
    Φ _ x → HForall Φ xl → HForall Φ (x +:: xl).

Inductive TCHForall (Φ : ∀ X, F X → Prop) : ∀ {Xl}, hlist F Xl → Prop :=
| TCHForall_nil: TCHForall Φ +[]
| TCHForall_cons {X Xl} (x : F X) (xl : hlist F Xl) :
    Φ _ x → TCHForall Φ xl → TCHForall Φ (x +:: xl).
Existing Class TCHForall.
Global Existing Instance TCHForall_nil.
Global Existing Instance TCHForall_cons.

Lemma TCHForall_impl {Xl} (Φ Ψ : ∀ X, F X → Prop) (xl : hlist F Xl) :
  (∀ X x, Φ X x → Ψ _ x) → TCHForall Φ xl → TCHForall Ψ xl.
Proof. move=> Imp. elim; constructor; by [apply Imp|]. Qed.

Lemma TCHForall_nth {Xl D} (Φ : ∀ X, F X → Prop) (d : F D) (xl : hlist F Xl) i :
  Φ _ d → TCHForall Φ xl → Φ _ (hnth d xl i).
Proof. move=> ? All. move: i. elim All; [done|]=> > ???. by case. Qed.

Context {G: A → Type}.

Inductive HForall_1 (Φ: ∀X, F X → G X → Prop)
  : ∀{Xl}, hlist F Xl → plist G Xl → Prop :=
| HForall_1_nil: HForall_1 Φ +[] -[]
| HForall_1_cons {X Xl} (x: _ X) y (xl: _ Xl) yl :
    Φ _ x y → HForall_1 Φ xl yl → HForall_1 Φ (x +:: xl) (y -:: yl).

Inductive HForallTwo (Φ: ∀X, F X → G X → Prop) : ∀{Xl}, hlist F Xl → hlist G Xl → Prop :=
| HForallTwo_nil: HForallTwo Φ +[] +[]
| HForallTwo_cons {X Xl} (x: _ X) y (xl: _ Xl) yl :
    Φ _ x y → HForallTwo Φ xl yl → HForallTwo Φ (x +:: xl) (y +:: yl).

Inductive HForallThree {H} (Φ: ∀X, F X → G X → H X → Prop) :
    ∀{Xl}, hlist F Xl → hlist G Xl → hlist H Xl → Prop :=
| HForallThree_nil: HForallThree Φ +[] +[] +[]
| HForallThree_cons {X Xl} (x: _ X) y z (xl: _ Xl) yl zl :
  Φ _ x y z → HForallThree Φ xl yl zl → HForallThree Φ (x +:: xl) (y +:: yl) (z +:: zl).

Lemma HForallTwo_impl {Xl} (Φ Ψ: ∀X, F X → G X → Prop) (xl: hlist F Xl) (yl: hlist G Xl) :
  (∀X x y, Φ X x y → Ψ X x y) → HForallTwo Φ xl yl → HForallTwo Ψ xl yl.
Proof. move=> Imp. elim; constructor; by [apply Imp|]. Qed.

Lemma HForall_1_nth {Xl D} (Φ: ∀X, F X → G X → Prop)
  (d: _ D) d' (xl: _ Xl) yl i :
  Φ _ d d' → HForall_1 Φ xl yl → Φ _ (hnth d xl i) (pnth d' yl i).
Proof. move=> ? All. move: i. elim All; [done|]=> > ???. by case. Qed.

Lemma HForallTwo_nth {Xl D}
  (Φ: ∀X, F X → G X → Prop) (d: _ D) d' (xl: _ Xl) yl i :
  Φ _ d d' → HForallTwo Φ xl yl → Φ _ (hnth d xl i) (hnth d' yl i).
Proof. move=> ? All. move: i. elim All; [done|]=> > ???. by case. Qed.

Lemma HForallTwo_forall `{!Inhabited Y} {Xl}
  (Φ: ∀X, Y → F X → G X → Prop) (xl yl: _ Xl) :
  (∀z, HForallTwo (λ X, Φ X z) xl yl) ↔ HForallTwo (λ X x y, ∀z, Φ _ z x y) xl yl.
Proof.
  split; [|elim; by constructor]. move=> All. set One := All inhabitant.
  induction One; [by constructor|]. constructor.
  { move=> z. move/(.$ z) in All. by dependent destruction All. }
  have All': ∀z, HForallTwo (λ X, Φ X z) xl yl.
  { move=> z. move/(.$ z) in All. by dependent destruction All. }
  auto.
Qed.

Lemma HForallTwo_cons_inv (Φ : ∀ x, F x → G x → Prop) (Xl : list A) (hl1 : hlist F Xl) (hl2 : hlist G Xl) (x : A) (h1 : F x) (h2 : G x) :
  HForallTwo Φ  (h1 +:: hl1) (h2 +:: hl2) →
  Φ _ h1 h2 ∧ HForallTwo Φ hl1 hl2.
Proof.
  inversion 1; subst.
  repeat match goal with
         | H : existT ?x _ = existT ?x _ |- _ => apply existT_inj in H
         end; subst.
  eauto.
Qed.

Lemma HForallThree_nth {H} {Xl D} (Φ: ∀X, F X → G X → H X → Prop)
    (d: _ D) d' d'' (xl: _ Xl) yl zl i :
  Φ _ d d' d'' → HForallThree Φ xl yl zl →
  Φ _ (hnth d xl i) (hnth d' yl i) (hnth d'' zl i).
Proof. move=> ? All. move: i. elim All; [done|]=> > ???. by case. Qed.

Lemma HForallThree_nth_len {H} {Xl D} (Φ: ∀X, F X → G X → H X → Prop)
    (d: _ D) d' d'' (xl: _ Xl) yl zl i :
  (i < length Xl)%nat → HForallThree Φ xl yl zl →
  Φ _ (hnth d xl i) (hnth d' yl i) (hnth d'' zl i).
Proof.
  move=> L All. move: i L. elim All; [simpl; lia|] => > ??? [|?] //=. auto with lia.
Qed.
End fa.

Global Hint Mode TCHForall ! ! ! ! ! : typeclass_instances.

Section HForallTwo.
Context {A} {F: A → Type} {Xl: list A} (R: ∀X, F X → F X → Prop).

Instance HForallTwo_reflexive :
  (∀X, Reflexive (R X)) → Reflexive (HForallTwo R (Xl:=Xl)).
Proof. move=> ?. elim; by constructor. Qed.
Instance HForallTwo_symmetric :
  (∀X, Symmetric (R X)) → Symmetric (HForallTwo R (Xl:=Xl)).
Proof. move=> >. elim; by constructor. Qed.
Instance HForallTwo_transitive :
  (∀X, Transitive (R X)) → Transitive (HForallTwo R (Xl:=Xl)).
Proof.
  move=> ??? zl All. move: zl. elim: All; [done|]=> > ?? IH ? All.
  dependent destruction All. constructor; by [etrans|apply IH].
Qed.

Global Instance HForallTwo_equivalence :
  (∀X, Equivalence (R X)) → Equivalence (HForallTwo R (Xl:=Xl)).
Proof. split; apply _. Qed.
End HForallTwo.

(** * Ofe *)
Section hlist_ofe.
Context {A} {F: A → ofe} {Xl : list A}.

Instance hlist_equiv : Equiv (hlist F Xl) := HForallTwo (λ _, (≡)).
Instance hlist_dist : Dist (hlist F Xl) := λ n, HForallTwo (λ _, dist n).

Definition hlist_ofe_mixin : OfeMixin (hlist F Xl).
Proof.
  split=> >.
  - rewrite /equiv /hlist_equiv HForallTwo_forall.
    split=> H; induction H; constructor=>//; by apply equiv_dist.
  - apply _.
  - rewrite /dist /hlist_dist. intros ??.
    eapply HForallTwo_impl; last done. intros ??? Hd.
    eapply dist_lt; first apply Hd. done.
Qed.

Canonical Structure hlistO := Ofe (hlist F Xl) hlist_ofe_mixin.
End hlist_ofe.

Arguments hlistO {_} _ _.

Section hlist_ofe_lemmas.
Context {A} {F: A → ofe} {Xl : list A}.

Global Instance hcons_ne {X} : NonExpansive2 (@hcons _ F X Xl).
Proof. by constructor. Qed.
Global Instance hcons_proper {X} : Proper ((≡) ==> (≡) ==> (≡)) (@hcons _ F X Xl).
Proof. by constructor. Qed.

Global Instance hnth_ne {D} n :
  Proper ((=) ==> (dist n) ==> forall_relation (λ i, dist n)) (@hnth _ F Xl D).
Proof. move=> ??->????. by apply (HForallTwo_nth (λ X, ofe_dist (F X) n)). Qed.
Global Instance hnth_proper {D} :
  Proper ((=) ==> (≡) ==> forall_relation (λ _, (≡))) (@hnth _ F Xl D).
Proof. move=> ??->?? /equiv_dist ??. apply equiv_dist=> ?. by apply hnth_ne. Qed.
End hlist_ofe_lemmas.

(** Forall2 for plist *)
Section pforall.
  Context {A} {F G : A → Type}.

  Fixpoint pforall {Xl} (Φ : ∀ X, F X → Prop) (xl : plist F Xl) : Prop :=
    match Xl, xl with
    | [], _ => True
    | _::_, cons_pair x xl' => Φ _ x ∧ pforall Φ xl'
    end.

  Fixpoint pforall2 {Xl} (Φ : ∀ X, F X → G X → Prop) (xl : plist F Xl) (yl : plist G Xl) : Prop :=
    match Xl, xl, yl with
    | [], _, _ => True
    | _ :: _, cons_pair x xl', cons_pair y yl' => Φ _ x y ∧ pforall2 Φ xl' yl'
    end.

  Lemma pforall2_forall {Xl W} (Φ : ∀ X, W → F X → G X → Prop) (xl : plist F Xl) (yl : plist G Xl) :
    (∀ w, pforall2 (λ X, Φ X w) xl yl) ↔ pforall2 (λ X x y, ∀ w, Φ _ w x y) xl yl.
  Proof.
    induction Xl as [ | X Xl IH] in xl, yl |-*.
    - destruct xl, yl. simpl. naive_solver.
    - destruct xl as [x xl], yl as [y yl].
      simpl. split.
      + intros Hw. split; first apply Hw.
        apply IH. apply Hw.
      + intros [Hh Hl]. split; [apply Hh | apply IH, Hl].
  Qed.

  Lemma pforall2_iff {Xl} (Φ Ψ : ∀ X, F X → G X → Prop) (xl : plist F Xl) (yl : plist G Xl) :
    (∀ X (x : F X) (y : G X), Φ X x y ↔ Ψ X x y) →
    pforall2 Φ xl yl ↔ pforall2 Ψ xl yl.
  Proof.
    intros Heq. induction Xl as [ | X Xl IH] in xl, yl |-*; simpl; first done.
    destruct xl as [x xl], yl as [y yl].
    rewrite Heq IH. done.
  Qed.

  Lemma pforall2_impl {Xl} (Φ Ψ : ∀ X, F X → G X → Prop) (xl : plist F Xl) (yl : plist G Xl) :
    (∀ X (x : F X) (y : G X), Φ X x y → Ψ X x y) →
    pforall2 Φ xl yl → pforall2 Ψ xl yl.
  Proof.
    intros Heq. induction Xl as [ | X Xl IH] in xl, yl |-*; simpl; first done.
    destruct xl as [x xl], yl as [y yl].
    intros [?%Heq ?%IH]; done.
  Qed.

  (*Lemma pforall2_length {Xl} (Φ : ∀ X, F X → Prop) (xl : plist F Xl) (yl : plist G Xl) :*)
    (*pforall2 Φ xl yl →*)
End pforall.

Section pforall2_rel.
  Context {A} {F : A → Type}.

  Instance pforall2_reflexive {Xl} (Φ : ∀ X, F X → F X → Prop) :
    (∀ X, Reflexive (Φ X)) → Reflexive (pforall2 (Xl:=Xl) Φ).
  Proof.
    intros Hrefl. induction Xl as [ | X Xl IH]; intros []; done.
  Qed.

  Instance pforall2_transitive {Xl} (Φ : ∀ X, F X → F X → Prop) :
    (∀ X, Transitive (Φ X)) → Transitive (pforall2 (Xl:=Xl) Φ).
  Proof.
    intros Htrans. induction Xl as [ | X Xl IH]; intros xl yl zl.
    - destruct xl, yl, zl; done.
    - destruct xl as [x xl], yl as [y yl], zl as [z zl].
      intros [? ?] [? ?]. split; last by eapply IH. by etrans.
  Qed.

  Instance pforall2_symmetric {Xl} (Φ : ∀ X, F X → F X → Prop) :
    (∀ X, Symmetric (Φ X)) → Symmetric (pforall2 (Xl:=Xl) Φ).
  Proof.
    intros Hsymm. induction Xl as [ | X Xl IH]; intros xl yl.
    - destruct xl, yl; done.
    - destruct xl as [x xl], yl as [y yl].
      intros [? ?]. split; last by eapply IH. by symmetry.
  Qed.

  Global Instance pforall_equivalence {Xl} (Φ : ∀ X, F X → F X → Prop) :
    (∀ X, Equivalence (Φ X)) → Equivalence (pforall2 (Xl:=Xl) Φ).
  Proof. intros; split; apply _. Qed.
End pforall2_rel.

(** * Ofe for plist *)
Section plist_ofe.
  Context {A} {F : A → ofe} {Xl : list A}.

  (* equiv and dist are lifted pointwise *)

  Instance plist_equiv : Equiv (plist F Xl) := pforall2 (λ _, (≡)).
  Instance plist_dist : Dist (plist F Xl) := λ n, pforall2 (λ _, dist n).

  Definition plist_ofe_mixin : OfeMixin (plist F Xl).
  Proof.
    split.
    - intros x y. rewrite pforall2_forall.
      apply pforall2_iff. intros. apply equiv_dist.
    - intros. apply _.
    - intros n m x y Ha ?.
      eapply pforall2_impl; last done. intros ??? Hd.
      eapply dist_lt; first apply Hd. done.
  Qed.

  Canonical Structure plistO := Ofe (plist F Xl) plist_ofe_mixin.
End plist_ofe.

(** * big_sep *)

Section big_sep.
Context {PROP: bi} {A : Type}.

Fixpoint big_sepHL' {F: A → Type} {Xl} (Φ: ∀X, nat → F X → PROP) (i : nat) (xl: hlist F Xl) : PROP :=
  match xl with
  | +[] => True
  | x +:: xl' => Φ _ i x ∗ big_sepHL' Φ (S i) xl'
  end.
Definition big_sepHL {F: A → Type} {Xl} (Φ: ∀X, nat → F X → PROP) (xl: hlist F Xl) : PROP := big_sepHL' Φ 0%nat xl.

Fixpoint big_sepHL_1' {F G: A → Type} {Xl} (Φ: ∀X, nat → F X → G X → PROP) (i : nat) (xl: hlist F Xl) (yl: plist G Xl) : PROP :=
  match xl, yl with
  | +[], _ => True
  | x +:: xl', cons_pair y yl' => Φ _ i x y ∗ big_sepHL_1' Φ (S i) xl' yl'
  end.
Definition big_sepHL_1 {F G: A → Type} {Xl} (Φ: ∀X, nat → F X → G X → PROP) (xl: hlist F Xl) (yl: plist G Xl) : PROP :=
  big_sepHL_1' Φ 0%nat xl yl.

(* additionally takes in a normal list *)
Fixpoint big_sepHL_2' {B} {F G: A → Type} {Xl} (Φ: ∀X, nat → B → F X → G X → PROP) (i : nat) (wl : list B) (xl: hlist F Xl) (yl: plist G Xl) : PROP :=
  match wl, xl, yl with
  | [], +[], _ => True
  | w :: wl', x +:: xl', cons_pair y yl' => Φ _ i w x y ∗ big_sepHL_2' Φ (S i) wl' xl' yl'
  | _, _, _ => False
  end.
Definition big_sepHL_2 {B} {F G: A → Type} {Xl} (Φ: ∀X, nat → B → F X → G X → PROP) (wl : list B) (xl: hlist F Xl) (yl: plist G Xl) : PROP :=
  big_sepHL_2' Φ 0%nat wl xl yl.

End big_sep.

Notation "[∗ hlist] x ∈ xl , P" := (big_sepHL (λ _ _ x, P%I) xl)
  (at level 200, xl at level 10, x at level 1, right associativity,
    format "[∗  hlist]  x  ∈  xl ,  P") : bi_scope.
Notation "[∗ hlist] i ↦ x ∈ xl , P" := (big_sepHL (λ _ i x, P%I) xl)
  (at level 200, xl at level 10, x at level 1, right associativity,
    format "[∗  hlist] i ↦  x  ∈  xl ,  P") : bi_scope.

Notation "[∗ hlist] x ;- y ∈ xl ;- yl , P" := (big_sepHL_1 (λ _ _ x y, P%I) xl yl)
  (at level 200, xl, yl at level 10, x, y at level 1, right associativity,
    format "[∗  hlist]  x ;-  y  ∈  xl ;-  yl ,  P") : bi_scope.
Notation "[∗ hlist] i ↦ x ;- y ∈ xl ;- yl , P" := (big_sepHL_1 (λ _ i x y, P%I) xl yl)
  (at level 200, xl, yl at level 10, x, y at level 1, right associativity,
    format "[∗  hlist]  i ↦ x ;-  y  ∈  xl ;-  yl ,  P") : bi_scope.

Notation "[∗ hlist] w ; x ;- y ∈ wl ; xl ;- yl , P" := (big_sepHL_2 (λ _ _ w x y, P%I) wl xl yl)
  (at level 200, wl, xl, yl at level 10, w, x, y at level 1, right associativity,
    format "[∗  hlist]  w ; x ;-  y  ∈  wl ; xl ;-  yl ,  P") : bi_scope.
Notation "[∗ hlist] i ↦ w ; x ;- y ∈ wl ; xl ;- yl , P" := (big_sepHL_2 (λ _ i w x y, P%I) wl xl yl)
  (at level 200, wl, xl, yl at level 10, w, x, y at level 1, right associativity,
    format "[∗  hlist]  i ↦ w ; x ;-  y  ∈  wl ; xl ;-  yl ,  P") : bi_scope.

(*Notation "[∗ hlist] x ; y ;- z ∈ xl ; yl ;- zl , P" :=*)
  (*(big_sepHL2_1 (λ _ _ x y z, P%I) xl yl zl)*)
  (*(at level 200, xl, yl, zl at level 10, x, y, z at level 1, right associativity,*)
    (*format "[∗  hlist]  x ;  y ;-  z  ∈  xl ;  yl ;-  zl ,  P") : bi_scope.*)

Section lemmas.
Context `{!BiAffine PROP}.

(** big_sepHL *)

Local Lemma big_sepHL'_mono `{F : A → Type} {Xl} (xl : hlist F Xl) (Φ Ψ : ∀ C, nat → F C → PROP) i :
  (∀ C k (x : F C), Φ C k x -∗ Ψ C k x) →
  big_sepHL' Φ i xl -∗ big_sepHL' Ψ i xl.
Proof.
  iIntros (Hw). induction xl as [ | X Xl x xl IH] in i |-*; simpl; first by auto.
  iIntros "(Hh & Hr)". iSplitL "Hh"; last by iApply IH.
  by iApply Hw.
Qed.
Lemma big_sepHL_mono `{F : A → Type} {Xl} (xl : hlist F Xl) (Φ Ψ : ∀ C, nat → F C → PROP) :
  (∀ C k (x : F C), Φ C k x -∗ Ψ C k x) →
  big_sepHL Φ xl -∗ big_sepHL Ψ xl.
Proof. apply big_sepHL'_mono. Qed.

Local Lemma big_sepHL'_shift `{F : A → Type} {Xl} (xl : hlist F Xl) (Φ : ∀ C, nat → F C → PROP) i :
  big_sepHL' Φ (S i) xl ⊣⊢ big_sepHL' (λ C k (x : F C), Φ C (S k) x) i xl.
Proof.
  induction xl as [ | X Xl x xl IH] in i |-*; simpl; first done. iSplit.
  - iIntros "($ & Ha)".
    iPoseProof (IH (S i) with "Ha") as "Ha".
    iApply (big_sepHL'_mono with "Ha"). eauto.
  - iIntros "($ & Ha)". by iApply (IH (S i) with "Ha").
Qed.

Lemma big_sepHL_app `{F: A → Type} {Xl Yl}
      (xl: hlist F Xl) (xl': hlist F Yl) (Φ: ∀C, nat → F C → PROP) :
  big_sepHL Φ (xl h++ xl') ⊣⊢ big_sepHL Φ xl ∗ big_sepHL (λ C i x, Φ C (length Xl + i) x) xl'.
Proof.
  unfold big_sepHL. generalize 0 as i => i.
  induction xl as [ | X Xl x xl IH] in i |-*; simpl.
  - rewrite left_id. iSplit; iApply big_sepHL'_mono; eauto.
  - rewrite IH. rewrite [big_sepHL' _ (S i) xl']big_sepHL'_shift assoc.
    iSplit; iIntros "($ & Ha)".
    all: iApply (big_sepHL'_mono with "Ha"); iIntros (???) "Ha".
    all: replace (length Xl + S k) with (S (length Xl + k)) by lia; done.
Qed.

Global Instance into_sep_big_sepHL_app `{F: A → Type} {Xl Yl}
  (xl: hlist F Xl) (xl': hlist F Yl) (Φ: ∀C, nat → F C → PROP) :
  IntoSep (big_sepHL Φ (xl h++ xl')) (big_sepHL Φ xl) (big_sepHL (λ C i x, Φ C (length Xl + i) x) xl').
Proof. by rewrite /IntoSep big_sepHL_app. Qed.
Global Instance from_sep_big_sepHL_app `{F: A → Type} {Xl Yl}
  (xl: hlist F Xl) (xl': hlist F Yl) (Φ: ∀C, F C → PROP) :
  FromSep (big_sepHL (λ C _, Φ C) (xl h++ xl')) (big_sepHL (λ C _, Φ C) xl) (big_sepHL (λ C _, Φ C) xl').
Proof. by rewrite /FromSep big_sepHL_app. Qed.

Global Instance frame_big_sepHL_app `{F: A → Type} {Xl Yl}
  p R Q (xl: hlist F Xl) (xl': hlist F Yl) (Φ: ∀C, F C → PROP) :
  Frame p R (big_sepHL (λ C _, Φ C) xl ∗ big_sepHL (λ C _, Φ C) xl') Q →
  Frame p R (big_sepHL (λ C _, Φ C) (xl h++ xl')) Q.
Proof. by rewrite /Frame big_sepHL_app. Qed.

(** big_sepHL_1 *)
Local Lemma big_sepHL_1'_mono `{F : A → Type} {G Xl} (xl : hlist F Xl) (yl : plist G Xl) (Φ Ψ : ∀ C, nat → F C → G C → PROP) i :
  (∀ C k (x : F C) (y : G C), Φ C k x y -∗ Ψ C k x y) →
  big_sepHL_1' Φ i xl yl -∗ big_sepHL_1' Ψ i xl yl.
Proof.
  iIntros (Hw). induction xl as [ | X Xl x xl IH] in i, yl |-*; simpl; first by auto.
  destruct yl as [y yl]. iIntros "(Hh & Hr)". iSplitL "Hh"; last by iApply IH.
  by iApply Hw.
Qed.
Lemma big_sepHL_1_mono `{F : A → Type} {G Xl} (xl : hlist F Xl) (yl : plist G Xl) (Φ Ψ : ∀ C, nat → F C → G C → PROP) :
  (∀ C k (x : F C) (y : G C), Φ C k x y -∗ Ψ C k x y) →
  big_sepHL_1 Φ xl yl -∗ big_sepHL_1 Ψ xl yl.
Proof. apply big_sepHL_1'_mono. Qed.

Local Lemma big_sepHL_1'_shift `{F : A → Type} {G Xl} (xl : hlist F Xl) (yl : plist G Xl) (Φ : ∀ C, nat → F C → G C → PROP) i :
  big_sepHL_1' Φ (S i) xl yl ⊣⊢ big_sepHL_1' (λ C k (x : F C) (y : G C), Φ C (S k) x y) i xl yl.
Proof.
  induction xl as [ | X Xl x xl IH] in i, yl |-*; simpl; first done.
  destruct yl as [y yl]. iSplit.
  - iIntros "($ & Ha)".
    iPoseProof (IH yl (S i) with "Ha") as "Ha".
    iApply (big_sepHL_1'_mono with "Ha"). eauto.
  - iIntros "($ & Ha)". by iApply (IH yl (S i) with "Ha").
Qed.

Lemma big_sepHL_1_app `{F: A → Type} {G Xl Yl}
      (xl: hlist F Xl) (xl': hlist F Yl)
      (yl: plist G Xl) (yl': plist G Yl) (Φ: ∀C, nat → F C → G C → PROP) :
  big_sepHL_1 Φ (xl h++ xl') (yl -++ yl') ⊣⊢ big_sepHL_1 Φ xl yl ∗ big_sepHL_1 (λ C i x y, Φ C (length Xl + i) x y) xl' yl'.
Proof.
  unfold big_sepHL_1. generalize 0 as i => i.
  induction xl as [ | X Xl x xl IH] in i, yl |-*; simpl; [destruct yl | destruct yl as [y yl]].
  - rewrite left_id. iSplit; iApply big_sepHL_1'_mono; eauto.
  - simpl. rewrite IH. rewrite [big_sepHL_1' _ (S i) xl' yl']big_sepHL_1'_shift assoc.
    iSplit; iIntros "($ & Ha)".
    all: iApply (big_sepHL_1'_mono with "Ha"); iIntros (????) "Ha".
    all: replace (length Xl + S k) with (S (length Xl + k)) by lia; done.
Qed.

Global Instance into_sep_big_sepHL_1_app `{F: A → Type} {G Xl Yl}
  (xl : hlist F Xl) (xl' : hlist F Yl) (yl : plist G Xl) (yl' : plist G Yl)
  (Φ: ∀C, nat → F C → G C → PROP) :
  IntoSep (big_sepHL_1 Φ (xl h++ xl') (yl -++ yl'))
    (big_sepHL_1 Φ xl yl) (big_sepHL_1 (λ C i x y, Φ C (length Xl + i) x y) xl' yl').
Proof. by rewrite /IntoSep big_sepHL_1_app. Qed.
Global Instance from_sep_big_sepHL_1_app `{F: A → Type} {G Xl Yl}
  (xl: hlist F Xl) (xl': hlist F Yl) (yl: plist G Xl) (yl': plist G Yl)
  (Φ: ∀C, F C → G C → PROP) :
  FromSep (big_sepHL_1 (λ C _, Φ C) (xl h++ xl') (yl -++ yl'))
    (big_sepHL_1 (λ C _, Φ C) xl yl) (big_sepHL_1 (λ C _, Φ C) xl' yl').
Proof. by rewrite /FromSep big_sepHL_1_app. Qed.

Global Instance frame_big_sepHL_1_app `{F: A → Type} {G Xl Yl}
  p R Q (xl: hlist F Xl) (xl': hlist F Yl) (yl: plist G Xl) (yl': plist G Yl)
  (Φ: ∀C, F C → G C → PROP) :
  Frame p R (big_sepHL_1 (λ C _, Φ C) xl yl ∗ big_sepHL_1 (λ C _, Φ C) xl' yl') Q →
  Frame p R (big_sepHL_1 (λ C _, Φ C) (xl h++ xl') (yl -++ yl')) Q.
Proof. by rewrite /Frame big_sepHL_1_app. Qed.

End lemmas.


Section hzipl.
  Set Universe Polymorphism.
  Fixpoint hzipl {X} {F} (l : list X) (hl : hlist F l) : list (sigT F) :=
    match hl with
    | hnil _ => []
    | @hcons _ _ X Xl x xl => (existT X x) :: hzipl Xl xl
    end.
  Lemma hzipl_length {X F} (l : list X) (hl : hlist F l) :
    length (hzipl l hl) = length l.
  Proof. induction hl; naive_solver. Qed.
  Lemma hzipl_lookup {X F} (l : list X) (hl : hlist F l) i x :
    l !! i = Some x →
    ∃ y, hzipl l hl !! i = Some (existT x y).
  Proof.
    intros Hlook. induction hl as [ | x' l y hl IH ] in i, Hlook |-*.
    - done.
    - destruct i as [ | i]; simpl in Hlook.
      + injection Hlook as [= ->]. eauto.
      + eapply IH in Hlook as (y' & Hlook). eauto.
  Qed.
  Lemma hzipl_lookup_inv {X F} (l : list X) (hl : hlist F l) i x y :
    hzipl l hl !! i = Some (existT x y) →
    l !! i = Some x.
  Proof.
    induction hl as [ | x' l y' hl IH] in i |-*; simpl.
    - done.
    - destruct i as [ | i]; simpl.
      + by intros [= -> Heq].
      + apply IH.
  Qed.

  Lemma hzipl_lookup_hnth {X} {F} (Xl : list X) (hl : hlist F Xl) i (d : X) (hd : F d) :
    (i < length Xl)%nat →
    hzipl Xl hl !! i = Some (existT _ (hnth hd hl i)).
  Proof.
    induction Xl as [ | x Xl IH] in hl, i |-*; simpl; intros Hi; inv_hlist hl; first lia.
    intros x1 hl. destruct i as [ | i]; simpl; first done.
    eapply IH. lia.
  Qed.
  Lemma hcmap_lookup_hzipl {X Y} {F} (f : ∀ x, F x → Y) (Xl : list X) (hl : hlist F Xl) k (x : X) (a : F x) :
    hzipl _ hl !! k = Some (existT x a) →
    hcmap f hl !! k = Some (f _ a).
  Proof.
    induction Xl as [ | x0 Xl IH] in hl, k |-*; simpl; inv_hlist hl; first done.
    intros x1 hl. destruct k as [ | k]; simpl.
    - intros [= -> Heq2]. apply existT_inj in Heq2 as ->. done.
    - eapply IH.
  Qed.

  Lemma TCHForall_nth_hzipl {X F} (Ψ : ∀ x : X, F x → Prop) (Xl : list X) (hl : hlist F Xl) i x y :
    TCHForall Ψ hl →
    hzipl _ hl !! i = Some (existT x y)  →
    Ψ x y.
  Proof.
    induction Xl as [ | ? Xl IH] in hl, i |-*; inv_hlist hl; first done.
    intros fx hl.
    inversion 1 as [ | ????? ? Ha Hb]. subst.
    repeat match goal with | H : existT ?A _ = existT ?A _ |- _ => apply existT_inj in H end; subst.
    destruct i as [ | i]; simpl.
    - intros [= <- ->%existT_inj]; done.
    - intros Hlook. eapply IH; last apply Hlook. done.
  Qed.

  Lemma hzipl_hmap_lookup_inv {X} {F} (Xl : list X) (xl : hlist F Xl) (f : ∀ x : X, F x → F x) i (x : X) (fx : F x) :
    hzipl Xl (f +<$> xl) !! i = Some (existT x fx) →
    ∃ y, hzipl Xl xl !! i = Some (existT x y) ∧ fx = f _ y.
  Proof.
    induction Xl as [ | a Xl IH] in i, xl |-*; inv_hlist xl; simpl; first done.
    intros fa xl. destruct i as [ | i]; simpl.
    - intros [= -> Heq]. apply existT_inj in Heq. subst. eauto.
    - intros Hlook%IH. done.
  Qed.
End hzipl.

Section hzipl2.
  Set Universe Polymorphism.

  Definition hzipl2 {X} {F G} : ∀ (l : list X), hlist F l → hlist G l → list (sigT (λ x, (F x * G x)%type)).
  Proof.
    refine (
    fix rec (l : list X) :=
      match l as l return hlist F l → hlist G l → list (sigT (λ x, (F x * G x)%type)) with
      | [] => λ _ _, []
      | X :: Xl =>
        λ (hl1 : hlist F (X :: Xl)) (hl2 : hlist G (X :: Xl)), _
    end).
    inversion hl1. inversion hl2. subst.
    eapply cons.
    - exists X. split; done.
    - eapply rec; done.
  Defined.

  Lemma hzipl2_cons {X} {F G} (x : X) (l : list X) (hl1 : hlist F l) (hl2 : hlist G l) (x1 : F x) (x2 : G x) :
    hzipl2 (x :: l) (x1 +:: hl1) (x2 +:: hl2) = (existT x (x1, x2)) :: hzipl2 l hl1 hl2.
  Proof. done. Qed.
  Lemma hzipl2_nil {X} {F G} :
    hzipl2 ([] : list X) (+[] : hlist F []) (+[] : hlist G []) = [].
  Proof. done. Qed.

  Lemma hzipl2_cons_inv {X} {F G} (x : X) (l : list X) (hl1 : hlist F (x :: l)) (hl2 : hlist G (x :: l)) (x1 : F x) (x2 : G x) l' :
    hzipl2 (x :: l) hl1 hl2 = (existT x (x1, x2)) :: l' →
    ∃ (hl1' : hlist F l) (hl2' : hlist G l),
      hl1 = x1 +:: hl1' ∧ hl2 = x2 +:: hl2' ∧ l' = hzipl2 l hl1' hl2'.
  Proof.
    inversion hl1 as [ | ?? x1' hl1']; inversion hl2 as [ | ?? x2' hl2']; subst.
    (*eexists _, _; split_and!.*)
  Abort.


  Lemma hzipl2_fmap_l {X} {F F2 G} (Xs : list X) (l1 : hlist F Xs) (l2 : hlist G Xs) (f : ∀ x : X, F x → F2 x) :
    hzipl2 Xs (f +<$> l1) l2 = (λ '(existT x (a, b)), existT x (f _ a, b)) <$> hzipl2 Xs l1 l2.
  Proof.
    induction Xs as [ | x Xs IH] in l1, l2 |-*; inv_hlist l1; inv_hlist l2; first done.
    intros x1 xl1 x2 xl2. cbn. f_equiv. done.
  Qed.
  Lemma hzipl2_fmap_r {X} {F G G2} (Xs : list X) (l1 : hlist F Xs) (l2 : hlist G Xs) (g : ∀ x : X, G x → G2 x) :
    hzipl2 Xs l1 (g +<$> l2) = (λ '(existT x (a, b)), existT x (a, g _ b)) <$> hzipl2 Xs l1 l2.
  Proof.
    induction Xs as [ | x Xs IH] in l1, l2 |-*; inv_hlist l1; inv_hlist l2; first done.
    intros x1 xl1 x2 xl2. cbn. f_equiv. done.
  Qed.
  Lemma hzipl2_fmap {X} {F F2 G G2} (Xs : list X) (l1 : hlist F Xs) (l2 : hlist G Xs) (f : ∀ x : X, F x → F2 x) (g : ∀ x : X, G x → G2 x) :
    hzipl2 Xs (f +<$> l1) (g +<$> l2) = (λ '(existT x (a, b)), existT x (f _ a, g _ b)) <$> hzipl2 Xs l1 l2.
  Proof.
    induction Xs as [ | x Xs IH] in l1, l2 |-*; inv_hlist l1; inv_hlist l2; first done.
    intros x1 xl1 x2 xl2. cbn. f_equiv. done.
  Qed.
  Lemma hzipl2_swap {X} {F G} (Xs : list X) (l1 : hlist F Xs) (l2 : hlist G Xs) :
    hzipl2 Xs l1 l2 = (λ '(existT x (a, b)), existT x (b, a)) <$> hzipl2 Xs l2 l1.
  Proof.
    induction Xs as [ | x Xs IH] in l1, l2 |-*; inv_hlist l1; inv_hlist l2; first done.
    intros x1 xl1 x2 xl2. cbn. f_equiv. done.
  Qed.

  Lemma hzipl_hzipl2_lookup {X} {F G} (Xl : list X) (hl1 : hlist F Xl) (hl2 : hlist G Xl) k x a b :
    hzipl Xl hl1 !! k = Some (existT x a) →
    hzipl Xl hl2 !! k = Some (existT x b) →
    hzipl2 Xl hl1 hl2 !! k = Some (existT x (a, b)).
  Proof.
    induction Xl as [ | ? Xl IH] in hl1, hl2, k |-*; inv_hlist hl1; inv_hlist hl2; first done.
    intros y' hl2 x' hl1. destruct k as [ | k].
    - simpl. intros [= -> ->%existT_inj] [= ->%existT_inj]. done.
    - rewrite hzipl2_cons. simpl. apply IH.
  Qed.

  Lemma zip_hzipl_hzipl2 {X} {F : X → Type} (Xs : list X) (xs : hlist F Xs) (ys : hlist F Xs) :
    zip (hzipl Xs xs) (hzipl Xs ys) = (λ '(existT x (a, b)), (existT x a, existT x b)) <$> hzipl2 Xs xs ys.
  Proof.
    induction Xs as [ | X1 Xs IH] in xs, ys |-*; simpl.
    { inv_hlist xs. inv_hlist ys. done. }
    inv_hlist xs => x1 xs. inv_hlist ys => y1 ys. simpl.
    f_equiv. apply IH.
  Qed.
End hzipl2.

Section pzipl.
  Set Universe Polymorphism.
  Fixpoint pzipl {X} {F : X → Type} (l : list X) : plist F l → list (sigT F) :=
    match l with
    | [] => λ hl, []
    | X :: Xl =>
        λ hl, (existT X (phd hl)) :: pzipl Xl (ptl hl)
    end.
  Lemma pzipl_length {X} {F : X → Type} (l : list X) (hl : plist F l) :
    length (pzipl l hl) = length l.
  Proof. induction l; naive_solver. Qed.
  Lemma pzipl_lookup {X} {F : X → Type} (l : list X) (hl : plist F l) i x :
    l !! i = Some x →
    ∃ y, pzipl l hl !! i = Some (existT x y).
  Proof.
    intros Hlook. induction l as [ | x' l IH ] in i, hl, Hlook |-*.
    - done.
    - destruct hl as [y hl].
      destruct i as [ | i]; simpl in Hlook.
      + injection Hlook as [= ->]. eauto.
      + eapply IH in Hlook as (y' & Hlook). simpl; eauto.
  Qed.
  Lemma pzipl_lookup_inv {X} {F : X → Type} (l : list X) (hl : plist F l) i x y :
    pzipl l hl !! i = Some (existT x y) →
    l !! i = Some x.
  Proof.
    induction l as [ | x' l IH] in i, hl |-*; simpl.
    - done.
    - destruct hl as [y' hl]. destruct i as [ | i]; simpl.
      + by intros [= -> Heq].
      + apply IH.
  Qed.
  Lemma pzipl_pzip_lookup_inv {X} {F G : X → Type} (l : list X) (hl : plist F l) (gl : plist G l) i x y z :
    pzipl l (pzip hl gl) !! i = Some (existT x (y, z)) →
    pzipl l hl !! i = Some (existT x y) ∧ pzipl l gl !! i = Some (existT x z).
  Proof.
    induction l as [ | h l IH] in i, hl, gl |-*; simpl.
    - done.
    - destruct hl as [y' hl]. destruct gl as [z' gl].
      destruct i as [ | i]; simpl.
      + intros [= -> [= Heq1] [= Heq2]]. rewrite Heq1 Heq2. done.
      + apply IH.
  Qed.

  Lemma pzipl_fmap_eqcast {X} {F : X → Type} (f : X → X) (g : sigT (λ x : X, F x) → sigT (λ x : X, F x))  (l : list X) (p : plist F (map f l))
    (Heq : ∀ l : list X, plist F (map f l) = plist F l) :
    (∀ x, F (f x) = F x) →
    (∀ x h Heq, existT (f x) h = g (existT x (rew [id] Heq in h))) →
    pzipl (map f l) p = fmap g (pzipl l (rew [id] (Heq l) in p)).
  Proof.
    intros HFf Heq0.
    induction l as [ | x l IH]; simpl; first done.
    destruct p as [ph p].
    f_equiv; first last.
    - simpl. rewrite IH.
      f_equiv. rewrite ptl_rew_commute; done.
    - simpl.
      rewrite phd_rew_commute; last done.
      simpl. apply Heq0.
  Qed.

  Lemma pzipl_lookup_pnth {X} {F} (Xl : list X) (pl : plist F Xl) i (d : X) (hd : F d) :
    (i < length Xl)%nat →
    pzipl Xl pl !! i = Some (existT _ (pnth hd pl i)).
  Proof.
    induction Xl as [ | x Xl IH] in pl, i |-*; simpl; intros Hi; first lia.
    destruct pl as [x1 pl]. destruct i as [ | i]; simpl; first done.
    eapply IH. lia.
  Qed.

  Lemma pcmap_lookup_pzipl {X Y} {F} (f : ∀ x, F x → Y) (Xl : list X) (pl : plist F Xl) k (x : X) (a : F x) :
    pzipl _ pl !! k = Some (existT x a) →
    pcmap f pl !! k = Some (f _ a).
  Proof.
    induction Xl as [ | x0 Xl IH] in pl, k |-*; simpl; first done.
    destruct pl as [x1 pl]. destruct k as [ | k]; simpl.
    - intros [= -> Heq2]. apply existT_inj in Heq2 as ->. done.
    - eapply IH.
  Qed.
End pzipl.

Section hlist_replace.
  Set Universe Polymorphism.
  Definition hlist_insert {X} {F} : ∀ (Xl : list X) (l : hlist F Xl) (i : nat) (x0 : X) (h : F x0), hlist F (<[i := x0]> Xl).
  Proof.
    refine (fix rec Xl l i x0 h :=
      match l with
      | +[] => +[]
      | @hcons _ _ x1 Xl h1 l =>
          match i with
          | 0%nat => hcons F h l
          | S i => hcons F h1 (rec Xl l i x0 h)
          end
      end).
  Defined.

  Lemma list_insert_lnth {X} (xs : list X) (d : X) i :
    <[i := lnth d xs i]> xs = xs.
  Proof.
    induction xs as [ | x xs IH] in i |-*; first done.
    destruct i as [ | i]; simpl; first done.
    by rewrite IH.
  (* defined transparently so that [hlist_insert_id] and [plist_insert_id] compute *)
  Defined.

  Definition hlist_insert_id {X} {F} (d : X) (Xl : list X) (l : hlist F Xl) (i : nat) (h : F (lnth d Xl i)) : hlist F Xl.
  Proof.
    exact (let r := hlist_insert Xl l i _ h in
      rew (list_insert_lnth Xl d i) in r).
  Defined.

  (* TODO remove? *)
  Definition hlist_insert_id' {X} {F} (Xl : list X) (l : hlist F Xl) (i : nat) (x0 : X) (h : F x0) (Heq: Xl !! i = Some x0) : hlist F Xl.
  Proof.
    exact (let r := hlist_insert Xl l i x0 h in
    rew (list_insert_id Xl i x0 Heq) in r).
  Defined.

  Lemma hzipl_hlist_insert {X} {F} (Xl : list X) (l : hlist F Xl) (i : nat) (x0 : X) (h : F x0) :
    hzipl _ (hlist_insert Xl l i x0 h) = <[i := existT x0 h]> (hzipl _ l).
  Proof.
    induction Xl as [ | x1 Xl IH] in i, l |-*; simpl; inv_hlist l; first done.
    intros x l. destruct i as [ | i]; simpl; first done.
    f_equiv. by eapply IH.
  Qed.
  Lemma hzipl_hlist_insert_id {X} {F} (Xl : list X) (l : hlist F Xl) (i : nat) (d : X) h :
    hzipl _ (hlist_insert_id d Xl l i h) = <[i := existT _ h]> (hzipl _ l).
  Proof.
    rewrite /hlist_insert_id. rewrite -hzipl_hlist_insert.
    generalize (list_insert_lnth Xl d i). intros <-. done.
  Qed.

  (** Interaction of mapping and list insertion *)
  Lemma hcmap_hlist_insert {X Y} {F} (f : ∀ x, F x → Y) (Xl : list X) (hl : hlist F Xl) i x0 (a : F x0) :
    hcmap f (hlist_insert Xl hl i x0 a) = <[i := f x0 a]> (hcmap f hl).
  Proof.
    induction Xl as [ | x Xl IH] in hl, i |-*; simpl; inv_hlist hl; first done.
    intros x1 hl. destruct i as [ | i]; simpl; first done.
    f_equiv. eapply IH.
  Qed.
  Lemma hcmap_hlist_insert_id {X Y} {F} (f : ∀ x, F x → Y) (Xl : list X) (hl : hlist F Xl) i d (a : F (lnth d Xl i)) :
    hcmap f (hlist_insert_id d Xl hl i a) = <[i := f _ a]> (hcmap f hl).
  Proof.
    rewrite /hlist_insert_id. rewrite -hcmap_hlist_insert.
    generalize (list_insert_lnth Xl d i). intros <-. done.
  Qed.
  Lemma hmap_hlist_insert {X} {F G} (f : ∀ x, F x → G x) (Xl : list X) (hl : hlist F Xl) i x0 (a : F x0) :
    hmap f (hlist_insert Xl hl i x0 a) = hlist_insert Xl (hmap f hl) i x0 (f x0 a).
  Proof.
    induction Xl as [ | x Xl IH] in hl, i |-*; simpl; inv_hlist hl; first done.
    intros x1 hl. destruct i as [ | i]; simpl; first done.
    f_equiv. eapply IH.
  Qed.
  Lemma hmap_hlist_insert_id {X} {F G} (f : ∀ x, F x → G x) (Xl : list X) (hl : hlist F Xl) i d (a : F (lnth d Xl i)) :
    hmap f (hlist_insert_id d Xl hl i a) = hlist_insert_id d Xl (hmap f hl) i (f _ a).
  Proof.
    rewrite /hlist_insert_id. rewrite -hmap_hlist_insert.
    generalize (list_insert_lnth Xl d i). intros <-. done.
  Qed.
End hlist_replace.

Section plist_replace.
  Set Universe Polymorphism.

  Definition plist_insert {X} {F} : ∀ (Xl : list X) (l : plist F Xl) (i : nat) (x0 : X) (h : F x0), plist F (<[i := x0]> Xl).
  Proof.
    refine (fix rec Xl :=
      match Xl with
      | [] => λ l i x0 h, -[]
      | x1 :: Xl => λ l i x0 h,
          let '(cons_pair h1 l) := l in
          match i with
          | 0%nat => pcons h l
          | S i => pcons h1 (rec Xl l i x0 h)
          end
      end).
  Defined.

  Definition plist_insert_id {X} {F} (d : X) (Xl : list X) (l : plist F Xl) (i : nat) (h : F (lnth d Xl i)) : plist F Xl.
  Proof.
    exact (let r := plist_insert Xl l i _ h in
      rew (list_insert_lnth Xl d i) in r).
  Defined.

  (* TODO remove? *)
  Definition plist_insert_id' {X} {F} (Xl : list X) (l : plist F Xl) (i : nat) (x0 : X) (h : F x0) (Heq : Xl !! i = Some x0) : plist F Xl.
  Proof.
    exact (let r := plist_insert Xl l i x0 h in
      rew (list_insert_id Xl i x0 Heq) in r).
  Defined.

  Lemma pzipl_plist_insert {X} {F} (Xl : list X) (l : plist F Xl) (i : nat) (x0 : X) (h : F x0) :
    pzipl _ (plist_insert Xl l i x0 h) = <[i := existT x0 h]> (pzipl _ l).
  Proof.
    induction Xl as [ | x1 Xl IH] in i, l |-*; simpl; first done.
    destruct l as [x l]. destruct i as [ | i]; simpl; first done.
    f_equiv. by eapply IH.
  Qed.
  Lemma pzipl_plist_insert_id {X} {F} (Xl : list X) (l : plist F Xl) (i : nat) (d : X) h :
    pzipl _ (plist_insert_id d Xl l i h) = <[i := existT _ h]> (pzipl _ l).
  Proof.
    rewrite /plist_insert_id. rewrite -pzipl_plist_insert.
    generalize (list_insert_lnth Xl d i). intros <-. done.
  Qed.

  Lemma pcmap_plist_insert {X Y} {F} (f : ∀ x, F x → Y) (Xl : list X) (pl : plist F Xl) i x0 (a : F x0) :
    pcmap f (plist_insert Xl pl i x0 a) = <[i := f x0 a]> (pcmap f pl).
  Proof.
    induction Xl as [ | x Xl IH] in pl, i |-*; simpl; first done.
    destruct pl as [x1 pl]. destruct i as [ | i]; simpl; first done.
    f_equiv. eapply IH.
  Qed.
  Lemma pcmap_plist_insert_id {X Y} {F} (f : ∀ x, F x → Y) (Xl : list X) (pl : plist F Xl) i d (a : F (lnth d Xl i)) :
    pcmap f (plist_insert_id d Xl pl i a) = <[i := f _ a]> (pcmap f pl).
  Proof.
    rewrite /plist_insert_id. rewrite -pcmap_plist_insert.
    generalize (list_insert_lnth Xl d i). intros <-. done.
  Qed.
  Lemma pmap_plist_insert {X} {F G} (f : ∀ x, F x → G x) (Xl : list X) (pl : plist F Xl) i x0 (a : F x0) :
    pmap f (plist_insert Xl pl i x0 a) = plist_insert Xl (pmap f pl) i x0 (f x0 a).
  Proof.
    induction Xl as [ | x Xl IH] in pl, i |-*; simpl; first done.
    destruct pl as [x1 pl]. destruct i as [ | i]; simpl; first done.
    rewrite IH. done.
  Qed.
  Lemma pmap_plist_insert_id {X} {F G} (f : ∀ x, F x → G x) (Xl : list X) (pl : plist F Xl) i d (a : F (lnth d Xl i)) :
    pmap f (plist_insert_id d Xl pl i a) = plist_insert_id d Xl (pmap f pl) i (f _ a).
  Proof.
    rewrite /plist_insert_id. rewrite -pmap_plist_insert.
    generalize (list_insert_lnth Xl d i). intros <-. done.
  Qed.
End plist_replace.

Section hpzip.
  Set Universe Polymorphism.
  Fixpoint hpzipl {X} {F : X → Type} {G : X → Type} (l : list X) (hl : hlist F l) : plist G l → list (sigT (λ X, F X * G X))%type :=
    match hl with
    | hnil _ => λ _, []
    | @hcons _ _ X l x hl => λ pl,
        (existT X (x, phd pl)) :: hpzipl l hl (ptl pl)
    end.

  Fixpoint hpziphl {X} {F G : X → Type} (l : list X) (hl : hlist F l) : plist G l → hlist (λ x, F x * G x)%type l :=
    match hl with
    | +[] => λ pl, +[]
    | a +:: hl => λ pl,
        (a, phd pl) +:: hpziphl _ hl (ptl pl)
    end.

  Context {X} {F : X → Type} {G : X → Type}.
  Lemma hpzipl_length (l : list X) (hl : hlist F l) (pl : plist G l) :
    length (hpzipl l hl pl) = length l.
  Proof. induction hl; naive_solver. Qed.
  Lemma hpzipl_lookup (l : list X) (hl : hlist F l) (pl : plist G l) i x :
    l !! i = Some x →
    ∃ y z, hpzipl l hl pl !! i = Some (existT x (y, z)).
  Proof.
    intros Hlook. induction hl as [ | X' l y hl IH ] in i, pl, Hlook |-*.
    - done.
    - destruct pl as [z pl].
      destruct i as [ | i]; simpl in Hlook.
      + injection Hlook as [= ->]. eauto.
      + eapply IH in Hlook as (y' & Hlook). simpl; eauto.
  Qed.
  Lemma hpzipl_lookup_inv (l : list X) (hl : hlist F l) (pl : plist G l) i x y z :
    hpzipl l hl pl !! i = Some (existT x (y, z)) →
    l !! i = Some x.
  Proof.
    induction hl as [ | X' l y' hl IH] in i, pl |-*; simpl.
    - done.
    - destruct pl as [z' pl]. destruct i as [ | i]; simpl.
      + by intros [= -> Heq].
      + apply IH.
  Qed.
  Lemma hpzipl_lookup_inv_hzipl_pzipl (l : list X) (hl : hlist F l) (gl : plist G l) i x y z :
    hpzipl l hl gl !! i = Some (existT x (y, z)) →
    hzipl l hl !! i = Some (existT x y) ∧ pzipl l gl !! i = Some (existT x z).
  Proof.
    induction hl as [ | X' l y' hl IH] in i, gl |-*; simpl.
    - done.
    - destruct gl as [z' gl]. destruct i as [ | i]; simpl.
      + intros [= -> [= Heq1] [= Heq2]]. rewrite Heq1 Heq2; done.
      + apply IH.
  Qed.

  Lemma hpzipl_hzipl2_lookup (Xs : list X) (l1 l2 : hlist F Xs) (pl1 pl2 : plist G Xs) (x : X) y1 y2 i :
    hpzipl Xs l1 pl1 !! i = Some (existT x y1) →
    hpzipl Xs l2 pl2 !! i = Some (existT x y2) →
    hzipl2 Xs l1 l2 !! i = Some (existT x (y1.1, y2.1)).
  Proof.
    induction Xs as [ | X0 Xs IH] in i, l1, l2, pl1, pl2 |-*; inv_hlist l1; inv_hlist l2; simpl; first done.
    intros x1 xl1 x2 xl2. destruct i as [ | i ]; simpl.
    - intros [= [= ->] Ha] [= Hb]. apply existT_inj in Ha as <-. apply existT_inj in Hb as <-. done.
    - apply IH.
  Qed.
  Lemma hpzipl_hpzipl_lookup_1_eq (Xs : list X) (l : hlist F Xs) (pl1 pl2 : plist G Xs) (x : X) a1 a2 b1 b2 i:
    hpzipl Xs l pl1 !! i = Some (existT x (a1, b1)) →
    hpzipl Xs l pl2 !! i = Some (existT x (a2, b2)) →
    a1 = a2.
  Proof.
    induction Xs as [ | X0 Xs IH] in i, l, pl1, pl2 |-*; inv_hlist l; simpl; first done.
    intros x1 xl1. destruct i as [ | i ]; simpl.
    - intros [= [= ->] Ha Hb] [= Hc Hd]. apply existT_inj in Ha as <-. apply existT_inj in Hb as <-.
      apply existT_inj in Hc as <-. apply existT_inj in Hd as <-. done.
    - apply IH.
  Qed.
  Lemma hpzipl_hpzipl_lookup_2_eq (Xs : list X) (l1 l2 : hlist F Xs) (pl : plist G Xs) (x : X) a1 a2 b1 b2 i:
    hpzipl Xs l1 pl !! i = Some (existT x (a1, b1)) →
    hpzipl Xs l2 pl !! i = Some (existT x (a2, b2)) →
    b1 = b2.
  Proof.
    induction Xs as [ | X0 Xs IH] in i, l1, l2, pl |-*; inv_hlist l1; inv_hlist l2; simpl; first done.
    intros x1 xl1 x2 xl2. destruct i as [ | i ]; simpl.
    - intros [= [= ->] Ha Hb] [= Hc Hd]. apply existT_inj in Ha as <-. apply existT_inj in Hb as <-.
      apply existT_inj in Hc as <-. apply existT_inj in Hd as <-. done.
    - apply IH.
  Qed.

  Lemma hnth_pnth_hpzipl_lookup (Xl : list X) (d : X) (fd : F d) (gd : G d) (hl : hlist F Xl) (pl : plist G Xl) (i : nat) a b :
    i < length Xl →
    hnth fd hl i = a →
    pnth gd pl i = b →
    hpzipl Xl hl pl !! i = Some (existT (lnth d Xl i) (a, b)).
  Proof.
    induction Xl as [ | x0 Xl IH] in i, hl, pl, a, b |-*; inv_hlist hl; simpl; first lia.
    intros a0 hl Hi.
    destruct pl as [b0 pl].
    destruct i as [ | i].
    - intros -> ->. done.
    - intros Ha Hb. simpl. eapply IH; [lia | done..].
  Qed.

  Lemma insert_hpzipl (Xl : list X) (hl : hlist F Xl) (pl : plist G Xl) (x : X) (a : F x) (b : G x) i :
    <[i := existT x (a, b)]> (hpzipl Xl hl pl) =
    hpzipl (<[i := x]> Xl) (hlist_insert Xl hl i x a) (plist_insert Xl pl i x b).
  Proof.
    induction Xl as [ | x0 Xl IH] in i, hl, pl |-*; inv_hlist hl; simpl; first done.
    intros a0 hl. destruct pl as [b0 pl].
    destruct i as [ | i]; simpl.
    - done.
    - f_equiv. eapply IH.
  Qed.

  Lemma hpzipl_hmap {H} (Xl : list X) (hl : hlist F Xl) (pl : plist G Xl) (f : ∀ x : X, F x → H x) :
    hpzipl Xl (hmap f hl) pl = (λ '(existT x (a,  b)), existT x (f _ a, b)) <$> hpzipl Xl hl pl.
  Proof.
    induction Xl as [ | x Xl IH]; simpl; inv_hlist hl; first done.
    intros a hl. destruct pl as [b pl]. simpl. f_equiv. eapply IH.
  Qed.

  Lemma big_sepL2_hzipl_hzipl_sepL_hzipl2 {PROP : bi} (Xs : list X) (l1 : hlist F Xs) (l2 : hlist G Xs) (Φ : nat → sigT F → sigT G → PROP) (Ψ : nat → sigT (λ x, F x * G x)%type → PROP) m :
    (∀ i x a b, Φ i (existT x a) (existT x b) ⊣⊢ Ψ i (existT x (a, b))) →
    ([∗ list] i ↦ a; b ∈ hzipl Xs l1; hzipl Xs l2, Φ (m + i)%nat a b) ⊣⊢
    [∗ list] i ↦ p ∈ hzipl2 Xs l1 l2, Ψ (m + i)%nat p.
  Proof.
    intros Ha.
    induction Xs as [ | X0 Xs IH] in m, l1, l2 |-*; inv_hlist l1; inv_hlist l2; simpl; first done.
    intros x1 xl1 x2 xl2. setoid_rewrite Nat.add_succ_r. rewrite (IH _ _ (S m)). rewrite Ha. done.
  Qed.

  Lemma hpzipl_hpziphl_hzipl2_lookup (Xs : list X) (l1 l2 : hlist F Xs) (pl1 pl2 : plist G Xs) (x : X) y1 y2 i :
    hpzipl Xs l1 pl1 !! i = Some (existT x y1) →
    hpzipl Xs l2 pl2 !! i = Some (existT x y2) →
    hzipl2 Xs (hpziphl _ l1 pl1) (hpziphl _ l2 pl2) !! i = Some (existT x (y1, y2)).
  Proof.
    induction Xs as [ | X0 Xs IH] in i, l1, l2, pl1, pl2 |-*; inv_hlist l1; inv_hlist l2; simpl; first done.
    intros x1 xl1 x2 xl2. destruct i as [ | i ]; simpl.
    - intros [= [= ->] Ha] [= Hb]. apply existT_inj in Ha as <-. apply existT_inj in Hb as <-. done.
    - apply IH.
  Qed.

  Lemma hpziphl_fmap_l {H : X → Type} (Xs : list X) (hl : hlist F Xs) (pl : plist G Xs) (f : ∀ x : X, F x → H x) :
    hpziphl _ (f +<$> hl) pl = (λ x p, (f _ p.1, p.2)) +<$> (hpziphl _ hl pl).
  Proof.
    induction Xs as [ | X0 Xs IH] in hl, pl |-*; inv_hlist hl.
    - destruct pl. done.
    - intros x hl. destruct pl as [p pl]. simpl. rewrite IH. done.
  Qed.

End hpzip.

Global Arguments hnth : simpl nomatch.
Global Arguments pnth : simpl nomatch.
Global Arguments lnth : simpl nomatch.
Global Arguments hlist_insert : simpl nomatch.
Global Arguments plist_insert : simpl nomatch.

Section of_list.
  Context {X} {F : X → Type} (a : X).
  Fixpoint list_to_plist (l : list (F a)) : plist F (replicate (length l) a) :=
    match l with
    | [] => -[]
    | x :: l => x -:: list_to_plist l
    end.

  Fixpoint mk_const_hlist (x : F a) n : hlist F (replicate n a) :=
    match n with
    | 0 => +[]
    | S n => x +:: mk_const_hlist x n
    end.
  Fixpoint mk_const_plist (x : F a) n : plist F (replicate n a) :=
    match n with
    | 0 => -[]
    | S n => x -:: mk_const_plist x n
    end.

  Lemma mk_const_plist_pzipl_lookup c n i :
    i < n → pzipl _ (mk_const_plist c n) !! i = Some (existT _ c).
  Proof.
    induction n as [ | n IH] in i |-*; simpl; first lia.
    intros Ha. destruct i as [ | i]; simpl; first done.
    apply IH. lia.
  Qed.
  Lemma mk_const_hlist_hzipl_lookup c n i :
    i < n → hzipl _ (mk_const_hlist c n) !! i = Some (existT _ c).
  Proof.
    induction n as [ | n IH] in i |-*; simpl; first lia.
    intros Ha. destruct i as [ | i]; simpl; first done.
    apply IH. lia.
  Qed.
End of_list.
