From Coq Require Import Qcanon.
From caesium Require Import derived.
From iris.bi Require Import fractional.
From iris.proofmode Require Import tactics.
From refinedrust Require Export base.
From iris.prelude Require Import options.
Set Default Proof Using "Type".

(** * Random collection of lemmas *)
(* TODO: probably some of this could be upstreamed *)

(** ** Pure lemmas *)
Program Definition Qp_total_sub (p q : Qp) : (q < p)%Qp → Qp :=
  match p, q with
  | mk_Qp p Hp, mk_Qp q Hq =>
      λ (Hle : (mk_Qp q Hq < mk_Qp p Hp)%Qp),
        let pq := (p - q)%Qc in (mk_Qp pq _)
  end.
Next Obligation.
  intros. rewrite -Qclt_minus_iff. apply Hle.
Qed.
Lemma Qp_total_sub_eq (q p : Qp) Hlt :
  (Qp_total_sub p q Hlt + q)%Qp = p.
Proof.
  destruct p as [p ], q as [q ].
  simpl. unfold Qp.add.
  match goal with
  | |- mk_Qp ?a ?pr = _ => generalize pr as prf; assert (a = p) as Heq by ring
  end.
  revert Heq. generalize (p - q + q)%Qc.
  intros ? -> ?. f_equal. apply proof_irrel.
Qed.

Lemma Fractional_fractional_le {Σ} (Φ : Qp → iProp Σ) `{Fractional _ Φ} (q q' : Qp):
  (q' ≤ q)%Qp →
  Φ q -∗
  Φ q' ∗ (Φ q' -∗ Φ q).
Proof.
  iIntros (Hle) "HΦ".
  destruct (decide (q = q')) as [<- | ?].
  { eauto with iFrame. }
  assert (q' < q)%Qp as Hlt.
  { apply Qp.le_lteq in Hle as [ | ]; done. }
  specialize (Qp_total_sub_eq q' q Hlt) as <-.
  iPoseProof (fractional with "HΦ") as "[H1 $]".
  iIntros "H2". iApply fractional; iFrame.
Qed.

Lemma Fractional_split_big_sepL {Σ} (Φ : Qp → iProp Σ) `{!Fractional Φ} n q :
  Φ q -∗ ∃ qs, ⌜length qs = n⌝ ∗
    ([∗ list] q' ∈ qs, Φ q') ∗
    (([∗ list] q' ∈ qs, Φ q') -∗ Φ q).
Proof.
  iInduction n as [ | n ] "IH" forall (q); simpl.
  - iIntros "Hp". iExists []. iSplitR; first done. iSplitR; first done. iIntros "_". done.
  - iIntros "Hp".
    rewrite -(Qp.div_2 q) {1}fractional. iDestruct "Hp" as "[Hp1 Hp2]".
    iDestruct ("IH" with "Hp2") as "(%qs & %Hlen & Hown & Hcl)".
    iExists ((q/2)%Qp :: qs).
    simpl. rewrite -Hlen. iSplitR; first done.
    iFrame.
    iIntros "(Ha & Hown)". iPoseProof ("Hcl" with "Hown") as "Ha2".
    iCombine "Ha Ha2" as "Ha". rewrite -fractional. done.
Qed.

Global Instance fractional_bi_later {Σ} (Φ : Qp → iProp Σ) :
  Fractional Φ → Fractional (λ q, ▷ Φ q)%I.
Proof.
  rewrite /Fractional. intros Ha p q. rewrite Ha bi.later_sep//.
Qed.


Lemma list_max_insert (l : list nat) i n :
  list_max (<[i := n]> l) ≤ Nat.max n (list_max l).
Proof.
  induction l as [ | a l IH] in i |-*; simpl.
  - lia.
  - destruct i as [ | i]; simpl; first lia.
    specialize (IH i). lia.
Qed.

Lemma list_max_le_lookup l i (m n : nat) :
  l !! i = Some m →
  n ≤ m →
  n ≤ list_max l.
Proof.
  induction l as [ | k l IH] in i |-*; simpl; first done.
  destruct i as [ | i]; simpl.
  - intros [= ->]. lia.
  - intros Ha ?. eapply IH in Ha; lia.
Qed.

Lemma lookup_zip {A B} (xs : list A) (ys : list B) i z :
  zip xs ys !! i = Some z →
  xs !! i = Some z.1 ∧ ys !! i = Some z.2.
Proof.
  induction xs as [ | x xs IH] in ys, i |-*; destruct ys as [ | y ys]; simpl; [ done.. | ].
  destruct i as [ | i]; simpl.
  - injection 1 as [= <-]. done.
  - apply IH.
Qed.

Lemma list_lookup_omap_Some {A B} (l : list A) (f : A → option B) x y i :
  l !! i = Some x →
  f x = Some y →
  ∃ j, omap f l !! j = Some y.
Proof.
  induction l as [ | h l IH] in i |-*; simpl; first done.
  destruct i as [ | i]; simpl.
  - intros [= ->] -> => /=.
    by exists 0.
  - intros Hlook Ha. destruct (IH _ Hlook Ha) as (j & Hlook').
    destruct (f h) as [Hx | ].
    + exists (S j). naive_solver.
    + naive_solver.
Qed.

Lemma elem_of_cons_dec {A} `{!EqDecision A} (l : list A) (x y : A) :
  x ∈ y :: l ↔ x = y ∨ x ≠ y ∧ x ∈ l.
Proof.
  rewrite elem_of_cons. destruct (decide (x = y)) as [<- | ?]; naive_solver.
Qed.

Lemma aligned_to_2_max_l l n1 n2 :
  l `aligned_to` 2 ^ (max n1 n2) →
  l `aligned_to` 2 ^ n1.
Proof.
  rewrite /aligned_to.
  assert ((2 ^ n1)%nat | (2 ^ (n1 `max` n2))%nat)%Z.
  { apply Zdivide_nat_pow. lia. }
  destruct caesium_config.enforce_alignment; last done.
  intros. etrans; last done. done.
Qed.
Lemma aligned_to_2_max_r l n1 n2 :
  l `aligned_to` 2 ^ (max n1 n2) →
  l `aligned_to` 2 ^ n2.
Proof. rewrite Nat.max_comm. apply aligned_to_2_max_l. Qed.


Lemma list_subseteq_mjoin {A} (l : list (list A)) (x : list A) :
  x ∈ l → x ⊆ mjoin l.
Proof.
  induction l as [ | y l' IH] in x |-*; simpl.
  - intros []%elem_of_nil.
  - intros [ -> | Hel]%elem_of_cons.
    + set_solver.
    + apply IH in Hel. set_solver.
Qed.

Lemma reshape_replicate_elem_length {A} (vs : list A) v n m :
  length vs = n * m →
  v ∈ reshape (replicate n m) vs →
  length v = m.
Proof.
  intros Hlen. induction n as [ | n IH] in vs, Hlen |-*; simpl.
  { rewrite elem_of_nil; done. }
  rewrite elem_of_cons.
  intros [-> | Hel].
  - rewrite take_length. lia.
  - eapply IH; last apply Hel.
    rewrite drop_length. lia.
Qed.

Lemma reshape_replicate_0 {A} (xs : list A) n :
  reshape (replicate n 0) xs = replicate n [].
Proof.
  induction n as [ | n IH]; simpl; first done.
  rewrite take_0 drop_0. f_equiv. apply IH.
Qed.

Section Forall.
  (** Recursive version of Forall, to make it computational and eligible for recursive definitions. *)
  Context {X} (P : X → Prop).
  Fixpoint Forall_cb (l : list X) :=
    match l with
    | [] => True
    | x :: l => P x ∧ Forall_cb l
    end.
  Lemma Forall_Forall_cb l :
    Forall P l ↔ Forall_cb l.
  Proof.
    induction l as [ | x l IH].
    - naive_solver.
    - simpl. split; last naive_solver. inversion 1; naive_solver.
  Qed.
End Forall.

Lemma Forall_iff_strong {A} (P Q : A → Prop) (l : list A) :
  (∀ x, x ∈ l → P x ↔ Q x) →
  Forall P l ↔ Forall Q l.
Proof.
  intros Hequiv. induction l as [ | x l IH]; simpl; first done.
  split; inversion 1; subst; (constructor; [ apply Hequiv; [ apply elem_of_cons | ] | apply IH]); eauto.
  all: intros; apply Hequiv; apply elem_of_cons; eauto.
Qed.

Lemma Forall_impl_strong {A} (P Q : A → Prop) (l : list A) :
  (∀ x, x ∈ l → P x → Q x) →
  Forall P l → Forall Q l.
Proof.
  intros Himpl. induction l as [ | x l IH]; simpl; first done.
  inversion 1; subst; (constructor; [ apply Himpl; [ apply elem_of_cons | ] | apply IH]); eauto.
  intros; apply Himpl; [apply elem_of_cons | ]; eauto.
Qed.

Lemma Forall_elem_of_iff {X} (P : X → Prop) l :
  Forall P l ↔ ∀ x, x ∈ l → P x.
Proof.
  rewrite Forall_lookup.
  split.
  - intros ? ? (i & Hel)%elem_of_list_lookup_1. eauto.
  - intros Hel i x Hlook%elem_of_list_lookup_2. eauto.
Qed.

Lemma Forall2_eq {A} (l1 l2 : list A) :
  Forall2 eq l1 l2 → l1 = l2.
Proof.
  induction l1 as [ | x1 l1 IH] in l2 |-*; simpl.
  { intros ->%Forall2_nil_inv_l. done. }
  intros (y1 & l2' & -> & Hf & ->)%Forall2_cons_inv_l.
  f_equiv. by apply IH.
Qed.

Lemma and_proper (A B C : Prop) :
  (A → B ↔ C) →
  (A ∧ B) ↔ (A ∧ C).
Proof. naive_solver. Qed.

Lemma zip_flip {A B} (l1 : list A) (l2 : list B) :
  zip l1 l2 = (λ '(x1, x2), (x2, x1)) <$> zip l2 l1.
Proof.
  induction l1 as [ | x1 l1 IH] in l2 |-*; simpl.
  { destruct l2; done. }
  destruct l2 as [ | x2 l2]; first done.
  simpl. f_equiv. apply IH.
Qed.
Lemma zip_assoc_r {A B C} (l1 : list A) (l2 : list B) (l3 : list C) :
  zip l1 (zip l2 l3) = (λ '((x, y), z), (x, (y, z))) <$> zip (zip l1 l2) l3.
Proof.
  induction l1 as [ | x l1 IH] in l2, l3 |-*; simpl; first done.
  destruct l2 as [ | y l2]; first done.
  destruct l3 as [ | z l3]; first done.
  simpl. f_equiv. apply IH.
Qed.
Lemma zip_assoc_l {A B C} (l1 : list A) (l2 : list B) (l3 : list C) :
  zip (zip l1 l2) l3 = (λ '(x, (y, z)), ((x, y), z)) <$> zip l1 (zip l2 l3).
Proof.
  induction l1 as [ | x l1 IH] in l2, l3 |-*; simpl; first done.
  destruct l2 as [ | y l2]; first done.
  destruct l3 as [ | z l3]; first done.
  simpl. f_equiv. apply IH.
Qed.

Lemma zip_fmap_l {A B C} (l1 : list A) (l2 : list B) (f : A → C) :
  zip (f <$> l1) l2 = (λ x : A * B, (f x.1, x.2)) <$> (zip l1 l2).
Proof.
  induction l1 as [ | a l1 IH] in l2 |-*; destruct l2 as [ | l2]; simpl; [done.. | ].
  f_equiv. apply IH.
Qed.

Lemma zip_length {A B} (l1 : list A) (l2 : list B) :
  length (zip l1 l2) = min (length l1) (length l2).
Proof.
  induction l1 as [ | x l1 IH] in l2 |-*; destruct l2 as [ | y l2]; simpl; [done.. | ].
  rewrite IH. done.
Qed.

Lemma zip_app {A B} (l1 l2 : list A) (l1' l2' : list B) :
  length l1 = length l1' →
  zip (l1 ++ l2) (l1' ++ l2') = zip l1 l1' ++ zip l2 l2'.
Proof.
  intros Hlen. induction l1 as [ | h1 l1 IH] in l1', Hlen |-*; simpl.
  { destruct l1'; done. }
  destruct l1' as [ | h1' l1']; first done.
  simpl. f_equiv. apply IH. simpl in *; lia.
Qed.

Lemma map_fmap {A B} (f : A → B) (l : list A) :
  f <$> l = map f l.
Proof. done. Qed.

(** ** big_sepL *)
Lemma big_sepL2_insert {Σ} {A B} (l1 : list A) (l2 : list B) (i : nat) (x1 : A) (x2 : B) (Φ : nat → A → B → iProp Σ) (m : nat) :
  i < length l1 →
  i < length l2 →
  ([∗ list] k ↦ v1; v2 ∈ <[i := x1]> l1; <[i := x2]> l2, Φ (m + k)%nat v1 v2) ⊣⊢ Φ (m + i)%nat x1 x2 ∗
    ([∗ list] k ↦ v1; v2 ∈ l1; l2, if decide (k = i) then emp else Φ (m + k)%nat v1 v2).
Proof.
  iInduction l1 as [ | h1 l1] "IH" forall (m i l2); simpl; iIntros (Hlt1 Hlt2); first lia.
  destruct l2 as [ | h2 l2]; simpl in *; first lia.
  destruct i as [ | i]; simpl.
  - iSplit.
    + iIntros "($ & Ha)". iSplitR; first done.
      setoid_rewrite Nat.add_succ_r. done.
    + iIntros "($ & _ & $)".
  - assert (Hlt1' : i < length l1) by lia. assert (Hlt2' : i < length l2) by lia.
    iSplit.
    + iIntros "($ & Ha)". setoid_rewrite Nat.add_succ_r.
      iPoseProof ("IH" $! (S m) i _ Hlt1' Hlt2' with "Ha") as "($ & Ha)".
      iApply (big_sepL2_mono with "Ha").
      iIntros (?????). case_decide as Heq; case_decide as Heq2; [first [lia | by eauto].. | ].
      rewrite Nat.add_succ_r. eauto.
    + iIntros "(Ha & $ & Hb)".

      rewrite Nat.add_succ_r.
      setoid_rewrite Nat.add_succ_r. iApply ("IH" $! (S m) i _ Hlt1' Hlt2'). iFrame "Ha".
      iApply (big_sepL2_mono with "Hb").
      iIntros (?????). case_decide as Heq; case_decide as Heq2; [first [lia | by eauto].. | ].
      rewrite Nat.add_succ_r. eauto.
Qed.

Lemma big_sepL_concat_lookup {Σ} {A} (L : list (list A)) (l : list A) (i : nat) (Φ : A → iProp Σ) :
  L !! i = Some l →
  ([∗ list] x ∈ concat L, Φ x) -∗
  [∗ list] x ∈ l, Φ x.
Proof.
  iInduction L as [ | l0 L IH] "IH" forall (i); simpl; iIntros (Hlook) "Ha"; first done.
  destruct i as [ | i]; simpl in *.
  - injection Hlook as [= ->].
    rewrite big_sepL_app. iDestruct "Ha" as "($ & _)".
  - rewrite big_sepL_app. iDestruct "Ha" as "(_ & Ha)".
    iApply "IH"; done.
Qed.

Lemma big_sepL2_Forall2 {Σ} {A B} (Φ : A → B → Prop) l1 l2 :
  ([∗ list] x;y ∈ l1; l2, ⌜Φ x y⌝) -∗ ⌜Forall2 Φ l1 l2⌝ : iProp Σ.
Proof.
  iIntros "Ha". iInduction l1 as [ | x l1] "IH" forall (l2) "Ha"; destruct l2 as [ | y l2]; simpl; [done.. | ].
  iDestruct "Ha" as "(%Ha & Hb)". iPoseProof ("IH" with "Hb") as "%Hc".
  iPureIntro. constructor; done.
Qed.
Lemma big_sepL_Forall {Σ} {A} (Φ : A → Prop) l :
  ([∗ list] x ∈ l, ⌜Φ x⌝) -∗ ⌜Forall Φ l⌝ : iProp Σ.
Proof.
  iIntros "Ha". iInduction l as [ | x l] "IH"; simpl; first done.
  iDestruct "Ha" as "(%Ha & Hb)". iPoseProof ("IH" with "Hb") as "%Hc".
  iPureIntro. constructor; done.
Qed.

(* when we know that the length is equal, we can get a stronger lemma *)
Lemma big_sepL2_laterN' {Σ} {A B} (Φ : nat → A → B → iProp Σ) (l1 : list A) (l2 : list B) n :
  length l1 = length l2 →
  ▷^n ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) ⊣⊢
   ([∗ list] k↦y1;y2 ∈ l1;l2, ▷^n Φ k y1 y2).
Proof.
  induction l1 as [ | a l1 IH] in l2, Φ |-*; destruct l2 as [ | b l2]; simpl; [intros; iSplit; eauto.. | ]; intros Hlen.
  iSplit; (iIntros "($ & Hb)"; iApply IH; [ lia | done]).
Qed.

Lemma big_sepL2_length_ne {Σ} {A B}  (l1 : list A) (l2 : list B) :
  length l1 ≠ length l2 →
  ∀ (Φ : nat → A → B → iProp Σ), ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2) ⊣⊢ False.
Proof.
  induction l1 as [ | x l1 IH] in l2 |-*; destruct l2 as [ | l2]; simpl; [done.. | ].
  intros Hneq Φ.
  rewrite IH; last lia.
  iSplit; [iIntros "(_ & $)" | iIntros "[]"].
Qed.

(* Lemma that gives additional [lookup] assumptions for the requirement persistence proof *)
Local Lemma big_sepL2_persistent_strong' {Σ} {A B} (Φ : nat → A → B → iProp Σ) (l1 : list A) (l2 : list B) :
  ∀ m,
  (∀ (k : nat) (x1 : A) (x2 : B), l1 !! k = Some x1 → l2 !! k = Some x2 → Persistent (Φ (m + k) x1 x2)) →
  Persistent ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ (m + k) y1 y2).
Proof.
  intros m Hpers.
  induction l1 as [ | y1 l1 IH] in m, Hpers, l2 |-*; destruct l2 as [ | y2 l2]; simpl; [apply _ .. | ].
  apply bi.sep_persistent.
  - apply Hpers; done.
  - setoid_rewrite Nat.add_succ_r. eapply (IH _ (S m)).
    intros. simpl. rewrite -Nat.add_succ_r. eapply (Hpers); done.
Qed.
Lemma big_sepL2_persistent_strong {Σ} {A B} (Φ : nat → A → B → iProp Σ) (l1 : list A) (l2 : list B) :
  (length l1 = length l2 → ∀ (k : nat) (x1 : A) (x2 : B), l1 !! k = Some x1 → l2 !! k = Some x2 → Persistent (Φ k x1 x2)) →
  Persistent ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2).
Proof.
  intros Hpers.
  destruct (decide (length l1 = length l2)).
  - eapply (big_sepL2_persistent_strong' _ _ _ 0); by apply Hpers.
  - rewrite big_sepL2_length_ne; first apply _. done.
Qed.

Local Lemma big_sepL_exists_zip' {Σ} {A X} (Φ : nat → A → X → iProp Σ) (l : list A) k :
  ([∗ list] i ↦ a ∈ l, ∃ x : X, Φ (k + i) a x) ⊣⊢
  (∃ xl : list X, ⌜length xl = length l⌝ ∗ [∗ list] i ↦ p ∈ zip l xl, Φ (k + i) p.1 p.2).
Proof.
  induction l as [ | a l IH] in k |-*; simpl.
  { iSplit; last by eauto. iIntros "_". iExists []. done. }
  iSplit.
  - iIntros "([%x Hx] & Hl)". setoid_rewrite Nat.add_succ_r.
    rewrite (IH (S k)). iDestruct "Hl" as "(%xl & %Hlen & Hl)".
    iExists (x :: xl). simpl. iFrame. iSplitR. { iPureIntro; lia. }
    iApply (big_sepL_impl with "Hl").
    iIntros "!>" (? [] ?). setoid_rewrite Nat.add_succ_r. eauto.
  - iIntros "(%xl & %Hlen & Hl)".
    destruct xl as [ | x xl]; simpl; first done.
    iDestruct "Hl" as "(Hx & Hl)".
    iSplitL "Hx". { iExists x. done. }
    setoid_rewrite Nat.add_succ_r. rewrite (IH (S k)).
    iExists xl. iSplitR. { simpl in Hlen; iPureIntro; lia. }
    iApply (big_sepL_impl with "Hl").
    iIntros "!>" (? [] ?). simpl. eauto.
Qed.
Lemma big_sepL_exists_zip {Σ} {A X} (Φ : nat → A → X → iProp Σ) (l : list A) :
  ([∗ list] i ↦ a ∈ l, ∃ x : X, Φ i a x) ⊣⊢
  (∃ xl : list X, ⌜length xl = length l⌝ ∗ [∗ list] i ↦ p ∈ zip l xl,  Φ i p.1 p.2).
Proof. apply (big_sepL_exists_zip' _ _ 0). Qed.

Local Lemma big_sepL_exists' {Σ} {A X} (Φ : nat → A → X → iProp Σ) (l : list A) k :
  ([∗ list] i ↦ a ∈ l, ∃ x : X, Φ (k + i) a x) ⊣⊢
  (∃ xl : list X, [∗ list] i ↦ a; x ∈ l; xl, Φ (k + i) a x).
Proof.
  induction l as [ | a l IH] in k |-*; simpl.
  { iSplit; last by eauto. iIntros "_". iExists []. done. }
  iSplit.
  - iIntros "([%x Hx] & Hl)". setoid_rewrite Nat.add_succ_r.
    rewrite (IH (S k)). iDestruct "Hl" as "(%xl & Hl)".
    iExists (x :: xl). simpl. iFrame.
    setoid_rewrite Nat.add_succ_r. done.
  - iIntros "(%xl & Hl)".
    destruct xl as [ | x xl]; simpl; first done.
    iDestruct "Hl" as "(Hx & Hl)".
    iSplitL "Hx". { iExists x. done. }
    setoid_rewrite Nat.add_succ_r. rewrite (IH (S k)).
    iExists xl. done.
Qed.
Lemma big_sepL_exists {Σ} {A X} (Φ : nat → A → X → iProp Σ) (l : list A) :
  ([∗ list] i ↦ a ∈ l, ∃ x : X, Φ i a x) ⊣⊢
  (∃ xl : list X, [∗ list] i ↦ a; x ∈ l; xl, Φ i a x).
Proof. apply (big_sepL_exists' _ _ 0). Qed.


Lemma big_sepL_prep_for_ind {Σ} {A} (Φ : nat → A → iProp Σ) (l : list A) :
  (∀ k, [∗ list] i ↦ x ∈ l, Φ (k + i) x) -∗
  ([∗ list] i ↦ x ∈ l, Φ i x).
Proof.
  iIntros "Ha". iApply ("Ha" $! 0).
Qed.
Lemma big_sepL2_prep_for_ind {Σ} {A B} (Φ : nat → A → B → iProp Σ) (l1 : list A) (l2 : list B) :
  (∀ k, [∗ list] i ↦ x; y ∈ l1; l2, Φ (k + i) x y) -∗
  ([∗ list] i ↦ x; y ∈ l1; l2, Φ i x y).
Proof.
  iIntros "Ha". iApply ("Ha" $! 0).
Qed.

Section big_sepL.
  Context {Σ: gFunctors}.
  (** Definition of [big_sepL] that also provides a proof that the elements are really contained in the list,
     in order to get the recursive definition for the struct ltype through. *)
  Program Fixpoint big_sepL_P {A : Type} (l : list A) (f : ∀ (i : nat) (a : A), a ∈ l → iProp Σ) : iProp Σ :=
    match l as l0 return l0 = l → iProp Σ with
    | [] => λ _, True%I
    | a :: l' => λ Heq, (f 0%nat a _ ∗ big_sepL_P l' (λ i a Hel, f (S i) a _))%I
    end eq_refl.
  Next Obligation.
    intros. rewrite -Heq. apply elem_of_cons. by left.
  Qed.
  Next Obligation.
    intros. rewrite -Heq. apply elem_of_cons. by right.
  Qed.

  Lemma big_sepL_P_ext {A : Type} (l : list A) (f1 f2 : ∀ (i : nat) (a : A), a ∈ l → iProp Σ) :
    (∀ i a H, f1 i a H = f2 i a H) →
    big_sepL_P l f1 = big_sepL_P l f2.
  Proof.
    intros Heq. induction l as [ | a l IH]; simpl; first done.
    rewrite Heq. f_equiv. apply IH.
    intros. rewrite Heq. done.
  Qed.

  Lemma big_sepL_ext {A : Type} (l : list A) (f1 f2 : nat → A → iProp Σ) :
    (∀ i a, f1 i a = f2 i a) →
    ([∗ list] i ↦ a ∈ l, f1 i a)%I = ([∗ list] i ↦ a ∈ l, f2 i a)%I.
  Proof.
    intros Heq. induction l as [ | a l IH] in f1, f2, Heq |-*; simpl; first done.
    rewrite Heq. f_equiv. apply IH.
    intros. rewrite Heq. done.
  Qed.

  (** We can just erase the extra proof-carrying stuff when the actually relevant term does not depend on the proof. *)
  Lemma big_sepL_P_eq' {A : Type} (l : list A) (f : nat → A → iProp Σ) n :
    big_sepL_P l (λ i a _, f (n + i)%nat a) = ([∗ list] i ↦ a ∈ l, f (n + i)%nat a)%I.
  Proof.
    induction l as [ | a l IH] in n |-*; simpl.
    - done.
    - f_equiv.
      rewrite (big_sepL_P_ext _ _ (λ i a _, f (S n + i)%nat a)); first last.
      { by setoid_rewrite Nat.add_succ_r. }
      rewrite (IH (S n)).
      apply big_sepL_ext. by setoid_rewrite Nat.add_succ_r.
  Qed.
  Lemma big_sepL_P_eq {A : Type} (l : list A) (f : nat → A → iProp Σ) :
    big_sepL_P l (λ i a _, f i a) = ([∗ list] i ↦ a ∈ l, f i a)%I.
  Proof. apply (big_sepL_P_eq' _ _ 0). Qed.
End big_sepL.

Lemma Forall_big_sepL {Σ} {X} (P : X → Prop) (Q : X → iProp Σ) (R : iProp Σ) (l : list X) :
  Forall P l →
  R -∗
  □(∀ x, R -∗ ⌜P x⌝ -∗ Q x ∗ R) -∗
  ([∗ list] x ∈ l, Q x) ∗ R.
Proof.
  iIntros (Hf) "HR #HP".
  iInduction l as [ | x l] "IH"; simpl; first by iFrame.
  inversion Hf; subst.
  iPoseProof ("HP" with "HR [//]") as "(Ha & HR)".
  iPoseProof ("IH" with "[//] HR") as "(Hb & HR)".
  iFrame.
Qed.

Lemma Forall2_big_sepL2 {Σ} {X Y} (P : X → Y → Prop) (Q : X → Y → iProp Σ) (R : iProp Σ) (l1 : list X) (l2 : list Y) :
  Forall2 P l1 l2 →
  length l1 = length l2 →
  R -∗
  □(∀ x y, R -∗ ⌜P x y⌝ -∗ Q x y ∗ R) -∗
  ([∗ list] x;y ∈ l1;l2, Q x y) ∗ R.
Proof.
  iIntros (Hf Hlen) "HR #HP".
  iInduction l1 as [ | x l] "IH" forall (l2 Hlen Hf); destruct l2 as [ | y l2]; simpl; [by iFrame |done | done | ].
  inversion Hf; subst.
  iPoseProof ("HP" with "HR [//]") as "(Ha & HR)".
  iPoseProof ("IH" with "[] [//] HR") as "(Hb & HR)".
  { simpl in *. iPureIntro. lia. }
  iFrame.
Qed.

Lemma big_sepL_eliminate_sequence {Σ} {A} (P : nat → iProp Σ) (l : list A) Φ i0 :
  ([∗ list] i ↦ x ∈ l, Φ (i + i0) x) -∗
  P i0 -∗
  (□ ∀ i x, ⌜l !! i = Some x⌝ -∗ P (i + i0) -∗ Φ (i + i0) x -∗ P (S (i + i0))) -∗
  P (length l + i0).
Proof.
  induction l as [ | x l IH] in i0 |-*; simpl.
  { iIntros "_ $ _"; done. }
  iIntros "(Ha & Hl) HP #Hp".
  setoid_rewrite <-Nat.add_succ_r.
  iApply (IH with "Hl [-]").
  - iApply ("Hp" $! 0 with "[] HP Ha"). done.
  - iModIntro. iIntros (i y Hlook) "HP Ha".
    rewrite {1 2}Nat.add_succ_r.
    iApply ("Hp" $! (S i) with "[] HP Ha"). done.
Qed.

Lemma big_sepL_eliminate_sequence_rev {Σ} {A} (P : nat → iProp Σ) (l : list A) Φ :
  ([∗ list] i ↦ x ∈ l, Φ i x) -∗
  P (length l) -∗
  □ (∀ i x, ⌜l !! i = Some x⌝ -∗ P (S i) -∗ Φ i x -∗ P i) -∗
  P 0.
Proof.
  induction l as [ | x l IH] using rev_ind; simpl.
  { iIntros "_ $ _ "; done. }
  iIntros "Hl HP #Hstep".
  rewrite big_sepL_app.
  rewrite !app_length/=.
  rewrite Nat.add_0_r. iDestruct "Hl" as "(Hl & Ha & _)".
  rewrite Nat.add_succ_r Nat.add_0_r.
  iPoseProof ("Hstep" with "[] HP Ha") as "HP".
  { rewrite lookup_app_r; last lia. rewrite Nat.sub_diag. done. }
  iApply (IH with "Hl HP").
  iModIntro. iIntros (i y Hlook) "HP Hp".
  iApply ("Hstep" with "[] HP Hp"). iPureIntro.
  by apply lookup_app_l_Some.
Qed.

Lemma big_sepL2_from_big_sepL {Σ} {A B} (l : list (A * B)) (Φ : _ → _ → _ → iProp Σ) :
  ([∗ list] i ↦ x ∈ l, Φ i x.1 x.2) ⊢
  [∗ list] i ↦ x; y ∈ l.*1; l.*2, Φ i x y.
Proof.
  iIntros "Ha". iApply big_sepL2_alt. rewrite !fmap_length. iR.
  rewrite zip_fst_snd//.
Qed.
Lemma big_sepL2_from_zip {Σ} {A B} (l1 : list A) (l2 : list B) (Φ : _ → _ → _ → iProp Σ) :
  length l1 = length l2 →
  ([∗ list] i ↦ x ∈ zip l1 l2, Φ i x.1 x.2) ⊢
  [∗ list] i ↦ x; y ∈ l1; l2, Φ i x y.
Proof.
  iIntros (?) "Ha". iApply big_sepL2_alt. iR. done.
Qed.
(* hypothesis-directed version *)
Lemma big_sepL2_from_zip' {Σ} {A B} (l1 : list A) (l2 : list B) (Φ : _ → _ → iProp Σ) :
  length l1 = length l2 →
  ([∗ list] i ↦ x ∈ zip l1 l2, Φ i x) ⊢
  [∗ list] i ↦ x; y ∈ l1; l2, Φ i (x, y).
Proof.
  iIntros (?) "Ha". iApply big_sepL2_alt. iR. setoid_rewrite <-surjective_pairing. done.
Qed.
Lemma big_sepL2_to_zip {Σ} {A B} (l1 : list A) (l2 : list B) (Φ : _ → _ → _ → iProp Σ) :
  ([∗ list] i ↦ x; y ∈ l1; l2, Φ i x y) ⊢
  [∗ list] i ↦ x ∈ zip l1 l2, Φ i x.1 x.2.
Proof.
  rewrite big_sepL2_alt. iIntros "(_ & $)".
Qed.
(* goal-directed version *)
Lemma big_sepL2_to_zip' {Σ} {A B} (l1 : list A) (l2 : list B) (Φ : _ → _ → iProp Σ) :
  ([∗ list] i ↦ x; y ∈ l1; l2, Φ i (x, y)) ⊢
  [∗ list] i ↦ x ∈ zip l1 l2, Φ i x.
Proof.
  rewrite big_sepL2_alt. iIntros "(_ & Ha)".
  setoid_rewrite <-surjective_pairing. done.
Qed.

Local Lemma big_sepL2_later' {Σ} {A B} (l1 : list A) (l2 : list B) (Φ : _ → _ → _ → iProp Σ) n :
  length l1 = length l2 →
  ▷ ([∗ list] i ↦ x; y ∈ l1; l2, Φ (i + n) x y) ⊣⊢ [∗ list] i ↦ x; y ∈ l1; l2, ▷ Φ (i + n) x y.
Proof.
  intros Hlen. induction l1 as [ | x l1 IH] in l2, Hlen, n |-*; simpl.
  { destruct l2; simpl; last done. iSplit; iIntros "_"; done. }
  destruct l2 as [ | y l2]; first done.
  simpl in *. iSplit.
  - iIntros "(Ha & Hb)". iFrame.
    setoid_rewrite <-Nat.add_succ_r. rewrite -IH; last lia. done.
  - iIntros "(Ha & Hb)". setoid_rewrite <-Nat.add_succ_r.
    rewrite -IH; last lia. iNext. iFrame.
Qed.
Lemma big_sepL2_later {Σ} {A B} (l1 : list A) (l2 : list B) (Φ : _ → _ → _ → iProp Σ) :
  length l1 = length l2 →
  ▷ ([∗ list] i ↦ x; y ∈ l1; l2, Φ i x y) ⊣⊢ [∗ list] i ↦ x; y ∈ l1; l2, ▷ Φ i x y.
Proof.
  specialize (big_sepL2_later' l1 l2 Φ 0). setoid_rewrite Nat.add_0_r. done.
Qed.

Lemma big_sepL2_exists_r {Σ} {A B C} l1 l2 (Φ : nat → A → B → C → iProp Σ):
  ([∗ list] i ↦ x; y ∈ l1; l2, ∃ z, Φ i x y z) ⊢ ∃ l3, ⌜length l2 = length l3⌝ ∗ ([∗ list] i ↦ x; y ∈ l1; zip l2 l3, Φ i x y.1 y.2).
Proof.
  iIntros "Ha". iPoseProof (big_sepL2_length with "Ha") as "%Hlen".
  rewrite big_sepL2_to_zip.
  rewrite big_sepL_exists. iDestruct "Ha" as "(%l3 & Ha)".
  iPoseProof (big_sepL2_length with "Ha") as "%Hlen2".
  rewrite zip_with_length in Hlen2.
  rewrite big_sepL2_to_zip.
  rewrite zip_assoc_l big_sepL_fmap.
  iExists l3. iSplitR. { iPureIntro. lia. }
  iApply (big_sepL2_from_zip). { rewrite zip_with_length. lia. }
  iApply (big_sepL_impl with "Ha").
  iModIntro. iIntros (? [? [? ?]] ?); simpl. eauto.
Qed.

Lemma big_sepL_extend_l {Σ} {A B} (l' : list B) (l : list A) Φ :
  length l' = length l →
  ([∗ list] i ↦ x ∈ l, Φ i x) ⊢@{iProp Σ} ([∗ list] i ↦ y; x ∈ l'; l, Φ i x).
Proof.
  iIntros (?) "Ha". iApply big_sepL2_const_sepL_r. iFrame. done.
Qed.
Lemma big_sepL_extend_r {Σ} {A B} (l' : list B) (l : list A) Φ :
  length l' = length l →
  ([∗ list] i ↦ x ∈ l, Φ i x) ⊢@{iProp Σ} ([∗ list] i ↦ x; y ∈ l; l', Φ i x).
Proof.
  iIntros (?) "Ha". iApply big_sepL2_const_sepL_l. iFrame. done.
Qed.
Lemma big_sepL2_elim_l {Σ} {A B} (l' : list B) (l : list A) Φ :
  ([∗ list] i ↦ y; x ∈ l'; l, Φ i x) ⊢@{iProp Σ} ([∗ list] i ↦ x ∈ l, Φ i x).
Proof.
  iIntros "Ha". rewrite big_sepL2_const_sepL_r. iDestruct "Ha" as "(_ & $)".
Qed.
Lemma big_sepL2_elim_r {Σ} {A B} (l' : list B) (l : list A) Φ :
  ([∗ list] i ↦ x; y ∈ l; l', Φ i x) ⊢@{iProp Σ} ([∗ list] i ↦ x ∈ l, Φ i x).
Proof.
  iIntros "Ha". rewrite big_sepL2_const_sepL_l. iDestruct "Ha" as "(_ & $)".
Qed.
Lemma big_sepL2_sep_1 {Σ} {A B} (l1 : list A) (l2 : list B) Φ Ψ :
  ⊢@{iProp Σ}
  ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) -∗
  ([∗ list] k↦y1;y2 ∈ l1;l2, Ψ k y1 y2) -∗
  ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2 ∗ Ψ k y1 y2).
Proof. iIntros "Ha Hb". iApply big_sepL2_sep. iFrame. Qed.

(** ** General Iris/BI things *)
Lemma sep_ne_proper {Σ} (A : Prop) (B C : iProp Σ) n :
  (A → B ≡{n}≡ C) →
  (⌜A⌝ ∗ B)%I ≡{n}≡ (⌜A⌝ ∗ C)%I.
Proof.
  (* TODO can we prove this without unsealing? *)
  intros Heq.
  uPred.unseal.
  split.
  intros n' x ? Hv. split.
  - intros (x1 & x2 & Heqa & HA & HB).
    rewrite Heqa. specialize (Heq HA).
    exists x1, x2. split; first done. split; first done. apply Heq; [done | | done].
    rewrite Heqa in Hv. by apply cmra_validN_op_r in Hv.
  - intros (x1 & x2 & Heqa & HA & HC).
    rewrite Heqa. specialize (Heq HA).
    exists x1, x2. split; first done. split; first done. apply Heq; [done | | done].
    rewrite Heqa in Hv. by apply cmra_validN_op_r in Hv.
Qed.
Lemma sep_equiv_proper {Σ} (A : Prop) (B C : iProp Σ) :
  (A → B ≡ C) →
  (⌜A⌝ ∗ B)%I ≡ (⌜A⌝ ∗ C)%I.
Proof.
  intros Ha. apply equiv_dist => n.
  apply sep_ne_proper. intros HA.
  apply equiv_dist. by apply Ha.
Qed.

Lemma bi_exist_comm {Σ} (A B : Type) (Φ : A → B → iProp Σ) :
  (∃ a, ∃ b, Φ a b) ⊣⊢ (∃ b, ∃ a, Φ a b).
Proof.
  iSplit.
  - iIntros "(%a & %b & Ha)". iExists b, a. done.
  - iIntros "(%b & %a & Ha)". iExists a, b. done.
Qed.

Lemma bi_sep_persistent_pure_l {Σ} (P : Prop) (Q : iProp Σ) :
  (P → Persistent Q) →
  Persistent (⌜P⌝ ∗ Q).
Proof.
  intros Ha.
  rewrite /Persistent.
  iIntros "(%HP & HQ)". specialize (Ha HP).
  iDestruct "HQ" as "#HQ". iModIntro. iFrame "#%".
Qed.
Lemma bi_sep_persistent_pure_r {Σ} (P : Prop) (Q : iProp Σ) :
  (P → Persistent Q) →
  Persistent (Q ∗ ⌜P⌝).
Proof.
  rewrite bi.sep_comm. apply bi_sep_persistent_pure_l.
Qed.


(** ** Lifetime logic things *)
Section util.
Context `{!lftGS Σ lft_userE} `{!refinedcG Σ}.

(** We can shift [P] to [Q] while assuming the additional frame [R],
  but we also need to prove that we can go back. *)
Lemma bor_fupd_later_strong F1 F2 κ P Q R q :
  lftE ⊆ F1 →
  F2 ⊆ F1 →
  lft_ctx -∗
  R -∗
  ((R ∗ ▷ P) ={F2}▷=∗ (▷ Q) ∗ R) -∗
  (Q -∗ P) -∗
  &{κ} (P) -∗ q.[κ] ={F1}▷=∗ &{κ} Q ∗ q.[κ] ∗ R.
Proof.
  iIntros (??) "#LFT HR HPQ HQP Hbor Htok".
  iMod (bor_acc_cons with "LFT Hbor Htok") as "(HP & Hcl)"; first solve_ndisj.
  iApply step_fupd_fupd.
  iApply (step_fupd_subseteq _ F2); first done.
  iApply (step_fupd_wand with "[HPQ HP HR]").
  { iApply ("HPQ" with "[$HP $HR]"). }
  iIntros "[HQ $]".
  iApply ("Hcl" with "[HQP] HQ").
  iNext. iIntros "HQ !>!>". by iApply "HQP".
Qed.

Lemma bor_fupd_later F1 F2 κ P q :
  lftE ⊆ F1 →
  F2 ⊆ F1 →
  lft_ctx -∗
  &{κ} (|={F2}=> P) -∗ q.[κ] ={F1}▷=∗ &{κ} P ∗ q.[κ].
Proof.
  iIntros (??) "#LFT Hbor Htok".
  iMod (bor_acc_cons with "LFT Hbor Htok") as "(HP & Hcl)"; first solve_ndisj.
  iModIntro. iNext. iMod (fupd_mask_subseteq F2) as "Hcl_F"; first done.
  iMod "HP" as "HP". iMod "Hcl_F".
  iMod ("Hcl" $! P with "[] [$HP]") as "($ & $)"; last done.
  eauto.
Qed.

Lemma lft_tok_lb q q' κ κ' :
  q.[κ] -∗ q'.[κ'] -∗ ∃ q'', q''.[κ] ∗ q''.[κ'] ∗ (q''.[κ] -∗ q''.[κ'] -∗ q.[κ] ∗ q'.[κ']).
Proof.
  iIntros "Htok1 Htok2".
  iPoseProof (Fractional_fractional_le (λ q, q.[_])%I _ (Qp.min q q') with "Htok1") as "(Htok1 & Htok1_cl)".
  { apply Qp.le_min_l. }
  iPoseProof (Fractional_fractional_le (λ q, q.[_])%I _ (Qp.min q q') with "Htok2") as "(Htok2 & Htok2_cl)".
  { apply Qp.le_min_r. }
  iExists (q `min` q')%Qp. iFrame.
  iIntros "Htok1 Htok2". iPoseProof ("Htok1_cl" with "Htok1") as "$". iPoseProof ("Htok2_cl" with "Htok2") as "$".
Qed.

Lemma bor_get_persistent (P Q : iProp Σ) E κ q :
  ↑lftN ⊆ E →
  lft_ctx -∗
  (▷ P ={E}=∗ ▷ P ∗ □ Q) -∗
  &{κ}(P) -∗ q.[κ] ={E}=∗
  Q ∗ &{κ}(P) ∗ q.[κ].
Proof.
  iIntros (?) "#LFT HPQ Hb Htok". iMod (bor_acc_cons with "LFT Hb Htok") as "(Hb & Hcl)"; first done.
  iMod ("HPQ" with "Hb") as "(HP & #HQ)".
  iMod ("Hcl" $! P with "[] HP") as "($ & $)". { eauto. }
  iModIntro. done.
Qed.

(* Note: from RustHornBelt *)
Lemma bor_exists_tok {A} (Φ : A → iProp Σ) E κ q :
  ↑lftN ⊆ E → lft_ctx -∗ &{κ}(∃ x, Φ x) -∗ q.[κ] ={E}=∗ ∃ x, &{κ}(Φ x) ∗ q.[κ].
Proof.
  iIntros (?) "#LFT Bor κ". iMod (bor_acc_cons with "LFT Bor κ") as "[Φ Hclose]"; [done|].
  iMod (bi.later_exist_except_0 with "Φ") as (x) "Φ".
  iMod ("Hclose" with "[] Φ") as "[?$]"; [iIntros "!>?!>!>"|iModIntro]; by iExists x.
Qed.

Lemma bor_big_sepL' {X} F κ (Φ : nat → X → iProp Σ) (l : list X) k :
  lftE ⊆ F →
  lft_ctx -∗
  &{κ} ([∗ list] i ↦ x ∈ l, Φ (k + i) x) ={F}=∗
  [∗ list] i ↦ x ∈ l, &{κ} (Φ (k + i) x).
Proof.
  iIntros (?) "#LFT Hb".
  iInduction l as [ | x l] "IH" forall (k); simpl; first done.
  iMod (bor_sep with "LFT Hb") as "($ & Hb)"; first done.
  setoid_rewrite Nat.add_succ_r.
  iApply ("IH" $! (S k)). done.
Qed.
Lemma bor_big_sepL {X} F κ (Φ : nat → X → iProp Σ) (l : list X) :
  lftE ⊆ F →
  lft_ctx -∗
  &{κ} ([∗ list] i ↦ x ∈ l, Φ (i) x) ={F}=∗
  [∗ list] i ↦ x ∈ l, &{κ} (Φ (i) x).
Proof.
  apply (bor_big_sepL' _ _ _ _ 0).
Qed.

(* TODO maybe find a better place for this *)
Lemma maybe_use_credit F F1 P n (wl : bool) :
  F1 ⊆ F →
  (if wl then £ (S n) ∗ atime 1 else True) -∗
  (▷?wl |={F1}=> P) -∗
  |={F}=> ((if wl then £ n else True) ∗ (if wl then atime 1 else True) ∗ P).
Proof.
  iIntros (?) "Hcred HP".
  destruct wl.
  - iDestruct "Hcred" as "[[Hcred1 Hcred] Hat]".
    iApply (lc_fupd_add_later with "Hcred1"). iNext. iFrame.
    iApply (fupd_mask_mono with "HP"); done.
  - rewrite !left_id. iApply (fupd_mask_mono with "HP"); done.
Qed.

Lemma lc_fupd_maybe_elim_later E P wl :
  £ (Nat.b2n wl) -∗ (▷?wl P) ={E}=∗ P.
Proof.
  iIntros "Hcred HP".
  destruct wl.
  - iApply (lc_fupd_elim_later with "Hcred HP").
  - eauto.
Qed.

Lemma lc_split_le (m n : nat) :
  m ≤ n →
  £ n -∗ £ m ∗ £ (n - m).
Proof.
  intros ?. replace n with (m + (n - m))%nat by lia.
  replace (m + (n - m) - m)%nat with (n - m)%nat by lia.
  rewrite lc_split. auto.
Qed.

Lemma maybe_later_mono (P : iProp Σ) b : ▷?b P -∗ ▷ P.
Proof.
  iIntros "P". by iPoseProof (bi.laterN_le _ 1 with "P") as "P"; first (destruct b; simpl; lia).
Qed.
End util.


