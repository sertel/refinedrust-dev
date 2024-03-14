From caesium Require Import lang notation.
From refinedrust Require Import typing.

Lemma list_lookup_insert_Some' {A} (l : list A) i x j y :
  <[i:=x]>l !! j = Some y ↔
    (i = j → x = y ∧ (j < length l)%nat) ∧ (i ≠ j → l !! j = Some y).
Proof. rewrite list_lookup_insert_Some. destruct (decide (i = j)); naive_solver. Qed.

Lemma list_eq_singleton {A} (l : list A) x:
  l = [x] ↔ (length l ≤ 1)%nat ∧ l !! 0%nat = Some x.
Proof.
  split.
  - move => ->. naive_solver.
  - move => [??]. destruct l as [|? [|]]; naive_solver lia.
Qed.

Global Instance simpl_lookup_total_insert_eq {A} `{!Inhabited A} (l : list A) i j x x' `{!CanSolve (i = j)} `{!CanSolve (j < length l)%nat}:
  SimplBothRel (=) (<[i := x']> l !!! j) (x) (x = x').
Proof.
  unfold SimplBothRel, CanSolve in *; subst.
  rewrite list_lookup_total_insert; naive_solver.
Qed.

#[universes(polymorphic)]
Definition extract_val {rt} (r : place_rfn rt) := if r is #r then Some r else None.

Section project_vec_els.
  Context {rt : Type}.
  Set Universe Polymorphism.

  Definition project_vec_els (len : nat) (els : list (place_rfn (option (place_rfn rt))))
    : list (place_rfn rt) :=
    (λ x, default (@PlaceGhost rt inhabitant) (extract_val x ≫= id)) <$> (take len els).

  Lemma project_vec_els_length len els :
    length (project_vec_els len els) = (len `min` length els)%nat.
  Proof. by rewrite /project_vec_els fmap_length take_length. Qed.

  Lemma project_vec_els_insert_lt (len : nat) (i : nat) x els:
    (i < len)%nat →
    project_vec_els len (<[i:=x]> els) =
       <[i:=default (@PlaceGhost rt inhabitant) (extract_val x ≫= id)]>
         (project_vec_els len els).
  Proof.
    rewrite {1}/project_vec_els => ?. by rewrite take_insert_lt // list_fmap_insert.
  Qed.
  Lemma project_vec_els_insert_ge (len : nat) (i : nat) x els:
    (len ≤ i)%nat →
    project_vec_els len (<[i:=x]> els) = project_vec_els len els.
  Proof. rewrite {1}/project_vec_els => ?. by rewrite take_insert. Qed.

  Lemma project_vec_els_lookup_mono (len : nat) (i : nat) els len' els':
    (i < len `min` len')%nat →
    els !! i = els' !! i →
    project_vec_els len els !! i = project_vec_els len' els' !! i.
  Proof.
    move => ? Hels. rewrite /project_vec_els !list_lookup_fmap. f_equal.
    rewrite !lookup_take //; lia.
  Qed.

  Lemma project_vec_els_take len els len':
    take len' (project_vec_els len els) = project_vec_els (len' `min` len) els.
  Proof. rewrite /project_vec_els. by rewrite !fmap_take take_take. Qed.
  Lemma project_vec_els_take_r len els :
    project_vec_els len els = project_vec_els len (take len els).
  Proof. rewrite /project_vec_els. f_equal. rewrite take_take. f_equal. lia. Qed.
  Lemma project_vec_els_drop len els len':
    drop len' (project_vec_els len els) = project_vec_els (len - len') (drop len' els).
  Proof. rewrite /project_vec_els. by rewrite -!fmap_drop skipn_firstn_comm. Qed.

  Lemma project_vec_els_lookup (len i : nat) els x :
    (i < len)%nat →
    els !! i = Some #(Some x) →
    project_vec_els len els !! i = Some x.
  Proof.
    intros Hi Hlook. rewrite /project_vec_els.
    simpl.
    rewrite list_lookup_fmap.
    rewrite lookup_take; last lia.
    rewrite Hlook. done.
  Qed.

  Lemma project_vec_els_length' xs x2 len :
    PlaceIn <$> xs = project_vec_els len x2 → length xs ≤ min len (length x2).
  Proof.
    intros Ha.
    assert (length (PlaceIn <$> xs) = length (project_vec_els len x2)) as Hlen.
    { rewrite Ha. done. }
    rewrite fmap_length project_vec_els_length in Hlen.
    lia.
  Qed.
End project_vec_els.

Global Typeclasses Opaque project_vec_els.
Global Opaque project_vec_els.

Global Hint Rewrite @project_vec_els_length : lithium_rewrite.
