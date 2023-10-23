From caesium Require Import base.

(** Representation of a type layout (byte size and alignment constraint). *)

Record layout :=
  Layout {
    ly_size : nat;
    ly_align_log : nat;
  }.

Definition sizeof   (ly : layout) : nat := ly.(ly_size).
Definition ly_align (ly : layout) : nat := 2 ^ ly.(ly_align_log).

Global Instance layout_dec_eq : EqDecision layout.
Proof. solve_decision. Defined.

Global Instance layout_inhabited : Inhabited layout :=
  populate (Layout 0 0).

Global Instance layout_countable : Countable layout.
Proof.
  refine (inj_countable'
    (λ ly, (ly.(ly_size), ly.(ly_align_log)))
    (λ '(sz, a), Layout sz a) _); by intros [].
Qed.

Global Instance layout_le : SqSubsetEq layout := λ ly1 ly2,
  (ly1.(ly_size) ≤ ly2.(ly_size))%nat ∧
  (ly1.(ly_align_log) ≤ ly2.(ly_align_log))%nat.

Global Instance layout_le_po : PreOrder layout_le.
Proof.
  split => ?; rewrite /layout_le => *; repeat case_bool_decide => //; lia.
Qed.

Definition ly_offset (ly : layout) (n : nat) : layout := {|
  ly_size := ly.(ly_size) - n;
  (* Sadly we need to have the second argument to factor2 as we want
  that if l is aligned to x, then l + n * x is aligned to x for all n
  including 0. *)
  ly_align_log := ly.(ly_align_log) `min` factor2 n ly.(ly_align_log)
|}.

Definition ly_set_size (ly : layout) (n : nat) : layout := {|
  ly_size := n;
  ly_align_log := ly.(ly_align_log)
|}.

Definition ly_mult (ly : layout) (n : nat) : layout := {|
  ly_size := ly.(ly_size) * n;
  ly_align_log := ly.(ly_align_log)
|}.

Definition ly_with_align (sz : nat) (align : nat) : layout := {|
  ly_size := sz;
  ly_align_log := factor2 align 0
|}.

Definition layout_wf (ly : layout) : Prop := (ly_align ly | ly.(ly_size)).

Lemma layout_wf_mod (ly : layout) :
  ly.(ly_size) `mod` ly_align ly = 0 → layout_wf ly.
Proof.
  move => ?. apply Z.mod_divide => //. have ->: 0 = O by [].
  move => /Nat2Z.inj/Nat.pow_nonzero. lia.
Qed.

Global Instance layout_wf_dec ly : Decision (layout_wf ly).
Proof.
  rewrite /layout_wf. apply Znumtheory.Zdivide_dec.
Qed.

Class LayoutWf (ly : layout) : Prop := layout_wf_wf : layout_wf ly.

(* Class required because the combinators of layout are made typeclass opaque
   later, so TCEq does not work. *)
Class LayoutEq (ly1 ly2 : layout) : Prop := layout_eq : ly1 = ly2.

Arguments ly_size : simpl never.
Arguments sizeof _ /.
Arguments ly_align : simpl never.

Global Typeclasses Opaque layout_le ly_offset ly_set_size ly_mult ly_with_align.

Global Hint Extern 0 (LayoutWf _) => refine (layout_wf_mod _ _); done : typeclass_instances.
Global Hint Extern 0 (LayoutWf _) => unfold LayoutWf; done : typeclass_instances.
Global Hint Extern 0 (LayoutEq _ _) => exact: eq_refl : typeclass_instances.

(*** Notations for specific layouts *)
Definition void_layout : layout := {| ly_size := 0; ly_align_log := 0 |}.

Lemma void_layout_wf : layout_wf void_layout.
Proof.
  rewrite /layout_wf /void_layout. apply Z.divide_0_r.
Qed.

Definition mk_array_layout := ly_mult.
Global Typeclasses Opaque mk_array_layout.

Lemma array_layout_wf ly len :
  layout_wf ly →
  layout_wf (mk_array_layout ly len).
Proof.
  rewrite /layout_wf /mk_array_layout /ly_mult /ly_align /=.
  rewrite {2}/ly_size.
  intros Ha. etrans; first apply Ha.
  rewrite Nat2Z.inj_mul.
  by apply Z.divide_mul_l.
Qed.

Lemma ly_size_mk_array_layout (n : nat) ly :
  ly_size (mk_array_layout ly n) = (ly_size ly * n)%nat.
Proof.
  rewrite /mk_array_layout /ly_mult /ly_size //.
Qed.
Lemma ly_align_mk_array_layout ly n :
  ly_align (mk_array_layout ly n) = ly_align ly.
Proof. done. Qed.



(*** Lemmas about [layout] *)

Lemma ly_align_log_ly_align_eq_iff ly1 ly2:
  ly_align_log ly1 = ly_align_log ly2 ↔ ly_align ly1 = ly_align ly2.
Proof. rewrite /ly_align. split; first naive_solver. move => /Nat.pow_inj_r. lia. Qed.

Lemma ly_align_log_ly_align_le_iff ly1 ly2:
  (ly_align_log ly1 ≤ ly_align_log ly2 ↔ ly_align ly1 ≤ ly_align ly2)%nat.
Proof. rewrite /ly_align. apply: Nat.pow_le_mono_r_iff. lia. Qed.

Lemma ly_size_ly_with_align m n :
  ly_size (ly_with_align m n) = m.
Proof. done. Qed.

Lemma ly_align_ly_with_align m n :
  ly_align (ly_with_align m n) = keep_factor2 n 1.
Proof. rewrite /ly_with_align/keep_factor2/factor2. by destruct (factor2' n). Qed.

Lemma ly_align_ly_offset ly n :
  ly_align (ly_offset ly n) = (ly_align ly `min` keep_factor2 n (ly_align ly))%nat.
Proof.
  rewrite /ly_align/keep_factor2/=/factor2. destruct (factor2' n) as [n'|] => /=; last by rewrite !Nat.min_id.
  destruct (decide (ly_align_log ly ≤ n'))%nat;[rewrite !min_l|rewrite !min_r]; try lia;
    apply Nat.pow_le_mono_r; lia.
Qed.

Lemma ly_size_ly_set_size ly n:
  ly_size (ly_set_size ly n) = n.
Proof. done. Qed.

Lemma ly_align_ly_set_size ly n:
  ly_align (ly_set_size ly n) = ly_align ly.
Proof. done. Qed.


Lemma layout_wf_align_log_0 ly :
  ly_align_log ly = 0%nat → layout_wf ly.
Proof.
  intros Ha. rewrite /layout_wf/ly_align Ha/=.
  apply Z.divide_1_l.
Qed.

Lemma ly_size_ly_offset ly n :
  ly_size (ly_offset ly n) = (ly_size ly - n)%nat.
Proof.
  rewrite /ly_size /ly_offset. destruct ly; done.
Qed.
Lemma layout_wf_mono ly1 ly2 :
  (ly_align_log ly2 ≤ ly_align_log ly1)%nat →
  ly_size ly1 = ly_size ly2 →
  layout_wf ly1 → layout_wf ly2.
Proof.
  rewrite /layout_wf /ly_align. intros Hle Hsz Hdiv.
  rewrite -Hsz. eapply Z.divide_trans; last apply Hdiv.
  eapply Zdivide_nat_pow. lia.
Qed.
