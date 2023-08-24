From refinedrust Require Export type.
Set Default Proof Using "Type".

Open Scope Z_scope.

Section int.
  Context `{!typeGS Σ}.

  (* Separate definition such that we can make it typeclasses opaque later. *)
  Program Definition int (it : int_type) : type Z := {|
    st_own tid z v := ⌜val_to_Z v it = Some z⌝ ∗ ⌜ly_size it ≤ max_int isize_t⌝;
    st_has_op_type ot mt := is_int_ot ot it;
    st_syn_type := IntSynType it;
  |}%I.
  Next Obligation.
    iIntros (it π z v [Hv ?]). iPureIntro.
    exists (it_layout it). split; last by eapply val_to_Z_length.
    by apply syn_type_has_layout_int.
  Qed.
  Next Obligation.
    intros it ot mt Hot. simpl. rewrite (is_int_ot_layout _ _ Hot).
    destruct ot; try done. all: destruct Hot as [ ]; by apply syn_type_has_layout_int.
  Qed.
  Next Obligation.
    simpl. iIntros (it ot mt st π r v Hot).
    destruct mt.
    - eauto.
    - iPureIntro. intros [Hv ?]. destruct ot; simpl in *; try done. subst.
      unfold mem_cast. erewrite val_to_bytes_id; last done. done.
    - iApply (mem_cast_compat_int (λ v, _)); first done.
      iIntros "[% %]". eauto.
  Qed.

  Lemma ty_own_int_in_range l π n it : l ◁ᵥ{π} n @ int it -∗ ⌜n ∈ it⌝.
  Proof. iIntros "[%Hl _]". iPureIntro. by eapply val_to_Z_in_range. Qed.

  (* We only get this under a later for sharing:
     the refinement predicate needs to sit under a later for the whole sharing business.
     TODO is that really the case?
  *)
  Lemma ty_shr_int_in_range l π κ n it : l ◁ₗ{π, κ} n @ int it -∗ ▷ ⌜n ∈ it⌝.
  Proof.
    iIntros "(%v & (%ly & Hv & (Ha & _) & Halg & Hl))" => /=. iNext. iDestruct "Ha" as "%Hn".
    iPureIntro. by eapply val_to_Z_in_range.
  Qed.

  Global Instance int_copyable it : Copyable (int it).
  Proof. apply _. Qed.

  Global Instance int_timeless l z it π:
    Timeless (l ◁ᵥ{π} z @ int it)%I.
  Proof. apply _. Qed.

End int.

Global Hint Unfold int : ty_unfold.
Global Typeclasses Opaque int.
Notation "int< it >" := (int it) (only printing, format "'int<' it '>'") : printing_sugar.

(** This represents the Rust bool type, which just has valid bit patterns 0x01 and 0x00 *)
Section boolean.
  Context `{!typeGS Σ}.

  (* Separate definition such that we can make it typeclasses opaque later. *)
  Program Definition bool_t : type bool := {|
    st_own tid b v := ⌜val_to_bool v = Some b⌝;
    st_syn_type := BoolSynType;
    st_has_op_type ot mt := is_bool_ot ot;
  |}%I.
  Next Obligation.
    iIntros (π z v Hv). iExists u8. iPureIntro. split; first done.
    unfold has_layout_val. erewrite val_to_bool_length; done.
  Qed.
  Next Obligation.
    intros ot mt Hot. simpl in *. rewrite (is_bool_ot_layout _ Hot). done.
  Qed.
  Next Obligation.
    simpl. iIntros (ot mt st π r v Hot).
    destruct mt.
    - eauto.
    - destruct ot; simpl in *; try done.
      { iPureIntro. intros Hv. unfold mem_cast.
      rewrite Hv. by erewrite val_to_bytes_id_bool. }
      subst; eauto.
    - iApply (mem_cast_compat_bool (λ v, _)); first done. eauto.
  Qed.

  Lemma bool_own_val_eq v π b :
    (v ◁ᵥ{π} b @ bool_t)%I ≡ ⌜val_to_bool v = Some b⌝%I.
  Proof. done. Qed.

  Global Instance bool_timeless π l b:
    Timeless (l ◁ᵥ{π} b @ bool_t)%I.
  Proof. apply _. Qed.

  Global Instance bool_copy : Copyable bool_t.
  Proof. apply _. Qed.
End boolean.

Global Hint Unfold bool_t : ty_unfold.
Global Typeclasses Opaque bool_t.
Notation "'bool'" := (bool_t) (only printing, format "'bool'") : printing_sugar.

