From refinedrust Require Export type.
From iris Require Import options.
Set Default Proof Using "Type".

(** * Uninitialized memory *)

(** This file just contains the uninit type definition (without rules), because we need it for the struct ltype definition. 
  The rules are in [uninit.v]. *)

(** The [bytewise] type allows to give a predicate that needs to hold for all bytes
  owned by the type. *)
Section bytewise.
  Context `{!typeGS Σ}.
  Implicit Types P : mbyte → Prop.

  Program Definition bytewise (P : mbyte → Prop) (st : syn_type) : type unit := {|
    st_own π _ v :=
        (∃ ly, ⌜syn_type_has_layout st ly⌝ ∗
        ⌜v `has_layout_val` ly⌝ ∗
        ⌜Forall P v⌝)%I;
    st_has_op_type ot mt :=
      ∃ ly, syn_type_has_layout st ly ∧ ot = UntypedOp ly;
    st_syn_type := st;
  |}.
  Next Obligation.
    intros. simpl. iIntros "(%ly & ? & ? & ?)"; eauto.
  Qed.
  Next Obligation.
    intros ? st ot mt (ly & Hst & ->). done.
  Qed.
  Next Obligation.
    simpl. iIntros (P st ot mt ? π ? v (ly & ? & ->)) "(%ly' & % & % & %)".
    assert (ly' = ly) as ->. { by eapply syn_type_has_layout_inj. }
    destruct mt.
    - done.
    - iExists ly. done.
    - done.
  Qed.

  Global Instance bytewise_copy P st : Copyable (bytewise P st).
  Proof. apply _. Qed.

  Lemma bytewise_weaken v π P1 P2 st :
    (∀ b, P1 b → P2 b) →
    v ◁ᵥ{π} .@ bytewise P1 st -∗ v ◁ᵥ{π} .@ bytewise P2 st.
  Proof.
    iIntros (? (ly & Hst & Hly & ?)). iExists ly.
    iPureIntro. split_and!; [done.. | ].
    by eapply Forall_impl.
  Qed.

  Lemma bytewise_weaken_share l π κ P1 P2 st :
    (∀ b, P1 b → P2 b) →
    l ◁ₗ{π, κ} .@ bytewise P1 st -∗ l ◁ₗ{π, κ} .@ bytewise P2 st.
  Proof.
    iIntros (?) "(%v & %ly & Hb)". simpl.
    iDestruct "Hb" as "(Hb & (%ly' & Hc) & Hd)".
    iExists v, ly. iFrame. iNext. simpl.
    iDestruct "Hc" as "(% & % & %)".
    iPureIntro. eexists _. split_and!; [done.. | ].
    by eapply Forall_impl.
  Qed.


  (*
  Lemma split_bytewise v n π P ly:
    (n ≤ ly.(ly_size))%nat →
    v ◁ᵥ{π} .@ bytewise P ly -∗
      (take n v) ◁ᵥ{π} .@ bytewise P (ly_set_size ly n) ∗
      (drop n v) ◁ᵥ{π} .@ bytewise P (ly_offset ly n).
  Proof.
    iIntros (?[Hv HP]). iSplitL.
    - eapply Forall_take in HP; iSplitL; last done.
      iPureIntro. rewrite /has_layout_val in Hv.
      by rewrite /has_layout_val take_length min_l // Hv.
    - eapply Forall_drop in HP; iSplitL; last done.
      iPureIntro. by rewrite /has_layout_val drop_length Hv.
  Qed.
  (* the corresponding lemma for shared ownership does not seem provable currently: how should we split the fractured borrow?*)
  (* TODO: check if this is a fundamental limitation / why are fractured borrows not covariant in their predicate? *)

  Lemma merge_bytewise v1 v2 π P ly1 ly2:
    (ly1.(ly_size) ≤ ly2.(ly_size))%nat →
    (ly_align ly2 ≤ ly_align ly1)%nat →
    v1 ◁ᵥ{π} .@ bytewise P ly1 -∗
    v2 ◁ᵥ{π} .@ (bytewise P (ly_offset ly2 ly1.(ly_size))) -∗
    (v1 ++ v2) ◁ᵥ{π} .@ bytewise P ly2.
  Proof.
    iIntros (??) "(%Hv1 & %HP1) (%Hv2 & %HP2)".
    iSplitL; iPureIntro.
    - rewrite /has_layout_val app_length Hv1 Hv2.
      rewrite {2}/ly_size/=. lia.
    - by apply Forall_app.
  Qed.
  *)

  (*
     ltype Own: essentially l ↦ v st. Forall P v

     if we offset l, then we get:
      two ltype owns! one for the first part, one for the latter.
      should pass the type of the latter on to the continuation

      how do we make that compatible with ltypes?
      -> the predicate/type we give to the continuation should be a predicate on rvalues, fundamentally.
        (it should handle the addition of two integers which are not stored on the stack/heap, but are just temporary rvalues  without an address).
      so, have a ltype-own to type conversion?

      alternative: directly state the whole typing rule in terms of rvalue stuff, including the ownership of the p.
        in this case: the owned ptr rvalue.

      then to apply this rule in practice: need a subsumption rule for having
        l ◁ₗ[_, Owned] r @ ◁ ty and v ◁ᵥ (r, l) @ own ty
                                or rather v ◁ᵥ r @ own (r @ ty) ??
  *)

End bytewise.

Notation "bytewise< P , st >" := (bytewise P st)
  (only printing, format "'bytewise<' P ',' st '>'") : printing_sugar.

Global Typeclasses Opaque bytewise.

Notation uninit := (bytewise (λ _, True)).

Section uninit.
  Context `{!typeGS Σ}.

  Lemma uninit_own_spec π v st :
    (v ◁ᵥ{π} .@ uninit st)%I ≡ (∃ ly, ⌜syn_type_has_layout st ly⌝ ∗ ⌜v `has_layout_val` ly⌝)%I.
  Proof.
    rewrite /ty_own_val/=; iSplit.
    - iIntros "(%ly & ? & ? & ?)"; iExists ly. iFrame.
    - iIntros "(%ly & ? & ?)"; iExists ly. iFrame.
      rewrite Forall_forall. done.
  Qed.
End uninit.

Notation "uninit< st >" := (uninit st) (only printing, format "'uninit<' st '>'") : printing_sugar.
