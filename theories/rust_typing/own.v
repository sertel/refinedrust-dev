(* TODO: something breaks with the lft logic notations as soon as we import this *)
(*From refinedc.lang Require Import rust.*)
From refinedrust Require Export type references.

(**
NOTE: we should never borrow an [own] mutably. That breaks refinement.
  Instead, should unfold to a [box] before.

  Assuming inner : rtype

  [r @ box inner] unfold to [∃ l. l @ own (r @ inner)]
  [l @ own (r @ inner)] folds to [r @ box inner]


   in terms of ltype:
      ltype_eq (own_ltype (◁ rty)) (◁ own (ty_of_rty rty))
      ltype_eq (box_ltype (◁ rty)) (◁ box rty)

    we cannot formulate the correspondence between box and own in terms of ltype_eq,
      because the refinements are different.

    So what is the right way of formulating this?


    For now, this question isn't so important: we are interested in own mainly for unsafe code¸
      where we might need to deal with strong updates (uninit etc)
    Well, we also need that for box. Moving out is allowed for boxes. just changing the refinement type is not.
    So have some dummy inner type that takes any refinement if we move things out.



   -------------------------------------


    What is the correct notion of owned ptrs? 
      1. Separate from that: need box, which also carries the permission to deallocate and is refined by just the inner refinement
      2. For owning stack values, we have (by default) the Owned ltype variant.

      What do we need owned pointers for beyond that?  (in a safe Rust program)
      - in lambda rust: need some notion that we get when we split a Box into two Boxes. 
        BUT: that is only required due to splitting. We just don't need the same notion of owned ptr, at least for the safe fragment. (for the unsafe part, we will need something similar).
      - ??

      result: we don't need them for specifications in principle

      It could still be useful to have them as "administrative" types for the typing rules to streamline the notions of ltypes and rtypes. 
      Instead of working with owned ltypes in the typing rules to reason about stack locations, we could have a owned ptr type.
        + subsumption rules that allow us to convert to the ltype under the right conditions.


      Guiding principle in the design of that: it should also work when, e.g., operating under a mutable reference:
      - assume we have l ◁[Owned] &mut (t2rt (uninit P ly)). 
        We do *l +ₗ n, this unfolds to  ?. 
        Rather &mut ( *l +ₗ n)?

        -> we just borrow some part of the sep. conj. and leave the rest there, effectively. 
        We can still access one part of that, if we want.
        (not permitted in safe Rust but the semantic model allows that of course)

        But: how would the typing rule for that look formally?

      -> but point: it should not be the case that a single binop application can do a reborrow. both on the MIR side and the Caesium side. we should need an explicit reborrow of the offset address, and that should do the whole thing.
        for the binop application itself, we should be able to assume full ownership of the location of the mut ref., since we are currently in the process of opening the borrow.  
        then, we should get the new ownership and the remaining ownership. the remaining ownership stays in the mutable borrow, but the new ownership that is passed to the continuation should be subject to reborrowing. (that should be stated in the continuation).


      Plan for owned pointers: 
      - we have the box type, well, for Rust boxes. 
      - we have the own_ptr type for an owned location, refined by the location.
          rvalue ownership of this unfolds to Owned ltype ownership of the nested type.

 *)



  (* 
Section own_ptr.
  Context `{typeGS Σ}.

  (** Owned ptrs are very similar to RefinedC's owned pointers:
    they do not reflect the refinement of the inner type to the outside in order to allow
    for strong updates to the inner types' refinement.
    Instead, they are refined by locations.
   *)

  Program Definition own_ptr_type (ty : type) (l' : loc) : type := {|
    ty_own_val tid v := (⌜v = l'⌝ ∗ ⌜l' `has_layout_loc` ty.(ty_layout)⌝ ∗ ▷ (l' ↦: (ty.(ty_own_val) tid)))%I;
    ty_layout := void*;
    ty_shr κ tid l :=
      (&frac{κ}(λ q', l ↦{q'} l') ∗
            □ (∀ F q, ⌜↑shrN ∪ ↑lftN ⊆ F⌝ -∗ q.[κ] ={F}[F∖↑shrN]▷=∗
                            ty.(ty_shr) κ tid l' ∗ q.[κ]))%I;
    ty_drop := ty.(ty_drop);
    ty_depth := 1 + ty.(ty_depth);
  |}.
  Next Obligation.
    iIntros (? l' ? v) "(-> & %Hly & Hown)".
    iPureIntro. done.
  Qed.
  Next Obligation.
    iIntros (ty l' E κ l tid q ?) "#LFT %Hly Hb Htok".
    iMod (bor_exists with "LFT Hb") as "(%v & Hb)"; first solve_ndisj.
    iMod (bor_sep with "LFT Hb") as "[Hl Hb]"; first solve_ndisj.
    iMod (bor_sep with "LFT Hb") as "[Heq Hb]"; first solve_ndisj.
    iMod (bor_sep with "LFT Hb") as "[Hly Hb]"; first solve_ndisj.

    iMod (bor_persistent with "LFT Heq Htok") as "[>-> Htok]"; first solve_ndisj.
    iMod (bor_persistent with "LFT Hly Htok") as "[>%Hly' Htok]"; first solve_ndisj.

    iFrame.
    iMod (bor_fracture (λ q, l ↦{q} l')%I with "LFT Hl") as "$"; first solve_ndisj.
    rewrite bor_unfold_idx.
    iDestruct "Hb" as (i) "(#Hpb&Hpbown)".
    iMod (inv_alloc shrN _ (idx_bor_own 1 i ∨ ty_shr ty κ tid l')%I
          with "[Hpbown]") as "#Hinv"; first by eauto.
    iIntros "!> !> * % Htok".
    iMod (inv_acc with "Hinv") as "[INV Hclose]"; first solve_ndisj.
    iDestruct "INV" as "[>Hbtok|#Hshr]".
    - iMod (bor_later_tok with "LFT [Hbtok] Htok") as "Hdelay"; first solve_ndisj.
      { rewrite bor_unfold_idx. eauto. }
      iModIntro. iNext. iMod "Hdelay" as "[Hb Htok]".
      iMod (ty.(ty_share) with "LFT [//] Hb Htok") as "[#$ $]"; first solve_ndisj.
      iApply "Hclose". auto.
    - iMod fupd_mask_subseteq as "Hclose'"; first solve_ndisj. iModIntro.
      iNext. iMod "Hclose'" as "_". iMod ("Hclose" with "[]") as "_"; by eauto.
  Qed.
  Next Obligation.
    iIntros (ty l' ?? tid l) "#Hincl (Hfrac & #Hvs)".
    iSplit; first by iApply (frac_bor_shorten with "[]"). iIntros "!> *% Htok".
    iApply (step_fupd_mask_mono F _ (F∖↑shrN)); [solve_ndisj..|].
    iMod (lft_incl_acc with "Hincl Htok") as (q') "[Htok Hclose]"; first solve_ndisj.
    iMod ("Hvs" with "[%] Htok") as "Hvs'"; first solve_ndisj. iModIntro. iNext.
    iMod "Hvs'" as "[Hshr Htok]". iMod ("Hclose" with "Htok") as "$".
    by iApply (ty.(ty_shr_mono) with "Hincl").
  Qed.
  Next Obligation.
    iIntros (????) "(_ & ? & H)".
    simpl. iModIntro. iNext. iDestruct "H" as "(%v' & ? & Hinner)".
    iModIntro. iApply (ty.(ty_own_drop) with "Hinner").
  Qed.

  Program Definition own_ptr (ty : type) : rtype := {|
    rty_type := loc;
    rty := own_ptr_type ty;
    rty_layout := void*;
    rty_depth := 1 + ty.(ty_depth);
  |}.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.

  Global Instance own_ptr_wf `{!TyWf ty} : RTyWf (own_ptr ty) :=
    λ r, {| ty_lfts := ty.(ty_lfts); ty_wf_E := ty.(ty_wf_E) |}.
End own_ptr.

Section own_lty.
  Context `{typeGS Σ} (inner_rty : Type) (inner : ltype inner_rty)
    (inner_core : ltype inner_rty)
    `{ghost_varG Σ loc}.
  Implicit Types (κ : lft) (γ : gname) (k : bor_kind).

  (* Even though owned pointers itself allow strong updates just fine,
    since we might nest mutable references on the outside, we still need to have
    a "core" inner type.
   *)
  Program Definition own_ltype : ltype loc := {|
    ltype_own k π l' l :=
      match k with
      | Owned =>
          ⌜l `has_layout_loc` void*⌝ ∗ ⌜l = l'⌝ ∗
          ∃ (l' : loc) r, l ↦ l' ∗ ▷ inner.(ltype_own) Owned π r l'
      | Uniq κ' γ => ⌜l `has_layout_loc` ref_layout⌝ ∗ ⌜l = l'⌝ ∗
            gvar_obs γ l ∗
            &pin{κ'}
              [∃ (l' : loc) (r : loc) r',
                gvar_auth γ r ∗ l ↦ l' ∗
                inner_core.(ltype_own) Owned π r' l']
              (∃ (l' : loc) (r : loc) r',
                gvar_auth γ r ∗ l ↦ l' ∗
                inner.(ltype_own) Owned π r' l')
      | Shared κ =>
        (* TODO: have layout requirements ? *)
        (*⌜l `has_layout_loc` ref_layout⌝ ∗*)
        ⌜l = l'⌝ ∗
        (∃ (li : loc) r, &frac{κ}(λ q', l ↦{q'} li) ∗
         □ ∀ F q, ⌜↑shrN ∪ ↑lftN ⊆ F⌝ -∗ q.[κ] ={F}[F∖↑shrN]▷=∗
         inner.(ltype_own) (Shared κ) π r li ∗ q.[κ])%I
      end%I;
    ltype_depth := 1 + inner.(ltype_depth);
    |}.
  Next Obligation.
    intros κ κ' π l' l. iIntros "#Hincl".
    iIntros "(<- & (%li & %r & Hf & #Hb))".
    iSplitR; first done.
    iExists li, r.
    iSplit; first by iApply (frac_bor_shorten with "[]").
    iIntros "!> * % Htok".
    iMod (lft_incl_acc with "Hincl Htok") as (q') "[Htok Hclose]"; first solve_ndisj.
    iMod ("Hb" with "[%] Htok") as "Hvs"; first solve_ndisj. iModIntro. iNext.
    iMod "Hvs" as "[Hshr Htok]". iMod ("Hclose" with "Htok") as "$".
    iModIntro. by iApply (ltype_shr_mono with "Hincl").
  Qed.
End own_lty.

Section ltype_agree.
  Context `{typeGS Σ}
    (rt : rtype)
    `{ghost_varG Σ rt.(rty_type)}
    `{ghost_varG Σ loc}.

  (* TODO *)
  (*
  Lemma own_unfold κ :
    ⊢ ltype_eq _ (own_ltype _ (◁ rt) (◁ rt)) (◁ (own_ptr ty)).
  Proof.
    iIntros "!#" (k π [r γ] l); iSplit; simpl.
    - destruct k; simpl.
      + iIntros ">[%Hly (%l' & Hl & %Hly' & Hobs & Hbor)]".
        iSplitR; first done. iModIntro. eauto with iFrame.
      + iIntros ">(%li & Hb & Hdel)". eauto with iFrame.
      + iIntros ">(%Hly & Hobs & Hb)".
        iSplitR; first done. iFrame "Hobs".
        iMod (pinned_bor_fold with "Hb") as "Hb".
        iApply (bor_iff with "[] Hb").
        iNext. iModIntro. iSplit.
        * iIntros "(%l' & %r' & Hauth & Hl & %Hly'' & Hobs & Hbor)".
          iExists r'. iFrame. destruct r' as [r' γ''].
          eauto with iFrame.
        * iIntros "(%p & Hauth & (%v & Hl & Hv))".
          destruct p as [r' γ''].
          iDestruct "Hv" as "(%l' & -> & %Hly' & Hobs & Hbor)".
          eauto with iFrame.
    - destruct k; simpl.
      + iIntros ">[%Hly (%v & Hl & %l' & -> & %Hly' & Hobs & Hbor)]".
        iSplitR; first done. eauto with iFrame.
      + iIntros ">(%li & Hb & Hdel)". eauto with iFrame.
      + iIntros ">(%Hly & Hobs & Hb)".
        iSplitR; first done. iFrame "Hobs".
        iApply pinned_bor_unfold.
        iApply (bor_iff with "[] Hb").
        iNext. iModIntro. iSplit.
        * iIntros "(%p & Hauth & (%v & Hl & Hv))".
          destruct p as [r' γ''].
          iDestruct "Hv" as "(%l' & -> & %Hly' & Hobs & Hbor)".
          eauto with iFrame.
        * iIntros "(%l' & %r' & Hauth & Hl & %Hly'' & Hobs & Hbor)".
          iExists r'. iFrame. destruct r' as [r' γ''].
          eauto with iFrame.
  Qed.
   *)
End ltype_agree.

   *)
