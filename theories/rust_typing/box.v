From caesium Require Import derived.
From refinedrust Require Export base type.
From refinedrust Require Import programs uninit ltypes ltype_rules.

(** * Box *)

Section box.
  Context `{typeGS Σ} {rt} `{Inhabited rt} (inner : type rt).

  Program Definition box : type (place_rfn rt) := {|
    ty_sidecond := True;
    ty_own_val π r v :=
      ∃ (l : loc) (ly : layout), ⌜v = l⌝ ∗ ⌜syn_type_has_layout inner.(ty_syn_type) ly⌝ ∗ ⌜l `has_layout_loc` ly⌝ ∗
        loc_in_bounds l 0 ly.(ly_size) ∗
        inner.(ty_sidecond) ∗
        (* No later here over the freeable. I don't know how to make the unfolding equation work with one. *)
        (freeable_nz l ly.(ly_size) 1 HeapAlloc) ∗
        £ num_cred ∗ atime 1 ∗
        ∃ (ri : rt), place_rfn_interp_owned r ri ∗
        (* this needs to match up with the corresponding later/fupd in the OfTyLtype to get the unfolding equation *)
        ▷ |={lftE}=> ∃ v' : val, l ↦ v' ∗ inner.(ty_own_val) π ri v';
    _ty_has_op_type ot mt := is_ptr_ot ot;
    ty_syn_type := PtrSynType;

    ty_shr κ tid r l :=
      (∃ (li : loc) (ly : layout) (ri : rt), place_rfn_interp_shared r ri ∗
        ⌜l `has_layout_loc` void*⌝ ∗
        ⌜use_layout_alg inner.(ty_syn_type) = Some ly⌝ ∗
        ⌜li `has_layout_loc` ly⌝ ∗
        inner.(ty_sidecond) ∗
        loc_in_bounds l 0 void*.(ly_size) ∗
        (* also need this for the inner location to get the right unfolding equations *)
        loc_in_bounds li 0 ly.(ly_size) ∗
        &frac{κ}(λ q', l ↦{q'} li) ∗
        (* later for contractiveness *)
        ▷ □ |={lftE}=> inner.(ty_shr) κ tid ri li)%I;
    ty_ghost_drop π r :=
      ∃ ri, place_rfn_interp_owned r ri ∗ inner.(ty_ghost_drop) π ri;

    ty_lfts := inner.(ty_lfts);
    ty_wf_E := inner.(ty_wf_E);
  |}%I.
  Next Obligation.
    iIntros (π v r) "(%l & %ly & -> & ? & ? & _)". eauto with iFrame.
  Qed.
  Next Obligation.
    iIntros (ot mt Hot). apply is_ptr_ot_layout in Hot as ->. done.
  Qed.
  Next Obligation.
    iIntros (???) "(%l & %ly & -> & _)". done.
  Qed.
  Next Obligation.
    iIntros (????) "_". done.
  Qed.
  Next Obligation.
    iIntros (κ π l r) "(%li & %ly & %ri & Hr & ? & ? & ?  & _)".
    eauto with iFrame.
  Qed.
  Next Obligation.
    iIntros (E κ l ly π r q ?) "#(LFT & TIME & LLCTX) Htok %Halg %Hly #Hlb Hb".
    rewrite -lft_tok_sep. iDestruct "Htok" as "(Htok & Htoki)".
    iApply fupd_logical_step.
    iMod (bor_exists with "LFT Hb") as (v) "Hb"; first solve_ndisj.
    iMod (bor_sep with "LFT Hb") as "(Hl & Hb)"; first solve_ndisj.
    iMod (bor_exists with "LFT Hb") as (l') "Hb"; first solve_ndisj.
    iMod (bor_exists with "LFT Hb") as (ly') "Hb"; first solve_ndisj.
    iMod (bor_sep with "LFT Hb") as "(Heq & Hb)"; first solve_ndisj.
    iMod (bor_persistent with "LFT Heq Htok") as "(>-> & Htok)"; first solve_ndisj.
    iMod (bor_sep with "LFT Hb") as "(Hst & Hb)"; first solve_ndisj.
    iMod (bor_persistent with "LFT Hst Htok") as "(>%Hst & Htok)"; first solve_ndisj.
    iMod (bor_sep with "LFT Hb") as "(Hly & Hb)"; first solve_ndisj.
    iMod (bor_persistent with "LFT Hly Htok") as "(>%Hly' & Htok)"; first solve_ndisj.
    iMod (bor_sep with "LFT Hb") as "(Hlb' & Hb)"; first solve_ndisj.
    iMod (bor_persistent with "LFT Hlb' Htok") as "(>#Hlb' & Htok)"; first solve_ndisj.
    iMod (bor_sep with "LFT Hb") as "(Hsc & Hb)"; first solve_ndisj.
    iMod (bor_persistent with "LFT Hsc Htok") as "(>Hsc & Htok)"; first solve_ndisj.
    iMod (bor_sep with "LFT Hb") as "(Hfree & Hb)"; first solve_ndisj.
    rewrite bi.sep_assoc.
    iMod (bor_sep with "LFT Hb") as "(Hcred & Hb)"; first solve_ndisj.
    iMod (bor_exists_tok with "LFT Hb Htok") as "(%ri & Hb & Htok)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Hrfn & Hb)"; first solve_ndisj.

    (* get observation about refinement *)
    iMod (place_rfn_interp_owned_share with "LFT Hrfn Htok") as "(Hrfn & Htok)"; first done.

    (* use credits to remove the later + fupd from Hb *)
    iDestruct "Htok" as "(Htok1 & Htok)".
    iMod (bor_acc with "LFT Hcred Htok1") as "(>(Hcred & Hat) & Hcl_cred)"; first solve_ndisj.
    iDestruct "Hcred" as "(Hcred1 & Hcred2 & Hcred)".
    set (R := (∃ v' : val, l' ↦ v' ∗ v' ◁ᵥ{ π} ri @ inner)%I).
    iPoseProof (bor_fupd_later_strong E lftE _ _ R True with "LFT [//] [Hcred1] [] Hb Htok") as "Hu"; [done | done | ..].
    { iIntros "(_ & Ha)". iModIntro. iNext. iApply (lc_fupd_add_later with "Hcred1"); iNext.
      iMod "Ha". by iFrame. }
    { eauto with iFrame. }
    iMod "Hu"as "Hu".
    iApply (lc_fupd_add_later with "Hcred2"); iNext.
    iMod "Hu" as "(Hb & Htok & _)".

    iMod (bor_fracture (λ q, l ↦{q} l')%I with "LFT Hl") as "Hl"; first solve_ndisj.

    (* recusively share *)
    iDestruct "Htoki" as "(Htoki & Htoki2)".
    iPoseProof (ty_share with "[$LFT $TIME $LLCTX] [Htok Htoki] [//] [//] Hlb' Hb") as "Hb"; first done.
    { rewrite -lft_tok_sep. iFrame. }
    iApply logical_step_fupd.
    iApply (logical_step_compose with "Hb").

    iApply (logical_step_intro_atime with "Hat").
    iModIntro. iIntros "Hcred' Hat !> [#Hshr Htok]".
    iMod ("Hcl_cred" with "[$Hcred' $Hat]") as "(? & Htok2)".
    iCombine "Htok2 Htoki2" as "Htok2". rewrite !lft_tok_sep.
    iCombine "Htok Htok2" as "$".
    iModIntro.
    iExists l', ly', ri. iFrame.
    iSplitR. { inversion Halg; subst; done. }
    iSplitR; first done. iSplitR; first done.
    inversion Halg; subst ly. iFrame "#".
    iNext. iModIntro. iModIntro. done.
  Qed.
  Next Obligation.
    simpl. iIntros (κ κ' π r l) "#Hincl (%li & %ly & %r' & Hrfn & ? & ? & ? & Hsc & Hlb & Hlbi & Hl & #Hshr)".
    iExists li, ly, r'. iFrame. iSplitL "Hl".
    { iApply (frac_bor_shorten with "Hincl Hl"). }
    iNext. iDestruct "Hshr" as "#Hshr". iModIntro. iMod "Hshr". iModIntro.
    by iApply (ty_shr_mono with "Hincl Hshr").
  Qed.
  Next Obligation.
    simpl. iIntros (π r v??) "(%l & %ly & -> & Halg & Hly & Hlb & Hsc & Hf & Hcred & Hat & Hb)".
    iDestruct "Hb" as "(%r' & Hr & Hv)".
    iApply fupd_logical_step.
    iDestruct "Hcred" as "(Hcred1 & Hcred)".
    iApply (lc_fupd_add_later with "Hcred1"); iNext.
    iMod (fupd_mask_mono with "Hv") as "Hv"; first done.
    iDestruct "Hv" as "(%v' & Hl & Hv)".
    iPoseProof (ty_own_ghost_drop with "Hv") as "Hgdrop"; first done.
    iApply (logical_step_compose with "Hgdrop").
    iApply (logical_step_intro_atime with "Hat").
    iIntros "!> Hcred' Hat !> Hgdrop".
    eauto with iFrame.
  Qed.
  Next Obligation.
    iIntros (ot mt st π r ? Hot).
    destruct mt.
    - eauto.
    - iIntros "(%l & %ly & -> & ?)".
      iExists l, ly. iFrame.
      iPoseProof (mem_cast_compat_loc (λ v, True)%I) as "%Hl"; first done.
      + eauto.
      + iPureIntro. by apply Hl.
    - iApply (mem_cast_compat_loc (λ v, _)); first done.
      iIntros "(%l & %ly & -> & _)". eauto.
  Qed.
End box.

Section subtype.
  Context `{!typeGS Σ}.

  Lemma box_own_val_mono_in {rt1 rt2} π (ty1 : type rt1) (ty2 : type rt2) r1 r2 v  :
    type_incl r2 r1 ty2 ty1 -∗
    v ◁ᵥ{π} #r2 @ box ty2 -∗
    v ◁ᵥ{π} #r1 @ box ty1.
  Proof.
    iIntros "(%Hst_eq & #Hsc_eq & #Hincl & #Hincl_shr)".
    iIntros "Hv".
    iDestruct "Hv" as (l ly) "(-> & Halg & Hly & Hlb & Hsc & Hf & Hcred & Hat & Hb)".
    iExists l. rewrite -Hst_eq. iExists ly. iSplitR; first done.
    iFrame. iDestruct "Hb" as (ri) "(-> & Hb)".
    iSplitL "Hsc". { by iApply "Hsc_eq". }
    iExists _. iSplitR; first done.
    iNext. iMod "Hb". iDestruct "Hb" as (v) "(Hl & Hv)". iExists v. iFrame. by iApply "Hincl".
  Qed.
  Lemma box_own_val_mono {rt} π (ty1 : type rt) (ty2 : type rt) r v  :
    (∀ r, type_incl r r ty2 ty1) -∗
    v ◁ᵥ{π} r @ box ty2 -∗
    v ◁ᵥ{π} r @ box ty1.
  Proof.
    iIntros "#Hincl".
    iIntros "Hv".
    iDestruct "Hv" as (l ly) "(-> & Halg & Hly & Hlb & Hsc & Hf & Hcred & Hat & Hb)".
    iExists l. iDestruct "Hb" as (ri) "(Hrfn & Hb)".
    iDestruct ("Hincl" $! ri) as "(%Hst_eq & #Hsc_eq & #Hinclv & #Hincl_shr)".
    rewrite -Hst_eq. iExists ly. iSplitR; first done. iFrame.
    iSplitL "Hsc". { by iApply "Hsc_eq". }
    iExists _. iFrame.
    iNext. iMod "Hb". iDestruct "Hb" as (v) "(Hl & Hv)". iExists v. iFrame. by iApply "Hinclv".
  Qed.

  Lemma box_shr_mono_in {rt1 rt2} π (ty1 : type rt1) (ty2 : type rt2) r1 r2 l κ :
    type_incl r2 r1 ty2 ty1 -∗
    l ◁ₗ{π, κ} #r2 @ box ty2 -∗
    l ◁ₗ{π, κ} #r1 @ box ty1.
  Proof.
    iIntros "(%Hst_eq & #Hsc_eq & #Hincl & #Hincl_shr) Hl".
    iDestruct "Hl" as (li ly ri) "(-> & ? & ? & ? & Hsc & Hlb & Hlb' & Hs & Hb)".
    iExists li, ly, _. iSplitR; first done. iFrame. rewrite -Hst_eq. iFrame.
    iSplitL "Hsc". { by iApply "Hsc_eq". }
    iNext. iDestruct "Hb" as "#Hb". iModIntro. iMod "Hb". iModIntro. by iApply "Hincl_shr".
  Qed.
  Lemma box_shr_mono {rt} π (ty1 ty2 : type rt) r l κ :
    (∀ r, type_incl r r ty2 ty1) -∗
    l ◁ₗ{π, κ} r @ box ty2 -∗
    l ◁ₗ{π, κ} r @ box ty1.
  Proof.
    iIntros "Hincl Hl".
    iDestruct "Hl" as (li ly ri) "(Hrfn & ? & ? & ? & Hsc & Hlb & Hlb' & Hs & Hb)".
    iDestruct ("Hincl" $! ri) as "(%Hst_eq & #Hsc_eq & #Hincl & #Hincl_shr)".
    iExists li, ly, ri. iFrame. rewrite -Hst_eq. iFrame.
    iSplitL "Hsc". { by iApply "Hsc_eq". }
    iNext. iDestruct "Hb" as "#Hb". iModIntro. iMod "Hb". iModIntro. by iApply "Hincl_shr".
  Qed.

  Lemma box_type_incl_in {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) r1 r2  :
    type_incl r2 r1 ty2 ty1 -∗
    type_incl #r2 #r1 (box ty2) (box ty1).
  Proof.
    iIntros "#Hincl".
    iSplitR; first done. iSplitR.
    { iPureIntro. simpl. lia. }
    iSplit; iIntros "!#".
    - iIntros (??). by iApply box_own_val_mono_in.
    - iIntros (???). by iApply box_shr_mono_in.
  Qed.
  Lemma box_type_incl {rt} (ty1 ty2 : type rt) r :
    (∀ r, type_incl r r ty2 ty1) -∗
    type_incl r r (box ty2) (box ty1).
  Proof.
    iIntros "#Hincl".
    iSplitR; first done. iSplitR.
    { iPureIntro. simpl. lia. }
    iSplit; iIntros "!#".
    - iIntros (??). by iApply box_own_val_mono.
    - iIntros (???). by iApply box_shr_mono.
  Qed.

  Lemma box_subtype {rt1 rt2} E L (ty1 : type rt1) (ty2 : type rt2) r1 r2 :
    subtype E L r1 r2 ty1 ty2 →
    subtype E L #r1 #r2 (box ty1) (box ty2).
  Proof.
    iIntros (Hsubt ?) "HL HE".
    iPoseProof (Hsubt with "HL HE") as "#Hsub".
    iApply box_type_incl_in. by iApply "Hsub".
  Qed.
  Lemma box_full_subtype {rt} E L (ty1 ty2 : type rt) :
    full_subtype E L ty1 ty2 →
    full_subtype E L (box ty1) (box ty2).
  Proof.
    iIntros (Hsubt ??) "HL HE".
    iApply box_type_incl. iIntros (?).
    iApply (Hsubt with "HL HE").
  Qed.
End subtype.

Section subltype.
  Context `{!typeGS Σ}.

  (** Box *)
  Local Lemma box_ltype_incl'_shared_in {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κ' r1 r2 :
    ltype_incl (Shared (κ')) r1 r2 lt1 lt2 -∗
    ltype_incl' (Shared κ') #(r1) #(r2) (BoxLtype lt1) (BoxLtype lt2).
  Proof.
    iIntros "#Heq".
    iModIntro.
    iIntros (π l). rewrite !ltype_own_box_unfold /box_ltype_own.
    iIntros "(%ly & ? & ? & ? & %r' & Hrfn & #Hb)".
    iExists ly. iFrame.
    iDestruct "Hrfn" as "%Heq". subst.
    iExists r2. iSplitR; first done.
    iModIntro. iMod "Hb". iDestruct "Hb" as "(%li & Hs & Hb)".
    iDestruct "Heq" as "(_ & Heq & _)".
    iModIntro. iExists _. iFrame "Hs". iApply ("Heq" with "Hb").
  Qed.
  Lemma box_ltype_incl_shared_in {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κ' r1 r2 :
    ltype_incl (Shared (κ')) r1 r2 lt1 lt2 -∗
    ltype_incl (Shared κ') #(r1) #(r2) (BoxLtype lt1) (BoxLtype lt2).
  Proof.
    iIntros "#Heq".
    iPoseProof (ltype_incl_syn_type with "Heq") as "%Hst".
    iSplitR; first done. iModIntro.
    simp_ltypes.
    iSplit; (iApply box_ltype_incl'_shared_in).
    - done.
    - iApply ltype_incl_core. done.
  Qed.

  Local Lemma box_ltype_incl'_shared {rt} (lt1 lt2 : ltype rt) κ' r :
    (∀ r, ltype_incl (Shared (κ')) r r lt1 lt2) -∗
    ltype_incl' (Shared κ') r r (BoxLtype lt1) (BoxLtype lt2).
  Proof.
    iIntros "#Heq".
    iModIntro.
    iIntros (π l). rewrite !ltype_own_box_unfold /box_ltype_own.
    iIntros "(%ly & ? & ? & ? & %r' & Hrfn & #Hb)".
    iExists ly. iFrame.
    iExists _. iFrame.
    iModIntro. iMod "Hb". iDestruct "Hb" as "(%li & Hs & Hb)".
    iDestruct ("Heq" $! _) as "(_ & Heq' & _)".
    iModIntro. iExists _. iFrame "Hs". iApply ("Heq'" with "Hb").
  Qed.
  Lemma box_ltype_incl_shared {rt} (lt1 : ltype rt) (lt2 : ltype rt) κ' r :
    (∀ r, ltype_incl (Shared (κ')) r r lt1 lt2) -∗
    ltype_incl (Shared κ') r r (BoxLtype lt1) (BoxLtype lt2).
  Proof.
    iIntros "#Heq".
    iPoseProof (ltype_incl_syn_type _ inhabitant with "Heq") as "%Hst".
    iSplitR; first done. iModIntro.
    simp_ltypes.
    iSplit; (iApply box_ltype_incl'_shared).
    - done.
    - iIntros (?). iApply ltype_incl_core. done.
  Qed.

  Local Lemma box_ltype_incl'_owned_in {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) wl r1 r2 :
    ltype_incl (Owned true) r1 r2 lt1 lt2  -∗
    ltype_incl' (Owned wl) #(r1) #(r2) (BoxLtype lt1) (BoxLtype lt2).
  Proof.
    iIntros "#Heq". iModIntro.
    iIntros (π l). rewrite !ltype_own_box_unfold /box_ltype_own.
    iIntros "(%ly & ? & ? & Hlb & ? & Hb)".
    iModIntro.
    iExists _. iFrame.
    iDestruct "Hb" as "(%r' & Hrfn & Hb)".
    iDestruct "Hrfn" as "%Heq". rewrite -Heq.
    iExists _. iSplitR; first done. iNext.
    iMod "Hb" as "(%li & %ly' & Hl & ? & ? & ? & Hb)".
    iDestruct "Heq" as "(%Hly_eq & Heq & _)".
    iExists li, ly'. rewrite Hly_eq. iFrame.
    iMod ("Heq" with "Hb") as "Hb". eauto with iFrame.
  Qed.
  Lemma box_ltype_incl_owned_in {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) wl r1 r2 :
    ltype_incl (Owned true) r1 r2 lt1 lt2  -∗
    ltype_incl (Owned wl) #(r1) #(r2) (BoxLtype lt1) (BoxLtype lt2).
  Proof.
    iIntros "#Heq".
    iPoseProof (ltype_incl_syn_type with "Heq") as "%Hst".
    iSplitR; first done. iModIntro.
    simp_ltypes.
    iSplit; (iApply box_ltype_incl'_owned_in).
    - done.
    - iApply ltype_incl_core. done.
  Qed.

  Local Lemma box_ltype_incl'_owned {rt} (lt1 lt2 : ltype rt) wl r :
    (∀ r, ltype_incl (Owned true) r r lt1 lt2) -∗
    ltype_incl' (Owned wl) r r (BoxLtype lt1) (BoxLtype lt2).
  Proof.
    iIntros "#Heq". iModIntro.
    iIntros (π l). rewrite !ltype_own_box_unfold /box_ltype_own.
    iIntros "(%ly & ? & ? & Hlb & ? & Hb)".
    iModIntro.
    iExists _. iFrame.
    iDestruct "Hb" as "(%r' & Hrfn & Hb)".
    iExists _. iFrame "Hrfn". iNext.
    iMod "Hb" as "(%li & %ly' & Hl & ? & ? & ? & Hb)".
    iDestruct ("Heq" $! _) as "(%Hly_eq & Heq' & _)".
    iExists li, ly'. rewrite Hly_eq. iFrame.
    iMod ("Heq'" with "Hb") as "Hb". eauto with iFrame.
  Qed.
  Lemma box_ltype_incl_owned {rt} (lt1 : ltype rt) (lt2 : ltype rt) wl r :
    (∀ r, ltype_incl (Owned true) r r lt1 lt2) -∗
    ltype_incl (Owned wl) r r (BoxLtype lt1) (BoxLtype lt2).
  Proof.
    iIntros "#Heq".
    iPoseProof (ltype_incl_syn_type _ inhabitant with "Heq") as "%Hst".
    iSplitR; first done. iModIntro.
    simp_ltypes.
    iSplit; (iApply box_ltype_incl'_owned).
    - done.
    - iIntros (?). iApply ltype_incl_core. done.
  Qed.


  (* Refinement subtyping under mutable references is restricted: we need to make sure that, no matter the future updates,
     we can always get back to what the lender expects. Thus we loose all refinement information when descending below mutable references. *)
  Local Lemma box_ltype_incl'_uniq {rt} (lt1 lt2 : ltype rt) κ r γ :
    (∀ r, ltype_eq (Owned true) r r lt1 lt2) -∗
    ltype_incl' (Uniq κ γ) r r (BoxLtype lt1) (BoxLtype lt2).
  Proof.
    iIntros "#Heq". iModIntro.
    iIntros (π l). rewrite !ltype_own_box_unfold /box_ltype_own.
      iIntros "(%ly & ? & ? & ? & ? & Hobs & Hb)".
      iExists ly. iFrame.
      iMod "Hb". iModIntro.
      iApply (pinned_bor_iff with "[] [] Hb").
      + iNext. iModIntro. iSplit; iIntros "(%r' & Hauth & Hb)";
        iDestruct ("Heq" $! _) as "((%Hly_eq & Heq1 & _) & (_ & Heq2 & _))";
        iExists _; rewrite Hly_eq; iFrame "Hauth".
        all: iMod "Hb"; iDestruct "Hb" as "(%li & %ly' & Hl & ? & ? & ? & Hb)".
        * iMod ("Heq1" with "Hb") as "Hb".
          iModIntro. iExists _, _. iFrame.
        * iMod ("Heq2" with "Hb") as "Hb".
          iModIntro. iExists _, _. iFrame.
      + iNext. iModIntro. iSplit; iIntros "(%r' & Hauth & Hb)";
        iDestruct ("Heq" $! _) as "((%Hly_eq & _ & Heq1) & (_ & _ & Heq2))";
        iExists _; rewrite Hly_eq; iFrame "Hauth".
        all: iMod "Hb"; iDestruct "Hb" as "(%li & %ly' & Hl & ? & ? & ? & Hb)".
        * rewrite !ltype_own_core_equiv. iMod ("Heq1" with "Hb") as "Hb".
          iModIntro. iExists _, _. iFrame. rewrite ltype_own_core_equiv. done.
        * rewrite !ltype_own_core_equiv. iMod ("Heq2" with "Hb") as "Hb".
          iModIntro. iExists _, _. iFrame. rewrite ltype_own_core_equiv. done.
  Qed.
  Lemma box_ltype_incl_uniq {rt} (lt1 lt2 : ltype rt) κ r γ :
    (∀ r, ltype_eq (Owned true) r r lt1 lt2) -∗
    ltype_incl (Uniq κ γ) r r (BoxLtype lt1) (BoxLtype lt2).
  Proof.
    iIntros "#Heq".
    iPoseProof (ltype_eq_syn_type _ inhabitant with "Heq") as "%Hst".
    iSplitR; first done. iModIntro.
    simp_ltypes.
    iSplit; (iApply box_ltype_incl'_uniq).
    - done.
    - iIntros (?). iApply ltype_eq_core. done.
  Qed.

  Lemma box_ltype_incl {rt} (lt1 lt2 : ltype rt) k r :
    (∀ k r, ltype_eq k r r lt1 lt2) -∗
    ltype_incl k r r (BoxLtype lt1) (BoxLtype lt2).
  Proof.
    iIntros "#Heq".
    destruct k.
    - iApply box_ltype_incl_owned. iIntros (?). iDestruct ("Heq" $! _ _) as "[$ _]".
    - iApply box_ltype_incl_shared. iIntros (?). iDestruct ("Heq" $! _ _) as "[$ _]".
    - iApply box_ltype_incl_uniq. iIntros (?). done.
  Qed.
  Lemma box_ltype_eq {rt} (lt1 lt2 : ltype rt) k r :
    (∀ k r, ltype_eq k r r lt1 lt2) -∗
    ltype_eq k r r (BoxLtype lt1) (BoxLtype lt2).
  Proof.
    iIntros "#Heq".
    iSplit.
    - iApply box_ltype_incl; done.
    - iApply box_ltype_incl. iIntros (??). iApply ltype_eq_sym. done.
  Qed.

  Lemma box_full_subltype E L {rt} (lt1 lt2 : ltype rt) :
    full_eqltype E L lt1 lt2 →
    full_subltype E L (BoxLtype lt1) (BoxLtype lt2).
  Proof.
    intros Hsub.
    iIntros (qL) "HL #CTX #HE". iIntros (??).
    iPoseProof (Hsub  with "HL CTX HE") as "Hsub".
    iApply (box_ltype_incl with "Hsub").
  Qed.
  Lemma box_full_eqltype E L {rt} (lt1 lt2 : ltype rt) :
    full_eqltype E L lt1 lt2 →
    full_eqltype E L (BoxLtype lt1) (BoxLtype lt2).
  Proof.
    intros Hsub.
    apply full_subltype_eqltype; eapply box_full_subltype; naive_solver.
  Qed.
End subltype.

Section unfold.
  Context `{typeGS Σ} {rt} (ty : type rt).

  Lemma box_ltype_unfold_1_owned wl r :
    ⊢ ltype_incl' (Owned wl) r r (BoxLtype (◁ ty)) (◁ (box (ty))).
  Proof.
    iModIntro. iIntros (π l). rewrite ltype_own_box_unfold /box_ltype_own ltype_own_ofty_unfold /lty_of_ty_own.
    iIntros "(%ly & ? & ? & Hlb & Hcred & %r' & Hrfn & Hb)".
    iModIntro. iExists ly. iFrame "∗".
    iExists _. iFrame. iNext. iMod "Hb".
    iDestruct "Hb" as (l' ly') "(Hl & % & % & Hf & Hb)".
    iExists l'. iFrame.
    iExists l', ly'. iSplitR; first done. iFrame "∗ %".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hb" as "(%ly'' & % & % & Hsc & Hlb' & [Hcred Hat] & Hb)".
    enough (ly'' = ly') as ->. { iModIntro. by iFrame. }
    eapply syn_type_has_layout_inj; done.
  Qed.
  Lemma box_ltype_unfold_2_owned wl r :
    ⊢ ltype_incl' (Owned wl) r r (◁ (box (ty))) (BoxLtype (◁ ty)).
  Proof.
    iModIntro. iIntros (π l).
    rewrite ltype_own_box_unfold /box_ltype_own ltype_own_ofty_unfold /lty_of_ty_own.
    iIntros "(%ly & Halg & Hly & Hsc & Hlb & Hcred & %r' & Hrfn & Hb)".
    iModIntro. iExists ly. iFrame.
    iExists r'. iFrame. iNext.
    iDestruct "Hb" as ">(%v & Hl & %l' & %ly' & -> & %Halg & %Hly & Hlb & Hsc' & Hf & Hcred & Hat & Hb)".
    iExists l', ly'. iFrame "∗ %".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own. iModIntro. iR. iExists ly'.
    iDestruct "Hb" as "(%ri & Hrfn & Hb)". iFrame "% ∗".
    eauto with iFrame.
  Qed.

  Lemma box_ltype_unfold_1_shared `{!Inhabited rt} κ r :
    ⊢ ltype_incl' (Shared κ) r r (BoxLtype (◁ ty)) (◁ (box (ty))).
  Proof.
    iModIntro. iIntros (π l). rewrite ltype_own_box_unfold /box_ltype_own ltype_own_ofty_unfold /lty_of_ty_own.
    iIntros "(%ly & %Ha & % & #Hlb & %ri & Hrfn & #Hb)".
    iExists ly. iFrame. iFrame "Hlb %".
    iExists _. iFrame. iModIntro. iMod "Hb".
    iDestruct "Hb" as "(%li & Hs & Hb)".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hb" as "(%ly' & >? & >? & >Hsc & >Hlb' & %ri' & >Hrfn & Hb)".
    iExists _, _, _. iFrame.
    injection Ha as <-. iFrame "#". done.
  Qed.
  Lemma box_ltype_unfold_2_shared κ r :
    ⊢ ltype_incl' (Shared κ) r r (◁ (box (ty))) (BoxLtype (◁ ty)).
  Proof.
    iModIntro. iIntros (π l). rewrite ltype_own_box_unfold /box_ltype_own ltype_own_ofty_unfold /lty_of_ty_own.
    iIntros "(%ly & ? & ? & Hsc & ? & %r' & Hrfn & #Hb)". iExists ly. iFrame "∗ %".
    iExists _. iFrame. iModIntro.
    iMod "Hb". iDestruct "Hb" as "(%li & %ly' & %ri & Hrfn & ? & ? & ? & Hsc & Hlb & Hlbi & Hs & Hb)".
    iModIntro. iExists li. iFrame. iNext. iDestruct "Hb" as "#Hb".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own. iExists ly'. iFrame.
    iExists _. iFrame. done.
  Qed.

  Lemma box_ltype_unfold_1_uniq κ γ r :
    ⊢ ltype_incl' (Uniq κ γ) r r (BoxLtype (◁ ty)) (◁ (box (ty))).
  Proof.
    iModIntro. iIntros (π l).
    rewrite ltype_own_box_unfold /box_ltype_own ltype_own_ofty_unfold /lty_of_ty_own.
    iIntros "(%ly & Halg & Hly & Hlb & (Hcred & Hat) & Hrfn & Hb)". iExists ly.
    iFrame "∗". iMod "Hb". iModIntro.
    setoid_rewrite ltype_own_core_equiv. simp_ltypes.
    iApply (pinned_bor_iff' with "[] Hb").
    iNext. iModIntro. iSplit.
    * iIntros "(%r' & Hauth & Hb)". iExists _. iFrame. iMod "Hb".
      iDestruct "Hb" as "(%l' & %ly' & Hl & %Halg & Hly & Hf & Hb)".
      iExists l'. iFrame.
      rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iExists l', ly'. iFrame "∗". iSplitR; first done.
      iDestruct "Hb" as "(%ly'' & %Halg' & Hly & Hsc & Hlb & [Hcred Hat] & Hb)".
      iModIntro. iFrame. iSplitR; first done.
      simp_ltypes in Halg. replace ly'' with ly'; first done.
      eapply syn_type_has_layout_inj; done.
    * iIntros "(%r' & Hauth & Hb)".
      iExists _. iFrame. iMod "Hb".
      iDestruct "Hb" as "(%v & Hl & %l' & %ly' & -> & %Halg & %Hly & Hlb & Hsc & Hf & Hcred & Hat & Hb)".
      iDestruct "Hb" as "(%ri & Hown & Hv)".
      iModIntro. iExists l', ly'. iFrame.
      iSplitR; first done. iSplitR; first done.
      rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iExists ly'. iFrame. iSplitR; first done. iSplitR; first done.
      iExists _. iFrame.
  Qed.
  Lemma box_ltype_unfold_2_uniq κ γ r :
    ⊢ ltype_incl' (Uniq κ γ) r r (◁ (box (ty))) (BoxLtype (◁ ty)).
  Proof.
    iModIntro. iIntros (π l).
    rewrite ltype_own_box_unfold /box_ltype_own ltype_own_ofty_unfold /lty_of_ty_own.
    iIntros "(%ly & Halg & Hly & Hsc & Hlb & (Hcred & Hat) & Hrfn & Hb)".
    iExists ly. iFrame. iMod "Hb". iModIntro.
    (* same proof as above *)
    setoid_rewrite ltype_own_core_equiv. simp_ltypes.
    iApply (pinned_bor_iff' with "[] Hb").
    iNext. iModIntro. iSplit.
    * iIntros "(%r' & Hauth & Hb)".
      iExists _. iFrame. iMod "Hb".
      iDestruct "Hb" as "(%v & Hl & %l' & %ly' & -> & %Halg & %Hly & Hlb & Hsc & Hf & Hcred & Hat & Hb)".
      iDestruct "Hb" as "(%ri & Hown & Hv)".
      iModIntro. iExists l', ly'. iFrame.
      iSplitR; first done. iSplitR; first done.
      rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iExists ly'. iFrame. iSplitR; first done. iSplitR; first done.
      iExists _. iFrame.
    * iIntros "(%r' & Hauth & Hb)". iExists _. iFrame. iMod "Hb".
      iDestruct "Hb" as "(%l' & %ly' & Hl & %Halg & Hly & Hf & Hb)".
      iExists l'. iFrame.
      rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iExists l', ly'. iFrame "∗". iSplitR; first done.
      iDestruct "Hb" as "(%ly'' & %Halg' & Hly & Hsc & Hlb & [Hcred Hat] & Hb)".
      iModIntro. iFrame. iSplitR; first done.
      simp_ltypes in Halg. replace ly'' with ly'; first done.
      eapply syn_type_has_layout_inj; done.
  Qed.

  Local Lemma box_ltype_unfold_1' `{!Inhabited rt} b r :
    ⊢ ltype_incl' b r r (BoxLtype (◁ ty)) (◁ (box (ty))).
  Proof.
    iModIntro. destruct b.
    - iApply box_ltype_unfold_1_owned.
    - iApply box_ltype_unfold_1_shared.
    - iApply box_ltype_unfold_1_uniq.
  Qed.
  Local Lemma box_ltype_unfold_2' b r :
    ⊢ ltype_incl' b r r (◁ (box ty)) (BoxLtype (◁ ty)).
  Proof.
    iModIntro. destruct b.
    - iApply box_ltype_unfold_2_owned.
    - iApply box_ltype_unfold_2_shared.
    - iApply box_ltype_unfold_2_uniq.
  Qed.
  Lemma box_ltype_unfold_1 `{!Inhabited rt} b r :
    ⊢ ltype_incl b r r (BoxLtype (◁ ty)) (◁ (box (ty))).
  Proof.
    iModIntro. iSplitR; first done.
    simp_ltypes. iSplit; iApply box_ltype_unfold_1'.
  Qed.
  Lemma box_ltype_unfold_2 b r :
    ⊢ ltype_incl b r r (◁ (box (ty))) (BoxLtype (◁ ty)).
  Proof.
    iModIntro. iSplitR; first done.
    simp_ltypes. iSplit; iApply box_ltype_unfold_2'.
  Qed.
  Lemma box_ltype_unfold `{Inhabited rt} b r :
    ⊢ ltype_eq b r r (BoxLtype (◁ ty)) (◁ (box (ty))).
  Proof.
    iSplit; [iApply box_ltype_unfold_1 | iApply box_ltype_unfold_2].
  Qed.

  Lemma box_ltype_unfold_full_eqltype `{!Inhabited rt} E L (lt : ltype rt) :
    full_eqltype E L lt (◁ ty)%I →
    full_eqltype E L (BoxLtype lt) (◁ (box ty))%I.
  Proof.
    intros Heq. etrans.
    { eapply box_full_eqltype; done. }
    iIntros (?) "HL #CTX #HE". iIntros (??).
    iApply box_ltype_unfold.
  Qed.
End unfold.

Section lemmas.
  Context `{!typeGS Σ}.

  Lemma box_ltype_place_cond_ty b {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) :
    typed_place_cond_ty b lt1 lt2 -∗
    typed_place_cond_ty b (BoxLtype lt1) (BoxLtype lt2).
  Proof.
    destruct b; simpl.
    - iIntros "_". done.
    - iIntros "(-> & %)". simp_ltypes. done.
    - iIntros "(%Hrefl & Heq & Hub)". subst.
      iExists eq_refl. cbn.
      iSplitL "Heq".
      + simp_ltypes. iIntros (??). by iApply box_ltype_eq.
      + by iApply box_ltype_imp_unblockable.
  Qed.

  Lemma box_ltype_acc_owned {rt} F π (lt : ltype rt) (r : place_rfn rt) wl l :
    lftE ⊆ F →
    l ◁ₗ[π, Owned wl] PlaceIn r @ BoxLtype lt -∗
    ⌜l `has_layout_loc` void*⌝ ∗ loc_in_bounds l 0 (ly_size void*) ∗ |={F}=>
      ∃ l' : loc, l ↦ l' ∗ l' ◁ₗ[π, Owned true] r @ lt ∗
      logical_step F
      (∀ rt2 (lt2 : ltype rt2) (r2 : place_rfn rt2),
        ⌜ltype_st lt2 = ltype_st lt⌝ -∗
        l ↦ l' -∗ l' ◁ₗ[π, Owned true] r2 @ lt2 ={F}=∗
        l ◁ₗ[π, Owned wl] PlaceIn r2 @ BoxLtype lt2 ∗
        (∀ bmin,
        ⌜place_access_rt_rel bmin rt rt2⌝ -∗
        typed_place_cond bmin lt lt2 r r2 -∗
        typed_place_cond bmin (BoxLtype lt) (BoxLtype lt2) (PlaceIn r) (PlaceIn r2))).
  Proof.
    iIntros (?) "Hb". rewrite ltype_own_box_unfold /box_ltype_own.
    iDestruct "Hb" as "(%ly & %Halg & %Hly & #Hlb & Hcred & %r' & <- & Hb)".
    injection Halg as <-. iFrame "#%".
    iMod (maybe_use_credit with "Hcred Hb") as "(Hcred & Hat & Hb)"; first done.
    iDestruct "Hb" as "(%l' & %ly' & Hl & %Halg & %Hly' & Hf & Hb)".
    iModIntro. iExists l'. iFrame.
    iApply (logical_step_intro_maybe with "Hat").
    iIntros "Hcred' !>". iIntros (rt2 lt2 r2 Hst) "Hl Hb". iModIntro.
    iSplitL "Hf Hl Hb Hcred'".
    { rewrite ltype_own_box_unfold /box_ltype_own. iExists void*. iFrame "# ∗".
      iSplitR; first done. iSplitR; first done.
      iExists r2. iSplitR; first done. iNext.
      iExists l', ly'. iFrame. rewrite Hst.
      iFrame "%#". done. }
    iIntros (bmin) "%Hrt Hcond".
    iDestruct "Hcond" as "(Hcondt & Hcondr)".
    iSplit.
    + iApply box_ltype_place_cond_ty; done.
    + destruct bmin; simpl; [done | | done].
      done.
      (*iExists eq_refl. done.*)
  Qed.

  Lemma box_ltype_acc_uniq {rt} F π (lt : ltype rt) (r : place_rfn rt) l q κ γ R :
    lftE ⊆ F →
    rrust_ctx -∗
    q.[κ] -∗
    (q.[κ] ={lftE}=∗ R) -∗
    l ◁ₗ[π, Uniq κ γ] #r @ BoxLtype lt -∗
    ⌜l `has_layout_loc` void*⌝ ∗ loc_in_bounds l 0 (ly_size void*) ∗ |={F}=>
      ∃ l' : loc, l ↦ l' ∗ l' ◁ₗ[π, Owned true] r @ lt ∗
      logical_step F
      ((* weak *)(∀ bmin (lt2 : ltype rt) r2,
        l ↦ l' -∗
        l' ◁ₗ[π, Owned true] r2 @ lt2  -∗
        bmin ⊑ₖ Uniq κ γ -∗
        typed_place_cond bmin lt lt2 r r2 ={F}=∗
        l ◁ₗ[π, Uniq κ γ] PlaceIn r2 @ BoxLtype lt2 ∗
        R ∗
        typed_place_cond bmin (BoxLtype lt) (BoxLtype lt2) (PlaceIn r) (PlaceIn r2)) ∧
      ((* strong *)∀ rt2 (lt2 : ltype rt2) r2,
        l ↦ l' -∗
        ⌜ltype_st lt2 = ltype_st lt⌝ -∗
        l' ◁ₗ[π, Owned true] r2 @ lt2 ={F}=∗
        l ◁ₗ[π, Uniq κ γ] PlaceIn r2 @ OpenedLtype (BoxLtype lt2) (BoxLtype lt) (BoxLtype lt)
          (λ r1 r1', ⌜r1 = r1'⌝) (λ _ _, R)))
      .
  Proof.
    iIntros (?) "#(LFT & TIME & LLCTX) Hκ HR Hb". rewrite ltype_own_box_unfold /box_ltype_own.
    iDestruct "Hb" as "(%ly & %Halg & %Hly & #Hlb & (Hcred & Hat) & Hrfn & Hb)".
    injection Halg as <-. iFrame "#%".
    iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
    iMod "Hb".
    (* NOTE: we are currently throwing away the existing "coring"-viewshift that we get *)
    iMod (pinned_bor_acc_strong lftE with "LFT Hb Hκ") as "(%κ' & #Hincl & Hb & _ & Hb_cl)"; first done.
    iMod "Hcl_F" as "_".
    iDestruct "Hcred" as "(Hcred1 & Hcred)".
    iApply (lc_fupd_add_later with "Hcred1"). iNext.
    iDestruct "Hb" as "(%r' &  Hauth & Hb)".
    iPoseProof (gvar_agree with "Hauth Hrfn") as "#->".
    iMod (fupd_mask_mono with "Hb") as "(%l' & %ly' & Hl & %Hst & %Hly' & Hf & Hb)"; first done.
    iModIntro. iExists l'. iFrame.
    iApply (logical_step_intro_atime with "Hat").
    iIntros "Hcred' Hat".
    iModIntro.
    iSplit.
    - (* close *)
      iIntros (bmin lt2 r2) "Hl Hb #Hincl_k #Hcond".
      (* extract the necessary info from the place_cond *)
      iPoseProof (typed_place_cond_incl _ (Uniq κ γ) with "Hincl_k Hcond") as "Hcond'".
      iDestruct "Hcond'" as "(Hcond' & _)".
      iDestruct "Hcond'" as "(%Heq & Heq & (_ & #Hub))".
      rewrite (UIP_refl _ _ Heq). cbn.
      iPoseProof (typed_place_cond_syn_type_eq with "Hcond") as "%Hst_eq".
      (* close the borrow *)
      iMod (gvar_update r2 with "Hauth Hrfn") as "(Hauth & Hrfn)".
      set (V := (∃ r', gvar_auth γ r' ∗ (|={lftE}=> ∃ (l' : loc) ly', l ↦ l' ∗ ⌜syn_type_has_layout (ltype_st lt2) ly'⌝ ∗ ⌜l' `has_layout_loc` ly'⌝ ∗ freeable_nz l' (ly_size ly') 1 HeapAlloc ∗ ltype_own lt2 (Owned true) π r' l'))%I).
      iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
      iDestruct "Hcred" as "(Hcred1 & Hcred)".
      iMod ("Hb_cl" $! V with "[] Hcred1 [Hauth Hf Hl Hb]") as "(Hb & Htok)".
      { iNext. iIntros "(%r' & Hauth & Hb) Hdead".
        iModIntro. iNext. iExists r'. iFrame "Hauth".
        clear. iMod "Hb" as "(%l' & %ly' & Hl & ? & ? & ? & Ha)".
        iMod (lft_incl_dead with "Hincl Hdead") as "Hdead"; first done.
        (* unblock *)
        iMod ("Hub" with "[$Hdead //] Ha") as "Ha".
        (* use that the cores are equal *)
        iDestruct ("Heq" $! (Owned true) _) as "(_ & (%Hst & #Hi & _))".
        rewrite ltype_own_core_equiv. iMod ("Hi" with "Ha") as "Ha".
        rewrite -ltype_own_core_equiv. move: Hst. rewrite !ltype_core_syn_type_eq.
        intros ->. eauto with iFrame. }
      { iModIntro. rewrite /V. rewrite -Hst_eq. eauto 8 with iFrame. }
      iMod ("HR" with "Htok") as "$".
      iMod "Hcl_F" as "_".
      iModIntro.
      (* TODO maybe donate the leftover credits *)
      iSplitL.
      { rewrite ltype_own_box_unfold /box_ltype_own.
        iExists void*. iFrame.
        iSplitR; first done. iSplitR; first done. iSplitR; first done.
        iPoseProof (pinned_bor_shorten with "Hincl Hb") as "Hb".
        iModIntro. subst V.
        (* need to adapt the pinned part, too *)
        iApply (pinned_bor_iff with "[] [] Hb").
        { iNext. iModIntro. eauto. }
        clear -Hst_eq.
        iNext. iModIntro. iSplit.
        - iIntros "(%r' & Hauth & Hb)". iExists r'. iFrame.
          iMod "Hb" as "(%l' & %ly' & Hl & Halg & Hly & Hf & Hb)".
          iDestruct ("Heq" $! (Owned true) _) as "((_ & #Heq1 & _) & (_ & #Heq2 & _))".
          rewrite ltype_own_core_equiv. iMod ("Heq1" with "Hb") as "Hb". rewrite -ltype_own_core_equiv.
          rewrite Hst_eq. eauto with iFrame.
        - iIntros "(%r' & Hauth & Hb)". iExists r'. iFrame.
          iMod "Hb" as "(%l' & %ly' & Hl & Halg & Hly & Hf & Hb)".
          iDestruct ("Heq" $! (Owned true) _) as "((_ & #Heq1 & _) & (_ & #Heq2 & _))".
          rewrite ltype_own_core_equiv. iMod ("Heq2" with "Hb") as "Hb". rewrite -ltype_own_core_equiv.
          rewrite Hst_eq. eauto with iFrame.
      }
      iDestruct "Hcond" as "(Hcond_ty & Hcond_rfn)".
      iSplit.
      + iApply box_ltype_place_cond_ty; done.
      + iApply typed_place_cond_rfn_lift. done.
    - (* shift to OpenedLtype *)
      iIntros (rt2 lt2 r2) "Hl %Hst' Hb". iModIntro.
      iDestruct "Hcred" as "(Hcred1 & Hcred)".
      iApply (opened_ltype_create_uniq_simple with "Hrfn Hauth Hcred1 Hat Hincl HR Hb_cl [] [Hcred']"); first done.
      { iModIntro. iIntros (?) "Hauth Hc". simp_ltypes.
        rewrite ltype_own_box_unfold /box_ltype_own.
        iExists _. iFrame. iDestruct "Hc" as ">(% & _ & _ & _ & _ & %r' & -> & >(%l0 & % & Hl & %Halg & % & Hf & Hb))".
        iModIntro. setoid_rewrite ltype_own_core_equiv.
        iExists _, _. move: Halg. rewrite ltype_core_syn_type_eq => ?.
        eauto with iFrame. }
      { iIntros (?) "Hobs Hat Hcred Hp". simp_ltypes.
        rewrite ltype_own_box_unfold /box_ltype_own.
        setoid_rewrite ltype_own_core_equiv. rewrite ltype_core_idemp.
        rewrite ltype_core_syn_type_eq. iModIntro. eauto 8 with iFrame. }
      { rewrite ltype_own_box_unfold /box_ltype_own.
        iExists void*. do 4 iR.
        iExists r2. iR. iNext. iModIntro. rewrite Hst'. eauto with iFrame. }
  Qed.

  Lemma box_ltype_acc_shared {rt} F π (lt : ltype rt) r l q κ :
    lftE ⊆ F →
    rrust_ctx -∗
    q.[κ] -∗
    l ◁ₗ[π, Shared κ] #r @ BoxLtype lt -∗
    ⌜l `has_layout_loc` void*⌝ ∗ loc_in_bounds l 0 (ly_size void*) ∗ |={F}=>
      ∃ (l' : loc) q', l ↦{q'} l' ∗ (|={F}▷=> l' ◁ₗ[π, Shared κ] r @ lt) ∗
    (∀ (lt' : ltype rt) r',
      l ↦{q'} l' -∗
      l' ◁ₗ[π, Shared κ] r' @ lt' -∗ |={F}=>
      l ◁ₗ[π, Shared κ] #r' @ BoxLtype lt' ∗
      q.[κ] ∗
      (∀ bmin,
      bmin ⊑ₖ Shared κ -∗
      typed_place_cond bmin lt lt' r r' ={F}=∗
      typed_place_cond bmin (BoxLtype lt) (BoxLtype lt') #r #r')).
  Proof.
    iIntros (?) "#(LFT & TIME & LLCTX) Hκ Hb". rewrite {1}ltype_own_box_unfold /box_ltype_own.
    iDestruct "Hb" as "(%ly & %Hst & %Hly & #Hlb & %r' & -> & #Hb)".
    apply syn_type_has_layout_ptr_inv in Hst. subst ly.
    iR. iR.
    iMod (fupd_mask_mono with "Hb") as "(%li & #Hf & #Hl)"; first done.
    iMod (frac_bor_acc with "LFT Hf Hκ") as "(%q' & >Hpts & Hclf)"; first done.
    iModIntro. iExists _, _. iFrame.
    iSplitR. { iApply step_fupd_intro; first done. auto. }
    iIntros (lt' r'') "Hpts #Hl'".
    iMod ("Hclf" with "Hpts") as "Htok".
    iFrame. iSplitL.
    { iModIntro. rewrite ltype_own_box_unfold /box_ltype_own. iExists void*. iFrame "% #".
      iR. iExists _. iR. iModIntro. iModIntro. iExists _. iFrame "#". }
    iModIntro. iIntros (bmin) "Hincl Hcond".
    iDestruct "Hcond" as "(Hcond_ty & Hcond_rfn)".
    iModIntro. iSplit.
    + iApply box_ltype_place_cond_ty; done.
    + destruct bmin; done.
  Qed.
End lemmas.

Section rules.
  Context `{!typeGS Σ}.


  (** Place access *)
  (* Needs to have lower priority than the id instance *)
  Lemma place_ofty_box {rt} `{Inhabited rt} π E L l (ty : type rt) (r : place_rfn (place_rfn rt)) bmin0 b P T :
    typed_place π E L l (BoxLtype (◁ ty)) r bmin0 b P T
    ⊢ typed_place π E L l (◁ (box ty)) r bmin0 b P T.
  Proof.
    iIntros "Hp". iApply typed_place_eqltype; last done.
    symmetry. apply box_ltype_unfold_full_eqltype; first apply _. reflexivity.
  Qed.
  Global Instance typed_place_ofty_box_inst {rt} `{Inhabited rt} π E L l (ty : type rt) (r : place_rfn (place_rfn rt)) bmin0 b P :
    TypedPlace E L π l (◁ (box ty))%I r bmin0 b P | 30 := λ T, i2p (place_ofty_box π E L l ty r bmin0 b P T).

  Lemma typed_place_box_owned {rto} π E L (lt2 : ltype rto) P l r wl bmin0 (T : place_cont_t (place_rfn rto)) :
    (∀ l', typed_place π E L l' lt2 r (bmin0) (Owned true) P
      (λ L' κs l2 b2 bmin rti tyli ri strong weak,
        T L' κs l2 b2 bmin rti tyli ri
          (fmap (λ strong, mk_strong
            (λ rti2, place_rfn (strong.(strong_rt) rti2))
            (λ rti2 lti2 ri2, BoxLtype (strong.(strong_lt) _ lti2 ri2))
            (λ rti2 (r : place_rfn rti2), PlaceIn (strong.(strong_rfn) _ r))
            strong.(strong_R)) strong)
          (fmap (λ weak, mk_weak
            (λ lti2 ri2, BoxLtype (weak.(weak_lt) lti2 ri2))
            (λ (r : place_rfn rti), PlaceIn (weak.(weak_rfn) r))
            weak.(weak_R)) weak)))
    ⊢ typed_place π E L l (BoxLtype lt2) (PlaceIn r) bmin0 (Owned wl) (DerefPCtx Na1Ord PtrOp true :: P) T.
  Proof.
    iIntros "HR" (Φ F ??). iIntros "#(LFT & TIME & LLCTX) #HE HL Hincl0 HP HΦ/=".
    iPoseProof (box_ltype_acc_owned F with "HP") as "(%Hly & Hlb & Hb)"; [done.. | ].
    iApply fupd_wp. iMod (fupd_mask_subseteq F) as "HclF"; first done.
    iMod "Hb" as "(%l' & Hl & Hb & Hcl)". iMod "HclF" as "_".
    iModIntro. iApply (wp_logical_step with "TIME Hcl"); [solve_ndisj.. | ].
    iApply (wp_deref with "Hl") => //; [solve_ndisj | by apply val_to_of_loc | ].
    iNext. iIntros (st) "Hl Hcred Hc". iMod (fupd_mask_subseteq F) as "HclF"; first done.
    iMod "HclF" as "_". iExists l'.
    iSplitR. { iPureIntro. unfold mem_cast. rewrite val_to_of_loc. done. }
    iApply ("HR" with "[//] [//] [$LFT $TIME $LLCTX] HE HL [] Hb"). { destruct bmin0; done. }
    iModIntro. iIntros (L' κs l2 b2 bmin rti tyli ri strong weak) "#Hincl1 Hb Hs".
    iApply ("HΦ" $! _ _ _ _ bmin _ _ _ _ _ with "Hincl1 Hb") => /=.
    iSplit.
    - (* strong update *) iDestruct "Hs" as "[Hs _]".
      destruct strong as [ strong | ]; last done.
      iIntros (rti2 ltyi2 ri2).
      iIntros "Hl2 %Hcond".
      iMod ("Hs" with "Hl2 [//]") as "(Hb & %Hcond2 & HR)".
      iMod ("Hc" with "[] Hl Hb") as "(Hb & Hcond)".
      { done. }
      iModIntro. iFrame "HR Hb".
      done.
    - (* weak update *)
      destruct weak as [ weak | ]; last done.
      iDestruct "Hs" as "[_ Hs]".
      iIntros (ltyi2 ri2 bmin').
      iIntros "Hincl2 Hl2 Hcond".
      iMod ("Hs" with "Hincl2 Hl2 Hcond") as "(Hb & Hcond & $ & HR)".
      iPoseProof (typed_place_cond_syn_type_eq with "Hcond") as "%Hst".
      iMod ("Hc" with "[//] Hl Hb") as "(Hb & Ha)".
      iPoseProof ("Ha" with "[] Hcond") as "Hcond".
      { iPureIntro. apply place_access_rt_rel_refl. }
      iModIntro. iFrame "HR Hb".
      done.
  Qed.
  Global Instance typed_place_box_owned_inst {rto} π E L (lt2 : ltype rto) bmin0 r l wl P :
    TypedPlace E L π l (BoxLtype lt2) (PlaceIn r) bmin0 (Owned wl) (DerefPCtx Na1Ord PtrOp true :: P) | 30 := λ T, i2p (typed_place_box_owned π E L lt2 P l r wl bmin0 T).

  Lemma typed_place_box_uniq {rto} π E L (lt2 : ltype rto) P l r κ' γ' bmin0
    (T : place_cont_t (place_rfn rto)) :
    li_tactic (lctx_lft_alive_count_goal E L κ') (λ '(κs, L'),
      (∀ l', typed_place π E L' l' lt2 r (bmin0) (Owned true) P
        (λ L'' κs' l2 b2 bmin rti tyli ri strong weak,
          T L'' (κs ++ κs') l2 b2 (Uniq κ' γ' ⊓ₖ bmin) rti tyli ri
            (* strong branch: fold to OpenedLtype *)
            (fmap (λ strong, mk_strong (place_rfn ∘ strong.(strong_rt))
              (λ rti2 ltyi2 ri2,
                OpenedLtype (BoxLtype (strong.(strong_lt) _ ltyi2 ri2)) (BoxLtype lt2) (BoxLtype lt2) (λ r1 r1', ⌜r1 = r1'⌝) (λ _ _, llft_elt_toks κs))
              (λ rti2 ri2, PlaceIn $ strong.(strong_rfn) _ ri2)
              strong.(strong_R)) strong)
            (* weak branch: just keep the Box *)
            (fmap (λ weak, mk_weak (λ lti2 ri2, BoxLtype (weak.(weak_lt) lti2 ri2)) (λ (r : place_rfn rti), PlaceIn (weak.(weak_rfn) r)) weak.(weak_R)) weak))))
    ⊢ typed_place π E L l (BoxLtype lt2) (PlaceIn r) bmin0 (Uniq κ' γ') (DerefPCtx Na1Ord PtrOp true :: P) T.
  Proof.
    rewrite /lctx_lft_alive_count_goal.
    iIntros "(%κs & %L2 & %Hal & HT)".
    iIntros (Φ F ??). iIntros "#(LFT & TIME & LLCTX) #HE HL #Hincl0 HP HΦ/=".
    (* get a token *)
    iApply fupd_wp. iMod (fupd_mask_subseteq lftE) as "HclF"; first done.
    iMod (lctx_lft_alive_count_tok lftE with "HE HL") as (q) "(Hκ' & Hclκ' & HL)"; [done.. | ].
    iMod "HclF" as "_". iMod (fupd_mask_subseteq F) as "HclF"; first done.
    iPoseProof (box_ltype_acc_uniq F with "[$LFT $TIME $LLCTX] Hκ' Hclκ' HP") as "(%Hly & Hlb & Hb)"; [done.. | ].
    iMod "Hb" as "(%l' & Hl & Hb & Hcl)". iMod "HclF" as "_".
    iModIntro. iApply (wp_logical_step with "TIME Hcl"); [solve_ndisj.. | ].
    iApply (wp_deref with "Hl") => //; [solve_ndisj | by apply val_to_of_loc | ].
    iNext.
    iIntros (st) "Hl Hcred Hcl".
    iExists l'.
    iSplitR. { iPureIntro. unfold mem_cast. rewrite val_to_of_loc. done. }
    iApply ("HT" with "[//] [//] [$LFT $TIME $LLCTX] HE HL [] Hb"). { destruct bmin0; done. }
    iModIntro. iIntros (L'' κs' l2 b2 bmin rti tyli ri strong weak) "#Hincl1 Hb Hs".
    iApply ("HΦ" $! _ _ _ _ (Uniq κ' γ' ⊓ₖ bmin) _ _ _ _ _ with "[Hincl1] Hb").
    { iApply bor_kind_incl_trans; last iApply "Hincl1". iApply bor_kind_min_incl_r. }
    simpl. iSplit.
    - (* strong update *)
      iDestruct "Hs" as "(Hs & _)". iDestruct "Hcl" as "(_ & Hcl)".
      destruct strong as [strong | ]; last done.
      iIntros (tyli2 ri2 bmin').
      iIntros "Hl2 %Hst".
      iMod ("Hs" with "Hl2 [//]") as "(Hb & %Hst' & HR)".
      iMod ("Hcl" with "Hl [] Hb") as "Hb".
      { iPureIntro. done. }
      iModIntro. simp_ltypes.
      iFrame. done.
    - (* weak update *)
      destruct weak as [ weak | ]; last done.
      iDestruct "Hs" as "(_ & Hs)". iDestruct "Hcl" as "(Hcl & _)".
      iIntros (ltyi2 ri2 bmin') "#Hincl2 Hl2 Hcond".
      iMod ("Hs" with "[Hincl2] Hl2 Hcond") as "(Hb & Hcond & ? & HR)".
      { iApply bor_kind_incl_trans; first iApply "Hincl2". iApply bor_kind_min_incl_r. }
      iMod ("Hcl" with "Hl Hb [//] Hcond") as "(Hb & Hκ' & Hcond)".
      iModIntro. rewrite llft_elt_toks_app. iFrame.
  Qed.
  Global Instance typed_place_box_uniq_inst {rto} π E L (lt2 : ltype rto) bmin0 r l κ' γ' P :
    TypedPlace E L π l (BoxLtype lt2) (PlaceIn r) bmin0 (Uniq κ' γ') (DerefPCtx Na1Ord PtrOp true :: P) | 30 := λ T, i2p (typed_place_box_uniq π E L lt2 P l r κ' γ' bmin0 T).

  Lemma typed_place_box_shared {rto} π E L (lt2 : ltype rto) P l r κ' bmin0 (T : place_cont_t (place_rfn rto)) :
    li_tactic (lctx_lft_alive_count_goal E L κ') (λ '(κs, L'),
      (∀ l', typed_place π E L' l' lt2 r (bmin0) (Shared κ') P
        (λ L'' κs' l2 b2 bmin rti tyli ri strong weak,
          T L'' (κs ++ κs') l2 b2 (Shared κ' ⊓ₖ bmin) rti tyli ri
            (* strong branch: fold to ShadowedLtype *)
            (* TODO *)
              None
            (* weak branch: just keep the Box *)
            (fmap (λ weak, mk_weak (λ lti2 ri2, BoxLtype (weak.(weak_lt) lti2 ri2)) (λ (r : place_rfn rti), PlaceIn (weak.(weak_rfn) r)) weak.(weak_R)) weak))))
    ⊢ typed_place π E L l (BoxLtype lt2) (PlaceIn r) bmin0 (Shared κ') (DerefPCtx Na1Ord PtrOp true :: P) T.
  Proof.
    rewrite /lctx_lft_alive_count_goal.
    iIntros "(%κs & %L2 & %Hal & HT)".
    iIntros (Φ F ??). iIntros "#(LFT & TIME & LLCTX) #HE HL #Hincl0 HP HΦ/=".
    (* get a token *)
    iApply fupd_wp. iMod (fupd_mask_subseteq lftE) as "HclF"; first done.
    iMod (lctx_lft_alive_count_tok lftE with "HE HL") as (q) "(Hκ' & Hclκ' & HL)"; [done.. | ].
    iMod "HclF" as "_". iMod (fupd_mask_subseteq F) as "HclF"; first done.
    iPoseProof (box_ltype_acc_shared F with "[$LFT $TIME $LLCTX] Hκ' HP") as "(%Hly & Hlb & Hb)"; [done.. | ].
    iMod "Hb" as "(%l' & %q' & Hl & Hb & Hcl)". iMod "Hb".
    iMod "HclF" as "_".
    iModIntro.
    iApply wp_fupd.
    iApply (wp_deref with "Hl") => //; [solve_ndisj | by apply val_to_of_loc | ].
    iNext.
    iIntros (st) "Hl Hcred".
    iExists l'. iMod (fupd_mask_mono with "Hb") as "Hb"; first done.
    iSplitR. { iPureIntro. unfold mem_cast. rewrite val_to_of_loc. done. }
    iApply ("HT" with "[//] [//] [$LFT $TIME $LLCTX] HE HL [] Hb"). { destruct bmin0; done. }
    iModIntro. iIntros (L'' κs' l2 b2 bmin rti tyli ri strong weak) "#Hincl1 Hb Hs".
    iApply ("HΦ" $! _ _ _ _ (Shared κ' ⊓ₖ bmin) _ _ _ _ _ with "[Hincl1] Hb").
    { iApply bor_kind_incl_trans; last iApply "Hincl1". iApply bor_kind_min_incl_r. }
    simpl. iSplit.
    - (* strong update *)
      done.
    - (* weak update *)
      destruct weak as [ weak | ]; last done.
      iDestruct "Hs" as "(_ & Hs)".
      iIntros (ltyi2 ri2 bmin') "#Hincl2 Hl2 Hcond".
      iMod ("Hs" with "[Hincl2] Hl2 Hcond") as "(Hb & Hcond & ? & HR)".
      { iApply bor_kind_incl_trans; first iApply "Hincl2". iApply bor_kind_min_incl_r. }
      iMod ("Hcl" with "Hl Hb") as "(Hb & Hκ' & Hcond')".
      iMod (fupd_mask_mono with "(Hclκ' Hκ')") as "?"; first done.
      rewrite llft_elt_toks_app. iFrame.
      cbn. iApply "Hcond'"; last done. done.
  Qed.
  Global Instance typed_place_box_shared_inst {rto} π E L (lt2 : ltype rto) bmin0 r l κ' P :
    TypedPlace E L π l (BoxLtype lt2) (#r) bmin0 (Shared κ') (DerefPCtx Na1Ord PtrOp true :: P) | 30 := λ T, i2p (typed_place_box_shared π E L lt2 P l r κ' bmin0 T).


  Lemma stratify_ltype_box_Owned {rt} `{Inhabited rt} π E L mu mdu ma {M} (ml : M) l (lt : ltype rt) (r : (place_rfn rt)) wl
      (T : llctx → iProp Σ → ∀ rt', ltype rt' → place_rfn rt' → iProp Σ) :
    (∀ l', stratify_ltype π E L mu mdu ma ml l' lt r (Owned true) (λ L' R rt' (lt' : ltype rt') r',
        if ma is StratRefoldFull
        then cast_ltype_to_type E L' lt' (λ ty', T L' R _ (◁ (box ty'))%I (PlaceIn r'))
        else T L' R _ (BoxLtype lt') (PlaceIn r')))
    ⊢ stratify_ltype π E L mu mdu ma ml l (BoxLtype lt) (PlaceIn r) (Owned wl) T.
  Proof.
    iIntros "Hs". iIntros (?? ?) "#(LFT & TIME & LLCTX) #HE HL Hb".
    iPoseProof (box_ltype_acc_owned F with "Hb") as "Hb"; [done.. | ].
    iDestruct "Hb" as "(%Hly & #Hlb & >(%l' & Hl & Hb & Hcl))".
    iPoseProof ("Hs" with "[//] [//] [$LFT $TIME $LLCTX] HE HL Hb") as "Hb".
    iMod "Hb" as "(%L' & %R & %rt' & %lt' & %r' & HL & %Hcond & Hstep & Hc)".
    destruct (decide (ma = StratRefoldFull)) as [Heq | ].
    - subst ma.
      iDestruct "Hc" as "(%ty' & %Heq' & HT)".
      rewrite full_eqltype_alt in Heq'.
      iPoseProof (eqltype_use F with "[$LFT $TIME $LLCTX] HE HL") as "(Hvs & HL)"; [done | .. ].
      { apply Heq'. }
      iPoseProof (eqltype_acc _ _ (Owned false) r' r' with "[$LFT $TIME $LLCTX] HE HL") as "#Heq"; first apply Heq'.
      iPoseProof (ltype_eq_syn_type with "Heq") as "%Hst".
      iModIntro. iExists L', R, _, _, _. iFrame.
      iSplitR. { simp_ltypes. done. }
      iApply logical_step_fupd.
      iApply (logical_step_compose with "Hcl").
      iApply (logical_step_compose with "Hstep").
      iApply logical_step_intro. iIntros "(Hb & $) Hcl".
      iMod ("Hvs" with "Hb") as "Hb".
      iMod ("Hcl" with "[] Hl Hb") as "(Hb & _)".
      { simp_ltype. done. }
      iDestruct (box_ltype_unfold_1 ty' (Owned wl)) as "(_ & #Hi & _)".
      iMod (fupd_mask_mono with "(Hi Hb)") as "$"; first done.
      done.
    - iAssert (T L' R _ (BoxLtype lt') (PlaceIn r'))%I with "[Hc]" as "Hc".
      { destruct ma; done. }
      iModIntro. iExists L', R, _, _, _. iFrame.
      iSplitR. { simp_ltypes; done. }
      iApply logical_step_fupd.
      iApply (logical_step_compose with "Hcl").
      iApply (logical_step_compose with "Hstep").
      iApply logical_step_intro. iIntros "(Hb & $) Hcl".
      by iMod ("Hcl" with "[] Hl Hb") as "($ & _)".
  Qed.
  Global Instance stratify_ltype_box_Owned_inst {rt} `{Inhabited rt} π E L mu mdu ma {M} (ml : M) l (lt : ltype rt) (r : (place_rfn rt)) wl :
    StratifyLtype π E L mu mdu ma ml l (BoxLtype lt) (PlaceIn r) (Owned wl) := λ T, i2p (stratify_ltype_box_Owned π E L mu mdu ma ml l lt r wl T).

  Lemma stratify_ltype_box_uniq {rt} π E L mu mdu ma {M} (ml : M) l (lt : ltype rt) (r : (place_rfn rt)) κ' γ'
      (T : llctx → iProp Σ → ∀ rt', ltype rt' → place_rfn rt' → iProp Σ) :
    (* get a lifetime token *)
    li_tactic (lctx_lft_alive_count_goal E L κ') (λ '(κs, L1),
      (∀ l', stratify_ltype π E L1 mu mdu ma ml l' lt r (Owned true) (λ L2 R rt' lt' r',
        (* validate the update *)
        prove_place_cond E L2 (Uniq κ' γ') lt lt' (λ upd,
          match upd with
          | ResultWeak Heq =>
              (* update obeys the contract, get a box *)
              match ma with
              | StratRefoldFull => cast_ltype_to_type E L2 lt' (λ ty', T L2 (llft_elt_toks κs ∗ R) _ (◁ (box ty'))%I (#r'))
              | _ => T L2 (llft_elt_toks κs ∗ R) _ (BoxLtype lt') (#r')
              end
          | ResultStrong =>
              (* unfold to an OpenedLtype *)
              ⌜ma = StratNoRefold⌝ ∗
              T L2 R _ (OpenedLtype (BoxLtype lt') (BoxLtype lt) (BoxLtype lt) (λ r1 r2, ⌜r1 = r2⌝) (λ _ _, llft_elt_toks κs)) (#r')
          end))))
    ⊢ stratify_ltype π E L mu mdu ma ml l (BoxLtype lt) (PlaceIn r) (Uniq κ' γ') T.
  Proof.
    iIntros "Hs". iIntros (?? ?) "#(LFT & TIME & LLCTX) #HE HL Hb".
    rewrite /lctx_lft_alive_count_goal.
    iDestruct "Hs" as "(%κs & %L1 & %Hal & Hs)".
    iMod (fupd_mask_subseteq lftE) as "HF_cl"; first done.
    iMod (lctx_lft_alive_count_tok with "HE HL") as "(%q & Htok & Hcl_tok & HL)"; [done.. | ].
    iMod "HF_cl" as "_".
    iPoseProof (box_ltype_acc_uniq F with "[$LFT $TIME $LLCTX] Htok Hcl_tok Hb") as "Hb"; [done.. | ].
    iDestruct "Hb" as "(%Hly & #Hlb & >(%l' & Hl & Hb & Hcl))".
    iPoseProof ("Hs" with "[//] [//] [$LFT $TIME $LLCTX] HE HL Hb") as "Hb".
    iMod "Hb" as "(%L2 & %R & %rt' & %lt' & %r' & HL & %Hcond & Hstep & Hc)".
    iMod ("Hc" with "[] [$LFT $TIME $LLCTX] HE HL") as "(HL & %upd & Hupd & Hs)"; first done.
    destruct upd as [ Heq | ].
    - (* weak *)
      subst rt'.
      destruct (decide (ma = StratRefoldFull)) as [Heq | ].
      + rewrite Heq. iDestruct "Hs" as "(%ty' & %Heqt & HT)".
        iPoseProof (full_eqltype_acc with "[$LFT $TIME $LLCTX] HE HL") as "#Heq"; [apply Heqt | ].

        iExists _, _, _, _, _. iFrame.
        iSplitR. { iModIntro. done. }
        iApply logical_step_fupd.
        iApply (logical_step_compose with "Hstep").
        iApply (logical_step_compose with "Hcl").
        iModIntro. iApply logical_step_intro.
        iIntros "[Hcl _] (Hb & HR)".
        iFrame. iMod ("Hcl" with "Hl Hb [] [Hupd]") as "(Hl & $ & _)".
        { iApply bor_kind_incl_refl. }
        { iSplit; first done. done. }
        iDestruct (box_ltype_incl_uniq with "[]") as "(_ & #Hincl & _)".
        { iIntros (?). iApply "Heq". }
        iPoseProof ("Hincl" with "Hl") as "Hl".
        by iApply (box_ltype_unfold_1_uniq with "Hl").
      + iAssert (T L2 (llft_elt_toks κs ∗ R) (place_rfn rt) (BoxLtype lt') # r')%I with "[Hs]" as "Hs".
        { destruct ma; first done. all: done. }
        iExists _, _, _, _, _. iFrame.
        iSplitR. { iModIntro. done. }
        iApply logical_step_fupd.
        iApply (logical_step_compose with "Hstep").
        iApply (logical_step_compose with "Hcl").
        iModIntro. iApply logical_step_intro.
        iIntros "[Hcl _] (Hb & HR)".
        iFrame. iMod ("Hcl" with "Hl Hb [] [Hupd]") as "(Hl & $ & _)".
        { iApply bor_kind_incl_refl. }
        { iSplit; first done. done. }
        done.
    - (* strong *)
      iDestruct "Hs" as "(-> & Hs)".
      iDestruct "Hupd" as "%Hst".
      iExists _, _, _, _, _. iFrame.
      iSplitR. { done. }
      iApply logical_step_fupd.
      iApply (logical_step_compose with "Hstep").
      iApply (logical_step_compose with "Hcl").
      iModIntro. iApply logical_step_intro.
      iIntros "[_ Hcl] (Hb & HR)".
      iFrame. iMod ("Hcl" with "Hl [] Hb") as "Hb".
      { done. }
      done.
  Qed.
  Global Instance stratify_ltype_box_uniq_inst {rt} π E L mu mdu ma {M} (ml : M) l (lt : ltype rt) (r : (place_rfn rt)) κ' γ' :
    StratifyLtype π E L mu mdu ma ml l (BoxLtype lt) (PlaceIn r) (Uniq κ' γ') :=
      λ T, i2p (stratify_ltype_box_uniq π E L mu mdu ma ml l lt r κ' γ' T).

  (* TODO: shared folding instance *)

  (** Unfolding instances *)
  Lemma stratify_ltype_ofty_box {rt} `{!Inhabited rt} π E L mu ma {M} (ml : M) l (ty : type rt) (r : place_rfn (place_rfn rt)) b T :
    stratify_ltype π E L mu StratDoUnfold ma ml l (BoxLtype (◁ ty)) r b T
    ⊢ stratify_ltype π E L mu StratDoUnfold ma ml l (◁ (box ty)) r b T.
  Proof.
    iIntros "Hp". iApply stratify_ltype_eqltype; iFrame.
    iPureIntro. apply full_eqltype_alt. symmetry.
    eapply box_ltype_unfold_full_eqltype; first apply _. reflexivity.
  Qed.
  Global Instance stratify_ltype_ofty_box_inst {rt} `{Inhabited rt} π E L mu ma {M} (ml : M) l (ty : type rt) (r : place_rfn (place_rfn rt)) b :
    StratifyLtype π E L mu StratDoUnfold ma ml l (◁ (box ty))%I r b | 30 := λ T, i2p (stratify_ltype_ofty_box π E L mu ma ml l ty r b T).


  (** prove_place_cond instances *)
  (* These need to have a lower priority than the ofty_refl instance (level 2) and the unblocking instances (level 5), but higher than the trivial "no" instance *)
  Lemma prove_place_cond_unfold_box_l E L {rt1 rt2} `{Inhabited rt1} (ty : type rt1) (lt : ltype rt2) k T :
    prove_place_cond E L k (BoxLtype (◁ ty)) lt T
    ⊢ prove_place_cond E L k (◁ (box ty)) lt T.
  Proof.
    iApply prove_place_cond_eqltype_l. apply symmetry. apply box_ltype_unfold_full_eqltype; done.
  Qed.
  Global Instance prove_place_cond_unfold_box_l_inst E L {rt1 rt2} `{Inhabited rt1} (ty : type rt1) (lt : ltype rt2) k :
    ProvePlaceCond E L k (◁ (box ty))%I lt | 10 := λ T, i2p (prove_place_cond_unfold_box_l E L ty lt k T).
  Lemma prove_place_cond_unfold_box_r E L {rt1 rt2} `{Inhabited rt1} (ty : type rt1) (lt : ltype rt2) k T :
    prove_place_cond E L k lt (BoxLtype (◁ ty)) T
    ⊢ prove_place_cond E L k lt (◁ (box ty)) T.
  Proof.
    iApply prove_place_cond_eqltype_r. apply symmetry. apply box_ltype_unfold_full_eqltype; done.
  Qed.
  Global Instance prove_place_cond_unfold_box_r_inst E L {rt1 rt2} `{Inhabited rt1} (ty : type rt1) (lt : ltype rt2) k :
    ProvePlaceCond E L k lt (◁ (box ty))%I | 10 := λ T, i2p (prove_place_cond_unfold_box_r E L ty lt k T).

  Lemma prove_place_cond_box_ltype E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) k T :
    prove_place_cond E L k lt1 lt2 (λ upd, T $ access_result_lift (place_rfn) upd)
    ⊢ prove_place_cond E L k (BoxLtype lt1) (BoxLtype lt2) T.
  Proof.
    iIntros "HT". iIntros (F ?) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "($ & (%upd & Hcond & HT))".
    iExists _. iFrame. destruct upd; cbn.
    - subst rt2. by iApply box_ltype_place_cond_ty.
    - done.
  Qed.
  Global Instance prove_place_cond_box_ltype_inst E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) k :
    ProvePlaceCond E L k (BoxLtype lt1) (BoxLtype lt2) | 5 := λ T, i2p (prove_place_cond_box_ltype E L lt1 lt2 k T).

  (** Resolve ghost *)
  Import EqNotations.
  Lemma resolve_ghost_box_Owned {rt} π E L l (lt : ltype rt) γ wl rm lb T :
    find_observation (place_rfn rt) γ FindObsModeDirect (λ or,
        match or with
        | None => ⌜rm = ResolveTry⌝ ∗ T L (PlaceGhost γ) True false
        | Some r => T L (PlaceIn $ r) True true
        end)
    ⊢ resolve_ghost π E L rm lb l (BoxLtype lt) (Owned wl) (PlaceGhost γ) T.
  Proof.
    iIntros "Ha" (???) "#CTX #HE HL Hl".
    iMod ("Ha" with "[//]") as "[(%r' & HObs & Ha) | (_ & Ha)]".
    - rewrite ltype_own_box_unfold /box_ltype_own.
      iDestruct "Hl" as "(%ly & ? & ? & ? & ? & % & Hinterp & ?)".
      simpl. iPoseProof (gvar_pobs_agree_2 with "Hinterp HObs") as "#<-".
      iExists _, _, _, _. iFrame. iApply maybe_logical_step_intro.
      iL. rewrite ltype_own_box_unfold /box_ltype_own.
      iExists _. iFrame. iExists _. iR. by iFrame.
    - iExists _, _, _, _. iFrame.  iApply maybe_logical_step_intro. by iFrame.
  Qed.
  Global Instance resolve_ghost_box_owned_inst {rt} π E L l (lt : ltype rt) γ wl rm lb :
    ResolveGhost π E L rm lb l (BoxLtype lt) (Owned wl) (PlaceGhost γ) | 7 := λ T, i2p (resolve_ghost_box_Owned π E L l lt γ wl rm lb T).

  Lemma resolve_ghost_box_Uniq {rt} π E L l (lt : ltype rt) γ rm lb κ γ' T :
    find_observation (place_rfn rt) γ FindObsModeDirect (λ or,
        match or with
        | None => ⌜rm = ResolveTry⌝ ∗ T L (PlaceGhost γ) True false
        | Some r => T L (PlaceIn $ r) True true
        end)
    ⊢ resolve_ghost π E L rm lb l (BoxLtype lt) (Uniq κ γ') (PlaceGhost γ) T.
  Proof.
    iIntros "Ha" (???) "#CTX #HE HL Hl".
    iMod ("Ha" with "[//]") as "[(%r' & HObs & Ha) | (_ & Ha)]".
    - rewrite ltype_own_box_unfold /box_ltype_own.
      iDestruct "Hl" as "(%ly & ? & ? & ? & ? & Hinterp & ?)".
      simpl.
      iPoseProof (Rel2_use_pobs with "HObs Hinterp") as "(%r2 & Hobs & ->)".
      iExists _, _, _, _. iFrame. iApply maybe_logical_step_intro.
      iL. rewrite ltype_own_box_unfold /box_ltype_own.
      iExists _. iFrame. done.
    - iExists _, _, _, _. iFrame.  iApply maybe_logical_step_intro. by iFrame.
  Qed.
  Global Instance resolve_ghost_box_uniq_inst {rt} π E L l (lt : ltype rt) γ κ γ' rm lb :
    ResolveGhost π E L rm lb l (BoxLtype lt) (Uniq κ γ') (PlaceGhost γ) | 7 := λ T, i2p (resolve_ghost_box_Uniq π E L l lt γ rm lb κ γ' T).

  Lemma resolve_ghost_box_shared {rt} π E L l (lt : ltype rt) γ rm lb κ T :
    find_observation (place_rfn rt) γ FindObsModeDirect (λ or,
        match or with
        | None => ⌜rm = ResolveTry⌝ ∗ T L (PlaceGhost γ) True false
        | Some r => T L (#r) True true
        end)
    ⊢ resolve_ghost π E L rm lb l (BoxLtype lt) (Shared κ) (PlaceGhost γ) T.
  Proof.
    iIntros "Ha" (???) "#CTX #HE HL Hl".
    iMod ("Ha" with "[//]") as "[(%r' & HObs & Ha) | (_ & Ha)]".
    - rewrite ltype_own_box_unfold /box_ltype_own.
      iDestruct "Hl" as "(%ly & ? & ? & ? & % & Hinterp & ?)".
      simpl. iPoseProof (gvar_pobs_agree_2 with "Hinterp HObs") as "#<-".
      iExists _, _, _, _. iFrame. iApply maybe_logical_step_intro.
      iL. rewrite ltype_own_box_unfold /box_ltype_own.
      iExists _. iFrame. iExists _. iR. by iFrame.
    - iExists _, _, _, _. iFrame. iApply maybe_logical_step_intro. by iFrame.
  Qed.
  Global Instance resolve_ghost_box_shared_inst {rt} π E L l (lt : ltype rt) γ κ rm lb :
    ResolveGhost π E L rm lb l (BoxLtype lt) (Shared κ) (PlaceGhost γ) | 7 := λ T, i2p (resolve_ghost_box_shared π E L l lt γ rm lb κ T).

  (** cast_ltype *)
  Lemma cast_ltype_to_type_box E L {rt} `{Inhabited rt} (lt : ltype rt) T  :
    cast_ltype_to_type E L lt (λ ty, T (box ty))
    ⊢ cast_ltype_to_type E L (BoxLtype lt) T.
  Proof.
    iIntros "Hs". iDestruct "Hs" as "(%ty & %Heq & HT)".
    iExists (box ty). iFrame "HT". iPureIntro.
    apply box_ltype_unfold_full_eqltype; done.
  Qed.
  Global Instance cast_ltype_to_type_box_inst E L {rt} `{Inhabited rt} (lt : ltype rt) :
    CastLtypeToType E L (BoxLtype lt) := λ T, i2p (cast_ltype_to_type_box E L lt T).

  (** Subtyping instances *)
  Lemma weak_subtype_box_in E L {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) r1 r2 T :
    weak_subtype E L r1 r2 ty1 ty2 T
    ⊢ weak_subtype E L #r1 #r2 (box ty1) (box ty2) T.
  Proof.
    iIntros "HT" (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(Hincl & $ & $)".
    by iApply box_type_incl_in.
  Qed.
  Global Instance weak_subtype_box_in_inst E L {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) r1 r2 :
    Subtype E L #r1 #r2 (box ty1) (box ty2) | 10 := λ T, i2p (weak_subtype_box_in E L ty1 ty2 r1 r2 T).

  Lemma weak_subtype_box E L {rt} (ty1 : type rt) (ty2 : type rt) r T :
    mut_subtype E L ty1 ty2 T
    ⊢ weak_subtype E L r r (box ty1) (box ty2) T.
  Proof.
    iIntros "(%Hsubt & HT)" (??) "#CTX #HE HL".
    iPoseProof (full_subtype_acc with "HE HL") as "#Hincl"; first done.
    iFrame. by iApply box_type_incl.
  Qed.
  Global Instance weak_subtype_box_inst E L {rt} (ty1 : type rt) (ty2 : type rt) r :
    Subtype E L r r (box ty1) (box ty2) | 15 := λ T, i2p (weak_subtype_box E L ty1 ty2 r T).

  Lemma mut_subtype_box E L {rt} (ty1 ty2 : type rt) T :
    mut_subtype E L ty1 ty2 T
    ⊢ mut_subtype E L (box ty1) (box ty2) T.
  Proof.
    iIntros "(%Hsubt & $)". iPureIntro.
    by eapply box_full_subtype.
  Qed.
  Global Instance mut_subtype_box_inst E L {rt} (ty1 ty2 : type rt) :
    MutSubtype E L (box ty1) (box ty2) := λ T, i2p (mut_subtype_box E L ty1 ty2 T).

  Lemma mut_eqtype_box E L {rt} (ty1 ty2 : type rt) T :
    mut_eqtype E L ty1 ty2 T
    ⊢ mut_eqtype E L (box ty1) (box ty2) T.
  Proof.
    iIntros "(%Hsubt & $)". iPureIntro.
    apply full_subtype_eqtype; eapply box_full_subtype.
    - by apply full_eqtype_subtype_l.
    - by apply full_eqtype_subtype_r.
  Qed.
  Global Instance mut_eqtype_box_inst E L {rt} (ty1 ty2 : type rt) :
    MutEqtype E L (box ty1) (box ty2) := λ T, i2p (mut_eqtype_box E L ty1 ty2 T).

  (** Subltyping instances *)
  (* generic in [r2] to handle the case that it is an evar *)
  Lemma weak_subltype_box_owned_in E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) wl r1 r2 T :
    (∃ r2', ⌜r2 = #r2'⌝ ∗ weak_subltype E L (Owned true) r1 r2' lt1 lt2 T)
    ⊢ weak_subltype E L (Owned wl) #r1 r2 (BoxLtype lt1) (BoxLtype lt2) T.
  Proof.
    iIntros "(%r2' & -> & HT)" (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(Hincl & $ & $)".
    by iApply box_ltype_incl_owned_in.
  Qed.
  Global Instance weak_subltype_box_owned_in_inst E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) wl r1 r2 :
    SubLtype E L (Owned wl) #r1 r2 (BoxLtype lt1) (BoxLtype lt2) | 10 := λ T, i2p (weak_subltype_box_owned_in E L lt1 lt2 wl r1 r2 T).

  Lemma weak_subltype_box_shared_in E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κ r1 r2 T :
    (∃ r2', ⌜r2 = #r2'⌝ ∗ weak_subltype E L (Shared κ) r1 r2' lt1 lt2 T)
    ⊢ weak_subltype E L (Shared κ) #r1 r2 (BoxLtype lt1) (BoxLtype lt2) T.
  Proof.
    iIntros "(%r2' & -> & HT)" (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(Hincl & $ & $)".
    by iApply box_ltype_incl_shared_in.
  Qed.
  Global Instance weak_subltype_box_shared_in_inst E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κ r1 r2 :
    SubLtype E L (Shared κ) #r1 r2 (BoxLtype lt1) (BoxLtype lt2) | 10 := λ T, i2p (weak_subltype_box_shared_in E L lt1 lt2 κ r1 r2 T).

  (* Base instance that will trigger, e.g., for Uniq or PlaceGhost refinements *)
  Lemma weak_subltype_box_base E L {rt} (lt1 lt2 : ltype rt) k r T :
    mut_eqltype E L lt1 lt2 T
    ⊢ weak_subltype E L k r r (BoxLtype lt1) (BoxLtype lt2) T.
  Proof.
    iIntros "(%Hsubt & T)" (??) "#CTX #HE HL".
    iPoseProof (full_eqltype_acc with "CTX HE HL") as "#Hincl"; first done. iFrame.
    iApply box_ltype_incl. done.
  Qed.
  Global Instance weak_subltype_box_base_inst E L {rt} (lt1 lt2 : ltype rt) k r :
    SubLtype E L k r r (BoxLtype lt1) (BoxLtype lt2) | 20 := λ T, i2p (weak_subltype_box_base E L lt1 lt2 k r T).

  Lemma mut_subltype_box E L {rt} (lt1 lt2 : ltype rt) T :
    mut_eqltype E L lt1 lt2 T
    ⊢ mut_subltype E L (BoxLtype lt1) (BoxLtype lt2) T.
  Proof.
    iIntros "(%Heqt & $)". iPureIntro.
    by eapply box_full_subltype.
  Qed.
  Global Instance mut_subltype_box_inst E L {rt} (lt1 lt2 : ltype rt) :
    MutSubLtype E L (BoxLtype lt1) (BoxLtype lt2) := λ T, i2p (mut_subltype_box E L lt1 lt2 T).

  Lemma mut_eqltype_box E L {rt} (lt1 lt2 : ltype rt) T :
    mut_eqltype E L lt1 lt2 T
    ⊢ mut_eqltype E L (BoxLtype lt1) (BoxLtype lt2) T.
  Proof.
    iIntros "(%Heqt & $)". iPureIntro.
    apply full_subltype_eqltype; eapply box_full_subltype.
    - done.
    - symmetry. done.
  Qed.
  Global Instance mut_eqltype_box_inst E L {rt} (lt1 lt2 : ltype rt) :
    MutEqLtype E L (BoxLtype lt1) (BoxLtype lt2) := λ T, i2p (mut_eqltype_box E L lt1 lt2 T).

  (* Ofty unfolding if necessary *)
  Lemma weak_subltype_box_ofty_1 E L {rt1 rt2} `{!Inhabited rt2} (lt1 : ltype rt1) (ty2 : type (place_rfn rt2)) k r1 r2 T :
    (∃ ty2', ⌜ty2 = box ty2'⌝ ∗ weak_subltype E L k r1 r2 (BoxLtype lt1) (BoxLtype (◁ ty2')) T)
    ⊢ weak_subltype E L k r1 r2 (BoxLtype lt1) (◁ ty2) T.
  Proof.
    iIntros "(%ty2' & -> & HT)" (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(Hincl & $ & $)".
    iApply (ltype_incl_trans with "Hincl").
    iApply box_ltype_unfold_1.
  Qed.
  Global Instance weak_subltype_box_ofty_1_inst E L {rt1 rt2} `{!Inhabited rt2} (lt1 : ltype rt1) (ty2 : type (place_rfn rt2)) k r1 r2 :
    SubLtype E L k r1 r2 (BoxLtype lt1) (◁ ty2)%I | 10 := λ T, i2p (weak_subltype_box_ofty_1 E L lt1 ty2 k r1 r2 T).

  Lemma weak_subltype_box_ofty_2 E L {rt1 rt2} `{!Inhabited rt2} (ty1 : type (place_rfn rt1)) (lt2 : ltype rt2) k r1 r2 T :
    (∃ ty1', ⌜ty1 = box ty1'⌝ ∗ weak_subltype E L k r1 r2 (BoxLtype (◁ ty1')) (BoxLtype lt2) T)
    ⊢ weak_subltype E L k r1 r2 (◁ ty1) (BoxLtype lt2) T.
  Proof.
    iIntros "(%ty1' & -> & HT)" (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(Hincl & $ & $)".
    iApply (ltype_incl_trans with "[] Hincl").
    iApply box_ltype_unfold_2.
  Qed.
  Global Instance weak_subltype_box_ofty_2_inst E L {rt1 rt2} `{!Inhabited rt2} (ty1 : type (place_rfn rt1)) (lt2 : ltype rt2) k r1 r2 :
    SubLtype E L k r1 r2 (◁ ty1)%I (BoxLtype lt2) | 10 := λ T, i2p (weak_subltype_box_ofty_2 E L ty1 lt2 k r1 r2 T).

  (* Same for [mut_subltype] *)
  Lemma mut_subltype_box_ofty_1 E L {rt} `{!Inhabited rt} (lt1 : ltype rt) (ty2 : type (place_rfn rt)) T :
    (∃ ty2', ⌜ty2 = box ty2'⌝ ∗ mut_subltype E L (BoxLtype lt1) (BoxLtype (◁ ty2')) T)
    ⊢ mut_subltype E L (BoxLtype lt1) (◁ ty2) T.
  Proof.
    iIntros "(%ty2' & -> & %Hsubt & $)". iPureIntro.
    etrans; first done. eapply full_eqltype_subltype_l.
    by eapply box_ltype_unfold_full_eqltype.
  Qed.
  Global Instance mut_subltype_box_ofty_1_inst E L {rt} `{!Inhabited rt} (lt1 : ltype rt) (ty2 : type (place_rfn rt)) :
    MutSubLtype E L (BoxLtype lt1) (◁ ty2)%I | 10 := λ T, i2p (mut_subltype_box_ofty_1 E L lt1 ty2 T).

  Lemma mut_subltype_box_ofty_2 E L {rt} `{!Inhabited rt} (ty1 : type (place_rfn rt)) (lt2 : ltype rt) T :
    (∃ ty1', ⌜ty1 = box ty1'⌝ ∗ mut_subltype E L (BoxLtype (◁ ty1')) (BoxLtype lt2) T)
    ⊢ mut_subltype E L (◁ ty1) (BoxLtype lt2) T.
  Proof.
    iIntros "(%ty1' & -> & %Hsubt & $)". iPureIntro.
    etrans; last done. eapply full_eqltype_subltype_r.
    by eapply box_ltype_unfold_full_eqltype.
  Qed.
  Global Instance mut_subltype_box_ofty_2_inst E L {rt} `{!Inhabited rt} (ty1 : type (place_rfn rt)) (lt2 : ltype rt) :
    MutSubLtype E L (◁ ty1)%I (BoxLtype lt2) | 10 := λ T, i2p (mut_subltype_box_ofty_2 E L ty1 lt2 T).

  (* Same for [mut_eqltype] *)
  Lemma mut_eqltype_box_ofty_1 E L {rt} `{!Inhabited rt} (lt1 : ltype rt) (ty2 : type (place_rfn rt)) T :
    (∃ ty2', ⌜ty2 = box ty2'⌝ ∗ mut_eqltype E L (BoxLtype lt1) (BoxLtype (◁ ty2')) T)
    ⊢ mut_eqltype E L (BoxLtype lt1) (◁ ty2) T.
  Proof.
    iIntros "(%ty2' & -> & %Heqt & $)". iPureIntro.
    etrans; first done. by eapply box_ltype_unfold_full_eqltype.
  Qed.
  Global Instance mut_eqltype_box_ofty_1_inst E L {rt} `{!Inhabited rt} (lt1 : ltype rt) (ty2 : type (place_rfn rt)) :
    MutEqLtype E L (BoxLtype lt1) (◁ ty2)%I | 10 := λ T, i2p (mut_eqltype_box_ofty_1 E L lt1 ty2 T).

  Lemma mut_eqltype_box_ofty_2 E L {rt} `{!Inhabited rt} (ty1 : type (place_rfn rt)) (lt2 : ltype rt) T :
    (∃ ty1', ⌜ty1 = box ty1'⌝ ∗ mut_eqltype E L (BoxLtype (◁ ty1')) (BoxLtype lt2) T)
    ⊢ mut_eqltype E L (◁ ty1) (BoxLtype lt2) T.
  Proof.
    iIntros "(%ty1' & -> & %Heqt & $)". iPureIntro.
    etrans; last done. symmetry. by eapply box_ltype_unfold_full_eqltype.
  Qed.
  Global Instance mut_eqltype_box_ofty_2_inst E L {rt} `{!Inhabited rt} (ty1 : type (place_rfn rt)) (lt2 : ltype rt) :
    MutEqLtype E L (◁ ty1)%I (BoxLtype lt2) | 10 := λ T, i2p (mut_eqltype_box_ofty_2 E L ty1 lt2 T).
End rules.
Global Typeclasses Opaque BoxLtype.
Global Typeclasses Opaque box.
