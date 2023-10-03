From refinedrust Require Export base type.
From refinedrust Require Import programs uninit ltypes.
From caesium Require Import derived.

Section owned_ptr.
  Context `{typeGS Σ} {rt}
  (*`{Inhabited rt} *)
  (inner : type rt).

  Program Definition owned_ptr : type (place_rfn rt * loc) := {|
    ty_sidecond := True;
    ty_own_val π '(r, l) v :=
      ∃ (ly : layout), ⌜v = l⌝ ∗ ⌜syn_type_has_layout inner.(ty_syn_type) ly⌝ ∗ ⌜l `has_layout_loc` ly⌝ ∗
        loc_in_bounds l 0 ly.(ly_size) ∗
        inner.(ty_sidecond) ∗
        £ num_cred ∗ atime 1 ∗
        ∃ (ri : rt), place_rfn_interp_owned r ri ∗
        (* this needs to match up with the corresponding later/fupd in the OfTyLtype to get the unfolding equation *)
        ▷ |={lftE}=> ∃ v' : val, l ↦ v' ∗ inner.(ty_own_val) π ri v';
    ty_has_op_type ot mt := is_ptr_ot ot;
    ty_syn_type := PtrSynType;

    ty_shr κ tid '(r, li) l :=
      (∃ (ly : layout) (ri : rt), place_rfn_interp_shared r ri ∗
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
    ty_ghost_drop π '(r, l) :=
      ∃ ri, place_rfn_interp_owned r ri ∗ inner.(ty_ghost_drop) π ri;

    ty_lfts := inner.(ty_lfts);
    ty_wf_E := inner.(ty_wf_E);
  |}%I.
  Next Obligation.
    iIntros (π [r l] v) "(%ly & -> & ? & ? & _)". eauto with iFrame.
  Qed.
  Next Obligation.
    iIntros (ot mt Hot). apply is_ptr_ot_layout in Hot as ->. done.
  Qed.
  Next Obligation.
    iIntros (?[] ?) "(%ly & -> & _)". done.
  Qed.
  Next Obligation.
    intros ??? []. apply _.
  Qed.
  Next Obligation.
    iIntros (κ π l []) "(%ly & %ri & Hr & ? & ? & ?  & _)".
    eauto with iFrame.
  Qed.
  Next Obligation.
    iIntros (E κ l ly π [r li] q ?) "#(LFT & TIME & LLCTX) Htok %Halg %Hly #Hlb Hb".
    rewrite -lft_tok_sep. iDestruct "Htok" as "(Htok & Htoki)".
    iApply fupd_logical_step.
    iMod (bor_exists with "LFT Hb") as (v) "Hb"; first solve_ndisj.
    iMod (bor_sep with "LFT Hb") as "(Hl & Hb)"; first solve_ndisj.
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
    set (R := (∃ v' : val, li ↦ v' ∗ v' ◁ᵥ{ π} ri @ inner)%I).
    iPoseProof (bor_fupd_later_strong E lftE _ _ R True with "LFT [//] [Hcred1] [] Hb Htok") as "Hu"; [done | done | ..].
    { iIntros "(_ & Ha)". iModIntro. iNext. iApply (lc_fupd_add_later with "Hcred1"); iNext.
      iMod "Ha". by iFrame. }
    { eauto with iFrame. }
    iMod "Hu"as "Hu".
    iApply (lc_fupd_add_later with "Hcred2"); iNext.
    iMod "Hu" as "(Hb & Htok & _)".

    iMod (bor_fracture (λ q, l ↦{q} li)%I with "LFT Hl") as "Hl"; first solve_ndisj.

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
    iExists ly', ri. iFrame.
    iSplitR. { inversion Halg; subst; done. }
    iSplitR; first done. iSplitR; first done.
    inversion Halg; subst ly. iFrame "#".
    iNext. iModIntro. iModIntro. done.
  Qed.
  Next Obligation.
    simpl. iIntros (κ κ' π [r li] l) "#Hincl (%ly & %r' & Hrfn & ? & ? & ? & Hsc & Hlb & Hlbi & Hl & #Hshr)".
    iExists ly, r'. iFrame. iSplitL "Hl".
    { iApply (frac_bor_shorten with "Hincl Hl"). }
    iNext. iDestruct "Hshr" as "#Hshr". iModIntro. iMod "Hshr". iModIntro.
    by iApply (ty_shr_mono with "Hincl Hshr").
  Qed.
  Next Obligation.
    simpl. iIntros (π [r l] v??) "(%ly & -> & Halg & Hly & Hlb & Hsc & Hcred & Hat & Hb)".
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
    iIntros (ot mt st π [r l] ? Hot).
    destruct mt.
    - eauto.
    - iIntros "(%ly & -> & ?)".
      iExists ly. iFrame.
      iPoseProof (mem_cast_compat_loc (λ v, True)%I) as "%Hl"; first done.
      + eauto.
      + iPureIntro. by apply Hl.
    - iApply (mem_cast_compat_loc (λ v, _)); first done.
      iIntros "(%ly & -> & _)". eauto.
  Qed.

End owned_ptr.

(* TODO rules *)

Section rules.
  Context `{!typeGS Σ}.




End rules.
