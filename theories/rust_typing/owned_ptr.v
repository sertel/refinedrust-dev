From caesium Require Import derived.
From refinedrust Require Export base type.
From refinedrust Require Import programs uninit ltypes.

(** * Owned pointers as value types. *)
(** This isn't fully developed currently, but should eventually replace the primitive Box type *)


Section owned_ptr.
  Context `{typeGS Σ} {rt} (inner : type rt).

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
    _ty_has_op_type ot mt := is_ptr_ot ot;
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
    iIntros (??[] ?) "_". done.
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

Section subltype.
  Context `{!typeGS Σ}.

  (** Owned Ptr *)
  Local Lemma owned_ptr_ltype_incl'_shared_in {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) b κ' r1 r2 l1 l2 :
    ltype_incl (Shared (κ')) r1 r2 lt1 lt2 -∗
    ⌜l1 = l2⌝ -∗
    ltype_incl' (Shared κ') #(r1, l1) #(r2, l2) (OwnedPtrLtype lt1 b) (OwnedPtrLtype lt2 b).
  Proof.
    iIntros "#Heq ->".
    iModIntro.
    iIntros (π l). rewrite !ltype_own_owned_ptr_unfold /owned_ptr_ltype_own.
    iIntros "(%ly & ? & ? & ? & %r' & %l' & Hrfn & #Hb)".
    iExists ly. iFrame.
    iDestruct "Hrfn" as "%Heq". injection Heq as <- <-.
    iExists r2, l2. iSplitR; first done.
    iModIntro. iMod "Hb". iDestruct "Hb" as "(Hs & Hb)".
    iDestruct "Heq" as "(_ & Heq & _)".
    iModIntro. iFrame "Hs". iApply ("Heq" with "Hb").
  Qed.
  Lemma owned_ptr_ltype_incl_shared_in {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) b κ' r1 r2 l1 l2 :
    ltype_incl (Shared (κ')) r1 r2 lt1 lt2 -∗
    ⌜l1 = l2⌝ -∗
    ltype_incl (Shared κ') #(r1, l1) #(r2, l2) (OwnedPtrLtype lt1 b) (OwnedPtrLtype lt2 b).
  Proof.
    iIntros "#Heq #Hincl1".
    iPoseProof (ltype_incl_syn_type with "Heq") as "%Hst".
    iSplitR; first done. iModIntro.
    simp_ltypes.
    iSplit; (iApply owned_ptr_ltype_incl'_shared_in; [ | done  ]).
    - done.
    - iApply ltype_incl_core. done.
  Qed.

  Local Lemma owned_ptr_ltype_incl'_shared {rt} (lt1 lt2 : ltype rt) b κ' r :
    (∀ r, ltype_incl (Shared (κ')) r r lt1 lt2) -∗
    ltype_incl' (Shared κ') r r (OwnedPtrLtype lt1 b) (OwnedPtrLtype lt2 b).
  Proof.
    iIntros "#Heq".
    iModIntro.
    iIntros (π l). rewrite !ltype_own_owned_ptr_unfold /owned_ptr_ltype_own.
    iIntros "(%ly & ? & ? & ? & %r' & %l' & Hrfn & #Hb)".
    iExists ly. iFrame.
    iExists _, _. iFrame.
    iModIntro. iMod "Hb". iDestruct "Hb" as "(Hs & Hb)".
    iDestruct ("Heq" $! _) as "(_ & Heq' & _)".
    iModIntro. iFrame "Hs". iApply ("Heq'" with "Hb").
  Qed.
  Lemma owned_ptr_ltype_incl_shared {rt} (lt1 : ltype rt) (lt2 : ltype rt) b κ' r :
    (∀ r, ltype_incl (Shared (κ')) r r lt1 lt2) -∗
    ltype_incl (Shared κ') r r (OwnedPtrLtype lt1 b) (OwnedPtrLtype lt2 b).
  Proof.
    iIntros "#Heq".
    iPoseProof (ltype_incl_syn_type _ inhabitant with "Heq") as "%Hst".
    iSplitR; first done. iModIntro.
    simp_ltypes.
    iSplit; (iApply owned_ptr_ltype_incl'_shared).
    - done.
    - iIntros (?). iApply ltype_incl_core. done.
  Qed.

  Local Lemma owned_ptr_ltype_incl'_owned_in {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) b wl r1 r2 l1 l2 :
    ltype_incl (Owned b) r1 r2 lt1 lt2  -∗
    ⌜l1 = l2⌝ -∗
    ltype_incl' (Owned wl) #(r1, l1) #(r2, l2) (OwnedPtrLtype lt1 b) (OwnedPtrLtype lt2 b).
  Proof.
    iIntros "#Heq ->". iModIntro.
    iIntros (π l). rewrite !ltype_own_owned_ptr_unfold /owned_ptr_ltype_own.
    iIntros "(%ly & ? & ? & Hlb & ? & Hb)".
    iModIntro.
    iExists _. iFrame.
    iDestruct "Hb" as "(%r' & %l' & Hrfn & Hb)".
    iDestruct "Hrfn" as "%Heq". injection Heq as <- <-.
    iExists _, _. iSplitR; first done. iNext.
    iMod "Hb" as "(%ly' & Hl & ? & ? & Hb)".
    iDestruct "Heq" as "(%Hly_eq & Heq & _)".
    iExists ly'. rewrite Hly_eq. iFrame.
    iMod ("Heq" with "Hb") as "Hb". eauto with iFrame.
  Qed.
  Lemma owned_ptr_ltype_incl_owned_in {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) b l1 l2 wl r1 r2 :
    ltype_incl (Owned b) r1 r2 lt1 lt2  -∗
    ⌜l1 = l2⌝ -∗
    ltype_incl (Owned wl) #(r1, l1) #(r2, l2) (OwnedPtrLtype lt1 b) (OwnedPtrLtype lt2 b).
  Proof.
    iIntros "#Heq #Hincl1".
    iPoseProof (ltype_incl_syn_type with "Heq") as "%Hst".
    iSplitR; first done. iModIntro.
    simp_ltypes.
    iSplit; (iApply owned_ptr_ltype_incl'_owned_in; [ | done  ]).
    - done.
    - iApply ltype_incl_core. done.
  Qed.

  Local Lemma owned_ptr_ltype_incl'_owned {rt} (lt1 lt2 : ltype rt) b wl r :
    (∀ r, ltype_incl (Owned b) r r lt1 lt2) -∗
    ltype_incl' (Owned wl) r r (OwnedPtrLtype lt1 b) (OwnedPtrLtype lt2 b).
  Proof.
    iIntros "#Heq". iModIntro.
    iIntros (π l). rewrite !ltype_own_owned_ptr_unfold /owned_ptr_ltype_own.
    iIntros "(%ly & ? & ? & Hlb & ? & Hb)".
    iModIntro.
    iExists _. iFrame.
    iDestruct "Hb" as "(%r' & %l' & Hrfn & Hb)".
    iExists _, _. iFrame "Hrfn". iNext.
    iMod "Hb" as "(%ly' & Hl & ? & ? & Hb)".
    iDestruct ("Heq" $! _) as "(%Hly_eq & Heq' & _)".
    iExists ly'. rewrite Hly_eq. iFrame.
    iMod ("Heq'" with "Hb") as "Hb". eauto with iFrame.
  Qed.
  Lemma owned_ptr_ltype_incl_owned {rt} (lt1 : ltype rt) (lt2 : ltype rt) b wl r :
    (∀ r, ltype_incl (Owned b) r r lt1 lt2) -∗
    ltype_incl (Owned wl) r r (OwnedPtrLtype lt1 b) (OwnedPtrLtype lt2 b).
  Proof.
    iIntros "#Heq".
    iPoseProof (ltype_incl_syn_type _ inhabitant with "Heq") as "%Hst".
    iSplitR; first done. iModIntro.
    simp_ltypes.
    iSplit; (iApply owned_ptr_ltype_incl'_owned).
    - done.
    - iIntros (?). iApply ltype_incl_core. done.
  Qed.

  (* Refinement subtyping under mutable references is restricted: we need to make sure that, no matter the future updates,
     we can always get back to what the lender expects. Thus we loose all refinement information when descending below mutable references. *)
  Local Lemma owned_ptr_ltype_incl'_uniq {rt} (lt1 lt2 : ltype rt) b κ r γ :
    (∀ r, ltype_eq (Owned b) r r lt1 lt2) -∗
    ltype_incl' (Uniq κ γ) r r (OwnedPtrLtype lt1 b) (OwnedPtrLtype lt2 b).
  Proof.
    iIntros "#Heq". iModIntro.
    iIntros (π l). rewrite !ltype_own_owned_ptr_unfold /owned_ptr_ltype_own.
      iIntros "(%ly & ? & ? & ? & ? & Hobs & Hb)".
      iExists ly. iFrame.
      iMod "Hb". iModIntro.
      iApply (pinned_bor_iff with "[] [] Hb").
      + iNext. iModIntro. iSplit; iIntros "(%r' & %l' & Hauth & Hb)";
        iDestruct ("Heq" $! _) as "((%Hly_eq & Heq1 & _) & (_ & Heq2 & _))";
        iExists _, _; rewrite Hly_eq; iFrame "Hauth".
        all: iMod "Hb"; iDestruct "Hb" as "(%ly' & Hl & ? & ? & Hb)".
        * iMod ("Heq1" with "Hb") as "Hb".
          iModIntro. iExists _. iFrame.
        * iMod ("Heq2" with "Hb") as "Hb".
          iModIntro. iExists _. iFrame.
      + iNext. iModIntro. iSplit; iIntros "(%r' & %l' & Hauth & Hb)";
        iDestruct ("Heq" $! _) as "((%Hly_eq & _ & Heq1) & (_ & _ & Heq2))";
        iExists _, _; rewrite Hly_eq; iFrame "Hauth".
        all: iMod "Hb"; iDestruct "Hb" as "(%ly' & Hl & ? & ? & Hb)".
        * rewrite !ltype_own_core_equiv. iMod ("Heq1" with "Hb") as "Hb".
          iModIntro. iExists _. iFrame. rewrite ltype_own_core_equiv. done.
        * rewrite !ltype_own_core_equiv. iMod ("Heq2" with "Hb") as "Hb".
          iModIntro. iExists _. iFrame. rewrite ltype_own_core_equiv. done.
  Qed.
  Lemma owned_ptr_ltype_incl_uniq {rt} (lt1 lt2 : ltype rt) b κ r γ :
    (∀ r, ltype_eq (Owned b) r r lt1 lt2) -∗
    ltype_incl (Uniq κ γ) r r (OwnedPtrLtype lt1 b) (OwnedPtrLtype lt2 b).
  Proof.
    iIntros "#Heq".
    iPoseProof (ltype_eq_syn_type _ inhabitant with "Heq") as "%Hst".
    iSplitR; first done. iModIntro.
    simp_ltypes.
    iSplit; (iApply owned_ptr_ltype_incl'_uniq).
    - done.
    - iIntros (?). iApply ltype_eq_core. done.
  Qed.

  Lemma owned_ptr_ltype_incl {rt} (lt1 lt2 : ltype rt) b k r :
    (∀ k r, ltype_eq k r r lt1 lt2) -∗
    ltype_incl k r r (OwnedPtrLtype lt1 b) (OwnedPtrLtype lt2 b).
  Proof.
    iIntros "#Heq".
    destruct k.
    - iApply owned_ptr_ltype_incl_owned. iIntros (?). iDestruct ("Heq" $! _ _) as "[$ _]".
    - iApply owned_ptr_ltype_incl_shared. iIntros (?). iDestruct ("Heq" $! _ _) as "[$ _]".
    - iApply owned_ptr_ltype_incl_uniq. iIntros (?). done.
  Qed.
  Lemma owned_ptr_ltype_eq {rt} (lt1 lt2 : ltype rt) k b r :
    (∀ k r, ltype_eq k r r lt1 lt2) -∗
    ltype_eq k r r (OwnedPtrLtype lt1 b) (OwnedPtrLtype lt2 b).
  Proof.
    iIntros "#Heq".
    iSplit.
    - iApply owned_ptr_ltype_incl; done.
    - iApply owned_ptr_ltype_incl. iIntros (??). iApply ltype_eq_sym. done.
  Qed.

  Lemma owned_ptr_full_subltype E L {rt} (lt1 lt2 : ltype rt) b :
    full_eqltype E L lt1 lt2 →
    full_subltype E L (OwnedPtrLtype lt1 b) (OwnedPtrLtype lt2 b).
  Proof.
    intros Hsub.
    iIntros (qL) "HL #CTX #HE". iIntros (??).
    iPoseProof (Hsub  with "HL CTX HE") as "Hsub".
    iApply (owned_ptr_ltype_incl with "Hsub").
  Qed.
  Lemma owned_ptr_full_eqltype E L {rt} (lt1 lt2 : ltype rt) b :
    full_eqltype E L lt1 lt2 →
    full_eqltype E L (OwnedPtrLtype lt1 b) (OwnedPtrLtype lt2 b).
  Proof.
    intros Hsub.
    apply full_subltype_eqltype; eapply owned_ptr_full_subltype; naive_solver.
  Qed.
End subltype.


(* TODO rules *)

Section rules.
  Context `{!typeGS Σ}.




End rules.
