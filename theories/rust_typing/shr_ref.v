From caesium Require Import derived.
From refinedrust Require Export base type ltypes.
From refinedrust Require Import programs ltype_rules.

Local Definition ref_layout := void_ptr.

(** * Shared references *)
Section shr_ref.
  Context `{typeGS Σ} {rt} (inner : type rt).
  Implicit Types (κ : lft).

  (* this is almost a simple type, but we have to be careful with
    the sharing predicate: we want to obtain the knowledge that l points to
    a location not under a later (to prove the agreement with the ltype unfolding),
     so the simple_type interface doesn't suffice *)
  Program Definition shr_ref κ : type (place_rfn rt) := {|
    ty_sidecond := True;
    ty_own_val π r v :=
      (∃ (l : loc) (ly : layout) (r' : rt),
        ⌜v = val_of_loc l⌝ ∗
        ⌜use_layout_alg inner.(ty_syn_type) = Some ly⌝ ∗ ⌜l `has_layout_loc` ly⌝ ∗
        loc_in_bounds l 0 ly.(ly_size) ∗
        inner.(ty_sidecond) ∗
        place_rfn_interp_shared r r' ∗
        □ |={lftE}=> inner.(ty_shr) κ π r' l)%I;

    _ty_has_op_type ot mt := is_ptr_ot ot;
    ty_syn_type := PtrSynType;

    ty_shr κ' π r l :=
      (∃ (li : loc) (ly : layout) (ri : rt),
        ⌜l `has_layout_loc` void*⌝ ∗
        (*loc_in_bounds l void*.(ly_size) ∗*)
        ⌜use_layout_alg inner.(ty_syn_type) = Some ly⌝ ∗
        ⌜li `has_layout_loc` ly⌝ ∗
        loc_in_bounds li 0 ly.(ly_size) ∗
        inner.(ty_sidecond) ∗
        place_rfn_interp_shared r ri ∗
        &frac{κ'} (λ q, l ↦{q} li) ∗ ▷ □ |={lftE}=> inner.(ty_shr) (κ) π ri li)%I;
    ty_ghost_drop _ _ := True%I;
    ty_lfts := κ :: inner.(ty_lfts);
    ty_wf_E := ty_outlives_E inner κ;
  |}.
  Next Obligation. iIntros (????) "(%l & %ly & %r' & -> & ? & ? & ?)". eauto. Qed.
  Next Obligation.
    iIntros (? ot Hot) => /=. destruct ot => /=// -> //.
  Qed.
  Next Obligation. iIntros (????) "_". done. Qed.
  Next Obligation. iIntros (?????) "_". done. Qed.
  Next Obligation.
    iIntros (?????). simpl. iIntros "(%l' & %ly & %r' & ? & ? & ? & _)". eauto.
  Qed.
  Next Obligation.
    iIntros (κ E κ' l ly π r q ?) "#[LFT TIME] Htok %Halg %Hly _ Hb".
    simpl. rewrite -{1}lft_tok_sep -{1}lft_tok_sep.
    iDestruct "Htok" as "(Htok_κ' & Htok_κ & Htok)".
    iApply fupd_logical_step.
    iMod (bor_exists with "LFT Hb") as "(%v & Hb)"; first solve_ndisj.
    iMod (bor_sep with "LFT Hb") as "[Hl Hb]"; first solve_ndisj.
    iMod (bor_exists with "LFT Hb") as "(%l' & Hb)"; first solve_ndisj.
    iMod (bor_exists with "LFT Hb") as "(%ly' & Hb)"; first solve_ndisj.
    iMod (bor_exists_tok with "LFT Hb Htok_κ'") as "(%r' & Hb & Htok_κ')"; first solve_ndisj.
    iMod (bor_sep with "LFT Hb") as "(Heq & Hb)"; first solve_ndisj.
    iMod (bor_persistent with "LFT Heq Htok_κ'") as "(>-> & Htok_κ')"; first solve_ndisj.
    iMod (bor_persistent with "LFT Hb Htok_κ'") as "(Ha & Htok_κ')"; first solve_ndisj.
    iDestruct "Ha" as "(>%Halg' & >%Hly' & >#Hlb & >#Hsc & >Hrfn & Hshr)".
    iMod (bor_fracture (λ q, l ↦{q} l')%I with "LFT Hl") as "Hl"; first solve_ndisj.
    iModIntro.
    iApply logical_step_intro.
    rewrite -!lft_tok_sep. iFrame.
    iExists l', ly', r'.
    iSplitR. { inversion Halg; subst; done. }
    iSplitR; first done. iSplitR; first done.
    iSplitR; first done. iSplitR; first done.
    iFrame.
  Qed.
  Next Obligation.
    iIntros (? κ' κ'' π r l) "#Hord H".
    iDestruct "H" as (li ly ri) "(? & ? & ? & Hlb & Hsc & Hr & #Hf & #Hown)".
    iExists li, ly, ri. iFrame. iSplit.
    - by iApply (frac_bor_shorten with "Hord").
    - iNext. iDestruct "Hown" as "#Hown". iModIntro. iMod "Hown". iModIntro.
      done.
  Qed.
  Next Obligation.
    iIntros (??????) "Ha".
    iApply logical_step_intro. done.
  Qed.
  Next Obligation.
    iIntros (? ot mt st ? r ? Hot).
    destruct mt.
    - eauto.
    - iIntros "(%l & %ly & %ri & -> & ? & ? & ?)".
      iExists l, ly, ri. iFrame.
      iPureIntro. move: ot Hot => [] /=// _.
      rewrite /mem_cast val_to_of_loc //.
    - iApply (mem_cast_compat_loc (λ v, _)); first done.
      iIntros "(%l & %ly & %ri & -> & _)". eauto.
  Qed.

  Global Instance shr_ref_copyable κ : Copyable (shr_ref κ).
  Proof.
    constructor; first apply _.
    iIntros (κ' π E  F l ly r ? ? Ha ?) "[LFT TIME] (%li & %ly' & %r' & %Hly' & % & % & #Hlb & #Hsc & #Hr & Hf & #Hown) Htok Hlft".
    iDestruct (na_own_acc with "Htok") as "[$ Htok]"; first solve_ndisj.
    iMod (frac_bor_acc with "LFT Hf Hlft") as (q') "[Hmt Hclose]"; first solve_ndisj.
    iModIntro.
    assert (ly = void*) as ->. { injection Ha. done. }
    iSplitR; first done.
    iExists _, li. iDestruct "Hmt" as "[Hmt1 Hmt2]".
    iSplitL "Hmt1". { iNext. iFrame "Hmt1". iExists li, ly', r'. iFrame "#". eauto. }
    iIntros "Htok2 Hmt1".
    iDestruct ("Htok" with "Htok2") as "$".
    iApply "Hclose". iModIntro. rewrite -{3}(Qp.div_2 q').
    iPoseProof (heap_mapsto_agree with "Hmt1 Hmt2") as "%Heq"; first done.
    rewrite heap_mapsto_fractional. iFrame.
  Qed.
End shr_ref.

Section ofty.
  Context `{!typeGS Σ}.

  (** A very fundamental equivalence that should hold *)
  Lemma shr_ref_ofty_shared_equiv {rt} (ty : type rt) π κ l r :
    l ◁ₗ[π, Shared κ] #r @ (◁ ty) ⊣⊢ l ◁ᵥ{π} #r @ shr_ref ty κ.
  Proof.
    rewrite ltype_own_ofty_unfold/lty_of_ty_own /ty_own_val/=.
    iSplit.
    - iIntros "(%ly & %Hst & %Hly & #Hsc & #Hlb & %r' & <- & #Ha)".
      iExists _, _, _. iR. iR. iR. iFrame "#". done.
    -iIntros "(%l' & %ly & %r' & %Hl & % & % & #Hsc & #Hlb & <- & #Ha)".
      apply val_of_loc_inj in Hl. subst.
      iExists _. iR. iR. iFrame "#". iExists _. iR. done.
  Qed.
End ofty.

Section subtype.
  Context `{typeGS Σ}.

  Lemma shr_ref_own_val_mono_in {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) v π r1 r2 κ1 κ2 :
    κ1 ⊑ κ2 -∗
    type_incl r1 r2 ty1 ty2 -∗
    v ◁ᵥ{π} #r1 @ shr_ref ty1 κ2 -∗
    v ◁ᵥ{π} #r2 @ shr_ref ty2 κ1.
  Proof.
    iIntros "#Hincl (%Hst_eq & #Hsc_eq & _ & #Hincl_shr)".
    iIntros "(%l & %ly & %r' & -> & ? & ? & Hlb & Hsc & -> & #Hl)". iExists l, ly, r2.
    iSplitR; first done. rewrite -Hst_eq. iFrame.
    iSplitL "Hsc". { by iApply "Hsc_eq". }
    iR. iModIntro. iMod "Hl". iModIntro.
    iApply ty_shr_mono; first iApply "Hincl".
    by iApply "Hincl_shr".
  Qed.
  Lemma shr_ref_own_val_mono {rt} `{!Inhabited rt} (ty1 ty2 : type rt) v π r κ1 κ2 :
    κ1 ⊑ κ2 -∗
    (∀ r, type_incl r r ty1 ty2) -∗
    v ◁ᵥ{π} r @ shr_ref ty1 κ2 -∗
    v ◁ᵥ{π} r @ shr_ref ty2 κ1.
  Proof.
    iIntros "#Hincl #Hsub".
    iDestruct ("Hsub" $! inhabitant) as "(%Hst_eq & #Hsc_eq & _)".
    iIntros "(%l & %ly & %r' & -> & ? & ? & Hlb & Hsc & Hr & #Hl)". iExists l, ly, r'.
    iSplitR; first done. rewrite -Hst_eq. iFrame.
    iSplitL "Hsc". { by iApply "Hsc_eq". }
    iModIntro. iMod "Hl". iModIntro.
    iPoseProof ("Hsub" $! r') as "(_ & _ & _ & #Hincl_shr)".
    iApply ty_shr_mono; first iApply "Hincl".
    by iApply "Hincl_shr".
  Qed.

  Lemma shr_ref_shr_mono_in {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) l π κ r1 r2 κ1 κ2 :
    κ1 ⊑ κ2 -∗
    type_incl r1 r2 ty1 ty2 -∗
    l ◁ₗ{π, κ} #r1 @ shr_ref ty1 κ2 -∗
    l ◁ₗ{π, κ} #r2 @ shr_ref ty2 κ1.
  Proof.
    iIntros "#Hincl (%Hst_eq & #Hsc_eq & _ & #Hincl_shr)".
    iIntros "(%li & %ly & %r' & ? & ? & ? & Hlb & Hsc & -> & Hli & #Hb)".
    iExists li, ly, r2. rewrite Hst_eq. iFrame.
    iSplitL "Hsc". { by iApply "Hsc_eq". }
    iR. iModIntro. iDestruct "Hb" as "#Hb". iModIntro. iMod "Hb". iModIntro.
    iApply ty_shr_mono; first iApply "Hincl".
    by iApply "Hincl_shr".
  Qed.
  Lemma shr_ref_shr_mono {rt} `{!Inhabited rt} (ty1 ty2 : type rt) l π κ r κ1 κ2 :
    κ1 ⊑ κ2 -∗
    (∀ r, type_incl r r ty1 ty2) -∗
    l ◁ₗ{π, κ} r @ shr_ref ty1 κ2 -∗
    l ◁ₗ{π, κ} r @ shr_ref ty2 κ1.
  Proof.
    iIntros "#Hincl #Hsub".
    iPoseProof ("Hsub" $! inhabitant) as "(%Hst_eq & #Hsc_eq & _)".
    iIntros "(%li & %ly & %r' & ? & ? & ? & Hlb & Hsc & Hr & Hli & #Hb)".
    iExists li, ly, r'. rewrite Hst_eq. iFrame.
    iSplitL "Hsc". { by iApply "Hsc_eq". }
    iModIntro. iDestruct "Hb" as "#Hb". iModIntro. iMod "Hb". iModIntro.
    iPoseProof ("Hsub" $! r') as "(_ & _ & _ & #Hincl_shr)".
    iApply ty_shr_mono; first iApply "Hincl".
    by iApply "Hincl_shr".
  Qed.

  Lemma shr_ref_type_incl_in {rt1 rt2} κ2 κ1 (ty1 : type rt1) (ty2 : type rt2) r1 r2 :
    κ1 ⊑ κ2 -∗
    type_incl r1 r2 ty2 ty1 -∗
    type_incl #r1 #r2 (shr_ref ty2 κ2) (shr_ref ty1 κ1).
  Proof.
    iIntros "#Hincl #Hsub".
    iSplitR; first done. iSplitR; first done.
    iSplit; iIntros "!#".
    - iIntros (??). by iApply shr_ref_own_val_mono_in.
    - iIntros (???). by iApply shr_ref_shr_mono_in.
  Qed.
  Lemma shr_ref_type_incl {rt} `{!Inhabited rt} κ2 κ1 (ty1 ty2 : type rt) r :
    κ1 ⊑ κ2 -∗
    (∀ r, type_incl r r ty2 ty1) -∗
    type_incl r r (shr_ref ty2 κ2) (shr_ref ty1 κ1).
  Proof.
    iIntros "#Hincl #Hsub".
    iSplitR; first done. iSplitR; first done.
    iSplit; iIntros "!#".
    - iIntros (??). by unshelve iApply shr_ref_own_val_mono.
    - iIntros (???). by unshelve iApply shr_ref_shr_mono.
  Qed.

  Lemma shr_ref_full_subtype {rt} `{!Inhabited rt} E L κ2 κ1 (ty1 ty2 : type rt) :
    lctx_lft_incl E L κ1 κ2 →
    full_subtype E L ty2 ty1 →
    full_subtype E L (shr_ref ty2 κ2) (shr_ref ty1 κ1).
  Proof.
    iIntros (Hincl Hsubt r ?) "HL #HE".
    iPoseProof (Hincl with "HL") as "#Hincl".
    iSpecialize ("Hincl" with "HE").
    iPoseProof (full_subtype_acc_noend with "HE HL") as "#Hsubt"; first apply Hsubt.
    unshelve iApply shr_ref_type_incl; done.
  Qed.
End subtype.


Section subltype.
  Context `{!typeGS Σ}.

  (** Shared references *)
  Local Lemma shr_ltype_incl'_shared_in {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κ' r1 r2 κ1 κ2 :
    ltype_incl (Shared (κ1)) r1 r2 lt1 lt2 -∗
    κ2 ⊑ κ1 -∗
    ltype_incl' (Shared κ') #(r1) #(r2) (ShrLtype lt1 κ1) (ShrLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1".
    iModIntro.
    iIntros (π l). rewrite !ltype_own_shr_ref_unfold /shr_ltype_own.
    iIntros "(%ly & ? & ? & Hlb & %ri & Hrfn & #Hb)".
    iExists ly. iFrame. rewrite -?Hd -?Hly_eq. iFrame.
    iDestruct "Hrfn" as "->".
    iExists r2. iSplitR; first done. iModIntro. iMod "Hb".
    iDestruct "Hb" as "(%li & Hs & Hb)". iModIntro. iExists li. iFrame. iNext.
    iDestruct "Heq" as "(_ & Hi1 & _)".
    iApply ltype_own_shr_mono; last by iApply "Hi1". done.
  Qed.
  Lemma shr_ltype_incl_shared_in {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κ' r1 r2 κ1 κ2 :
    ltype_incl (Shared (κ1)) r1 r2 lt1 lt2 -∗
    κ2 ⊑ κ1 -∗
    ltype_incl (Shared κ') #(r1) #(r2) (ShrLtype lt1 κ1) (ShrLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1".
    iPoseProof (ltype_incl_syn_type with "Heq") as "%Hst".
    iSplitR; first done. iModIntro.
    simp_ltypes.
    iSplit; (iApply shr_ltype_incl'_shared_in; [ | done  ]).
    - done.
    - iApply ltype_incl_core. done.
  Qed.

  Local Lemma shr_ltype_incl'_shared {rt} (lt1 lt2 : ltype rt) κ' r κ1 κ2 :
    (∀ r, ltype_incl (Shared (κ1)) r r lt1 lt2) -∗
    κ2 ⊑ κ1 -∗
    ltype_incl' (Shared κ') r r (ShrLtype lt1 κ1) (ShrLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1".
    iModIntro.
    iIntros (π l). rewrite !ltype_own_shr_ref_unfold /shr_ltype_own.
    iIntros "(%ly & ? & ? & Hlb & %ri & Hrfn & #Hb)".
    iExists ly. iFrame. rewrite -?Hd -?Hly_eq. iFrame.
    iExists ri. iFrame. iModIntro. iMod "Hb".
    iDestruct "Hb" as "(%li & Hs & Hb)". iModIntro. iExists li. iFrame. iNext.
    iDestruct ("Heq" $! _) as "(_ & Hi1 & _)".
    iApply ltype_own_shr_mono; last by iApply "Hi1". done.
  Qed.
  Lemma shr_ltype_incl_shared {rt} (lt1 : ltype rt) (lt2 : ltype rt) κ' r κ1 κ2 :
    (∀ r, ltype_incl (Shared (κ1)) r r lt1 lt2) -∗
    κ2 ⊑ κ1 -∗
    ltype_incl (Shared κ') r r (ShrLtype lt1 κ1) (ShrLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1".
    iPoseProof (ltype_incl_syn_type _ inhabitant with "Heq") as "%Hst".
    iSplitR; first done. iModIntro.
    simp_ltypes.
    iSplit; (iApply shr_ltype_incl'_shared; [ | done  ]).
    - done.
    - iIntros (?). iApply ltype_incl_core. done.
  Qed.

  Local Lemma shr_ltype_incl'_owned_in {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κ1 κ2 wl r1 r2 :
    ltype_incl (Shared κ1) r1 r2 lt1 lt2  -∗
    κ2 ⊑ κ1 -∗
    ltype_incl' (Owned wl) #(r1) #(r2) (ShrLtype lt1 κ1) (ShrLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1". iModIntro.
    iIntros (π l). rewrite !ltype_own_shr_ref_unfold /shr_ltype_own.
    iIntros "(%ly & ? & ? & Hlb & ? & %ri & Hrfn & Hb)".
    iModIntro.
    iExists ly. iFrame. rewrite -?Hd -?Hly_eq.
    iFrame. iDestruct "Hrfn" as "->". iExists r2. iSplitR; first done. iNext.
    iMod "Hb" as "(%li & Hli & Hb)". iExists li. iFrame "Hli".
    iDestruct "Heq" as "(_ & Heq & _)".
    iApply ltype_own_shr_mono; last by iApply "Heq". done.
  Qed.
  Lemma shr_ltype_incl_owned_in {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κ1 κ2 wl r1 r2 :
    ltype_incl (Shared κ1) r1 r2 lt1 lt2  -∗
    κ2 ⊑ κ1 -∗
    ltype_incl (Owned wl) #(r1) #(r2) (ShrLtype lt1 κ1) (ShrLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1".
    iPoseProof (ltype_incl_syn_type with "Heq") as "%Hst".
    iSplitR; first done. iModIntro.
    simp_ltypes.
    iSplit; (iApply shr_ltype_incl'_owned_in; [ | done  ]).
    - done.
    - iApply ltype_incl_core. done.
  Qed.

  Local Lemma shr_ltype_incl'_owned {rt} (lt1 lt2 : ltype rt) κ1 κ2 wl r :
    (∀ r, ltype_incl (Shared κ1) r r lt1 lt2) -∗
    κ2 ⊑ κ1 -∗
    ltype_incl' (Owned wl) r r (ShrLtype lt1 κ1) (ShrLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1". iModIntro.
    iIntros (π l). rewrite !ltype_own_shr_ref_unfold /shr_ltype_own.
    iIntros "(%ly & ? & ? & Hlb & ? & %ri & Hrfn & Hb)".
    iModIntro.
    iExists ly. iFrame. rewrite -?Hd -?Hly_eq.
    iFrame. iExists ri. iFrame. iNext.
    iMod "Hb" as "(%li & Hli & Hb)". iExists li. iFrame "Hli".
    iDestruct ("Heq" $! _) as "(_ & Heq' & _)".
    iApply ltype_own_shr_mono; last by iApply "Heq'". done.
  Qed.
  Lemma shr_ltype_incl_owned {rt} (lt1 : ltype rt) (lt2 : ltype rt) κ1 κ2 wl r :
    (∀ r, ltype_incl (Shared κ1) r r lt1 lt2)  -∗
    κ2 ⊑ κ1 -∗
    ltype_incl (Owned wl) r r (ShrLtype lt1 κ1) (ShrLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1".
    iPoseProof (ltype_incl_syn_type (Shared _) inhabitant with "Heq") as "%Hst".
    iSplitR; first done. iModIntro.
    simp_ltypes.
    iSplit; (iApply shr_ltype_incl'_owned; [ | done  ]).
    - done.
    - iIntros (?). iApply ltype_incl_core. done.
  Qed.

  (* Refinement subtyping under mutable references is restricted: we need to make sure that, no matter the future updates,
     we can always get back to what the lender expects. Thus we loose all refinement information when descending below mutable references. *)
  Local Lemma shr_ltype_incl'_uniq {rt} (lt1 lt2 : ltype rt) κ1 κ2 κ r γ :
    (∀ r, ltype_eq (Shared (κ1)) r r lt1 lt2) -∗
    (* Note: requires mutual inclusion, because we may be below a mutable reference *)
    κ2 ⊑ κ1 -∗
    κ1 ⊑ κ2 -∗
    ltype_incl' (Uniq κ γ) r r (ShrLtype lt1 κ1) (ShrLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1 #Hincl2". iModIntro.
    iIntros (π l). rewrite !ltype_own_shr_ref_unfold /shr_ltype_own.
    iIntros "(%ly & ? & ? & Hlb & ? &  Hrfn & Hb)".
    iExists ly. iFrame. rewrite -?Hly_eq. iFrame.
    iMod "Hb". iModIntro. iApply (pinned_bor_iff with "[] [] Hb").
    + iNext. iModIntro. iSplit.
      * iIntros "(%ri & Hauth & Hb)". iExists ri. iFrame.
        iMod "Hb" as "(%li & Hl & Hb)". iModIntro. iExists _. iFrame.
        iDestruct ("Heq" $! ri) as "((_ & Hi & _) & _)".
        iApply ltype_own_shr_mono; last by iApply "Hi". done.
      * iIntros "(%ri & Hauth & Hb)". iExists ri. iFrame.
        iMod "Hb" as "(%li & Hl & Hb)". iModIntro. iExists _. iFrame.
        iDestruct ("Heq" $! ri) as "(_ & (_ & Hi & _))".
        iApply "Hi"; last by iApply ltype_own_shr_mono.
    + (* the same proof *)
      iNext. iModIntro. iSplit.
      * iIntros "(%ri & Hauth & Hb)". iExists ri. iFrame.
        iMod "Hb" as "(%li & Hl & Hb)". iModIntro. iExists _. iFrame.
        iDestruct ("Heq" $! ri) as "((_ & _ & Hi) & _)".
        rewrite !ltype_own_core_equiv.
        iApply ltype_own_shr_mono; last by iApply "Hi". done.
      * iIntros "(%ri & Hauth & Hb)". iExists ri. iFrame.
        iMod "Hb" as "(%li & Hl & Hb)". iModIntro. iExists _. iFrame.
        iDestruct ("Heq" $! ri) as "(_ & (_ & _ & Hi))".
        rewrite !ltype_own_core_equiv.
        iApply "Hi"; last by iApply ltype_own_shr_mono.
  Qed.
  Lemma shr_ltype_incl_uniq {rt} (lt1 lt2 : ltype rt) κ1 κ2 κ r γ :
    (∀ r, ltype_eq (Shared (κ1)) r r lt1 lt2) -∗
    κ2 ⊑ κ1 -∗
    κ1 ⊑ κ2 -∗
    ltype_incl (Uniq κ γ) r r (ShrLtype lt1 κ1) (ShrLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1 #Hincl2".
    iPoseProof (ltype_eq_syn_type _ inhabitant with "Heq") as "%Hst".
    iSplitR; first done. iModIntro.
    simp_ltypes.
    iSplit; (iApply shr_ltype_incl'_uniq; [ | done  | done]).
    - done.
    - iIntros (?). iApply ltype_eq_core. done.
  Qed.

  Lemma shr_ltype_incl {rt} (lt1 lt2 : ltype rt) b r κ1 κ2 :
    (∀ b r, ltype_eq b r r lt1 lt2) -∗
    κ2 ⊑ κ1 -∗
    κ1 ⊑ κ2 -∗
    ltype_incl b r r (ShrLtype lt1 κ1) (ShrLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1 #Hincl2".
    destruct b.
    - iApply shr_ltype_incl_owned; last done. iIntros (?). iDestruct ("Heq" $! _ _) as "[$ _]".
    - iApply shr_ltype_incl_shared; last done. iIntros (?). iDestruct ("Heq" $! _ _) as "[$ _]".
    - iApply shr_ltype_incl_uniq; [ | done..]. iIntros (?). done.
  Qed.
  Lemma shr_ltype_eq {rt} (lt1 lt2 : ltype rt) b r κ1 κ2 :
    (∀ b r, ltype_eq b r r lt1 lt2) -∗
    κ2 ⊑ κ1 -∗
    κ1 ⊑ κ2 -∗
    ltype_eq b r r (ShrLtype lt1 κ1) (ShrLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1 #Hincl2".
    iSplit.
    - iApply shr_ltype_incl; done.
    - iApply shr_ltype_incl; [ | done..]. iIntros (??). iApply ltype_eq_sym. done.
  Qed.

  Lemma shr_full_subltype E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 :
    full_eqltype E L lt1 lt2 →
    lctx_lft_incl E L κ1 κ2 →
    lctx_lft_incl E L κ2 κ1 →
    full_subltype E L (ShrLtype lt1 κ1) (ShrLtype lt2 κ2).
  Proof.
    intros Hsub Hincl1 Hincl2.
    iIntros (qL) "HL #CTX #HE". iIntros (??).
    iPoseProof (lctx_lft_incl_incl_noend with "HL HE") as "#Hincl1"; first apply Hincl1.
    iPoseProof (lctx_lft_incl_incl_noend with "HL HE") as "#Hincl2"; first apply Hincl2.
    iPoseProof (Hsub  with "HL CTX HE") as "Hsub".
    iApply (shr_ltype_incl with "Hsub Hincl2 Hincl1").
  Qed.
  Lemma shr_full_eqltype E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 :
    full_eqltype E L lt1 lt2 →
    lctx_lft_incl E L κ1 κ2 →
    lctx_lft_incl E L κ2 κ1 →
    full_eqltype E L (ShrLtype lt1 κ1) (ShrLtype lt2 κ2).
  Proof.
    intros Hsub Hincl1 Hincl2.
    apply full_subltype_eqltype; eapply shr_full_subltype; naive_solver.
  Qed.
End subltype.

Section ltype_agree.
  Context `{typeGS Σ}
    {rt}
    (ty : type rt).

  Lemma shr_ref_unfold_1_owned κ wl r :
    ⊢ ltype_incl' (Owned wl) r r (ShrLtype (◁ ty) κ) (◁ (shr_ref ty κ)).
  Proof.
    iModIntro. iIntros (π l). rewrite ltype_own_shr_ref_unfold /shr_ltype_own ltype_own_ofty_unfold /lty_of_ty_own.
    iIntros "(%ly & ? & ? & #Hlb & ? &  %ri & Hrfn & Hb)".
    iModIntro.
    iExists ly.
    iFrame. iFrame "Hlb". iExists _. iFrame. iNext. iMod "Hb" as "(%l' & Hl & Hb)".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hb" as "(%ly' & ? & ? & Hsc & Hlb' & %ri' & Hrfn' & Hb)".
    iExists l'. iFrame. iExists l', _, _. iFrame. done.
  Qed.
  Lemma shr_ref_unfold_1_shared `{!Inhabited rt} κ κ' r :
    ⊢ ltype_incl' (Shared κ') r r (ShrLtype (◁ ty) κ) (◁ (shr_ref ty κ)).
  Proof.
    iModIntro. iIntros (π l). rewrite ltype_own_shr_ref_unfold /shr_ltype_own ltype_own_ofty_unfold /lty_of_ty_own.
    iIntros "(%ly & %Ha & % & #Hlb & %ri & Hrfn & #Hb)".
    iExists ly. iFrame. iFrame "Hlb %". iExists _. iFrame.
    iModIntro. iMod "Hb".
    iDestruct "Hb" as "(%li & #Hs & Hb)".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hb" as "(%ly' & >? & >? & >Hsc & >Hlb' & %r' & >Hrfn & Hb)". iModIntro.
    iExists _, _, _. iFrame. iSplitR; last done.
    injection Ha as <-. done.
  Qed.
  Lemma shr_ref_unfold_1_uniq κ κ' γ r :
    ⊢ ltype_incl' (Uniq κ' γ) r r (ShrLtype (◁ ty) κ) (◁ (shr_ref ty κ)).
  Proof.
    iModIntro. iIntros (π l). rewrite ltype_own_shr_ref_unfold /shr_ltype_own ltype_own_ofty_unfold /lty_of_ty_own.
    iIntros "(%ly & ? & ? & ? & ? & ?  & Hb)". iExists ly. iFrame. iMod "Hb". iModIntro.
    iApply (pinned_bor_iff with "[] [] Hb").
    - iNext. iModIntro. iSplit.
      * iIntros "(%r' & Hauth & Hb)". iExists _. iFrame.
        iMod "Hb" as "(%l' & Hl & Hb)". iExists l'. iFrame.
        rewrite ltype_own_ofty_unfold /lty_of_ty_own.
        iDestruct "Hb" as "(%ly' & ? & ? & Hsc & Hlb & %ri & Hrfn & Hb)".
        iExists l', ly', _. iFrame. done.
      * iIntros "(%r' & Hauth & Hb)". iExists _; iFrame.
        iMod "Hb" as "(%v & Hl & Hb)".
        iDestruct "Hb" as "(%li & %ly' & %ri & -> & ? & ? & Hlb & Hsc & Hrfn & Hb)".
        iExists _. iFrame. rewrite ltype_own_ofty_unfold /lty_of_ty_own.
        iFrame. iExists ly'. iFrame.
        iExists _. by iFrame.
    - iNext. iModIntro. iSplit.
      * iIntros "(%r' & Hauth & Hb)". iExists _. iFrame.
        iMod "Hb" as "(%l' & Hl & Hb)". iExists l'. iFrame.
        rewrite ltype_own_core_equiv. simp_ltypes.
        rewrite ltype_own_ofty_unfold /lty_of_ty_own.
        iDestruct "Hb" as "(%ly' & ? & ? & Hsc & Hlb & %ri & Hrfn & Hb)".
        iExists l', ly', _. iFrame. done.
      * iIntros "(%r' & Hauth & Hb)". iExists _; iFrame.
        iMod "Hb" as "(%v & Hl & Hb)".
        iDestruct "Hb" as "(%li & %ly' & %ri & -> & ? & ? & Hlb & Hsc & Hrfn & Hb)".
        iExists _. iFrame.
        rewrite ltype_own_core_equiv. simp_ltype.
        rewrite ltype_own_ofty_unfold /lty_of_ty_own.
        iFrame. iExists ly'. iFrame.
        iExists _. by iFrame.
  Qed.

  Local Lemma shr_ref_unfold_1' `{!Inhabited rt} κ k r :
    ⊢ ltype_incl' k r r (ShrLtype (◁ ty) κ) (◁ (shr_ref ty κ)).
  Proof.
    iModIntro. destruct k.
    - iApply shr_ref_unfold_1_owned.
    - iApply shr_ref_unfold_1_shared.
    - iApply shr_ref_unfold_1_uniq.
  Qed.
  Lemma shr_ref_unfold_1 `{!Inhabited rt} κ k r :
    ⊢ ltype_incl k r r (ShrLtype (◁ ty) κ) (◁ (shr_ref ty κ)).
  Proof.
    iSplitR; first done. iModIntro. iSplit.
    - iApply shr_ref_unfold_1'.
    - simp_ltypes. iApply shr_ref_unfold_1'.
  Qed.

  Lemma shr_ref_unfold_2_owned κ wl r :
    ⊢ ltype_incl' (Owned wl) r r (◁ (shr_ref ty κ)) (ShrLtype (◁ ty) κ).
  Proof.
    iModIntro. iIntros (π l). rewrite ltype_own_shr_ref_unfold /shr_ltype_own ltype_own_ofty_unfold /lty_of_ty_own.
    iIntros "(%ly & ? & ? & Hsc & Hlb & ? & %r' & Hrfn & Hb)".
    iModIntro. iExists ly. iFrame. iExists _. iFrame.
    iNext. iMod "Hb" as "(%v & Hl & %li & %ly' & %ri & -> & ? & ? & Hlb' & Hsc' & Hrfn' & Hb)".
    iExists _. iFrame. rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iExists ly'. iFrame.
    iExists _. by iFrame.
  Qed.
  Lemma shr_ref_unfold_2_shared κ κ' r :
    ⊢ ltype_incl' (Shared κ') r r (◁ (shr_ref ty κ)) (ShrLtype (◁ ty) κ).
  Proof.
    iModIntro. iIntros (π l). rewrite ltype_own_shr_ref_unfold /shr_ltype_own ltype_own_ofty_unfold /lty_of_ty_own.
    iIntros "(%ly & ? & ? & Hsc & Hlb & %r' & Hrfn & #Hb)". iExists ly. iFrame.
    iExists r'. iFrame. iModIntro. iMod "Hb".
    iDestruct "Hb" as "(%li & %ly' & %ri & ? & ? & ? & Hlb' & Hsc & Hrfn & Hs & Hb)".
    iModIntro. iExists _. iFrame. iNext. iDestruct "Hb" as "#Hb".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iExists ly'. iFrame.
    iExists _. iFrame. done.
  Qed.
  Lemma shr_ref_unfold_2_uniq κ κ' γ r :
    ⊢ ltype_incl' (Uniq κ' γ) r r (◁ (shr_ref ty κ)) (ShrLtype (◁ ty) κ).
  Proof.
    iModIntro. iIntros (π l). rewrite ltype_own_shr_ref_unfold /shr_ltype_own ltype_own_ofty_unfold /lty_of_ty_own.
    (* same proof as above essentially *)
    iIntros "(%ly & ? & ? & Hsc & ? & ? & ? & Hb)". iExists ly. iFrame. iMod "Hb". iModIntro.
    iApply (pinned_bor_iff with "[] [] Hb").
    - iNext. iModIntro. iSplit.
      * iIntros "(%r' & Hauth & Hb)". iExists _. iFrame.
        iMod "Hb" as "(%v & Hl & Hb)".
        iDestruct "Hb" as "(%li & %ly' & %ri & -> & ? & ? & Hlb & Hsc & Hrfn & Hb)".
        iExists _. iFrame. rewrite ltype_own_ofty_unfold /lty_of_ty_own.
        iExists ly'. iFrame.
        iExists _. by iFrame.
      * iIntros "(%r' & Hauth & Hb)". iExists _. iFrame.
        iMod "Hb" as "(%l' & Hl & Hb)".
        iExists l'. iFrame. rewrite ltype_own_ofty_unfold /lty_of_ty_own.
        iDestruct "Hb" as "(%ly' & ? & ? & Hsc & Hlb & %ri & Hrfn & Hb)".
        iExists l', _, _. iFrame. done.
    - iNext. iModIntro. iSplit.
      * iIntros "(%r' & Hauth & Hb)". iExists _. iFrame.
        iMod "Hb" as "(%v & Hl & Hb)".
        iDestruct "Hb" as "(%li & %ly' & %ri & -> & ? & ? & Hlb & Hsc & Hrfn & Hb)".
        iExists _. iFrame. rewrite ltype_own_core_equiv. simp_ltypes.
        rewrite ltype_own_ofty_unfold /lty_of_ty_own.
        iExists ly'. iFrame.
        iExists _. by iFrame.
      * iIntros "(%r' & Hauth & Hb)". iExists _. iFrame.
        iMod "Hb" as "(%l' & Hl & Hb)".
        iExists l'. iFrame. rewrite ltype_own_core_equiv. simp_ltype.
        rewrite ltype_own_ofty_unfold /lty_of_ty_own.
        iDestruct "Hb" as "(%ly' & ? & ? & Hsc & Hlb & %ri & Hrfn & Hb)".
        iExists l', _, _. iFrame. done.
  Qed.


  Local Lemma shr_ref_unfold_2' κ k r :
    ⊢ ltype_incl' k r r (◁ (shr_ref ty κ)) (ShrLtype (◁ ty) κ).
  Proof.
    destruct k.
    - iApply shr_ref_unfold_2_owned.
    - iApply shr_ref_unfold_2_shared.
    - iApply shr_ref_unfold_2_uniq.
  Qed.
  Lemma shr_ref_unfold_2 κ k r :
    ⊢ ltype_incl k r r (◁ (shr_ref ty κ)) (ShrLtype (◁ ty) κ).
  Proof.
    iSplitR; first done. iModIntro; iSplit.
    - iApply shr_ref_unfold_2'.
    - simp_ltypes. iApply shr_ref_unfold_2'.
  Qed.

  Lemma shr_ref_unfold `{!Inhabited rt} κ k r :
    ⊢ ltype_eq k r r (ShrLtype (◁ (ty)) κ) (◁ (shr_ref ty κ)).
  Proof.
    iSplit.
    - iApply shr_ref_unfold_1.
    - iApply shr_ref_unfold_2.
  Qed.

  Lemma shr_ref_unfold_full_eqltype `{!Inhabited rt} E L κ (lt : ltype rt) :
    full_eqltype E L lt (◁ ty)%I →
    full_eqltype E L (ShrLtype lt κ) (◁ (shr_ref ty κ))%I.
  Proof.
    iIntros (Heql ?) "HL #CTX #HE". iIntros (??).
    iPoseProof (Heql with "HL CTX HE") as "#Heql".
    iApply ltype_eq_trans; last iApply shr_ref_unfold.
    iApply shr_ltype_eq; [ | iApply lft_incl_refl.. ].
    by iApply "Heql".
  Qed.
End ltype_agree.

Global Typeclasses Opaque shr_ref.
Notation "&shr< κ , τ >" := (shr_ref τ κ) (only printing, format "'&shr<' κ , τ '>'") : stdpp_scope.

Section acc.
  Context `{!typeGS Σ}.

  Lemma shr_ltype_place_cond_ty b κ {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) :
    typed_place_cond_ty b lt1 lt2 -∗
    typed_place_cond_ty b (ShrLtype lt1 κ) (ShrLtype lt2 κ).
  Proof.
    destruct b; simpl.
    - iIntros "_". done.
    - iIntros "(-> & %)". simp_ltypes. done.
    - iIntros "(%Hrefl & Heq & Hub)".
      subst rt2. cbn.
      iExists eq_refl. cbn. iSplitR "Hub".
      + simp_ltypes. iIntros (??). iApply (shr_ltype_eq with "Heq"); iApply lft_incl_refl.
      + by iApply shr_ltype_imp_unblockable.
  Qed.

  Lemma shr_ltype_acc_owned {rt} F π (lt : ltype rt) (r : place_rfn rt) l κ' wl :
    lftE ⊆ F →
    rrust_ctx -∗
    l ◁ₗ[π, Owned wl] PlaceIn (r) @ ShrLtype lt κ' -∗
    ⌜l `has_layout_loc` void*⌝ ∗ loc_in_bounds l 0 (ly_size void*) ∗ |={F}=>
      ∃ (l' : loc), l ↦ l' ∗ l' ◁ₗ[π, Shared κ'] r @ lt ∗
      logical_step F
      (∀ bmin rt' (lt2 : ltype rt') r2,
        l ↦ l' -∗
        l' ◁ₗ[π, Shared κ'] r2 @ lt2 ={F}=∗
        l ◁ₗ[π, Owned wl] PlaceIn (r2) @ ShrLtype lt2 κ' ∗
        (typed_place_cond bmin lt lt2 r r2 -∗
         ⌜place_access_rt_rel bmin rt rt'⌝ -∗
         typed_place_cond bmin (ShrLtype lt κ') (ShrLtype lt2 κ') (PlaceIn (r)) (PlaceIn (r2)))).
  Proof.
    iIntros (?) "#[LFT TIME] HP".
    rewrite ltype_own_shr_ref_unfold /shr_ltype_own.
    iDestruct "HP" as "(%ly & %Halg & %Hly & #Hlb & Hcred & %r' & %Heq & Hb)".
    injection Halg as <-. subst.
    iFrame "Hlb %".
    iMod (maybe_use_credit with "Hcred Hb") as "(Hcred & Hat & Hb)"; first done.
    iDestruct "Hb" as "(%l' & Hl & Hb)".
    iModIntro. iExists l'. iFrame.
    iApply (logical_step_intro_maybe with "Hat").
    iIntros "Hcred' !>". iIntros (bmin rt2 lt2 r2) "Hl Hb".
    iModIntro. iSplitL.
    - rewrite ltype_own_shr_ref_unfold /shr_ltype_own. iExists void*.
      iSplitR; first done. iFrame "Hlb % ∗".
      iExists _. iSplitR; first done. iNext. eauto with iFrame.
    - iIntros "Hcond %Hrt". iDestruct "Hcond" as "[Hty Hrfn]".
      subst. iSplit.
      + by iApply (shr_ltype_place_cond_ty).
      + destruct bmin; cbn in Hrt; [ done | subst rt2..].
        all: by iApply (typed_place_cond_rfn_lift _ _ _ (λ r, PlaceIn (r))).
  Qed.


  (* Note: this doesn't allow changing the type below the shared reference *)
  Lemma shr_ltype_acc_uniq {rt} F π (lt : ltype rt) (r : place_rfn rt) l κ' κ γ q R :
    lftE ⊆ F →
    rrust_ctx -∗
    q.[κ] -∗
    (q.[κ] ={lftE}=∗ R) -∗
    l ◁ₗ[π, Uniq κ γ] #r @ ShrLtype lt κ' -∗
    ⌜l `has_layout_loc` void*⌝ ∗ loc_in_bounds l 0 (ly_size void*) ∗ |={F}=>
      ∃ l' : loc, l ↦ l' ∗ (l' ◁ₗ[π, Shared κ'] r @ lt) ∗
      logical_step F
      ( (* weak update *)
       (∀ bmin r2,
        l ↦ l' -∗
        l' ◁ₗ[π, Shared κ'] r2 @ lt -∗
        bmin ⊑ₖ Uniq κ γ -∗
        typed_place_cond bmin lt lt r r2 ={F}=∗
        l ◁ₗ[π, Uniq κ γ] #r2 @ ShrLtype lt κ' ∗
        R ∗
        typed_place_cond bmin (ShrLtype lt κ') (ShrLtype lt κ') (#r) (#r2)) ∧
      (* strong update, go to Opened *)
      (∀ rt2 (lt2 : ltype rt2) r2,
        l ↦ l' -∗
        ⌜ltype_st lt2 = ltype_st lt⌝ -∗
        l' ◁ₗ[π, Shared κ'] r2 @ lt2 ={F}=∗
        l ◁ₗ[π, Uniq κ γ] #r2 @ OpenedLtype (ShrLtype lt2 κ') (ShrLtype lt κ') (ShrLtype lt κ')
          (λ r1 r1', ⌜r1 = r1'⌝) (λ _ _, R))).
  Proof.
    iIntros (?) "#[LFT TIME] Hκ HR HP".
    rewrite ltype_own_shr_ref_unfold /shr_ltype_own.
    iDestruct "HP" as "(%ly & %Halg & %Hly & #Hlb & (Hcred & Hat) & Hrfn & Hb)".
    injection Halg as <-. iFrame "Hlb". iSplitR; first done.

    iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
    iMod "Hb".
    (* NOTE: we are currently throwing away the existing "coring"-viewshift that we get *)
    iMod (pinned_bor_acc_strong lftE with "LFT Hb Hκ") as "(%κ'' & #Hincl & Hb & Hx & Hb_cl)"; first done.
    iMod "Hcl_F" as "_".
    iDestruct "Hcred" as "(Hcred1 & Hcred)".
    iApply (lc_fupd_add_later with "Hcred1"). iNext.
    iDestruct "Hb" as "(%r' &  Hauth & Hb)".
    iPoseProof (gvar_agree with "Hauth Hrfn") as "#->".
    iMod (fupd_mask_mono with "Hb") as "(%l' & Hl & Hb)"; first done.
    iModIntro. iExists l'. iFrame.
    iApply (logical_step_intro_atime with "Hat").
    iIntros "Hcred' Hat".
    iModIntro.
    iSplit.
    - (* close *)
      iIntros (bmin r2) "Hl Hb #Hincl_k #Hcond".
      (* extract the necessary info from the place_cond *)
      iPoseProof (typed_place_cond_incl _ (Uniq κ γ) with "Hincl_k Hcond") as "Hcond'".
      iDestruct "Hcond'" as "(Hcond' & _)".
      iDestruct "Hcond'" as "(%Heq & Heq & (#Hub & _))".
      rewrite (UIP_refl _ _ Heq). cbn.
      iPoseProof (typed_place_cond_syn_type_eq with "Hcond") as "%Hst_eq".
      (* close the borrow *)
      iMod (gvar_update r2 with "Hauth Hrfn") as "(Hauth & Hrfn)".
      iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
      iDestruct "Hcred" as "(Hcred1 & Hcred)".
      iMod ("Hb_cl" with "Hx Hcred1 [Hauth Hl Hb]") as "(Hb & Htok)".
      { iModIntro. eauto 8 with iFrame. }
      iMod ("HR" with "Htok") as "$".
      iMod "Hcl_F" as "_".
      iModIntro.
      (* TODO maybe donate the leftover credits *)
      iSplitL.
      { rewrite ltype_own_shr_ref_unfold /shr_ltype_own.
        iExists void*. iFrame. do 3 iR.
        iPoseProof (pinned_bor_shorten with "Hincl Hb") as "Hb".
        iModIntro. done. }
      iDestruct "Hcond" as "(Hcond_ty & Hcond_rfn)".
      iSplit.
      + iApply shr_ltype_place_cond_ty; done.
      + iApply (typed_place_cond_rfn_lift _ _ _ (λ a, #a)). done.
    - (* shift to OpenedLtype *)
      iIntros (rt2 lt2 r2) "Hl %Hst' Hb". iModIntro.
      iDestruct "Hcred" as "(Hcred1 & Hcred)".
      iApply (opened_ltype_create_uniq_simple with "Hrfn Hauth Hcred1 Hat Hincl HR Hb_cl [] [Hcred']"); first done.
      { iModIntro. iIntros (?) "Hauth Hc". simp_ltypes.
        rewrite ltype_own_shr_ref_unfold /shr_ltype_own.
        iExists _. iFrame. iDestruct "Hc" as ">(% & _ & _ & _ & _ & %r' & -> & >(%l0 & Hl & Hb))".
        iModIntro. setoid_rewrite ltype_own_core_equiv.
        iExists _. eauto with iFrame. }
      { iIntros (?) "Hobs Hat Hcred Hp". simp_ltypes.
        rewrite ltype_own_shr_ref_unfold /shr_ltype_own.
        setoid_rewrite ltype_own_core_equiv. rewrite ltype_core_idemp.
        iModIntro. eauto 8 with iFrame. }
      { rewrite ltype_own_shr_ref_unfold /shr_ltype_own.
        iExists void*. do 4 iR.
        iExists r2. iR. iNext. iModIntro. eauto with iFrame. }
  Qed.

  Lemma shr_ltype_acc_shared {rt} F π (lt : ltype rt) r l q κ κ' :
    lftE ⊆ F →
    rrust_ctx -∗
    q.[κ] -∗
    l ◁ₗ[π, Shared κ] #r @ ShrLtype lt κ' -∗
    ⌜l `has_layout_loc` void*⌝ ∗ loc_in_bounds l 0 (ly_size void*) ∗ |={F}=>
      ∃ (l' : loc) q', l ↦{q'} l' ∗ (|={F}▷=> l' ◁ₗ[π, Shared κ'] r @ lt) ∗
    (∀ (lt' : ltype rt) r',
      l ↦{q'} l' -∗
      l' ◁ₗ[π, Shared κ'] r' @ lt' -∗ |={F}=>
      l ◁ₗ[π, Shared κ] #r' @ ShrLtype lt' κ' ∗
      q.[κ] ∗
      (∀ bmin,
      bmin ⊑ₖ Shared κ -∗
      typed_place_cond bmin lt lt' r r' ={F}=∗
      typed_place_cond bmin (ShrLtype lt κ') (ShrLtype lt' κ') #r #r')).
  Proof.
    iIntros (?) "#(LFT & TIME & LLCTX) Hκ Hb". rewrite {1}ltype_own_shr_ref_unfold /shr_ltype_own.
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
    { iModIntro. rewrite ltype_own_shr_ref_unfold /shr_ltype_own. iExists void*. iFrame "% #".
      iR. iExists _. iR. iModIntro. iModIntro. iExists _. iFrame "#". }
    iModIntro. iIntros (bmin) "Hincl Hcond".
    iDestruct "Hcond" as "(Hcond_ty & Hcond_rfn)".
    iModIntro. iSplit.
    + iApply shr_ltype_place_cond_ty; done.
    + destruct bmin; simpl; done.
  Qed.

End acc.


Section rules.
  Context `{!typeGS Σ}.

  Global Instance get_lft_names_shr_ref {rt} (ty : type rt) κ lfts lfts' name tree :
    GetLftNames ty lfts tree lfts' →
    GetLftNames (shr_ref ty κ) lfts (LftNameTreeRef name tree) (named_lft_update name κ lfts') := λ _, GLN.

  Lemma typed_place_shr_owned {rto} π κ (lt2 : ltype rto) P E L l r wl bmin0 (T : place_cont_t (place_rfn rto)) :
    (∀ l', typed_place π E L l' lt2 r (Shared κ ⊓ₖ bmin0) (Shared κ) P
        (λ L' κs l2 b2 bmin rti tyli ri strong weak,
          T L' (κs) l2 b2 bmin rti tyli ri
          (option_map (λ strong, mk_strong
            (λ rti2, (place_rfn (strong.(strong_rt) rti2)))%type
            (λ rti2 lti2 ri2, ShrLtype (strong.(strong_lt) _ lti2 ri2) κ)
            (λ rti2 (r : place_rfn rti2), PlaceIn (strong.(strong_rfn) _ r))
            strong.(strong_R)) strong)
          (fmap (λ weak,  mk_weak
            (λ lti2 ri2, ShrLtype (weak.(weak_lt) lti2 ri2) κ)
            (λ (r : place_rfn rti), PlaceIn (weak.(weak_rfn) r))
            weak.(weak_R)) weak)))
    ⊢ typed_place π E L l (ShrLtype lt2 κ) (#r) bmin0 (Owned wl) (DerefPCtx Na1Ord PtrOp true :: P) T.
  Proof.
    iIntros "HR" (Φ F ??).
    iIntros "#(LFT & TIME & LLCTX) #HE HL Hincl0 HP HΦ/=".
    iPoseProof (shr_ltype_acc_owned F with "[$LFT $TIME $LLCTX] HP") as "(%Hly & Hlb & Hb)"; [done.. | ].
    iApply fupd_wp. iMod (fupd_mask_subseteq F) as "HclF"; first done.
    iMod "Hb" as "(%l' & Hl & Hb & Hcl)". iMod "HclF" as "_". iModIntro.
    iApply (wp_logical_step with "TIME Hcl"); [solve_ndisj.. | ].
    iApply (wp_deref with "Hl") => //; [solve_ndisj | by apply val_to_of_loc | ].
    iNext. iIntros (st) "Hl Hcred Hc". iMod (fupd_mask_subseteq F) as "HclF"; first done.
    iMod "HclF" as "_". iExists l'.
    iSplitR. { iPureIntro. unfold mem_cast. rewrite val_to_of_loc. done. }
    iApply ("HR" with "[//] [//] [$LFT $TIME $LLCTX] HE HL [] Hb"). { iApply bor_kind_min_incl_l. }
    iModIntro. iIntros (L' κs l2 b2 bmin rti tyli ri strong weak) "#Hincl1 Hb Hs".
    iApply ("HΦ" $! _ _ _ _ bmin _ _ _ _ _ with "Hincl1 Hb").
    simpl. iSplit.
    - (* strong *) iDestruct "Hs" as "[Hs _]".
      destruct strong as [ strong | ]; last done.
      iIntros (rti2 ltyi2 ri2) "Hl2 Hcond".
      iMod ("Hs" with "Hl2 Hcond") as "(Hb & Hcond & HR)".
      iMod ("Hc" $! (Owned false) with "Hl Hb") as "(Hb & _)".
      iFrame. iPureIntro. simp_ltypes. done.
    - (* weak *)
      destruct weak as [ weak | ]; last done.
      iDestruct "Hs" as "[_ Hs]".
      iIntros (ltyi2 ri2 bmin').
      iIntros "Hincl2 Hl2 Hcond".
      iMod ("Hs" with "Hincl2 Hl2 Hcond") as "(Hb & Hcond & $ & HR)".
      iMod ("Hc" with "Hl Hb") as "(Hb & Hcond')".
      iPoseProof ("Hcond'" with "Hcond") as "Hcond".
      iModIntro. iFrame "HR Hb".
      iApply typed_place_cond_incl; last iApply "Hcond".
      + iApply bor_kind_min_incl_r.
      + iPureIntro. apply place_access_rt_rel_refl.
  Qed.
  Global Instance typed_place_shr_owned_inst {rto} E L π κ (lt2 : ltype rto) bmin0 r l wl P :
    TypedPlace E L π l (ShrLtype lt2 κ) (PlaceIn (r)) bmin0 (Owned wl) (DerefPCtx Na1Ord PtrOp true :: P) | 30 := λ T, i2p (typed_place_shr_owned π κ lt2 P E L l r wl bmin0 T).

  Lemma typed_place_shr_uniq {rto} π κ (lt2 : ltype rto) P E L l r κ' γ bmin0 (T : place_cont_t (place_rfn rto)) :
    li_tactic (lctx_lft_alive_count_goal E L κ') (λ '(κs, L2),
    (∀ l', typed_place π E L2 l' lt2 r (Shared κ) (Shared κ) P
        (λ L3 κs' l2 b2 bmin rti tyli ri strong weak,
          T L3 (κs' ++ κs) l2 b2 bmin rti tyli ri
            (* strong branch: fold to OpenedLtype *)
            (fmap (λ strong, mk_strong (λ rti, (place_rfn (strong.(strong_rt) rti)))
              (λ rti2 ltyi2 ri2,
                OpenedLtype (ShrLtype (strong.(strong_lt) _ ltyi2 ri2) κ) (ShrLtype lt2 κ) (ShrLtype lt2 κ) (λ r1 r1', ⌜r1 = r1'⌝) (λ _ _, llft_elt_toks κs))
              (λ rti2 ri2, #((strong.(strong_rfn) _ ri2)))
              strong.(strong_R)) strong)
              (* TODO: maybe we should enable weak accesses *)
            (* weak branch: just keep the ShrLtype *)
              (*
            (fmap (λ weak,  mk_weak
            (λ lti2 ri2, ShrLtype (weak.(weak_lt) lti2 ri2) κ)
            (λ (r : place_rfn rti), PlaceIn (weak.(weak_rfn) r))
            weak.(weak_R)) weak)
               *)
              None
        )))
    ⊢ typed_place π E L l (ShrLtype lt2 κ) (#r) bmin0 (Uniq κ' γ) (DerefPCtx Na1Ord PtrOp true :: P) T.
  Proof.
    rewrite /lctx_lft_alive_count_goal.
    iIntros "(%κs & %L2 & %Hal & HT)".
    iIntros (Φ F ??). iIntros "#(LFT & TIME & LLCTX) #HE HL #Hincl0 HP HΦ/=".
    (* get a token *)
    iApply fupd_wp. iMod (fupd_mask_subseteq lftE) as "HclF"; first done.
    iMod (lctx_lft_alive_count_tok lftE with "HE HL") as (q) "(Hκ' & Hclκ' & HL)"; [done.. | ].
    iMod "HclF" as "_". iMod (fupd_mask_subseteq F) as "HclF"; first done.
    iPoseProof (shr_ltype_acc_uniq F with "[$LFT $TIME $LLCTX] Hκ' Hclκ' HP") as "(%Hly & Hlb & Hb)"; [done.. | ].
    iMod "Hb" as "(%l' & Hl & Hb & Hcl)". iMod "HclF" as "_". iModIntro.
    iApply (wp_logical_step with "TIME Hcl"); [solve_ndisj.. | ].
    iApply (wp_deref with "Hl") => //; [solve_ndisj | by apply val_to_of_loc | ].
    iNext. iIntros (st) "Hl Hcred Hc". iMod (fupd_mask_subseteq F) as "HclF"; first done.
    iMod "HclF" as "_". iExists l'.
    iSplitR. { iPureIntro. unfold mem_cast. rewrite val_to_of_loc. done. }
    iApply ("HT" with "[//] [//] [$LFT $TIME $LLCTX] HE HL [] Hb"). { iApply bor_kind_incl_refl. }
    iModIntro. iIntros (L' κs' l2 b2 bmin rti tyli ri strong weak) "#Hincl1 Hb Hs".
    iApply ("HΦ" $! _ _ _ _ bmin _ _ _ _ _ with "Hincl1 Hb").
    simpl. iSplit.
    - (* strong *) iDestruct "Hs" as "[Hs _]".
      destruct strong as [ strong | ]; last done.
      iIntros (rti2 ltyi2 ri2) "Hl2 Hcond".
      iMod ("Hs" with "Hl2 Hcond") as "(Hb & %Hcond & HR)".
      iDestruct "Hc" as "[_ Hc]". simpl.
      iMod ("Hc" with "Hl [] Hb") as "Hb".
      { rewrite Hcond. done. }
      iFrame. iPureIntro. simp_ltypes. done.
    - (* weak *)
      destruct weak as [ weak | ]; last done.
      iDestruct "Hs" as "[_ Hs]".
      done.
      (*
      iIntros (ltyi2 ri2 bmin').
      iIntros "Hincl2 Hl2 Hcond".
      iDestruct "Hc" as "[Hc _]". simpl.
      iMod ("Hs" with "Hincl2 Hl2 Hcond") as "(Hb & Hcond & Htoks & HR)".

      iMod ("Hc" with "Hl Hb []") as "(Hb & Hcond')".
      iPoseProof ("Hcond'" with "Hcond") as "Hcond".
      iModIntro. iFrame "HR Hb".
      iApply typed_place_cond_incl; last iApply "Hcond".
      + iApply bor_kind_min_incl_r.
      + iPureIntro. apply place_access_rt_rel_refl.
       *)
  Qed.
  Global Instance typed_place_shr_uniq_inst {rto} E L π κ (lt2 : ltype rto) bmin0 r l κ' γ P :
    TypedPlace E L π l (ShrLtype lt2 κ) (#r) bmin0 (Uniq κ' γ) (DerefPCtx Na1Ord PtrOp true :: P) | 30 := λ T, i2p (typed_place_shr_uniq π κ lt2 P E L l r κ' γ bmin0 T).

  Lemma typed_place_shr_shared {rto} π E L (lt2 : ltype rto) P l r κ κ' bmin0 (T : place_cont_t (place_rfn rto)) :
    li_tactic (lctx_lft_alive_count_goal E L κ') (λ '(κs, L'),
      (∀ l', typed_place π E L' l' lt2 r (Shared κ ⊓ₖ bmin0) (Shared κ) P
        (λ L'' κs' l2 b2 bmin rti tyli ri strong weak,
          T L'' (κs ++ κs') l2 b2 (Shared κ' ⊓ₖ bmin) rti tyli ri
            (* strong branch: fold to ShadowedLtype *)
              None (* TODO *)
            (*(fmap (λ strong, mk_strong (λ rti, (place_rfn (strong.(strong_rt) rti) * gname)%type)*)
              (*(λ rti2 ltyi2 ri2,*)
                (*OpenedLtype (MutLtype (strong.(strong_lt) _ ltyi2 ri2) κ) (MutLtype lt2 κ) (MutLtype lt2 κ) (λ r1 r1', ⌜r1 = r1'⌝) (λ _ _, llft_elt_toks κs))*)
              (*(λ rti2 ri2, #((strong.(strong_rfn) _ ri2), γ))*)
              (*strong.(strong_R)) strong)*)
            (* weak branch: just keep the MutLtype *)
            (fmap (λ weak, mk_weak (λ lti' ri', ShrLtype (weak.(weak_lt) lti' ri') κ) (λ (r : place_rfn rti), #(weak.(weak_rfn) r)) weak.(weak_R)) weak))))
    ⊢ typed_place π E L l (ShrLtype lt2 κ) #r bmin0 (Shared κ') (DerefPCtx Na1Ord PtrOp true :: P) T.
  Proof.
    rewrite /lctx_lft_alive_count_goal.
    iIntros "(%κs & %L2 & %Hal & HT)".
    iIntros (Φ F ??). iIntros "#(LFT & TIME & LLCTX) #HE HL #Hincl0 HP HΦ/=".
    (* get a token *)
    iApply fupd_wp. iMod (fupd_mask_subseteq lftE) as "HclF"; first done.
    iMod (lctx_lft_alive_count_tok lftE with "HE HL") as (q) "(Hκ' & Hclκ' & HL)"; [done.. | ].
    iMod "HclF" as "_". iMod (fupd_mask_subseteq F) as "HclF"; first done.
    iPoseProof (shr_ltype_acc_shared F with "[$LFT $TIME $LLCTX] Hκ' HP") as "(%Hly & Hlb & Hb)"; [done.. | ].
    iMod "Hb" as "(%l' & %q' & Hl & >Hb & Hcl)". iMod "HclF" as "_".
    iModIntro. iApply wp_fupd. iApply (wp_deref with "Hl") => //; [solve_ndisj | by apply val_to_of_loc | ].
    iNext.
    iIntros (st) "Hl Hcred". iMod (fupd_mask_mono with "Hb") as "#Hb"; first done.
    iExists l'.
    iSplitR. { iPureIntro. unfold mem_cast. rewrite val_to_of_loc. done. }
    iApply ("HT" with "[//] [//] [$LFT $TIME $LLCTX] HE HL [] Hb"). { iApply bor_kind_min_incl_l. }
    iModIntro. iIntros (L'' κs' l2 b2 bmin rti tyli ri strong weak) "#Hincl1 Hb' Hs".
    iApply ("HΦ" $! _ _ _ _ (Shared κ' ⊓ₖ bmin) _ _ _ _ _ with "[Hincl1] Hb'").
    { iApply bor_kind_incl_trans; last iApply "Hincl1". iApply bor_kind_min_incl_r. }
    simpl. iSplit.
    - (* strong update *)
      done.
    - (* weak update *)
      destruct weak as [ weak | ]; last done.
      iDestruct "Hs" as "(_ & Hs)".
      iIntros (ltyi2 ri2 bmin') "#Hincl2 Hl2 Hcond".
      iMod ("Hs" with "[Hincl2] Hl2 Hcond") as "(Hb' & Hcond & ? & HR)".
      { iApply bor_kind_incl_trans; first iApply "Hincl2". iApply bor_kind_min_incl_r. }
      simpl.
      iMod ("Hcl" with "Hl Hb'") as "(Hb' & Hκ' & Hcond')".
      iFrame. rewrite llft_elt_toks_app.
      iMod (fupd_mask_mono with "(Hclκ' Hκ')") as "?"; first done.
      iFrame. iApply "Hcond'".
      + done.
      + iApply typed_place_cond_incl; last done.
        iApply bor_kind_min_incl_r.
  Qed.
  Global Instance typed_place_shr_shared_inst {rto} E L π κ κ' (lt2 : ltype rto) bmin0 r l P :
    TypedPlace E L π l (ShrLtype lt2 κ) (#r) bmin0 (Shared κ') (DerefPCtx Na1Ord PtrOp true :: P) | 30 := λ T, i2p (typed_place_shr_shared π E L lt2 P l r κ κ' bmin0 T).

  (* TODO more place instances *)

  Lemma typed_place_ofty_shr {rt} `{Inhabited rt} π E L l (ty : type rt) κ (r : place_rfn (place_rfn rt)) bmin0 b P T :
    typed_place π E L l (ShrLtype (◁ ty) κ) r bmin0 b P T
    ⊢ typed_place π E L l (◁ (shr_ref ty κ)) r bmin0 b P T.
  Proof.
    iIntros "Hp". iApply typed_place_eqltype; last done.
    iIntros (?) "HL CTX HE".
    iIntros (??). iApply ltype_eq_sym. iApply shr_ref_unfold.
  Qed.
  Global Instance typed_place_ofty_shr_inst {rt} `{Inhabited rt} π E L l (ty : type rt) κ (r : place_rfn (place_rfn rt)) bmin0 b P :
    TypedPlace E L π l (◁ (shr_ref ty κ))%I r bmin0 b P | 30 := λ T, i2p (typed_place_ofty_shr π E L l ty κ r bmin0 b P T).

  Lemma stratify_ltype_shr_owned {rt} π E L mu mdu ma {M} (ml : M) l (lt : ltype rt) κ (r : (place_rfn rt)) wl
      (T : stratify_ltype_cont_t) :
    (∀ l', stratify_ltype π E L mu mdu ma ml l' lt r (Shared κ) (λ L' R rt' lt' r',
      match ma with
      | StratRefoldFull =>
          ∃ (_ : Inhabited rt'), cast_ltype_to_type E L' lt' (λ ty', T L' R _ (◁ (shr_ref ty' κ))%I (#r'))
      | _ => T L' R _ (ShrLtype lt' κ) (#r')
      end))
    ⊢ stratify_ltype π E L mu mdu ma ml l (ShrLtype lt κ) (#r) (Owned wl) T.
  Proof.
    iIntros "Hs". iIntros (?? ?) "#(LFT & TIME & LLCTX) #HE HL Hb".
    iPoseProof (shr_ltype_acc_owned F with "[$LFT $TIME $LLCTX] Hb") as "Hb"; [done.. | ].
    iDestruct "Hb" as "(%Hly & #Hlb & >(%l' & Hl & Hb & Hcl))".
    iPoseProof ("Hs" with "[//] [//] [$LFT $TIME $LLCTX] HE HL Hb") as "Hb".
    iMod "Hb" as "(%L' & %R & %rt' & %lt' & %r' & HL & %Hcond & Hstep & Hc)".
    destruct (decide (ma = StratRefoldFull)) as [Heq | ].
    - subst ma.
      iDestruct "Hc" as "(% & %ty' & %Heq & HT)".
      iPoseProof (eqltype_use F with "[$LFT $TIME $LLCTX] HE HL") as "(Hvs & HL)"; [done | .. ].
      { apply full_eqltype_alt. apply Heq. }
      (*iPoseProof (eqltype_acc with "[$LFT $TIME $LLCTX] HE HL") as "#Heq"; first done.*)
      iModIntro. iExists L', R, _, _, _. iFrame.
      iSplitR. { simp_ltypes. done. }
      iApply logical_step_fupd.
      iApply (logical_step_compose with "Hcl").
      iApply (logical_step_compose with "Hstep").
      iApply logical_step_intro. iIntros "(Hb & $) Hcl".
      iMod ("Hvs" with "Hb") as "Hb".
      iMod ("Hcl" $! (Shared κ) with "Hl Hb") as "(Hb & _)".
      iDestruct (shr_ref_unfold_1 ty' κ (Owned wl)) as "(_ & #Hi & _)".
      iMod (fupd_mask_mono with "(Hi Hb)") as "$"; first done.
      done.
    - iAssert (T L' R _ (ShrLtype lt' κ) (#r')) with "[Hc]" as "Hc".
      { destruct ma; done. }
      iModIntro. iExists L', R, _, _, _. iFrame.
      iSplitR. { simp_ltypes; done. }
      iApply logical_step_fupd.
      iApply (logical_step_compose with "Hcl").
      iApply (logical_step_compose with "Hstep").
      iApply logical_step_intro. iIntros "(Hb & $) Hcl".
      by iMod ("Hcl" $! (Shared κ) with "Hl Hb") as "($ & _)".
  Qed.
  Global Instance stratify_ltype_shr_owned_none_inst {rt} π E L mdu ma {M} (ml : M) l (lt : ltype rt) κ (r : (place_rfn rt)) wl :
    StratifyLtype π E L StratMutNone mdu ma ml l (ShrLtype lt κ) (#r) (Owned wl) := λ T, i2p (stratify_ltype_shr_owned π E L StratMutNone mdu ma ml l lt κ r wl T).

  (* TODO Uniq *)

  (* Notes on stratification of [Shared]:
     basically:
     when we are accessing, we are unfolding

    - in principle, this should "just work" by operating under these laters.
      Below shared references, the amount of unfolding we could have done is very limited: basically, we can only have
        ShrBlocked or Shadowed.
      For Shadowed: should easily be able to take it back.
      For ShrBlocked: this might be more of a problem.
          We actually need to execute the viewshift for the inheritance, right.
          However, do we ever have nested shrblocked (ie below Shared) in practice?
          => No. I cannot initialize a shrblocked from that, because I cannot initialize sharing.
            Rather, creating a shr reference from a shared place should copy the existing sharing.

      Then: I basically just want to be able to execute this stratification below the later.
        Issue with using this stratify: the lifetime context stuff.
        But in principle, shared stratification should also not use the lifetime context stuff.

      Maybe have a separate notion of shared stratification to account for that?
      That basically should just take the thing unter an iterated step_fupdN and also only need to provide the stratified thing under a step_fupdN.

      Eventually: what happens if we do interior mutability?
        then we will actually open an invariant and get some tokens for stuff back.
        Though we might just want to have that for primitive ofty things, not nested

      In the shared case, can we just set this up differently altogether?
        Maybe just require subtyping of core?
        Can Shared stuff always go directly to the core?
        => Yes, I think so, for now.
        Alternative: directly go to the core.
          i.e. would have to prove that for Shared we can always go to the core.
          For more advanced sharing patterns where we actually want to have shrblocked, this might not work though. but that is anyways far in the future now.
          This is anyways slightly incompatible with the current model/needs work.

      Options now:
      - have stratify_ltype version for Shared that operates below the laters. Basically, this would just be a fancy version of subtyping though.
      - use subtyping, by proving that it is a subtype of the core, and then folding that.
      - use the core, but have proved it once and for all.

    - maybe we also want to have the depth certificates here? *)
  (* This is loosing information by dropping potential [ShadowedLtype], so we should only do it when really necessary. *)
  Lemma stratify_ltype_shared {rt} π E L mu mdu ma {M} (ml : M) l (lt : ltype rt) κ (r : place_rfn rt) (T : stratify_ltype_cont_t):
    (cast_ltype_to_type E L (ltype_core lt) (λ ty', T L True _ (◁ ty')%I (r)))
    ⊢ stratify_ltype π E L mu mdu ma ml l lt r (Shared κ) T.
  Proof.
    iIntros "HT". iIntros (???) "#CTX #HE HL Hl".
    iDestruct "HT" as "(%ty & %Heq & HT)".
    iPoseProof (full_eqltype_acc with "CTX HE HL") as "#Heq"; first apply Heq.
    iPoseProof (ltype_own_shared_to_core with "Hl") as "Hl".
    iDestruct ("Heq" $! (Shared κ) r) as "((%Hsteq & #Hinc & _) & _)".
    iPoseProof ("Hinc" with "Hl") as "Hl".
    iExists L, _, _, _, _. iFrame.
    iModIntro. iSplitR. { simp_ltypes. done. }
    iApply logical_step_intro. iSplitL; done.
  Qed.
  Global Instance stratify_ltype_shared_inst1 {rt} π E L mu mdu {M} (ml : M) l (lt : ltype rt) κ (r : place_rfn rt) :
    StratifyLtype π E L mu mdu StratRefoldFull ml l lt r (Shared κ) :=
    λ T, i2p (stratify_ltype_shared π E L mu mdu StratRefoldFull ml l lt κ r T).
  Global Instance stratify_ltype_shared_inst2 {rt} π E L mu mdu {M} (ml : M) l (lt : ltype rt) κ (r : place_rfn rt) :
    StratifyLtype π E L mu mdu StratRefoldOpened ml l lt r (Shared κ) :=
    λ T, i2p (stratify_ltype_shared π E L mu mdu StratRefoldOpened ml l lt κ r T).

  Lemma stratify_ltype_ofty_shr {rt} `{Inhabited rt} π E L mu ma {M} (ml : M) l (ty : type rt) κ (r : place_rfn (place_rfn rt)) b T :
    stratify_ltype π E L mu StratDoUnfold ma ml l (ShrLtype (◁ ty) κ) r b T
    ⊢ stratify_ltype π E L mu StratDoUnfold ma ml l (◁ (shr_ref ty κ)) r b T.
  Proof.
    iIntros "Hp". iApply stratify_ltype_eqltype; iFrame.
    iPureIntro. iIntros (?) "HL CTX HE".
    iApply ltype_eq_sym. iApply shr_ref_unfold.
  Qed.
  Global Instance stratify_ltype_ofty_shr_inst {rt} `{Inhabited rt} π E L mu ma {M} (ml : M) l (ty : type rt) κ (r : place_rfn (place_rfn rt)) b :
    StratifyLtype π E L mu StratDoUnfold ma ml l (◁ (shr_ref ty κ))%I r b | 30 := λ T, i2p (stratify_ltype_ofty_shr π E L mu ma ml l ty κ r b T).
  (** prove_place_cond instances *)
  (* These need to have a lower priority than the ofty_refl instance (level 2) and the unblocking instances (level 5), but higher than the trivial "no" instance *)
  Lemma prove_place_cond_unfold_shr_l E L {rt1 rt2} `{Inhabited rt1} (ty : type rt1) (lt : ltype rt2) κ k T :
    prove_place_cond E L k (ShrLtype (◁ ty) κ) lt T
    ⊢ prove_place_cond E L k (◁ (shr_ref ty κ)) lt T.
  Proof.
    iApply prove_place_cond_eqltype_l. apply symmetry. apply shr_ref_unfold_full_eqltype; done.
  Qed.
  Global Instance prove_place_cond_unfold_shr_l_inst E L {rt1 rt2} `{Inhabited rt1} (ty : type rt1) (lt : ltype rt2) κ k :
    ProvePlaceCond E L k (◁ (shr_ref ty κ))%I lt | 10 := λ T, i2p (prove_place_cond_unfold_shr_l E L ty lt κ k T).
  Lemma prove_place_cond_unfold_shr_r E L {rt1 rt2} `{Inhabited rt1} (ty : type rt1) (lt : ltype rt2) κ k T :
    prove_place_cond E L k lt (ShrLtype (◁ ty) κ) T
    ⊢ prove_place_cond E L k lt (◁ (shr_ref ty κ)) T.
  Proof.
    iApply prove_place_cond_eqltype_r. apply symmetry. apply shr_ref_unfold_full_eqltype; done.
  Qed.
  Global Instance prove_place_cond_unfold_shr_r_inst E L {rt1 rt2} `{Inhabited rt1} (ty : type rt1) (lt : ltype rt2) κ k :
    ProvePlaceCond E L k lt (◁ (shr_ref ty κ))%I | 10 := λ T, i2p (prove_place_cond_unfold_shr_r E L ty lt κ k T).

  Lemma prove_place_cond_ShrLtype E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κ k T :
    prove_place_cond E L (Shared κ ⊓ₖ k) lt1 lt2 (λ upd, T $ access_result_lift place_rfn upd)
    ⊢ prove_place_cond E L k (ShrLtype lt1 κ) (ShrLtype lt2 κ) T.
  Proof.
    (* TODO *)
  Abort.

  (** Typing rule for shared borrowing, manually applied by the tactics *)
  Lemma type_shr_bor E L T e π κ_name ty_annot :
    (∃ M, named_lfts M ∗ li_tactic (compute_map_lookup_nofail_goal M κ_name) (λ κ,
    (named_lfts M -∗ typed_borrow_shr π E L e κ ty_annot (λ L' v rt ty r, T L' v (place_rfn rt) (shr_ref ty κ) (r)))))
    ⊢ typed_val_expr π E L (&ref{Shr, ty_annot, κ_name} e)%E T.
  Proof.
    rewrite /compute_map_lookup_nofail_goal.
    iIntros "(%M & Hnamed & %κ & _ & HT)". iIntros (Φ) "#(LFT & TIME & LLCTX) #HE HL Hna HΦ".
    wp_bind. iSpecialize ("HT" with "Hnamed"). iApply ("HT" $! _ ⊤ with "[//] [//] [//] [$LFT $TIME $LLCTX] HE HL Hna").
    iIntros (l) "HT".
    unfold Ref. wp_bind. iApply ewp_fupd.
    iApply (wp_logical_step with "TIME HT"); [solve_ndisj.. | ].
    iApply wp_skip. iNext. iIntros "Hcred HT !> !>".
    iApply (wp_logical_step with "TIME HT"); [solve_ndisj.. | ].
    iApply wp_skip. iNext. iIntros "Hcred' HT".
    iMod ("HT" with "Hcred'") as (L' rt ty r r' ly) "(#Hrfn & #Hshr & %Halg & %Hly & #Hlb & #Hsc & HL & Hna & HT)".
    iModIntro. iApply ("HΦ" with "HL Hna [Hshr] HT").
    iExists l, ly, r'. iSplitR; first done. iFrame "Hlb Hrfn Hsc %".
    iModIntro. iModIntro. done.
  Qed.

  (** cast_ltype *)
  Lemma cast_ltype_to_type_shr E L {rt} `{Inhabited rt} (lt : ltype rt) κ T  :
    cast_ltype_to_type E L lt (λ ty, T (shr_ref ty κ))
    ⊢ cast_ltype_to_type E L (ShrLtype lt κ) T.
  Proof.
    iIntros "Hs". iDestruct "Hs" as "(%ty & %Heq & HT)".
    iExists (shr_ref ty κ). iFrame "HT". iPureIntro.
    by apply shr_ref_unfold_full_eqltype.
  Qed.
  Global Instance cast_ltype_to_type_shr_inst E L {rt} `{Inhabited rt} (lt : ltype rt) κ :
    CastLtypeToType E L (ShrLtype lt κ) :=
    λ T, i2p (cast_ltype_to_type_shr E L lt κ T).

  (** subtyping *)
  Lemma weak_subtype_shr_in E L {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) κ1 κ2 r1 r2 T :
    (⌜lctx_lft_incl E L κ2 κ1⌝ ∗ weak_subtype E L r1 r2 ty1 ty2 T)
    ⊢ weak_subtype E L #r1 #r2 (shr_ref ty1 κ1) (shr_ref ty2 κ2) T.
  Proof.
    iIntros "(%Hincl & HT)". iIntros (??) "#CTX #HE HL".
    iPoseProof (lctx_lft_incl_incl with "HL") as "#Hincl"; first done.
    iSpecialize ("Hincl" with "HE").
    iMod ("HT" with "[//] CTX HE HL") as "(#Hsub & $ & $)".
    iApply shr_ref_type_incl_in; done.
  Qed.
  Global Instance weak_subtype_shr_in_inst E L {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) κ1 κ2 r1 r2 :
    Subtype E L #r1 #r2 (shr_ref ty1 κ1) (shr_ref ty2 κ2) | 10:= λ T, i2p (weak_subtype_shr_in E L ty1 ty2 κ1 κ2 r1 r2 T).

  Lemma weak_subtype_shr E L {rt} `{!Inhabited rt} (ty1 ty2 : type rt) κ1 κ2 r1 r2 T :
    (⌜r1 = r2⌝ ∗ ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ mut_subtype E L ty1 ty2 T)
    ⊢ weak_subtype E L r1 r2 (shr_ref ty1 κ1) (shr_ref ty2 κ2) T.
  Proof.
    iIntros "(-> & %Hincl & %Hsubt & HT)". iIntros (??) "#CTX #HE HL".
    iPoseProof (lctx_lft_incl_incl with "HL") as "#Hincl"; first done.
    iSpecialize ("Hincl" with "HE").
    iPoseProof (full_subtype_acc with "HE HL") as "#Hsub"; first done.
    iFrame. unshelve iApply shr_ref_type_incl; done.
  Qed.
  Global Instance weak_subtype_shr_inst E L {rt} `{!Inhabited rt} (ty1 ty2 : type rt) κ1 κ2 r1 r2 :
    Subtype E L r1 r2 (shr_ref ty1 κ1) (shr_ref ty2 κ2) | 11 := λ T, i2p (weak_subtype_shr E L ty1 ty2 κ1 κ2 r1 r2 T).

  Lemma weak_subtype_shr_evar_lft E L {rt} (ty1 ty2 : type rt) κ1 κ2 r1 r2 T `{!IsProtected κ2} :
    ⌜κ1 = κ2⌝ ∗ weak_subtype E L r1 r2 (shr_ref ty1 κ1) (shr_ref ty2 κ1) T
    ⊢ weak_subtype E L r1 r2 (shr_ref ty1 κ1) (shr_ref ty2 κ2) T.
  Proof. iIntros "(<- & $)". Qed.
  Global Instance weak_subtype_shr_evar_lft_inst E L {rt} (ty1 ty2 : type rt) κ1 κ2 r1 r2 `{!IsProtected κ2} :
    Subtype E L r1 r2 (shr_ref ty1 κ1) (shr_ref ty2 κ2) | 9 := λ T, i2p (weak_subtype_shr_evar_lft E L ty1 ty2 κ1 κ2 r1 r2 T).

  Lemma mut_subtype_shr E L {rt} `{!Inhabited rt} (ty1 ty2 : type rt) κ1 κ2 T :
    ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ mut_subtype E L ty1 ty2 T
    ⊢ mut_subtype E L (shr_ref ty1 κ1) (shr_ref ty2 κ2) T.
  Proof.
    iIntros "(%Hincl & %Hsub & $)". iPureIntro. by eapply shr_ref_full_subtype.
  Qed.
  Global Instance mut_subtype_shr_inst E L {rt} `{!Inhabited rt} (ty1 ty2 : type rt) κ1 κ2 :
    MutSubtype E L (shr_ref ty1 κ1) (shr_ref ty2 κ2) | 10 := λ T, i2p (mut_subtype_shr E L ty1 ty2 κ1 κ2 T).
  Lemma mut_subtype_shr_evar_lft E L {rt} (ty1 ty2 : type rt) κ1 κ2 T `{!IsProtected κ2} :
    ⌜κ1 = κ2⌝ ∗ mut_subtype E L (shr_ref ty1 κ1) (shr_ref ty2 κ1) T
    ⊢ mut_subtype E L (shr_ref ty1 κ1) (shr_ref ty2 κ2) T.
  Proof. iIntros "(<- & $)". Qed.
  Global Instance mut_subtype_shr_evar_lft_inst E L {rt} (ty1 ty2 : type rt) κ1 κ2 `{!IsProtected κ2} :
    MutSubtype E L (shr_ref ty1 κ1) (shr_ref ty2 κ2) | 9:= λ T, i2p (mut_subtype_shr_evar_lft E L ty1 ty2 κ1 κ2 T).

  Lemma mut_eqtype_shr E L {rt} `{!Inhabited rt} (ty1 ty2 : type rt) κ1 κ2 T :
    ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ ⌜lctx_lft_incl E L κ1 κ2⌝ ∗ mut_eqtype E L ty1 ty2 T
    ⊢ mut_eqtype E L (shr_ref ty1 κ1) (shr_ref ty2 κ2) T.
  Proof.
    iIntros "(%Hincl & %Hsub & %Hsub2 & $)". iPureIntro. split.
    - eapply shr_ref_full_subtype; first done. by eapply full_eqtype_subtype_l.
    - eapply shr_ref_full_subtype; first done. by eapply full_eqtype_subtype_r.
  Qed.
  Global Instance mut_eqtype_shr_inst E L {rt} `{!Inhabited rt} (ty1 ty2 : type rt) κ1 κ2 :
    MutEqtype E L (shr_ref ty1 κ1) (shr_ref ty2 κ2) | 10 := λ T, i2p (mut_eqtype_shr E L ty1 ty2 κ1 κ2 T).
  Lemma mut_eqtype_shr_evar_lft E L {rt} (ty1 ty2 : type rt) κ1 κ2 T `{!IsProtected κ2} :
    ⌜κ1 = κ2⌝ ∗ mut_eqtype E L (shr_ref ty1 κ1) (shr_ref ty2 κ1) T
    ⊢ mut_eqtype E L (shr_ref ty1 κ1) (shr_ref ty2 κ2) T.
  Proof. iIntros "(<- & $)". Qed.
  Global Instance mut_eqtype_shr_evar_lft_inst E L {rt} (ty1 ty2 : type rt) κ1 κ2 `{!IsProtected κ2} :
    MutEqtype E L (shr_ref ty1 κ1) (shr_ref ty2 κ2) | 9:= λ T, i2p (mut_eqtype_shr_evar_lft E L ty1 ty2 κ1 κ2 T).

  (** subltyping *)
  Lemma weak_subltype_shr_owned_in E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) wl κ1 κ2 r1 r2 T :
    (∃ r2', ⌜r2 = #r2'⌝ ∗ ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ weak_subltype E L (Shared κ1) r1 r2' lt1 lt2 T)
    ⊢ weak_subltype E L (Owned wl) #r1 r2 (ShrLtype lt1 κ1) (ShrLtype lt2 κ2) T.
  Proof.
    iIntros "(%r2' & -> & %Hincl & HT)" (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(Hincl' & HL & $)".
    iPoseProof (lctx_lft_incl_incl with "HL") as "#Hincl"; first done.
    iSpecialize ("Hincl" with "HE"). iFrame.
    iApply (shr_ltype_incl_owned_in with "Hincl'").
    done.
  Qed.
  Global Instance weak_subltype_shr_owned_in_inst E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) wl κ1 κ2 r1 r2 :
    SubLtype E L (Owned wl) #r1 r2 (ShrLtype lt1 κ1) (ShrLtype lt2 κ2) | 10 := λ T, i2p (weak_subltype_shr_owned_in E L lt1 lt2 wl κ1 κ2 r1 r2 T).

 Lemma weak_subltype_shr_owned E L {rt} (lt1 : ltype rt) (lt2 : ltype rt) wl κ1 κ2 r1 r2 T :
    (⌜r1 = r2⌝ ∗ ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ mut_subltype E L lt1 lt2 T)
    ⊢ weak_subltype E L (Owned wl) r1 r2 (ShrLtype lt1 κ1) (ShrLtype lt2 κ2) T.
  Proof.
    iIntros "(-> & %Hincl & %Hsubt & HT)" (??) "#CTX #HE HL".
    iPoseProof (full_subltype_acc with "CTX HE HL") as "#Hsub"; first apply Hsubt.
    iPoseProof (lctx_lft_incl_incl with "HL") as "#Hincl"; first done.
    iSpecialize ("Hincl" with "HE"). iFrame.
    iApply (shr_ltype_incl_owned); last done.
    iApply "Hsub".
  Qed.
  Global Instance weak_subltype_shr_owned_inst E L {rt} (lt1 : ltype rt) (lt2 : ltype rt) wl κ1 κ2 r1 r2 :
    SubLtype E L (Owned wl) r1 r2 (ShrLtype lt1 κ1) (ShrLtype lt2 κ2) | 11 := λ T, i2p (weak_subltype_shr_owned E L lt1 lt2 wl κ1 κ2 r1 r2 T).

  Lemma weak_subltype_shr_shared_in E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κ κ1 κ2 r1 r2 T :
    (∃ r2', ⌜r2 = #r2'⌝ ∗ ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ weak_subltype E L (Shared (κ1)) r1 r2' lt1 lt2 T)
    ⊢ weak_subltype E L (Shared κ) #r1 r2 (ShrLtype lt1 κ1) (ShrLtype lt2 κ2) T.
  Proof.
    iIntros "(%r2' & -> & %Hincl & HT)" (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(Hincl' & HL & $)".
    iPoseProof (lctx_lft_incl_incl with "HL") as "#Hincl"; first done.
    iSpecialize ("Hincl" with "HE"). iFrame.
    iApply (shr_ltype_incl_shared_in with "[Hincl']"); last done.
    done.
  Qed.
  Global Instance weak_subltype_shr_shared_in_inst E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κ κ1 κ2 r1 r2 :
    SubLtype E L (Shared κ) #r1 r2 (ShrLtype lt1 κ1) (ShrLtype lt2 κ2) | 10 := λ T, i2p (weak_subltype_shr_shared_in E L lt1 lt2 κ κ1 κ2 r1 r2 T).

  Lemma weak_subltype_shr_shared E L {rt} (lt1 : ltype rt) (lt2 : ltype rt) κ κ1 κ2 r1 r2 T :
    (⌜r1 = r2⌝ ∗ ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ mut_subltype E L lt1 lt2 T)
    ⊢ weak_subltype E L (Shared κ) r1 r2 (ShrLtype lt1 κ1) (ShrLtype lt2 κ2) T.
  Proof.
    iIntros "(-> & %Hincl & %Hsubt & HT)" (??) "#CTX #HE HL".
    iPoseProof (full_subltype_acc with "CTX HE HL") as "#Hsub"; first apply Hsubt.
    iPoseProof (lctx_lft_incl_incl with "HL") as "#Hincl"; first done.
    iSpecialize ("Hincl" with "HE"). iFrame.
    iApply (shr_ltype_incl_shared); last done.
    iApply "Hsub".
  Qed.
  Global Instance weak_subltype_shr_shared_inst E L {rt} (lt1 : ltype rt) (lt2 : ltype rt) κ κ1 κ2 r1 r2 :
    SubLtype E L (Shared κ) r1 r2 (ShrLtype lt1 κ1) (ShrLtype lt2 κ2) | 11 := λ T, i2p (weak_subltype_shr_shared E L lt1 lt2 κ κ1 κ2 r1 r2 T).

  (* Base instance that will trigger, e.g., for Uniq or PlaceGhost refinements *)
  Lemma weak_subltype_shr_base E L {rt} (lt1 lt2 : ltype rt) k κ1 κ2 r1 r2 T :
    ⌜r1 = r2⌝ ∗ ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ ⌜lctx_lft_incl E L κ1 κ2⌝ ∗ mut_eqltype E L lt1 lt2 T
    ⊢ weak_subltype E L k r1 r2 (ShrLtype lt1 κ1) (ShrLtype lt2 κ2) T.
  Proof.
    iIntros "(<- & %Hincl1 & %Hincl2 & %Hsubt & T)" (??) "#CTX #HE HL".
    iPoseProof (full_eqltype_acc with "CTX HE HL") as "#Hincl"; first done.
    iPoseProof (lctx_lft_incl_incl with "HL") as "#Hincl1"; first apply Hincl1.
    iSpecialize ("Hincl1" with "HE").
    iPoseProof (lctx_lft_incl_incl with "HL") as "#Hincl2"; first apply Hincl2.
    iSpecialize ("Hincl2" with "HE").
    iFrame. iApply shr_ltype_incl; done.
  Qed.
  Global Instance weak_subltype_shr_base_inst E L {rt} (lt1 lt2 : ltype rt) k κ1 κ2 r1 r2 :
    SubLtype E L k r1 r2 (ShrLtype lt1 κ1) (ShrLtype lt2 κ2) | 20 := λ T, i2p (weak_subltype_shr_base E L lt1 lt2 k κ1 κ2 r1 r2 T).

  Lemma weak_subltype_shr_evar_lft E L {rt} (lt1 lt2 : ltype rt) k κ1 κ2 r1 r2 T `{!IsProtected κ2} :
    ⌜κ1 = κ2⌝ ∗ weak_subltype E L k r1 r2 (ShrLtype lt1 κ1) (ShrLtype lt2 κ1) T
    ⊢ weak_subltype E L k r1 r2 (ShrLtype lt1 κ1) (ShrLtype lt2 κ2) T.
  Proof. iIntros "(<- & $)". Qed.
  Global Instance weak_subltype_shr_evar_lft_inst E L {rt} (lt1 lt2 : ltype rt) k κ1 κ2 r1 r2 `{!IsProtected κ2} :
    SubLtype E L k r1 r2 (ShrLtype lt1 κ1) (ShrLtype lt2 κ2) | 9 := λ T, i2p (weak_subltype_shr_evar_lft E L lt1 lt2 k κ1 κ2 r1 r2 T).

  Lemma mut_subltype_shr E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 T :
    ⌜lctx_lft_incl E L κ1 κ2⌝ ∗ ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ mut_eqltype E L lt1 lt2 T
    ⊢ mut_subltype E L (ShrLtype lt1 κ1) (ShrLtype lt2 κ2) T.
  Proof.
    iIntros "(%Hsub1 & %Hsub2 & %Heq & $)".
    iPureIntro. by eapply shr_full_subltype.
  Qed.
  Global Instance mut_subltype_shr_inst E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 :
    MutSubLtype E L (ShrLtype lt1 κ1) (ShrLtype lt2 κ2) | 10 := λ T, i2p (mut_subltype_shr E L lt1 lt2 κ1 κ2 T).

  Lemma mut_subltype_shr_evar_lft E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 T `{!IsProtected κ2} :
    ⌜κ1 = κ2⌝ ∗ mut_subltype E L (ShrLtype lt1 κ1) (ShrLtype lt2 κ1) T
    ⊢ mut_subltype E L (ShrLtype lt1 κ1) (ShrLtype lt2 κ2) T.
  Proof. iIntros "(<- & $)". Qed.
  Global Instance mut_subltype_shr_evar_lft_inst E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 `{!IsProtected κ2} :
    MutSubLtype E L (ShrLtype lt1 κ1) (ShrLtype lt2 κ2) | 9 := λ T, i2p (mut_subltype_shr_evar_lft E L lt1 lt2 κ1 κ2 T).

  Lemma mut_eqltype_shr E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 T :
    ⌜lctx_lft_incl E L κ1 κ2⌝ ∗ ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ mut_eqltype E L lt1 lt2 T
    ⊢ mut_eqltype E L (ShrLtype lt1 κ1) (ShrLtype lt2 κ2) T.
  Proof.
    iIntros "(%Heq1 & %Heq2 & %Heq & $)".
    iPureIntro. by eapply shr_full_eqltype.
  Qed.
  Global Instance mut_eqltype_shr_inst E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 :
    MutEqLtype E L (ShrLtype lt1 κ1) (ShrLtype lt2 κ2) | 10 := λ T, i2p (mut_eqltype_shr E L lt1 lt2 κ1 κ2 T).

  Lemma mut_eqltype_shr_evar_lft E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 T `{!IsProtected κ2} :
    ⌜κ1 = κ2⌝ ∗ mut_eqltype E L (ShrLtype lt1 κ1) (ShrLtype lt2 κ1) T
    ⊢ mut_eqltype E L (ShrLtype lt1 κ1) (ShrLtype lt2 κ2) T.
  Proof. iIntros "(<- & $)". Qed.
  Global Instance mut_eqltype_shr_evar_lft_inst E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 `{!IsProtected κ2} :
    MutEqLtype E L (ShrLtype lt1 κ1) (ShrLtype lt2 κ2) := λ T, i2p (mut_eqltype_shr_evar_lft E L lt1 lt2 κ1 κ2 T).

  (* Ofty unfolding if necessary *)
  Lemma weak_subltype_shr_ofty_1_evar E L {rt1 rt2} `{!Inhabited rt2} (lt1 : ltype rt1) (ty2 : type (place_rfn rt2)) k κ1 r1 r2 T :
    (∃ ty2', ⌜ty2 = shr_ref ty2' κ1⌝ ∗ weak_subltype E L k r1 r2 (ShrLtype lt1 κ1) (◁ (shr_ref ty2' κ1)) T)
    ⊢ weak_subltype E L k r1 r2 (ShrLtype lt1 κ1) (◁ ty2) T.
  Proof.
    iIntros "(%ty2' & -> & HT)". done.
  Qed.
  Global Instance weak_subltype_shr_ofty_1_evar_inst E L {rt1 rt2} `{!Inhabited rt2} (lt1 : ltype rt1) (ty2 : type (place_rfn rt2)) k κ1 r1 r2 `{!IsProtected ty2} :
    SubLtype E L k r1 r2 (ShrLtype lt1 κ1) (◁ ty2)%I | 10 := λ T, i2p (weak_subltype_shr_ofty_1_evar E L lt1 ty2 k κ1 r1 r2 T).

  Lemma weak_subltype_shr_ofty_1 E L {rt1 rt2} `{!Inhabited rt2} (lt1 : ltype rt1) (ty2 : type (rt2)) k κ1 κ2 r1 r2 T :
    weak_subltype E L k r1 r2 (ShrLtype lt1 κ1) (ShrLtype (◁ ty2) κ2) T
    ⊢ weak_subltype E L k r1 r2 (ShrLtype lt1 κ1) (◁ (shr_ref ty2 κ2)) T.
  Proof.
    iIntros "HT". iIntros (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(Hincl & $ & $)".
    iApply (ltype_incl_trans with "Hincl").
    iApply shr_ref_unfold_1.
  Qed.
  Global Instance weak_subltype_shr_ofty_1_inst E L {rt1 rt2} `{!Inhabited rt2} (lt1 : ltype (rt1)) (ty2 : type rt2) k r1 r2 κ1 κ2 :
    SubLtype E L k r1 r2 (ShrLtype lt1 κ1) (◁ (shr_ref ty2 κ2))%I | 12 := λ T, i2p (weak_subltype_shr_ofty_1 E L lt1 ty2 k κ1 κ2 r1 r2 T).

  Lemma weak_subltype_shr_ofty_2 E L {rt1 rt2} `{!Inhabited rt2} (ty1 : type (rt1)) (lt2 : ltype rt2) k r1 r2 κ1 κ2 T :
    (weak_subltype E L k r1 r2 (ShrLtype (◁ ty1) κ1) (ShrLtype lt2 κ2) T)
    ⊢ weak_subltype E L k r1 r2 (◁ (shr_ref ty1 κ1)) (ShrLtype lt2 κ2) T.
  Proof.
    iIntros "HT" (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(Hincl & $ & $)".
    iApply (ltype_incl_trans with "[] Hincl").
    iApply shr_ref_unfold_2.
  Qed.
  Global Instance weak_subltype_shr_ofty_2_inst E L {rt1 rt2} `{!Inhabited rt2} (ty1 : type (rt1)) (lt2 : ltype rt2) k r1 r2 κ1 κ2 :
    SubLtype E L k r1 r2 (◁ (shr_ref ty1 κ1))%I (ShrLtype lt2 κ2) | 10 := λ T, i2p (weak_subltype_shr_ofty_2 E L ty1 lt2 k r1 r2 κ1 κ2 T).

  (* same for [mut_subltype] *)
  Lemma mut_subltype_shr_ofty_1_evar E L {rt} `{!Inhabited rt} (lt1 : ltype rt) (ty2 : type (place_rfn rt))  κ1 T :
    (∃ ty2', ⌜ty2 = shr_ref ty2' κ1⌝ ∗ mut_subltype E L (ShrLtype lt1 κ1) (◁ (shr_ref ty2' κ1)) T)
    ⊢ mut_subltype E L (ShrLtype lt1 κ1) (◁ ty2) T.
  Proof.
    iIntros "(%ty2' & -> & HT)". done.
  Qed.
  Global Instance mut_subltype_shr_ofty_1_evar_inst E L {rt} `{!Inhabited rt} (lt1 : ltype rt) (ty2 : type (place_rfn rt)) κ1 `{!IsProtected ty2} :
    MutSubLtype E L (ShrLtype lt1 κ1) (◁ ty2)%I | 10 := λ T, i2p (mut_subltype_shr_ofty_1_evar E L lt1 ty2 κ1 T).

  Lemma mut_subltype_shr_ofty_1 E L {rt} `{!Inhabited rt} (lt1 : ltype rt) (ty2 : type (rt)) κ1 κ2 T :
    mut_subltype E L (ShrLtype lt1 κ1) (ShrLtype (◁ ty2) κ2) T
    ⊢ mut_subltype E L (ShrLtype lt1 κ1) (◁ (shr_ref ty2 κ2)) T.
  Proof.
    iIntros "(%Hsub & $)". iPureIntro.
    etrans; first done. eapply full_eqltype_subltype_l. by eapply shr_ref_unfold_full_eqltype.
  Qed.
  Global Instance mut_subltype_shr_ofty_1_inst E L {rt} `{!Inhabited rt} (lt1 : ltype (rt)) (ty2 : type rt) κ1 κ2 :
    MutSubLtype E L (ShrLtype lt1 κ1) (◁ (shr_ref ty2 κ2))%I | 12 := λ T, i2p (mut_subltype_shr_ofty_1 E L lt1 ty2 κ1 κ2 T).

  Lemma mut_subltype_shr_ofty_2 E L {rt} `{!Inhabited rt} (ty1 : type rt) (lt2 : ltype rt) κ1 κ2 T :
    (mut_subltype E L (ShrLtype (◁ ty1) κ1) (ShrLtype lt2 κ2) T)
    ⊢ mut_subltype E L (◁ (shr_ref ty1 κ1)) (ShrLtype lt2 κ2) T.
  Proof.
    iIntros "(%Hsub & $)". iPureIntro.
    etrans; last done. eapply full_eqltype_subltype_r. by eapply shr_ref_unfold_full_eqltype.
  Qed.
  Global Instance mut_subltype_shr_ofty_2_inst E L {rt} `{!Inhabited rt} (ty1 : type rt) (lt2 : ltype rt) κ1 κ2 :
    MutSubLtype E L (◁ (shr_ref ty1 κ1))%I (ShrLtype lt2 κ2) | 10 := λ T, i2p (mut_subltype_shr_ofty_2 E L ty1 lt2 κ1 κ2 T).

  (* same for [mut_eqltype] *)
  Lemma mut_eqltype_shr_ofty_1_evar E L {rt} `{!Inhabited rt} (lt1 : ltype rt) (ty2 : type (place_rfn rt))  κ1 T :
    (∃ ty2', ⌜ty2 = shr_ref ty2' κ1⌝ ∗ mut_eqltype E L (ShrLtype lt1 κ1) (◁ (shr_ref ty2' κ1)) T)
    ⊢ mut_eqltype E L (ShrLtype lt1 κ1) (◁ ty2) T.
  Proof.
    iIntros "(%ty2' & -> & HT)". done.
  Qed.
  Global Instance mut_eqltype_shr_ofty_1_evar_inst E L {rt} `{!Inhabited rt} (lt1 : ltype rt) (ty2 : type (place_rfn rt)) κ1 `{!IsProtected ty2} :
    MutEqLtype E L (ShrLtype lt1 κ1) (◁ ty2)%I | 10 := λ T, i2p (mut_eqltype_shr_ofty_1_evar E L lt1 ty2 κ1 T).

  Lemma mut_eqltype_shr_ofty_1 E L {rt} `{!Inhabited rt} (lt1 : ltype rt) (ty2 : type (rt)) κ1 κ2 T :
    mut_eqltype E L (ShrLtype lt1 κ1) (ShrLtype (◁ ty2) κ2) T
    ⊢ mut_eqltype E L (ShrLtype lt1 κ1) (◁ (shr_ref ty2 κ2)) T.
  Proof.
    iIntros "(%Heq & $)". iPureIntro.
    etrans; first done. by eapply shr_ref_unfold_full_eqltype.
  Qed.
  Global Instance mut_eqltype_shr_ofty_1_inst E L {rt} `{!Inhabited rt} (lt1 : ltype (rt)) (ty2 : type rt) κ1 κ2 :
    MutEqLtype E L (ShrLtype lt1 κ1) (◁ (shr_ref ty2 κ2))%I | 12 := λ T, i2p (mut_eqltype_shr_ofty_1 E L lt1 ty2 κ1 κ2 T).

  Lemma mut_eqltype_shr_ofty_2 E L {rt} `{!Inhabited rt} (ty1 : type rt) (lt2 : ltype rt) κ1 κ2 T :
    (mut_eqltype E L (ShrLtype (◁ ty1) κ1) (ShrLtype lt2 κ2) T)
    ⊢ mut_eqltype E L (◁ (shr_ref ty1 κ1)) (ShrLtype lt2 κ2) T.
  Proof.
    iIntros "(%Heq & $)". iPureIntro.
    etrans; last done. symmetry. by eapply shr_ref_unfold_full_eqltype.
  Qed.
  Global Instance mut_eqltype_shr_ofty_2_inst E L {rt} `{!Inhabited rt} (ty1 : type rt) (lt2 : ltype rt) κ1 κ2 :
    MutEqLtype E L (◁ (shr_ref ty1 κ1))%I (ShrLtype lt2 κ2) | 10 := λ T, i2p (mut_eqltype_shr_ofty_2 E L ty1 lt2 κ1 κ2 T).

  (** shortenlft *)
  (*
  Lemma type_shortenlft_shr E L sup_lfts {rt} `{!Inhabited rt} (ty : type rt) r κ π v T :
    (∃ M κs, named_lfts M ∗ ⌜lookup_named_lfts M sup_lfts = Some κs⌝ ∗
      ⌜lctx_lft_incl E L (lft_intersect_list' κs) κ⌝ ∗
      (named_lfts M -∗ v ◁ᵥ{π} r @ shr_ref ty (lft_intersect_list' κs) -∗ T L)) -∗
    typed_annot_expr E L 0 (ShortenLftAnnot sup_lfts) v (v ◁ᵥ{π} r @ shr_ref ty κ) T.
  Proof.
    iIntros "(%M & %κs & Hnamed & % & %Hincl & HT)".
    iIntros "#CTX #HE HL Hv /=".
    iPoseProof (lctx_lft_incl_incl with "HL HE") as "#Hsyn"; first done.
    iModIntro. iExists L. iFrame "HL". iApply ("HT" with "Hnamed").
    unshelve iApply (shr_ref_own_val_mono with "[//] [] Hv"); first done.
    iIntros (?). iApply type_incl_refl.
  Qed.
  Global Instance type_shortenlft_shr_inst E L sup_lfts {rt} `{Inhabited rt} (ty : type rt) r κ π v :
    TypedAnnotExpr E L 0 (ShortenLftAnnot sup_lfts) v (v ◁ᵥ{π} r @ shr_ref ty κ) :=
    λ T, i2p (type_shortenlft_shr E L sup_lfts ty r κ π v T).
   *)
End rules.
