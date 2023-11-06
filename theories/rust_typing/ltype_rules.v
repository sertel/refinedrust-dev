From caesium Require Export proofmode notation.
From caesium Require Import derived.
From refinedrust Require Export ltypes.
From iris Require Import options.


(** * Ltype rules *)

(** Every ltype should fulfill this direct subsumption property. *)
Local Lemma lty_of_ty_mono `{!typeGS Σ} {rt} (ty : type rt) b1 b2 π r l :
  bor_kind_direct_incl b2 b1 -∗
  lty_of_ty_own ty b1 π r l -∗
  lty_of_ty_own ty b2 π r l.
Proof.
  iIntros "#Hincl". destruct b1, b2; try done; unfold bor_kind_direct_incl.
  + iDestruct "Hincl" as "->". eauto.
  + rewrite /lty_of_ty_own.
    iIntros "(%ly & Hst & Hly & Hsc & Hlb & % & ? & #Hb)". iExists ly. iFrame.
    iExists r'. iFrame. iModIntro. iMod "Hb". iModIntro.
    by iApply ty_shr_mono.
  + rewrite /lty_of_ty_own.
    iDestruct "Hincl" as "(Hincl & ->)".
    iIntros "(%ly & Hst & Hly & Hsc & Hlb & Hcred & Hrfn & Hb)". iExists ly. iFrame.
    iMod "Hb". iModIntro. iApply pinned_bor_shorten; done.
Qed.
Local Lemma alias_mono `{!typeGS Σ} rt st p b1 b2 π r l :
  bor_kind_direct_incl b2 b1 -∗
  alias_lty_own rt st p b1 π r l -∗
  alias_lty_own rt st p b2 π r l.
Proof.
  iIntros "#Hincl". destruct b1, b2; try done; unfold bor_kind_direct_incl.
  iDestruct "Hincl" as "->"; eauto.
Qed.
Local Lemma mutltype_mono `{!typeGS Σ} {rt} (lt : ltype rt) π κ :
  (∀ b1 b2 r l, bor_kind_direct_incl b2 b1 -∗ l ◁ₗ[π, b1] r @ lt -∗ l ◁ₗ[π, b2] r @ lt) →
  ∀ b1 b2 r l, bor_kind_direct_incl b2 b1 -∗
    l ◁ₗ[π, b1] r @ MutLtype lt κ -∗ l ◁ₗ[π, b2] r @ MutLtype lt κ.
Proof.
  iIntros (IH b1 b2 r l) "#Hincl".
  destruct b1, b2; try done; unfold bor_kind_direct_incl.
  + iDestruct "Hincl" as "->". eauto.
  + rewrite !ltype_own_mut_ref_unfold /mut_ltype_own.
    iIntros "(%ly & ? & ? & ? & %r' & %γ & ? & #Hb)".
    iExists ly. iFrame. iExists r', γ. iFrame. iModIntro. iMod "Hb".
    iDestruct "Hb" as "(%li & Hf & Hb)". iModIntro. iExists li.
    iSplitL "Hf". { by iApply frac_bor_shorten. }
    iNext. iApply IH; last done.
    unfold bor_kind_direct_incl.
    iApply lft_intersect_mono; last done. iApply lft_incl_refl.
  + iDestruct "Hincl" as "(Hincl & ->)".
    rewrite !ltype_own_mut_ref_unfold /mut_ltype_own.
    iIntros "(%ly & ? & ? & ? & ? & ? & Hb)".
    iExists ly. iFrame. iMod "Hb". by iApply pinned_bor_shorten.
Qed.
Local Lemma shrltype_mono `{!typeGS Σ} {rt} (lt : ltype rt) π κ :
  (∀ b1 b2 r l, bor_kind_direct_incl b2 b1 -∗ l ◁ₗ[π, b1] r @ lt -∗ l ◁ₗ[π, b2] r @ lt) →
  ∀ b1 b2 r l, bor_kind_direct_incl b2 b1 -∗
    l ◁ₗ[π, b1] r @ ShrLtype lt κ -∗ l ◁ₗ[π, b2] r @ ShrLtype lt κ.
Proof.
  iIntros (IH b1 b2 r l) "#Hincl".
  destruct b1, b2; try done; unfold bor_kind_direct_incl.
  + iDestruct "Hincl" as "->". eauto.
  + rewrite !ltype_own_shr_ref_unfold /shr_ltype_own.
    iIntros "(%ly & ? & ? & ? & %r' & ? & #Hb)".
    iExists ly. iFrame. iExists r'. iFrame. iModIntro. iMod "Hb".
    iDestruct "Hb" as "(%li & Hf & Hb)". iModIntro. iExists li.
    iSplitL "Hf". { by iApply frac_bor_shorten. }
    done.
  + iDestruct "Hincl" as "(Hincl & ->)".
    rewrite !ltype_own_shr_ref_unfold /shr_ltype_own.
    iIntros "(%ly & ? & ? & ? & ? & ? & Hb)".
    iExists ly. iFrame. iMod "Hb". by iApply pinned_bor_shorten.
Qed.
Local Lemma box_ltype_mono `{!typeGS Σ} {rt} (lt : ltype rt) π :
  (∀ b1 b2 r l, bor_kind_direct_incl b2 b1 -∗ l ◁ₗ[π, b1] r @ lt -∗ l ◁ₗ[π, b2] r @ lt) →
  ∀ b1 b2 r l, bor_kind_direct_incl b2 b1 -∗
    l ◁ₗ[π, b1] r @ BoxLtype lt -∗ l ◁ₗ[π, b2] r @ BoxLtype lt.
Proof.
  iIntros (IH b1 b2 r l) "#Hincl".
  destruct b1, b2; try done; unfold bor_kind_direct_incl.
  + iDestruct "Hincl" as "->". eauto.
  + rewrite !ltype_own_box_unfold /box_ltype_own.
    iIntros "(%ly & ? & ? & ? & %r' & ? & #Hb)".
    iExists ly. iFrame. iExists r'. iFrame. iModIntro. iMod "Hb".
    iDestruct "Hb" as "(%li & Hf & Hb)". iModIntro. iExists li.
    iSplitL "Hf". { by iApply frac_bor_shorten. }
    iNext. iApply IH; last done. done.
  + iDestruct "Hincl" as "(Hincl & ->)".
    rewrite !ltype_own_box_unfold /box_ltype_own.
    iIntros "(%ly & ? & ? & ? & ? & ? & Hb)".
    iExists ly. iFrame. iMod "Hb". by iApply pinned_bor_shorten.
Qed.
Local Lemma owned_ptr_ltype_mono `{!typeGS Σ} {rt} (lt : ltype rt) (ls : bool) π :
  (∀ b1 b2 r l, bor_kind_direct_incl b2 b1 -∗ l ◁ₗ[π, b1] r @ lt -∗ l ◁ₗ[π, b2] r @ lt) →
  ∀ b1 b2 r l, bor_kind_direct_incl b2 b1 -∗
    l ◁ₗ[π, b1] r @ OwnedPtrLtype lt ls -∗ l ◁ₗ[π, b2] r @ OwnedPtrLtype lt ls.
Proof.
  iIntros (IH b1 b2 r l) "#Hincl".
  destruct b1, b2; try done; unfold bor_kind_direct_incl.
  + iDestruct "Hincl" as "->". eauto.
  + rewrite !ltype_own_owned_ptr_unfold /owned_ptr_ltype_own.
    iIntros "(%ly & ? & ? & ? & %r' & %li & ? & #Hb)".
    iExists ly. iFrame. iExists r', li. iFrame. iModIntro. iMod "Hb".
    iDestruct "Hb" as "(Hf & Hb)". iModIntro.
    iSplitL "Hf". { by iApply frac_bor_shorten. }
    iNext. iApply IH; last done. done.
  + iDestruct "Hincl" as "(Hincl & ->)".
    rewrite !ltype_own_owned_ptr_unfold /owned_ptr_ltype_own.
    iIntros "(%ly & ? & ? & ? & ? & ? & Hb)".
    iExists ly. iFrame. iMod "Hb". by iApply pinned_bor_shorten.
Qed.
Local Lemma struct_ltype_mono `{!typeGS Σ} {rts} (lts : hlist ltype rts) sls π :
  (∀ lt b1 b2 r l, lt ∈ hzipl rts lts → bor_kind_direct_incl b2 b1 -∗ l ◁ₗ[π, b1] r @ (projT2 lt) -∗ l ◁ₗ[π, b2] r @ (projT2 lt)) →
  ∀ b1 b2 r l, bor_kind_direct_incl b2 b1 -∗
    l ◁ₗ[π, b1] r @ StructLtype lts sls -∗ l ◁ₗ[π, b2] r @ StructLtype lts sls.
Proof.
  iIntros (IH b1 b2 r l) "#Hincl".
  destruct b1, b2; try done; unfold bor_kind_direct_incl.
  + iDestruct "Hincl" as "->". eauto.
  + rewrite !ltype_own_struct_unfold /struct_ltype_own.
    iIntros "(%sl & ? & ? & ? & ? & %r' & ? & #Hb)".
    iExists sl. iFrame. iExists r'. iFrame. iModIntro. iMod "Hb".
    iApply (big_sepL_wand with "Hb").
    iModIntro. iApply big_sepL_intro. iIntros "!>" (k [rt [lt r0]] Hlook).
    apply pad_struct_lookup_Some_1 in Hlook as (n & ly & ? & [[? Hlook] | [? Heq]]).
    * simpl. specialize (IH (existT rt lt)).
      iIntros "(%ly0 & ? & ? & Hb)".
      iExists ly0. iFrame. iApply (IH with "[] Hb"); last done.
      eapply hpzipl_lookup_inv_hzipl_pzipl in Hlook as (Hlook & _).
      by eapply elem_of_list_lookup_2.
    * injection Heq as -> Heq1 Heq2. simpl.
      apply existT_inj in Heq1 as ->. apply existT_inj in Heq2 as ->.
      iIntros "(%ly0 & ? & ? & Hb)". iExists ly0. iFrame.
      rewrite /UninitLtype !ltype_own_ofty_unfold. by iApply (lty_of_ty_mono with "[] Hb").
  + iDestruct "Hincl" as "(Hincl & ->)".
    rewrite !ltype_own_struct_unfold /struct_ltype_own.
    iIntros "(%sl & ? & ? & ? & ? & ? & ? & Hb)".
    iExists sl. iFrame. iMod "Hb".
    by iApply pinned_bor_shorten.
Qed.
Local Lemma array_ltype_mono `{!typeGS Σ} {rt} (def : type rt) (len : nat) (lts : list (nat * ltype rt)) π :
  (∀ lt b1 b2 r l, lt ∈ (interpret_iml (◁ def)%I len lts) → bor_kind_direct_incl b2 b1 -∗ l ◁ₗ[π, b1] r @ lt -∗ l ◁ₗ[π, b2] r @ lt) →
  ∀ b1 b2 r l, bor_kind_direct_incl b2 b1 -∗
    l ◁ₗ[π, b1] r @ ArrayLtype def len lts -∗ l ◁ₗ[π, b2] r @ ArrayLtype def len lts.
Proof.
  iIntros (IH b1 b2 r l) "#Hincl".
  destruct b1, b2; try done; unfold bor_kind_direct_incl.
  + iDestruct "Hincl" as "->"; eauto.
  + rewrite !ltype_own_array_unfold /array_ltype_own.
    iIntros "(%ly & Hst & Hly & Hlb & Ha & %r' &  Hrfn & #Hb)".
    iExists ly. iFrame. iExists r'. iFrame.
    iModIntro. iMod "Hb" as "(%Hlen2 & Hb)". iModIntro. iR.
    iApply (big_sepL2_wand with "Hb").
    iApply big_sepL2_intro. { rewrite interpret_iml_length //. }
    iIntros "!>" (?????) "($ & Hb)". iApply IH; last done; [ | done].
    by eapply elem_of_list_lookup_2.
  + rewrite !ltype_own_array_unfold /array_ltype_own.
    iDestruct "Hincl" as "(Hincl & ->)".
    iIntros "(%ly &  ? & ? & ? & ? & ? & ? & Hb)".
    iExists ly. iFrame.
    iMod "Hb". iModIntro. iApply pinned_bor_shorten; done.
Qed.
Local Lemma enum_ltype_mono `{!typeGS Σ} {rt} (en : enum rt) (tag : string) (lte : ltype (enum_tag_rt en tag)) π :
  (∀ b1 b2 r l, bor_kind_direct_incl b2 b1 -∗ l ◁ₗ[π, b1] r @ lte -∗ l ◁ₗ[π, b2] r @ lte) →
  ∀ b1 b2 r l, bor_kind_direct_incl b2 b1 -∗
    l ◁ₗ[π, b1] r @ EnumLtype en tag lte -∗ l ◁ₗ[π, b2] r @ EnumLtype en tag lte.
Proof.
  iIntros (IH b1 b2 r l) "#Hincl".
  destruct b1, b2; try done; unfold bor_kind_direct_incl.
  + iDestruct "Hincl" as "->"; eauto.
  + rewrite !ltype_own_enum_unfold /enum_ltype_own.
    iIntros "(%el & %Hen & %Hly & Hlb & ? & [])".
  + rewrite !ltype_own_enum_unfold /enum_ltype_own.
    iDestruct "Hincl" as "(Hincl & ->)".
    iIntros "(%el & %Hen & %Hly & Hlb & ? & [])".
Qed.


Lemma ltype_bor_kind_direct_incl' `{!typeGS Σ} {rt} (lt : ltype rt) b1 b2 π r l :
  bor_kind_direct_incl b2 b1 -∗
  ((l ◁ₗ[π, b1] r @ lt -∗ l ◁ₗ[π, b2] r @ lt) ∗ (l ◁ₗ[π, b1] r @ ltype_core lt -∗ l ◁ₗ[π, b2] r @ ltype_core lt)).
Proof.
  move: rt lt r l b1 b2.
  apply (ltype_induction (λ rt lt, ∀ r l b1 b2, (⊢ b2 ⊑ₛₖ b1 -∗ (l ◁ₗ[ π, b1] r @ lt -∗ l ◁ₗ[ π, b2] r @ lt) ∗ (l ◁ₗ[π, b1] r @ ltype_core lt -∗ l ◁ₗ[π, b2] r @ ltype_core lt))%I)).
  - iIntros (rt ty κ r l b1 b2) "#Hincl". simp_ltypes.
    iSplitL; first last. { rewrite !ltype_own_ofty_unfold. iApply lty_of_ty_mono. done. }
    destruct b1, b2; try done; unfold bor_kind_direct_incl.
    + iDestruct "Hincl" as "->"; eauto.
    + rewrite !ltype_own_blocked_unfold /blocked_lty_own.
      iIntros "(%ly & ? & ? & ? & ? & [])".
    + rewrite !ltype_own_blocked_unfold /blocked_lty_own.
      iDestruct "Hincl" as "(Hincl & ->)".
      iIntros "(%ly & ? & ? & ? & ? & Hb & ?)". iExists ly. iFrame.
      iIntros "Hdead". iMod ("Hb" with "Hdead") as "($ & Hb)". by iApply pinned_bor_shorten.
  - iIntros (rt ty κ r l b1 b2) "#Hincl". simp_ltypes.
    iSplitL; first last. { rewrite !ltype_own_ofty_unfold. by iApply lty_of_ty_mono. }
    destruct b1, b2; try done; unfold bor_kind_direct_incl.
    + iDestruct "Hincl" as "->"; eauto.
    + rewrite !ltype_own_shrblocked_unfold /shr_blocked_lty_own.
      iIntros "(%ly & ? & ? & ? & ? & %r' & Hrfn & Hb)".
      done.
      (*iExists ly. iFrame. iExists r'. iSplitR; first done.*)
      (*by iApply ty_shr_mono.*)
    + rewrite !ltype_own_shrblocked_unfold /shr_blocked_lty_own.
      iDestruct "Hincl" as "(Hincl & ->)".
      iIntros "(%ly & ? & ? & ? & ? & %r' & ? & ? & Hb & Hs & $ & $)".
      iExists ly. iFrame. iExists r'. iFrame.
      iIntros "Hdead". iMod ("Hs" with "Hdead") as "Hdead". by iApply pinned_bor_shorten.
  - iIntros (rt ty r l b1 b2) "#Hincl". simp_ltypes.
    iSplitL; rewrite !ltype_own_ofty_unfold; iApply lty_of_ty_mono; done.
  - iIntros (rt st p r l b1 b2) "#Hincl". simp_ltypes.
    iSplitL; rewrite !ltype_own_alias_unfold; iApply alias_mono; done.
  - iIntros (rt lt IH κ r l b1 b2) "#Hincl". simp_ltypes.
    iSplitL; (iApply mutltype_mono; [ | done]).
    + iIntros (????) "Hincl". iDestruct (IH with "Hincl") as "($ & _)".
    + iIntros (????) "Hincl". iDestruct (IH with "Hincl") as "(_ & $)".
  - iIntros (rt lt IH κ r l b1 b2) "#Hincl". simp_ltypes.
    iSplitL; (iApply shrltype_mono; [ | done]).
    + iIntros (????) "Hincl". iDestruct (IH with "Hincl") as "($ & _)".
    + iIntros (????) "Hincl". iDestruct (IH with "Hincl") as "(_ & $)".
  - iIntros (rt lt IH r l b1 b2) "#Hincl". simp_ltypes.
    iSplitL; (iApply box_ltype_mono; [ | done]).
    + iIntros (????) "Hincl". iDestruct (IH with "Hincl") as "($ & _)".
    + iIntros (????) "Hincl". iDestruct (IH with "Hincl") as "(_ & $)".
  - iIntros (rt lt ls IH r l b1 b2) "#Hincl". simp_ltypes.
    iSplitL; (iApply owned_ptr_ltype_mono; [ | done]).
    + iIntros (????) "Hincl". iDestruct (IH with "Hincl") as "($ & _)".
    + iIntros (????) "Hincl". iDestruct (IH with "Hincl") as "(_ & $)".
  - iIntros (rts lts IH sls r l b1 b2) "#Hincl".
    simp_ltypes.
    iSplitL.
    + iApply (struct_ltype_mono lts); last done.
      iIntros (????? Hel) "Hincl". by iDestruct (IH with "Hincl") as "($ & _)".
    + iApply (struct_ltype_mono (@ltype_core _ _ +<$> lts)); last done.
      iIntros (????? Hel) "Hincl".
      apply elem_of_list_lookup_1 in Hel as (i & Hel).
      destruct lt as [rt lt].
      eapply hzipl_hmap_lookup_inv in Hel as (y & Hlook & ->).
      apply elem_of_list_lookup_2 in Hlook.
      eapply IH in Hlook.
      iDestruct (Hlook with "Hincl") as "(_ & Ha)".
      iApply "Ha".
  - iIntros (rt def len lts IH r l b1 b2) "#Hincl".
    simp_ltypes. iSplitL; (iApply array_ltype_mono; [ | done]).
    + iIntros (????? Hel) "Hincl".
      apply elem_of_interpret_iml_inv in Hel as [ -> | []].
      { rewrite !ltype_own_ofty_unfold. by iApply lty_of_ty_mono. }
      by iDestruct (IH with "Hincl") as "($ & _)".
    + iIntros (????? Hel) "Hincl".
      rewrite -ltype_core_ofty in Hel.
      rewrite interpret_iml_fmap in Hel.
      apply elem_of_list_fmap in Hel as (lt' & -> & Hel).
      apply elem_of_interpret_iml_inv in Hel as [ -> | []].
      { simp_ltypes. rewrite !ltype_own_ofty_unfold. by iApply lty_of_ty_mono. }
      by iDestruct (IH with "Hincl") as "(_ & $)".
  - iIntros (rt en variant lte IH r l b1 b2) "#Hincl".
    simp_ltypes. iSplitL; (iApply enum_ltype_mono; [ | done]).
    + iIntros (????) "Hincl". iPoseProof (IH with "Hincl") as "($ & _)".
    + iIntros (????) "Hincl". iPoseProof (IH with "Hincl") as "(_ & $)".
  - iIntros (rt_cur rt_inner rt_full lt_cur lt_inner lt_full Cpre Cpost IH1 IH2 IH3 r l b1 b2) "#Hincl".
    simp_ltypes.
    iAssert (□ (l ◁ₗ[ π, b1] r @ OpenedLtype lt_cur lt_inner lt_full Cpre Cpost -∗ l ◁ₗ[ π, b2] r @ OpenedLtype lt_cur lt_inner lt_full Cpre Cpost))%I as "#Ha"; first last.
    { iSplitL; eauto with iFrame. }
    iModIntro. destruct b1, b2; try done; unfold bor_kind_direct_incl.
    + iDestruct "Hincl" as "->"; eauto.
    + rewrite !ltype_own_opened_unfold /opened_ltype_own.
      iIntros "(%ly & ? & ? & ? & ? & ? & Ha)".
      done.
      (*iExists ly. iFrame.*)
      (*iDestruct (IH1 with "[]") as "(Hb & _)"; last by iApply "Hb". done.*)
    + iDestruct "Hincl" as "(Hincl & ->)".
      rewrite !ltype_own_opened_unfold /opened_ltype_own.
      iIntros "(%ly & ? & ? & ? & ? & ? & Hb & Hstep)".
      iExists ly. iFrame.
      iApply (logical_step_wand with "Hstep"). iIntros "Hstep".
      iIntros (P κs r0 r') "Hpre #Hincl' Hown Hvs".
      iMod ("Hstep" with "Hpre [] Hown Hvs") as "(Ha & Hobs & Hpost)".
      { iApply (big_sepL_wand with "Hincl'"). iApply big_sepL_intro.
        iIntros "!>" (? κ' _) "#Hincl0". iApply lft_incl_trans; done. }
      iModIntro. iFrame.
      iIntros "Hdead Hobs".
      rewrite !ltype_own_core_equiv.
      iDestruct (IH3 with "[]") as "(_ & Hb)"; first last.
      { iApply "Hb". iApply ("Hpost" with "Hdead Hobs"). }
      iSplit; done.
  - iIntros (rt_full κs lt_full IH r l b1 b2) "#Hincl".
    simp_ltypes.
    iSplitL; first last.
    { iDestruct (IH with "Hincl") as "(_ & $)". }
    destruct b1, b2; try done; unfold bor_kind_direct_incl.
    + iDestruct "Hincl" as "->"; eauto.
    + rewrite !ltype_own_coreable_unfold /coreable_ltype_own.
      iIntros "(%ly & ? & ? & ? & Ha)".
      iExists ly. iFrame. rewrite !ltype_own_core_equiv.
      iDestruct (IH with "[]") as "(_ & Hb)"; last by iApply "Hb".
      done.
    + iDestruct "Hincl" as "(Hincl & ->)".
      rewrite !ltype_own_coreable_unfold /coreable_ltype_own.
      iIntros "(%ly & ? & ? & ? & ? & Ha)".
      iExists ly. iFrame.
      iIntros "Hdead Hrfn". iMod ("Ha" with "Hdead Hrfn") as "Ha".
      rewrite !ltype_own_core_equiv.
      iDestruct (IH with "[]") as "(_ & Hb)"; last by iApply "Hb".
      iSplit; done.
  - iIntros (rt_cur rt_full lt_cur r_cur lt_full IH1 IH2 r l b1 b2) "#Hincl".
    simp_ltypes. iSplitL; first last.
    { iPoseProof (IH2 with "Hincl") as "(_ &  Ha)". iApply "Ha". }
    rewrite !ltype_own_shadowed_unfold /shadowed_ltype_own.
    iIntros "(%Hst & Ha & Hb)". iSplitR; first done.
    iSplitL "Ha". { iPoseProof (IH1 with "Hincl") as "(Ha1 & _)". by iApply "Ha1". }
    iPoseProof (IH2 with "Hincl") as "(Ha1 & _)". by iApply "Ha1".
Qed.
Lemma ltype_bor_kind_direct_incl `{!typeGS Σ} {rt} (lt : ltype rt) b1 b2 π r l :
  bor_kind_direct_incl b2 b1 -∗
  (l ◁ₗ[π, b1] r @ lt -∗ l ◁ₗ[π, b2] r @ lt).
Proof.
  iIntros "Hincl". iDestruct (ltype_bor_kind_direct_incl' with "Hincl") as "($ & _)".
Qed.
Lemma ltype_own_shr_mono `{!typeGS Σ} {rt} (lt : ltype rt) l π r κ1 κ2 :
  κ2 ⊑ κ1 -∗
  l ◁ₗ[π, Shared κ1] r @ lt -∗
  l ◁ₗ[π, Shared κ2] r @ lt.
Proof.
  iIntros "Hincl". iApply ltype_bor_kind_direct_incl. done.
Qed.
Lemma ltype_own_uniq_mono `{!typeGS Σ} {rt} (lt : ltype rt) l π r γ κ1 κ2 :
  κ2 ⊑ κ1 -∗
  l ◁ₗ[π, Uniq κ1 γ] r @ lt -∗
  l ◁ₗ[π, Uniq κ2 γ] r @ lt.
Proof.
  iIntros "Hincl". iApply ltype_bor_kind_direct_incl. iSplitL; done.
Qed.

Section subtype.
  Context `{!typeGS Σ}.

  Lemma ltype_incl_syn_type {rt1 rt2} b r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) :
    ltype_incl b r1 r2 lt1 lt2 -∗ ⌜ltype_st lt1 = ltype_st lt2⌝.
  Proof.
    iIntros "(#$ & _)".
  Qed.
  Lemma ltype_incl_core {rt1 rt2} b r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) :
    ltype_incl b r1 r2 lt1 lt2 -∗ ltype_incl b r1 r2 (ltype_core lt1) (ltype_core lt2).
  Proof.
    iIntros "(%Hst & _ & #Hi)".
    iSplitR. { rewrite !ltype_core_syn_type_eq. done. }
    iSplitR; iModIntro.
    - done.
    - rewrite !ltype_core_idemp. done.
  Qed.

  (* TODO subtyping for OpenedLtype and CoreableLtype? *)
End subtype.

Section accessors.
  Context `{typeGS Σ}.

  Lemma shadowed_ltype_acc_cur {rt_cur rt_full} (lt_cur : ltype rt_cur) (lt_full : ltype rt_full) (r_cur : place_rfn rt_cur) l π b r :
    l ◁ₗ[π, b] r @ ShadowedLtype lt_cur r_cur lt_full -∗
    l ◁ₗ[π, b] r_cur @ lt_cur ∗
    (∀ (rt_cur' : Type) (lt_cur' : ltype rt_cur') (r_cur' : place_rfn rt_cur'),
    ⌜ltype_st lt_cur = ltype_st lt_cur'⌝ -∗
      l ◁ₗ[π, b] r_cur' @ lt_cur' -∗
      l ◁ₗ[π, b] r @ ShadowedLtype lt_cur' (r_cur') lt_full).
  Proof.
    rewrite ltype_own_shadowed_unfold /shadowed_ltype_own.
    iIntros "(%Hst & Hcur & Hfull)". iFrame.
    iIntros (rt_cur' lt_cur' r_cur' Hst') "Hb".
    rewrite ltype_own_shadowed_unfold /shadowed_ltype_own.
    iFrame. rewrite -Hst. done.
  Qed.

  Lemma opened_ltype_create_uniq_simple π {rt_cur rt_full} (lt_cur : ltype rt_cur) (lt_full : ltype rt_full) r l κ κ' γ (r1 r2 : rt_full) q C n R :
    ltype_st lt_cur = ltype_st lt_full →
    gvar_obs γ r1 -∗
    gvar_auth γ r2 -∗
    £ 1 -∗
    atime n -∗
    κ ⊑ κ' -∗
    (q.[κ] ={lftE}=∗ R) -∗
    (∀ K', ▷ (K' -∗ [†κ'] ={lft_userE}=∗ ▷ C) -∗ £ 1 -∗ ▷ K' ={lftE}=∗ &pin{ κ' }[C] K' ∗ q.[κ]) -∗
    (□ ∀ r, gvar_auth γ r -∗ (|={lftE}=> l ◁ₗ[π, Owned false] #r @ ltype_core lt_full) -∗ C) -∗
    (∀ r, gvar_obs γ r -∗ atime n -∗ £ (num_laters_per_step n) -∗ &pin{κ} [C] C ={lftE}=∗ l ◁ₗ[ π, Uniq κ γ] # r @ ltype_core lt_full) -∗
    l ◁ₗ[π, Owned false] r @ lt_cur -∗
    l ◁ₗ[π, Uniq κ γ] r @ (OpenedLtype lt_cur lt_full lt_full (λ r1 r2, ⌜r1 = r2⌝) (λ r1 r2, R)).
  Proof.
    (* TODO this is to a large degree duplicated with the existential unfolding lemma.
       Can we deduplicate this somewhow?
       Main obstacle: we have different pre/postconditions.
       Option 1: allow updating the pre/postcondition of an OpenedLtype
        challenge: update lt_inner. need lt_inner' ==∗ lt_inner, but that does not hold in our case.
        can we change the definition of opened_ltype a bit to allow that?
       Option 2: make the unfolding lemma more flexible directly
       *)
    iIntros (Hst_eq) "Hobs Hauth Hcred Hat #? HR Hcl #HC Ha Hcur".
    rewrite ltype_own_opened_unfold /opened_ltype_own.
    iPoseProof (ltype_own_has_layout with "Hcur") as "(%ly & %Hst & %Hly)".
    iPoseProof (ltype_own_loc_in_bounds with "Hcur") as "#Hlb"; first done.
    iExists ly. do 5 iR. iFrame.
    iApply (logical_step_intro_atime with "Hat").
    iIntros "Hcred' Hat". iModIntro.
    iIntros (Hown κs r0 r0') "Hpre #Hincl' Hown #Hub".
    iMod (gvar_update with "Hauth Hobs") as "(Hauth & $)".

    iAssert (□ ([† κ'] ={lftE}=∗ lft_dead_list κs))%I as "#Hkill".
    { iModIntro. iIntros "#Hdead".
      iApply big_sepL_fupd. iApply (big_sepL_wand with "Hincl'"). iApply big_sepL_intro.
      iIntros "!>" (? κ0 _) "#Hincl0".
      iApply (lft_incl_dead with "[] Hdead"); first done.
      iApply lft_incl_trans; done. }

    (* close the borrow *)
    set (V := (gvar_auth γ r0' ∗ Hown π r0 l ∗ (lft_dead_list κs ={lftE}=∗ ⌜r0 = r0'⌝))%I).
    iMod ("Hcl" $! V with "[HC] Hcred [Hauth Hown Hpre]") as "(Hb & Htok)".
    { iNext. iIntros "(Hauth & Hown &Heq) #Hdead".
      iModIntro. iNext. iApply ("HC" with "Hauth").
      iMod ("Hkill" with "Hdead") as "#Hdead'".
      iMod ("Heq" with "Hdead'") as "<-".
      iMod ("Hub" with "Hdead' Hown") as "Hown".
      rewrite ltype_own_core_equiv. done. }
    { iNext. rewrite /V. iFrame. }
    iMod ("HR" with "Htok") as "$".
    iModIntro. iIntros "#Hdead Hobs".
    iApply (ltype_own_core_equiv).
    iSpecialize ("Hub" with "Hdead").
    iPoseProof (pinned_bor_shorten κ κ' with "[//] Hb") as "Hb".
    iApply ("Ha" with "Hobs Hat Hcred' [Hb]").
    (* bring the pinned bor in the right shape *)
    iApply (pinned_bor_impl with "[] Hb").
    iNext. iModIntro. iSplit; first last. { eauto. }
    iIntros "(Hauth & Hown & Hk)".
    iApply ("HC" with "Hauth").
    iMod ("Hk" with "Hdead") as "<-".
    rewrite ltype_own_core_equiv. by iApply "Hub".
  Qed.

  Lemma ofty_ltype_acc_owned {rt} F π (ty : type rt) (r : rt) wl l :
    lftE ⊆ F →
    l ◁ₗ[π, Owned wl] PlaceIn r @ (◁ ty) -∗
    ∃ ly, ⌜syn_type_has_layout ty.(ty_syn_type) ly⌝ ∗
      ⌜l `has_layout_loc` ly⌝ ∗ ty_sidecond ty ∗ loc_in_bounds l 0 (ly_size ly) ∗ |={F}=>
      ∃ v : val, l ↦ v ∗ v ◁ᵥ{π} r @ ty ∗
      logical_step F
      (∀ v2 rt2 (ty2 : type rt2) (r2 : rt2),
        l ↦ v2 -∗
        ⌜ty.(ty_syn_type) = ty2.(ty_syn_type)⌝ -∗
        ty_sidecond ty2 -∗
        (▷?wl v2 ◁ᵥ{π} r2 @ ty2) ={F}=∗
        l ◁ₗ[π, Owned wl] PlaceIn r2 @ (◁ ty2)).
  Proof.
    iIntros (?) "Hb". rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hb" as "(%ly & %Halg & %Hly & #Hsc & #Hlb & Hcred & %r' & Hrfn & Hv)".
    iExists ly. iFrame "% #".
    iMod (maybe_use_credit with "Hcred Hv") as "(Hcred & Hat & Hv)"; first done.
    iDestruct "Hv" as "(%v & Hl & Hv)".
    iDestruct "Hrfn" as "<-".
    iModIntro. iExists v. iFrame.
    iApply (logical_step_intro_maybe with "Hat").
    iIntros "Hcred' !>". iIntros (v2 rt2 ty2 r2) "Hl %Hst_eq Hsc' Hv".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iModIntro. rewrite -Hst_eq. iExists ly. iFrame "#∗%".
    iExists _. iSplitR; first done.
    iNext. eauto with iFrame.
  Qed.

  Lemma ofty_ltype_acc_uniq {rt} F π (ty : type rt) (r : rt) κ γ l R q :
    lftE ⊆ F →
    rrust_ctx -∗
    q.[κ] -∗
    (q.[κ] ={lftE}=∗ R) -∗
    l ◁ₗ[π, Uniq κ γ] #r @ (◁ ty) -∗
    ∃ ly, ⌜syn_type_has_layout ty.(ty_syn_type) ly⌝ ∗
      ⌜l `has_layout_loc` ly⌝ ∗ loc_in_bounds l 0 (ly_size ly) ∗ |={F}=>
      ∃ v : val, l ↦ v ∗ v ◁ᵥ{π} r @ ty ∗
      logical_step F
      ((* weak update *)
       (∀ v2 (r2 : rt),
        l ↦ v2 -∗
        (▷ v2 ◁ᵥ{π} r2 @ ty) ={F}=∗
        l ◁ₗ[π, Uniq κ γ] #r2 @ (◁ ty) ∗ R) ∧
       (* strong update *)
       (∀ v2 rt2 (ty2 : type rt2) (r2 : rt2),
        l ↦ v2 -∗
        ty_sidecond ty2 -∗
        (v2 ◁ᵥ{π} r2 @ ty2)  -∗
        ⌜ty_syn_type ty = ty_syn_type ty2⌝ ={F}=∗
        l ◁ₗ[π, Uniq κ γ] #(r2) @ OpenedLtype (◁ty2) (◁ty) (◁ty) (λ r1 r1', ⌜r1 = r1'⌝) (λ _ _, R))).
  Proof.
    iIntros (?) "#(LFT & TIME & LLCTX) Htok HclR Hb". rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hb" as "(%ly & %Halg & %Hly & #Hsc & #Hlb & Hcred & Hobs & Hb)".
    iExists ly. iFrame "%#".
    iMod (fupd_mask_subseteq lftE) as "HF_cl"; first done.
    iMod "Hb" as "Hb".
    iMod (pinned_bor_acc_strong lftE with "LFT Hb Htok") as "(%κ' & #Hinclκ & Hb & Hvcl & Hcl)"; first done.
    iMod "HF_cl" as "_".
    iDestruct "Hcred" as "([Hcred1 Hcred] & Hat)".
    iApply (lc_fupd_add_later with "Hcred1"); iNext.
    iDestruct "Hb" as "(%r' & Hauth & Hb)".
    iMod (fupd_mask_mono lftE with "Hb") as "(%v & Hl & Hv)"; first done.
    iPoseProof (gvar_agree with "Hauth Hobs") as "#->".
    iModIntro. iExists _. iFrame.
    iApply (logical_step_intro_atime with "Hat").
    iIntros "Hcred' Hat !>". iSplit.
    - iIntros (v2 r2) "Hl Hv".
      iMod (gvar_update r2 with "Hauth Hobs") as "(Hauth & Hobs)".
      iDestruct "Hcred" as "(Hcred1 & Hcred)".
      iMod (fupd_mask_mono with "(Hcl Hvcl Hcred1 [Hauth Hv Hl])") as "(Hb & Htok)"; first done.
      { iNext. eauto with iFrame. }
      iMod (fupd_mask_mono with "(HclR Htok)") as "$"; first done.
      iModIntro. rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iExists ly. iFrame "#∗%". iApply pinned_bor_shorten; done.
      (* TODO maybe provide excess credits *)
    - iIntros (v2 rt2 ty2 r2) "Hl #Hsc2 Hv %Hst". iModIntro.
      iDestruct "Hcred" as "(Hcred1 & Hcred)".
      iApply (opened_ltype_create_uniq_simple with "Hobs Hauth Hcred1 Hat Hinclκ HclR Hcl [] [Hcred']"); first done.
      { iModIntro. iIntros (?) "Hauth Hc". iExists _. iFrame. simp_ltypes.
        rewrite ltype_own_ofty_unfold /lty_of_ty_own.
        iDestruct "Hc" as ">(%ly' & % & % & _ & _ & _ & %r' & -> & >Hb)". eauto. }
      { iIntros (?) "Hobs Hat Hcred Hp". simp_ltypes.
        iModIntro. rewrite ltype_own_ofty_unfold /lty_of_ty_own.
        eauto 8 with iFrame. }
      { rewrite ltype_own_ofty_unfold /lty_of_ty_own.
        rewrite -Hst. iExists _. do 5 iR. iExists _. iR.
        iNext. eauto 8 with iFrame. }
  Qed.

  Lemma ofty_ltype_acc_shared {rt} F π (ty : type rt) (r : rt) κ l :
    lftE ⊆ F →
    l ◁ₗ[π, Shared κ] PlaceIn r @ (◁ ty) -∗
    ∃ ly, ⌜syn_type_has_layout ty.(ty_syn_type) ly⌝ ∗
    ⌜l `has_layout_loc` ly⌝ ∗ loc_in_bounds l 0 (ly_size ly) ∗ |={F}=>
    l ◁ₗ{π, κ} r @ ty.
  Proof.
    iIntros (?) "Hb".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hb" as "(%ly & %Halg & %Hly & #Hsc & #Hlb & %r' & <- & #Hb)".
    iExists ly. iFrame "%#". iApply (fupd_mask_mono with "Hb"). done.
  Qed.

  (* TODO: accessors for shared refs *)

  Lemma opened_ltype_acc_owned π {rt_cur rt_inner rt_full} (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full) Cpre Cpost l wl r :
    l ◁ₗ[π, Owned wl] r @ OpenedLtype lt_cur lt_inner lt_full Cpre Cpost -∗
    l ◁ₗ[π, Owned false] r @ lt_cur ∗
    (∀ rt_cur' (lt_cur' : ltype rt_cur') r',
      l ◁ₗ[π, Owned false] r' @ lt_cur' -∗
      ⌜ltype_st lt_cur' = ltype_st lt_cur⌝ -∗
      l ◁ₗ[π, Owned wl] r' @ OpenedLtype lt_cur' lt_inner lt_full Cpre Cpost).
  Proof.
    rewrite ltype_own_opened_unfold /opened_ltype_own.
    iIntros "(%ly & ? & ? & ? & ? & ? & $ & Hcl)".
    iIntros (rt_cur' lt_cur' r') "Hown %Hst".
    rewrite ltype_own_opened_unfold /opened_ltype_own.
    iExists ly. rewrite Hst. eauto with iFrame.
  Qed.
  Lemma opened_ltype_acc_uniq π {rt_cur rt_inner rt_full} (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full) Cpre Cpost l κ γ r :
    l ◁ₗ[π, Uniq κ γ] r @ OpenedLtype lt_cur lt_inner lt_full Cpre Cpost -∗
    l ◁ₗ[π, Owned false] r @ lt_cur ∗
    (∀ rt_cur' (lt_cur' : ltype rt_cur') r',
      l ◁ₗ[π, Owned false] r' @ lt_cur' -∗
      ⌜ltype_st lt_cur' = ltype_st lt_cur⌝ -∗
      l ◁ₗ[π, Uniq κ γ] r' @ OpenedLtype lt_cur' lt_inner lt_full Cpre Cpost).
  Proof.
    rewrite ltype_own_opened_unfold /opened_ltype_own.
    iIntros "(%ly & ? & ? & ? & ? & ? & $ & Hcl)".
    iIntros (rt_cur' lt_cur' r') "Hown %Hst".
    rewrite ltype_own_opened_unfold /opened_ltype_own.
    iExists ly. rewrite Hst. eauto with iFrame.
  Qed.

End accessors.

Section ofty.
  Context `{!typeGS Σ}.

  Lemma ofty_mono_ly_strong_in π {rt1 rt2} l wl (ty1 : type rt1) (ty2 : type rt2) (r1 : rt1) (r2 : rt2) ly1 ly2 :
    syn_type_has_layout (ty1.(ty_syn_type)) ly1 →
    syn_type_has_layout (ty2.(ty_syn_type)) ly2 →
    (l `has_layout_loc` ly1 → l `has_layout_loc` ly2) →
    ly_size ly2 = ly_size ly1 →
    (∀ v, ty1.(ty_own_val) π r1 v -∗ ty2.(ty_own_val) π r2 v) -∗
    (ty_sidecond ty1 -∗ ty_sidecond ty2) -∗
    l ◁ₗ[π, Owned wl] #r1 @ (◁ ty1) -∗
    l ◁ₗ[π, Owned wl] #r2 @ (◁ ty2).
  Proof.
    intros Halg1 Halg2 Halign Hsz. iIntros "Hvs Hscvs Hl".
    rewrite !ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hl" as "(%ly1' & %Halg1' & %Hly & Hsc & Hlb & Hcred & %r' & <- & Hb)".
    assert (ly1' = ly1) as -> by by eapply syn_type_has_layout_inj.
    iExists ly2. iSplitR; first done.
    iSplitR. { iPureIntro. by apply Halign. }
    iPoseProof ("Hscvs" with "Hsc") as "$".
    rewrite Hsz. iFrame "Hlb Hcred".
    iExists r2. iSplitR; first done.
    iNext. iMod "Hb" as "(%v & Hl & Hv)".
    iModIntro. iExists v. iFrame. by iApply "Hvs".
  Qed.
  Lemma ofty_mono_ly_strong π {rt1} l wl (ty1 : type rt1) (ty2 : type rt1) (r1 : place_rfn rt1) ly1 ly2 :
    syn_type_has_layout (ty1.(ty_syn_type)) ly1 →
    syn_type_has_layout (ty2.(ty_syn_type)) ly2 →
    (l `has_layout_loc` ly1 → l `has_layout_loc` ly2) →
    ly_size ly2 = ly_size ly1 →
    (∀ v r, ty1.(ty_own_val) π r v -∗ ty2.(ty_own_val) π r v) -∗
    (ty_sidecond ty1 -∗ ty_sidecond ty2) -∗
    l ◁ₗ[π, Owned wl] r1 @ (◁ ty1) -∗
    l ◁ₗ[π, Owned wl] r1 @ (◁ ty2).
  Proof.
    intros Halg1 Halg2 Halign Hsz. iIntros "Hvs Hscvs Hl".
    rewrite !ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hl" as "(%ly1' & %Halg1' & %Hly & Hsc & Hlb & Hcred & %r' & ? & Hb)".
    assert (ly1' = ly1) as -> by by eapply syn_type_has_layout_inj.
    iExists ly2. iSplitR; first done.
    iSplitR. { iPureIntro. by apply Halign. }
    iPoseProof ("Hscvs" with "Hsc") as "$".
    rewrite Hsz. iFrame "Hlb Hcred".
    iExists _. iFrame.
    iNext. iMod "Hb" as "(%v & Hl & Hv)".
    iModIntro. iExists v. iFrame. by iApply "Hvs".
  Qed.
End ofty.

Section open.
  Context `{!typeGS Σ}.

  Lemma ltype_own_make_alias wl' {rt rt2} (lt : ltype rt) r r2 π wl l :
    l ◁ₗ[π, Owned wl] r @ lt -∗
    maybe_creds wl' -∗
    l ◁ₗ[π, Owned wl] r @ lt ∗ l ◁ₗ[π, Owned wl'] r2 @ AliasLtype rt2 (ltype_st lt) l.
  Proof.
    iIntros "Hl Hcreds".
    iPoseProof (ltype_own_has_layout with "Hl") as "(%ly & %Halg & %Hly)".
    iPoseProof (ltype_own_loc_in_bounds with "Hl") as "#Hlb"; first done.
    iFrame. rewrite ltype_own_alias_unfold /alias_lty_own.
    eauto 8 with iFrame.
  Qed.


  (* TODO move /generalize. We can also use this for the stratify-unfold things. *)
  (* TODO can we design it so that we can also use it for the place instances? *)
  Definition ltype_owned_openable {rt} (lt : ltype rt) : Prop :=
    ∀ π r l wl,
      l ◁ₗ[π, Owned wl] r @ lt -∗
      (* TODO can we just have a later instead of the logstep? *)
      maybe_creds wl ∗ (▷?wl (l ◁ₗ[π, Owned false] r @ lt)).
  Definition ltype_uniq_openable {rt} (lt : ltype rt) : Prop :=
    ∀ F κ γ π r l q κs,
      lftE ⊆ F →
      rrust_ctx -∗
      q.[κ] -∗
      (q.[κ] ={lftE}=∗ llft_elt_toks κs) -∗
      l ◁ₗ[π, Uniq κ γ] r @ lt -∗ |={F}=>
      (l ◁ₗ[π, Uniq κ γ] r @ OpenedLtype lt lt lt (λ ri ri', ⌜ri = ri'⌝) (λ ri ri', llft_elt_toks κs)).
  Lemma ltype_owned_openable_elim_logstep {rt} (lt : ltype rt) F π r l wl :
    ltype_owned_openable lt →
    l ◁ₗ[π, Owned wl] r @ lt -∗
    |={F}=> l ◁ₗ[π, Owned false] r @ lt ∗ logical_step F (maybe_creds wl).
  Proof.
    iIntros (Hopen) "Hb". iPoseProof (Hopen with "Hb") as "(Hcred & Hb)".
    destruct wl.
    - iDestruct "Hcred" as "([Hcred1 Hcred] & Hat)".
      iMod (lc_fupd_elim_later with "Hcred1 Hb") as "$".
      iApply (logical_step_intro_atime with "Hat").
      iModIntro. by iIntros "$ $".
    - iFrame. iApply logical_step_intro. done.
  Qed.

  (** Lemmas for ofty *)
  Lemma ltype_owned_openable_ofty {rt} (ty : type rt) :
    ltype_owned_openable (◁ ty)%I.
  Proof.
    iIntros (π r l wl) "Hb".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hb" as "(%ly & ? & ? & ? & ? & Hcred & %r' & ? & Hb)".
    iFrame. iNext. rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    eauto 8 with iFrame.
  Qed.
  Lemma ltype_uniq_openable_ofty {rt} (ty : type rt) :
    ltype_uniq_openable (◁ ty)%I.
  Proof.
    iIntros (? κ γ π r l q κs ?) "#(LFT & TIME & LLCTX) Htok Hcl_tok Hb".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hb" as "(%ly & % & % & #? & #? & ((Hcred1 & Hcred) & Hat) & Hrfn & Hb)".
    iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
    iMod "Hb".
    iMod (pinned_bor_acc_strong lftE with "LFT Hb Htok") as "(%κ' & #Hincl & Hb & ? & Hcl_b)"; first done.
    iMod "Hcl_F" as "_".
    iApply (lc_fupd_add_later with "Hcred1"). iNext.
    iDestruct "Hb" as "(%r' & Hauth & Hb)".
    iMod (fupd_mask_mono with "Hb") as "Hb"; first done.
    iDestruct "Hb" as "(%v & Hl & Hv)".

    iMod (place_rfn_interp_mut_owned with "Hrfn Hauth") as "(Hrfn & Hobs & Hauth)".
    iModIntro.
    iDestruct "Hcred" as "(Hcred1 & Hcred)".
    iApply (opened_ltype_create_uniq_simple with "Hobs Hauth Hcred1 Hat Hincl Hcl_tok Hcl_b [] []").
    - done.
    - iModIntro. iIntros (r0) "Hauth Hb". iExists r0. iFrame.
      iMod "Hb" as "Hb". simp_ltypes.
      rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iDestruct "Hb" as "(%ly' & ? & ? & ? & ? & ? & %r0' & <- & $)".
    - iIntros (r0) "Hobs Hat Hcred Hb".
      iModIntro. simp_ltypes.
      rewrite (ltype_own_ofty_unfold _ (Uniq _ _)) /lty_of_ty_own.
      iExists ly. do 4 iR. by iFrame.
    - rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iExists ly. iR. iR. iR. iR. iR. iExists _. iFrame.
      iModIntro. eauto with iFrame.
  Qed.

End open.

Section deinit.
  Context `{!typeGS Σ}.

  (* TODO seem to be redundant. Rather use the stronger extractable stuff *)
  Lemma ltype_uniq_deinitializable_deinit_mut F π l st {rt} (lt : ltype rt) r κ γ wl :
    lftE ⊆ F →
    ltype_uniq_deinitializable lt →
    syn_type_compat PtrSynType st →
    (l ◁ₗ[π, Owned wl] #(r, γ) @ (MutLtype lt κ)) ={F}=∗
    l ◁ₗ[π, Owned false] #() @ (◁ uninit st) ∗ place_rfn_interp_mut r γ.
  Proof.
    iIntros (? Hdeinit Hcompat).
    iIntros "Hl".
    rewrite ltype_own_mut_ref_unfold /mut_ltype_own.
    iDestruct "Hl" as "(%ly & %Halg & %Hly & Hlb & Hcred & %γ' & %r' & %Heq & Hb)".
    injection Heq as <- <-.
    iMod (maybe_use_credit with "Hcred Hb") as "(Hcred & Hat & Hc)"; first done.
    iDestruct "Hc" as "(%l' & Hl & Hb)".
    iMod (ltype_own_deinit_ghost_drop_uniq with "Hb") as "Hrfn"; [done.. | ].
    iFrame.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own. iExists ly.
    iSplitR. { destruct Hcompat as [<- | (ly1 & Hst' & ->)]; first done.
      simpl. iPureIntro. eapply syn_type_has_layout_make_untyped; last done.
      by eapply syn_type_has_layout_inj. }
    iR. iSplitR. { rewrite /ty_own_val/=//. }
    iFrame. iR. iExists tt. iR. iModIntro. iExists _. iFrame.
    rewrite uninit_own_spec. iExists ly.
    apply syn_type_has_layout_ptr_inv in Halg as ->. iSplitR; last done.
    iPureIntro. destruct Hcompat as [<- | (ly1 & Hst' & ->)]; first done.
    specialize (syn_type_has_layout_ptr_inv _ Hst') as ->.
    eapply syn_type_has_layout_make_untyped; done.
  Qed.

  (* TODO try to find a good way to unify with previous lemma *)
  Lemma ltype_uniq_deinitializable_deinit_mut' F π l st {rt} (lt : ltype rt) r κ γ wl :
    lftE ⊆ F →
    ltype_uniq_deinitializable lt →
    syn_type_compat PtrSynType st →
    £ (Nat.b2n wl) -∗
    (l ◁ₗ[π, Owned wl] #(r, γ) @ (MutLtype lt κ)) ={F}=∗
    l ◁ₗ[π, Owned wl] #() @ (◁ uninit st) ∗ place_rfn_interp_mut r γ.
  Proof.
    iIntros (? Hdeinit Hcompat).
    iIntros "Hcred' Hl".
    rewrite ltype_own_mut_ref_unfold /mut_ltype_own.
    iDestruct "Hl" as "(%ly & %Halg & %Hly & Hlb & Hcred & %γ' & %r' & %Heq & Hb)".
    injection Heq as <- <-.
    iMod (maybe_use_credit with "Hcred Hb") as "(Hcred & Hat & Hc)"; first done.
    iDestruct "Hc" as "(%l' & Hl & Hb)".
    iMod (ltype_own_deinit_ghost_drop_uniq with "Hb") as "Hrfn"; [done.. | ].
    iFrame.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own. iExists ly.
    iSplitR. { destruct Hcompat as [<- | (ly1 & Hst' & ->)]; first done.
      simpl. iPureIntro. eapply syn_type_has_layout_make_untyped; last done.
      by eapply syn_type_has_layout_inj. }
    iR. iSplitR. { rewrite /ty_own_val/=//. }
    iFrame. iSplitR "Hl".
    { iModIntro. destruct wl; last done. simpl. rewrite /num_cred. iFrame. iApply lc_succ; iFrame. }
    iExists tt. iR. iModIntro. iExists _. iFrame.
    rewrite uninit_own_spec. iExists ly.
    apply syn_type_has_layout_ptr_inv in Halg as ->. iSplitR; last done.
    iPureIntro. destruct Hcompat as [<- | (ly1 & Hst' & ->)]; first done.
    specialize (syn_type_has_layout_ptr_inv _ Hst') as ->.
    eapply syn_type_has_layout_make_untyped; done.
  Qed.

  Lemma ltype_uniq_extractable_deinit_mut F π l st {rt} (lt : ltype rt) r κ κm γ wl :
    lftE ⊆ F →
    ltype_uniq_extractable lt = Some κm →
    syn_type_compat PtrSynType st →
    (l ◁ₗ[π, Owned wl] #(r, γ) @ (MutLtype lt κ)) ={F}=∗
    l ◁ₗ[π, Owned false] #() @ (◁ uninit st) ∗ MaybeInherit κm InheritGhost (place_rfn_interp_mut r γ).
  Proof.
    iIntros (? Hdeinit Hcompat).
    iIntros "Hl".
    rewrite ltype_own_mut_ref_unfold /mut_ltype_own.
    iDestruct "Hl" as "(%ly & %Halg & %Hly & Hlb & Hcred & %γ' & %r' & %Heq & Hb)".
    injection Heq as <- <-.
    iMod (maybe_use_credit with "Hcred Hb") as "(Hcred & Hat & Hc)"; first done.
    iDestruct "Hc" as "(%l' & Hl & Hb)".
    iMod (ltype_own_extract_ghost_drop_uniq with "Hb") as "Hrfn"; [done.. | ].
    iFrame.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own. iExists ly.
    iSplitR. { destruct Hcompat as [<- | (ly1 & Hst' & ->)]; first done.
      simpl. iPureIntro. eapply syn_type_has_layout_make_untyped; last done.
      by eapply syn_type_has_layout_inj. }
    iR. iSplitR. { rewrite /ty_own_val/=//. }
    iFrame. iR. iExists tt. iR. iModIntro. iExists _. iFrame.
    rewrite uninit_own_spec. iExists ly.
    apply syn_type_has_layout_ptr_inv in Halg as ->. iSplitR; last done.
    iPureIntro. destruct Hcompat as [<- | (ly1 & Hst' & ->)]; first done.
    specialize (syn_type_has_layout_ptr_inv _ Hst') as ->.
    eapply syn_type_has_layout_make_untyped; done.
  Qed.

  (* TODO try to find a good way to unify with previous lemma *)
  Lemma ltype_uniq_extractable_deinit_mut' F π l st {rt} (lt : ltype rt) r κ κm γ wl :
    lftE ⊆ F →
    ltype_uniq_extractable lt = Some κm →
    syn_type_compat PtrSynType st →
    £ (Nat.b2n wl) -∗
    (l ◁ₗ[π, Owned wl] #(r, γ) @ (MutLtype lt κ)) ={F}=∗
    l ◁ₗ[π, Owned wl] #() @ (◁ uninit st) ∗ MaybeInherit κm InheritGhost (place_rfn_interp_mut r γ).
  Proof.
    iIntros (? Hdeinit Hcompat).
    iIntros "Hcred' Hl".
    rewrite ltype_own_mut_ref_unfold /mut_ltype_own.
    iDestruct "Hl" as "(%ly & %Halg & %Hly & Hlb & Hcred & %γ' & %r' & %Heq & Hb)".
    injection Heq as <- <-.
    iMod (maybe_use_credit with "Hcred Hb") as "(Hcred & Hat & Hc)"; first done.
    iDestruct "Hc" as "(%l' & Hl & Hb)".
    iMod (ltype_own_extract_ghost_drop_uniq with "Hb") as "Hrfn"; [done.. | ].
    iFrame.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own. iExists ly.
    iSplitR. { destruct Hcompat as [<- | (ly1 & Hst' & ->)]; first done.
      simpl. iPureIntro. eapply syn_type_has_layout_make_untyped; last done.
      by eapply syn_type_has_layout_inj. }
    iR. iSplitR. { rewrite /ty_own_val/=//. }
    iFrame. iSplitR "Hl".
    { iModIntro. destruct wl; last done. simpl. rewrite /num_cred. iFrame. iApply lc_succ; iFrame. }
    iExists tt. iR. iModIntro. iExists _. iFrame.
    rewrite uninit_own_spec. iExists ly.
    apply syn_type_has_layout_ptr_inv in Halg as ->. iSplitR; last done.
    iPureIntro. destruct Hcompat as [<- | (ly1 & Hst' & ->)]; first done.
    specialize (syn_type_has_layout_ptr_inv _ Hst') as ->.
    eapply syn_type_has_layout_make_untyped; done.
  Qed.

  Lemma ltype_deinit_shr F π l st {rt} (lt : ltype rt) r κ wl :
    lftE ⊆ F →
    syn_type_compat PtrSynType st →
    (l ◁ₗ[π, Owned wl] r @ (ShrLtype lt κ)) ={F}=∗
    l ◁ₗ[π, Owned false] #() @ (◁ uninit st).
  Proof.
    iIntros (? Hstcomp) "Hl".
    rewrite ltype_own_shr_ref_unfold /shr_ltype_own.
    iDestruct "Hl" as "(%ly & %Halg & % & ? & Hcreds & %r' & ? & Hb)".
    iMod (maybe_use_credit with "Hcreds Hb") as "(? & ? & %l' & Hl & Hb)"; first done.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iModIntro. iExists ly. simpl. iSplitR.
    { destruct Hstcomp as [<- | (ly1 & Hst' & ->)]; first done.
      simpl. iPureIntro. eapply syn_type_has_layout_make_untyped; last done.
      by eapply syn_type_has_layout_inj. }
    iR. iR. iFrame.  iR. iExists tt. iR.
    iModIntro. iExists l'. iFrame. rewrite uninit_own_spec. iExists ly.
    apply syn_type_has_layout_ptr_inv in Halg as ->. iSplitR; last done.
    iPureIntro. destruct Hstcomp as [<- | (ly1 & Hst' & ->)]; first done.
    specialize (syn_type_has_layout_ptr_inv _ Hst') as ->.
    eapply syn_type_has_layout_make_untyped; done.
  Qed.

  Lemma ltype_deinit_shr' F π l st {rt} (lt : ltype rt) r κ wl :
    lftE ⊆ F →
    syn_type_compat PtrSynType st →
    £ (Nat.b2n wl) -∗
    (l ◁ₗ[π, Owned wl] r @ (ShrLtype lt κ)) ={F}=∗
    l ◁ₗ[π, Owned wl] #() @ (◁ uninit st).
  Proof.
    iIntros (? Hstcomp) "Hcred Hl".
    rewrite ltype_own_shr_ref_unfold /shr_ltype_own.
    iDestruct "Hl" as "(%ly & %Halg & % & ? & Hcreds & %r' & ? & Hb)".
    iMod (maybe_use_credit with "Hcreds Hb") as "(? & ? & %l' & Hl & Hb)"; first done.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iModIntro. iExists ly. simpl. iSplitR.
    { destruct Hstcomp as [<- | (ly1 & Hst' & ->)]; first done.
      simpl. iPureIntro. eapply syn_type_has_layout_make_untyped; last done.
      by eapply syn_type_has_layout_inj. }
    iR. iR. iFrame. iSplitR "Hl".
    { destruct wl; last done. simpl. rewrite /num_cred. iFrame. iApply lc_succ; iFrame. }
    iExists tt. iR.
    iModIntro. iExists l'. iFrame. rewrite uninit_own_spec. iExists ly.
    apply syn_type_has_layout_ptr_inv in Halg as ->. iSplitR; last done.
    iPureIntro. destruct Hstcomp as [<- | (ly1 & Hst' & ->)]; first done.
    specialize (syn_type_has_layout_ptr_inv _ Hst') as ->.
    eapply syn_type_has_layout_make_untyped; done.
  Qed.
End deinit.
