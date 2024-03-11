From refinedrust Require Export type uninit_def.
From refinedrust Require Import programs ltype_rules value.
Set Default Proof Using "Type".

(** * Typing rules for the uninit type *)

Section lemmas.
  Context `{!typeGS Σ}.

  (* TODO move *)
  Lemma ofty_owned_subtype_aligned π {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) r1 r2 ly2 l  :
    (* location needs to be suitably aligned for ty2 *)
    syn_type_has_layout (ty_syn_type ty2) ly2 →
    l `has_layout_loc` ly2 →
    owned_type_incl π r1 r2 ty1 ty2
    ⊢ (l ◁ₗ[π, Owned false] #r1 @ ◁ ty1) -∗ (l ◁ₗ[π, Owned false] #r2 @ ◁ ty2).
  Proof.
    iIntros (Hst2 Hly2) "Hincl Hl".
    rewrite !ltype_own_ofty_unfold/lty_of_ty_own.
    iDestruct "Hl" as "(%ly' & %Halg' & %Hlyl & Hsc1 & Hlb & _ & % & -> & Hl)".
    iExists ly2. iR. iR.
    iDestruct "Hincl" as "(%Hszeq & Hsc & Hvi)".
    assert (ly_size ly' = ly_size ly2) as Hszeq'. { apply Hszeq; done. }
    iSplitL "Hsc Hsc1". { by iApply "Hsc". }
    rewrite -Hszeq'. iFrame. iR.
    iExists _. iR. iMod "Hl" as "(%v & Hl & Hv)".
    iModIntro. iExists _. iFrame.
    by iApply "Hvi".
  Qed.
  Lemma ofty_owned_subtype_aligned' π {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) r1 r2 ly2 l  :
    (* location needs to be suitably aligned for ty2 *)
    syn_type_has_layout (ty_syn_type ty2) ly2 →
    l `has_layout_loc` ly2 →
    (∀ r1, owned_type_incl π r1 r2 ty1 ty2)
    ⊢ (l ◁ₗ[π, Owned false] r1 @ ◁ ty1) -∗ (l ◁ₗ[π, Owned false] #r2 @ ◁ ty2).
  Proof.
    iIntros (Hst2 Hly2) "Hincl Hl".
    rewrite !ltype_own_ofty_unfold/lty_of_ty_own.
    iDestruct "Hl" as "(%ly' & %Halg' & %Hlyl & Hsc1 & Hlb & _ & % & Hrfn & Hl)".
    iExists ly2. iR. iR.
    iDestruct ("Hincl" $! r') as "(%Hszeq & Hsc & Hvi)".
    assert (ly_size ly' = ly_size ly2) as Hszeq'. { apply Hszeq; done. }
    iSplitL "Hsc Hsc1". { by iApply "Hsc". }
    rewrite -Hszeq'. iFrame. iR.
    iExists r2. iR. iMod "Hl" as "(%v & Hl & Hv)".
    iModIntro. iExists _. iFrame.
    by iApply "Hvi".
  Qed.

  Lemma owned_type_incl_uninit' π {rt1} (r1 : rt1) r2 (ty1 : type rt1) st ly :
    syn_type_size_eq (ty_syn_type ty1) st →
    syn_type_has_layout st ly →
    ⊢ owned_type_incl π r1 r2 ty1 (uninit st).
  Proof.
    iIntros (Hst ?). iSplitR; last iSplitR.
    - iPureIntro. done.
    - simpl. eauto.
    - iIntros (v) "Hv". iEval (rewrite /ty_own_val/=).
      iPoseProof (ty_has_layout with "Hv") as "(%ly' & %Hst' & %Hly)".
      iExists ly. iR. iSplitR. { iPureIntro. rewrite /has_layout_val Hly. apply Hst; done. }
      iPureIntro. eapply Forall_forall.  eauto.
  Qed.
  Lemma owned_type_incl_uninit π {rt1} (r1 : rt1) r2 (ty1 : type rt1) st :
    st = ty_syn_type ty1 →
    ⊢ owned_type_incl π r1 r2 ty1 (uninit st).
  Proof.
    iIntros (Hst). iSplitR; last iSplitR.
    - iPureIntro. iIntros (?? Hst1 Hst2). subst st. simpl in *.
      f_equiv. by eapply syn_type_has_layout_inj.
    - simpl. eauto.
    - iIntros (v) "Hv". iEval (rewrite /ty_own_val/=).
      iPoseProof (ty_has_layout with "Hv") as "(%ly & %Hst' & %Hly)".
      iExists ly. subst st. iR.  iR. iPureIntro.
      eapply Forall_forall.  eauto.
  Qed.

End lemmas.

Section typing.
  Context `{!typeGS Σ}.

  (** ** Instances for deinitializing a type *)

  (*
li_tactic (compute_layout_goal (ty_syn_type ty1)) (λ ly1,
      (* augment context *) ⌜syn_type_has_layout (ty_syn_type ty1) ly1⌝ -∗
      li_tactic (compute_layout_goal (ty_syn_type ty2)) (λ ly2,
        (* augment context *) ⌜syn_type_has_layout (ty_syn_type ty2) ly2⌝ -∗
        ⌜l `has_layout_loc` ly1⌝ -∗ ⌜l `has_layout_loc` ly2⌝ ∗ owned_subtype π E L false r1 r2 ty1 ty2 (λ L', T L' True%I)))
        *)

  (* Two low-priority instances that trigger as a fallback for ltypes foldable to a ty (no borrows below) *)
  Lemma owned_subltype_step_ofty_uninit π E L {rt} (lt : ltype rt) r st l T :
    cast_ltype_to_type E L lt (λ ty,
    li_tactic (compute_layout_goal (ty_syn_type ty)) (λ ly1,
      ⌜syn_type_has_layout (ty_syn_type ty) ly1⌝ -∗
      li_tactic (compute_layout_goal st) (λ ly2,
        ⌜syn_type_has_layout st ly2⌝ -∗
        ⌜l `has_layout_loc` ly1⌝ -∗ ⌜l `has_layout_loc` ly2⌝ ∗ 
        ⌜ly_size ly1 = ly_size ly2⌝ ∗
        T L (ty_ghost_drop ty π r))))
    ⊢ owned_subltype_step π E L l #r #() lt (◁ uninit st) T.
  Proof.
    iDestruct 1 as "(%ty & %Heqt & HT)".
    rewrite /compute_layout_goal.
    iDestruct "HT" as "(%ly1 & %Hst1 & HT)".
    iDestruct ("HT" with "[//]") as "(%ly2 & %Hst2 & HT)".
    iIntros (??) "CTX HE HL Hl". simp_ltypes; simpl.

    iPoseProof (full_eqltype_acc with "CTX HE HL") as "#Hincl"; first apply Heqt.
    iSpecialize ("Hincl" $! (Owned false) (#r)).
    iDestruct "Hincl" as "(Hincl & _)". iDestruct "Hincl" as "(%Hst & Hincl & _)".
    iMod (ltype_incl'_use with "Hincl Hl") as "Hl"; first done.

    iPoseProof (ltype_own_has_layout' with "Hl") as "%". { simp_ltype. rewrite Heq_lt. done. }
    iDestruct ("HT" with "[//] [//]") as "(%Hly' & %Hsz & HT)".
    
    iExists _, _. iFrame.
    assert (syn_type_size_eq (ltype_st lt) st) as ?.
    { rewrite Hst ltype_st_ofty. 
      intros ly3 ly4 Hst3 Hst4. 
      assert (ly3 = ly1) as -> by by eapply syn_type_has_layout_inj.
      assert (ly4 = ly2) as -> by by eapply syn_type_has_layout_inj.
      done. }
    iSplitL.
    { iMod lc_zero as "Hlc".
      iMod (ofty_own_split_value_untyped_lc with "[Hlc] Hl") as "(%v & Hv & Hl)"; [done.. | ].
      iPoseProof (ty_own_ghost_drop with "Hv") as "Hb"; first done.
      iApply (logical_step_wand with "Hb"). iModIntro. iIntros "$".
      iApply (ofty_owned_subtype_aligned with "[] Hl"); [done | | ].
      { done. }
      iApply owned_type_incl_uninit'; last done.
      simpl. 
      intros ?? (-> & _)%syn_type_has_layout_untyped_inv Hst4. 
      assert (ly2 = ly3) as <- by by eapply syn_type_has_layout_inj. done.
    }
    iPureIntro. done.
  Qed.
  Global Instance owned_subltype_step_ofty_uninit_inst π E L l {rt} (lt : ltype rt) r st :
    OwnedSubltypeStep π E L l #r #() lt (◁ uninit st)%I | 101:=
    λ T, i2p (owned_subltype_step_ofty_uninit π E L lt r st l T).

  (*
  Lemma owned_subltype_step_ofty_uninit π E L {rt} (lt : ltype rt) r st T :
    cast_ltype_to_type E L lt (λ ty,
    li_tactic (compute_layout_goal (ty_syn_type ty)) (λ ly1,
      li_tactic (compute_layout_goal st) (λ ly2,
        ⌜ly1 = ly2⌝ ∗ T L (ty_ghost_drop ty π r))))
    ⊢ owned_subltype_step π E L #r #() lt (◁ uninit st) T.
  Proof.
    iDestruct 1 as "(%ty & %Heqt & HT)".
    rewrite /compute_layout_goal.
    iDestruct "HT" as "(%ly1 & %Hst1 & %ly2 & %Hst2 & <- & HT)".
    iIntros (???) "CTX HE HL Hl". simp_ltypes; simpl.
    iPoseProof (full_eqltype_acc with "CTX HE HL") as "#Hincl"; first apply Heqt.
    iSpecialize ("Hincl" $! (Owned false) (#r)).
    iDestruct "Hincl" as "(Hincl & _)". iDestruct "Hincl" as "(%Hst & Hincl & _)".
    iMod (ltype_incl'_use with "Hincl Hl") as "Hl"; first done.
    iExists _, _. iFrame.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hl" as "(%ly & %Halg & %Hly & Hsc & Hlb & _ & %r' & <- & Hb)".
    assert (ly1 = ly) as -> by by eapply (syn_type_has_layout_inj (ty_syn_type ty)).
    iMod (fupd_mask_mono with "Hb") as "(%v & Hl & Hv)"; first done.
    iModIntro. iSplitL.
    { iPoseProof (ty_own_val_has_layout with "Hv") as "%Hlyv"; first done.
      iPoseProof (ty_own_ghost_drop with "Hv") as "Hb"; first done.
      iApply (logical_step_wand with "Hb"). iIntros "$".
      rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iExists _. iR. iR. simpl. iR. iFrame. iR.
      iExists _. iR. iModIntro. iExists _. iFrame.
      rewrite uninit_own_spec. eauto. }
    iPureIntro.
    iIntros (ly1' ly2' Hst1' Hst2').
    rewrite Hst in Hst1'. simp_ltypes in Hst1'.
    assert (ly1' = ly) as -> by by eapply syn_type_has_layout_inj.
    assert (ly2' = ly) as -> by by eapply syn_type_has_layout_inj.
    done.
  Qed.
  Global Instance owned_subltype_step_ofty_uninit_inst π E L {rt} (lt : ltype rt) r st :
    OwnedSubltypeStep π E L #r #() lt (◁ uninit st)%I | 101:=
    λ T, i2p (owned_subltype_step_ofty_uninit π E L lt r st T).
  *)

  (* TODO move *)
  Lemma syn_type_has_layout_untyped_mono ly1 ly2 : 
    ly_align_log ly2 ≤ ly_align_log ly1 →
    ly_size ly1 = ly_size ly2 →
    syn_type_has_layout (UntypedSynType ly1) ly1 →
    syn_type_has_layout (UntypedSynType ly2) ly2.
  Proof.
    intros ?? Hut. apply syn_type_has_layout_untyped_inv in Hut as (_ & Hwf & Hsz & Hal).
    apply syn_type_has_layout_untyped; first done. 
    - eapply layout_wf_mono; done.
    - lia.
    - by eapply ly_align_in_bounds_mono.
  Qed.

  (* Higher-priority instacne for the special case that we go to Untyped *)
  Lemma owned_subltype_step_ofty_uninit_untyped π E L l {rt} (lt : ltype rt) r ly T :
    cast_ltype_to_type E L lt (λ ty,
      li_tactic (compute_layout_goal (ty_syn_type ty)) (λ ly1,
      ⌜syn_type_has_layout (ty_syn_type ty) ly1⌝ -∗ 
      ⌜l `has_layout_loc` ly⌝ ∗
      ⌜syn_type_has_layout (UntypedSynType ly) ly⌝ ∗
      (⌜l `has_layout_loc` ly1⌝ -∗
      ⌜ly_size ly1 = ly_size ly⌝ ∗ T L (ty_ghost_drop ty π r))))
    ⊢ owned_subltype_step π E L l #r #() lt (◁ uninit (UntypedSynType ly)) T.
  Proof.
    iDestruct 1 as "(%ty & %Heqt & HT)".
    rewrite /compute_layout_goal.
    iDestruct "HT" as "(%ly1 & %Hst & HT)".
    iApply owned_subltype_step_ofty_uninit.
    iExists ty. iR.
    iExists ly1. iR. iIntros (_). iExists ly.
    iPoseProof ("HT" with "[//]") as "(%Hly & %Hwf & HT)". 
    iR. 
    (*iSplitR. { iPureIntro. *)
      (*eapply (syn_type_has_layout_untyped_mono ly1); [done.. | ].*)
      (*by eapply syn_type_has_layout_make_untyped. }*)
    iIntros (? ?). 
    iPoseProof ("HT" with "[//]") as "(%Hsz & ?)".
    iR. iR. done.
  Qed.
  Global Instance owned_subltype_step_ofty_uninit_untyped_inst π E L l {rt} (lt : ltype rt) r ly :
    OwnedSubltypeStep π E L l #r #() lt (◁ uninit (UntypedSynType ly))%I | 100 :=
    λ T, i2p (owned_subltype_step_ofty_uninit_untyped π E L l lt r ly T).
  
  (*
  Lemma owned_subltype_step_ofty_uninit_untyped π E L {rt} (lt : ltype rt) r ly T :
    cast_ltype_to_type E L lt (λ ty,
    ⌜syn_type_has_layout (ty_syn_type ty) ly⌝ ∗ T L (ty_ghost_drop ty π r))
    ⊢ owned_subltype_step π E L #r #() lt (◁ uninit (UntypedSynType ly)) T.
  Proof.
    iDestruct 1 as "(%ty & %Heqt & HT)".
    iDestruct "HT" as "(%Hst & HT)".
    iApply owned_subltype_step_ofty_uninit.
    iExists ty. iR.
    iExists ly. iR. iExists ly.
    iSplitR. { iPureIntro. by eapply syn_type_has_layout_make_untyped. }
    iR. done.
  Qed.
  Global Instance owned_subltype_step_ofty_uninit_untyped_inst π E L {rt} (lt : ltype rt) r ly :
    OwnedSubltypeStep π E L #r #() lt (◁ uninit (UntypedSynType ly))%I | 100 :=
    λ T, i2p (owned_subltype_step_ofty_uninit_untyped π E L lt r ly T).
   *)

  (* More specific instances *)
  Lemma owned_subltype_step_shrltype_uninit π E L {rt} (lt : ltype rt) r st κ l T  :
    ⌜syn_type_compat PtrSynType st⌝ ∗ T L True%I
    ⊢ owned_subltype_step π E L l r #() (ShrLtype lt κ) (◁ uninit st) T.
  Proof.
    iIntros "(%Hstcomp & HT)".
    iIntros (??) "CTX HE HL Hl". simp_ltypes; simpl.
    iMod (ltype_deinit_shr with "Hl") as "Hl"; [done.. | ].
    iExists _, _. iFrame.
    iSplitL. { iApply logical_step_intro. by iFrame. }
    iModIntro. iPureIntro. intros ?? Hst1 Hst2.
    destruct Hstcomp as [<- | (ly1' & Hst' & ->)]. 
    + f_equiv. by eapply syn_type_has_layout_inj.
    + eapply syn_type_has_layout_untyped_inv in Hst2 as (<- & _).
      f_equiv. by eapply syn_type_has_layout_inj.
  Qed.
  Global Instance owned_subltype_step_shrltype_uninit_inst π E L {rt} (lt : ltype rt) r st κ l :
    OwnedSubltypeStep π E L l (r) #() (ShrLtype lt κ) (◁ uninit st)%I | 20 :=
    λ T, i2p (owned_subltype_step_shrltype_uninit π E L lt r st κ l T).

  Lemma owned_subltype_step_mutltype_uninit π E L {rt} (lt : ltype rt) r γ st κ l T  :
    match ltype_uniq_extractable lt with
    | None => False
    | Some κm =>
        ⌜syn_type_compat PtrSynType st⌝ ∗ T L (MaybeInherit κm InheritGhost (place_rfn_interp_mut_extracted r γ))
    end
    ⊢ owned_subltype_step π E L l #(r, γ) #() (MutLtype lt κ) (◁ uninit st) T.
  Proof.
    iIntros "HT".
    iIntros (??) "CTX HE HL Hl". simp_ltypes; simpl.
    destruct (ltype_uniq_extractable lt) eqn:Hextract; last done.
    iDestruct "HT" as "(%Hstcomp & HT)".
    iExists _, _. iFrame.
    iMod (ltype_uniq_extractable_deinit_mut with "Hl") as "(Hl & Hf)"; [done.. | ].
    iPoseProof (MaybeInherit_update (place_rfn_interp_mut_extracted r γ) with "[] Hf") as "Hf".
    { iIntros (?) "Hrfn". iMod (place_rfn_interp_mut_extract with "Hrfn") as "?". done. }
    iModIntro. iSplitL. { iApply logical_step_intro. iFrame. }
    iPureIntro. iIntros (ly1 ly2 Halg1 Halg2).
    specialize (syn_type_compat_layout_trans _ _ _ Hstcomp Halg2) as ?.
    f_equiv. by eapply syn_type_has_layout_inj.
  Qed.
  Global Instance owned_subltype_step_mutltype_uninit_inst π E L {rt} (lt : ltype rt) r γ st κ l :
    OwnedSubltypeStep π E L l #(r, γ) #() (MutLtype lt κ) (◁ uninit st)%I | 20 :=
    λ T, i2p (owned_subltype_step_mutltype_uninit π E L lt r γ st κ l T).

  (*Lemma owned_subltype_step_cast_to_type_uninit : *)
    (*cast_ltype_to_type E L lt (λ ty, *)
      (*⌜syn_type_compat (ty_syn_type ty) st⌝ ∗ T L (ty_ghost_drop ty)) -∗*)
    (*owned_subltype_step π E L r #() lt (◁ uninit st) T.*)

  (* TODO have fallback instance that uses cast_ltype *)

  (* TODO more instances for other ltypes under which borrows can happen, e.g. for structs *)

  (* Fallback without a logical step -- here, we cannot ghost_drop *)
  (* TODO: maybe restrict this instance more for earlier failure *)
  Lemma uninit_mono E L l {rt} (ty : type rt) r π st T :
    (li_tactic (compute_layout_goal st) (λ ly, ⌜syn_type_has_layout ty.(ty_syn_type) ly⌝ ∗ (∀ v, v ◁ᵥ{π} r @ ty -∗ T L True%I)))
    ⊢ subsume_full E L false (l ◁ₗ[π, Owned false] #r @ (◁ ty)) (l ◁ₗ[π, Owned false] .@ (◁ (uninit st))) T.
  Proof.
    rewrite /compute_layout_goal.
    iIntros "(%ly & %Halg1 & %Halg2 & HT)".
    iIntros (???) "#CTX #HE HL Hl".
    rewrite !ltype_own_ofty_unfold /lty_of_ty_own. simpl.
    iDestruct "Hl" as "(%ly' & %Halg & %Hly & Hsc & ? & ? & %r' & <- & Hv)".
    iMod (fupd_mask_mono with "Hv") as "(%v & Hl & Hv)"; first done.
    iPoseProof (ty_own_val_has_layout with "Hv") as "%"; first done.
    iExists L, True%I. iPoseProof ("HT" with "Hv") as "$". iFrame "HL".
    rewrite right_id. assert (ly' = ly) as -> by by eapply syn_type_has_layout_inj.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own. simpl.
    iExists ly. iSplitR; first done. iSplitR; first done.
    iSplitR; first done. iFrame. iExists _. iSplitR; first done.
    iModIntro. iModIntro. iExists v. iFrame.
    iExists ly. iSplitR; first done. iSplitR; first done.
    iPureIntro. rewrite Forall_forall. done.
  Qed.
  Global Instance uninit_mono_inst π E L l {rt} (ty : type rt) (r : rt) st :
    SubsumeFull E L false (l ◁ₗ[π, Owned false] PlaceIn r @ (◁ ty))%I (l ◁ₗ[π, Owned false] .@ ◁ (uninit st))%I | 40 :=
    λ T, i2p (uninit_mono E L l ty r π st T).


  (** We have this instance because it even works when [r1 = PlaceGhost ..] *)
  Lemma weak_subltype_deinit E L {rt1} (r1 : place_rfn rt1) r2 (ty : type rt1) st T :
    ⌜ty_syn_type ty = st⌝ ∗ T
    ⊢ weak_subltype E L (Owned false) r1 #r2 (◁ ty) (◁ uninit st) T.
  Proof.
    iIntros "(%Hst & HT)".
    iIntros  (??) "#CTX #HE HL". iFrame.
    iModIntro. iModIntro. simp_ltypes. iR.
    rewrite -bi.persistent_sep_dup.
    iModIntro. iIntros (??) "Hl".
    iPoseProof (ltype_own_has_layout with "Hl") as "(%ly & %Hst' & %Hly)".
    iModIntro. iApply (ofty_owned_subtype_aligned' with "[] Hl").
    { simp_ltypes in Hst'. simpl. subst st. apply Hst'. }
    { done. }
    iIntros. iApply owned_type_incl_uninit. done.
  Qed.
  Global Instance weak_subltype_deinit_inst E L {rt1} (r1 : place_rfn rt1) r2 (ty : type rt1) st :
    SubLtype E L (Owned false) r1 #r2 (◁ ty)%I (◁ uninit st)%I := λ T, i2p (weak_subltype_deinit E L r1 r2 ty st T).

  (** ** Subsumption with uninit on the LHS (for initializing) *)
  (* TODO consider: we could also support the case where ty just takes a prefix of the chunk. *)
  Lemma subsume_full_ofty_owned_subtype π E L step l {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) r1 r2 T :
    li_tactic (compute_layout_goal (ty_syn_type ty1)) (λ ly1,
      (* augment context *) ⌜syn_type_has_layout (ty_syn_type ty1) ly1⌝ -∗
      li_tactic (compute_layout_goal (ty_syn_type ty2)) (λ ly2,
        (* augment context *) ⌜syn_type_has_layout (ty_syn_type ty2) ly2⌝ -∗
        ⌜l `has_layout_loc` ly1⌝ -∗ ⌜l `has_layout_loc` ly2⌝ ∗ owned_subtype π E L false r1 r2 ty1 ty2 (λ L', T L' True%I)))
    ⊢ subsume_full E L step (l ◁ₗ[π, Owned false] #r1 @ ◁ ty1) (l ◁ₗ[π, Owned false] #r2 @ ◁ ty2) T.
  Proof.
    rewrite /compute_layout_goal. iIntros "(%ly1 & %Halg1 & HT)".
    iDestruct ("HT" with "[//]") as "(%ly2 & %Halg2 & HT)".
    iIntros (???) "#CTX #HE HL Hl".
    iPoseProof (ltype_own_has_layout with "Hl") as "(%ly1' & %Halg1' & %Hlyl)".
    assert (ly1' = ly1) as -> by by eapply syn_type_has_layout_inj.
    iDestruct ("HT" with "[//] [//]") as "(%Hl_ly2 & Hsubt)".
    iMod ("Hsubt" with "[//] [//] CTX HE HL") as "(%L' & Hv & ? & ?)".
    iExists L', True%I. iFrame.
    iApply maybe_logical_step_intro. rewrite right_id.
    iApply (ofty_owned_subtype_aligned with "Hv Hl"); done.
  Qed.
  (** We only declare an instance for this where the LHS is uninit -- generally, we'd rather want to  go via the "full subtyping" judgments,
    because the alignment sidecondition here may be hard to prove explicitly. *)
  Global Instance subsume_full_ofty_uninit_owned_subtype_inst π E L step l {rt2} (ty2 : type rt2) r2 st :
    SubsumeFull E L step (l ◁ₗ[π, Owned false] .@ ◁ (uninit st))%I (l ◁ₗ[π, Owned false] #r2 @ ◁ ty2)%I | 30 :=
    λ T, i2p (subsume_full_ofty_owned_subtype π E L step l (uninit st) ty2 () r2 T).

  Lemma owned_subtype_to_uninit π E L pers {rt} (ty1 : type rt) r st2 T :
    li_tactic (compute_layout_goal (ty_syn_type ty1)) (λ ly1,
      (* augment context *) ⌜syn_type_has_layout (ty_syn_type ty1) ly1⌝ -∗
      li_tactic (compute_layout_goal st2) (λ ly2,
        (* augment context *) ⌜syn_type_has_layout st2 ly2⌝ -∗ ⌜ly_size ly1 = ly_size ly2⌝ ∗ T L))
    ⊢ owned_subtype π E L pers r () (ty1) (uninit st2) T.
  Proof.
    rewrite /compute_layout_goal.
    iIntros "(%ly1 & %Hst1 & HT)".
    iDestruct ("HT" with "[//]") as "(%ly2 & %Hst2 & HT)".
    iDestruct ("HT" with "[//]") as "(%Hsz & HT)".
    iIntros (???) "#CTX #HE HL".
    iModIntro. iExists _. iFrame. iApply bi.intuitionistically_intuitionistically_if.
    iModIntro.
    iSplit; last iSplitR.
    - iPureIntro. simpl. iIntros (ly1' ly2' Hst1' Hst2').
      assert (ly1' = ly1) as -> by by eapply syn_type_has_layout_inj.
      assert (ly2' = ly2) as -> by by eapply syn_type_has_layout_inj.
      done.
    - simpl. eauto.
    - iIntros (v) "Hv".
      rewrite {2}/ty_own_val/=.
      iPoseProof (ty_own_val_has_layout with "Hv") as "%Hv"; first done.
      (*iIntros "(%ly & %Hst & %Hly & Hv)".*)
      iExists _. iR. iSplitL.
      + iPureIntro. move: Hv. rewrite /has_layout_val Hsz//.
      + iPureIntro. apply Forall_forall. eauto.
  Qed.
  Global Instance owned_subtype_to_uninit_inst π E L pers {rt} (ty : type rt) r st2 :
    OwnedSubtype π E L pers r () (ty) (uninit st2) :=
    λ T, i2p (owned_subtype_to_uninit π E L pers ty r st2 T).


  (** ** Evar instantiation *)
  Lemma uninit_mono_untyped_evar π E L step l ly1 ly2 T `{!IsProtected ly2} :
    ⌜ly1 = ly2⌝ ∗ T L True%I
    ⊢ subsume_full E L step (l ◁ₗ[π, Owned false] .@ (◁ uninit (UntypedSynType ly1))) (l ◁ₗ[π, Owned false] .@ (◁ uninit (UntypedSynType ly2))) T.
  Proof. iIntros "(-> & HT)". iApply subsume_full_subsume. iFrame. eauto. Qed.
  Global Instance uninit_mono_untyped_evar_inst π E L step l ly1 ly2 `{!IsProtected ly2} :
    SubsumeFull E L step (l ◁ₗ[π, Owned false] .@ (◁ uninit (UntypedSynType ly1)))%I (l ◁ₗ[π, Owned false] .@ (◁ uninit (UntypedSynType ly2)))%I | 10 :=
    λ T, i2p (uninit_mono_untyped_evar π E L step l ly1 ly2 T).

  Lemma uninit_mono_untyped_id E L π step l (ly1 ly2 : layout) T `{TCDone (ly1 = ly2)}:
    T L True%I
    ⊢ subsume_full E L step (l ◁ₗ[π, Owned false] .@ (◁ uninit (UntypedSynType ly1))) (l ◁ₗ[π, Owned false] .@ (◁ uninit (UntypedSynType ly2))) T.
  Proof.
    match goal with
    | H : TCDone _ |- _ => rename H into Heq
    end.
    rewrite /TCDone in Heq. subst. iIntros "HL".
    iApply subsume_full_subsume. iFrame. eauto.
  Qed.
  Global Instance uninit_mono_untyped_id_inst E L step π l (ly1 ly2 : layout) `{!TCDone (ly1 = ly2)} :
    SubsumeFull E L step (l ◁ₗ[π, Owned false] .@ (◁ uninit (UntypedSynType ly1)))%I (l ◁ₗ[π, Owned false] .@ (◁ uninit (UntypedSynType ly2)))%I | 11 :=
    λ T, i2p (uninit_mono_untyped_id E L π step l ly1 ly2 T).
End typing.
