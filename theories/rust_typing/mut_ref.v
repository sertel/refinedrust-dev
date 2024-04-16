From caesium Require Import derived.
From refinedrust Require Export base type ltypes.
From refinedrust Require Import programs ltype_rules.

Local Definition ref_layout := void_ptr.

(*Global Hint Extern 4 (Inhabited _) => refine (populate _); assumption : typeclass_instances.*)

(** * Mutable references *)
Section mut_ref.
  Context `{typeGS Σ}.
  Implicit Types (κ : lft) (γ : gname).

  (* Mutable references only really make sense when the inner type is a refinement type,
    because we cannot make strong updates to the inner type -- thus the inner refinement needs to be
     exposed through the mutable reference's refinement *)
  Program Definition mut_ref {rt} (κ : lft) (inner : type rt) : type (place_rfn rt * gname) := {|
    ty_sidecond := True;
    ty_own_val π '(r, γ) v :=
      (∃ (l : loc) (ly : layout), ⌜v = l⌝ ∗
      ⌜use_layout_alg inner.(ty_syn_type) = Some ly⌝ ∗
      ⌜l `has_layout_loc` ly⌝ ∗
      loc_in_bounds l 0 ly.(ly_size) ∗
      inner.(ty_sidecond) ∗
      place_rfn_interp_mut r γ ∗
      have_creds ∗
      |={lftE}=> &pin{κ} (∃ r' : rt, gvar_auth γ r' ∗ |={lftE}=> l ↦: inner.(ty_own_val) π r'))%I;

    _ty_has_op_type ot mt := is_ptr_ot ot;
    ty_syn_type := PtrSynType;

    ty_shr κ' tid '(r, γ) l :=
      (∃ (li : loc) (ly : layout) (r' : rt),
        ⌜l `has_layout_loc` void*⌝ ∗
        place_rfn_interp_shared r r' ∗
          &frac{κ'}(λ q', l ↦{q'} li) ∗
          (* needed explicity because there is a later + fupd over the sharing predicate *)
          ⌜use_layout_alg inner.(ty_syn_type) = Some ly⌝ ∗
          ⌜li `has_layout_loc` ly⌝ ∗
          loc_in_bounds l 0 void*.(ly_size) ∗
          loc_in_bounds li 0 ly.(ly_size) ∗
          inner.(ty_sidecond) ∗
          (* we still need a later for contractiveness *)
          ▷ □ (|={lftE}=> inner.(ty_shr) (κ⊓κ') tid r' li))%I;
    (* NOTE: we cannot descend below the borrow here to get more information recursively.
       But this is fine, since the observation about γ here already contains all the information we need. *)
    ty_ghost_drop _ '(r, γ) :=
    (*place_rfn_interp_mut r γ;*)
      match r with
      | #r' => gvar_pobs γ r'
      | PlaceGhost γ' => Rel2 γ' γ (@eq rt)
      end;
    ty_lfts := [κ] ++ inner.(ty_lfts);
    ty_wf_E := ty_outlives_E inner κ;
  |}.
  Next Obligation.
    iIntros (? κ ? π [r γ] v) "(%l & %ly & -> & _)". eauto.
  Qed.
  Next Obligation.
    iIntros (??? ot Hot) => /=. destruct ot => /=// -> //.
  Qed.
  Next Obligation.
    iIntros (? κ ? π r v) "_". done.
  Qed.
  Next Obligation.
    iIntros (? κ ? ? π r v) "_". done.
  Qed.
  Next Obligation.
    iIntros (? κ ? κ' π l [r γ]). apply _.
  Qed.
  Next Obligation.
    iIntros (??????[r γ]) "(%li & %ly & %r' & ? & ? &  _)". eauto.
  Qed.
  Next Obligation.
    (* initiate sharing *)
    (*
       Plan:
       - get the borrow containing the credit + atime.
       - open the borrows to obtain the receipts.
       - use the credit (will need more than one) to bring the nested borrow in the right shape.
         will need:
          + 1 credit/later for the fupd_later
          + 1 credit for folding the pinned borrow
            + 1 credit for unfoldign the pinned borrow
          + 1 credit/later for getting rid of the second fupd after unnesting
          + 1 credit/later for unnesting
        - then do recursive sharing and eliminate the logical_step for that.
        - introduce the logical step, using the time receipt.
        - after getting the credits and the receipt back, can close the two borrows
        - can now prove the conclusion.

    *)

    iIntros (? κ ? E κ' l ly π [r γ] q ?) "#[LFT TIME] Htok %Hst %Hly _ Hb".
    iApply fupd_logical_step.
    iMod (bor_exists with "LFT Hb") as (v) "Hb"; first solve_ndisj.
    iMod (bor_sep with "LFT Hb") as "(Hl & Hb)"; first solve_ndisj.
    simpl. rewrite -{1}lft_tok_sep -{1}lft_tok_sep. iDestruct "Htok" as "[Htok_κ' [Htok_κ Htok]]".

    iMod (bor_exists with "LFT Hb") as (l0) "Hb"; first solve_ndisj.
    iMod (bor_exists with "LFT Hb") as (ly0) "Hb"; first solve_ndisj.
    iMod (bor_sep with "LFT Hb") as "(Ha & Hb)"; first solve_ndisj.
    iMod (bor_persistent with "LFT Ha Htok_κ'") as "(>-> & Htok_κ')"; first solve_ndisj.
    iMod (bor_sep with "LFT Hb") as "(Ha & Hb)"; first solve_ndisj.
    iMod (bor_persistent with "LFT Ha Htok_κ'") as "(>%Halg & Htok_κ')"; first solve_ndisj.
    iMod (bor_sep with "LFT Hb") as "(Ha & Hb)"; first solve_ndisj.
    iMod (bor_persistent with "LFT Ha Htok_κ'") as "(>%Hly0 & Htok_κ')"; first solve_ndisj.
    iMod (bor_sep with "LFT Hb") as "(Ha & Hb)"; first solve_ndisj.
    iMod (bor_persistent with "LFT Ha Htok_κ'") as "(>#Hlb & Htok_κ')"; first solve_ndisj.
    iMod (bor_sep with "LFT Hb") as "(Ha & Hb)"; first solve_ndisj.
    iMod (bor_persistent with "LFT Ha Htok_κ'") as "(>#Hsc & Htok_κ')"; first solve_ndisj.
    iMod (bor_sep with "LFT Hb") as "(Hobs & Hb)"; first solve_ndisj.
    iMod (bor_sep with "LFT Hb") as "(Hcred & Hb)"; first solve_ndisj.
    iDestruct "Htok_κ'" as "(Htok_κ' & Htokc)".
    iMod (bor_acc with "LFT Hcred Htokc") as "(>(Hcred & Hat) & Hclos_c)"; first solve_ndisj.

    (* unnest the pinned borrow *)
    rewrite /num_cred. assert (5 = 2 + 3) as Heq by lia.
    rewrite {1}Heq. iDestruct "Hcred" as "(Hcred1 & Hcred)".
    iMod (pinned_bor_unnest_full with "LFT Hcred1 Htok_κ' Hb") as "Hb"; first done.
    iDestruct "Hcred" as "(Hcred1 & Hcred2 & Hcred)".
    iApply (lc_fupd_add_later with "Hcred1"). iNext.
    iMod "Hb". iMod "Hb".
    iApply (lc_fupd_add_later with "Hcred2"). iNext.
    iMod "Hb" as "(Hb & Htok_κ')".
    rewrite lft_intersect_comm.

    iDestruct "Htok_κ" as "(Htok_κ & Htok_κ2)".
    iCombine "Htok_κ Htok_κ'" as "Htoka". rewrite lft_tok_sep.
    iMod (bor_exists_tok with "LFT Hb Htoka") as "(%r' & Hb & Htoka)"; first solve_ndisj.
    iMod (bor_sep with "LFT Hb") as "(Hauth & Hb)"; first solve_ndisj.
    iMod (bor_fupd_later with "LFT Hb Htoka") as "Hu"; [done.. | ].
    iApply (lc_fupd_add_later with "Hcred"). iNext. iMod "Hu" as "(Hb & Htoka)".

    (* gain knowledge about the refinement *)
    iMod (place_rfn_interp_mut_share with "LFT [Hobs] Hauth Htoka") as "(#rfn & _ & _ & Htoka)"; first done.
    { iApply bor_shorten; last done. iApply lft_intersect_incl_r. }
    iDestruct "Htoka" as "(Htoka & Htoka2)".
    rewrite -{1}lft_tok_sep. iDestruct "Htoka" as "(Htok_κ & Htok_κ')".

    (* get a loc_in_bounds fact from the pointsto *)
    iMod (bor_acc with "LFT Hl Htok_κ'") as "(>Hl & Hcl_l)"; first solve_ndisj.
    iPoseProof (heap_mapsto_loc_in_bounds with "Hl") as "#Hlb'".
    iMod ("Hcl_l" with "Hl") as "(Hl & Htok_κ')".
    iCombine "Htok_κ Htok_κ'" as "Htoka1". rewrite lft_tok_sep.
    iCombine "Htoka1 Htoka2" as "Htoka".

    (* fracture *)
    iMod (bor_fracture (λ q, l ↦{q} l0)%I with "LFT Hl") as "Hl"; first solve_ndisj.

    (* recursively share *)
    iDestruct "Htok" as "(Htok1 & Htok2)".
    iPoseProof (ty_share _ E with "[$LFT $TIME] [Htok2 Htoka] [//] [//] Hlb Hb") as "Hu"; first solve_ndisj.
    { rewrite -!lft_tok_sep. iFrame. }
    iModIntro. iApply (logical_step_compose with "Hu").
    iApply (logical_step_intro_atime with "Hat").
    iIntros "Hcred Hat".
    iMod ("Hclos_c" with "[Hcred Hat]") as "(_ & Htok_κ'2)".
    { iNext. iFrame. }

    iModIntro. iIntros "(#Hshr & Htok)".
    iCombine "Htok_κ2 Htok_κ'2 Htok1" as "Htok2".
    rewrite !lft_tok_sep.
    rewrite lft_intersect_assoc.
    iCombine "Htok Htok2" as "Htok". rewrite {2}lft_intersect_comm lft_intersect_assoc. iFrame "Htok".
    iExists l0, ly0, r'. iFrame "Hl".
    inversion Hst; subst ly.
    iR. iSplitR. { destruct r; simpl; eauto. }
    iSplitR; first done. iSplitR; first done.
    iSplitR; first done.
    iSplitR; first done. iSplitR; first done.
    iNext. iModIntro. iModIntro. done.
  Qed.
  Next Obligation.
    iIntros (? κ ? κ0 κ' π [r γ] l) "#Hincl".
    iIntros "(%li & %ly & %r' & Hly & Hrfn & Hf & ? & ? & ? & ? & ? & #Hb)".
    iExists li, ly, r'. iFrame.
    iSplitL "Hf". { iApply frac_bor_shorten; done. }
    iNext. iDestruct "Hb" as "#Hb". iModIntro. iMod "Hb". iModIntro.
    iApply ty_shr_mono; last done.
    iApply lft_intersect_mono; last done. iApply lft_incl_refl.
  Qed.
  Next Obligation.
    iIntros (????[r γ]???) "(%l & %ly & -> & _ & _ & _ & _ & Hrfn & Hcred &  _)".
    iApply fupd_logical_step. destruct r as [ r | γ'].
    - iMod (gvar_obs_persist with "Hrfn") as "?".
      iApply logical_step_intro. by iFrame.
    - by iApply logical_step_intro.
  Qed.
  Next Obligation.
    iIntros (??? ot mt st ? [r γ] ? Hot).
    destruct mt.
    - eauto.
    - iIntros "(%l & %ly & -> & ?)". iExists l, ly. iFrame.
      iPureIntro. move: ot Hot => [] /=// _.
      rewrite /mem_cast val_to_of_loc //.
    - iApply (mem_cast_compat_loc (λ v, _)); first done.
      iIntros "(%l & %ly & -> & _)". eauto.
  Qed.
End mut_ref.

Section contractive.
  Context `{!typeGS Σ}.

  (* Point: 
     We probably need a different definition of contractiveness and non-expansiveness that takes these things into account.
     We need a semantic notion of functors "preserving" the lifetime information in a good way.


   *)

  Lemma mut_ref_contractive {rt} κ : TypeContractive (mut_ref (rt:=rt) κ).
  Proof.
    intros n ty1 ty2 Heq.
    constructor.
    - done. 
    - 
      admit.
    - 
      admit.
    - done.
    - rewrite !ty_has_op_type_unfold/=; done.
    - admit.
    - admit. 
    - done.
    - done. 
      (* TODO: for the pure requirements, we have a problem. 
          We could try to remove the pure requirements, but then it won't be sufficient for taking a fixpoint.

      *)
      (*apply Heq.*)
  Abort.
End contractive.

Section ofty.
  Context `{!typeGS Σ}.

  (** A very fundamental equivalence that should hold. *)
  Lemma mut_ref_ofty_uniq_equiv {rt} (ty : type rt) π κ l r γ :
    l ◁ₗ[π, Uniq κ γ] #r @ (◁ ty) ⊣⊢ l ◁ᵥ{π} (#r, γ) @ mut_ref ty κ.
  Proof.
    rewrite ltype_own_ofty_unfold/lty_of_ty_own {3}/ty_own_val/=.
    iSplit.
    - iIntros "(%ly & %Hst & %Hly & #Hsc & #Hlb & Hc & Hobs & Hb)".
      iExists _, _. iR. iR. iR. iFrame "# ∗".
    -iIntros "(%l' & %ly & %Hl & % & % & #Hlb & #Hsc & Hobs & Hc & Hb)".
      apply val_of_loc_inj in Hl. subst.
      iExists _. iR. iR. iFrame "# ∗".
  Qed.
End ofty.

Section subtype.
  Context `{!typeGS Σ}.

  Lemma mut_ref_own_val_mono {rt} `{!Inhabited rt} (ty1 ty2 : type rt) v π r κ1 κ2 :
    κ1 ⊑ κ2 -∗
    (∀ r, type_incl r r ty1 ty2) -∗
    (∀ r, type_incl r r ty2 ty1) -∗
    v ◁ᵥ{π} r @ mut_ref ty1 κ2 -∗
    v ◁ᵥ{π} r @ mut_ref ty2 κ1.
  Proof.
    destruct r as [r γ].
    iIntros "#Hincl #Ht12 #Ht21 (%l & %ly & -> & ? & Hly & Hlb & Hsc & Hobs & ? & Hb)".
    iDestruct ("Ht12" $! inhabitant) as "(%Hst & #Hsceq & _)".
    (*iDestruct "Ht21" as "(_ & _ & #Hv21 & #Hs21)".*)
    iExists l, ly. iFrame. iSplitR; first done.
    rewrite -Hst. iFrame. iSplitL "Hsc". { by iApply "Hsceq". }
    iMod "Hb". iModIntro.
    iApply (pinned_bor_shorten with "Hincl").
    iApply (pinned_bor_iff' with "[] Hb").
    iNext. iModIntro. iSplit.
    + iIntros "(%r' & Hauth & Hv)". iExists r'. iFrame.
      iMod "Hv" as "(%v & Hl & Hv)". iModIntro. iExists v. iFrame.
      iDestruct ("Ht12" $! r') as "(_ & _ & Hv12 & _)". by iApply "Hv12".
    + iIntros "(%r' & Hauth & Hv)". iExists r'. iFrame.
      iMod "Hv" as "(%v & Hl & Hv)". iModIntro. iExists v. iFrame.
      iDestruct ("Ht21" $! r') as "(_ & _ & Hv21 & _)". by iApply "Hv21".
  Qed.

  Lemma mut_ref_shr_mono_in {rt} (ty1 ty2 : type rt) l π r1 r2 γ κ κ1 κ2 :
    κ1 ⊑ κ2 -∗
    type_incl r1 r2 ty1 ty2 -∗
    l ◁ₗ{π, κ} (#r1, γ) @ mut_ref ty1 κ2 -∗
    l ◁ₗ{π, κ} (#r2, γ) @ mut_ref ty2 κ1.
  Proof.
    iIntros "#Hincl #Ht12 (%li & %ly & %r' & ? & <- & Hs & ? & ? & ? & ? & Hsc & Hb)".
    iDestruct "Ht12" as "(%Hst & #Hsceq & #Hv12 & #Hs12)".
    iExists li, ly, r2. iFrame. iR. rewrite Hst. iFrame.
    iSplitL "Hsc". { by iApply "Hsceq". }
    iNext. iDestruct "Hb" as "#Hb". iModIntro. iMod "Hb". iModIntro.
    iApply ty_shr_mono.
    { iApply lft_incl_glb.
      + iApply lft_incl_trans; first iApply lft_intersect_incl_l. iApply "Hincl".
      + iApply lft_intersect_incl_r. }
    by iApply "Hs12".
  Qed.
  Lemma mut_ref_shr_mono {rt} `{!Inhabited rt} (ty1 ty2 : type rt) l π r κ κ1 κ2 :
    κ1 ⊑ κ2 -∗
    (∀ r, type_incl r r ty1 ty2) -∗
    l ◁ₗ{π, κ} r @ mut_ref ty1 κ2 -∗
    l ◁ₗ{π, κ} r @ mut_ref ty2 κ1.
  Proof.
    destruct r as [r γ].
    iIntros "#Hincl #Ht12 (%li & %ly & %r' & ? & ? & Hs & ? & ? & ? & ? & Hsc & Hb)".
    iDestruct ("Ht12" $! inhabitant) as "(%Hst & #Hsceq & _)".
    iExists li, ly, r'. iFrame. rewrite Hst. iFrame.
    iSplitL "Hsc". { by iApply "Hsceq". }
    iNext. iDestruct "Hb" as "#Hb". iModIntro. iMod "Hb". iModIntro.
    iApply ty_shr_mono.
    { iApply lft_incl_glb.
      + iApply lft_incl_trans; first iApply lft_intersect_incl_l. iApply "Hincl".
      + iApply lft_intersect_incl_r. }
    iDestruct ("Ht12" $! r') as "(_ & _ & _ & #Hs12)". by iApply "Hs12".
  Qed.

  Lemma mut_ref_type_incl {rt} `{!Inhabited rt} (ty1 ty2 : type rt) r κ2 κ1 :
    κ1 ⊑ κ2 -∗
    (∀ r, type_incl r r ty1 ty2) -∗
    (∀ r, type_incl r r ty2 ty1) -∗
    type_incl r r (mut_ref ty1 κ2) (mut_ref ty2 κ1).
  Proof.
    iIntros "#Hincl #Ht12 #Ht21". iSplitR; first done. iSplitR; first done.
    iSplit; iIntros "!#".
    - iIntros (??). by unshelve iApply mut_ref_own_val_mono.
    - iIntros (???). by unshelve iApply mut_ref_shr_mono.
  Qed.

  Lemma mut_ref_full_subtype {rt} `{!Inhabited rt} E L (ty1 ty2 : type rt) κ1 κ2 :
    full_eqtype E L ty1 ty2 →
    lctx_lft_incl E L κ2 κ1 →
    full_subtype E L (mut_ref ty1 κ1) (mut_ref ty2 κ2).
  Proof.
    iIntros (Hsub1 Hincl r qL) "HL #HE".
    iPoseProof (full_eqtype_acc_noend with "HE HL") as "#Heq"; first done.
    iPoseProof (Hincl with "HL HE") as "#Hincl".
    unshelve iApply mut_ref_type_incl; [done | done | ..].
    - iIntros (r'). iDestruct ("Heq" $! r') as "($ & _)".
    - iIntros (r'). iDestruct ("Heq" $! r') as "(_ & $)".
  Qed.
End subtype.

Section subltype.
  Context `{!typeGS Σ}.
  (** Mutable references *)


  Local Lemma mut_ltype_incl'_shared_in {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κ' r1 r2 γ κ1 κ2 :
    ltype_incl (Shared (κ1 ⊓ κ')) r1 r2 lt1 lt2 -∗
    κ2 ⊑ κ1 -∗
    ltype_incl' (Shared κ') #(r1, γ) #(r2, γ) (MutLtype lt1 κ1) (MutLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1".
    iModIntro.
    iIntros (π l). rewrite !ltype_own_mut_ref_unfold /mut_ltype_own /=.
    iIntros "(%ly & ? & ? & ? & (%r' & %γ' & %Hrfn & #Hb))".
    iExists ly. iFrame. iExists _, _. iFrame. iSplitR; first done.
    iModIntro. iMod "Hb" as "(%li & Hs & Hb)". iModIntro.
    iDestruct ("Heq") as "(%Hly_eq & #Hi1 & #Hc1)".
    injection Hrfn as -> ->.
    iExists li. iFrame. iApply ltype_own_shr_mono; last by iApply "Hi1".
    iApply lft_intersect_mono; first done.
    iApply lft_incl_refl.
  Qed.
  Lemma mut_ltype_incl_shared_in {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κ' γ r1 r2 κ1 κ2 :
    ltype_incl (Shared (κ1 ⊓ κ')) r1 r2 lt1 lt2 -∗
    κ2 ⊑ κ1 -∗
    ltype_incl (Shared κ') #(r1, γ) #(r2, γ) (MutLtype lt1 κ1) (MutLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1".
    iPoseProof (ltype_incl_syn_type with "Heq") as "%Hst".
    iSplitR; first done. iModIntro.
    simp_ltypes.
    iSplit; (iApply mut_ltype_incl'_shared_in; [ | done  ]).
    - done.
    - iApply ltype_incl_core. done.
  Qed.

  Local Lemma mut_ltype_incl'_shared {rt} (lt1 lt2 : ltype rt) κ' r κ1 κ2 :
    (∀ r, ltype_incl (Shared (κ1 ⊓ κ')) r r lt1 lt2) -∗
    κ2 ⊑ κ1 -∗
    ltype_incl' (Shared κ') r r (MutLtype lt1 κ1) (MutLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1".
    iModIntro.
    iIntros (π l). rewrite !ltype_own_mut_ref_unfold /mut_ltype_own /=.
    iIntros "(%ly & ? & ? & ? & (%r' & %γ & Hrfn & #Hb))".
    iExists ly. iFrame. iExists _, _. iFrame.
    iModIntro. iMod "Hb" as "(%li & Hs & Hb)". iModIntro.
    iDestruct ("Heq" $! r') as "(%Hly_eq & #Hi1 & #Hc1)".
    iExists li. iFrame. iApply ltype_own_shr_mono; last by iApply "Hi1".
    iApply lft_intersect_mono; first done.
    iApply lft_incl_refl.
  Qed.
  Lemma mut_ltype_incl_shared {rt} (lt1 : ltype rt) (lt2 : ltype rt) κ' r κ1 κ2 :
    (∀ r, ltype_incl (Shared (κ1 ⊓ κ')) r r lt1 lt2) -∗
    κ2 ⊑ κ1 -∗
    ltype_incl (Shared κ') r r (MutLtype lt1 κ1) (MutLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1".
    iPoseProof (ltype_incl_syn_type _ inhabitant with "Heq") as "%Hst".
    iSplitR; first done. iModIntro.
    simp_ltypes.
    iSplit; (iApply mut_ltype_incl'_shared; [ | done  ]).
    - done.
    - iIntros (?). iApply ltype_incl_core. done.
  Qed.

  Local Lemma mut_ltype_incl'_owned_in {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κ1 κ2 wl r1 r2 γ :
    ltype_incl (Uniq κ1 γ) r1 r2 lt1 lt2  -∗
    κ2 ⊑ κ1 -∗
    ltype_incl' (Owned wl) #(r1, γ) #(r2, γ) (MutLtype lt1 κ1) (MutLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1". iModIntro.
    iIntros (π l). rewrite !ltype_own_mut_ref_unfold /mut_ltype_own /=.
    iIntros "(%ly & ? & ? & ? &  ? & (%γ' & %r' & %Hrfn & Hl))".
    injection Hrfn as <- <-.
    iModIntro.
    iExists ly. iFrame. iExists γ, r2. iSplitR; first done.
    iNext. iMod "Hl" as "(%l' & Hl & Hb)".
    iExists l'. iFrame. iDestruct "Heq" as "(_ & Heq & _)".
    iApply ltype_own_uniq_mono; last by iApply "Heq". done.
  Qed.
  Lemma mut_ltype_incl_owned_in {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κ1 κ2 wl r1 r2 γ :
    ltype_incl (Uniq κ1 γ) r1 r2 lt1 lt2  -∗
    κ2 ⊑ κ1 -∗
    ltype_incl (Owned wl) #(r1, γ) #(r2, γ) (MutLtype lt1 κ1) (MutLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1".
    iPoseProof (ltype_incl_syn_type with "Heq") as "%Hst".
    iSplitR; first done. iModIntro.
    simp_ltypes.
    iSplit; (iApply mut_ltype_incl'_owned_in; [ | done  ]).
    - done.
    - iApply ltype_incl_core. done.
  Qed.

  Local Lemma mut_ltype_incl'_owned {rt} (lt1 lt2 : ltype rt) κ1 κ2 wl r :
    (∀ γ r, ltype_incl (Uniq κ1 γ) r r lt1 lt2) -∗
    κ2 ⊑ κ1 -∗
    ltype_incl' (Owned wl) r r (MutLtype lt1 κ1) (MutLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1". iModIntro.
    iIntros (π l). rewrite !ltype_own_mut_ref_unfold /mut_ltype_own /=.
    iIntros "(%ly & ? & ? & ? &  ? & (%γ' & %r' & Hrfn & Hl))".
    iModIntro.
    iExists ly. iFrame. iExists γ', r'. iFrame "Hrfn".
    iNext. iMod "Hl" as "(%l' & Hl & Hb)".
    iExists l'. iFrame. iModIntro.
    iApply ltype_own_uniq_mono; first done.
    iDestruct ("Heq" $! _ _) as "(_ & #Heq' & _)". by iApply "Heq'".
  Qed.
  Lemma mut_ltype_incl_owned {rt} (lt1 : ltype rt) (lt2 : ltype rt) κ1 κ2 wl r :
    (∀ γ r, ltype_incl (Uniq κ1 γ) r r lt1 lt2)  -∗
    κ2 ⊑ κ1 -∗
    ltype_incl (Owned wl) r r (MutLtype lt1 κ1) (MutLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1".
    iPoseProof (ltype_incl_syn_type (Uniq _ inhabitant) inhabitant with "Heq") as "%Hst".
    iSplitR; first done. iModIntro.
    simp_ltypes.
    iSplit; (iApply mut_ltype_incl'_owned; [ | done  ]).
    - done.
    - iIntros (??). iApply ltype_incl_core. done.
  Qed.

  (* Refinement subtyping under mutable references is restricted: we need to make sure that, no matter the future updates,
     we can always get back to what the lender expects. Thus we loose all refinement information when descending below mutable references. *)
  Local Lemma mut_ltype_incl'_uniq {rt} (lt1 lt2 : ltype rt) κ1 κ2 κ r γ :
    (∀ γ r, ltype_eq (Uniq (κ1) γ) r r lt1 lt2) -∗
    (* Note: requires mutual inclusion, because we may be below a mutable reference *)
    κ2 ⊑ κ1 -∗
    κ1 ⊑ κ2 -∗
    ltype_incl' (Uniq κ γ) r r (MutLtype lt1 κ1) (MutLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1 #Hincl2". iModIntro.
    iIntros (π l). rewrite !ltype_own_mut_ref_unfold /mut_ltype_own /=.
    iIntros "(%ly & ? & ? & ? & ? & ? & Hb)".
    iExists ly. iFrame.
    iMod "Hb". iModIntro. iApply (pinned_bor_iff with "[] [] Hb").
    + iNext. iModIntro. iSplit.
      * iIntros "(%r' & Hauth & Hb)"; iExists _; iFrame.
        iMod "Hb" as "(%l' & Hl & Hb)". iModIntro. iExists _. iFrame.
        iDestruct ("Heq" $! _ r'.1) as "((%Hly_eq & #Hi1 & #Hc1) & (_ & #Hi2 & #Hc2))".
        iApply ltype_own_uniq_mono; last by iApply "Hi1". done.
      * iIntros "(%r' & Hauth & Hb)"; iExists _; iFrame.
        iMod "Hb" as "(%l' & Hl & Hb)". iModIntro. iExists _. iFrame.
        iDestruct ("Heq" $! _ r'.1) as "((%Hly_eq & #Hi1 & #Hc1) & (_ & #Hi2 & #Hc2))".
        iApply "Hi2". iApply ltype_own_uniq_mono; done.
    + iNext. iModIntro. iSplit.
      * iIntros "(%r' & Hauth & Hb)"; iExists _; iFrame.
        iMod "Hb" as "(%l' & Hl & Hb)". iModIntro. iExists _. iFrame.
        iDestruct ("Heq" $! _ r'.1) as "((%Hly_eq & #Hi1 & #Hc1) & (_ & #Hi2 & #Hc2))".
        rewrite !ltype_own_core_equiv.
        iApply ltype_own_uniq_mono; last by iApply "Hc1". done.
      * iIntros "(%r' & Hauth & Hb)"; iExists _; iFrame.
        iMod "Hb" as "(%l' & Hl & Hb)". iModIntro. iExists _. iFrame.
        iDestruct ("Heq" $! _ r'.1) as "((%Hly_eq & #Hi1 & #Hc1) & (_ & #Hi2 & #Hc2))".
        rewrite !ltype_own_core_equiv.
        iApply "Hc2". iApply ltype_own_uniq_mono; done.
  Qed.
  Lemma mut_ltype_incl_uniq {rt} (lt1 lt2 : ltype rt) κ1 κ2 κ r γ :
    (∀ γ r, ltype_eq (Uniq (κ1) γ) r r lt1 lt2) -∗
    κ2 ⊑ κ1 -∗
    κ1 ⊑ κ2 -∗
    ltype_incl (Uniq κ γ) r r (MutLtype lt1 κ1) (MutLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1 #Hincl2".
    iPoseProof (ltype_eq_syn_type (Uniq _ inhabitant) inhabitant with "Heq") as "%Hst".
    iSplitR; first done. iModIntro.
    simp_ltypes.
    iSplit; (iApply mut_ltype_incl'_uniq; [ | done  | done]).
    - done.
    - iIntros (??). iApply ltype_eq_core. done.
  Qed.

  Lemma mut_ltype_incl {rt} (lt1 lt2 : ltype rt) b r κ1 κ2 :
    (∀ b r, ltype_eq b r r lt1 lt2) -∗
    κ2 ⊑ κ1 -∗
    κ1 ⊑ κ2 -∗
    ltype_incl b r r (MutLtype lt1 κ1) (MutLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1 #Hincl2".
    destruct b.
    - iApply mut_ltype_incl_owned; last done. iIntros (??). iDestruct ("Heq" $! _ _) as "[$ _]".
    - iApply mut_ltype_incl_shared; last done. iIntros (?). iDestruct ("Heq" $! _ _) as "[$ _]".
    - iApply mut_ltype_incl_uniq; [ | done..]. iIntros (??). done.
  Qed.

  Lemma mut_ltype_eq {rt} (lt1 lt2 : ltype rt) b r κ1 κ2 :
    (∀ b r, ltype_eq b r r lt1 lt2) -∗
    κ2 ⊑ κ1 -∗
    κ1 ⊑ κ2 -∗
    ltype_eq b r r (MutLtype lt1 κ1) (MutLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1 #Hincl2".
    iSplit.
    - iApply mut_ltype_incl; done.
    - iApply mut_ltype_incl; [ | done..]. iIntros (??). iApply ltype_eq_sym. done.
  Qed.

  Lemma mut_full_subltype E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 :
    full_eqltype E L lt1 lt2 →
    lctx_lft_incl E L κ1 κ2 →
    lctx_lft_incl E L κ2 κ1 →
    full_subltype E L (MutLtype lt1 κ1) (MutLtype lt2 κ2).
  Proof.
    intros Heq Hincl1 Hincl2.
    iIntros (qL) "HL #CTX #HE". iIntros (b r).
    iPoseProof (Heq with "HL CTX HE") as "#Heq".
    iPoseProof (lctx_lft_incl_incl_noend with "HL HE") as "#Hincl1"; first apply Hincl1.
    iPoseProof (lctx_lft_incl_incl_noend with "HL HE") as "#Hincl2"; first apply Hincl2.
    iApply mut_ltype_incl; done.
  Qed.
  Lemma mut_full_eqltype E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 :
    full_eqltype E L lt1 lt2 →
    lctx_lft_incl E L κ1 κ2 →
    lctx_lft_incl E L κ2 κ1 →
    full_eqltype E L (MutLtype lt1 κ1) (MutLtype lt2 κ2).
  Proof.
    intros Heq Hincl1 Hincl2.
    apply full_subltype_eqltype; eapply mut_full_subltype; naive_solver.
  Qed.
End subltype.

Section ltype_agree.
  Context `{typeGS Σ}
    {rt}
    (ty: type rt).
  Context `{Inhabited rt}.

  Lemma mut_ref_unfold_1_owned κ wl r :
    ⊢ ltype_incl' (Owned wl) r r (MutLtype (◁ ty) κ) (◁ (mut_ref ty κ)).
  Proof.
    iModIntro. iIntros (π l). rewrite ltype_own_mut_ref_unfold /mut_ltype_own ltype_own_ofty_unfold /lty_of_ty_own.
    iIntros "(%ly & ? & ? & Hlb & ? & %γ & %r' & Hrfn & Hb)".
    iModIntro.
    iExists ly. iFrame "∗". iExists _. iFrame. iNext.
    iMod "Hb" as "(%l' & Hl & Hb)".
    iExists l'. iFrame.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hb" as "(%ly' & ? & ? & Hsc & Hlb' & ? & Hrfn'  & Hb)".
    iExists l'. iFrame. iExists ly'. iSplitR; first done. iFrame "∗". done.
  Qed.
  Lemma mut_ref_unfold_1_uniq κ κ' γ r :
    ⊢ ltype_incl' (Uniq κ' γ) r r (MutLtype (◁ ty) κ) (◁ (mut_ref ty κ)).
  Proof.
    iModIntro.
    iIntros (π l). rewrite ltype_own_mut_ref_unfold /mut_ltype_own ltype_own_ofty_unfold /lty_of_ty_own.
    iIntros "(%ly & ? & %Hly & ? & ? & ? & Hb)". iExists ly. iFrame "∗". iSplitR; first done.
    iMod "Hb". iModIntro.
    setoid_rewrite ltype_own_core_equiv. simp_ltypes.
    iApply (pinned_bor_iff' with "[] Hb").
    iNext. iModIntro. iSplit.
    * iIntros "(%r' & Hauth & Hb)". iExists _. iFrame. iMod "Hb" as "(%l' & Hl & Hb)".
      iExists l'. iFrame. rewrite ltype_own_ofty_unfold /lty_of_ty_own. destruct r' as [r' γ'].
      iDestruct "Hb" as "(%ly' & Hst' & Hly' & Hsc & Hlb & ? & Hrfn & >Hb)".
      iModIntro. iExists l', ly'. iFrame "∗". iSplitR; first done. by iFrame.
    * iIntros "(%r' & Hauth & Hb)". iExists _. iFrame. iMod "Hb" as "(%v & Hl & Hb)". destruct r' as [r' γ'].
      iDestruct "Hb" as "(%l' & %ly' & -> & ? & ? & Hlb & Hsc & Hrfn & ? & >Hb)".
      iExists _. iFrame. rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iModIntro. iExists ly'. iFrame. done.
  Qed.
  Lemma mut_ref_unfold_1_shared κ κ' r :
    ⊢ ltype_incl' (Shared κ') r r (MutLtype (◁ ty) κ) (◁ (mut_ref ty κ)).
  Proof.
    iModIntro.
    iIntros (π l). rewrite ltype_own_mut_ref_unfold /mut_ltype_own ltype_own_ofty_unfold /lty_of_ty_own.
    iIntros "(%ly & %Hst & % & #Hlb & %ri & %γ & Hrfn & #Hb)".
    injection Hst as <-. iExists _. iFrame "# ∗". iSplitR; first done. iSplitR; first done.
    iExists _. iFrame "∗". iModIntro. iMod "Hb" as "(%li & Hs & Hb)".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hb" as "(%ly' & >? & >? & >Hsc & >Hlb' & %r' & >Hrfn & #Hb)".
    (* TODO proof uses timelessness of Hrfn, can we do it without? *)
    iModIntro. iExists _, _, _. iFrame "∗ #". done.
  Qed.

  Local Lemma mut_ref_unfold_1' κ k r :
    ⊢ ltype_incl' k r r (MutLtype (◁ ty) κ) (◁ (mut_ref ty κ)).
  Proof.
    destruct k.
    - iApply mut_ref_unfold_1_owned.
    - iApply mut_ref_unfold_1_shared.
    - iApply mut_ref_unfold_1_uniq.
  Qed.
  Lemma mut_ref_unfold_1 κ k r :
    ⊢ ltype_incl k r r (MutLtype (◁ ty) κ) (◁ (mut_ref ty κ)).
  Proof.
    iSplitR; first done. iModIntro. iSplit.
    - iApply mut_ref_unfold_1'.
    - simp_ltypes. iApply mut_ref_unfold_1'.
  Qed.

  Lemma mut_ref_unfold_2_owned κ wl r :
    ⊢ ltype_incl' (Owned wl) r r (◁ (mut_ref ty κ)) (MutLtype (◁ ty) κ).
  Proof.
    iModIntro. iIntros (π l). rewrite ltype_own_mut_ref_unfold /mut_ltype_own ltype_own_ofty_unfold /lty_of_ty_own.
    iIntros "(%ly & ? & ? & _ & #Hlb & ? & %r' & Hrfn & Hb)". destruct r' as [r' γ'].
    (*iApply except_0_if_intro.*)
    iModIntro. iExists ly. iFrame "∗ #". iExists γ', r'. iFrame. iNext.
    iMod "Hb" as "(%v & Hl & %l' & %ly' & -> & ? & ? & #Hlb' & Hsc & ? &  Hrfn' & >Hb)".
    iExists _. iFrame. rewrite ltype_own_ofty_unfold /lty_of_ty_own. iExists ly'. iFrame "∗ #". done.
  Qed.
  Lemma mut_ref_unfold_2_uniq κ κ' γ r :
    ⊢ ltype_incl' (Uniq κ' γ) r r (◁ (mut_ref ty κ)) (MutLtype (◁ ty) κ).
  Proof.
    iModIntro.
    iIntros (π l). rewrite ltype_own_mut_ref_unfold /mut_ltype_own ltype_own_ofty_unfold /lty_of_ty_own.
    iIntros "(%ly & ? & ? &  _ & Hlb & ? &  Hrfn & Hb)". iExists ly. iFrame "∗". iMod "Hb".
    iModIntro.
    setoid_rewrite ltype_own_core_equiv. simp_ltypes.
    iApply (pinned_bor_iff' with "[] Hb").
    iNext. iModIntro. iSplit.
    * iIntros "(%r' & Hauth & Hb)". iExists _. iFrame. iMod "Hb" as "(%v & Hl & Hb)". destruct r' as [r' γ'].
      iDestruct "Hb" as "(%l' & %ly' & -> & ? & ? & Hlb & Hsc & Hrfn & ? & >Hb)".
      iExists _. iFrame. rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iModIntro. iExists ly'. iFrame. done.
    * iIntros "(%r' & Hauth & Hb)". iExists _. iFrame. iMod "Hb" as "(%l' & Hl & Hb)".
      iExists l'. iFrame. rewrite ltype_own_ofty_unfold /lty_of_ty_own. destruct r' as [r' γ'].
      iDestruct "Hb" as "(%ly' & Hst' & Hly' & Hsc & Hlb & ? &  Hrfn & >Hb)".
      iModIntro. iExists l', ly'. iFrame "∗". iSplitR; first done. by iFrame.
  Qed.
  Lemma mut_ref_unfold_2_shared κ κ' r :
    ⊢ ltype_incl' (Shared κ') r r (◁ (mut_ref ty κ)) (MutLtype (◁ ty) κ).
  Proof.
    iModIntro. iIntros (π l). rewrite ltype_own_mut_ref_unfold /mut_ltype_own ltype_own_ofty_unfold /lty_of_ty_own.
    iIntros "(%ly & ? & ? & Hsc & Hlb & %r' & Hrfn & #Hb)". destruct r' as [r' γ'].
    iExists ly. iFrame "∗ #". iExists _, _. iFrame.
    iModIntro. iMod "Hb".
    iDestruct "Hb" as "(%li & %ly' & %ri & ? & Hrfn' & Hs & ? & ? & Hlb & Hlb' & Hsc & #Hb)".
    iModIntro. iExists li. iFrame.
    iNext. rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iExists ly'. iFrame.
    iExists _. iFrame. done.
  Qed.

  Local Lemma mut_ref_unfold_2' κ k r :
    ⊢ ltype_incl' k r r (◁ (mut_ref ty κ)) (MutLtype (◁ ty) κ).
  Proof.
    destruct k.
    - iApply mut_ref_unfold_2_owned.
    - iApply mut_ref_unfold_2_shared.
    - iApply mut_ref_unfold_2_uniq.
  Qed.
  Local Lemma mut_ref_unfold_2 κ k r :
    ⊢ ltype_incl k r r (◁ (mut_ref ty κ)) (MutLtype (◁ ty) κ).
  Proof.
    iSplitR; first done. iModIntro. iSplit.
    - iApply mut_ref_unfold_2'.
    - simp_ltypes. iApply mut_ref_unfold_2'.
  Qed.

  Lemma mut_ref_unfold κ k r :
    ⊢ ltype_eq k r r (MutLtype (◁ ty) κ) (◁ (mut_ref ty κ)).
  Proof.
    iSplit; iModIntro.
    - iApply mut_ref_unfold_1.
    - iApply mut_ref_unfold_2.
  Qed.

  Lemma mut_ref_unfold_full_eqltype E L κ (lt : ltype rt) :
    full_eqltype E L lt (◁ ty)%I →
    full_eqltype E L (MutLtype lt κ) (◁ (mut_ref ty κ))%I.
  Proof.
    iIntros (Heql ?) "HL #CTX #HE". iIntros (b r).
    iPoseProof (Heql with "HL CTX HE") as "#Heql".
    iApply ltype_eq_trans; last iApply mut_ref_unfold.
    iApply mut_ltype_eq; [ | iApply lft_incl_refl.. ].
    by iApply "Heql".
  Qed.
End ltype_agree.

Section rules.
  Context `{!typeGS Σ}.

  Global Instance get_lft_names_mut_ref {rt} (ty : type rt) κ lfts lfts' name tree :
    GetLftNames ty lfts tree lfts' →
    GetLftNames (mut_ref ty κ) lfts (LftNameTreeRef name tree) (named_lft_update name κ lfts') := λ _, GLN.

  (* extraction *)
  Lemma stratify_ltype_extract_ofty_mut π E L {rt} (ty : type rt) r κ γ l (wl : bool) (T : stratify_ltype_post_hook_cont_t) :
    T L (place_rfn_interp_mut r γ) _ (◁ uninit PtrSynType)%I (#())
    ⊢ stratify_ltype_post_hook π E L (StratifyExtractOp κ) l (◁ (mut_ref ty κ)) (#(r, γ)) (Owned wl) T.
  Proof.
    iIntros "HT".
    iIntros (???) "#CTX #HE HL Hl".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iExists _, _, _, _, _. iFrame.
    iDestruct "Hl" as "(%ly & %Hst & %Hly & Hsc & Hlb & Hcreds & %r' & <- & Hb)".
    iMod (maybe_use_credit with "Hcreds Hb") as "(Hcreds & Hat & Hb)"; first done.
    iDestruct "Hb" as "(%v & Hl & Hb)".
    rewrite /ty_own_val/=.
    iDestruct "Hb" as "(% & % & -> & ? & ? & ? & ? & Hb & Hcred' & ?)".
    iFrame.
    iSplitR. { simp_ltypes. done. }
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iExists _. simpl. iFrame. iR. iR.
    iSplitL "Hcred'". { destruct wl; last done. by iFrame. }
    iExists _. iR. iModIntro. iModIntro. iModIntro.
    iExists _. iFrame. rewrite uninit_own_spec. iExists _. iR.
    iPureIntro. eapply syn_type_has_layout_ptr_inv in Hst. subst.
    done.
  Qed.
  Global Instance stratify_ltype_extract_ofty_mut_inst π E L {rt} (ty : type rt) r κ γ l (wl : bool) :
    StratifyLtypePostHook π E L (StratifyExtractOp κ) l (◁ (mut_ref ty κ))%I (#(r, γ)) (Owned wl) | 20 :=
    λ T, i2p (stratify_ltype_extract_ofty_mut π E L ty r κ γ l wl T).

  Import EqNotations.
  Lemma mut_ltype_place_cond_ty b κ {rt rt2} (lt1 : ltype rt) (lt2 : ltype rt2) :
    typed_place_cond_ty (b) lt1 lt2
    ⊢ typed_place_cond_ty b (MutLtype lt1 κ) (MutLtype lt2 κ).
  Proof.
    destruct b; simpl.
    - iIntros "_". done.
    - iIntros "(-> & %)". iR. simp_ltypes. done.
    - iIntros "(%Hrefl & Heq & Hub)".
      subst rt2. cbn.
      iExists eq_refl. cbn. iSplitR "Hub".
      + simp_ltypes. iIntros (??). iApply (mut_ltype_eq with "Heq"); iApply lft_incl_refl.
      + by iApply mut_ltype_imp_unblockable.
  Qed.

  Lemma mut_ltype_acc_owned {rt} F π (lt : ltype rt) (r : place_rfn rt) l κ' γ' wl :
    lftE ⊆ F →
    rrust_ctx -∗
    l ◁ₗ[π, Owned wl] #(r, γ') @ MutLtype lt κ' -∗
    ⌜l `has_layout_loc` void*⌝ ∗ loc_in_bounds l 0 (ly_size void*) ∗ |={F}=>
      ∃ l' : loc, l ↦ l' ∗ l' ◁ₗ[π, Uniq κ' γ'] r @ lt ∗
      logical_step F
      (∀ rt' (lt2 : ltype rt') r2,
        l ↦ l' -∗
        l' ◁ₗ[π, Uniq κ' γ'] r2 @ lt2 ={F}=∗
        l ◁ₗ[π, Owned wl] #(r2, γ') @ MutLtype lt2 κ' ∗
        (∀ bmin, typed_place_cond bmin lt lt2 r r2 -∗
         ⌜place_access_rt_rel bmin rt rt'⌝ -∗
         typed_place_cond bmin (MutLtype lt κ') (MutLtype lt2 κ') (#(r, γ')) (#(r2, γ')))).
  Proof.
    iIntros (?) "#[LFT TIME] HP".
    rewrite ltype_own_mut_ref_unfold /mut_ltype_own.
    iDestruct "HP" as "(%ly & %Halg & %Hly & #Hlb & Hcred & %γ & %r' & %Heq & Hb)".
    injection Halg as <-. injection Heq as <- <-.
    iFrame "Hlb %".
    iMod (maybe_use_credit with "Hcred Hb") as "(Hcred & Hat & Hb)"; first done.
    iDestruct "Hb" as "(%l' & Hl & Hb)".
    iModIntro. iExists l'. iFrame.
    iApply (logical_step_intro_maybe with "Hat").
    iIntros "Hcred' !>". iIntros (rt2 lt2 r2) "Hl Hb".
    iModIntro. iSplitL.
    - rewrite ltype_own_mut_ref_unfold /mut_ltype_own. iExists void*.
      iSplitR; first done. iFrame "Hlb % ∗".
      iExists _, _. iSplitR; first done. iNext. eauto with iFrame.
    - iIntros (bmin) "Hcond %Hrt". iDestruct "Hcond" as "[Hty Hrfn]".
      subst. iSplit.
      + by iApply (mut_ltype_place_cond_ty).
      + destruct bmin; cbn in Hrt; [ done | subst rt2..].
        all: by iApply (typed_place_cond_rfn_lift _ _ _ (λ r, PlaceIn (r, γ'))).
  Qed.

  Lemma mut_ltype_acc_uniq {rt} F π (lt : ltype rt) (r : place_rfn rt) l κ' γ' κ γ q R :
    lftE ⊆ F →
    rrust_ctx -∗
    q.[κ] -∗
    (q.[κ] ={lftE}=∗ R) -∗
    l ◁ₗ[π, Uniq κ γ] #(r, γ') @ MutLtype lt κ' -∗
    ⌜l `has_layout_loc` void*⌝ ∗ loc_in_bounds l 0 (ly_size void*) ∗ |={F}=>
      ∃ l' : loc, l ↦ l' ∗ (l' ◁ₗ[π, Uniq κ' γ'] r @ lt) ∗
      logical_step F
      ( (* weak update *)
       (∀ bmin (lt2 : ltype rt) r2,
        l ↦ l' -∗
        l' ◁ₗ[π, Uniq κ' γ'] r2 @ lt2  -∗
        bmin ⊑ₖ Uniq κ γ -∗
        typed_place_cond bmin lt lt2 r r2 ={F}=∗
        l ◁ₗ[π, Uniq κ γ] PlaceIn (r2, γ') @ MutLtype lt2 κ' ∗
        R ∗
        typed_place_cond bmin (MutLtype lt κ') (MutLtype lt2 κ') (PlaceIn (r, γ')) (PlaceIn (r2, γ'))) ∧
      (* strong update, go to Opened *)
      (∀ rt2 (lt2 : ltype rt2) r2,
        l ↦ l' -∗
        ⌜ltype_st lt2 = ltype_st lt⌝ -∗
        l' ◁ₗ[π, Uniq κ' γ'] r2 @ lt2 ={F}=∗
        l ◁ₗ[π, Uniq κ γ] PlaceIn (r2, γ') @ OpenedLtype (MutLtype lt2 κ') (MutLtype lt κ') (MutLtype lt κ')
          (λ r1 r1', ⌜r1 = r1'⌝) (λ _ _, R))).
  Proof.
    iIntros (?) "#[LFT TIME] Hκ HR HP".
    rewrite ltype_own_mut_ref_unfold /mut_ltype_own.
    iDestruct "HP" as "(%ly & %Halg & %Hly & #Hlb & (Hcred & Hat) & Hrfn & Hb)".
    injection Halg as <-. iFrame "Hlb". iSplitR; first done.

    iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
    iMod "Hb".
    (* NOTE: we are currently throwing away the existing "coring"-viewshift that we get *)
    iMod (pinned_bor_acc_strong lftE with "LFT Hb Hκ") as "(%κ'' & #Hincl & Hb & _ & Hb_cl)"; first done.
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
      iIntros (bmin lt2 r2) "Hl Hb #Hincl_k #Hcond".
      (* extract the necessary info from the place_cond *)
      iPoseProof (typed_place_cond_incl _ (Uniq κ γ) with "Hincl_k Hcond") as "Hcond'".
      iDestruct "Hcond'" as "(Hcond' & _)".
      iDestruct "Hcond'" as "(%Heq & Heq & (#Hub & _))".
      rewrite (UIP_refl _ _ Heq). cbn.
      iPoseProof (typed_place_cond_syn_type_eq with "Hcond") as "%Hst_eq".
      (* close the borrow *)
      iMod (gvar_update (r2, γ') with "Hauth Hrfn") as "(Hauth & Hrfn)".
      set (V := (∃ r', gvar_auth γ r' ∗ (|={lftE}=> ∃ (l' : loc), l ↦ l' ∗ ltype_own lt2 (Uniq κ' r'.2) π r'.1 l'))%I).
      iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
      iDestruct "Hcred" as "(Hcred1 & Hcred)".
      iMod ("Hb_cl" $! V with "[] Hcred1 [Hauth Hl Hb]") as "(Hb & Htok)".
      { iNext. iIntros "(%r' & Hauth & Hb) Hdead".
        iModIntro. iNext. iExists r'. iFrame "Hauth".
        clear. iMod "Hb" as "(%l' & ? & Ha)".
        iMod (lft_incl_dead with "Hincl Hdead") as "Hdead"; first done.
        (* unblock *)
        iMod ("Hub" with "[$Hdead //] Ha") as "Ha".
        (* use that the cores are equal *)
        iDestruct ("Heq" $! (Uniq _ _) _) as "(_ & (%Hst & #Hi & _))".
        rewrite ltype_own_core_equiv. iPoseProof ("Hi" with "Ha") as "Ha".
        rewrite -ltype_own_core_equiv. eauto with iFrame. }
      { iModIntro. rewrite /V. eauto 8 with iFrame. }
      iMod ("HR" with "Htok") as "$".
      iMod "Hcl_F" as "_".
      iModIntro.
      (* TODO maybe donate the leftover credits *)
      iSplitL.
      { rewrite ltype_own_mut_ref_unfold /mut_ltype_own.
        iExists void*. iFrame. do 3 iR.
        iPoseProof (pinned_bor_shorten with "Hincl Hb") as "Hb".
        iModIntro. subst V.
        (* need to adapt the pinned part, too *)
        iApply (pinned_bor_iff with "[] [] Hb").
        { iNext. iModIntro. eauto. }
        clear -Hst_eq.
        iNext. iModIntro. iSplit.
        - iIntros "(%r' & Hauth & Hb)". iExists r'. iFrame.
          iMod "Hb" as "(%l' & Hl & Hb)".
          iDestruct ("Heq" $! (Uniq _ _) _) as "((_ & #Heq1 & _) & (_ & #Heq2 & _))".
          rewrite ltype_own_core_equiv. iPoseProof ("Heq1" with "Hb") as "Hb". rewrite -ltype_own_core_equiv.
          eauto with iFrame.
        - iIntros "(%r' & Hauth & Hb)". iExists r'. iFrame.
          iMod "Hb" as "(%l' & Hl & Hb)".
          iDestruct ("Heq" $! (Uniq _ _) _) as "((_ & #Heq1 & _) & (_ & #Heq2 & _))".
          rewrite ltype_own_core_equiv. iPoseProof ("Heq2" with "Hb") as "Hb". rewrite -ltype_own_core_equiv.
          eauto with iFrame.
      }
      iDestruct "Hcond" as "(Hcond_ty & Hcond_rfn)".
      iSplit.
      + iApply mut_ltype_place_cond_ty; done.
      + iApply (typed_place_cond_rfn_lift _ _ _ (λ a, #(a, γ'))). done.
    - (* shift to OpenedLtype *)
      iIntros (rt2 lt2 r2) "Hl %Hst' Hb". iModIntro.
      iDestruct "Hcred" as "(Hcred1 & Hcred)".
      iApply (opened_ltype_create_uniq_simple with "Hrfn Hauth Hcred1 Hat Hincl HR Hb_cl [] [Hcred']"); first done.
      { iModIntro. iIntros (?) "Hauth Hc". simp_ltypes.
        rewrite ltype_own_mut_ref_unfold /mut_ltype_own.
        iExists _. iFrame. iDestruct "Hc" as ">(% & _ & _ & _ & _ & %r' & % & -> & >(%l0 & Hl & Hb))".
        iModIntro. setoid_rewrite ltype_own_core_equiv.
        iExists _. eauto with iFrame. }
      { iIntros (?) "Hobs Hat Hcred Hp". simp_ltypes.
        rewrite ltype_own_mut_ref_unfold /mut_ltype_own.
        setoid_rewrite ltype_own_core_equiv. rewrite ltype_core_idemp.
        iModIntro. eauto 8 with iFrame. }
      { rewrite ltype_own_mut_ref_unfold /mut_ltype_own.
        iExists void*. do 4 iR.
        iExists _, r2. iR. iNext. iModIntro. eauto with iFrame. }
  Qed.

  Lemma mut_ltype_acc_shared {rt} F π (lt : ltype rt) r l q κ κ' γ :
    lftE ⊆ F →
    rrust_ctx -∗
    q.[κ] -∗
    l ◁ₗ[π, Shared κ] #(r, γ) @ MutLtype lt κ' -∗
    ⌜l `has_layout_loc` void*⌝ ∗ loc_in_bounds l 0 (ly_size void*) ∗ |={F}=>
      ∃ (l' : loc) q', l ↦{q'} l' ∗ (|={F}▷=> l' ◁ₗ[π, Shared (κ' ⊓ κ)] r @ lt) ∗
    (∀ (lt' : ltype rt) r',
      l ↦{q'} l' -∗
      l' ◁ₗ[π, Shared (κ' ⊓ κ)] r' @ lt' -∗ |={F}=>
      l ◁ₗ[π, Shared κ] #(r', γ) @ MutLtype lt' κ' ∗
      q.[κ] ∗
      (∀ bmin,
      bmin ⊑ₖ Shared κ -∗
      typed_place_cond bmin lt lt' r r' ={F}=∗
      typed_place_cond bmin (MutLtype lt κ') (MutLtype lt' κ') #(r, γ) #(r', γ))).
  Proof.
    iIntros (?) "#(LFT & TIME & LLCTX) Hκ Hb". rewrite {1}ltype_own_mut_ref_unfold /mut_ltype_own.
    iDestruct "Hb" as "(%ly & %Hst & %Hly & #Hlb & %r' & %γ' & %Ha & #Hb)".
    injection Ha as <- <-.
    apply syn_type_has_layout_ptr_inv in Hst. subst ly.
    iR. iR.
    iMod (fupd_mask_mono with "Hb") as "(%li & #Hf & #Hl)"; first done.
    iMod (frac_bor_acc with "LFT Hf Hκ") as "(%q' & >Hpts & Hclf)"; first done.
    iModIntro. iExists _, _. iFrame.
    iSplitR. { iApply step_fupd_intro; first done. auto. }
    iIntros (lt' r'') "Hpts #Hl'".
    iMod ("Hclf" with "Hpts") as "Htok".
    iFrame. iSplitL.
    { iModIntro. rewrite ltype_own_mut_ref_unfold /mut_ltype_own. iExists void*. iFrame "% #".
      iR. iExists _, _. iR. iModIntro. iModIntro. iExists _. iFrame "#". }
    iModIntro. iIntros (bmin) "Hincl Hcond".
    iDestruct "Hcond" as "(Hcond_ty & Hcond_rfn)".
    iModIntro. iSplit.
    + iApply mut_ltype_place_cond_ty; done.
    + destruct bmin; simpl; done.
  Qed.


  (** Place *)
  (* This needs to have a lower priority than the id instances, because we do not want to unfold when P = []. *)
  Lemma typed_place_ofty_mut {rt} `{Inhabited rt} π E L l (ty : type rt) κ (r : place_rfn (place_rfn rt * gname)) bmin0 b P T :
    typed_place π E L l (MutLtype (◁ ty) κ) r bmin0 b P T
    ⊢ typed_place π E L l (◁ (mut_ref ty κ)) r bmin0 b P T.
  Proof.
    iIntros "Hp". iApply typed_place_eqltype; last done.
    iIntros (?) "HL CTX HE". iIntros (??).
    iApply ltype_eq_sym. iApply mut_ref_unfold.
  Qed.
  Global Instance typed_place_ofty_mut_inst {rt} `{Inhabited rt} π E L l (ty : type rt) κ (r : place_rfn (place_rfn rt * gname)) bmin0 b P :
    TypedPlace E L π l (◁ (mut_ref ty κ))%I r bmin0 b P | 30 := λ T, i2p (typed_place_ofty_mut π E L l ty κ r bmin0 b P T).

  Lemma typed_place_mut_owned {rto} π κ (lt2 : ltype rto) P E L γ l r wl bmin0
    (T : place_cont_t ((place_rfn rto) * gname)) :
    (∀ l', typed_place π E L l' lt2 r (Uniq κ γ ⊓ₖ bmin0) (Uniq κ γ) P
        (λ L' κs l2 b2 bmin rti tyli ri strong weak,
          T L' (κs) l2 b2 bmin rti tyli ri
          (option_map (λ strong, mk_strong
            (λ rti2, (place_rfn (strong.(strong_rt) rti2)) * gname)%type
            (λ rti2 lti2 ri, MutLtype (strong.(strong_lt) _ lti2 ri) κ)
            (λ rti2 (r : place_rfn rti2), PlaceIn (strong.(strong_rfn) _ r, γ))
            strong.(strong_R)) strong)
          (fmap (λ weak,  mk_weak
            (λ ltyi2 ri2, MutLtype (weak.(weak_lt) ltyi2 ri2) κ)
            (λ (r : place_rfn rti), PlaceIn (weak.(weak_rfn) r, γ))
            weak.(weak_R)) weak)))
    ⊢ typed_place π E L l (MutLtype lt2 κ) (PlaceIn (r, γ)) bmin0 (Owned wl) (DerefPCtx Na1Ord PtrOp true :: P) T.
  Proof.
    iIntros "HR" (Φ F ??).
    rewrite /li_tactic /lctx_lft_alive_count_goal.
    iIntros "#(LFT & TIME & LLCTX) #HE HL Hincl0 HP HΦ/=".
    iPoseProof (mut_ltype_acc_owned F with "[$LFT $TIME $LLCTX] HP") as "(%Hly & Hlb & Hb)"; [done.. | ].
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
      iMod ("Hc" with "Hl Hb") as "(Hb & _)".
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
  Global Instance typed_place_mut_owned_inst {rto} E L π κ γ (lt2 : ltype rto) bmin0 r l wl P :
    TypedPlace E L π l (MutLtype lt2 κ) (PlaceIn (r, γ)) bmin0 (Owned wl) (DerefPCtx Na1Ord PtrOp true :: P) | 30 := λ T, i2p (typed_place_mut_owned π κ lt2 P E L γ l r wl bmin0 T).

  Lemma typed_place_mut_uniq {rto} π E L (lt2 : ltype rto) P l r κ γ κ' γ' bmin0 (T : place_cont_t (place_rfn rto * gname)) :
    li_tactic (lctx_lft_alive_count_goal E L κ') (λ '(κs, L'),
      (∀ l', typed_place π E L' l' lt2 r (Uniq κ γ ⊓ₖ bmin0) (Uniq κ γ) P
        (λ L'' κs' l2 b2 bmin rti tyli ri strong weak,
          T L'' (κs ++ κs') l2 b2 (Uniq κ' γ' ⊓ₖ bmin) rti tyli ri
            (* strong branch: fold to OpenedLtype *)
            (fmap (λ strong, mk_strong (λ rti, (place_rfn (strong.(strong_rt) rti) * gname)%type)
              (λ rti2 ltyi2 ri2,
                OpenedLtype (MutLtype (strong.(strong_lt) _ ltyi2 ri2) κ) (MutLtype lt2 κ) (MutLtype lt2 κ) (λ r1 r1', ⌜r1 = r1'⌝) (λ _ _, llft_elt_toks κs))
              (λ rti2 ri2, #((strong.(strong_rfn) _ ri2), γ))
              strong.(strong_R)) strong)
            (* weak branch: just keep the MutLtype *)
            (fmap (λ weak, mk_weak (λ lti' ri', MutLtype (weak.(weak_lt) lti' ri') κ) (λ (r : place_rfn rti), #(weak.(weak_rfn) r, γ)) weak.(weak_R)) weak))))
    ⊢ typed_place π E L l (MutLtype lt2 κ) #(r, γ) bmin0 (Uniq κ' γ') (DerefPCtx Na1Ord PtrOp true :: P) T.
  Proof.
    rewrite /lctx_lft_alive_count_goal.
    iIntros "(%κs & %L2 & %Hal & HT)".
    iIntros (Φ F ??). iIntros "#(LFT & TIME & LLCTX) #HE HL #Hincl0 HP HΦ/=".
    (* get a token *)
    iApply fupd_wp. iMod (fupd_mask_subseteq lftE) as "HclF"; first done.
    iMod (lctx_lft_alive_count_tok lftE with "HE HL") as (q) "(Hκ' & Hclκ' & HL)"; [done.. | ].
    iMod "HclF" as "_". iMod (fupd_mask_subseteq F) as "HclF"; first done.
    iPoseProof (mut_ltype_acc_uniq F with "[$LFT $TIME $LLCTX] Hκ' Hclκ' HP") as "(%Hly & Hlb & Hb)"; [done.. | ].
    iMod "Hb" as "(%l' & Hl & Hb & Hcl)". iMod "HclF" as "_".
    iModIntro. iApply (wp_logical_step with "TIME Hcl"); [solve_ndisj.. | ].
    iApply (wp_deref with "Hl") => //; [solve_ndisj | by apply val_to_of_loc | ].
    iNext.
    iIntros (st) "Hl Hcred Hcl".
    iExists l'.
    iSplitR. { iPureIntro. unfold mem_cast. rewrite val_to_of_loc. done. }
    iApply ("HT" with "[//] [//] [$LFT $TIME $LLCTX] HE HL [] Hb"). { iApply bor_kind_min_incl_l. }
    iModIntro. iIntros (L'' κs' l2 b2 bmin rti tyli ri strong weak) "#Hincl1 Hb Hs".
    iApply ("HΦ" $! _ _ _ _ (Uniq κ' γ' ⊓ₖ bmin) _ _ _ _ _ with "[Hincl1] Hb").
    { iApply bor_kind_incl_trans; last iApply "Hincl1". iApply bor_kind_min_incl_r. }
    simpl. iSplit.
    - (* strong update *)
      iDestruct "Hs" as "(Hs & _)". iDestruct "Hcl" as "(_ & Hcl)".
      destruct strong as [ strong | ]; last done.
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
      simpl.
      iMod ("Hcl" with "Hl Hb [] Hcond") as "(Hb & Hκ' & Hcond)".
      { iApply bor_kind_incl_trans; first iApply bor_kind_min_incl_r. done. }
      iModIntro. iFrame. rewrite llft_elt_toks_app. iFrame.
      iApply typed_place_cond_incl; last done.
      iApply bor_kind_min_incl_r.
  Qed.
  Global Instance typed_place_mut_uniq_inst {rto} E L π κ κ' γ γ' (lt2 : ltype rto) bmin0 r l P :
    TypedPlace E L π l (MutLtype lt2 κ) (#(r, γ)) bmin0 (Uniq κ' γ') (DerefPCtx Na1Ord PtrOp true :: P) | 30 := λ T, i2p (typed_place_mut_uniq π E L lt2 P l r κ γ κ' γ' bmin0 T).

  Lemma typed_place_mut_shared {rto} π E L (lt2 : ltype rto) P l r κ γ κ' bmin0 (T : place_cont_t (place_rfn rto * gname)) :
    li_tactic (lctx_lft_alive_count_goal E L κ') (λ '(κs, L'),
      (∀ l', typed_place π E L' l' lt2 r (Shared (κ ⊓ κ') ⊓ₖ bmin0) (Shared (κ ⊓ κ')) P
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
            (fmap (λ weak, mk_weak (λ lti' ri', MutLtype (weak.(weak_lt) lti' ri') κ) (λ (r : place_rfn rti), #(weak.(weak_rfn) r, γ)) weak.(weak_R)) weak))))
    ⊢ typed_place π E L l (MutLtype lt2 κ) #(r, γ) bmin0 (Shared κ') (DerefPCtx Na1Ord PtrOp true :: P) T.
  Proof.
    rewrite /lctx_lft_alive_count_goal.
    iIntros "(%κs & %L2 & %Hal & HT)".
    iIntros (Φ F ??). iIntros "#(LFT & TIME & LLCTX) #HE HL #Hincl0 HP HΦ/=".
    (* get a token *)
    iApply fupd_wp. iMod (fupd_mask_subseteq lftE) as "HclF"; first done.
    iMod (lctx_lft_alive_count_tok lftE with "HE HL") as (q) "(Hκ' & Hclκ' & HL)"; [done.. | ].
    iMod "HclF" as "_". iMod (fupd_mask_subseteq F) as "HclF"; first done.
    iPoseProof (mut_ltype_acc_shared F with "[$LFT $TIME $LLCTX] Hκ' HP") as "(%Hly & Hlb & Hb)"; [done.. | ].
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
  Global Instance typed_place_mut_shared_inst {rto} E L π κ κ' γ (lt2 : ltype rto) bmin0 r l P :
    TypedPlace E L π l (MutLtype lt2 κ) (#(r, γ)) bmin0 (Shared κ') (DerefPCtx Na1Ord PtrOp true :: P) | 30 := λ T, i2p (typed_place_mut_shared π E L lt2 P l r κ γ κ' bmin0 T).

  (** Stratification *)
  Lemma stratify_ltype_mut_owned {rt} π E L mu mdu ma {M} (ml : M) l (lt : ltype rt) κ (r : (place_rfn rt)) wl γ
      (T : llctx → iProp Σ → ∀ rt', ltype rt' → place_rfn rt' → iProp Σ) :
    (∀ l', stratify_ltype π E L mu mdu ma ml l' lt r (Uniq κ γ) (λ L' R rt' lt' r',
      match ma with
      | StratRefoldFull =>
          cast_ltype_to_type E L' lt' (λ ty', T L' R _ (◁ (mut_ref ty' κ))%I (PlaceIn (r', γ)))
      | _ =>
          T L' R _ (MutLtype lt' κ) (PlaceIn (r', γ))
      end))
    ⊢ stratify_ltype π E L mu mdu ma ml l (MutLtype lt κ) (PlaceIn (r, γ)) (Owned wl) T.
  Proof.
    iIntros "Hs". iIntros (?? ?) "#(LFT & TIME & LLCTX) #HE HL Hb".
    iPoseProof (mut_ltype_acc_owned F with "[$LFT $TIME $LLCTX] Hb") as "Hb"; [done.. | ].
    iDestruct "Hb" as "(%Hly & #Hlb & >(%l' & Hl & Hb & Hcl))".
    iPoseProof ("Hs" with "[//] [//] [$LFT $TIME $LLCTX] HE HL Hb") as "Hb".
    iMod "Hb" as "(%L' & %R & %rt' & %lt' & %r' & HL & %Hcond & Hstep & Hc)".
    destruct (decide (ma = StratRefoldFull)) as [Heq | ].
    - subst ma.
      iDestruct "Hc" as "(%ty' & %Heq' & HT)".
      iPoseProof (eqltype_use F with "[$LFT $TIME $LLCTX] HE HL") as "(Hvs & HL)"; [done | .. ].
      { apply full_eqltype_alt. apply Heq'. }
      (*iPoseProof (eqltype_acc with "[$LFT $TIME $LLCTX] HE HL") as "#Heq"; first done.*)
      iModIntro. iExists L', R, _, _, _. iFrame.
      iSplitR. { simp_ltypes. done. }
      iApply logical_step_fupd.
      iApply (logical_step_compose with "Hcl").
      iApply (logical_step_compose with "Hstep").
      iApply logical_step_intro. iIntros "(Hb & $) Hcl".
      iMod ("Hvs" with "Hb") as "Hb".
      iMod ("Hcl" with "Hl Hb") as "(Hb & _)".
      iDestruct (mut_ref_unfold_1 ty' κ (Owned wl)) as "(_ & #Hi & _)".
      iMod (fupd_mask_mono with "(Hi Hb)") as "$"; first done.
      done.
    - iAssert (T L' R _ (MutLtype lt' κ) (PlaceIn (r', γ)))%I with "[Hc]" as "Hc".
      { destruct ma; done. }
      iModIntro. iExists L', R, _, _, _. iFrame.
      iSplitR. { simp_ltypes; done. }
      iApply logical_step_fupd.
      iApply (logical_step_compose with "Hcl").
      iApply (logical_step_compose with "Hstep").
      iApply logical_step_intro. iIntros "(Hb & $) Hcl".
      by iMod ("Hcl" with "Hl Hb") as "($ & _)".
  Qed.
  Global Instance stratify_ltype_mut_owned_weak_inst {rt} π E L mdu ma {M} (ml : M) l (lt : ltype rt) κ (r : (place_rfn rt)) wl γ :
    StratifyLtype π E L StratMutWeak mdu ma ml l (MutLtype lt κ) (PlaceIn (r, γ)) (Owned wl) :=
      λ T, i2p (stratify_ltype_mut_owned π E L StratMutWeak mdu ma ml l lt κ r wl γ T).
  Global Instance stratify_ltype_mut_owned_none_inst {rt} π E L mdu ma {M} (ml : M) l (lt : ltype rt) κ (r : (place_rfn rt)) wl γ :
    StratifyLtype π E L StratMutNone mdu ma ml l (MutLtype lt κ) (PlaceIn (r, γ)) (Owned wl) := λ T, i2p (stratify_ltype_mut_owned π E L StratMutNone mdu ma ml l lt κ r wl γ T).

  Lemma stratify_ltype_mut_uniq {rt} π E L mu mdu ma {M} (ml : M) l (lt : ltype rt) κ (r : (place_rfn rt)) κ' γ' γ
      (T : llctx → iProp Σ → ∀ rt', ltype rt' → place_rfn rt' → iProp Σ) :
    (* get a lifetime token *)
    li_tactic (lctx_lft_alive_count_goal E L κ') (λ '(κs, L1),
      (∀ l', stratify_ltype π E L1 mu mdu ma ml l' lt r (Uniq κ γ) (λ L2 R rt' lt' r',
        (* validate the update *)
        prove_place_cond E L2 (Uniq κ' γ') lt lt' (λ upd,
          match upd with
          | ResultWeak Heq =>
              (* update obeys the contract, get a mutable reference *)
              match ma with
              | StratRefoldFull => cast_ltype_to_type E L2 lt' (λ ty', T L2 (llft_elt_toks κs ∗ R) _ (◁ (mut_ref ty' κ))%I (PlaceIn (r', γ)))
              | _ => T L2 (llft_elt_toks κs ∗ R) _ (MutLtype lt' κ) (PlaceIn (r', γ))
              end
          | ResultStrong =>
              (* unfold to an OpenedLtype *)
              ⌜ma = StratNoRefold⌝ ∗
              T L2 R _ (OpenedLtype (MutLtype lt' κ) (MutLtype lt κ) (MutLtype lt κ) (λ r1 r2, ⌜r1 = r2⌝) (λ _ _, llft_elt_toks κs)) (PlaceIn (r', γ))
          end))))
    ⊢ stratify_ltype π E L mu mdu ma ml l (MutLtype lt κ) (PlaceIn (r, γ)) (Uniq κ' γ') T.
  Proof.
    iIntros "Hs". iIntros (?? ?) "#(LFT & TIME & LLCTX) #HE HL Hb".
    rewrite /lctx_lft_alive_count_goal.
    iDestruct "Hs" as "(%κs & %L1 & %Hal & Hs)".
    iMod (fupd_mask_subseteq lftE) as "HF_cl"; first done.
    iMod (lctx_lft_alive_count_tok with "HE HL") as "(%q & Htok & Hcl_tok & HL)"; [done.. | ].
    iMod "HF_cl" as "_".
    iPoseProof (mut_ltype_acc_uniq F with "[$LFT $TIME $LLCTX] Htok Hcl_tok Hb") as "Hb"; [done.. | ].
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
        iDestruct (mut_ltype_incl_uniq with "[] [] []") as "(_ & #Hincl & _)".
        { iIntros (?). iApply "Heq". }
        { iApply lft_incl_refl. }
        { iApply lft_incl_refl. }
        iPoseProof ("Hincl" with "Hl") as "Hl".
        by iApply (mut_ref_unfold_1_uniq with "Hl").
      + iAssert (T L2 (llft_elt_toks κs ∗ R) _ (MutLtype lt' κ) #(r', γ))%I with "[Hs]" as "Hs".
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
  Global Instance stratify_ltype_mut_uniq_weak_inst {rt} π E L mdu ma {M} (ml : M) l (lt : ltype rt) κ (r : (place_rfn rt)) κ' γ' γ :
    StratifyLtype π E L StratMutWeak mdu ma ml l (MutLtype lt κ) (PlaceIn (r, γ)) (Uniq κ' γ') :=
      λ T, i2p (stratify_ltype_mut_uniq π E L StratMutWeak mdu ma ml l lt κ r κ' γ' γ T).
  Global Instance stratify_ltype_mut_uniq_none_inst {rt} π E L mdu ma {M} (ml : M) l (lt : ltype rt) κ (r : (place_rfn rt)) κ' γ' γ :
    StratifyLtype π E L StratMutNone mdu ma ml l (MutLtype lt κ) (PlaceIn (r, γ)) (Uniq κ' γ') :=
      λ T, i2p (stratify_ltype_mut_uniq π E L StratMutNone mdu ma ml l lt κ r κ' γ' γ T).

  (** Unfolding instances *)
  Lemma stratify_ltype_ofty_mut {rt} `{Inhabited rt} π E L mu ma {M} (ml : M) l (ty : type rt) κ (r : place_rfn (place_rfn rt * gname)) b T :
    stratify_ltype π E L mu StratDoUnfold ma ml l (MutLtype (◁ ty) κ) r b T
    ⊢ stratify_ltype π E L mu StratDoUnfold ma ml l (◁ (mut_ref ty κ)) r b T.
  Proof.
    iIntros "Hp". iApply stratify_ltype_eqltype; iFrame.
    iPureIntro. iIntros (?) "HL CTX HE".
    iApply ltype_eq_sym. iApply mut_ref_unfold.
  Qed.
  Global Instance stratify_ltype_ofty_mut_inst {rt} `{Inhabited rt} π E L mu ma {M} (ml : M) l (ty : type rt) κ (r : place_rfn (place_rfn rt * gname)) b :
    StratifyLtype π E L mu StratDoUnfold ma ml l (◁ (mut_ref ty κ))%I r b | 30 :=
      λ T, i2p (stratify_ltype_ofty_mut π E L mu ma ml l ty κ r b T).


  (** prove_place_cond instances *)
  (* These need to have a lower priority than the ofty_refl instance (level 2) and the unblocking instances (level 5), but higher than the trivial "no" instance *)
  Lemma prove_place_cond_unfold_mut_l E L {rt1 rt2} `{Inhabited rt1} (ty : type rt1) (lt : ltype rt2) κ k T :
    prove_place_cond E L k (MutLtype (◁ ty) κ) lt T
    ⊢ prove_place_cond E L k (◁ (mut_ref ty κ)) lt T.
  Proof.
    iApply prove_place_cond_eqltype_l. apply symmetry. apply mut_ref_unfold_full_eqltype; done.
  Qed.
  Global Instance prove_place_cond_unfold_mut_l_inst E L {rt1 rt2} `{Inhabited rt1} (ty : type rt1) (lt : ltype rt2) κ k :
    ProvePlaceCond E L k (◁ (mut_ref ty κ))%I lt | 10 := λ T, i2p (prove_place_cond_unfold_mut_l E L ty lt κ k T).
  Lemma prove_place_cond_unfold_mut_r E L {rt1 rt2} `{Inhabited rt1} (ty : type rt1) (lt : ltype rt2) κ k T :
    prove_place_cond E L k lt (MutLtype (◁ ty) κ) T
    ⊢ prove_place_cond E L k lt (◁ (mut_ref ty κ)) T.
  Proof.
    iApply prove_place_cond_eqltype_r. apply symmetry. apply mut_ref_unfold_full_eqltype; done.
  Qed.
  Global Instance prove_place_cond_unfold_mut_r_inst E L {rt1 rt2} `{Inhabited rt1} (ty : type rt1) (lt : ltype rt2) κ k :
    ProvePlaceCond E L k lt (◁ (mut_ref ty κ))%I | 10 := λ T, i2p (prove_place_cond_unfold_mut_r E L ty lt κ k T).

  Lemma prove_place_cond_mut_ltype E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κ1 κ2 k T :
    ⌜lctx_lft_incl E L κ1 κ2⌝ ∗ ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ prove_place_cond E L k lt1 lt2 (λ upd, T $ access_result_lift (λ rt, (place_rfn rt * gname)%type) upd)
    ⊢ prove_place_cond E L k (MutLtype lt1 κ1) (MutLtype lt2 κ2) T.
  Proof.
    iIntros "(%Hincl1 & %Hincl2 & HT)". iIntros (F ?) "#CTX #HE HL".
    iPoseProof (lctx_lft_incl_incl with "HL HE") as "#Hincl1"; first apply Hincl1.
    iPoseProof (lctx_lft_incl_incl with "HL HE") as "#Hincl2"; first apply Hincl2.
    iMod ("HT" with "[//] CTX HE HL") as "($ & (%upd & Hcond & HT))".
    iExists _. iFrame.
    destruct upd.
    - subst rt2. cbn.
      iApply ltype_eq_place_cond_ty_trans; first last.
      { by iApply mut_ltype_place_cond_ty. }
      iIntros (??). iApply mut_ltype_eq; [ | done..]. iIntros (??). iApply ltype_eq_refl.
    - cbn. done.
  Qed.
  Global Instance prove_place_cond_mut_ltype_inst E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κ1 κ2 k :
    ProvePlaceCond E L k (MutLtype lt1 κ1) (MutLtype lt2 κ2) | 5 := λ T, i2p (prove_place_cond_mut_ltype E L lt1 lt2 κ1 κ2 k T).

  (** Typing rule for mutable borrows, manually applied by the tactics *)
  Lemma type_mut_bor E L T e π κ_name (ty_annot : option rust_type) :
    (∃ M, named_lfts M ∗ li_tactic (compute_map_lookup_nofail_goal M κ_name) (λ κ,
      (named_lfts M -∗ typed_borrow_mut π E L e κ ty_annot (λ L' v γ rt ty r,
        T L' v (place_rfn rt * gname)%type (mut_ref ty κ) (PlaceIn r, γ)))))
    ⊢ typed_val_expr π E L (&ref{Mut, ty_annot, κ_name} e)%E T.
  Proof.
    rewrite /compute_map_lookup_nofail_goal.
    iIntros "HT".
    iDestruct "HT" as "(%M & Hnamed & %κ & _ & HT)". iIntros (Φ) "#(LFT & TIME & LLCTX) #HE HL Hna HΦ".
    wp_bind. iSpecialize ("HT" with "Hnamed").
    iApply ("HT" $! _ ⊤ with "[//] [//] [//] [$LFT $TIME $LLCTX] HE HL Hna").
    iIntros (l) "Hat HT".
    unfold Ref.
    wp_bind.
    iApply (wp_logical_step with "TIME [HT Hat]"); [solve_ndisj.. | | ].
    { iApply (logical_step_compose with "HT").
      iApply (logical_step_intro_atime with "Hat").
      iIntros "H1 H2 !> H3". iApply ("H3" with "H1 H2"). }
    (* also need to generate a new cumulative receipt for the created reference *)
    iMod (additive_time_receipt_0) as "Hc".
    iMod (persistent_time_receipt_0) as "Hp".
    iApply (wp_skip_credits with "TIME Hc Hp"); first done.
    iIntros "!> Hcred1 Hc HT" => /=.
    iMod ("HT") as "(%L' & %rt' & %ty & %r & %γ & %ly & Hobs & Hbor & %Hst & %Hly & #Hlb & #Hsc & HL & Hna & HT)".
    iModIntro.
    (* generate the credits for the new reference *)
    iMod (persistent_time_receipt_0) as "Hp".
    iApply (wp_skip_credits with "TIME Hc Hp"); first done.
    rewrite (additive_time_receipt_sep 1). iNext. iIntros "[Hcred2 Hcred] [Hat1 Hat]".
    (* We use [Hcred1] for folding the pinned borrow, and [Hcred] as a deposit in the reference *)
    iApply ("HΦ" with "HL Hna [Hcred Hcred1 Hat Hat1 Hbor Hobs] HT").
    iExists l, ly. iSplitR; first done. iFrame "# ∗".
    iSplitR; first done. iSplitR; first done.
    by iApply (pinned_bor_unfold with "LFT Hcred1 Hbor").
  Qed.

  (** resolve_ghost *)
  Lemma resolve_ghost_mut_Owned {rt} π E L l (lt : ltype rt) γ rm lb κ wl T :
    find_observation (place_rfn rt * gname) γ FindObsModeDirect (λ or,
        match or with
        | None => ⌜rm = ResolveTry⌝ ∗ T L (PlaceGhost γ) True false
        | Some r => T L #r True true
        end)
    ⊢ resolve_ghost π E L rm lb l (MutLtype lt κ) (Owned wl) (PlaceGhost γ) T.
  Proof.
    rewrite /FindOptGvarPobs /=.
    iIntros "HT". iIntros (F ??) "#CTX #HE HL Hb".
    iMod ("HT" with "[//]") as "HT". iDestruct "HT" as "[(%r & Hobs & HT) | (-> & HT)]".
    - rewrite ltype_own_mut_ref_unfold /mut_ltype_own.
      iDestruct "Hb" as "(%ly & %Hst & %Hly & ? & ? & %γ0 & %r'& Hrfn & ?)".
      simpl.
      iPoseProof (gvar_pobs_agree_2 with "Hrfn Hobs") as "%Heq". subst r.
      iModIntro. iExists _, _, _, _. iFrame. iApply maybe_logical_step_intro.
      iL. rewrite ltype_own_mut_ref_unfold /mut_ltype_own.
      iExists _. iFrame. do 2 iR. iExists _, _. iR. iFrame.
    - iExists _, _, _, _. iFrame. iApply maybe_logical_step_intro. by iFrame.
  Qed.
  Global Instance resolve_ghost_mut_owned_inst {rt} π E L l (lt : ltype rt) κ γ wl rm lb :
    ResolveGhost π E L rm lb l (MutLtype lt κ) (Owned wl) (PlaceGhost γ) | 7 := λ T, i2p (resolve_ghost_mut_Owned π E L l lt γ rm lb κ wl T).

  Lemma resolve_ghost_mut_Uniq {rt} π E L l (lt : ltype rt) γ rm lb κ κ' γ' T :
    find_observation (place_rfn rt * gname) γ FindObsModeDirect (λ or,
        match or with
        | None => ⌜rm = ResolveTry⌝ ∗ T L (PlaceGhost γ) True false
        | Some r => T L #r True true
        end)
    ⊢ resolve_ghost π E L rm lb l (MutLtype lt κ) (Uniq κ' γ') (PlaceGhost γ) T.
  Proof.
    rewrite /FindOptGvarPobs /=.
    iIntros "HT". iIntros (F ??) "#CTX #HE HL Hb".
    iMod ("HT" with "[//]") as "HT". iDestruct "HT" as "[(%r & Hobs & HT) | (-> & HT)]".
    - rewrite ltype_own_mut_ref_unfold /mut_ltype_own.
      iDestruct "Hb" as "(%ly & %Hst & %Hly & ? & ? & Hrfn & ?)".
      simpl.
      iPoseProof (Rel2_use_pobs with "Hobs Hrfn") as "(%r2 & Hobs & ->)".
      iModIntro. iExists _, _, _,_. iFrame. iApply maybe_logical_step_intro.
      iL. rewrite ltype_own_mut_ref_unfold /mut_ltype_own.
      iExists _. iFrame. done.
    - iExists _, _, _, _. iFrame. iApply maybe_logical_step_intro. by iFrame.
  Qed.
  Global Instance resolve_ghost_mut_uniq_inst {rt} π E L l (lt : ltype rt) κ γ κ' γ' rm lb :
    ResolveGhost π E L rm lb l (MutLtype lt κ) (Uniq κ' γ') (PlaceGhost γ) | 7 := λ T, i2p (resolve_ghost_mut_Uniq π E L l lt γ rm lb κ κ' γ' T).

  Lemma resolve_ghost_mut_shared {rt} π E L l (lt : ltype rt) γ rm lb κ κ' T :
    find_observation (place_rfn rt * gname) γ FindObsModeDirect (λ or,
        match or with
        | None => ⌜rm = ResolveTry⌝ ∗ T L (PlaceGhost γ) True false
        | Some r => T L #r True true
        end)
    ⊢ resolve_ghost π E L rm lb l (MutLtype lt κ) (Shared κ') (PlaceGhost γ) T.
  Proof.
    rewrite /FindOptGvarPobs /=.
    iIntros "HT". iIntros (F ??) "#CTX #HE HL Hb".
    iMod ("HT" with "[//]") as "HT". iDestruct "HT" as "[(%r & Hobs & HT) | (-> & HT)]".
    - rewrite ltype_own_mut_ref_unfold /mut_ltype_own.
      iDestruct "Hb" as "(%ly & %Hst & %Hly & ? & %γ0 & %r'& Hrfn & ?)".
      simpl.
      iPoseProof (gvar_pobs_agree_2 with "Hrfn Hobs") as "%Heq". subst r.
      iModIntro. iExists _, _, _, _. iFrame. iApply maybe_logical_step_intro.
      iL. rewrite ltype_own_mut_ref_unfold /mut_ltype_own.
      iExists _. iFrame. do 2 iR. iExists _, _. iR. iFrame.
    - iExists _, _, _, _. iFrame. iApply maybe_logical_step_intro. by iFrame.
  Qed.
  Global Instance resolve_ghost_mut_shared_inst {rt} π E L l (lt : ltype rt) κ γ κ' rm lb :
    ResolveGhost π E L rm lb l (MutLtype lt κ) (Shared κ') (PlaceGhost γ) | 7 := λ T, i2p (resolve_ghost_mut_shared π E L l lt γ rm lb κ κ' T).

  (** cast_ltype *)
  Lemma cast_ltype_to_type_mut E L {rt} `{Inhabited rt} (lt : ltype rt) κ T  :
    cast_ltype_to_type E L lt (λ ty, T (mut_ref ty κ))
    ⊢ cast_ltype_to_type E L (MutLtype lt κ) T.
  Proof.
    iIntros "Hs". iDestruct "Hs" as "(%ty & %Heq & HT)".
    iExists (mut_ref ty κ). iFrame "HT". iPureIntro.
    by apply mut_ref_unfold_full_eqltype.
  Qed.
  Global Instance cast_ltype_to_type_mut_inst E L {rt} `{Inhabited rt} (lt : ltype rt) κ :
    CastLtypeToType E L (MutLtype lt κ) :=
    λ T, i2p (cast_ltype_to_type_mut E L lt κ T).

  (** Subtyping instances *)
  Lemma weak_subtype_mut E L {rt} `{!Inhabited rt} (ty1 ty2 : type rt) r1 r2 κ1 κ2 T :
    ⌜r1 = r2⌝ ∗ ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ mut_eqtype E L ty1 ty2 T
    ⊢ weak_subtype E L r1 r2 (mut_ref ty1 κ1) (mut_ref ty2 κ2) T.
  Proof.
    iIntros "(-> & %Hincl & %Heq & HT)".
    iIntros (??) "#CTX #HE HL".
    iPoseProof (lctx_lft_incl_incl with "HL") as "#Hincl"; first done.
    iSpecialize ("Hincl" with "HE").
    iPoseProof (full_eqtype_acc with "HE HL") as "#Heq"; first done.
    iFrame. unshelve iApply mut_ref_type_incl; [done | done | ..].
    - iIntros (r). iDestruct ("Heq" $! r) as "($ & _)".
    - iModIntro. iIntros (r). iDestruct ("Heq" $! r) as "(_ & $)".
  Qed.
  Global Instance weak_subtype_mut_inst E L {rt} `{!Inhabited rt} (ty1 ty2 : type rt) r1 r2 κ1 κ2 :
    Subtype E L r1 r2 (mut_ref ty1 κ1) (mut_ref ty2 κ2) :=
    λ T, i2p (weak_subtype_mut E L ty1 ty2 r1 r2 κ1 κ2 T).

  Lemma mut_subtype_mut E L {rt} `{!Inhabited rt} (ty1 ty2 : type rt) κ1 κ2 T :
    ⌜lctx_lft_incl E L κ1 κ2⌝ ∗ ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ mut_eqtype E L ty1 ty2 T
    ⊢ mut_subtype E L (mut_ref ty1 κ1) (mut_ref ty2 κ2) T.
  Proof.
    iIntros "(%Hincl1 & %Hincl2 & %Hsub & HT)". iFrame "HT".
    iPureIntro. apply mut_ref_full_subtype; done.
  Qed.
  Global Instance mut_subtype_mut_inst E L {rt} `{!Inhabited rt} (ty1 ty2 : type rt) κ1 κ2 :
    MutSubtype E L (mut_ref ty1 κ1) (mut_ref ty2 κ2) :=
    λ T, i2p (mut_subtype_mut E L ty1 ty2 κ1 κ2 T).

  Lemma mut_eqtype_mut E L {rt} `{!Inhabited rt} (ty1 ty2 : type rt) κ1 κ2 T :
    ⌜lctx_lft_incl E L κ1 κ2⌝ ∗ ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ mut_eqtype E L ty1 ty2 T
    ⊢ mut_eqtype E L (mut_ref ty1 κ1) (mut_ref ty2 κ2) T.
  Proof.
    iIntros "(%Hincl1 & %Hincl2 & %Heq & HT)". iFrame "HT".
    iPureIntro. apply full_subtype_eqtype; apply mut_ref_full_subtype; done.
  Qed.
  Global Instance mut_eqtype_mut_inst E L {rt} `{!Inhabited rt} (ty1 ty2 : type rt) κ1 κ2 :
    MutEqtype E L (mut_ref ty1 κ1) (mut_ref ty2 κ2) :=
    λ T, i2p (mut_eqtype_mut E L ty1 ty2 κ1 κ2 T).

  (** Subltyping instances *)
  (* generic in [r2] to handle the case that it is an evar *)
  Lemma weak_subltype_mut_owned_in E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) wl κ1 κ2 γ r1 r2 T :
    (∃ r2', ⌜r2 = #(r2', γ)⌝ ∗ ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ weak_subltype E L (Uniq κ1 γ) r1 r2' lt1 lt2 T)
    ⊢ weak_subltype E L (Owned wl) #(r1, γ) r2 (MutLtype lt1 κ1) (MutLtype lt2 κ2) T.
  Proof.
    iIntros "(%r2' & -> & %Hincl & HT)" (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(Hincl' & HL & $)".
    iPoseProof (lctx_lft_incl_incl with "HL") as "#Hincl"; first done.
    iSpecialize ("Hincl" with "HE"). iFrame.
    iApply (mut_ltype_incl_owned_in with "Hincl'").
    done.
  Qed.
  Global Instance weak_subltype_mut_owned_in_inst E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) wl κ1 κ2 γ r1 r2 :
    SubLtype E L (Owned wl) #(r1, γ) r2 (MutLtype lt1 κ1) (MutLtype lt2 κ2) | 10 := λ T, i2p (weak_subltype_mut_owned_in E L lt1 lt2 wl κ1 κ2 γ r1 r2 T).

  (* instance to destruct the pair if necessary *)
  Lemma weak_subltype_mut_owned_in' E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) wl κ1 κ2 r1 r2 T :
    (∀ r1' γ, ⌜r1 = (r1', γ)⌝ -∗ weak_subltype E L (Owned wl) #(r1', γ) r2 (MutLtype lt1 κ1) (MutLtype lt2 κ2) T)
    ⊢ weak_subltype E L (Owned wl) #r1 r2 (MutLtype lt1 κ1) (MutLtype lt2 κ2) T.
  Proof.
    iIntros "Ha". destruct r1. by iApply "Ha".
  Qed.
  Global Instance weak_subltype_mut_owned_in'_inst E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) wl κ1 κ2 r1 r2 :
    SubLtype E L (Owned wl) #r1 r2 (MutLtype lt1 κ1) (MutLtype lt2 κ2) | 12 := λ T, i2p (weak_subltype_mut_owned_in' E L lt1 lt2 wl κ1 κ2 r1 r2 T).

  Lemma weak_subltype_mut_shared_in E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κ κ1 κ2 γ r1 r2 T :
    (∃ r2', ⌜r2 = #(r2', γ)⌝ ∗ ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ weak_subltype E L (Shared (κ1 ⊓ κ)) r1 r2' lt1 lt2 T)
    ⊢ weak_subltype E L (Shared κ) #(r1, γ) r2 (MutLtype lt1 κ1) (MutLtype lt2 κ2) T.
  Proof.
    iIntros "(%r2' & -> & %Hincl & HT)" (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(Hincl' & HL & $)".
    iPoseProof (lctx_lft_incl_incl with "HL") as "#Hincl"; first done.
    iSpecialize ("Hincl" with "HE"). iFrame.
    iApply (mut_ltype_incl_shared_in with "[Hincl']"); last done.
    done.
  Qed.
  Global Instance weak_subltype_mut_shared_in_inst E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κ κ1 κ2 γ r1 r2 :
    SubLtype E L (Shared κ) #(r1, γ) r2 (MutLtype lt1 κ1) (MutLtype lt2 κ2) | 10 := λ T, i2p (weak_subltype_mut_shared_in E L lt1 lt2 κ κ1 κ2 γ r1 r2 T).

  (* Base instance that will trigger, e.g., for Uniq or PlaceGhost refinements *)
  (* TODO can have more specific instances for PlaceGhost for Shared and Owned *)
  Lemma weak_subltype_mut_base E L {rt} (lt1 lt2 : ltype rt) k κ1 κ2 r1 r2 T :
    ⌜r1 = r2⌝ ∗ ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ ⌜lctx_lft_incl E L κ1 κ2⌝ ∗ mut_eqltype E L lt1 lt2 T
    ⊢ weak_subltype E L k r1 r2 (MutLtype lt1 κ1) (MutLtype lt2 κ2) T.
  Proof.
    iIntros "(<- & %Hincl1 & %Hincl2 & %Hsubt & T)" (??) "#CTX #HE HL".
    iPoseProof (full_eqltype_acc with "CTX HE HL") as "#Hincl"; first done.
    iPoseProof (lctx_lft_incl_incl with "HL") as "#Hincl1"; first apply Hincl1.
    iSpecialize ("Hincl1" with "HE").
    iPoseProof (lctx_lft_incl_incl with "HL") as "#Hincl2"; first apply Hincl2.
    iSpecialize ("Hincl2" with "HE").
    iFrame. iApply mut_ltype_incl; done.
  Qed.
  Global Instance weak_subltype_mut_base_inst E L {rt} (lt1 lt2 : ltype rt) k κ1 κ2 r1 r2 :
    SubLtype E L k r1 r2 (MutLtype lt1 κ1) (MutLtype lt2 κ2) | 20 := λ T, i2p (weak_subltype_mut_base E L lt1 lt2 k κ1 κ2 r1 r2 T).

  Lemma weak_subltype_mut_evar_lft E L {rt} (lt1 lt2 : ltype rt) k κ1 κ2 r1 r2 T `{!IsProtected κ2} :
    ⌜κ1 = κ2⌝ ∗ weak_subltype E L k r1 r2 (MutLtype lt1 κ1) (MutLtype lt2 κ1) T
    ⊢ weak_subltype E L k r1 r2 (MutLtype lt1 κ1) (MutLtype lt2 κ2) T.
  Proof. iIntros "(<- & $)". Qed.
  Global Instance weak_subltype_mut_evar_lft_inst E L {rt} (lt1 lt2 : ltype rt) k κ1 κ2 r1 r2 `{!IsProtected κ2} :
    SubLtype E L k r1 r2 (MutLtype lt1 κ1) (MutLtype lt2 κ2) | 9 := λ T, i2p (weak_subltype_mut_evar_lft E L lt1 lt2 k κ1 κ2 r1 r2 T).

  Lemma mut_subltype_mut E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 T :
    ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ ⌜lctx_lft_incl E L κ1 κ2⌝ ∗ mut_eqltype E L lt1 lt2 T
    ⊢ mut_subltype E L (MutLtype lt1 κ1) (MutLtype lt2 κ2) T.
  Proof.
    iIntros "(%Hincl1 & %Hincl2 & %Heq & $)".
    iPureIntro. apply mut_full_subltype; done.
  Qed.
  Global Instance mut_subltype_mut_inst E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 :
    MutSubLtype E L (MutLtype lt1 κ1) (MutLtype lt2 κ2) | 10 := λ T, i2p (mut_subltype_mut E L lt1 lt2 κ1 κ2 T).

  Lemma mut_subltype_mut_evar_lft E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 T `{!IsProtected κ2} :
    ⌜κ1 = κ2⌝ ∗ mut_subltype E L (MutLtype lt1 κ1) (MutLtype lt2 κ1) T
    ⊢ mut_subltype E L (MutLtype lt1 κ1) (MutLtype lt2 κ2) T.
  Proof. iIntros "(<- & $)". Qed.
  Global Instance mut_subltype_mut_evar_lft_inst E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 `{!IsProtected κ2} :
    MutSubLtype E L (MutLtype lt1 κ1) (MutLtype lt2 κ2) | 9 := λ T, i2p (mut_subltype_mut_evar_lft E L lt1 lt2 κ1 κ2 T).

  Lemma mut_eqltype_mut E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 T :
    ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ ⌜lctx_lft_incl E L κ1 κ2⌝ ∗ mut_eqltype E L lt1 lt2 T
    ⊢ mut_eqltype E L (MutLtype lt1 κ1) (MutLtype lt2 κ2) T.
  Proof.
    iIntros "(%Hincl1 & %Hincl2 & %Heq & $)".
    iPureIntro. apply mut_full_eqltype; done.
  Qed.
  Global Instance mut_eqltype_mut_inst E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 :
    MutEqLtype E L (MutLtype lt1 κ1) (MutLtype lt2 κ2) := λ T, i2p (mut_eqltype_mut E L lt1 lt2 κ1 κ2 T).

  Lemma mut_eqltype_mut_evar_lft E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 T `{!IsProtected κ2} :
    ⌜κ1 = κ2⌝ ∗ mut_eqltype E L (MutLtype lt1 κ1) (MutLtype lt2 κ1) T
    ⊢ mut_eqltype E L (MutLtype lt1 κ1) (MutLtype lt2 κ2) T.
  Proof. iIntros "(<- & $)". Qed.
  Global Instance mut_eqltype_mut_evar_lft_inst E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 `{!IsProtected κ2} :
    MutEqLtype E L (MutLtype lt1 κ1) (MutLtype lt2 κ2) := λ T, i2p (mut_eqltype_mut_evar_lft E L lt1 lt2 κ1 κ2 T).

  (* Ofty unfolding if necessary *)
  Lemma weak_subltype_mut_ofty_1_evar E L {rt1 rt2} (lt1 : ltype rt1) (ty2 : type (place_rfn rt2 * gname)) k κ1 r1 r2 T :
    (∃ ty2', ⌜ty2 = mut_ref ty2' κ1⌝ ∗ weak_subltype E L k r1 r2 (MutLtype lt1 κ1) (◁ (mut_ref ty2' κ1)) T)
    ⊢ weak_subltype E L k r1 r2 (MutLtype lt1 κ1) (◁ ty2) T.
  Proof.
    iIntros "(%ty2' & -> & HT)". done.
  Qed.
  Global Instance weak_subltype_mut_ofty_1_evar_inst E L {rt1 rt2} (lt1 : ltype rt1) (ty2 : type (place_rfn rt2 * gname)) k κ1 r1 r2 `{!IsProtected ty2} :
    SubLtype E L k r1 r2 (MutLtype lt1 κ1) (◁ ty2)%I | 10 := λ T, i2p (weak_subltype_mut_ofty_1_evar E L lt1 ty2 k κ1 r1 r2 T).

  Lemma weak_subltype_mut_ofty_1 E L {rt1 rt2} `{!Inhabited rt2} (lt1 : ltype rt1) (ty2 : type rt2) k κ1 κ2 r1 r2 T :
    weak_subltype E L k r1 r2 (MutLtype lt1 κ1) (MutLtype (◁ ty2) κ2) T
    ⊢ weak_subltype E L k r1 r2 (MutLtype lt1 κ1) (◁ (mut_ref ty2 κ2)) T.
  Proof.
    iIntros "HT". iIntros (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(Hincl & $ & $)".
    iApply (ltype_incl_trans with "Hincl").
    iApply mut_ref_unfold_1.
  Qed.
  Global Instance weak_subltype_mut_ofty_1_inst E L {rt1 rt2} `{!Inhabited rt2} (lt1 : ltype rt1) (ty2 : type rt2) k κ1 κ2 r1 r2 :
    SubLtype E L k r1 r2 (MutLtype lt1 κ1) (◁ (mut_ref ty2 κ2))%I | 11 := λ T, i2p (weak_subltype_mut_ofty_1 E L lt1 ty2 k κ1 κ2 r1 r2 T).

  Lemma weak_subltype_mut_ofty_2 E L {rt1 rt2} `{!Inhabited rt1} (ty1 : type (rt1)) (lt2 : ltype rt2) k r1 r2 κ1 κ2 T :
    (weak_subltype E L k r1 r2 (MutLtype (◁ ty1) κ1) (MutLtype lt2 κ2) T)
    ⊢ weak_subltype E L k r1 r2 (◁ (mut_ref ty1 κ1)) (MutLtype lt2 κ2) T.
  Proof.
    iIntros "HT" (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(Hincl & $ & $)".
    iApply (ltype_incl_trans with "[] Hincl").
    iApply mut_ref_unfold_2.
  Qed.
  Global Instance weak_subltype_mut_ofty_2_inst E L {rt1 rt2} `{!Inhabited rt1} (ty1 : type (rt1)) (lt2 : ltype rt2) k r1 r2 κ1 κ2 :
    SubLtype E L k r1 r2 (◁ (mut_ref ty1 κ1))%I (MutLtype lt2 κ2) | 10 := λ T, i2p (weak_subltype_mut_ofty_2 E L ty1 lt2 k r1 r2 κ1 κ2 T).

  (* Same for mut_subltype *)
  Lemma mut_subltype_mut_ofty_1_evar E L {rt} (lt1 : ltype rt) (ty2 : type (place_rfn rt * gname)) κ1 T :
    (∃ ty2', ⌜ty2 = mut_ref ty2' κ1⌝ ∗ mut_subltype E L (MutLtype lt1 κ1) (◁ (mut_ref ty2' κ1)) T)
    ⊢ mut_subltype E L (MutLtype lt1 κ1) (◁ ty2) T.
  Proof.
    iIntros "(%ty2' & -> & HT)". done.
  Qed.
  Global Instance mut_subltype_mut_ofty_1_evar_inst E L {rt} (lt1 : ltype rt) (ty2 : type (place_rfn rt * gname)) κ1 `{!IsProtected ty2} :
    MutSubLtype E L (MutLtype lt1 κ1) (◁ ty2)%I | 10 := λ T, i2p (mut_subltype_mut_ofty_1_evar E L lt1 ty2 κ1 T).

  Lemma mut_subltype_mut_ofty_1 E L {rt} `{!Inhabited rt} (lt1 : ltype rt) (ty2 : type rt) κ1 κ2 T :
    mut_subltype E L (MutLtype lt1 κ1) (MutLtype (◁ ty2) κ2) T
    ⊢ mut_subltype E L (MutLtype lt1 κ1) (◁ (mut_ref ty2 κ2)) T.
  Proof.
    iIntros "(%Hsub & $)". iPureIntro.
    etrans; first done.
    eapply full_eqltype_subltype_l. by apply mut_ref_unfold_full_eqltype.
  Qed.
  Global Instance mut_subltype_mut_ofty_1_inst E L {rt} `{!Inhabited rt} (lt1 : ltype rt) (ty2 : type rt) κ1 κ2 :
    MutSubLtype E L (MutLtype lt1 κ1) (◁ (mut_ref ty2 κ2))%I | 10 := λ T, i2p (mut_subltype_mut_ofty_1 E L lt1 ty2 κ1 κ2 T).

  Lemma mut_subltype_mut_ofty_2 E L {rt} `{!Inhabited rt} (ty1 : type (rt)) (lt2 : ltype rt) κ1 κ2 T :
    (mut_subltype E L (MutLtype (◁ ty1) κ1) (MutLtype lt2 κ2) T)
    ⊢ mut_subltype E L (◁ (mut_ref ty1 κ1)) (MutLtype lt2 κ2) T.
  Proof.
    iIntros "(%Hsub & $)". iPureIntro.
    etrans; last done.
    eapply full_eqltype_subltype_r. by apply mut_ref_unfold_full_eqltype.
  Qed.
  Global Instance mut_subltype_mut_ofty_2_inst E L {rt} `{!Inhabited rt} (ty1 : type (rt)) (lt2 : ltype rt) κ1 κ2 :
    MutSubLtype E L (◁ (mut_ref ty1 κ1))%I (MutLtype lt2 κ2) | 10 := λ T, i2p (mut_subltype_mut_ofty_2 E L ty1 lt2 κ1 κ2 T).

  (* Same for mut_eqltype *)
  Lemma mut_eqltype_mut_ofty_1_evar E L {rt} (lt1 : ltype rt) (ty2 : type (place_rfn rt * gname)) κ1 T :
    (∃ ty2', ⌜ty2 = mut_ref ty2' κ1⌝ ∗ mut_eqltype E L (MutLtype lt1 κ1) (◁ (mut_ref ty2' κ1)) T)
    ⊢ mut_eqltype E L (MutLtype lt1 κ1) (◁ ty2) T.
  Proof.
    iIntros "(%ty2' & -> & HT)". done.
  Qed.
  Global Instance mut_eqltype_mut_ofty_1_evar_inst E L {rt} (lt1 : ltype rt) (ty2 : type (place_rfn rt * gname)) κ1 `{!IsProtected ty2} :
    MutEqLtype E L (MutLtype lt1 κ1) (◁ ty2)%I | 10 := λ T, i2p (mut_eqltype_mut_ofty_1_evar E L lt1 ty2 κ1 T).

  Lemma mut_eqltype_mut_ofty_1 E L {rt} `{!Inhabited rt} (lt1 : ltype rt) (ty2 : type rt) κ1 κ2 T :
    mut_eqltype E L (MutLtype lt1 κ1) (MutLtype (◁ ty2) κ2) T
    ⊢ mut_eqltype E L (MutLtype lt1 κ1) (◁ (mut_ref ty2 κ2)) T.
  Proof.
    iIntros "(%Heq & $)". iPureIntro.
    etrans; first done. by apply mut_ref_unfold_full_eqltype.
  Qed.
  Global Instance mut_eqltype_mut_ofty_1_inst E L {rt} `{!Inhabited rt} (lt1 : ltype rt) (ty2 : type rt) κ1 κ2 :
    MutEqLtype E L (MutLtype lt1 κ1) (◁ (mut_ref ty2 κ2))%I | 10 := λ T, i2p (mut_eqltype_mut_ofty_1 E L lt1 ty2 κ1 κ2 T).

  Lemma mut_eqltype_mut_ofty_2 E L {rt} `{!Inhabited rt} (ty1 : type (rt)) (lt2 : ltype rt) κ1 κ2 T :
    (mut_eqltype E L (MutLtype (◁ ty1) κ1) (MutLtype lt2 κ2) T)
    ⊢ mut_eqltype E L (◁ (mut_ref ty1 κ1)) (MutLtype lt2 κ2) T.
  Proof.
    iIntros "(%Heq & $)". iPureIntro.
    etrans; last done. symmetry. by apply mut_ref_unfold_full_eqltype.
  Qed.
  Global Instance mut_eqltype_mut_ofty_2_inst E L {rt} `{!Inhabited rt} (ty1 : type (rt)) (lt2 : ltype rt) κ1 κ2 :
    MutEqLtype E L (◁ (mut_ref ty1 κ1))%I (MutLtype lt2 κ2) | 10 := λ T, i2p (mut_eqltype_mut_ofty_2 E L ty1 lt2 κ1 κ2 T).

  (** Annotations for shortening the lifetime of a reference *)
  (* TODO: generalize this to nametrees and nested stuff *)
  (* TODO think about how this should deal with structs and descending below them *)
  (*
  Lemma type_shortenlft_mut E L sup_lfts {rt} `{!Inhabited rt} (ty : type rt) r κ π v T :
    (∃ M κs, named_lfts M ∗ ⌜lookup_named_lfts M sup_lfts = Some κs⌝ ∗
      ⌜lctx_lft_incl E L (lft_intersect_list' κs) κ⌝ ∗
      (named_lfts M -∗ v ◁ᵥ{π} r @ mut_ref ty (lft_intersect_list' κs) -∗ T L)) -∗
    typed_annot_expr E L 0 (ShortenLftAnnot sup_lfts) v (v ◁ᵥ{π} r @ mut_ref ty κ) T.
  Proof.
    iIntros "(%M & %κs & Hnamed & % & %Hincl & HT)".
    iIntros "#CTX #HE HL Hv /=".
    iPoseProof (lctx_lft_incl_incl with "HL HE") as "#Hincl"; first done.
    iModIntro. iExists L. iFrame "HL". iApply ("HT" with "Hnamed").
    unshelve iApply (mut_ref_own_val_mono with "[//] [] [] Hv"); first done.
    all: iIntros (?); iApply type_incl_refl.
  Qed.
  Global Instance type_shortenlft_mut_inst E L sup_lfts {rt} `{!Inhabited rt} (ty : type rt) r κ π v :
    TypedAnnotExpr E L 0 (ShortenLftAnnot sup_lfts) v (v ◁ᵥ{π} r @ mut_ref ty κ) :=
    λ T, i2p (type_shortenlft_mut E L sup_lfts ty r κ π v T).
   *)
End rules.

Global Typeclasses Opaque mut_ref.
Notation "&mut< κ , τ >" := (mut_ref τ κ) (only printing, format "'&mut<' κ , τ '>'") : stdpp_scope.
