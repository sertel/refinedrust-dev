From lrust.lifetime Require Export lifetime.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import saved_prop.
From iris Require Import options.

(** * Defining pinned borrows on top of the existing lifetime logic. *)

(** Normal borrows &{κ} P in the lifetime logic just carry around their current contents P.
Pinned borrows &{κ}[Q] P additionally remember what ownership Q the lender actually expects back, and this can be used to get stronger rules when updating the contents P to P'.

Pinned borrows can be obtained from regular borrows at any time, and folded back when the current contents P match the pinned ownership Q, as expressed by the rules [pinned_bor_fold] and [pinned_bor_unfold].

The key new rule provided by pinned borrows is [pinned_bor_acc_strong]: it states how the contents P of a pinned borrow &{κ} [Q] P may be accessed and modified by \emph{opening} the borrow.
Specifically, it allows to exchange a pinned borrow and a proof that κ is still alive (expressed through a lifetime token q.[κ]) for the contents P of the borrow, as well as an update stating how the borrow may be closed again.
This update allows to put any updated proposition P' into the borrow to regain ownership of the borrow and the token, provided that it can be shown that P' can be returned to the ownership Q expected by the borrows lender again.
Specifically, once κ is dead (expressed by †κ), P' needs to be updatable either to P, the previous contents, or just to the pinned contents Q expected by the lender.
 *)

(** Compared to a proper deep change in the model of the lifetime logic, we have to strip two later modalities for some operations, which we get around with using Iris's later credits mechanism. *)

Class pinnedBorG Σ := PinnedBorG {
  pinnedBorG_saved_prop_ownG : savedPropG Σ;
}.
Local Existing Instance pinnedBorG_saved_prop_ownG.
Global Hint Mode pinnedBorG - : typeclass_instances.

Definition pinnedBorΣ : gFunctors := #[ savedPropΣ ].
Global Instance subG_pinnedBorΣ {Σ} : subG pinnedBorΣ Σ → pinnedBorG Σ.
Proof. solve_inG. Qed.

Section pinned_borrows.
  Context `{!invGS Σ} `{!pinnedBorG Σ} `{!lftGS Σ userE}.

  (** The model of pinned borrows *)
  Local Definition pinned_bor_def (κ : lft) (Q : iProp Σ) (P : iProp Σ) : iProp Σ :=
    ∃ γ κ' P', κ ⊑ κ' ∗ saved_prop_own γ (DfracOwn (1/2)) P' ∗
      ▷ □ (P' → P) ∗
      ▷ □ (P → P' ∨ Q) ∗
      &{κ'} (∃ P' : iProp Σ, saved_prop_own γ (DfracOwn (1/2)) P' ∗ P' ∗
        £1 ∗ (P' -∗ [† κ'] ={userE}=∗ ▷ Q)).
  Local Definition pinned_bor_aux : seal (@pinned_bor_def). Proof. by eexists. Qed.
  Definition pinned_bor := pinned_bor_aux.(unseal).
  Local Definition pinned_bor_unseal : @pinned_bor = @pinned_bor_def := pinned_bor_aux.(seal_eq).

  Lemma pinned_bor_shorten κ κ' Q P :
    κ ⊑ κ' -∗
    pinned_bor κ' Q P -∗
    pinned_bor κ Q P.
  Proof.
    iIntros "Hincl Hb". rewrite pinned_bor_unseal.
    iDestruct "Hb" as (γ κ0 P0) "(Hincl0 & Hsaved & Hbor)".
    iExists γ, κ0, P0. iFrame.
    iApply (lft_incl_trans with "Hincl Hincl0").
  Qed.

  Lemma pinned_bor_fake E κ P Q :
    ↑lftN ⊆ E →
    lft_ctx -∗
    [†κ] ={E}=∗ pinned_bor κ Q P.
  Proof.
    iIntros (?) "#LFT Hdead". rewrite pinned_bor_unseal.
    iMod (saved_prop_alloc P (DfracOwn 1)) as (γ) "[Hsaved1 Hsaved2]"; first done.
    iMod (bor_fake with "LFT Hdead") as "Hb"; first done.
    iExists γ, κ, P.
    iFrame. iModIntro. iSplit; last iSplit.
    - iApply lft_incl_refl.
    - eauto.
    - eauto.
  Qed.

  (** We need the credit for the inheritance viewshift. *)
  Lemma pinned_bor_unfold E κ P :
    ↑lftN ⊆ E →
    lft_ctx -∗
    £1 -∗
    &{κ} P ={E}=∗ pinned_bor κ P P.
  Proof.
    iIntros (?) "#LFT Hcred Hb".
    iMod (saved_prop_alloc P (DfracOwn 1%Qp)) as (γ) "[Hs1 Hs2]"; first done.
    iMod (bor_acc_atomic_strong with "LFT Hb") as "[Ha | Hdead]"; first done.
    - rewrite pinned_bor_unseal.
      iDestruct "Ha" as (κ') "(#Hincl & HP & Hcl)".
      set (Q := (∃ P', saved_prop_own γ (DfracOwn (1/2)) P' ∗ P' ∗ £1 ∗
        (P' -∗ [† κ'] ={userE}=∗ ▷ P))%I).
      iMod ("Hcl" $! Q with "[] [Hs2 HP Hcred]") as "Ha".
      + iNext. iIntros "(%P' & Hsaved & HP' & >Hcred & Hvs) Hdead".
        (* this is a problem due to commuting. Need a credit. *)
        iApply (lc_fupd_add_later with "Hcred"). iNext.
        iMod ("Hvs" with "HP' Hdead") as "HP". eauto.
      + iNext. iExists P. iFrame. eauto.
      + iModIntro. iExists γ, κ', P. iFrame "#∗". iSplit; eauto.
    - iDestruct "Hdead" as "(Hdead & Hcl)". iMod "Hcl" as "_".
      by iApply (pinned_bor_fake with "LFT Hdead").
  Qed.

  (** Note: we need a credit here to eliminate the later when opening a borrow.
     Just having a later in the VS does not work because we are using an atomic accessor. *)
  Lemma pinned_bor_fold E κ P :
    ↑lftN ⊆ E →
    lft_ctx -∗
    £1 -∗
    pinned_bor κ P P ={E}=∗ &{κ} P.
  Proof.
    iIntros (?) "#LFT Hcred Hb". rewrite pinned_bor_unseal.
    iDestruct "Hb" as (γ κ' P0) "(Hincl & Hsaved & #HP0P & #HPP0 & Hb)".
    iMod (bor_acc_atomic_strong with "LFT Hb") as "[Ha | Hdead]"; first done.
    - iDestruct "Ha" as (κ'') "(#Hincl' & HP & Hcl)".
      iDestruct "HP" as (P') "HP".
      (* we cannot just use [Hcred'] here, as we need to return it in the closing viewshift *)
      iMod (lc_fupd_elim_later with "Hcred HP") as "HP".
      iDestruct "HP" as "(Hsaved' & HP & Hcred' & _)".
      iPoseProof (saved_prop_agree with "Hsaved Hsaved'") as "#Hag".
      iMod (saved_prop_update_halves P with "Hsaved Hsaved'") as "[Hsaved Hsaved']".
      iMod ("Hcl" $! P with "[Hsaved' Hcred'] [HP]") as "HP".
      + iNext. iIntros "HP _ !>!>". iExists P. iFrame. eauto.
      + iNext. iApply "HP0P". iRewrite "Hag". done.
      + iModIntro. iApply (bor_shorten with "[Hincl] HP").
        iApply (lft_incl_trans with "Hincl Hincl'").
    - iDestruct "Hdead" as "(Hdead & Hcl)". iMod "Hcl" as "_".
      iMod (lft_incl_dead with "Hincl Hdead") as "Hdead"; first done.
      iApply (bor_fake with "LFT Hdead"); done.
  Qed.

  (** This variant requires a proof of liveness of [κ], but in turn only requires a later instead of a credit. *)
  Lemma pinned_bor_fold_tok E q κ P :
    ↑lftN ⊆ E →
    lft_ctx -∗
    q.[κ] -∗
    pinned_bor κ P P ={E}▷=∗ &{κ} P ∗ q.[κ].
  Proof.
    iIntros (?) "#LFT Htok Hb". rewrite pinned_bor_unseal.
    iDestruct "Hb" as (γ κ' P0) "(#Hincl & Hsaved & #HP0P & #HPP0 & Hb)".
    iMod (lft_incl_acc with "Hincl Htok") as "(%q' & Htok & Hcl_tok)"; first done.
    iMod (bor_acc_strong with "LFT Hb Htok") as "(%κ'' & #Hincl' & Ha & Hcl)"; first done.
    iDestruct "Ha" as (P') "HP".
    iModIntro. iNext.
    iDestruct "HP" as "(Hsaved' & HP & Hcred' & _)".
    iPoseProof (saved_prop_agree with "Hsaved Hsaved'") as "#Hag".
    iMod (saved_prop_update_halves P with "Hsaved Hsaved'") as "[Hsaved Hsaved']".
    iMod ("Hcl" $! P with "[Hsaved' Hcred'] [HP]") as "(HP & Htok)".
    + iNext. iIntros "HP _ !>!>". iExists P. iFrame. eauto.
    + iNext. iApply "HP0P". iRewrite "Hag". done.
    + iMod ("Hcl_tok" with "Htok") as "$".
      iApply (bor_shorten with "[Hincl] HP").
      iApply (lft_incl_trans with "Hincl Hincl'").
  Qed.


  (** The key rule *)
  (* This lemma requires a credit in the closing viewshift.
     This is a choice we take in order to not get two laters over [P] when opening, but "just" one.
     For the client, this slightly restricts the interface, but the credit-based reasoning we do here
     could not otherwise encoded on top of the client since having two laters over [P] breaks
     timeless-ness reasoning for credits.
  *)
  Lemma pinned_bor_acc_strong E q κ P Q :
    ↑lftN ⊆ E →
    lft_ctx -∗
    pinned_bor κ Q P -∗
    q.[κ] ={E}=∗
    ∃ κ' : lft, κ ⊑ κ' ∗
      ▷ P ∗
      ▷ (P -∗ [† κ'] ={userE}=∗ ▷ Q) ∗
      (∀ R,
        ▷ (R -∗ [†κ'] ={userE}=∗ ▷ Q) -∗
        £1 -∗
        ▷ R ={E}=∗
        pinned_bor κ' Q R ∗ q.[κ]).
  Proof.
    iIntros (?) "#LFT Hb Htok". rewrite pinned_bor_unseal.
    iDestruct "Hb" as (γ κ' P0) "(#Hincl & Hsaved1 & #HP0P & #HPP0 & Hb)".
    iMod (lft_incl_acc with "Hincl Htok") as (q') "(Htok & Hcl_tok)"; first done.
    iMod (bor_acc with "LFT Hb Htok") as "(HP & Hcl)"; first done.
    iDestruct "HP" as (P') "(Hsaved2 & HP & >Hcred & Hvs)".
    (* use the credit to strip the later over [Hsaved2] *)
    iMod (lc_fupd_elim_later with "Hcred Hsaved2") as "Hsaved2".
    iPoseProof (saved_prop_agree with "Hsaved1 Hsaved2") as "#Hag".
    iModIntro. iExists κ'. iFrame "Hincl".
    iSplitL "HP". { iNext. iApply "HP0P". iRewrite "Hag". done. }
    iSplitL "Hvs". {
      iNext. iIntros "HP". iDestruct ("HPP0" with "HP") as "[HP0 | HQ]".
      - iRewrite "Hag" in "HP0". iApply ("Hvs" with "HP0").
      - eauto.
    }
    iIntros (R) "Hvs' Hcred HR".
    iMod (saved_prop_update_halves R with "Hsaved1 Hsaved2") as "(Hsaved1 & Hsaved2)".
    iMod ("Hcl"  with "[Hsaved2 HR Hcred Hvs']") as "(Hb & Htok)".
    - iNext. iExists R. iFrame.
    - iMod ("Hcl_tok" with "Htok") as "$".
      iModIntro. iExists γ, κ', R. iFrame. iSplitL; last iSplitL.
      + iApply lft_incl_refl.
      + eauto.
      + eauto.
  Qed.

  (* A variant with two laters instead of the credit for completeness. *)
  Lemma pinned_bor_acc_strong' E q κ P Q :
    ↑lftN ⊆ E →
    lft_ctx -∗
    pinned_bor κ Q P -∗
    q.[κ] ={E}=∗
    ∃ κ' : lft, κ ⊑ κ' ∗ ▷(
      ▷ P ∗
      ▷ (P -∗ [† κ'] ={userE}=∗ ▷ Q) ∗
      (∀ R,
        ▷ (R -∗ [†κ'] ={userE}=∗ ▷ Q) -∗
        ▷ R ={E}=∗
        pinned_bor κ' Q R ∗ q.[κ])).
  Proof.
    iIntros (?) "#LFT Hb Htok". rewrite pinned_bor_unseal.
    iDestruct "Hb" as (γ κ' P0) "(#Hincl & Hsaved1 & #HP0P & #HPP0 & Hb)".
    iMod (lft_incl_acc with "Hincl Htok") as (q') "(Htok & Hcl_tok)"; first done.
    iMod (bor_acc with "LFT Hb Htok") as "(HP & Hcl)"; first done.
    iDestruct "HP" as (P') "(Hsaved2 & HP & >Hcred & Hvs)".
    iModIntro. iExists κ'. iFrame "Hincl". iNext.
    iPoseProof (saved_prop_agree with "Hsaved1 Hsaved2") as "#Hag".
    iSplitL "HP". { iNext. iRewrite -"Hag" in "HP". iApply "HP0P". done. }
    iSplitL "Hvs". {
      iNext. iIntros "HP". iDestruct ("HPP0" with "HP") as "[HP0 | HQ]".
      - iRewrite "Hag" in "HP0". iApply ("Hvs" with "HP0").
      - eauto.
    }
    iIntros (R) "Hvs' HR".
    iMod (saved_prop_update_halves R with "Hsaved1 Hsaved2") as "(Hsaved1 & Hsaved2)".
    iMod ("Hcl"  with "[Hsaved2 HR Hcred Hvs']") as "(Hb & Htok)".
    - iNext. iExists R. iFrame.
    - iMod ("Hcl_tok" with "Htok") as "$".
      iModIntro. iExists γ, κ', R. iFrame. iSplitL; last iSplitL.
      + iApply lft_incl_refl.
      + eauto.
      + eauto.
  Qed.

  (** derived variant where we go back to [P] *)
  Lemma pinned_bor_acc_back E q κ P Q :
    ↑lftN ⊆ E →
    lft_ctx -∗
    pinned_bor κ Q P -∗
    q.[κ] ={E}=∗ ▷ P ∗
    (▷ Q -∗ £1 ={E}=∗ pinned_bor κ Q Q ∗ q.[κ]).
  Proof.
    iIntros (?) "#LFT Hb Htok".
    iMod (pinned_bor_acc_strong with "LFT Hb Htok") as (κ') "(Hincl & Hb & Hvs & Hclose)"; first done.
    iModIntro. iFrame "Hb".
    iIntros "HQ Hcred". iMod ("Hclose" $! Q with "[] Hcred HQ") as "(Hb & $)".
    { eauto. }
    iApply (pinned_bor_shorten with "Hincl Hb").
  Qed.

  Lemma pinned_bor_acc E q κ P Q :
    ↑lftN ⊆ E →
    lft_ctx -∗
    pinned_bor κ Q P -∗
    q.[κ] ={E}=∗
    ▷ P ∗ (▷ P -∗ £1 ={E}=∗ pinned_bor κ Q P ∗ q.[κ]).
  Proof.
    iIntros (?) "#LFT Hb Htok".
    iMod (pinned_bor_acc_strong with "LFT Hb Htok") as (κ') "(Hincl & Hb & Hvs & Hclose)"; first done.
    iModIntro. iFrame "Hb".
    iIntros "HP Hcred". iMod ("Hclose" $! P with "Hvs Hcred HP") as "(Hb & $)".
    iApply (pinned_bor_shorten with "Hincl Hb").
  Qed.

  (* NOTE: we could also have an adapted version of this that takes a lifetime token proving that κ is live,
      and in turn use laters instead of credits
     -- the credits are necessary because we can't intro laters in a step_fupdN when accessing a borrow atomically. *)
  Lemma pinned_bor_rebor_full E κ κ' P Q :
    ↑lftN ⊆ E →
    lft_ctx -∗
    κ' ⊑ κ -∗
    £2 -∗
    pinned_bor κ Q P ={E}=∗
    &{κ'} P ∗ ([† κ'] ={E}=∗ pinned_bor κ Q P).
  Proof.
    (* Proof sketch:
        1. unfold the pinned borrow.
        2. rebor the full borrow.
        3. adapt the contents of the borrow to P somehow.
          - open with atomic accessor
          - strip the later with a credit
          - use saved prop agreement, use a credit
          - close the borrow with the existential over P'' frozen to P
        4. use bor_sep on the closed borrow to throw away the parts that are not P.
        5. for the inheritance, use the inheritance of the full reborrow.
           then just assemble everything again. *)
    iIntros (?) "#LFT #Hincl (Hcred1 & Hcred2) Hb".
    rewrite pinned_bor_unseal /pinned_bor_def.
    iDestruct "Hb" as "(%γ & %κ'' & %P' & #Hincl' & Hsaved & HP & HP' & Hb)".
    iMod (rebor _ _ κ' with "LFT [] Hb") as "(Hb & Hinh)"; first done.
    { iApply lft_incl_trans; done. }

    (* access the borrow to get agreement, spends credits due to atomic borrow *)
    iMod (bor_acc_atomic_strong with "LFT Hb") as "[(%κ0 & #Hincl0 & Hb & Hcl_b) | (#Hdead_κ' & >_)]"; first done; first last.
    { iMod (bor_fake _ _ P with "LFT Hdead_κ'") as "$"; first done.
      iIntros "!> _".
      iMod ("Hinh" with "Hdead_κ'") as "Hb".
      iModIntro. iExists γ, κ'', P'. iFrame. done. }
    iApply (lc_fupd_add_later with "Hcred1"). iNext.
    iDestruct "Hb" as "(%P'' & Hsaved2 & HP'' & Hcred & Hvs)".
    iPoseProof (saved_prop_agree with "Hsaved Hsaved2") as "#Hag".
    iApply (lc_fupd_add_later with "Hcred2"). iNext.
    iMod (saved_prop_update_halves P with "Hsaved Hsaved2") as "(Hsaved & Hsaved2)".
    iDestruct "HP" as "#HP". iDestruct "HP'" as "#HP'".
    iMod ("Hcl_b" $! (saved_prop_own γ (DfracOwn (1 / 2)) P ∗ P ∗ £ 1 ∗ (P -∗ [†κ''] ={userE}=∗ ▷ Q))%I with "[] [Hsaved2 HP'' Hcred Hvs]") as "Hb".
    { iNext. iIntros "(Hsaved & Hprop & Hcred & Hvs) Hdead".
      iModIntro. iNext. iExists P. iFrame. }
    { iFrame. iNext. iSplitL "HP''". { iApply "HP". iRewrite "Hag". iFrame. }
      iIntros "Hprop Hdead". iDestruct ("HP'" with "Hprop") as "[Hprop | Hprop]"; last by eauto.
      iApply ("Hvs" with "[Hprop] Hdead"). iRewrite -"Hag". done. }

    iMod (bor_sep with "LFT Hb") as "(_ & Hb)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Hb & _)"; first done.

    iModIntro.
    iSplitL "Hb". { iApply bor_shorten; last done. done. }
    iIntros "Hdead". iMod ("Hinh" with "Hdead") as "Hb".
    iModIntro. iExists γ, κ'', P. iFrame.
    iSplit; first done. iSplit; iNext; iModIntro; eauto.
  Qed.

  (* Here, we need [κ] to be alive, because we cannot use the atomic accessor for the proof.
      With the atomic accessor, we cannot execute the update inside the borrow when first opening it,
     but that update is important for the inheritance viewshift of the outer borrow for thunking. *)
  Lemma pinned_bor_unnest_full E κ κ' P Q q :
    ↑lftN ⊆ E →
    lft_ctx -∗
    £ 2 -∗
    q.[κ] -∗
    &{κ} (|={↑lftN}=> pinned_bor κ' Q P) ={E}▷=∗^2
    &{κ ⊓ κ'} P ∗ q.[κ].
  Proof.
    (* Proof sketch:
       1. open the borrow
       2. use a later.
       3. use the reborrow lemma for κ ⊓ κ'
       4. close the borrow, with the full borrow + inheritance; the fact that we have the ↑lftN mask is crucial for the inheritance here.
       5. use bor_sep and throw away the borrow of the inheritance
       6. use the bor_unnest lemma *)
    iIntros (?) "#LFT Hcred2 Htok Hb".
    iMod (bor_acc_strong with "LFT Hb Htok") as "(%κ'' & #Hincl & Hb & Hcl)"; first done.
    iModIntro. iNext. iMod (fupd_mask_mono with "Hb") as "Hb"; first done.
    iMod (fupd_mask_subseteq (↑lftN)) as "Hcl_E"; first done.
    iMod (pinned_bor_rebor_full (↑lftN) _ (κ ⊓ κ') with "LFT [] Hcred2 Hb") as "Hb"; first done.
    { iApply lft_intersect_incl_r. }
    iMod "Hcl_E" as "_".
    iMod ("Hcl" with "[] Hb") as "(Hb & $)".
    { iNext. iIntros "(Hb & Hinh) Hdead".
      iModIntro. iNext. iMod (lft_incl_dead _ (κ ⊓ κ') with "[] Hdead") as "Hdead"; first done.
      { iApply lft_incl_trans; last done. iApply lft_intersect_incl_l. }
      iMod ("Hinh" with "Hdead") as "$". eauto. }
    iMod (bor_sep with "LFT Hb") as "(Hb & _)"; first done.
    iMod (bor_unnest with "LFT Hb") as "Hb"; first done.
    iModIntro. iModIntro. iNext. iMod "Hb".
    iApply (bor_shorten with "[] Hb").
    iApply lft_incl_glb.
    - iApply lft_incl_refl.
    - iApply lft_incl_trans; last done.
      iApply lft_intersect_incl_l.
  Qed.

  Global Instance pinned_bor_ne κ n :
    Proper (dist n ==> dist n ==> dist n) (pinned_bor κ).
  Proof. rewrite pinned_bor_unseal. solve_proper. Qed.

  Global Instance pinned_bor_equiv κ :
    Proper (equiv ==> equiv ==> equiv) (pinned_bor κ).
  Proof. rewrite pinned_bor_unseal. solve_proper. Qed.

  Lemma pinned_bor_impl κ P Q R :
    (▷ □ ((P → R) ∧ (R → Q))) -∗
    pinned_bor κ Q P -∗
    pinned_bor κ Q R.
  Proof.
    rewrite pinned_bor_unseal. iIntros "#[HPR HRQ] Hb".
    iDestruct "Hb" as (γ κ' P0) "(#Hincl & Hsaved1 & #HP0P & #HPP0 & Hb)".
    iExists γ, κ', P0. iFrame "#∗".
    iSplit; iModIntro; iModIntro.
    - iIntros "HP0". iApply "HPR". iApply "HP0P". done.
    - iIntros "HR". iRight. iApply "HRQ". done.
  Qed.

  Lemma pinned_bor_iff κ P P' Q Q' :
    (▷ □ ((P → P') ∧ (P' → P))) -∗
    (▷ □ ((Q → Q') ∧ (Q' → Q))) -∗
    pinned_bor κ Q P -∗
    pinned_bor κ Q' P'.
  Proof.
    rewrite pinned_bor_unseal. iIntros "#[HPP' HP'P] #[HQQ' HQ'Q] Hb".
    iDestruct "Hb" as (γ κ' P0) "(#Hincl & Hsaved1 & #HP0P & #HPP0 & Hb)".
    iExists γ, κ', P0. iFrame "#∗".
    iSplitR; last iSplitR.
    - iIntros "!> !>HP0". iApply "HPP'". iApply "HP0P". done.
    - iIntros "!>!>HP'".
      iPoseProof ("HP'P" with "HP'") as "HP".
      iPoseProof ("HPP0" with "HP") as "[HP0 | HQ]".
      + by iLeft.
      + iRight. by iApply "HQQ'".
    - iApply (bor_iff with "[] Hb").
      iNext. iModIntro. iSplit; iIntros "(%PP & Hsaved & HPP & Hcred & Hvs)"; iExists PP; iFrame.
      all: iIntros "HPP Hdead"; iMod ("Hvs" with "HPP Hdead") as "HQ".
      + by iApply "HQQ'".
      + by iApply "HQ'Q".
  Qed.

  Lemma pinned_bor_iff' κ P Q :
    (▷ □ ((P → Q) ∧ (Q → P))) -∗
    pinned_bor κ P P -∗
    pinned_bor κ Q Q.
  Proof.
    iIntros "#Heq". iApply pinned_bor_iff; done.
  Qed.

  Lemma pinned_bor_impl' κ (P Q Q' R : iProp Σ) :
    ▷ □ ((P → R) ∧ (R → Q)) -∗
    ▷ □ ((Q → Q') ∧ (Q' → Q)) -∗
    pinned_bor κ Q P -∗ pinned_bor κ Q' R.
  Proof.
    iIntros "#Ha #Hb".
    iIntros "Hx".
    iPoseProof (pinned_bor_iff _ _ P _ Q' with "[] [] Hx") as "Hx".
    { eauto 8. }
    { done. }
    iApply (pinned_bor_impl with "[] Hx").
    iNext. iModIntro. iSplit.
    - iDestruct "Ha" as "(Hc & _)". done.
    - iDestruct "Ha" as "(_ & Hc)".
      iDestruct "Hb" as "(Hb & _)".
      iIntros "HR". iApply "Hb". iApply "Hc". done.
  Qed.

  (* TODO maybe we can get the same thing without a token by using atomic accessors? *)
  Lemma pinned_bor_exists_freeze {X} `{Inhabited X} κ q E (Q : iProp Σ) (Φ : X → iProp Σ) :
    ↑lftN ⊆ E →
    lft_ctx -∗
    pinned_bor κ Q (∃ x : X, Φ x) -∗
    q.[κ] -∗
    £ 1 ={E}=∗
    ∃ x : X, pinned_bor κ Q (Φ x) ∗ q.[κ].
  Proof.
    iIntros (?) "#LFT Hb Htok Hcred".
    iMod (pinned_bor_acc_strong with "LFT Hb Htok") as "(%κ' & #Hincl & HP & Hret & Hcl)"; first done.
    iDestruct "HP" as "(%x & HP)".
    iMod ("Hcl" $! (Φ x) with "[Hret] Hcred HP") as "(Hb & Htok)".
    - iNext. iIntros "HP". iApply "Hret". eauto.
    - iModIntro. iExists x. iFrame.
      by iApply pinned_bor_shorten.
  Qed.
  (* using a later instead *)
  Lemma pinned_bor_exists_freeze' {X} `{Inhabited X} κ q E (Q : iProp Σ) (Φ : X → iProp Σ) :
    ↑lftN ⊆ E →
    lft_ctx -∗
    pinned_bor κ Q (∃ x : X, Φ x) -∗
    q.[κ] ={E}▷=∗
    ∃ x : X, pinned_bor κ Q (Φ x) ∗ q.[κ].
  Proof.
    iIntros (?) "#LFT Hb Htok".
    iMod (pinned_bor_acc_strong' with "LFT Hb Htok") as "(%κ' & #Hincl & HP & Hret & Hcl)"; first done.
    iDestruct "HP" as "(%x & HP)".
    iExists x.
    iModIntro. iNext.
    iMod ("Hcl" $! (Φ x) with "[Hret] HP") as "(Hb & Htok)".
    - iNext. iIntros "HP". iApply "Hret". eauto.
    - iModIntro. iFrame.
      by iApply pinned_bor_shorten.
  Qed.

  (* TODO can we have atomic accessors for pinned borrows like bor_acc_atomic?
     Problem/disadvantage: they will require later credits, which makes them much less useful for many things.
   *)
End pinned_borrows.

Notation "'&pin{'  κ  }  [ P ]  Q" := (pinned_bor κ P Q) (at level 40) : bi_scope.
Notation "'&pin{'  κ  }  P" := (pinned_bor κ P P) (at level 40) : bi_scope.


(*
  One idle idea (that does not work):
  If we work in a model where everything is prepaid, do we need pinned borrows anymore?
    The immediate idea would be to use atomic accessors and use the credits we have stored to strip the laters,
    and that we can do even if we don't have lifetime tokens, since all this happens atomically.
    The problem then is that we cannot regenerate those credits.
 *)
