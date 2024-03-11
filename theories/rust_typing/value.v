From refinedrust Require Export type ltypes programs.
From refinedrust Require Import memcasts ltype_rules.
From iris Require Import options.

(** * The value type *)
(** The value type just says that there is a particular sequence of bytes which can be read and written from memory at a particular [op_type]. *)


Definition is_value_ot_core (ot : op_type) (ot' : op_type) (mt : memcast_compat_type) : Prop :=
  match ot' with
  | UntypedOp ly => ly = ot_layout ot
  | _ => ot' = ot ∧ mt ≠ MCId
  end.
Lemma is_value_ot_core_layout ot ot' mt:
  is_value_ot_core ot ot' mt → ot_layout ot' = ot_layout ot.
Proof. destruct ot' => //=; naive_solver. Qed.
Lemma is_value_ot_core_refl ot mt :
  mt ≠ MCId → is_value_ot_core ot ot mt.
Proof. destruct ot;simpl; done. Qed.

Definition is_value_ot `{!LayoutAlg} (st : syn_type) (ot' : op_type) (mt : memcast_compat_type) : Prop :=
  ∃ ot, use_op_alg st = Some ot ∧ is_value_ot_core ot ot' mt ∧ syn_type_has_layout st (ot_layout ot).

Global Typeclasses Opaque is_value_ot.

Lemma is_value_ot_untyped `{!LayoutAlg} st mt ly :
  syn_type_has_layout st ly →
  is_value_ot (UntypedSynType ly) (UntypedOp ly) mt.
Proof.
  intros Halg. eexists (UntypedOp ly). split_and!.
  - done.
  - done.
  - eapply syn_type_has_layout_make_untyped; done.
Qed.

Lemma is_value_ot_use_op_alg `{!LayoutAlg} st ly mc :
  mc ≠ MCId →
  syn_type_has_layout st ly →
  is_value_ot st (use_op_alg' st) mc.
Proof.
  intros ? Ha.
  specialize (syn_type_has_layout_op_alg _ _ Ha) as (ot & Hot & <-).
  rewrite /use_op_alg' Hot /=. eexists _. split; first done.
  split; last done. destruct ot; done.
Qed.

Section value.
  Context `{!typeGS Σ}.

  (* Intuitively: want to say that the value is v _up to memcasts_ at st.  *)
  Program Definition value_t (st : syn_type) : type val := {|
    st_own π vs v :=
      (∃ ot,
        ⌜use_op_alg st = Some ot⌝ ∗
        ⌜is_memcast_val vs ot v⌝ ∗
        ⌜v `has_layout_val` (ot_layout ot)⌝ ∗
        ⌜syn_type_has_layout st (ot_layout ot)⌝)%I;
    st_syn_type := st;
    st_has_op_type ot' mt := is_value_ot st ot' mt;
  |}.
  Next Obligation.
    iIntros (st π vs v) "(%ot & % & % & % & %)". eauto.
  Qed.
  Next Obligation.
    simpl. intros st ot' mt (ot & Halg & Hot & Hst).
    rewrite (is_value_ot_core_layout _ _ _ Hot). done.
  Qed.
  Next Obligation.
    (* mem-cast *)
    intros st ot' mt ? π vs v (ot & Halg & Hot & Hst).
    iIntros "(%ot'' & %Halg' & %Hmc & %Hly & %Hst')".
    assert (ot'' = ot) as -> by by eapply use_op_alg_inj.
    destruct mt; first done.
    - iPureIntro. exists ot. split_and!; [ done | | | done].
      + specialize (is_memcast_val_has_layout_val' _ _ _ _ Hmc Hly) as Hly'.
        destruct ot'; simpl in Hot; try destruct Hot; subst;
          [.. | done | ].
        all: apply is_memcast_val_memcast; [done | by eapply use_op_alg_wf | done].
      + by apply has_layout_val_mem_cast.
    - iPureIntro.
      destruct ot'; simpl in Hot;
        try match type of Hot with | _ ∧ _  => destruct Hot end; subst; done.
  Qed.

  Global Instance value_copy st : Copyable (value_t st).
  Proof. apply _. Qed.
End value.

Section lemmas.
  Context `{!typeGS Σ}.

  Lemma value_has_length π v v1 st ly :
    syn_type_has_layout st ly →
    v ◁ᵥ{π} v1 @ value_t st -∗
    ⌜length v1 = ly_size ly⌝ ∗ ⌜length v = ly_size ly⌝.
  Proof.
    rewrite /ty_own_val/=.
    iDestruct 1 as "(%ot & %Hot & %Hmc & %Hly & %Hst)".
    assert (ly = ot_layout ot) as -> by by eapply syn_type_has_layout_inj.
    iL. iPureIntro. apply is_memcast_val_length in Hmc as ->; done.
  Qed.

  Lemma value_has_layout π st v vs :
    v ◁ᵥ{π} vs @ value_t st -∗
    ∃ ly, ⌜syn_type_has_layout st ly⌝ ∗ ⌜v `has_layout_val` ly⌝.
  Proof.
    rewrite /ty_own_val.
    iDestruct 1 as "(%ot & %Hot & %Hmv & %Hv & %Hst)".
    iExists (ot_layout ot). iR. done.
  Qed.

  Lemma own_val_split_value π {rt} (ty : type rt) r v st ly :
    syn_type_has_layout (ty_syn_type ty) ly ∧ syn_type_has_layout st ly →
    v ◁ᵥ{π} r @ ty -∗
    v ◁ᵥ{π} v @ value_t st ∗ v ◁ᵥ{π} r @ ty.
  Proof.
    iIntros ((Hly & Hly')) "Hv".
    iPoseProof (ty_own_val_has_layout with "Hv") as "%Hv"; first done.
    subst. iFrame.
    specialize (syn_type_has_layout_op_alg _ _ Hly') as (ot & Hot & <-).
    iExists ot. iSplitR; first done.
    iSplitR. { iLeft. done. }
    done.
  Qed.

  Lemma value_untyped_make_typed π st ly v vs :
    syn_type_has_layout st ly →
    v ◁ᵥ{π} vs @ value_t (UntypedSynType ly) -∗
    v ◁ᵥ{π} vs @ value_t st.
  Proof.
    iIntros "%Halg Hv".
    rewrite /ty_own_val /=. iDestruct "Hv" as "(%ot & %Heq & %Hmc & %Hlyv & _)".
    injection Heq as <-.
    specialize (syn_type_has_layout_op_alg _ _ Halg) as (ot & Hop & <-).
    iExists ot. iSplitR; first done.
    iSplitR. { iLeft. apply is_memcast_val_untyped_inv in Hmc. done. }
    iSplitR; first done. done.
  Qed.

  Lemma value_untyped_layout_mono π v vs ly1 ly2 :
    ly_size ly1 = ly_size ly2 →
    (layout_wf ly1 → layout_wf ly2) →
    (ly_align_in_bounds ly1 → ly_align_in_bounds ly2) →
    v ◁ᵥ{π} vs @ value_t (UntypedSynType ly1) -∗
    v ◁ᵥ{π} vs @ value_t (UntypedSynType ly2).
  Proof.
    iIntros (Hsz Hwf Hal) "Hv". rewrite /ty_own_val /=.
    iDestruct "Hv" as "(%ot & %Heq & %Hmc & %Hly & %Hst)".
    injection Heq as <-. iExists _. iSplitR; first done.
    iSplitR. { apply is_memcast_val_untyped_inv in Hmc. by iLeft. }
    simpl. iSplitR. { rewrite /has_layout_val -Hsz //. }
    iPureIntro. simpl in Hst. apply syn_type_has_layout_untyped_inv in Hst as (_ & Hwf' & Hsz_le & ?).
    eapply syn_type_has_layout_untyped.
    - done.
    - by apply Hwf.
    - lia.
    - by apply Hal.
  Qed.

  Lemma value_untyped_app_merge π v1 v2 r1 r2 ly1 ly2 ly3 :
    syn_type_has_layout (UntypedSynType ly3) ly3 →
    ly_size ly3 = ly_size ly1 + ly_size ly2 →
    v1 ◁ᵥ{π} r1 @ value_t (UntypedSynType ly1) -∗
    v2 ◁ᵥ{π} r2 @ value_t (UntypedSynType ly2) -∗
    (v1 ++ v2) ◁ᵥ{π} (r1 ++ r2) @ value_t (UntypedSynType ly3).
  Proof.
    iIntros (??) "Hv1 Hv2".
    rewrite /ty_own_val /=.
    iDestruct "Hv1" as "(%ot1 & %Heq1 & %Hmc1 & %Hly1 & %Halg1)".
    iDestruct "Hv2" as "(%ot2 & %Heq2 & %Hmc2 & %Hly2 & %Halg2)".
    injection Heq1 as <-. injection Heq2 as <-.
    apply syn_type_has_layout_untyped_inv in Halg1 as (<- & Hwf1 & Hsz1).
    apply syn_type_has_layout_untyped_inv in Halg2 as (<- & Hwf2 & Hsz2).
    rewrite /has_layout_val in Hly1. rewrite /has_layout_val in Hly2.
    simpl in *.
    iExists _. iR. simpl.
    iPureIntro. split_and!.
    - eapply is_memcast_val_untyped_app; [ | done..]. done.
    - rewrite /has_layout_val. rewrite app_length. lia.
    - done.
  Qed.

  Lemma value_untyped_app_split π v v1 v2 ly1 ly2 ly3 :
    ly_size ly1 = ly_size ly2 + ly_size ly3 →
    length v1 = ly_size ly2 →
    layout_wf ly2 →
    layout_wf ly3 →
    ly_align_in_bounds ly3 →
    ly_align_in_bounds ly2 →
    v ◁ᵥ{π} (v1 ++ v2) @ value_t (UntypedSynType ly1) -∗
    (take (length v1) v) ◁ᵥ{π} v1 @ value_t (UntypedSynType ly2) ∗
    (drop (length v1) v) ◁ᵥ{π} v2 @ value_t (UntypedSynType ly3).
  Proof.
    iIntros (Hsz ?????) "Hv".
    rewrite /ty_own_val/=. iDestruct "Hv" as "(%ot & %Hot & %Hmc & %Hly & %Hst)".
    apply use_op_alg_untyped_inv in Hot as ->.
    apply syn_type_has_layout_untyped_inv in Hst as (<- & Hwf & Hsz' & ?).
    apply is_memcast_val_untyped_inv in Hmc as <-.
    rewrite /has_layout_val/= app_length in Hly.
    simpl in *.
    iSplit.
    - iPureIntro. exists (UntypedOp ly2). split; first done.
      split. { left. rewrite take_app//. }
      split. { rewrite take_app. rewrite /has_layout_val/=. lia. }
      apply syn_type_has_layout_untyped; try naive_solver lia.
    - iPureIntro. exists (UntypedOp ly3). split; first done.
      split. { left. rewrite drop_app//. }
      split. { rewrite drop_app. rewrite /has_layout_val/=. lia. }
      apply syn_type_has_layout_untyped; naive_solver lia.
  Qed.
End lemmas.

Section ofty_lemmas.
  Context `{!typeGS Σ}.

  Lemma ofty_value_has_length F π l st ly v1 :
    lftE ⊆ F →
    syn_type_has_layout st ly →
    l ◁ₗ[π, Owned false] #v1 @ (◁ value_t st) ={F}=∗
    ⌜length v1 = ly_size ly⌝ ∗ l ◁ₗ[π, Owned false] #v1 @ (◁ value_t st).
  Proof.
    iIntros (??) "Hl".
    rewrite ltype_own_ofty_unfold/lty_of_ty_own.
    iDestruct "Hl" as "(%ly' & % & % & ? & ? & ? & %r' & <- & Hb)".
    iMod (fupd_mask_mono with "Hb") as "(%v & Hl & Hv)"; first done.
    iPoseProof (value_has_length with "Hv") as "(% & %)"; first done.
    assert (ly' = ly) as -> by by eapply syn_type_has_layout_inj.
    iR. iModIntro. iExists _. iFrame. iR. iR. iExists _. iR.
    iModIntro. eauto with iFrame.
  Qed.

  (* NOTE: We can make this into a typed value afterwards using [ofty_value_untyped_make_typed] *)
  Lemma ofty_own_split_value_untyped π F l wl {rt} (ty : type rt) r ly :
    lftE ⊆ F →
    syn_type_has_layout (ty_syn_type ty) ly →
    (l ◁ₗ[π, Owned wl] #r @ ◁ ty)%I -∗ ▷?wl |={F}=> ∃ v,
    v ◁ᵥ{π} r @ ty ∗ l ◁ₗ[π, Owned wl] #v @ ◁ (value_t (UntypedSynType ly)).
  Proof.
    iIntros (? Halg) "Hty".
    rewrite (ltype_own_ofty_unfold ty) /lty_of_ty_own.
    iDestruct "Hty" as "(%ly' & % & % & Hsc & Hlb & Hc & %r' & <- & Hb)".
    assert (ly' = ly) as -> by by eapply syn_type_has_layout_inj.
    iNext.
    iMod (fupd_mask_mono with "Hb") as "(%v & Hl & Hv)"; first done.
    iPoseProof (own_val_split_value _ _ _ _ (UntypedSynType _) with "Hv") as "(Hv' & Hv)".
    { split; first done. eapply syn_type_has_layout_make_untyped; done. }
    iExists v. iFrame.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iExists _. simpl.
    iSplitR. { iPureIntro. eapply syn_type_has_layout_make_untyped; done. }
    iSplitR; first done. iFrame.
    iExists _. iSplitR; first done. iModIntro.
    iExists v. by iFrame.
  Qed.
  Lemma ofty_own_split_value_untyped_lc π F l wl {rt} (ty : type rt) r ly :
    lftE ⊆ F →
    syn_type_has_layout (ty_syn_type ty) ly →
    £ (Nat.b2n wl) -∗
    (l ◁ₗ[π, Owned wl] #r @ ◁ ty)%I ={F}=∗ ∃ v,
    v ◁ᵥ{π} r @ ty ∗ l ◁ₗ[π, Owned wl] #v @ ◁ (value_t (UntypedSynType ly)).
  Proof.
    iIntros (? Halg) "Hcred Hty".
    iPoseProof (ofty_own_split_value_untyped with "Hty") as "Hb"; [done.. |].
    iMod (lc_fupd_maybe_elim_later with "Hcred Hb") as "Ha". done.
  Qed.

  (* TODO ideally, the requirement for the UntypedOp case should just generally hold for types. Untyped should always be possible. *)
  Lemma ofty_own_merge_value {rt} π (ty : type rt) wl v r st l :
    match st with
    | UntypedSynType ly1 =>
        syn_type_has_layout (ty_syn_type ty) ly1 ∧ ty_has_op_type ty (UntypedOp ly1) MCCopy
    | _ =>
        ty_has_op_type ty (use_op_alg' (ty_syn_type ty)) MCCopy ∧ ty_syn_type ty = st
    end →
    v ◁ᵥ{ π} r @ ty -∗
    l ◁ₗ[ π, Owned wl] #v @ (◁ value_t st) -∗
    l ◁ₗ[ π, Owned wl] #r @ (◁ ty).
  Proof.
    iIntros (?) "Hv Hl".
    rewrite !ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hl" as "(%ly & %Halg & % & Hsc & Hlb & Hcred & %r' & Hrfn & Hb)".
    simpl in Halg.
    iExists ly.
    iFrame. iFrame "%".
    iPoseProof (ty_own_val_sidecond with "Hv") as "#$".
    assert ((∃ ly1, st = UntypedSynType ly1 ∧ syn_type_has_layout (ty_syn_type ty) ly1 ∧ ty_has_op_type ty (UntypedOp ly1) MCCopy) ∨ (ty_has_op_type ty (use_op_alg' (ty_syn_type ty)) MCCopy ∧ ty_syn_type ty = st)) as Hb.
    { destruct st; eauto. }
    iSplitR. { iPureIntro. destruct Hb as [(ly1 & -> & ? & ?) | (? & <-)]; last done.
      apply syn_type_has_layout_untyped_inv in Halg as (-> & _). done. }
    iExists r. iSplitR; first done.
    iNext. iMod "Hb" as "(%v' & Hl & Hv')". iModIntro.
    iDestruct "Hrfn" as "<-".
    iExists v'. iFrame.
    iEval (rewrite /ty_own_val/=) in "Hv'".
    iDestruct "Hv'" as "(%ot & %Hot' & %Hmc & %Hv & ?)".
    destruct Hmc as [-> | [st' ->]]; first done.
    iApply (ty_memcast_compat_copy with "Hv").

    destruct Hb as [(ly1 & -> & Hst & ?) | (Hst & <-)].
    - injection Hot' as <-. done.
    - move: Hst. rewrite /use_op_alg' Hot' //.
  Qed.

  Lemma ofty_value_untyped_make_typed π l vs st ly wl :
    syn_type_has_layout st ly →
    (l ◁ₗ[π, Owned wl] #vs @ ◁ value_t (UntypedSynType ly)) -∗
    l ◁ₗ[π, Owned wl] #vs @ ◁ value_t st.
  Proof.
    iIntros (?) "Ha".
    iApply (ofty_mono_ly_strong_in with "[] [] Ha").
    - simpl. by eapply syn_type_has_layout_make_untyped.
    - done.
    - done.
    - done.
    - iIntros (?). by iApply value_untyped_make_typed.
    - simpl. eauto.
  Qed.

  Lemma ofty_uninit_to_value F π l st :
    lftE ⊆ F →
    (l ◁ₗ[π, Owned false] .@ ◁ (uninit st))%I ={F}=∗
    ∃ v, l ◁ₗ[π, Owned false] #v @ (◁ value_t st)%I.
  Proof.
    iIntros (?) "Ha".
    iPoseProof (ltype_own_has_layout with "Ha") as "(%ly & %Hst & %Hly)".
    simp_ltypes in Hst. simpl in Hst.
    iMod (ofty_own_split_value_untyped with "Ha") as "(%v & _ & Ha)"; [done.. | ].
    iExists v. by iApply (ofty_value_untyped_make_typed with "Ha").
  Qed.

  Lemma ofty_value_untyped_reduce_alignment π l vs ly1 ly2 :
    ly_size ly1 = ly_size ly2 →
    l `has_layout_loc` ly2 →
    layout_wf ly2 →
    (ly_align_in_bounds ly1 → ly_align_in_bounds ly2) →
    (l ◁ₗ[π, Owned false] vs @ ◁ value_t (UntypedSynType ly1)) -∗
    (l ◁ₗ[π, Owned false] vs @ ◁ value_t (UntypedSynType ly2)).
  Proof.
    iIntros (Hsz Halign ? Halmon) "Hl".
    iPoseProof (ltype_own_has_layout with "Hl") as "(%ly & %Halg & #_)".
    simp_ltypes in Halg. simpl in Halg.
    apply syn_type_has_layout_untyped_inv in Halg as (-> & Hwf1 & Hsz_le & Hal).
    iApply (ofty_mono_ly_strong with "[] [] Hl").
    + simpl. eapply syn_type_has_layout_untyped; done.
    + simpl. eapply syn_type_has_layout_untyped; first done.
      - done.
      - lia.
      - by apply Halmon.
    + done.
    + done.
    + iIntros (??). iApply value_untyped_layout_mono; [done.. | ]. eauto.
    + simpl. done.
  Qed.

  Lemma ofty_value_untyped_app_merge π l vs1 vs2 ly1 ly2 ly3 :
    l `has_layout_loc` ly3 →
    ly_size ly1 ≤ ly_size ly3 →
    ly_size ly2 = ly_size ly3 - ly_size ly1 →
    syn_type_has_layout (UntypedSynType ly3) ly3 →
    (l ◁ₗ[π, Owned false] #vs1 @ ◁ value_t (UntypedSynType ly1)) -∗
    ((l +ₗ ly_size ly1) ◁ₗ[π, Owned false] #vs2 @ ◁ value_t (UntypedSynType ly2)) -∗
    (l ◁ₗ[π, Owned false] #(vs1++vs2) @ ◁ value_t (UntypedSynType ly3)).
  Proof.
    iIntros (Hal Hsz Hlysz ?) "Hl1 Hl2".
    rewrite !ltype_own_ofty_unfold /lty_of_ty_own. simpl.
    iDestruct "Hl1" as "(%ly10 & %Hly1 & %Hly_l & _ & #Hlb1 & _ & %r' & -> & Hb1)".
    apply syn_type_has_layout_untyped_inv in Hly1 as (-> & _).
    iDestruct "Hl2" as "(%ly20 & %Hly2 & %Hly_l' & _ & #Hlb2 & _ & %r'' & -> & Hb2)".
    apply syn_type_has_layout_untyped_inv in Hly2 as (-> & _).
    iExists ly3. simpl. iR.
    iSplitR. { done. }
    iR.
    iSplitR. { iCombine "Hlb1 Hlb2" as "Hlb". rewrite loc_in_bounds_split_suf.
      rewrite {2}Hlysz.
      match goal with | |- context[(?m + (?n - ?m))] => replace (m + (n - m)) with n by lia end; done. }
    iSplitR; first done.
    iExists _. iSplitR; first done.
    iMod (fupd_mask_mono with "Hb1") as "(%v1 & Hl1 & Hv1)"; first done.
    iMod (fupd_mask_mono with "Hb2") as "(%v2 & Hl2 & Hv2)"; first done.
    iModIntro.
    iExists (v1 ++ v2).
    rewrite heap_mapsto_app. iFrame.
    iPoseProof (ty_has_layout with "Hv1") as "(%ly' & %Halg & %Hlyv)".
    apply syn_type_has_layout_untyped_inv in Halg as (-> & ? & ?).
    iSplitL "Hl2". { rewrite /has_layout_val in Hlyv. rewrite Hlyv. done. }
    iApply (value_untyped_app_merge with "Hv1 Hv2").
    - done.
    - rewrite Hlysz. lia.
  Qed.

  Lemma ofty_value_untyped_app_split F π l v1 v2 v3 ly1 ly2 ly3 :
    lftE ⊆ F →
    ly_align_log ly3 ≤ ly_align_log ly2 →
    ly_align_log ly2 ≤ ly_align_log ly1 →
    ly_size ly1 = ly_size ly2 + ly_size ly3 →
    v1 = v2 ++ v3 →
    length v2 = ly_size ly2 →
    layout_wf ly2 →
    layout_wf ly3 →
    ⊢ l ◁ₗ[π, Owned false] #v1 @ (◁ value_t (UntypedSynType ly1)) ={F}=∗
    l ◁ₗ[π, Owned false] #v2 @ (◁ value_t (UntypedSynType ly2)) ∗
    (l +ₗ ly_size ly2) ◁ₗ[π, Owned false] #v3 @ ◁ value_t (UntypedSynType ly3).
  Proof.
    iIntros (? Hal3 Hal2 Hsz -> Hszeq Hwf2 Hwf3) "Hl".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hl" as "(%ly & %Halg & %Hly & Hsc & Hlb & _ & %r' & <- & Hb)".
    iMod (fupd_mask_mono with "Hb") as "(%v & Hl & Hv)"; first done.
    specialize (syn_type_has_layout_untyped_inv _ _  Halg) as (-> & ? & ? &?).
    rewrite Hsz. rewrite -loc_in_bounds_split_suf. iDestruct "Hlb" as "(Hlb1 & Hlb2)".
    efeed pose proof (ly_align_in_bounds_mono ly1 ly2); [done.. | ].
    efeed pose proof (ly_align_in_bounds_mono ly1 ly3); [lia | done | ].
    iPoseProof (value_has_length with "Hv") as "(%Hlen1 & %Hlen2)"; first done.
    rewrite app_length in Hlen1.
    iPoseProof (value_untyped_app_split _ _ _ _ ly1 ly2 ly3 with "Hv") as "(Hv1 & Hv2)".
    { done. }
    { done. }
    { done. }
    { done. }
    { done. }
    { done. }
    (rewrite -{1}(take_drop (length v2) v)).
    rewrite heap_mapsto_app. iDestruct "Hl" as "(Hl1 & Hl2)".
    iSplitL "Hv1 Hl1 Hlb1".
    - iModIntro. rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iExists ly2. iSplitR. { iPureIntro. apply syn_type_has_layout_untyped; naive_solver lia. }
      iSplitR. { iPureIntro. eapply has_layout_loc_trans; first done. lia. }
      simpl. iR. iFrame. iR. iExists v2. iR.
      iModIntro. iExists _. iFrame.
    - iModIntro. rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iExists ly3. iSplitR. { iPureIntro. apply syn_type_has_layout_untyped; naive_solver lia. }
      iSplitR. { iPureIntro. apply has_layout_loc_shift_loc_nat.
        + eapply has_layout_loc_trans; first done. lia.
        + trans (ly_align ly2); first last. { rewrite -Nat2Z.divide//. }
          rewrite -Nat2Z.divide. apply Zdivide_nat_pow. done. }
      simpl. iR. iFrame. iExists v3. iR.
      iModIntro. iExists _. iFrame.
      rewrite take_length. rewrite Hszeq Nat.min_l; first done.
      lia.
  Qed.

  Lemma ofty_value_untyped_split_app_array F π l (n m k : nat) ly v1 :
    lftE ⊆ F →
    n = (m + k)%nat →
    layout_wf ly →
    l ◁ₗ[ π, Owned false] # v1 @ (◁ value_t (UntypedSynType (mk_array_layout ly n))) ={F}=∗
    l ◁ₗ[ π, Owned false] # (take (ly_size ly * k) v1) @ (◁ value_t (UntypedSynType (mk_array_layout ly k))) ∗
    (l offset{ly}ₗ k) ◁ₗ[ π, Owned false] # (drop (ly_size ly * k) v1) @ (◁ value_t (UntypedSynType (mk_array_layout ly m))).
  Proof.
    iIntros (? Hn ?).
    rewrite /offset_loc.
    rewrite -Nat2Z.inj_mul -{3}(ly_size_mk_array_layout k ly).
    iIntros "Hl".
    iPoseProof (ltype_own_has_layout with "Hl") as "(%lyv & %Hstly & %Hlyl)".
    simp_ltypes in Hstly. simpl in Hstly.
    iMod (ofty_value_has_length with "Hl") as "(%Hlen & Hl)"; [done.. | ].
    simpl in *.
    iApply (ofty_value_untyped_app_split with "Hl").
    - done.
    - simpl. lia.
    - simpl. lia.
    - simpl. rewrite !ly_size_mk_array_layout. lia.
    - rewrite take_drop//.
    - rewrite take_length. simpl.
      apply syn_type_has_layout_untyped_inv in Hstly as (-> & ? & ? & ?).
      rewrite Hlen !ly_size_mk_array_layout. lia.
    - by apply array_layout_wf.
    - by apply array_layout_wf.
  Qed.

  Lemma ofty_value_untyped_to_bytes π l vn ly :
    l ◁ₗ[π, Owned false] #vn @ (◁ value_t (UntypedSynType ly)) -∗
    l ◁ₗ[π, Owned false] #vn @ (◁ value_t (UntypedSynType $ mk_array_layout u8 (ly_size ly))).
  Proof.
    (* We can always go to something with a lower alignment *)
    iIntros "Hl". iPoseProof (ltype_own_has_layout with "Hl") as "(%ly' & %Halg & %Hly)".
    simp_ltypes in Halg. simpl in Halg.
    apply syn_type_has_layout_untyped_inv in Halg as (-> & ? & ?).
    iApply (ofty_value_untyped_reduce_alignment with "Hl").
    - rewrite /mk_array_layout/u8{2}/ly_size/=. lia.
    - rewrite /has_layout_loc/ly_align/mk_array_layout/u8/=.
      rewrite /aligned_to. destruct caesium_config.enforce_alignment; last done.
      apply Z.divide_1_l.
    - rewrite /layout_wf/ly_align/u8/=. apply Z.divide_1_l.
    - done.
  Qed.
End ofty_lemmas.

Global Hint Unfold value_t : tyunfold.
Global Typeclasses Opaque value_t.

(** ** value rules *)
Section rules.
  Context `{!typeGS Σ}.
  (** *** Rules converting other types to/from values*)
  (** NOTE: This needs to have lower priority than the below subsumption instances that specialize to the case where [ty = value_t _].
     In addition, other rules for other types should similarly be able to implement their own proof strategies.
     Namely, this rule makes a pretty strong commitment (having an exactly fitting value assignment available),
     so we should really try it as a last resort. So we give it a pretty low priority. *)

  (** By default, we go to UntypedSynType, and can later on specialize if needed by subsumption (we cannot go the other way around due to memcast compatibility) *)
  Lemma value_subsume_goal π {rt} (ty : type rt) (r : rt) v vs st T :
    (∃ ly, ⌜syn_type_has_layout ty.(ty_syn_type) ly⌝ ∗
      (v ◁ᵥ{π} r @ ty -∗ subsume (v ◁ᵥ{π} v @ value_t (UntypedSynType ly)) (v ◁ᵥ{π} vs @ value_t st) T))
    ⊢ subsume (v ◁ᵥ{π} r @ ty) (v ◁ᵥ{π} vs @ value_t st) T.
  Proof.
    iIntros "(%ly & %Halg & HT) Hv".
    iPoseProof (own_val_split_value _ _ _ _ (UntypedSynType _) with "Hv") as "(Hv' & Hv)".
    { split; first done. eapply syn_type_has_layout_make_untyped; done. }
    iApply ("HT" with "Hv Hv'").
  Qed.
  Global Instance value_subsume_goal_inst π {rt} (ty : type rt) (r : rt) v vs st :
    Subsume (v ◁ᵥ{π} r @ ty) (v ◁ᵥ{π} vs @ value_t st) | 50 :=
    λ T, i2p (value_subsume_goal π ty r v vs st T).

  (* TODO: this isn't ideal if v' is an evar -- then this currently will lead to evar instantiation failures, since we don't know the value yet.
     Maybe we want to have a type which encapsulates the existential quantifier in that case?
  *)
  Lemma value_subsume_full_goal_ofty π E L step {rt} l v' st (ty : type rt) r T:
    li_tactic (compute_layout_goal ty.(ty_syn_type)) (λ ly,
      (∀ v, v ◁ᵥ{π} r @ ty -∗
      subsume_full E L step (l ◁ₗ[π, Owned false] #v @ ◁ value_t (UntypedSynType ly)) (l ◁ₗ[π, Owned false] #v' @ ◁ (value_t st)) T))
    ⊢ subsume_full E L step (l ◁ₗ[π, Owned false] #r @ ◁ ty)
        (l ◁ₗ[π, Owned false] #v' @ ◁ (value_t st)) T.
  Proof.
    rewrite /compute_layout_goal.
    iIntros "(%ly & %Hst & HT)" (???) "#CTX #HE HL Hty".
    iMod (ofty_own_split_value_untyped with "Hty") as "(%v & Hv & Hty)"; [done.. | ].
    iDestruct ("HT" with "Hv") as "HT".
    by iApply ("HT" with "[//] [//] CTX HE HL").
  Qed.
  (* NOTE: not an instance due to the above issue *)
  (*Global Instance value_subsume_full_goal_ofty_inst π E L {rt} l v' st (ty : type rt) r :*)
    (*SubsumeFull E L (l ◁ₗ[π, Owned false] PlaceIn r @ ◁ ty)%I (l ◁ₗ[π, Owned false] PlaceIn v' @ ◁ (value_t st))%I | 50 :=*)
    (*λ T, i2p (value_subsume_full_goal_ofty π E L l v' st ty r T).*)

  (** When we require assembled ownership, try to assemble it. *)

  Lemma subsume_full_value_merge_ofty_untyped {rt} π E L (ty : type rt) r v l ly1 wl T :
    (prove_with_subtype E L false ProveDirect (v ◁ᵥ{π} r @ ty) (λ L' _ R,
      ⌜syn_type_has_layout ty.(ty_syn_type) ly1⌝ ∗ ⌜ty_has_op_type ty (UntypedOp ly1) MCCopy⌝ ∗ T L' R))
    ⊢ subsume_full E L false (l ◁ₗ[π, Owned wl] PlaceIn v @ ◁ value_t (UntypedSynType ly1)) (l ◁ₗ[π, Owned wl] PlaceIn r @ (◁ ty)) T.
  Proof.
    iIntros "HT".
    iIntros (???) "#CTX #HE HL Hl".
    iMod ("HT" with "[//] [//] CTX HE HL") as "(%L' & % & %R & >(Hv & HR) & HL & % & % & HT)".
    iPoseProof (ofty_own_merge_value with "Hv Hl") as "?"; first done.
    iModIntro. iExists L', R. iFrame. done.
  Qed.
  (* should have a lower priority than Lithium's id instance - in case the goal specifies that we want a value_t, we should not try to fiddle with that. *)
  Global Instance subsume_full_value_merge_ofty_untyped_inst {rt} π E L (ty : type rt) r v l ly1 wl :
    SubsumeFull E L false (l ◁ₗ[π, Owned wl] PlaceIn v @ ◁ value_t (UntypedSynType ly1))%I (l ◁ₗ[π, Owned wl] PlaceIn r @ (◁ ty))%I | 100 :=
    λ T, i2p (subsume_full_value_merge_ofty_untyped π E L ty r v l ly1 wl T).

  Lemma subsume_full_value_merge_ofty {rt} π E L (ty : type rt) r v l st wl T :
    (prove_with_subtype E L false ProveDirect (v ◁ᵥ{π} r @ ty) (λ L' _ R,
      ⌜ty_has_op_type ty (use_op_alg' ty.(ty_syn_type)) MCCopy⌝ ∗ ⌜ty_syn_type ty = st⌝ ∗ T L' R))
    ⊢ subsume_full E L false (l ◁ₗ[π, Owned wl] #v @ ◁ value_t st) (l ◁ₗ[π, Owned wl] #r @ (◁ ty)) T.
  Proof.
    iIntros "HT".
    iIntros (???) "#CTX #HE HL Hl". iPoseProof (ltype_own_has_layout with "Hl") as "(%ly' & %Hst & %)".
    iMod ("HT" with "[//] [//] CTX HE HL") as "(%L' & % & %R & >(Hv & HR) & HL & %Hc & %Ha & HT)".
    iModIntro. iExists L', R. iFrame.
    iApply (ofty_own_merge_value with "Hv Hl").
    destruct st; try done. simp_ltypes in Hst. simpl in Hst. rewrite Ha.
    specialize (syn_type_has_layout_untyped_inv _ _ Hst) as (-> & _).
    rewrite Ha in Hc. split; done.
  Qed.
  (* should have a lower priority than Lithium's id instance - in case the goal specifies that we want a value_t, we should not try to fiddle with that. *)
  Global Instance subsume_full_value_merge_ofty_inst {rt} π E L (ty : type rt) r v l st wl :
    SubsumeFull E L false (l ◁ₗ[π, Owned wl] PlaceIn v @ ◁ value_t st)%I (l ◁ₗ[π, Owned wl] PlaceIn r @ (◁ ty))%I | 101 :=
    λ T, i2p (subsume_full_value_merge_ofty π E L ty r v l st wl T).

  Lemma owned_subtype_value_merge {rt} π E L (ty : type rt) r v' st T :
    prove_with_subtype E L false ProveDirect (v' ◁ᵥ{π} r @ ty) (λ L' _ R,
      introduce_with_hooks E L' R (λ L2, ⌜ty_has_op_type ty (use_op_alg' ty.(ty_syn_type)) MCCopy⌝ ∗
      ⌜ty_syn_type ty = st⌝ ∗ T L2))
    ⊢ owned_subtype π E L false v' r (value_t st) (ty) T.
  Proof.
    iIntros "HT".
    iIntros (???) "#CTX #HE HL".
    iMod ("HT" with "[//] [//] CTX HE HL") as "(%L2 & %κs & %R & >(Hv' & HR) & HL & HT)".
    iMod ("HT" with "[//] HE HL HR") as "(%L3 & HL & %Hot & <- & HT)".
    iExists _. iFrame. iModIntro.
    iPoseProof (ty_own_val_sidecond with "Hv'") as "#$".
    iSplitR. { iPureIntro. simpl. iIntros (????). f_equiv. by eapply syn_type_has_layout_inj. }
    iSplitR; first by eauto.
    iIntros (v) "Hv".
    iEval (rewrite /ty_own_val/=) in "Hv".
    iDestruct "Hv" as "(%ot & %Hot' & %Hmc & %Hly & %Hst')".
    rewrite /use_op_alg' Hot'/= in Hot.
    destruct Hmc as [-> | (st & ->)]; first done.
    iApply (ty_memcast_compat_copy with "Hv'"). done.
  Qed.
  (* shouldn't have super high priority because the conclusion is very general *)
  Global Instance owned_subtype_value_merge_inst {rt} π E L (ty : type rt) r v' st :
    OwnedSubtype π E L false v' r (value_t st) (ty) | 100 :=
    λ T, i2p (owned_subtype_value_merge π E L ty r v' st T).
End rules.

Section unify_loc.
  Context `{!typeGS Σ}.
  (** Strategy for unifying two values:
     Step 1 (equalize st):
     - if goal st is evar, instantiate with same and proceed to 2
     - if goal st is given:
       + if current is Untyped and goal is Untyped, go to step 2
       + if current is Untyped and goal is something else, make goal Untyped
       + otherwise, require equality (TODO: not complete: we could also make a prefix here)

     Invariant after step 2: either st match, or both are Untyped.

     Step 2
     - if both are untyped:
        a) if both are using the same layout, done
        b) if both have the same size, require the goal's alignment to be lower, done
        c) otherwise (size also not equal), require current to be a prefix and continue with prove_with_subtype of the rest (startign at step 1 again); require goal's alignment to be lower
     - otherwise: require the values to be the same.
   *)

  (** Step 1 *)
  (* instantiate in case [st2] is an evar *)
  Lemma subsume_full_ofty_value_st_evar π E L step l st1 st2 vs1 vs2 T :
    ⌜st1 = st2⌝ ∗ subsume_full E L step (l ◁ₗ[π, Owned false] PlaceIn vs1 @ ◁ value_t st1)%I (l ◁ₗ[π, Owned false] PlaceIn vs2 @ ◁ value_t st1)%I T
    ⊢ subsume_full E L step (l ◁ₗ[π, Owned false] PlaceIn vs1 @ ◁ value_t st1) (l ◁ₗ[π, Owned false] PlaceIn vs2 @ ◁ value_t st2) T.
  Proof.
    iIntros "(-> & HT)". iApply "HT".
  Qed.
  Global Instance subsume_full_ofty_value_st_evar_inst π E L step l st1 st2 vs1 vs2 `{!IsProtected st2} :
    SubsumeFull E L step (l ◁ₗ[π, Owned false] PlaceIn vs1 @ ◁ value_t st1)%I (l ◁ₗ[π, Owned false] PlaceIn vs2 @ ◁ value_t st2)%I | 10 :=
    λ T, i2p (subsume_full_ofty_value_st_evar π E L step l st1 st2 vs1 vs2 T).

  (* in case st1 is Untyped, make the goal untyped, too *)
  Lemma subsume_full_ofty_value_st_untyped π E L step vs1 vs2 l st2 ly1 T :
    (li_tactic (compute_layout_goal st2) (λ ly2,
      subsume_full E L step (l ◁ₗ[π, Owned false] vs1 @ ◁ value_t (UntypedSynType ly1))%I
      (l ◁ₗ[π, Owned false] vs2 @ (◁ value_t (UntypedSynType ly2)))%I T))
    ⊢ subsume_full E L step (l ◁ₗ[π, Owned false] vs1 @ ◁ value_t (UntypedSynType ly1))
      (l ◁ₗ[π, Owned false] vs2 @ (◁ value_t st2)) T.
  Proof.
    rewrite /compute_layout_goal.
    iIntros "(%ly2 & %Halg & HT)".
    iIntros (F ??) "#CTX #HE HL Hl".
    iMod ("HT" with "[//] [//] CTX HE HL Hl") as "(%L' & %R2 & Hl & HL & HT)".
    iModIntro. iExists L', R2. iFrame.
    iApply (maybe_logical_step_wand with "[] Hl"). iIntros "(Hl & $)".
    iApply (ofty_mono_ly_strong with "[] [] Hl").
    - simpl. by eapply syn_type_has_layout_make_untyped.
    - done.
    - done.
    - done.
    - iIntros (v r) "Hv". rewrite /ty_own_val /=.
      iDestruct "Hv" as "(%ot & %Heq & %Hmc & %Hv & _)".
      injection Heq as <-. apply is_memcast_val_untyped_inv in Hmc as <-.
      specialize (syn_type_has_layout_op_alg _ _ Halg) as (ot & Hot & <-).
      iExists ot. iSplitR; first done. iSplitR. { by iLeft. }
      done.
    - simpl. done.
  Qed.
  Global Instance subsume_full_ofty_value_st_untyped_inst π E L step l ly1 st2 vs1 vs2 :
    SubsumeFull E L step (l ◁ₗ[π, Owned false] vs1 @ ◁ value_t (UntypedSynType ly1))%I (l ◁ₗ[π, Owned false] vs2 @ ◁ value_t st2)%I | 15 :=
    λ T, i2p (subsume_full_ofty_value_st_untyped π E L step vs1 vs2 l st2 ly1 T).

  (* if both of the above fail, require equality of the syntypes.
     TODO: this is too strict *)
  Lemma subsume_full_ofty_value_st_eq π E L step l vs1 vs2 st1 st2 T :
    ⌜st1 = st2⌝ ∗ subsume_full E L step (l ◁ₗ[π, Owned false] vs1 @ ◁ value_t st2)
      (l ◁ₗ[π, Owned false] vs2 @ ◁ value_t st2) T
    ⊢ subsume_full E L step (l ◁ₗ[π, Owned false] vs1 @ ◁ value_t st1)
      (l ◁ₗ[π, Owned false] vs2 @ ◁ value_t st2) T.
  Proof.
    iIntros "(-> & $)".
  Qed.
  Global Instance subsume_full_ofty_value_st_eq_inst π E L step l st1 st2 vs1 vs2 :
    SubsumeFull E L step (l ◁ₗ[π, Owned false] vs1 @ ◁ value_t st1)%I (l ◁ₗ[π, Owned false] vs2 @ ◁ value_t st2)%I | 20 :=
    λ T, i2p (subsume_full_ofty_value_st_eq π E L step l vs1 vs2 st1 st2 T).


  (** Step 2 *)

  (* if both are using the same st, unify the values *)
  Lemma subsume_full_ofty_value_unify_vs π E L step l vs1 vs2 st T :
    ⌜vs1 = vs2⌝ ∗ T L True%I
    ⊢ subsume_full E L step (l ◁ₗ[π, Owned false] #vs1 @ ◁ value_t st) (l ◁ₗ[π, Owned false] #vs2 @ ◁ value_t st) T.
  Proof.
    iIntros "(-> & HT)". iApply subsume_full_id. done.
  Qed.
  Global Instance subsume_full_ofty_value_unify_vs_inst π E L step l vs1 vs2 st :
    SubsumeFull E L step (l ◁ₗ[π, Owned false] #vs1 @ ◁ value_t st)%I (l ◁ₗ[π, Owned false] #vs2 @ ◁ value_t st)%I | 5 :=
    λ T, i2p (subsume_full_ofty_value_unify_vs π E L step l vs1 vs2 st T).


  (* if both are untyped, and have not been handled by the previous instance,
     check if the sizes of the layout are the same;
     - if so, fully subsume the values
     - else if the size of the first layout is smaller, prove that the left one is a prefix of the latter, and continue searching for the rest.
     - else, the goal refers to a subset of the current chunk and we split off. *)
  Lemma subsume_full_ofty_value_untyped_full π E L step l vs1 vs2 ly1 ly2 T `{!LayoutSizeEq ly1 ly2} :
    (⌜l `has_layout_loc` ly1⌝ -∗ ⌜ly_align_in_bounds ly1⌝ -∗ ⌜l `has_layout_loc` ly2⌝ ∗ ⌜vs1 = vs2⌝ ∗ ⌜ly_align_in_bounds ly2⌝ ∗ ⌜layout_wf ly2⌝ ∗ T L True%I)
    ⊢ subsume_full E L step (l ◁ₗ[π, Owned false] vs1 @ ◁ value_t (UntypedSynType ly1))
        (l ◁ₗ[π, Owned false] vs2 @ ◁ value_t (UntypedSynType ly2)) T.
  Proof.
    (*iIntros "(%Halign & -> & HT)".*)
    iIntros "HT".
    iIntros (F ??) "#CTX #HE HL Hl". iModIntro. iExists L, True%I. iFrame.
    iPoseProof (ltype_own_has_layout with "Hl") as "(%ly' & %Hly' & %Hlyl)". simp_ltypes in Hly'. simpl in *.
    apply syn_type_has_layout_untyped_inv in Hly' as (-> & ? & ? & ?).
    iPoseProof ("HT" with "[//] [//]") as "(% & -> & % & % & HT)".
    iPoseProof (ofty_value_untyped_reduce_alignment _ _ _ _ ly2 with "Hl") as "Hl".
    { done. }
    { done. }
    { done. }
    { done. }
    iFrame. iApply (maybe_logical_step_intro). iL. done.
  Qed.
  Global Instance subsume_full_ofty_value_untyped_full_inst π E L step l vs1 vs2 ly1 ly2 `{!LayoutSizeEq ly1 ly2} :
    SubsumeFull E L step (l ◁ₗ[π, Owned false] vs1 @ ◁ value_t (UntypedSynType ly1))%I (l ◁ₗ[π, Owned false] vs2 @ ◁ value_t (UntypedSynType ly2))%I | 6 :=
    λ T, i2p (subsume_full_ofty_value_untyped_full π E L step l vs1 vs2 ly1 ly2 T).


  (* Prove a prefix of the goal, and continue finding the rest of the ownership *)
  Lemma subsume_full_ofty_value_untyped_prefix π E L step l vs1 vs2 ly1 ly2 T `{!LayoutSizeLe ly1 ly2} :
    (⌜syn_type_has_layout (UntypedSynType ly2) ly2⌝ ∗
    (⌜l `has_layout_loc` ly1⌝ -∗
    ⌜l `has_layout_loc` ly2⌝ ∗
    ∃ vs2', ⌜vs2 = vs1 ++ vs2'⌝ ∗
    ∃ ly1', prove_with_subtype E L step ProveDirect ((l +ₗ ly_size ly1) ◁ₗ[π, Owned false] #vs2' @ ◁ value_t (UntypedSynType ly1'))
        (λ L2 _ R2, ⌜ly_size ly1' = ly_size ly2 - ly_size ly1⌝ ∗ T L2 R2)))
    ⊢ subsume_full E L step (l ◁ₗ[π, Owned false] #vs1 @ ◁ value_t (UntypedSynType ly1))
        (l ◁ₗ[π, Owned false] #vs2 @ ◁ value_t (UntypedSynType ly2)) T.
  Proof.
    iIntros "(%Hst & HT)".
    match goal with H : LayoutSizeLe _ _ |- _ => rewrite /LayoutSizeLe in H end.
    iIntros (F ??) "#CTX #HE HL Hl".
    iPoseProof (ltype_own_has_layout with "Hl") as "(%ly & %Halg & %Hal)".
    apply syn_type_has_layout_untyped_inv in Halg as (-> & ? & ?).
    iDestruct ("HT" with "[//]") as "(%Hal2 & %vs2' & -> & %ly1' & HT)".
    iMod ("HT" with "[//] [//] CTX HE HL") as "(%L' & % & %R2 & Hl' & HL & %Hsz & HT)".
    iExists _, R2. iFrame.
    iApply maybe_logical_step_fupd.
    iApply (maybe_logical_step_compose with "Hl'").
    iApply maybe_logical_step_intro.
    iIntros "!> (Hl' & $)".
    iPoseProof (ofty_value_untyped_app_merge with "Hl Hl'") as "$"; last done.
    - done.
    - done.
    - done.
    - done.
  Qed.
  Global Instance subsume_full_ofty_value_untyped_prefix_inst π E L step l vs1 vs2 ly1 ly2 `{!LayoutSizeLe ly1 ly2} :
    SubsumeFull E L step (l ◁ₗ[π, Owned false] #vs1 @ ◁ value_t (UntypedSynType ly1))%I (l ◁ₗ[π, Owned false] #vs2 @ ◁ value_t (UntypedSynType ly2))%I | 7 :=
    λ T, i2p (subsume_full_ofty_value_untyped_prefix π E L step l vs1 vs2 ly1 ly2 T).
End unify_loc.

Section unify_val.
  Context `{!typeGS Σ}.

  (** Same instances for the case that we have just values *)

  (** Step 1 *)
  (* instantiate in case [st2] is an evar *)
  Lemma subsume_full_value_st_evar E L step π v st1 st2 vs1 vs2 T :
    ⌜st1 = st2⌝ ∗ subsume_full E L step (v ◁ᵥ{π} vs1 @ value_t st1)%I (v ◁ᵥ{π} vs2 @ value_t st1)%I T
    ⊢ subsume_full E L step (v ◁ᵥ{π} vs1 @ value_t st1) (v ◁ᵥ{π} vs2 @ value_t st2) T.
  Proof.
    iIntros "(-> & HT)". iApply "HT".
  Qed.
  Global Instance subsume_full_value_st_evar_inst E L step π v st1 st2 vs1 vs2 `{!IsProtected st2} :
    SubsumeFull E L step (v ◁ᵥ{π} vs1 @ value_t st1)%I (v ◁ᵥ{π} vs2 @ value_t st2)%I | 10 :=
    λ T, i2p (subsume_full_value_st_evar E L step π v st1 st2 vs1 vs2 T).

  (* in case st1 is Untyped, make the goal untyped, too *)
  Lemma subsume_full_value_st_untyped E L step π vs1 vs2 v st2 ly1 T :
    (li_tactic (compute_layout_goal st2) (λ ly2, subsume_full E L step (v ◁ᵥ{π} vs1 @ value_t (UntypedSynType ly1))%I (v ◁ᵥ{π} vs2 @ (value_t (UntypedSynType ly2)))%I T))
    ⊢ subsume_full E L step (v ◁ᵥ{π} vs1 @ value_t (UntypedSynType ly1)) (v ◁ᵥ{π} vs2 @ (value_t st2)) T.
  Proof.
    rewrite /compute_layout_goal.
    iIntros "(%ly2 & %Halg & HT)".
    iIntros (???) "#CTX #HE HL Hv".
    iMod ("HT" with "[//] [//] CTX HE HL Hv") as "(%L2 & %R2 & Hv & ? & ?)".
    iExists L2, _. iFrame.
    iApply (maybe_logical_step_wand with "[] Hv").
    iIntros "(Hv & $)". iApply value_untyped_make_typed; done.
  Qed.
  Global Instance subsume_full_value_st_untyped_inst E L step π v ly1 st2 vs1 vs2 :
    SubsumeFull E L step (v ◁ᵥ{π} vs1 @ value_t (UntypedSynType ly1))%I (v ◁ᵥ{π} vs2 @ value_t st2)%I | 15 :=
    λ T, i2p (subsume_full_value_st_untyped E L step π vs1 vs2 v st2 ly1 T).

  (* if all of the above fail, require equality of the syntypes.
     TODO: this is too strict *)
  Lemma subsume_full_value_st_eq E L step π v vs1 vs2 st1 st2 T :
    ⌜st1 = st2⌝ ∗ subsume_full E L step (v ◁ᵥ{π} vs1 @ value_t st2) (v ◁ᵥ{π} vs2 @ value_t st2) T
    ⊢ subsume_full E L step (v ◁ᵥ{π} vs1 @ value_t st1) (v ◁ᵥ{π} vs2 @ value_t st2) T.
  Proof.
    iIntros "(-> & $)".
  Qed.
  Global Instance subsume_full_value_st_eq_inst E L step π v st1 st2 vs1 vs2 :
    SubsumeFull E L step (v ◁ᵥ{π} vs1 @ value_t st1)%I (v ◁ᵥ{π} vs2 @ value_t st2)%I | 20 :=
    λ T, i2p (subsume_full_value_st_eq E L step π v vs1 vs2 st1 st2 T).

  (* TODO: one thing that definitely needs to work:
      value_t (UntypedOp ly) <: value_t st when st_has_layout st ly
   *)

  (** Step 2 *)
  (* for untyped, require compatibility of the layouts *)
  Lemma subsume_full_value_untyped_full π E L step v vs1 vs2 ly1 ly2 T `{!LayoutSizeEq ly1 ly2} :
    ⌜ly_align_log ly2 ≤ ly_align_log ly1⌝ ∗ ⌜vs1 = vs2⌝ ∗ T L True%I
    ⊢ subsume_full E L step (v ◁ᵥ{π} vs1 @ value_t (UntypedSynType ly1)) (v ◁ᵥ{π} vs2 @ value_t (UntypedSynType ly2)) T.
  Proof.
    iIntros "(%Hal & -> & HT)".
    iIntros (???) "#CTX #HE HL Hv".
    iExists _, _. iFrame.
    iApply maybe_logical_step_intro. iL.
    iApply value_untyped_layout_mono; last done.
    - done.
    - intros. by eapply layout_wf_mono.
    - intros. by eapply ly_align_in_bounds_mono.
  Qed.
  (* NOTE: needs to be higher-priority than [subsume_full_value_st_untyped] in order to prevent divergence *)
  Global Instance subsume_full_value_untyped_full_inst π E L step v vs1 vs2 ly1 ly2 `{!LayoutSizeEq ly1 ly2} :
    SubsumeFull E L step (v ◁ᵥ{π} vs1 @ value_t (UntypedSynType ly1))%I (v ◁ᵥ{π} vs2 @ value_t (UntypedSynType ly2))%I | 6 :=
    λ T, i2p (subsume_full_value_untyped_full π E L step v vs1 vs2 ly1 ly2 T).

  (* if both are using the same st, unify the values *)
  Lemma subsume_full_value_unify_vs E L step π v vs1 vs2 st T :
    ⌜vs1 = vs2⌝ ∗ T L True%I
    ⊢ subsume_full E L step (v ◁ᵥ{π} vs1 @ value_t st) (v ◁ᵥ{π} vs2 @ value_t st) T.
  Proof.
    iIntros "(-> & HT)". iApply subsume_full_id. done.
  Qed.
  Global Instance subsume_full_value_unify_vs_inst E L step π v vs1 vs2 st :
    SubsumeFull E L step (v ◁ᵥ{π} vs1 @ value_t st)%I (v ◁ᵥ{π} vs2 @ value_t st)%I | 5 :=
    λ T, i2p (subsume_full_value_unify_vs E L step π v vs1 vs2 st T).

  (* TODO prefix /suffix *)
End unify_val.

Section rules.
  Context `{!typeGS Σ}.

  (* Read instance that leaves uninit on moves.
     TODO: Ideally, we would like to leave a value instead to not loose information.
      The lemmas below explore this, but currently do not work. *)
  Lemma type_read_ofty_move_owned E L {rt} π (T : typed_read_end_cont_t rt) l (ty : type rt) r ot wl bmin :
    (⌜ty_has_op_type ty ot MCCopy⌝ ∗
        ∀ v, T L v _ ty r unit (◁ uninit ty.(ty_syn_type)) (#()) ResultStrong)
    ⊢ typed_read_end π E L l (◁ ty) (#r) (Owned wl) bmin AllowStrong ot T.
  Proof.
    iIntros "(%Hot & Hs)" (F ???) "#CTX #HE HL Hna".
    iIntros "_ Hb".
    iPoseProof (ofty_ltype_acc_owned with "Hb") as "(%ly' & %Halg & %Hly & Hsc & Hlb & >(%v & Hl & Hv & Hcl))"; first done.
    iPoseProof (ty_own_val_has_layout with "Hv") as "%Hlyv"; first done.
    specialize (ty_op_type_stable Hot) as Halg''.
    assert (ly' = ot_layout ot) as ->. { by eapply syn_type_has_layout_inj. }
    iModIntro. iExists _, _, rt, _, _.
    iFrame "Hl Hv".
    iSplitR; first done. iSplitR; first done.
    iApply (logical_step_wand with "Hcl").
    iIntros "Hcl %st Hl Hv". iMod ("Hcl" $! v _ (uninit ty.(ty_syn_type)) tt with "Hl [//] [] []") as "Hl".
    { simpl. done. }
    { iNext. iApply uninit_own_spec. iExists _. iSplitR; first done. done. }
    iPoseProof (ty_memcast_compat with "Hv") as "Hid"; first done. simpl.
    iModIntro. iExists _, _,_, _. iFrame.
    (* strong update *)
    iExists _, _, _, ResultStrong. iFrame.
    iSplitR; first done.
    iR.
    done.
  Qed.
  Global Instance type_read_ofty_move_owned_inst E L {rt} π wl bmin l (ty : type rt) r ot :
    TypedReadEnd π E L l (◁ ty)%I (PlaceIn r) (Owned wl) bmin AllowStrong (ot) | 20 :=
    λ T, i2p (type_read_ofty_move_owned E L π T l ty r ot wl bmin).

  (* We also have a corresponding rule for Uniq ownership that leaves [Opened].
    This allows us to move out of mutable references, as long as another object is moved in at a later point. *)
  (* TODO also move value out here. *)
  Lemma type_read_ofty_move_uniq E L {rt} π (T : typed_read_end_cont_t rt) l (ty : type rt) r ot κ γ bmin :
    (li_tactic (lctx_lft_alive_count_goal E L κ) (λ '(κs, L2),
      ⌜ty_has_op_type ty ot MCCopy⌝ ∗
        ∀ v, T L2 v _ ty r unit (OpenedLtype (◁ uninit ty.(ty_syn_type)) (◁ ty) (◁ ty) (λ r1 r2, ⌜r1 = r2⌝) (λ _ _, llft_elt_toks κs)) (#()) ResultStrong))
    ⊢ typed_read_end π E L l (◁ ty) (#r) (Uniq κ γ) bmin AllowStrong ot T.
  Proof.
    iIntros "HT" (F ???) "#CTX #HE HL Hna".
    rewrite /lctx_lft_alive_count_goal.
    iDestruct "HT" as (κs L2) "(%Hal & %Hot & HT)".
    iIntros "Hincl0 Hb".

    iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
    iMod (lctx_lft_alive_count_tok with "HE HL") as (q) "(Htok & Hcl_tok & HL)"; [done.. | ].
    iPoseProof (ofty_ltype_acc_uniq with "CTX Htok Hcl_tok Hb") as "(%ly & %Halg & %Hly & Hlb & >(%v & Hl & Hv & Hcl))"; first done.
    iPoseProof (ty_own_val_has_layout with "Hv") as "%Hlyv"; first done.
    specialize (ty_op_type_stable Hot) as Halg''.
    assert (ly = ot_layout ot) as ->. { by eapply syn_type_has_layout_inj. }
    iMod "Hcl_F" as "_".
    iModIntro. iExists _, _, rt, _, _.
    iFrame "Hl Hv".
    do 2 iR.
    iApply (logical_step_mask_mono lftE); first done.
    iApply (logical_step_wand with "Hcl").
    iIntros "[_ Hcl] %st Hl Hv".
    iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
    iMod ("Hcl" $! v _ (uninit ty.(ty_syn_type)) tt with "Hl [] [] [//]") as "Hl".
    { simpl. done. }
    { iApply uninit_own_spec. iExists _. iSplitR; first done. done. }
    iPoseProof (ty_memcast_compat _ _ _ _ st with "Hv") as "Hid"; first done. simpl.
    iMod "Hcl_F" as "_".
    iModIntro. iExists _, _,_, _. iFrame.
    (* strong update *)
    iExists _, _, _, ResultStrong. iFrame.
    iSplitR; first done.
    iR.
    done.
  Qed.
  Global Instance type_read_ofty_move_uniq_inst E L {rt} π κ γ bmin l (ty : type rt) r ot :
    TypedReadEnd π E L l (◁ ty)%I (#r) (Uniq κ γ) bmin AllowStrong ot | 20 :=
    λ T, i2p (type_read_ofty_move_uniq E L π T l ty r ot κ γ bmin).

  (* [type_read_end] instance that does a move -- should be triggered when the copy instance does not work, hence the lower priority.
     This leaves a [value_t] at the place. *)
  Lemma type_read_ofty_move_owned_value E L {rt} π (T : typed_read_end_cont_t rt) l (ty : type rt) r ot wl bmin :
    ( ⌜use_op_alg (ty_syn_type ty) = Some ot⌝ ∗ (* TODO too strong, should also allow Untyped *)
    (* TODO for some reason, [simpl] will even unfold [ty_has_op_type] here... this breaks automation ofc *)
      (*⌜ty_allows_reads ty⌝ ∗*)
      ⌜ty_has_op_type ty (use_op_alg' (ty_syn_type ty)) MCCopy⌝ ∗
      (*⌜ty.(ty_has_op_type) ot MCCopy⌝ ∗*)
      ∀ v v', v ◁ᵥ{π} r @ ty -∗
      T L v' _ (value_t ty.(ty_syn_type)) v val (◁ value_t ty.(ty_syn_type)) (#v) ResultStrong)
    ⊢ typed_read_end π E L l (◁ ty) (#r) (Owned wl) bmin AllowStrong ot T.
  Proof.
    iIntros "(%Hotalg & %Hot & Hs)" (F ???) "#CTX #HE HL Hna".
    iIntros "_ Hb".
    iPoseProof (ofty_ltype_acc_owned with "Hb") as "(%ly & %Halg & %Hly & Hsc & Hlb & >(%v & Hl & Hv & Hcl))"; first done.
    iPoseProof (ty_own_val_has_layout with "Hv") as "%Hlyv"; first done.
    specialize (ty_op_type_stable Hot) as Halg''.
    rewrite /use_op_alg' Hotalg in Halg''.
    assert (ly = ot_layout ot) as ->. { by eapply syn_type_has_layout_inj. }
    iModIntro. iExists _, _, rt, _, _.
    iFrame "Hl Hv".
    iSplitR; first done. iSplitR; first done.
    iApply (logical_step_wand with "Hcl").
    iIntros "Hcl %st Hl Hv".
    iAssert (v ◁ᵥ{π} v @ value_t ty.(ty_syn_type))%I as "Hv'".
    { rewrite /ty_own_val/=.
      (*destruct (syn_type_has_layout_op_alg _ _ Halg) as (ot' & Hop & Hot').*)
      iExists (ot).
      iR. iSplitR. { iPureIntro. left. done. }
      iSplitR; last done. iPureIntro. rewrite /has_layout_val . done. }
    iPoseProof (ty_memcast_compat_copy _ _ _ ot _ st with "Hv'") as "Hv''".
    { rewrite ty_has_op_type_unfold. exists ot. split_and!; first done; last done. by apply is_value_ot_core_refl. }
    iMod ("Hcl" $! v _ (value_t ty.(ty_syn_type)) (v) with "Hl [//] [] []") as "Hl".
    { simpl. done. }
    { iNext. done. }
    (*iPoseProof (ty_memcast_compat with "Hv") as "Hid"; first done. simpl.*)
    iModIntro. iExists _, _, (value_t (ty_syn_type ty)), _. iFrame "∗ #".
    (* strong update *)
    iExists _, _, _, ResultStrong. iFrame.
    do 2 iR.
    iApply "Hs". done.
  Qed.
  (* TODO replace the preceding instances with this, once we have fixed:
      (a) owned_subtype to be able to move stuff into it again reliably, also below structs etc.
      (b) the model to allow syntype updates as long as the layout stays the same *)
  (*Global Instance type_read_ofty_move_owned_inst E L {rt} π wl bmin l (ty : type rt) r ot :*)
    (*TypedReadEnd π E L l (◁ ty)%I (PlaceIn r) (Owned wl) bmin AllowStrong ot | 19 :=*)
    (*λ T, i2p (type_read_ofty_move_owned E L π T l ty r ot wl bmin).*)

  (* TODO for Untyped, we currently cannot leave a value, because we cannot do syntype updates, but [value_t] relies on the syntype to compute the value update *)
  Lemma type_read_ofty_move_owned_untyped E L {rt} π (T : typed_read_end_cont_t rt) l (ty : type rt) r ly wl bmin :
    ( ⌜ty_has_op_type ty (UntypedOp ly) MCCopy⌝ ∗
      ∀ v v', v ◁ᵥ{π} r @ ty -∗
      T L v' _ (value_t (UntypedSynType ly)) v val (◁ value_t (UntypedSynType ly)) (#v) ResultStrong) -∗
      typed_read_end π E L l (◁ ty) (#r) (Owned wl) bmin AllowStrong (UntypedOp ly) T.
  Proof.
    iIntros "(%Hot & Hs)" (F ???) "#CTX #HE HL".
    iIntros "_ Hb".
  Abort.

  (* Instead we leave uninit *)
  Lemma type_read_ofty_move_owned_value_untyped E L {rt} π (T : typed_read_end_cont_t rt) l (ty : type rt) r ly wl bmin :
    (⌜ty_has_op_type ty (UntypedOp ly) MCCopy⌝ ∗
        ∀ v, T L v _ ty r unit (◁ uninit ty.(ty_syn_type)) (#()) ResultStrong)
    ⊢ typed_read_end π E L l (◁ ty) (#r) (Owned wl) bmin AllowStrong (UntypedOp ly) T.
  Proof.
    iIntros "(%Hot & Hs)" (F ???) "#CTX #HE HL Hna".
    iIntros "_ Hb".
    iPoseProof (ofty_ltype_acc_owned with "Hb") as "(%ly' & %Halg & %Hly & Hsc & Hlb & >(%v & Hl & Hv & Hcl))"; first done.
    iPoseProof (ty_own_val_has_layout with "Hv") as "%Hlyv"; first done.
    specialize (ty_op_type_stable Hot) as Halg''.
    assert (ly' = ly) as ->. { by eapply syn_type_has_layout_inj. }
    iModIntro. iExists _, _, rt, _, _.
    iFrame "Hl Hv".
    iSplitR; first done. iSplitR; first done.
    iApply (logical_step_wand with "Hcl").
    iIntros "Hcl %st Hl Hv". iMod ("Hcl" $! v _ (uninit ty.(ty_syn_type)) tt with "Hl [//] [] []") as "Hl".
    { simpl. done. }
    { iNext. iApply uninit_own_spec. iExists _. iSplitR; first done. done. }
    iPoseProof (ty_memcast_compat with "Hv") as "Hid"; first done. simpl.
    iModIntro. iExists _, _,_, _. iFrame.
    (* strong update *)
    iExists _, _, _, ResultStrong. iFrame.
    iSplitR; first done.
    iR.
    done.
  Qed.
  (*
  Global Instance type_read_ofty_move_owned_untyped_inst E L {rt} π wl bmin l (ty : type rt) r ly :
    TypedReadEnd π E L l (◁ ty)%I (PlaceIn r) (Owned wl) bmin AllowStrong (UntypedOp ly) | 20 :=
    λ T, i2p (type_read_ofty_move_owned_untyped E L π T l ty r ly wl bmin).
  *)

  (* TODO: this is now problematic. Maybe should have an untyped bit in the syntype after all?
       Alternative: use syn_type_compat everywhere to allow untyped interaction.

       Use an untyped bit:
       - then we still have a problem that often we should maybe be talking about a concrete layout instead.
          In particular when we assemble chunks.
          For array, we can work around that, since it is "chunkable", but for everything else, that does not really work.
          Q: do we reallyneed that for anything but arrays?
          + when we want to have a view on data and change the element type: e.g. in copy_nonoverlapping, would like to have an array of u8.
            We could in principle also do that for the ArraySynType, but it would be more of a hassle, and we would again end up with a different syntype
            OTOH is copy_nonoverlapping that much of a concern?
            In principle, we could also have something that first adapts
       - making things untyped would be much less of a hassle in the rules.

       Make rules compatible with UntypedSynType everywhere:
       - what is the intuitive justification for this? Why should we do it?
         + to my mind, UntypedSynType is just an undesirable artifact -- at least in safe Rust.
         + for unsafe stuff, the story may be different. We may want to treat stuff just as bytes.
            - allocation API itself should maybe treat it that way. We should just have some layout there.
              In our system, we will have a mixed concrete-symbolic layout.
              Arguably, that should not be a proper syntype, but that's how it is: our types need a syntype, and generally that requirement seems sensible.

       Alternative for this particular issue:
       - at the place, just don't leave an Untyped, but the right type. We should not loose information there!
         Then we also do not need a syntype update.

     *)

  (* TODO: consider whether we need special instances for reading/writing.
     In particular, what if we read with an ot from an UntypedOp-value? Then we should specialize the ot further in the result of the read.
     - problem currently: the generic ofty instance requires the type to have the same ot
     - but in case of value_t, we can change the ot!
   *)



  (* We also need stratification instances: should we generally move values back in during stratification?
    - One option: always cancel value_t in stratification.
        This limits expressivity a bit for specs, because when we really want to have value_t there, we get stuck.
      => do this for now, it should suffice.
     - Other option: have a (non-semantic) guidance parameter that gets provided by OpenedLtype.
       Only if that guidance parameter is not giving us identity do we fold the value_t.
     - Other option: do not let stratify do this, but rather have subtyping do this before folding.

     TODO: currently not an instance, because we sometimes do not want to do this!
     Instead, should give stratify some syntactic guidance from OpenedLtype above it.
   *)
  Lemma stratify_ltype_ofty_value_owned π E L mu mdu ma {M} (m : M) l st v wl (T : stratify_ltype_cont_t) :
    find_in_context (FindVal v π) (λ '(existT rt (ty', r')),
      ⌜ty_has_op_type ty' (use_op_alg' ty'.(ty_syn_type)) MCCopy⌝ ∗
      ⌜ty'.(ty_syn_type) = st⌝ ∗
      stratify_ltype π E L mu mdu ma m l (◁ ty') (#r') (Owned wl) T)
    ⊢ stratify_ltype π E L mu mdu ma m l (◁ value_t st)%I (#v) (Owned wl) T.
  Proof.
    iDestruct 1 as ([rt [ty' r']]) "(Hv & %Hot & %Heq & HT)" => /=.
    iIntros (???) "#CTX #HE HL Hl".
    iPoseProof (ltype_own_has_layout with "Hl") as "#(%ly & %Hst &_)".
    iPoseProof (ofty_own_merge_value with "Hv Hl") as "Ha".
    { subst st. destruct (ty_syn_type ty'); try done.
      simp_ltypes in Hst. simpl in Hst.
      specialize (syn_type_has_layout_untyped_inv _ _ Hst) as (-> & _).
      done. }
    iMod ("HT" with "[//] [//] CTX HE HL Ha") as "Ha".
    subst st. eauto.
  Qed.
  (* needs to have a higher priority than the ofty_resolve_ghost instance *)
  (*Global Instance stratify_ltype_unblock_ofty_value_owned_inst π E L mu mdu ma l st v wl :*)
    (*StratifyLtype π E L mu mdu ma StratifyUnblockOp l (◁ value_t st)%I (PlaceIn v) (Owned wl) | 10:=*)
    (*λ T, i2p (stratify_ltype_ofty_value_owned π E L mu mdu ma StratifyUnblockOp l st v wl T).*)
  (* TODO: not an instance right now since we don't always want to stratify this -- esp. not for functions passing values in their interface *)


  (* Simplification instance - when introducing a value_t, we simply destruct it *)
  (* TODO how does this overlap with ghost_drop?
     TODO can we simplify the is_memcast_val? Otherwise, it seems pretty useless. *)
  (*
  Lemma value_simplify π v T ot st p :
    (⌜is_memcast_val p ot v⌝ -∗ ⌜v `has_layout_val` ot_layout ot⌝ -∗ ⌜syn_type_has_layout st (ot_layout ot)⌝ -∗ T) -∗
    simplify_hyp (v ◁ᵥ{π} p @ value_t st)%I T.
  Proof. iIntros "HT (% & % & %)". by iApply "HT". Qed.
  Global Instance value_simplify_inst π v ot st p :
    SimplifyHypVal v π (value_t ot st) p (Some 0%N) :=
    λ T, i2p (value_simplify π v T ot st p).
   *)



End rules.

Global Typeclasses Opaque value_t.
