From refinedrust Require Export type ltypes.
From refinedrust Require Import ltype_rules.
From refinedrust Require Import uninit_def int.
From refinedrust Require Import uninit value alias_ptr programs.
Set Default Proof Using "Type".

(** Design decisions:
  - our array's refinements are homogeneously typed.
    TODO: check in future if we maybe should switch to option refinements for uninit
  - we have a fixed capacity -- otherwise, we cannot define the syntype (it would be a dynamically sized type..)
  - the array does not own its deallocation permission -- because its value form is not a pointer type.
  - it is refined by a list (homogeneous), similarly for the ltype. (we could also refine the ltype by a vec - but that would make everything more complicated)
*)
(* How do we get the Rust type [T; n] as a derived form?
   - want that it unfolds to the same place type at least. It's fine if the type specifies some additional invariants, as long as the place type can accomodate them.
   - the array ltype needs to be heterogeneous in the child ltypes, so it's got a list of child ltypes -- this enables us to get folding equations with [T; n]

  What does this mean for initialization?
  - we cannot partially initialize an array, or move some components out of it, even individually.
    + is this a problem for drop?
      => Yes. Dropping will drop all elements in sequence, so I need a representation of the intermediate state.
      => This is not a problem for the Vec use case, but if we want to support proper Rust arrays, we cannot get around it.
        TODO
    + we cannot do strong accesses below arrays.
      We can however at least do borrows. And we should be able to show that imp_unblockable lifts to arrays.
   This seems excessively restrictive.
   For now (just for doing Vec) it seems fine however.

  How do we deal with the restricted form of updates allowed below arrays?
  - we cannot unfold invariants below, at least not directly. We can first borrow to enable that.
  - how do we express that in terms of constraints? we just do not allow a strong update vs. i.e., we probably also need to make that one optional.
    That is a rather artificial limitation and an annoying break with the rest of the typesystem.
  - Note that it would be rather more desirable if I would not have to introduce a new place type for that, given that this is a really specialized type for the concrete vec use case.
    Basically, I don't want to have to go through the trouble of having a new place type if I don't need very fine-grained tracking of borrows.
    Can I phrase it like that?
    + option 1: would need ofty-based typing rules where I do not fully evaluate the place.
      - potentially: also hand out a remaining place context to the base judgment, in case we do not have a suitable unfolding rule.
      - then: can add new read/write/borrow _end rules for our new type specifying suitable place context.
        one quite big departure: we need a wp in the place_end rules.
        maybe restrict the set of place contexts allowed here.
      => this seems like it could work, although it too is not a very principles approach.
    + option 2: have a custom place rule for that that goes from an ofty (array ty len) to an ofty (ty)
      this basically shortcuts the ltype part.
      * When we do a shared borrow: get shared borrow; BUT: the whole place context handling is not really prepared for that.
      + same for mutable borrows, I can't really phrase it in terms of the place contexts.
      => this does not really seem to be implementable, as it does not fit in our current framework.

   In general, one could even make this case for ArrayLtype in general: rust's bororw checker does not support precise tracking of borrows below, so we could also make a case that we don't need this here.
      Only issue: other cases where we want to be able to do funky stuff below arrays, e.g. unfolding invariants -- these we fundamentally cannot just collapse into actions on an ofty because something interesting happens on the types below the array.
   Maybe: this kind of argument is not a good kind of argument, since we even need to handle the cases that in Rust would be unsafe, or are (in case of invariants/functional properties) not expressible in the Rust type system. For the former, this in particular applies to drop handling, and this is the reason why we should have a proper ltype.

   One other point: if I want to implement iterMut properly, I will likely also need this fine-grained control, because that is what happens internally - in unsafe code.

   Is this such a frequently occurring case that it warrants support for that in the judgments?
   Are cases where this occurrs not rather cases indicating that our current type system is not complete enough?
  *)


  (*
       coericing ArrayLtype to uninit?
        if we have a fully concrete array, it's the same.
       difficulty compared to struct: what happens for symbolic arrays (e.g. an insert with Blocked)?

      Can we develop some generally useful theory for reasoning about symbolic arrays?
      TODO
   *)




(* TODO: should we also have an ArrayOp that reads the array elements at an op that is valid for the element types? *)
Definition is_array_ot `{!typeGS Σ} {rt} (ty : type rt) (len : nat) (ot : op_type) (mt : memcast_compat_type) : Prop :=
  match ot with
  | UntypedOp ly =>
      ∃ ly', ly = mk_array_layout ly' len ∧ ty.(ty_has_op_type) (UntypedOp ly') mt ∧
        (* required for offsetting with LLVM's GEP *)
        (ly_size ly ≤ max_int isize_t)%Z ∧
        (* enforced by Rust *)
        layout_wf ly'
  | _ => False
  end.
Global Typeclasses Opaque is_array_ot.

Section array.
  Context `{!typeGS Σ}.
  Context {rt : Type}.



  Program Definition array_t (ty : type rt) (len : nat) : type (list (place_rfn rt)) := {|
    ty_own_val π r v :=
      ∃ ly,
        ⌜syn_type_has_layout ty.(ty_syn_type) ly⌝ ∗
        ⌜(ly_size ly * len ≤ max_int isize_t)%Z⌝ ∗
        ⌜length r = len⌝ ∗
        ⌜v `has_layout_val` (mk_array_layout ly len)⌝ ∗
        [∗ list] r'; v' ∈ r; reshape (replicate len (ly_size ly)) v,
          ∃ r'', place_rfn_interp_owned r' r'' ∗ ty.(ty_own_val) π r'' v';
    ty_shr κ π r l :=
      ∃ ly,
        ⌜syn_type_has_layout ty.(ty_syn_type) ly⌝ ∗
        ⌜(ly_size ly * len ≤ max_int isize_t)%Z⌝ ∗
        ⌜length r = len⌝ ∗
        ⌜l `has_layout_loc` ly⌝ ∗
        [∗ list] i ↦ r' ∈ r,
          ∃ r'', place_rfn_interp_shared r' r'' ∗ ty.(ty_shr) κ π r'' (offset_loc l ly i);
    ty_syn_type := ArraySynType ty.(ty_syn_type) len;
    ty_has_op_type := is_array_ot ty len;
    ty_sidecond := True;
    ty_ghost_drop π r :=
      [∗ list] r' ∈ r, match r' with | #r'' => ty.(ty_ghost_drop) π r'' | _ => True end;
    ty_lfts := ty.(ty_lfts);
    ty_wf_E := ty.(ty_wf_E);
  |}%I.
  Next Obligation.
    iIntros (ty len π r v) "(%ly & %Hst & %Hsz & %Hlen & %Hly & Hv)".
    iExists _.
    iSplitR. { iPureIntro. eapply syn_type_has_layout_array; done. }
    done.
  Qed.
  Next Obligation.
    iIntros (ty len ot mt Hot).
    destruct ot; try done.
    destruct Hot as (ly' & -> & Hot & Hsz & Hwf).
    eapply ty_op_type_stable in Hot.
    eapply syn_type_has_layout_array.
    - done.
    - done.
    - rewrite /ly_size /mk_array_layout in Hsz. simpl in Hsz. lia.
  Qed.
  Next Obligation.
    iIntros (ty len π r v) "_". done.
  Qed.
  Next Obligation.
    iIntros (ty len κ π l r) "(%ly & %Hst & %Hsz & %Hlen & %Hly & Hv)".
    iExists (mk_array_layout ly len). iSplitR; first done.
    iPureIntro. by eapply syn_type_has_layout_array.
  Qed.
  Next Obligation.
    iIntros (ty len E κ l ly π r q ?).
    iIntros "#(LFT & TIME & LCTX) Htok %Hst %Hly #Hlb Hb".
    rewrite -lft_tok_sep. iDestruct "Htok" as "(Htok & Htok')".
    iApply fupd_logical_step.
    (* reshape the borrow - we must not freeze the existential over v to initiate recursive sharing *)
    iPoseProof (bor_iff _ _ (∃ ly', ⌜syn_type_has_layout (ty_syn_type ty) ly'⌝ ∗ ⌜(ly_size ly' * len ≤ max_int isize_t)%Z⌝ ∗  ⌜length r = len⌝ ∗
      [∗ list] i ↦ r' ∈ r, ∃ v r'', (l offset{ly'}ₗ i) ↦ v ∗ place_rfn_interp_owned r' r'' ∗ ty.(ty_own_val) π r'' v)%I with "[] Hb") as "Hb".
    { iNext. iModIntro. iSplit.
      - iIntros "(%v & Hl & %ly' & %Hst' & %Hsz & %Hlen & %Hv & Hv)".
        iExists ly'. iSplitR; first done. iSplitR; first done. iSplitR; first done.
        subst len. clear -Hv.
        set (szs := replicate (length r) (ly_size ly')).
        assert (length r = length (reshape szs v)).
        { subst szs. rewrite reshape_length replicate_length //. }
        rewrite -{1}(join_reshape szs v); first last.
        { rewrite sum_list_replicate. rewrite Hv /mk_array_layout /ly_mult {2}/ly_size. lia. }
        rewrite (heap_mapsto_mjoin_uniform _ _ (ly_size ly')); first last.
        { subst szs. intros v'.
          intros ?%reshape_replicate_elem_length; first done.
          rewrite Hv. rewrite {1}/ly_size /mk_array_layout /=. lia. }
        iDestruct "Hl" as "(_ & Hl)".
        iAssert ([∗ list] i ↦ r'; v' ∈ r; reshape szs v, (l +ₗ ly_size ly' * i) ↦ v')%I with "[Hl]" as "Hl".
        { iApply big_sepL2_const_sepL_r. iSplit; done. }
        iPoseProof (big_sepL2_sep with "[$Hv $Hl]") as "Hl".
        iPoseProof (big_sepL2_wand _ (λ i r _, ∃ v' r'', (l offset{ly'}ₗ i) ↦ v' ∗ place_rfn_interp_owned r r'' ∗ v' ◁ᵥ{π} r'' @ ty)%I with "Hl []") as "Hl".
        { iApply big_sepL2_intro; first done. iIntros "!>" (k ? ? _ _) "((% & ? &Hv) & Hl)".
          iExists _, _; iFrame. rewrite /offset_loc. done. }
        rewrite big_sepL2_const_sepL_l. iDestruct "Hl" as "(_ & $)".
      - iIntros "(%ly' & %Hst' & %Hsz & %Hlen & Hl)".
        (* if r is empty, we don't have any loc_in_bounds available.. we really need to require that in the sharing predicate. *)
        rewrite big_sepL_exists. iDestruct "Hl" as "(%vs & Hl)".
        setoid_rewrite <-bi.sep_exist_l.
        iExists (mjoin vs). rewrite big_sepL2_sep. iDestruct "Hl" as "(Hl & Hv)".
        iPoseProof (big_sepL2_length with "Hv") as "%Hlen'".
        iAssert (∀ v, ⌜v ∈ vs⌝ -∗ ⌜v `has_layout_val` ly'⌝)%I with "[Hv]" as "%Ha".
        { iIntros (v (i & Hlook)%elem_of_list_lookup_1).
          assert (∃ r', r !! i = Some r') as (r' & Hlook').
          { destruct (r !! i) eqn:Heq; first by eauto. exfalso.
            apply lookup_lt_Some in Hlook. apply lookup_ge_None_1 in Heq. lia. }
          iPoseProof (big_sepL2_lookup _ _ _ i with "Hv") as "Hv"; [done.. | ].
          iDestruct "Hv" as "(% & _ & Hv)". by iApply (ty_own_val_has_layout with "Hv"). }
        iSplitL "Hl". {
          rewrite big_sepL2_const_sepL_r. iDestruct "Hl" as "(_ & Hl)".
          iApply heap_mapsto_mjoin_uniform. { done. }
          iSplitR; last done.
          apply syn_type_has_layout_array_inv in Hst as (ly0 & Hst0 & -> & ?).
          assert (ly0 = ly') as ->. { by eapply syn_type_has_layout_inj. }
          rewrite -Hlen -Hlen'. rewrite Nat.mul_comm. done. }
        iExists ly'. iSplitR; first done. iSplitR; first done. iSplitR; first done.
        iSplitR. { rewrite /has_layout_val.
          rewrite join_length.
          rewrite (sum_list_fmap_same (ly_size ly')).
          - rewrite -Hlen' -Hlen. rewrite Nat.mul_comm. done.
          - apply Forall_elem_of_iff. done. }
            rewrite reshape_join; first done.
            apply Forall2_lookup.
            intros i.
            destruct (vs !! i) eqn:Heq1; first last.
            { rewrite Heq1.
              rewrite (proj1 (lookup_replicate_None _ _ _)); first constructor.
              apply lookup_ge_None in Heq1. lia. }
            rewrite lookup_replicate_2; first last.
            { apply lookup_lt_Some in Heq1. lia. }
            rewrite Heq1. constructor. rewrite Ha; first last. { eapply elem_of_list_lookup_2. eauto. }
            done.
    }

    iMod (bor_exists with "LFT Hb") as "(%ly' & Hb)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Hst & Hb)"; first done.
    iMod (bor_persistent with "LFT Hst Htok") as "(>%Hst' & Htok)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Hsz & Hb)"; first done.
    iMod (bor_persistent with "LFT Hsz Htok") as "(>%Hsz & Htok)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Hlen & Hb)"; first done.
    iMod (bor_persistent with "LFT Hlen Htok") as "(>%Hlen & Htok)"; first done.
    iMod (bor_big_sepL with "LFT Hb") as "Hb"; first done.
    iCombine "Htok Htok'" as "Htok". rewrite lft_tok_sep.
    (* fracture the tokens over the big_sep *)
    iPoseProof (Fractional_split_big_sepL (λ q, q.[_]%I) len with "Htok") as "(%qs & %Hlen' & Htoks & Hcl_toks)".
    set (κ' := κ ⊓ foldr meet static (ty_lfts ty)).
    iAssert ([∗ list] i ↦ x; q' ∈ r; qs, &{κ} (∃ v r'', (l offset{ly'}ₗ i) ↦ v ∗ place_rfn_interp_owned x r'' ∗ v ◁ᵥ{ π} r'' @ ty) ∗ q'.[κ'])%I with "[Htoks Hb]" as "Hb".
    { iApply big_sepL2_sep_sepL_r; iFrame. iApply big_sepL2_const_sepL_l. iSplitR; last done. rewrite Hlen Hlen' //. }

    eapply syn_type_has_layout_array_inv in Hst as (ly0 & Hst & -> & ?).
    assert (ly0 = ly') as -> by by eapply syn_type_has_layout_inj.
    iAssert ([∗ list] i ↦ x; q' ∈ r; qs, logical_step E ((∃ r', place_rfn_interp_shared x r' ∗ (l offset{ly'}ₗ i) ◁ₗ{π, κ} r' @ ty)
      ∗ q'.[κ']))%I with "[Hb]" as "Hb".
    { iApply (big_sepL2_wand with "Hb"). iApply big_sepL2_intro; first by lia.
      iModIntro. iIntros (k x q0 Hlook1 Hlook2) "(Hb & Htok)".
      rewrite bi_exist_comm.
      iApply fupd_logical_step.
      subst κ'.
      rewrite -{1}lft_tok_sep. iDestruct "Htok" as "(Htok1 & Htok2)".
      iMod (bor_exists_tok with "LFT Hb Htok1") as "(%r' & Ha & Htok1)"; first done.
      iPoseProof (bor_iff _ _ (place_rfn_interp_owned x r' ∗ ∃ a, (l offset{ly'}ₗ k) ↦ a ∗ a ◁ᵥ{ π} r' @ ty)%I with "[] Ha") as "Ha".
      { iNext. iModIntro. iSplit.
        - iIntros "(%a & ? & ? & ?)". eauto with iFrame.
        - iIntros "(? & %a & ? & ?)". eauto with iFrame. }
      iMod (bor_sep with "LFT Ha") as "(Hrfn & Hb)"; first done.
      iMod (place_rfn_interp_owned_share with "LFT Hrfn Htok1") as "(Hrfn & Htok1)"; first done.
      iCombine "Htok1 Htok2" as "Htok". rewrite lft_tok_sep. iModIntro.
      iPoseProof (ty_share with "[$LFT $TIME $LCTX] Htok [] [] [] Hb") as "Hb"; first done.
      - done.
      - iPureIntro.
        apply has_layout_loc_offset_loc.
        { eapply use_layout_alg_wf. done. }
        {  done. }
      - assert (1 + k ≤ len)%nat as ?.
        { eapply lookup_lt_Some in Hlook1. lia. }
        iApply loc_in_bounds_offset; last done.
        { done. }
        { rewrite /offset_loc. simpl. lia. }
        { rewrite /mk_array_layout /ly_mult {2}/ly_size. rewrite /offset_loc /=. nia. }
      - iApply (logical_step_wand with "Hb"). iIntros "(? & ?)".
        eauto with iFrame.
    }
    iPoseProof (logical_step_big_sepL2 with "Hb") as "Hb".
    iModIntro. iApply (logical_step_wand with "Hb"). iIntros "Hb".
    iPoseProof (big_sepL2_sep_sepL_r with "Hb") as "(Hb & Htok)".
    iPoseProof ("Hcl_toks" with "Htok") as "$".
    iPoseProof (big_sepL2_const_sepL_l with "Hb") as "(_ & Hb)".
    iExists _. do 4 iR. done.
  Qed.
  Next Obligation.
    iIntros (ty len κ κ' π r l) "#Hincl Hb".
    iDestruct "Hb" as "(%ly & Hst & Hsz & Hlen & Hly & Hb)".
    iExists ly. iFrame.
    iApply (big_sepL_wand with "Hb"). iApply big_sepL_intro.
    iIntros "!>" (k x Hlook) "(% & ? & Hb)".
    iExists _; iFrame. iApply ty_shr_mono; done.
  Qed.
  Next Obligation.
    iIntros (ty len π r v F ?) "(%ly & ? & ? & ? & ? & Hb)".
    iAssert (logical_step F $ [∗ list] r'; v' ∈ r; reshape (replicate len (ly_size ly)) v,
      match r' with | # r'' => ty_ghost_drop ty π r'' | PlaceGhost _ => True end)%I with "[Hb]" as "Hb".
    { iApply logical_step_big_sepL2. iApply (big_sepL2_mono with "Hb"). iIntros (? r' ???).
      iIntros "(%r'' & Hrfn & Hb)". destruct r'; last by iApply logical_step_intro.
      iDestruct "Hrfn" as "->". by iApply ty_own_ghost_drop. }
    iApply (logical_step_wand with "Hb").
    iIntros "Hb". iPoseProof (big_sepL2_const_sepL_l with "Hb") as "(_ & $)".
  Qed.
  Next Obligation.
    iIntros (ty len ot mt st π r v Hot) "Hb".
    destruct ot as [ | | | | ly']; [done.. | ].
    destruct Hot as (ly0 & -> & Hot & Hwf).
    destruct mt; [done | done | done].
    (* TODO maybe the second case should really change once we support an ArrayOpType? *)
  Qed.

  (* TODO: non-expansiveness *)

  (* TODO copy *)
End array.


Section lemmas.
  Context `{!typeGS Σ}.

  Lemma array_t_own_val_split {rt} (ty : type rt) π n1 n2 v1 v2 rs1 rs2 :
    length rs1 = n1 →
    length rs2 = n2 →
    length v1 = n1 * size_of_st ty.(ty_syn_type) →
    length v2 = n2 * size_of_st ty.(ty_syn_type) →
    (v1 ++ v2) ◁ᵥ{π} (rs1 ++ rs2) @ array_t ty (n1 + n2) -∗
    v1 ◁ᵥ{π} rs1 @ array_t ty n1 ∗ v2 ◁ᵥ{π} rs2 @ array_t ty n2.
  Proof.
    intros Hrs1 Hrs2 Hv1 Hv2. rewrite /ty_own_val /=.
    iIntros "(%ly & %Halg & %Hsz & %Hlen & %Hly & Hb)".
    rewrite /size_of_st /use_layout_alg' Halg /= in Hv1.
    rewrite /size_of_st /use_layout_alg' Halg /= in Hv2.
    rewrite replicate_add. rewrite reshape_app.
    rewrite sum_list_replicate.
    rewrite take_app_alt; last lia.
    rewrite drop_app_alt; last lia.
    iPoseProof (big_sepL2_app_inv with "Hb") as "[Hb1 Hb2]".
    { rewrite reshape_length replicate_length. eauto. }
    iSplitL "Hb1".
    - iExists _. iR. iSplitR. { iPureIntro. lia. }
      iR. iSplitR. { iPureIntro. rewrite /has_layout_val ly_size_mk_array_layout. lia. }
      done.
    - iExists _. iR. iSplitR. { iPureIntro. lia. }
      iR. iSplitR. { iPureIntro. rewrite /has_layout_val ly_size_mk_array_layout. lia. }
      done.
  Qed.

  Lemma array_t_own_val_merge {rt} (ty : type rt) π (n1 n2 : nat) v1 v2 rs1 rs2 :
    (size_of_st ty.(ty_syn_type) * (n1 + n2) ≤ max_int isize_t)%Z →
    v1 ◁ᵥ{π} rs1 @ array_t ty n1 -∗
    v2 ◁ᵥ{π} rs2 @ array_t ty n2 -∗
    (v1 ++ v2) ◁ᵥ{π} (rs1 ++ rs2) @ array_t ty (n1 + n2).
  Proof.
    rewrite /ty_own_val/=.
    iIntros (Hsz) "(%ly1 & %Halg1 & %Hsz1 & %Hlen1 & %Hv1 & Hb1) (%ly2 & %Halg2 & %Hsz2 & %Hlen2 & %Hv2 & Hb2)".
    assert (ly1 = ly2) as <- by by eapply syn_type_has_layout_inj. clear Halg2.
    rewrite /size_of_st /use_layout_alg' Halg1 /= in Hsz.
    iExists ly1. iR. iSplitR. { iPureIntro. lia. }
    rewrite /has_layout_val ly_size_mk_array_layout in Hv1.
    rewrite /has_layout_val ly_size_mk_array_layout in Hv2.
    rewrite app_length -Hlen1 -Hlen2. iR.
    iSplitR. { iPureIntro. rewrite /has_layout_val app_length Hv1 Hv2 ly_size_mk_array_layout. lia. }
    rewrite replicate_add. rewrite reshape_app.
    rewrite sum_list_replicate.
    rewrite take_app_alt; last lia.
    rewrite drop_app_alt; last lia.
    iApply (big_sepL2_app with "Hb1 Hb2").
  Qed.

  Lemma array_t_shr_split {rt} (ty : type rt) π κ n1 n2 l rs1 rs2 :
    length rs1 = n1 →
    length rs2 = n2 →
    l ◁ₗ{π, κ} (rs1 ++ rs2) @ array_t ty (n1 + n2) -∗
    l ◁ₗ{π, κ} rs1 @ array_t ty n1 ∗ (l offsetst{ty.(ty_syn_type)}ₗ n1) ◁ₗ{π, κ} rs2 @ array_t ty n2.
  Proof.
    rewrite /ty_shr/=. iIntros (Hlen1 Hlen2).
    iIntros "(%ly & %Halg & %Hsz & %Hlen & %Hly & Hb)".
    rewrite big_sepL_app. iDestruct "Hb" as "(Hb1 & Hb2)".
    rewrite app_length in Hlen.
    iSplitL "Hb1".
    - iExists _. iR. iSplitR. { iPureIntro. lia. }
      iSplitR. { iPureIntro. lia. }
      iR. done.
    - iExists _. iR. iSplitR. { iPureIntro. lia. }
      iSplitR. { iPureIntro. lia. }
      rewrite /OffsetLocSt /use_layout_alg' Halg/=.
      iSplitR. { iPureIntro. eapply has_layout_loc_offset_loc; last done.
        by eapply use_layout_alg_wf. }
      setoid_rewrite offset_loc_offset_loc. rewrite Hlen1.
      setoid_rewrite Nat2Z.inj_add. done.
  Qed.

  Lemma array_t_shr_merge {rt} (ty : type rt) π κ (n1 n2 : nat) l rs1 rs2 :
    (size_of_st ty.(ty_syn_type) * (n1 + n2) ≤ max_int isize_t)%Z →
    l ◁ₗ{π, κ} rs1 @ array_t ty n1 -∗
    (l offsetst{ty.(ty_syn_type)}ₗ n1) ◁ₗ{π, κ} rs2 @ array_t ty n2 -∗
    l ◁ₗ{π, κ} (rs1 ++ rs2) @ array_t ty (n1 + n2).
  Proof.
    rewrite /ty_shr/=. iIntros (Hsz).
    iIntros "(%ly1 & %Halg1 & %Hsz1 & %Hlen1 & %Hly1 & Hb1) (%ly2 & %Halg2 & %Hsz2 & %Hlen2 & %Hly2 & Hb2)".
    assert (ly2 = ly1) as -> by by eapply syn_type_has_layout_inj. clear Halg2.
    rewrite /size_of_st /use_layout_alg' Halg1 /= in Hsz.
    iExists _. iR. iSplitR. { iPureIntro. lia. }
    rewrite app_length. iSplitR. { iPureIntro. lia. }
    iR. iApply (big_sepL_app).
    iFrame.
    rewrite /OffsetLocSt /use_layout_alg' Halg1 /=.
    setoid_rewrite offset_loc_offset_loc. rewrite -Hlen1.
    setoid_rewrite Nat2Z.inj_add. done.
  Qed.

End lemmas.

Section subtype.
  Context `{!typeGS Σ}.

  Import EqNotations.
  Local Definition array_t_incl_precond {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) rs1 rs2 :=
    ([∗ list] r1; r2 ∈ rs1; rs2,
      match r1, r2 with
      | #r1, #r2 => type_incl r1 r2 ty1 ty2
      | _, _ => ∃ (Heq : rt1 = rt2), ⌜r1 = rew <- [place_rfn] Heq in r2⌝ ∗ ∀ (r : rt1), type_incl r (rew Heq in r) ty1 ty2
      end)%I.
  Local Instance array_t_incl_precond_pers {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) rs1 rs2 :
    Persistent (array_t_incl_precond ty1 ty2 rs1 rs2).
  Proof.
    apply big_sepL2_persistent. intros ? [] []; simpl; apply _.
  Qed.

  (* TODO: should we handle things like [u16; 2] << [u8; 4]? *)

  (* TODO: in practice, we probably just want equality for the refinements? think about the symbolic case.. *)
  Lemma array_t_own_val_mono' {rt1 rt2} π (ty1 : type rt1) (ty2 : type rt2) rs1 rs2 len v :
    array_t_incl_precond ty1 ty2 rs1 rs2 -∗
    v ◁ᵥ{π} rs1 @ array_t ty1 len -∗
    v ◁ᵥ{π} rs2 @ array_t ty2 len.
  Proof.
  Admitted.
  (* the "trivial" (Rust) subtyping that we need for, e.g., lifetimes *)
  Lemma array_t_own_val_mono {rt} π (ty1 ty2 : type rt) len v rs :
    (∀ r, type_incl r r ty1 ty2) -∗
    v ◁ᵥ{π} rs @ array_t ty1 len -∗
    v ◁ᵥ{π} rs @ array_t ty2 len.
  Proof.
  Admitted.

  Lemma array_t_shr_mono' {rt1 rt2} π (ty1 : type rt1) (ty2 : type rt2) rs1 rs2 len v κ :
    array_t_incl_precond ty1 ty2 rs1 rs2 -∗
    v ◁ₗ{π, κ} rs1 @ array_t ty1 len -∗
    v ◁ₗ{π, κ} rs2 @ array_t ty2 len.
  Proof.
  Admitted.
  Lemma array_t_shr_mono {rt} π (ty1 ty2 : type rt) len v rs κ :
    (∀ r, type_incl r r ty1 ty2) -∗
    v ◁ₗ{π, κ} rs @ array_t ty1 len -∗
    v ◁ₗ{π, κ} rs @ array_t ty2 len.
  Proof.
  Admitted.

  Lemma array_t_type_incl' {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) rs1 rs2 len :
    array_t_incl_precond ty1 ty2 rs1 rs2 -∗
    type_incl rs1 rs2 (array_t ty1 len) (array_t ty2 len).
  Proof.
  Admitted.
  Lemma array_t_type_incl {rt} (ty1 ty2 : type rt) rs len :
    (∀ r, type_incl r r ty1 ty2) -∗
    type_incl rs rs (array_t ty1 len) (array_t ty2 len).
  Proof.
  Admitted.

  Lemma array_t_full_subtype E L {rt} (ty1 ty2 : type rt) len :
    full_subtype E L ty1 ty2 →
    full_subtype E L (array_t ty1 len) (array_t ty2 len).
  Proof.
  Admitted.

End subtype.

Section subltype.
  Context `{!typeGS Σ}.


  Local Lemma array_ltype_incl_big_wand_in {rt1 rt2} k π F (def1 : type rt1) (def2 : type rt2) len (lts1 : list (nat * ltype rt1)) (lts2 : list (nat * ltype rt2)) rs1 rs2 l b ly :
    lftE ⊆ F →
    length rs1 = len → length rs2 = len →
    ty_syn_type def1 = ty_syn_type def2 →
    ([∗ list] lt1;lt2 ∈ zip (interpret_iml (◁ def1) len lts1) rs1; zip (interpret_iml (◁ def2) len lts2) rs2, ltype_incl b lt1.2 lt2.2 lt1.1 lt2.1) -∗
    ([∗ list] i↦lt;r0 ∈ interpret_iml (◁ def1) len lts1;rs1, ⌜ltype_st lt = ty_syn_type def1⌝ ∗ (l offset{ly}ₗ (k + i)%nat) ◁ₗ[ π, b] r0 @ lt) ={F}=∗
    ([∗ list] i↦lt;r0 ∈ interpret_iml (◁ def2) len lts2;rs2, ⌜ltype_st lt = ty_syn_type def2⌝ ∗ (l offset{ly}ₗ (k + i)%nat) ◁ₗ[ π, b] r0 @ lt).
  Proof.
    iIntros (? Hlen1 Hlen2 Hstdef) "#Hincl Ha".
    iInduction len as [ | len] "IH" forall (k rs1 rs2 lts1 lts2 Hlen1 Hlen2); simpl.
    { destruct rs2; last done. rewrite !interpret_iml_0 //. }
    destruct rs2 as [ | r2 rs2]; first done.
    destruct rs1 as [ | r1 rs1]; first done.
    simpl.
    rewrite !interpret_iml_succ. simpl.
    iDestruct "Ha" as "((%Hsteq & Ha) & Hb)".
    iDestruct "Hincl" as "(Hincl1 & Hincl)".
    simpl in *.
    iSpecialize ("IH" $! (S k) with "[] [] Hincl [Hb]").
    { iPureIntro. lia. }
    { iPureIntro. lia. }
    { setoid_rewrite Nat.add_succ_r. done. }
    iMod "IH" as "IH".
    iPoseProof "Hincl1" as "(%Hst & _)".
    iMod (ltype_incl_use with "Hincl1 Ha") as "$"; first done.
    iSplitR. { rewrite -Hst -Hstdef. done. }
    setoid_rewrite Nat.add_succ_r. done.
  Qed.

  Local Lemma array_ltype_incl_big_wand {rt} k π F (def1 : type rt) (def2 : type rt) len (lts1 : list (nat * ltype rt)) (lts2 : list (nat * ltype rt)) rs l b ly :
    lftE ⊆ F →
    length rs = len →
    ty_syn_type def1 = ty_syn_type def2 →
    ([∗ list] lt1;lt2 ∈ interpret_iml (◁ def1) len lts1; interpret_iml (◁ def2) len lts2, ∀ r, ltype_incl b r r lt1 lt2) -∗
    ([∗ list] i↦lt;r0 ∈ interpret_iml (◁ def1) len lts1;rs, ⌜ltype_st lt = ty_syn_type def1⌝ ∗ (l offset{ly}ₗ (k + i)%nat) ◁ₗ[ π, b] r0 @ lt) ={F}=∗
    ([∗ list] i↦lt;r0 ∈ interpret_iml (◁ def2) len lts2;rs, ⌜ltype_st lt = ty_syn_type def2⌝ ∗ (l offset{ly}ₗ (k + i)%nat) ◁ₗ[ π, b] r0 @ lt).
  Proof.
    iIntros (? Hlen Hstdef) "#Hincl Ha".
    iInduction len as [ | len] "IH" forall (k rs lts1 lts2 Hlen); simpl.
    { destruct rs; last done. rewrite !interpret_iml_0 //. }
    destruct rs as [ | r rs]; first done.
    simpl.
    rewrite !interpret_iml_succ. simpl.
    iDestruct "Ha" as "((%Hsteq & Ha) & Hb)".
    iDestruct "Hincl" as "(Hincl1 & Hincl)".
    simpl in *.
    setoid_rewrite Nat.add_succ_r.
    iSpecialize ("IH" $! (S k) rs with "[] Hincl Hb").
    { iPureIntro. lia. }
    iMod "IH" as "IH".
    iPoseProof ("Hincl1" $! r) as "(%Hst & _)".
    iMod (ltype_incl_use with "Hincl1 Ha") as "$"; first done.
    iSplitR. { rewrite -Hst -Hstdef. done. }
    done.
  Qed.


  Local Lemma array_ltype_incl'_shared_in {rt1 rt2} (def1 : type rt1) (def2 : type rt2) len (lts1 : list (nat * ltype rt1)) (lts2 : list (nat * ltype rt2)) κ' rs1 rs2 :
    ty_syn_type def1 = ty_syn_type def2 →
    (⌜length rs1 = len⌝ -∗ ⌜length rs2 = len⌝ ∗ ([∗ list] lt1; lt2 ∈ zip (interpret_iml (◁ def1) len lts1) rs1; zip (interpret_iml (◁ def2) len lts2) rs2,
      ltype_incl (Shared κ') (lt1).2 (lt2).2 (lt1).1 (lt2).1)) -∗
    ltype_incl' (Shared κ') #rs1 #rs2 (ArrayLtype def1 len lts1) (ArrayLtype def2 len lts2).
  Proof.
    iIntros (Hst) "#Hel".
    iModIntro. iIntros (π l) "Ha".
    rewrite !ltype_own_array_unfold /array_ltype_own.
    iDestruct "Ha" as "(%ly & %Halg & %Hsz & %Hly & Hlb & %r' & <- & %Hlen & #Ha)".
    iExists ly. iSplitR. { rewrite -Hst. done. }
    iR. iR. iFrame. iExists rs2. iR.
    iPoseProof ("Hel" with "[//]") as "Hc".
    iDestruct "Hc" as "(%Hb & Hc)". iR.
    iModIntro. iMod "Ha".
    iMod (array_ltype_incl_big_wand_in 0 with "Hc Ha") as "Ha"; [done.. | ].
    done.
  Qed.
  Lemma array_ltype_incl_shared_in {rt1 rt2} (def1 : type rt1) (def2 : type rt2) len (lts1 : list (nat * ltype rt1)) (lts2 : list (nat * ltype rt2)) κ' rs1 rs2 :
    ty_syn_type def1 = ty_syn_type def2 →
    (⌜length rs1 = len⌝ -∗ ⌜length rs2 = len⌝ ∗ [∗ list] lt1; lt2 ∈ zip (interpret_iml (◁ def1) len lts1) rs1; zip (interpret_iml (◁ def2) len lts2) rs2,
      ltype_incl (Shared κ') (lt1).2 (lt2).2 (lt1).1 (lt2).1) -∗
    ltype_incl (Shared κ') #rs1 #rs2 (ArrayLtype def1 len lts1) (ArrayLtype def2 len lts2).
  Proof.
    iIntros (Hst) "#Heq".
    iSplitR. { iPureIntro. simp_ltypes. rewrite Hst//. }
    iModIntro. simp_ltypes.
    iSplit; (iApply array_ltype_incl'_shared_in; first done).
    - done.
    - iIntros (Hlen'). iSpecialize ("Heq" with "[//]"). iDestruct "Heq" as "($ & Heq)".
      rewrite -{2}(ltype_core_ofty def1) -{2}(ltype_core_ofty def2).
      rewrite !interpret_iml_fmap.
      rewrite !zip_fmap_l.
      rewrite big_sepL2_fmap_l big_sepL2_fmap_r.
      iApply (big_sepL2_mono with "Heq").
      iIntros (k [lt1 r1] [lt2 r2] ??). simpl. iApply ltype_incl_core; done.
  Qed.

  Local Lemma array_ltype_incl'_shared {rt} (def1 : type rt) (def2 : type rt) len (lts1 : list (nat * ltype rt)) (lts2 : list (nat * ltype rt)) κ' rs :
    ty_syn_type def1 = ty_syn_type def2 →
    ([∗ list] lt1; lt2 ∈ interpret_iml (◁ def1) len lts1; interpret_iml (◁ def2) len lts2,
      ∀ r, ltype_incl (Shared κ') r r lt1 lt2) -∗
    ltype_incl' (Shared κ') rs rs (ArrayLtype def1 len lts1) (ArrayLtype def2 len lts2).
  Proof.
    iIntros (Hst) "#Hel".
    iModIntro. iIntros (π l) "Ha".
    rewrite !ltype_own_array_unfold /array_ltype_own.
    iDestruct "Ha" as "(%ly & %Halg & %Hsz & %Hly & Hlb & %r' & Hrfn & %Hlen & #Ha)".
    iExists ly. iSplitR. { rewrite -Hst. done. }
    iR. iR. iFrame. iExists r'. iFrame. iR.
    iPoseProof ("Hel" with "") as "Hc".
    iModIntro. iMod "Ha".
    iMod (array_ltype_incl_big_wand 0 with "Hc Ha") as "Ha"; [done.. | ].
    done.
  Qed.
  Lemma array_ltype_incl_shared {rt} (def1 : type rt) (def2 : type rt) len (lts1 : list (nat * ltype rt)) (lts2 : list (nat * ltype rt)) κ' rs :
    ty_syn_type def1 = ty_syn_type def2 →
    ([∗ list] lt1; lt2 ∈ interpret_iml (◁ def1) len lts1; interpret_iml (◁ def2) len lts2,
      ∀ r, ltype_incl (Shared κ') r r lt1 lt2) -∗
    ltype_incl (Shared κ') rs rs (ArrayLtype def1 len lts1) (ArrayLtype def2 len lts2).
  Proof.
    iIntros (Hst) "#Heq".
    iSplitR. { iPureIntro. simp_ltypes. rewrite Hst//. }
    iModIntro. simp_ltypes.
    iSplit; (iApply array_ltype_incl'_shared; first done).
    - done.
    - rewrite -{2}(ltype_core_ofty def1) -{2}(ltype_core_ofty def2).
      rewrite !interpret_iml_fmap.
      rewrite big_sepL2_fmap_l big_sepL2_fmap_r.
      iApply (big_sepL2_mono with "Heq").
      iIntros (k lt1 lt2 ??). simpl. iIntros "Ha" (?). iApply ltype_incl_core; done.
  Qed.

  Local Lemma array_ltype_incl'_owned_in {rt1 rt2} (def1 : type rt1) (def2 : type rt2) len (lts1 : list (nat * ltype rt1)) (lts2 : list (nat * ltype rt2)) wl rs1 rs2 :
    ty_syn_type def1 = ty_syn_type def2 →
    (⌜length rs1 = len⌝ -∗ ⌜length rs2 = len⌝ ∗ [∗ list] lt1; lt2 ∈ zip (interpret_iml (◁ def1) len lts1) rs1; zip (interpret_iml (◁ def2) len lts2) rs2,
      ltype_incl (Owned false) (lt1).2 (lt2).2 (lt1).1 (lt2).1) -∗
    ltype_incl' (Owned wl) #rs1 #rs2 (ArrayLtype def1 len lts1) (ArrayLtype def2 len lts2).
  Proof.
    iIntros (Hst) "#Hel".
    iModIntro. iIntros (π l) "Ha".
    rewrite !ltype_own_array_unfold /array_ltype_own.
    iDestruct "Ha" as "(%ly & %Halg & %Hsz & %Hly & Hlb & Hcred & %r' & <- & %Hlen & Ha)".
    iExists ly. iSplitR. { rewrite -Hst. done. }
    iR. iR. iFrame. iExists rs2. iR.
    iPoseProof ("Hel" with "[//]") as "Hc".
    iDestruct "Hc" as "(%Hb & Hc)". iR.
    iModIntro. iNext. iMod "Ha".
    iMod (array_ltype_incl_big_wand_in 0 with "Hc Ha") as "Ha"; [done.. | ].
    done.
  Qed.
  Lemma array_ltype_incl_owned_in {rt1 rt2} (def1 : type rt1) (def2 : type rt2) len (lts1 : list (nat * ltype rt1)) (lts2 : list (nat * ltype rt2)) wl rs1 rs2 :
    ty_syn_type def1 = ty_syn_type def2 →
    (⌜length rs1 = len⌝ -∗ ⌜length rs2 = len⌝ ∗ [∗ list] lt1; lt2 ∈ zip (interpret_iml (◁ def1) len lts1) rs1; zip (interpret_iml (◁ def2) len lts2) rs2,
      ltype_incl (Owned false) (lt1).2 (lt2).2 (lt1).1 (lt2).1) -∗
    ltype_incl (Owned wl) #rs1 #rs2 (ArrayLtype def1 len lts1) (ArrayLtype def2 len lts2).
  Proof.
    iIntros (Hst) "#Heq".
    iSplitR. { iPureIntro. simp_ltypes. rewrite Hst//. }
    iModIntro. simp_ltypes.
    iSplit; (iApply array_ltype_incl'_owned_in; first done).
    - done.
    - iIntros (Hlen'). iSpecialize ("Heq" with "[//]"). iDestruct "Heq" as "(% & Heq)". iR.
      rewrite -{2}(ltype_core_ofty def1) -{2}(ltype_core_ofty def2).
      rewrite !interpret_iml_fmap.
      rewrite !zip_fmap_l.
      rewrite big_sepL2_fmap_l big_sepL2_fmap_r.
      iApply (big_sepL2_mono with "Heq").
      iIntros (k [lt1 r1] [lt2 r2] ??). simpl. iApply ltype_incl_core; done.
  Qed.

  Local Lemma array_ltype_incl'_owned {rt} (def1 : type rt) (def2 : type rt) len (lts1 : list (nat * ltype rt)) (lts2 : list (nat * ltype rt)) wl rs :
    ty_syn_type def1 = ty_syn_type def2 →
    ([∗ list] lt1; lt2 ∈ interpret_iml (◁ def1) len lts1; interpret_iml (◁ def2) len lts2,
      ∀ r, ltype_incl (Owned false) r r lt1 lt2) -∗
    ltype_incl' (Owned wl) rs rs (ArrayLtype def1 len lts1) (ArrayLtype def2 len lts2).
  Proof.
    iIntros (Hst) "#Hel".
    iModIntro. iIntros (π l) "Ha".
    rewrite !ltype_own_array_unfold /array_ltype_own.
    iDestruct "Ha" as "(%ly & %Halg & %Hsz & %Hly & Hlb & Hcred & %r' & Hrfn & %Hlen & Ha)".
    iExists ly. iSplitR. { rewrite -Hst. done. }
    iR. iR. iFrame. iExists r'. iFrame. iR.
    iPoseProof ("Hel" with "") as "Hc".
    iModIntro. iNext. iMod "Ha".
    iMod (array_ltype_incl_big_wand 0 with "Hc Ha") as "Ha"; [done.. | ].
    done.
  Qed.
  Lemma array_ltype_incl_owned {rt} (def1 : type rt) (def2 : type rt) len (lts1 : list (nat * ltype rt)) (lts2 : list (nat * ltype rt)) wl rs :
    ty_syn_type def1 = ty_syn_type def2 →
    ([∗ list] lt1; lt2 ∈ interpret_iml (◁ def1) len lts1; interpret_iml (◁ def2) len lts2,
      ∀ r, ltype_incl (Owned false) r r lt1 lt2) -∗
    ltype_incl (Owned wl) rs rs (ArrayLtype def1 len lts1) (ArrayLtype def2 len lts2).
  Proof.
    iIntros (Hst) "#Heq".
    iSplitR. { iPureIntro. simp_ltypes. rewrite Hst//. }
    iModIntro. simp_ltypes.
    iSplit; (iApply array_ltype_incl'_owned; first done).
    - done.
    - rewrite -{2}(ltype_core_ofty def1) -{2}(ltype_core_ofty def2).
      rewrite !interpret_iml_fmap.
      rewrite big_sepL2_fmap_l big_sepL2_fmap_r.
      iApply (big_sepL2_mono with "Heq").
      iIntros (k lt1 lt2 ??). simpl. iIntros "Ha" (?). iApply ltype_incl_core; done.
  Qed.

  Local Lemma array_ltype_incl'_uniq {rt} (def1 : type rt) (def2 : type rt) len (lts1 : list (nat * ltype rt)) (lts2 : list (nat * ltype rt)) κ' γ rs :
    ty_syn_type def1 = ty_syn_type def2 →
    ([∗ list] lt1; lt2 ∈ interpret_iml (◁ def1) len lts1; interpret_iml (◁ def2) len lts2,
      ∀ r, ltype_eq (Owned false) r r lt1 lt2) -∗
    ltype_incl' (Uniq κ' γ) rs rs (ArrayLtype def1 len lts1) (ArrayLtype def2 len lts2).
  Proof.
    iIntros (Hst) "#Hel".
    iModIntro. iIntros (π l) "Ha".
    rewrite !ltype_own_array_unfold /array_ltype_own.
    iDestruct "Ha" as "(%ly & %Halg & %Hsz & %Hly & Hlb & ? & ? & Hrfn & Ha)".
    iExists ly. iSplitR. { rewrite -Hst. done. }
    iR. iR. iFrame.
    iMod "Ha". iModIntro.
    iApply (pinned_bor_iff with "[] [] Ha"); iNext; iModIntro.
    - iSplit; iIntros "(%r' & ? & % & Ha)"; iExists _; iFrame "∗%"; iMod "Ha";
        (iMod (array_ltype_incl_big_wand 0 with "[Hel] Ha") as "Hx"; [done.. |  | done ]).
      + iApply (big_sepL2_mono with "Hel"). iIntros (?????) "Ha". iIntros (?). iDestruct ("Ha" $! _) as "($ & _)".
      + rewrite big_sepL2_flip.
        iApply (big_sepL2_mono with "Hel"). iIntros (?????) "Ha". iIntros (?). iDestruct ("Ha" $! _) as "(_ & $)".
    - iSplit; iIntros "(%r' & ? & % & Ha)"; iExists _; iFrame "∗%"; iMod "Ha".
      + setoid_rewrite ltype_own_core_equiv.

        (*
        iMod (array_ltype_incl_big_wand 0 with "[Hel] [Ha]") as "Hx".
        5: { iApply (big_sepL2_mono with "Ha"). iIntros (?????). iIntros "(? & ?)". iFrame.
          simpl.
        [done.. |  | done ].
        iApply (big_sepL2_mono with "Hel"). iIntros (?????) "Ha". iIntros (?). iDestruct ("Ha" $! _) as "($ & _)".
      + rewrite big_sepL2_flip.
        iApply (big_sepL2_mono with "Hel"). iIntros (?????) "Ha". iIntros (?). iDestruct ("Ha" $! _) as "(_ & $)".
    done.
         *)
  Admitted.
  Lemma array_ltype_incl_uniq {rt} (def1 : type rt) (def2 : type rt) len (lts1 : list (nat * ltype rt)) (lts2 : list (nat * ltype rt)) κ' γ rs :
    ty_syn_type def1 = ty_syn_type def2 →
    ([∗ list] lt1; lt2 ∈ interpret_iml (◁ def1) len lts1; interpret_iml (◁ def2) len lts2,
      ∀ r, ltype_eq (Owned false) r r lt1 lt2) -∗
    ltype_incl (Uniq κ' γ) rs rs (ArrayLtype def1 len lts1) (ArrayLtype def2 len lts2).
  Proof.
    iIntros (Hst) "#Heq".
    iSplitR. { iPureIntro. simp_ltypes. rewrite Hst//. }
    iModIntro. simp_ltypes.
    iSplit; (iApply array_ltype_incl'_uniq; first done).
    - done.
    - rewrite -{2}(ltype_core_ofty def1) -{2}(ltype_core_ofty def2).
      rewrite !interpret_iml_fmap.
      rewrite big_sepL2_fmap_l big_sepL2_fmap_r.
      iApply (big_sepL2_mono with "Heq").
      iIntros (k lt1 lt2 ??). simpl. iIntros "Ha" (?). iApply ltype_eq_core; done.
  Qed.

  Lemma array_ltype_incl {rt} (def1 def2 : type rt) len (lts1 lts2 : list (nat * ltype rt)) k rs :
    ty_syn_type def1 = ty_syn_type def2 →
    (∀ k, [∗ list] lt1; lt2 ∈ interpret_iml (◁ def1) len lts1; interpret_iml (◁ def2) len lts2,
      ∀ r, ltype_eq k r r lt1 lt2) -∗
    ltype_incl k rs rs (ArrayLtype def1 len lts1) (ArrayLtype def2 len lts2).
  Proof.
    iIntros (?) "#Heq".
    destruct k.
    - iApply array_ltype_incl_owned; first done.
      iApply (big_sepL2_wand with "Heq"). iApply big_sepL2_intro.
      { rewrite !interpret_iml_length//. }
      iIntros "!>" (? lt1 lt2 ? ?) "Ha". iIntros (r).
      iDestruct ("Ha" $! r) as "[$ _]".
    - iApply array_ltype_incl_shared; first done.
      iApply (big_sepL2_wand with "Heq"). iApply big_sepL2_intro.
      { rewrite !interpret_iml_length//. }
      iIntros "!>" (? lt1 lt2 ? ?) "Ha". iIntros (r).
      iDestruct ("Ha" $! r) as "[$ _]".
    - iApply array_ltype_incl_uniq; done.
  Qed.

  Lemma array_ltype_eq {rt} (def1 def2 : type rt) (lts1 lts2 : list (nat * ltype rt)) len rs k :
    ty_syn_type def1 = ty_syn_type def2 →
    (∀ k, [∗ list] lt1; lt2 ∈ (interpret_iml (◁ def1) len lts1); (interpret_iml (◁ def2) len lts2),
      ∀ r, ltype_eq k r r lt1 lt2) -∗
    ltype_eq k rs rs (ArrayLtype def1 len lts1) (ArrayLtype def2 len lts2).
  Proof.
    iIntros (?) "#Heq".
    iSplit.
    - iApply array_ltype_incl; done.
    - iApply array_ltype_incl; first done. iIntros (k').
      iSpecialize ("Heq" $! k').
      iApply big_sepL2_flip.
      iApply (big_sepL2_wand with "Heq").
      iApply big_sepL2_intro. { rewrite !interpret_iml_length//. }
      iIntros "!>" (? ?? ??) "Heq'".
      iIntros (?). iApply ltype_eq_sym. done.
  Qed.

  Lemma array_full_subltype E L {rt} (def1 def2 : type rt) (lts1 lts2 : list (nat * ltype rt)) len :
    ty_syn_type def1 = ty_syn_type def2 →
    Forall2 (λ lt1 lt2, full_eqltype E L lt1 lt2) (interpret_iml (◁ def1) len lts1)%I (interpret_iml (◁ def2)%I len lts2) →
    full_subltype E L (ArrayLtype def1 len lts1) (ArrayLtype def2 len lts2).
  Proof.
    intros ? Hsub.
    iIntros (qL) "HL #CTX #HE".
    iAssert (∀ k, [∗ list] lt1; lt2 ∈ interpret_iml (◁ def1) len lts1; interpret_iml (◁ def2)%I len lts2,
      ∀ r, ltype_eq k r r lt1 lt2)%I with "[HL]" as "#Heq".
    { iIntros (k).
      iPoseProof (Forall2_big_sepL2 with "HL []") as "(Ha & HL)"; first apply Hsub.
      { rewrite !interpret_iml_length. done. }
      { iModIntro. iIntros (lt1 lt2) "HL %Heqt".
        iPoseProof (Heqt with "HL CTX HE") as "#Ha". iFrame "HL". iApply "Ha". }
      iApply (big_sepL2_mono with "Ha").
      iIntros (??? ??) "#Heq". iIntros (r). iApply "Heq". }
    iIntros (k r). iApply array_ltype_incl; done.
  Qed.
  Lemma array_full_eqltype E L {rt} (def1 def2 : type rt) len (lts1 lts2 : list (nat * ltype rt)) :
    ty_syn_type def1 = ty_syn_type def2 →
    Forall2 (λ lt1 lt2, full_eqltype E L lt1 lt2) (interpret_iml (◁ def1) len lts1)%I (interpret_iml (◁ def2)%I len lts2) →
    full_eqltype E L (ArrayLtype def1 len lts1) (ArrayLtype def2 len lts2).
  Proof.
    intros ? Hsub.
    apply full_subltype_eqltype; (eapply array_full_subltype; first done).
    - done.
    - rewrite Forall2_flip. eapply Forall2_impl; first done.
      intros ??; naive_solver.
  Qed.
End subltype.


Section unfold.
  Context `{!typeGS Σ}.

  Lemma array_t_unfold_1_owned {rt} wl (ty : type rt) (len : nat) rs :
    ⊢ ltype_incl' (Owned wl) rs rs (ArrayLtype ty len []) (◁ (array_t ty len)).
  Proof.
  Admitted.

  Lemma array_t_unfold_1_shared {rt} κ (ty : type rt) (len : nat) rs :
    ⊢ ltype_incl' (Shared κ) rs rs (ArrayLtype ty len []) (◁ (array_t ty len)).
  Proof.
  Admitted.

  Lemma array_t_unfold_1_uniq {rt} κ γ (ty : type rt) (len : nat) rs :
    ⊢ ltype_incl' (Uniq κ γ) rs rs (ArrayLtype ty len []) (◁ (array_t ty len)).
  Proof.
  Admitted.

  Local Lemma array_t_unfold_1' {rt} k (ty : type rt) (len : nat) rs :
    ⊢ ltype_incl' k rs rs (ArrayLtype ty len []) (◁ (array_t ty len)).
  Proof.
    destruct k.
    - by apply array_t_unfold_1_owned.
    - by apply array_t_unfold_1_shared.
    - by apply array_t_unfold_1_uniq.
  Qed.

  Lemma array_t_unfold_1 {rt} k (ty : type rt) (len : nat) rs :
    ⊢ ltype_incl k rs rs (ArrayLtype ty len []) (◁ (array_t ty len)).
  Proof.
    iModIntro.
    iSplitR. { simp_ltypes. rewrite {2}/ty_syn_type /array_t //. }
    iSplitR.
    - by iApply array_t_unfold_1'.
    - simp_ltypes. by iApply array_t_unfold_1'.
  Qed.

  Lemma array_t_unfold_2_owned {rt} wl (ty : type rt) (len : nat) rs :
    ⊢ ltype_incl' (Owned wl) rs rs (◁ (array_t ty len)) (ArrayLtype ty len []).
  Proof.
  Admitted.

  Lemma array_t_unfold_2_shared {rt} κ (ty : type rt) (len : nat) rs :
    ⊢ ltype_incl' (Shared κ) rs rs (◁ (array_t ty len)) (ArrayLtype ty len []).
  Proof.
  Admitted.

  Lemma array_t_unfold_2_uniq {rt} κ γ (ty : type rt) (len : nat) rs :
    ⊢ ltype_incl' (Uniq κ γ) rs rs (◁ (array_t ty len)) (ArrayLtype ty len []).
  Proof.
  Admitted.

  Local Lemma array_t_unfold_2' {rt} k (ty : type rt) (len : nat) rs :
    ⊢ ltype_incl' k rs rs (◁ (array_t ty len)) (ArrayLtype ty len []).
  Proof.
    destruct k.
    - by apply array_t_unfold_2_owned.
    - by apply array_t_unfold_2_shared.
    - by apply array_t_unfold_2_uniq.
  Qed.

  Lemma array_t_unfold_2 {rt} k (ty : type rt) (len : nat) rs :
    ⊢ ltype_incl k rs rs (◁ (array_t ty len)) (ArrayLtype ty len []).
  Proof.
    iModIntro.
    iSplitR. { simp_ltypes. rewrite {2}/ty_syn_type /array_t //. }
    iSplitR.
    - by iApply array_t_unfold_2'.
    - simp_ltypes. by iApply array_t_unfold_2'.
  Qed.

  Lemma array_t_unfold {rt} k (ty : type rt) (len : nat) rs:
    ⊢ ltype_eq k rs rs (◁ (array_t ty len)) (ArrayLtype ty len []).
  Proof.
    iSplit.
    - by iApply array_t_unfold_2.
    - by iApply array_t_unfold_1.
  Qed.

  Lemma array_t_unfold_full_eqltype E L {rt} (ty : type rt) (len : nat) :
    full_eqltype E L (◁ (array_t ty len))%I (ArrayLtype ty len []).
  Proof.
    iIntros (?) "HL CTX HE". iIntros (??). iApply array_t_unfold.
  Qed.
End unfold.

Section lemmas.
  Context `{!typeGS Σ}.

  Lemma array_t_rfn_length_eq π {rt} (ty : type rt) len r v :
    v ◁ᵥ{π} r @ array_t ty len -∗ ⌜length r = len⌝.
  Proof.
    rewrite /ty_own_val/=. iIntros "(%ly & %Hst & % & $ & _)".
  Qed.

  (** Learnable *)
  Global Program Instance learn_from_hyp_val_array {rt} (ty : type rt) xs len :
    LearnFromHypVal (array_t ty len) xs :=
    {| learn_from_hyp_val_Q := length xs = len |}.
  Next Obligation.
    iIntros (????????) "Hv".
    iPoseProof (array_t_rfn_length_eq with "Hv") as "%Hlen".
    by iFrame.
  Qed.

  (* TODO: possibly also prove these lemmas for location ownership? *)

  Fixpoint delete_iml {X} i (iml : list (nat * X)) : list (nat * X) :=
    match iml with
    | [] => []
    | (j, x) :: iml => if decide (i = j) then delete_iml i iml else (j, x) :: delete_iml i iml
    end.

  Lemma array_ltype_make_default {rt} (def : type rt) len lts i lt1 b r1 r2 :
    (∀ b r, ltype_incl b r r lt1 (◁ def)) -∗
    ltype_incl b r1 r2 (ArrayLtype def len ((i, lt1) :: lts)) (ArrayLtype def len (delete_iml i lts)).
  Proof.

  Abort.

  Lemma array_ltype_make_defaults {rt} (def : type rt) b r len lts :
    ([∗ list] lt ∈ interpret_iml (◁ def)%I len lts, ∀ b r, ltype_incl b r r lt (◁ def)) -∗
    ltype_incl b r r (ArrayLtype def len lts) (ArrayLtype def len []).
  Proof.
    iInduction lts as [ | [i lt] lts] "IH"; simpl.
    { iIntros "_". iApply ltype_incl_refl. }
    destruct i as [ | i]; simpl.
    - destruct len; simpl.
      + rewrite interpret_iml_0; simpl.
        iIntros "_".
        (* TODO *)
  Admitted.

  Lemma array_ltype_make_defaults_full_eqltype E L {rt} (def : type rt) len lts :
    Forall (λ lt, full_eqltype E L lt (◁ def)%I) (interpret_iml (◁ def)%I len lts) →
    full_eqltype E L (ArrayLtype def len lts) (ArrayLtype def len []).
  Proof.
    intros Ha. iIntros (?) "HL #CTX #HE". iIntros (??).
    iPoseProof (Forall_big_sepL with "HL []") as "(Ha & HL)"; first apply Ha.
    { iModIntro. iIntros (lt) "HL %Heqt". iPoseProof (Heqt with "HL CTX HE") as "#Heq".
      iFrame "HL". iApply "Heq". }
    iSplit.
    - iApply array_ltype_make_defaults.
    simpl.
    (* TODO *)
  Admitted.

  Import EqNotations.
  Lemma array_ltype_place_cond_ty b {rt rt'} (def : type rt) (def' : type rt') (len : nat) (lts : list (nat * ltype rt)) (lts' : list (nat * ltype rt')) :
    place_access_rt_rel b rt rt' →
    ty_syn_type def = ty_syn_type def' →
    ([∗ list] lt; lt' ∈ interpret_iml (◁ def) len lts; interpret_iml (◁ def') len lts', typed_place_cond_ty b lt lt') -∗
    typed_place_cond_ty b (ArrayLtype def len lts) (ArrayLtype def' len lts').
  Proof.
    iIntros (Hrel Hst). destruct b; simpl.
    - iIntros "_". iPureIntro. simp_ltypes. rewrite Hst. done.
    - iIntros "Hrel".
      simpl in Hrel. subst rt'.
      iExists eq_refl.
      setoid_rewrite <-bi.sep_exist_r.
      rewrite big_sepL2_sep_sepL_r. iDestruct "Hrel" as "(#Heq & #Hub)".
      iSplitL.
      + iIntros (k r). cbn. iApply array_ltype_eq; first done. iIntros (b').
        iApply (big_sepL2_mono with "Heq").
        iIntros (? lt1 lt2 Hlook1 Hlook2). iIntros "(%Heq & Ha)".
        rewrite (UIP_refl _ _ Heq). iIntros (?). iApply "Ha".
      + iApply array_ltype_imp_unblockable. done.
    - iIntros "Hrel".
      simpl in Hrel. subst rt'.
      iExists eq_refl.
      setoid_rewrite <-bi.sep_exist_r.
      rewrite big_sepL2_sep_sepL_r. iDestruct "Hrel" as "(#Heq & #Hub)".
      iSplitL.
      + cbn. simp_ltypes. iIntros (k r). iApply array_ltype_eq; first done. iIntros (k').
        rewrite -{-1}(ltype_core_ofty def) -{-1}(ltype_core_ofty def').
        rewrite !interpret_iml_fmap. rewrite big_sepL2_fmap_l big_sepL2_fmap_r.
        iApply (big_sepL2_mono with "Heq").
        iIntros (? lt1 lt2 Hlook1 Hlook2). iIntros "(%Heq & Ha)".
        rewrite (UIP_refl _ _ Heq). iIntros (?). iApply "Ha".
      + iApply array_ltype_imp_unblockable. done.
  Qed.
  Lemma array_ltype_place_cond_ty_strong wl {rt rt'} (def : type rt) (def' : type rt') (len : nat) (lts : list (nat * ltype rt)) (lts' : list (nat * ltype rt')) :
    ty_syn_type def = ty_syn_type def' →
    ⊢ typed_place_cond_ty (Owned wl) (ArrayLtype def len lts) (ArrayLtype def' len lts').
  Proof.
    iIntros (Hst). iPureIntro. simp_ltypes. rewrite Hst. done.
  Qed.

  Lemma array_ltype_acc_owned' {rt} F π (def : type rt) (len : nat) (lts : list (nat * ltype rt)) (rs : list (place_rfn rt)) l wl :
    lftE ⊆ F →
    l ◁ₗ[π, Owned wl] #rs @ ArrayLtype def len lts -∗
    ∃ ly, ⌜syn_type_has_layout def.(ty_syn_type) ly⌝ ∗
      ⌜l `has_layout_loc` (mk_array_layout ly len)⌝ ∗
      ⌜(ly_size ly * len ≤ max_int isize_t)%Z⌝ ∗
      (*⌜Forall (λ '(i, _), i < len) lts⌝ ∗*)
      loc_in_bounds l 0 (ly.(ly_size) * len) ∗ |={F}=>
      ([∗ list] i↦lt;r0 ∈ interpret_iml (◁ def) len lts;rs, ⌜ltype_st lt = ty_syn_type def⌝ ∗ (l offset{ly}ₗ i) ◁ₗ[π, Owned false] r0 @ lt) ∗
      (∀ (rt' : Type) (def' : type rt') (lts' : list (nat * ltype rt')) (rs' : list (place_rfn rt')),
        (if wl then £1 else True) -∗
        ⌜ty_syn_type def = ty_syn_type def'⌝ -∗
        (*⌜Forall (λ '(i, _), i < len) lts'⌝ -∗*)
        (* new ownership *)
        ([∗ list] i↦lt;r0 ∈ interpret_iml (◁ def') len lts';rs', ⌜ltype_st lt = ty_syn_type def'⌝ ∗ (l offset{ly}ₗ i) ◁ₗ[π, Owned false] r0 @ lt)
         ={F}=∗
        l ◁ₗ[π, Owned wl] #rs' @ ArrayLtype def' len lts').
  Proof.
    (* TODO  *)
    iIntros (?) "Hb". rewrite ltype_own_array_unfold /array_ltype_own.
    iDestruct "Hb" as "(%ly & %Hst & % & %Hly & #Hlb & Hcred & %r' & <- & <- & Hb)".
    iExists ly. iR. iR. iR. iR.
    iMod (maybe_use_credit with "Hcred Hb") as "(Hcred & Hat & Hb)"; first done.
    iModIntro. iFrame.
    iIntros (rt' def' lts' rs') "Hcred' %Hst' Hb".
    rewrite ltype_own_array_unfold /array_ltype_own.
    iModIntro.
    iExists ly. rewrite -Hst'. iR. iR. iR. iR. iFrame.
    iSplitL "Hat Hcred Hcred'".
    { destruct wl; last done. iFrame. rewrite /num_cred. iApply lc_succ. iFrame. }
    iExists rs'. iR.
    iPoseProof (big_sepL2_length with "Hb") as "%Hleneq".
    rewrite interpret_iml_length in Hleneq. iR.
    iNext. done.
  Qed.

  Lemma array_ltype_acc_owned {rt} F π (def : type rt) (len : nat) (lts : list (nat * ltype rt)) (rs : list (place_rfn rt)) l wl :
    lftE ⊆ F →
    l ◁ₗ[π, Owned wl] #rs @ ArrayLtype def len lts -∗
    ∃ ly, ⌜syn_type_has_layout def.(ty_syn_type) ly⌝ ∗
      ⌜l `has_layout_loc` (mk_array_layout ly len)⌝ ∗
      ⌜(ly_size ly * len ≤ max_int isize_t)%Z⌝ ∗
      (*⌜Forall (λ '(i, _), i < len) lts⌝ ∗*)
      loc_in_bounds l 0 (ly.(ly_size) * len) ∗ |={F}=>
      ([∗ list] i↦lt;r0 ∈ interpret_iml (◁ def) len lts;rs, ⌜ltype_st lt = ty_syn_type def⌝ ∗ (l offset{ly}ₗ i) ◁ₗ[π, Owned false] r0 @ lt) ∗
      logical_step F
      (∀ (rt' : Type) (def' : type rt') (lts' : list (nat * ltype rt')) (rs' : list (place_rfn rt')),
        ⌜ty_syn_type def = ty_syn_type def'⌝ -∗
        (*⌜Forall (λ '(i, _), i < len) lts'⌝ -∗*)
        (* new ownership *)
        ([∗ list] i↦lt;r0 ∈ interpret_iml (◁ def') len lts';rs', ⌜ltype_st lt = ty_syn_type def'⌝ ∗ (l offset{ly}ₗ i) ◁ₗ[π, Owned false] r0 @ lt)
         ={F}=∗
        l ◁ₗ[π, Owned wl] #rs' @ ArrayLtype def' len lts' ∗
        (* place condition, if required *)
        (∀ bmin,
         ([∗ list] lt1; lt2 ∈ interpret_iml (◁ def) len lts; interpret_iml (◁ def') len lts', typed_place_cond_ty bmin lt1 lt2) -∗
         ([∗ list] r1; r2 ∈ rs; rs', typed_place_cond_rfn bmin r1 r2) -∗
         ⌜place_access_rt_rel bmin rt rt'⌝ -∗
         typed_place_cond bmin (ArrayLtype def len lts) (ArrayLtype def' len lts') (#rs) (#rs'))).
  Proof.
    iIntros (?) "Hb". rewrite ltype_own_array_unfold /array_ltype_own.
    iDestruct "Hb" as "(%ly & %Hst & % & %Hly & #Hlb & Hcred & %r' & <- & <- & Hb)".
    iExists ly. iR. iR. iR. iR.
    iMod (maybe_use_credit with "Hcred Hb") as "(Hcred & Hat & Hb)"; first done.
    iModIntro. iFrame.
    iApply (logical_step_intro_maybe with "Hat"). iIntros "Hcred' !>".
    iIntros (rt' def' lts' rs') "%Hst' Hb".
    iSplitL "Hb Hcred'".
    { rewrite ltype_own_array_unfold /array_ltype_own.
      iModIntro.
      iExists ly. rewrite -Hst'. iR. iR. iR. iR. iFrame.
      iExists rs'. iR.
      iPoseProof (big_sepL2_length with "Hb") as "%Hleneq".
      rewrite interpret_iml_length in Hleneq. iR.
      iNext. done. }
    (* place cond: *)
    iModIntro.
    iIntros (bmin) "Hcond_ty Hcond_rfn %Hrt".
    rewrite /typed_place_cond.
    iSplitL "Hcond_ty".
    { iApply array_ltype_place_cond_ty; [done | done | done]. }
    destruct bmin; simpl; [done | | done].
    simpl in Hrt. subst rt'.
    iExists eq_refl. iClear "Hlb Hcred". clear.
    iInduction rs as [ | r1 rs IH] "IH" forall (rs'); destruct rs' as [ | r2 rs']; simpl; [done.. | ].
    iDestruct "Hcond_rfn" as "(Hh & Hcond_rfn)".
    iDestruct ("IH" with "Hcond_rfn") as "%Heq". injection Heq as <-.
    iDestruct "Hh" as "(%Heq & %Heq2)".
    rewrite -Heq2. rewrite (UIP_refl _ _ Heq). done.
  Qed.

  (* TODO: uniq access *)

  Lemma array_ltype_acc_shared {rt} F π (def : type rt) (len : nat) (lts : list (nat * ltype rt)) (rs : list (place_rfn rt)) l κ :
    lftE ⊆ F →
    l ◁ₗ[π, Shared κ] #rs @ ArrayLtype def len lts -∗
    ∃ ly, ⌜syn_type_has_layout def.(ty_syn_type) ly⌝ ∗
      ⌜l `has_layout_loc` (mk_array_layout ly len)⌝ ∗
      ⌜(ly_size ly * len ≤ max_int isize_t)%Z⌝ ∗
      (*⌜Forall (λ '(i, _), i < len) lts⌝ ∗*)
      loc_in_bounds l 0 (ly.(ly_size) * len) ∗ |={F}=>
      ([∗ list] i↦lt;r0 ∈ interpret_iml (◁ def) len lts;rs, ⌜ltype_st lt = ty_syn_type def⌝ ∗ (l offset{ly}ₗ i) ◁ₗ[π, Shared κ] r0 @ lt) ∗
      (∀ (def' : type rt) (lts' : list (nat * ltype rt)),
        ⌜ty_syn_type def = ty_syn_type def'⌝ -∗
        (*⌜Forall (λ '(i, _), i < len) lts'⌝ -∗*)
        (* new ownership *)
        ([∗ list] i↦lt;r0 ∈ interpret_iml (◁ def') len lts';rs, ⌜ltype_st lt = ty_syn_type def'⌝ ∗ (l offset{ly}ₗ i) ◁ₗ[π, Shared κ] r0 @ lt)
         ={F}=∗
        l ◁ₗ[π, Shared κ] #rs @ ArrayLtype def' len lts' ∗
        (* place condition, if required *)
        (∀ bmin,
         ([∗ list] lt1; lt2 ∈ interpret_iml (◁ def) len lts; interpret_iml (◁ def') len lts', typed_place_cond_ty bmin lt1 lt2) -∗
         typed_place_cond bmin (ArrayLtype def len lts) (ArrayLtype def' len lts') (#rs) (#rs))
      ).
  Proof.
    iIntros (?) "Hb". rewrite ltype_own_array_unfold /array_ltype_own.
    iDestruct "Hb" as "(%ly & %Hst & % & %Hly & #Hlb & %r' & <- & <- & #Hb)".
    iExists ly. iR. iR. iR. iR.
    iMod (fupd_mask_mono with "Hb") as "#Hb'"; first done.
    iModIntro. iFrame "Hb'".
    iIntros (def' lts') "%Hst' #Hb''".
    rewrite ltype_own_array_unfold /array_ltype_own.
    iModIntro.
    iSplitL.
    { iExists ly. rewrite -Hst'. iR. iR. iR. iR.
      iExists _. iR. iR. iModIntro. by iFrame "Hb''".
    }
    iIntros (bmin) "Hcond".
    iSplitL; last iApply typed_place_cond_rfn_refl.
    iApply array_ltype_place_cond_ty.
    - apply place_access_rt_rel_refl.
    - done.
    - done.
  Qed.
End lemmas.

Section rules.
  Context `{!typeGS Σ}.

  (** ** typed_place *)
  Lemma typed_place_array_owned π E L {rt rtv} (def : type rt) (lts : list (nat * ltype rt)) (len : nat) (rs : list (place_rfn rt)) wl bmin ly l it v (tyv : type rtv) (i : rtv) P T :
    (∃ i',
      ⌜syn_type_has_layout (ty_syn_type def) ly⌝ ∗
      subsume_full E L false (v ◁ᵥ{π} i @ tyv) (v ◁ᵥ{π} i' @ int it) (λ L1 R2, R2 -∗
      ⌜(0 ≤ i')%Z⌝ ∗ ⌜(i' < len)%Z⌝ ∗
      ∀ lt r,
        (* relies on Lithium's built-in simplification of lookups. *)
        ⌜interpret_iml (◁ def) len lts !! Z.to_nat i' = Some lt⌝ -∗
        ⌜rs !! Z.to_nat i' = Some r⌝ -∗
        (* sidecondition for other components *)
        ⌜Forall (lctx_bor_kind_outlives E L1 bmin) (concat ((λ '(_, lt), ltype_blocked_lfts lt) <$> (lts)))⌝ ∗
        typed_place π E L1 (l offsetst{ty_syn_type def}ₗ i') lt r bmin (Owned false) P (λ L2 κs li bi bmin2 rti ltyi ri strong weak,
          T L2 κs li bi bmin2 rti ltyi ri None
            (fmap (λ weak, mk_weak
              (λ lti2 ri2, ArrayLtype def len ((Z.to_nat i', weak.(weak_lt) lti2 ri2) :: lts))
              (λ ri, #(<[Z.to_nat i' := weak.(weak_rfn) ri]> rs))
              (weak.(weak_R))
              ) weak))))
    ⊢ typed_place π E L l (ArrayLtype def len lts) (#rs) bmin (Owned wl) (BinOpPCtx (PtrOffsetOp ly) (IntOp it) v rtv tyv i :: P) T.
  Proof.
    iIntros "(%i' & %Hst & HT)".
    iIntros (????) "#CTX #HE HL #Hincl Hl Hcont".
    simpl. iIntros "Hv".
    iApply fupd_wp.
    iMod ("HT" with "[] [] CTX HE HL Hv") as "(%L' & %R2 & >(Hi & R2) & HL & HT)"; [done.. | ].
    iDestruct ("HT" with "R2") as "(% & % & HT)".
    iMod (fupd_mask_subseteq F) as "HclF"; first done.
    iPoseProof (array_ltype_acc_owned with "Hl") as "(%ly' & %Hst' & %Hly & %Hsz & #Hlb & >(Hb & Hcl))"; first done.
    assert (ly' = ly) as -> by by eapply syn_type_has_layout_inj.
    iMod "HclF" as "_".
    iEval (rewrite /ty_own_val/=) in "Hi".
    iDestruct "Hi" as "(%Hi & %Hiz)".
    iDestruct "CTX" as "(LFT & TIME & LLCTX)".
    iApply (wp_logical_step with "TIME Hcl"); [done.. | ].
    iApply wp_ptr_offset.
    { eapply val_to_of_loc. }
    { done. }
    { rewrite /elem_of/int_elem_of_it. split; last nia.
      specialize (min_int_le_0 isize_t). lia. }
    { iPoseProof (loc_in_bounds_array_offset _ _ (Z.to_nat i') with "Hlb") as "Hlb'"; first lia.
      rewrite Z2Nat.id; last done.
      iApply loc_in_bounds_shorten_suf; last done. lia. }
    { iApply loc_in_bounds_shorten_suf; last done. lia. }
    iModIntro. iNext. iIntros "Hcred Hcl".
    iModIntro. iExists _. iR.
    iPoseProof (big_sepL2_length with "Hb") as "%Hlen_eq".
    rewrite interpret_iml_length in Hlen_eq.
    clear i. set (i := Z.to_nat i').
    destruct (lookup_lt_is_Some_2 (interpret_iml (◁ def) len lts)%I i) as (lti & Hlook_lti).
    { rewrite interpret_iml_length. lia. }
    destruct (lookup_lt_is_Some_2 rs i) as (ri & Hlook_ri).
    { lia. }
    iPoseProof ("HT" $! lti ri with "[//] [//]") as "(%Houtl & HT)".
    iPoseProof (lctx_bor_kind_outlives_all_use with "[//] HE HL") as "#Houtl".
    iPoseProof (big_sepL2_insert_acc with "Hb") as "((%Hsti & Hb) & Hcl_b)"; [done | done | ].
    iPoseProof ("HT" with "[//] [//] [$LFT $TIME $LLCTX] HE HL") as "Hc".
    rewrite /OffsetLocSt/use_layout_alg' Hst/=.
    rewrite /offset_loc.
    iApply ("Hc" with "[] [Hb]").
    { destruct bmin; done. }
    { subst i. rewrite Z2Nat.id//. }
    iIntros (L2 κs l2 b2 bmin0 rti ltyi ri' strong weak) "#Hincl1 Hi Hc".
    iApply ("Hcont" with "[//] Hi").
    iSplitR; first done. destruct weak as [ weak | ]; last done.
    simpl. iIntros (ltyi2 ri2 bmin') "#Hincl2 Hi Hcond".
    iDestruct "Hc" as "(_ & Hc)".
    iMod ("Hc" with "[//] Hi Hcond") as "(Hi & Hcond & Htoks & HR)".
    iPoseProof (typed_place_cond_syn_type_eq with "Hcond") as "%Hsteq".
    iPoseProof ("Hcl_b" with "[Hi]") as "Hb".
    { rewrite /i Z2Nat.id; last done. iFrame. rewrite -Hsteq//. }
    rewrite insert_interpret_iml.
    iMod ("Hcl" with "[//] Hb") as "(Hb & Hcondv)".
    (*{ iPureIntro. rewrite Forall_cons. split; first lia. done. }*)
    iFrame.
    iModIntro.
    iDestruct "Hcond" as "(Hcond & Hcond_rfn)".
    iApply ("Hcondv" with "[Hcond] [Hcond_rfn] []").
    - simpl.
      rewrite -{1}(list_insert_id (interpret_iml _ _ _) i lti); last done.
      rewrite (big_sepL2_insert _ _ _ _ _ (λ _ lt1 lt2, typed_place_cond_ty bmin lt1 lt2) 0); cycle 1.
      { rewrite interpret_iml_length. lia. }
      { rewrite interpret_iml_length. lia. }
      iFrame. iApply big_sepL2_intro; first done.
      iModIntro. iIntros (k lt1 lt2 Hlook ?). case_decide; first done.
      assert (lt1 = lt2) as -> by congruence.
      apply lookup_interpret_iml_Some_inv in Hlook as (? & [-> | Hel]).
      { iApply typed_place_cond_ty_refl_ofty. }
      apply elem_of_list_lookup_1 in Hel as (k' & Hlook).
      iApply typed_place_cond_ty_refl.
      iPoseProof (big_sepL_concat_lookup _ _ k' with "Houtl") as "Ha".
      { rewrite list_lookup_fmap Hlook. done. }
      done.
    - rewrite -{1}(list_insert_id rs i ri); last done.
      rewrite (big_sepL2_insert _ _ _ _ _ (λ _ r1 r2, _) 0); [ | lia..].
      iSplitL; first done.
      iApply big_sepL2_intro; first done. iModIntro.
      iIntros (? r1 r2 ??). case_decide; first done.
      assert (r1 = r2) as -> by congruence. iApply typed_place_cond_rfn_refl.
    - iPureIntro. apply place_access_rt_rel_refl.
  Qed.
  Global Instance typed_place_array_owned_inst π E L {rt rtv} (def : type rt) (lts : list (nat * ltype rt)) (len : nat) (rs : list (place_rfn rt)) wl bmin ly l it v (tyv : type rtv) (i : rtv) P :
    TypedPlace E L π l (ArrayLtype def len lts) (#rs) bmin (Owned wl) (BinOpPCtx (PtrOffsetOp ly) (IntOp it) v rtv tyv i :: P) | 30 :=
    λ T, i2p (typed_place_array_owned π E L def lts len rs wl bmin ly l it v tyv i P T).

  Lemma typed_place_array_uniq π E L {rt rtv} (def : type rt) (lts : list (nat * ltype rt)) (len : nat) (rs : list (place_rfn rt)) κ γ bmin ly l it v (tyv : type rtv) (i : rtv) P T :
    (∃ i',
      ⌜syn_type_has_layout (ty_syn_type def) ly⌝ ∗
      subsume_full E L false (v ◁ᵥ{π} i @ tyv) (v ◁ᵥ{π} i' @ int it) (λ L1 R2, R2 -∗
      ⌜(0 ≤ i')%Z⌝ ∗ ⌜(i' < len)%Z⌝ ∗
      (* get lifetime token *)
      li_tactic (lctx_lft_alive_count_goal E L1 κ) (λ '(κs, L2),
      ∀ lt r,
        (* relies on Lithium's built-in simplification of lookups. *)
        ⌜interpret_iml (◁ def) len lts !! Z.to_nat i' = Some lt⌝ -∗
        ⌜rs !! Z.to_nat i' = Some r⌝ -∗
        (* sidecondition for other components *)
        ⌜Forall (lctx_bor_kind_outlives E L1 bmin) (concat ((λ '(_, lt), ltype_blocked_lfts lt) <$> (lts)))⌝ ∗
        typed_place π E L2 (l offsetst{ty_syn_type def}ₗ i') lt r bmin (Owned false) P (λ L3 κs' li bi bmin2 rti ltyi ri strong weak,
        T L3 (κs ++ κs') li bi bmin2 rti ltyi ri None
            (fmap (λ weak, mk_weak
              (λ lti2 ri2, ArrayLtype def len ((Z.to_nat i', weak.(weak_lt) lti2 ri2) :: lts))
              (λ ri, #(<[Z.to_nat i' := weak.(weak_rfn) ri]> rs))
              (weak.(weak_R))
              ) weak)))))
    ⊢ typed_place π E L l (ArrayLtype def len lts) (#rs) bmin (Uniq κ γ) (BinOpPCtx (PtrOffsetOp ly) (IntOp it) v rtv tyv i :: P) T.
  Proof.
    (* TODO *)
  Admitted.
  Global Instance typed_place_array_uniq_inst π E L {rt rtv} (def : type rt) (lts : list (nat * ltype rt)) (len : nat) (rs : list (place_rfn rt)) κ γ bmin ly l it v (tyv : type rtv) (i : rtv) P :
    TypedPlace E L π l (ArrayLtype def len lts) (#rs) bmin (Uniq κ γ) (BinOpPCtx (PtrOffsetOp ly) (IntOp it) v rtv tyv i :: P) | 30 :=
    λ T, i2p (typed_place_array_uniq π E L def lts len rs κ γ bmin ly l it v tyv i P T).

  (* TODO this is a problem, because we can only get strong below OpenedLtype etc.

  *)
  Lemma typed_place_array_shared π E L {rt rtv} (def : type rt) (lts : list (nat * ltype rt)) (len : nat) (rs : list (place_rfn rt)) κ bmin ly l it v (tyv : type rtv) (i : rtv) P T :
    (∃ i',
      ⌜syn_type_has_layout (ty_syn_type def) ly⌝ ∗
      subsume_full E L false (v ◁ᵥ{π} i @ tyv) (v ◁ᵥ{π} i' @ int it) (λ L1 R2, R2 -∗
      ⌜(0 ≤ i')%Z⌝ ∗ ⌜(i' < len)%Z⌝ ∗
      (* get lifetime token *)
      li_tactic (lctx_lft_alive_count_goal E L1 κ) (λ '(κs, L2),
      ∀ lt r,
        (* relies on Lithium's built-in simplification of lookups. *)
        ⌜interpret_iml (◁ def) len lts !! Z.to_nat i' = Some lt⌝ -∗
        ⌜rs !! Z.to_nat i' = Some r⌝ -∗
        (* sidecondition for other components *)
        ⌜Forall (lctx_bor_kind_outlives E L1 bmin) (concat ((λ '(_, lt), ltype_blocked_lfts lt) <$> (lts)))⌝ ∗
        typed_place π E L2 (l offsetst{ty_syn_type def}ₗ i') lt r bmin (Owned false) P (λ L3 κs' li bi bmin2 rti ltyi ri strong weak,
        T L3 (κs ++ κs') li bi bmin2 rti ltyi ri None
            (fmap (λ weak, mk_weak
              (λ lti2 ri2, ArrayLtype def len ((Z.to_nat i', weak.(weak_lt) lti2 ri2) :: lts))
              (λ ri, #(<[Z.to_nat i' := weak.(weak_rfn) ri]> rs))
              (weak.(weak_R))
              ) weak)))))
    ⊢ typed_place π E L l (ArrayLtype def len lts) (#rs) bmin (Shared κ) (BinOpPCtx (PtrOffsetOp ly) (IntOp it) v rtv tyv i :: P) T.
  Proof.
    (* TODO *)
  Admitted.
  Global Instance typed_place_array_shared_inst π E L {rt rtv} (def : type rt) (lts : list (nat * ltype rt)) (len : nat) (rs : list (place_rfn rt)) κ bmin ly l it v (tyv : type rtv) (i : rtv) P :
    TypedPlace E L π l (ArrayLtype def len lts) (#rs) bmin (Shared κ) (BinOpPCtx (PtrOffsetOp ly) (IntOp it) v rtv tyv i :: P) | 30 :=
    λ T, i2p (typed_place_array_shared π E L def lts len rs κ bmin ly l it v tyv i P T).

  Lemma typed_place_array_unfold π E L l {rt} (def : type rt) len rs bmin k P T :
    typed_place π E L l (ArrayLtype def len []) rs bmin k P T
    ⊢ typed_place π E L l (◁ array_t def len) rs bmin k P T.
  Proof.
    iIntros "HT". iApply typed_place_eqltype; last done.
    apply array_t_unfold_full_eqltype.
  Qed.
  Global Instance typed_place_array_unfold_inst π E L l {rt} (def : type rt) len rs bmin k P :
    TypedPlace E L π l (◁ array_t def len)%I rs bmin k P | 20 :=
    λ T, i2p (typed_place_array_unfold π E L l def len rs bmin k P T).

  (** ** subtype instances *)

  (* TODO: should this really match on the addition in the conclusion? probably not. *)
  (*
  Lemma subsume_full_array_split_goal :
    subsume_full E L pers (l ◁ₗ[π, Owned false] r @ lt) (l ◁ₗ[π, Owned false] #(a1) @ ◁ array_t def (length a1)) (λ L R2,
      prove_with_subtype E L pers (l +ₗ ... ◁ₗ[π, Owned false] #a2 @ ◁ array_t def (len - length a1)) T)
    subsume_full E L pers (l ◁ₗ[π, Owned false] r @ lt) (l ◁ₗ[π, Owned false] #(a1 ++ a2) @ ◁ array_t def (len)) T.
  *)
  (* Alternative: do this splitting on prove_with_subtype for array values instead.
   *)
  (* Higher priority instance than direct search for the value: as a heuristic, we split app values *)
  (* TODO: how would that scale to more complex transformations? E.g. what about take etc. -- I guess for that we could have instances as well.
    Basically, I would imagine that we only want to look in the context for primitive values. *)
  Lemma prove_with_subtype_array_val_split π E L pm v1 v2 {rt} (ty : type rt) r1 r2 (len : nat) T :
    ⌜(size_of_st (ty_syn_type ty) * len ≤ max_int isize_t)%Z⌝ ∗
    ⌜length r1 ≤ len⌝ ∗
    prove_with_subtype E L false pm (v1 ◁ᵥ{π} r1 @ array_t ty (length r1)) (λ L2 κs1 R2,
      prove_with_subtype E L2 false pm (v2 ◁ᵥ{π} r2 @ array_t ty (len - length r1)) (λ L3 κs2 R3, T L3 (κs1 ++ κs2) (R2 ∗ R3)%I))
    ⊢ prove_with_subtype E L false pm ((v1 ++ v2) ◁ᵥ{π} r1 ++ r2 @ array_t ty len) T.
  Proof.
    iIntros "(% & % & HT)" (???) "#CTX #HE HL".
    iMod ("HT" with "[//] [//] CTX HE HL") as "(%L2 & %κs1 & %R2 & >(Hv1 & HR2) & HL & HT)".
    iMod ("HT" with "[//] [//] CTX HE HL") as "(%L3 & %κs2 & %R3 & >(Hv2 & HR3) & HL & HT)".
    iModIntro. iExists L3, _, _. iFrame.
    destruct pm.
    - iEval (replace len with ((length r1) + (len - length r1)) by lia).
      iApply (array_t_own_val_merge with "Hv1 Hv2").
      nia.
    - iModIntro. rewrite lft_dead_list_app. iIntros "(Hdead1 & Hdead2)".
      iMod ("Hv1" with "Hdead1") as "Hv1". iMod ("Hv2" with "Hdead2") as "Hv2".
      iEval (replace len with ((length r1) + (len - length r1)) by lia).
      iApply (array_t_own_val_merge with "Hv1 Hv2").
      nia.
  Qed.
  Global Instance prove_with_subtype_array_val_split_inst π E L pm v1 v2 {rt} (ty : type rt) r1 r2 (len : nat) :
    ProveWithSubtype E L false pm ((v1 ++ v2) ◁ᵥ{π} r1 ++ r2 @ array_t ty len) | 20 :=
    λ T, i2p (prove_with_subtype_array_val_split π E L pm v1 v2 ty r1 r2 len T).


  (* TODO: we could strengthen this by taking into account the refinements *)
  Lemma weak_subtype_array E L {rt} (ty1 ty2 : type rt) len1 len2 rs1 rs2 T :
    ⌜len1 = len2⌝ ∗ ⌜rs1 = rs2⌝ ∗ mut_subtype E L ty1 ty2 T
    ⊢ weak_subtype E L rs1 rs2 (array_t ty1 len1) (array_t ty2 len2) T.
  Proof.
    iIntros "(<- & <- & %Hsubt & HT)".
    iIntros (??) "#CTX #HE HL". iPoseProof (full_subtype_acc with "HE HL") as "#Hincl"; first done.
    iFrame. iApply array_t_type_incl. done.
  Qed.
  Global Instance weak_subtype_array_inst E L {rt} (ty1 ty2 : type rt) len1 len2 rs1 rs2 :
    Subtype E L rs1 rs2 (array_t ty1 len1) (array_t ty2 len2) :=
    λ T, i2p (weak_subtype_array E L ty1 ty2 len1 len2 rs1 rs2 T).

  Lemma mut_subtype_array E L {rt} (ty1 ty2 : type rt) len1 len2 T :
    ⌜len1 = len2⌝ ∗ mut_subtype E L ty1 ty2 T
    ⊢ mut_subtype E L (array_t ty1 len1) (array_t ty2 len2) T.
  Proof.
    iIntros "(<- & %Hsubt & HT)".
    iSplitR; last done. iPureIntro. by eapply array_t_full_subtype.
  Qed.
  Global Instance mut_subtype_array_inst E L {rt} (ty1 ty2 : type rt) len1 len2 :
    MutSubtype E L (array_t ty1 len1) (array_t ty2 len2) :=
    λ T, i2p (mut_subtype_array E L ty1 ty2 len1 len2 T).

  Lemma mut_eqtype_array E L {rt} (ty1 ty2 : type rt) len1 len2 T :
    ⌜len1 = len2⌝ ∗ mut_eqtype E L ty1 ty2 T
    ⊢ mut_eqtype E L (array_t ty1 len1) (array_t ty2 len2) T.
  Proof.
    iIntros "(<- & %Hsubt & HT)".
    iSplitR; last done. iPureIntro.
    eapply full_subtype_eqtype.
    - eapply array_t_full_subtype. by apply full_eqtype_subtype_l.
    - eapply array_t_full_subtype. by apply full_eqtype_subtype_r.
  Qed.
  Global Instance mut_eqtype_array_inst E L {rt} (ty1 ty2 : type rt) len1 len2 :
    MutEqtype E L (array_t ty1 len1) (array_t ty2 len2) :=
    λ T, i2p (mut_eqtype_array E L ty1 ty2 len1 len2 T).

  (** ** subltype *)

  (* we use the [relate_list] mechanism *)
  Program Definition weak_subltype_list_interp {rt1 rt2} (k : bor_kind) (rs1 : list (place_rfn rt1)) (rs2 : list (place_rfn rt2)) : FoldableRelation :=
    {|
      fr_rel (E : elctx) (L : llctx) (i : nat) (lt1 : (ltype rt1)) (lt2 : (ltype rt2)) (T : iProp Σ) :=
        (∃ r1 r2,  ⌜rs1 !! i = Some r1⌝ ∗ ⌜rs2 !! i = Some r2⌝ ∗ weak_subltype E L k r1 r2 lt1 lt2 T)%I;
      fr_cap := length rs1;
      fr_inv := length rs1 = length rs2;
      fr_elim_mode := true;
      fr_core_rel E L (i : nat) (lt1 : (ltype rt1)) (lt2 : (ltype rt2))  :=
        (∃ r1 r2,  ⌜rs1 !! i = Some r1⌝ ∗ ⌜rs2 !! i = Some r2⌝ ∗ ltype_incl k r1 r2 lt1 lt2)%I;
    |}.
  Next Obligation.
    iIntros (??? rs1 rs2 E L i a b T ? ?) "#CTX #HE HL (%r1 & %r2 & %Hlook1 & %Hlook2 & Hsubt)".
    iMod ("Hsubt" with "[//] CTX HE HL") as "(Hincl & $ & $)".
    iModIntro. eauto with iFrame.
  Qed.

   (* options;
       - require homogeneous and then use mut_subltype in the assumption
       - what about array_t T <: array_t (maybe_uninit T)?
          for that, would need a pattern on replicate there too.
          this seems fine, but is difficult to implement. The problem is that we can't pattern on that easily. We'd first need to remove any leading inserts.
       TODO: Probably have both, with the first one as fallback.
     *)
  Lemma weak_subltype_list_replicate_1 (E : elctx) (L : llctx) {rt} (k : bor_kind) (lt1 : ltype rt) (lt2 : ltype rt) rs1 rs2 n ig i0 T :
    ⌜list_subequiv ig rs1 rs2⌝ ∗ mut_subltype E L lt1 lt2 T
    ⊢ relate_list E L ig (replicate n lt1) (replicate n lt2) i0 (weak_subltype_list_interp k rs1 rs2) T.
  Proof.
    iIntros "(%Heq & %Hsubt & HT)".
    iApply relate_list_replicate_elim_full; first done; last done.
    simpl. iIntros "#CTX HE HL %Hlen".
    iPoseProof (full_subltype_acc with "CTX HE HL") as "#Hincl"; first done.
    iModIntro. iIntros (i) "%Hlt %Hnel".
    specialize (Heq i) as (? & Hi).
    destruct (lookup_lt_is_Some_2 rs1 i) as (r1 & Hlook1). { lia. }
    destruct (lookup_lt_is_Some_2 rs2 i) as (r2 & Hlook2). { lia. }
    iExists r1, r2. iR. iR. assert (r1 = r2) as <-.
    { specialize (Hi Hnel). congruence. }
    iApply "Hincl".
  Qed.
  Global Instance weak_subltype_list_replicate_1_inst (E : elctx) (L : llctx) {rt} (k : bor_kind) (lt1 : ltype rt) (lt2 : ltype rt) rs1 rs2 n ig i0 :
    RelateList E L ig (replicate n lt1) (replicate n lt2) i0 (weak_subltype_list_interp k rs1 rs2) :=
    λ T, i2p (weak_subltype_list_replicate_1 E L k lt1 lt2 rs1 rs2 n ig i0 T).

  Program Definition mut_subltype_list_interp {rt} (cap : nat) (interp : bool) : FoldableRelation :=
    {|
      fr_rel (E : elctx) (L : llctx) (i : nat) (lt1 : (ltype rt)) (lt2 : (ltype rt)) (T : iProp Σ) := (mut_subltype E L lt1 lt2 T)%I;
      fr_cap := cap;
      fr_inv := True;
      fr_elim_mode := interp;
      fr_core_rel (E : elctx) (L : llctx) (i : nat) (lt1 : (ltype rt)) (lt2 : (ltype rt)) :=
        if interp then (∀ k r,  ltype_incl k r r lt1 lt2)%I else ⌜full_subltype E L lt1 lt2⌝%I;
    |}.
  Next Obligation.
    iIntros (rt _ interp E L i a b). destruct interp.
    - iIntros (???) "#CTX #HE HL (%Hsubt & $)".
      iPoseProof (full_subltype_acc with "CTX HE HL") as "#$"; first done.
      by iFrame.
    - iIntros (?) "(% & $)"; done.
  Qed.

  Lemma mut_subltype_list_replicate (E : elctx) (L : llctx) {rt} (lt1 : ltype rt) (lt2 : ltype rt) cap interp n ig i0 T :
    mut_subltype E L lt1 lt2 T
    ⊢ relate_list E L ig (replicate n lt1) (replicate n lt2) i0 (mut_subltype_list_interp cap interp) T.
  Proof.
    iIntros "(%Hsubt & HT)". destruct interp.
    - iApply relate_list_replicate_elim_full; first done; last done.
      simpl. iIntros "#CTX HE HL _".
      iPoseProof (full_subltype_acc with "CTX HE HL") as "#Hincl"; first done.
      iModIntro. iIntros (i) "%Hlt %Hnel". done.
    - iApply relate_list_replicate_elim_weak; first done; last done.
      simpl. iIntros "_". eauto.
  Qed.
  Global Instance mut_subltype_list_replicate_inst (E : elctx) (L : llctx) {rt} (lt1 : ltype rt) (lt2 : ltype rt) cap interp n ig i0 :
    RelateList E L ig (replicate n lt1) (replicate n lt2) i0 (mut_subltype_list_interp cap interp) :=
    λ T, i2p (mut_subltype_list_replicate E L lt1 lt2 cap interp n ig i0 T).

  Program Definition mut_eqltype_list_interp {rt} (cap : nat) (interp : bool) : FoldableRelation :=
    {|
      fr_rel (E : elctx) (L : llctx) (i : nat) (lt1 : (ltype rt)) (lt2 : (ltype rt)) (T : iProp Σ) := (mut_eqltype E L lt1 lt2 T)%I;
      fr_cap := cap;
      fr_inv := True;
      fr_elim_mode := interp;
      fr_core_rel E L (i : nat) (lt1 : (ltype rt)) (lt2 : (ltype rt))  :=
        if interp then (∀ k r,  ltype_incl k r r lt1 lt2 ∗ ltype_incl k r r lt2 lt1)%I else ⌜full_eqltype E L lt1 lt2⌝%I;
    |}.
  Next Obligation.
    iIntros (rt _ interp E L i a b). destruct interp.
    - iIntros (T ? ?) "#CTX #HE HL (%Hsubt & $)".
      iPoseProof (full_eqltype_acc with "CTX HE HL") as "#$"; first done.
      by iFrame.
    - iIntros (T) "(%Heqt & $)". eauto.
  Qed.

  Lemma mut_eqltype_list_replicate (E : elctx) (L : llctx) {rt} (lt1 : ltype rt) (lt2 : ltype rt) cap interp n ig i0 T :
    mut_eqltype E L lt1 lt2 T
    ⊢ relate_list E L ig (replicate n lt1) (replicate n lt2) i0 (mut_eqltype_list_interp cap interp) T.
  Proof.
    iIntros "(%Hsubt & HT)". destruct interp.
    - iApply relate_list_replicate_elim_full; first done; last done.
      simpl. iIntros "#CTX HE HL _".
      iPoseProof (full_eqltype_acc with "CTX HE HL") as "#Hincl"; first done.
      iModIntro. iIntros (i) "%Hlt %Hnel". done.
    - iApply relate_list_replicate_elim_weak; first done; last done.
      simpl. iIntros "_". eauto.
  Qed.
  Global Instance mut_eqltype_list_replicate_inst (E : elctx) (L : llctx) {rt} (lt1 : ltype rt) (lt2 : ltype rt) cap interp n ig i0 :
    RelateList E L ig (replicate n lt1) (replicate n lt2) i0 (mut_eqltype_list_interp cap interp) :=
    λ T, i2p (mut_eqltype_list_replicate E L lt1 lt2 cap interp n ig i0 T).

  Local Typeclasses Transparent weak_subltype_list_interp.
  Local Typeclasses Transparent mut_subltype_list_interp.
  Local Typeclasses Transparent mut_eqltype_list_interp.

  Lemma weak_subltype_array_evar_def E L {rt1} (def1 : type rt1) (def2 : type rt1) len1 len2 (lts1 : list (nat * ltype rt1)) (lts2 : list (nat * ltype rt1)) rs1 rs2 k T :
    ⌜def1 = def2⌝ ∗ weak_subltype E L k rs1 rs2 (ArrayLtype def1 len1 lts1) (ArrayLtype def1 len2 lts2) T
    ⊢ weak_subltype E L k rs1 rs2 (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) T.
  Proof. iIntros "(<- & $)". Qed.
  Global Instance weak_subltype_array_evar_def_inst E L {rt1} (def1 : type rt1) (def2 : type rt1) len1 len2 (lts1 : list (nat * ltype rt1)) (lts2 : list (nat * ltype rt1)) rs1 rs2 k `{!IsProtected def2} :
    SubLtype E L k rs1 rs2 (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) | 8 :=
    λ T, i2p (weak_subltype_array_evar_def E L def1 def2 len1 len2 lts1 lts2 rs1 rs2 k T).

  Lemma weak_subltype_array_evar_lts E L {rt1} (def1 : type rt1) (def2 : type rt1) len1 len2 (lts1 : list (nat * ltype rt1)) (lts2 : list (nat * ltype rt1)) rs1 rs2 k T :
    ⌜lts1 = lts2⌝ ∗ weak_subltype E L k rs1 rs2 (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts1) T
    ⊢ weak_subltype E L k rs1 rs2 (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) T.
  Proof. iIntros "(<- & $)". Qed.
  Global Instance weak_subltype_array_evar_lts_inst E L {rt1} (def1 : type rt1) (def2 : type rt1) len1 len2 (lts1 : list (nat * ltype rt1)) (lts2 : list (nat * ltype rt1)) rs1 rs2 k `{!IsProtected lts2} :
    SubLtype E L k rs1 rs2 (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) | 9 :=
    λ T, i2p (weak_subltype_array_evar_lts E L def1 def2 len1 len2 lts1 lts2 rs1 rs2 k T).

  Lemma weak_subltype_array_owned_in E L {rt1 rt2} (def1 : type rt1) (def2 : type rt2) len1 len2 (lts1 : list (nat * ltype rt1)) (lts2 : list (nat * ltype rt2)) rs1 rs2 wl T :
    (⌜len1 = len2⌝ ∗
    ∃ rs2', ⌜rs2 = #rs2'⌝ ∗
    ⌜ty_syn_type def1 = ty_syn_type def2⌝ ∗
    relate_list E L [] (interpret_iml (◁ def1) len1 lts1) (interpret_iml (◁ def2) len1 lts2) 0 (weak_subltype_list_interp (Owned false) rs1 rs2') (
      ⌜length rs2' = len1⌝ ∗ T))
    ⊢ weak_subltype E L (Owned wl) #rs1 rs2 (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) T.
  Proof.
    iIntros "(<- & %rs2' & -> & %Hst & HT)". iIntros (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(Ha & $ & (%Hlen' & $))".
    iModIntro.
    iApply array_ltype_incl_owned_in; first done.
    simpl. iIntros (?). rewrite interpret_iml_length.
    iSpecialize ("Ha" with "[] []"). { iPureIntro. lia. } {iPureIntro. lia. }
    iR.
  Admitted.
  Global Instance weak_subltype_array_owned_in_inst E L {rt1 rt2} (def1 : type rt1) (def2 : type rt2) len1 len2 (lts1 : list (nat * ltype rt1)) (lts2 : list (nat * ltype rt2)) rs1 rs2 wl :
    SubLtype E L (Owned wl) #rs1 rs2 (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) |10 :=
    λ T, i2p (weak_subltype_array_owned_in E L def1 def2 len1 len2 lts1 lts2 rs1 rs2 wl T).

  Lemma weak_subltype_array_owned E L {rt1 } (def1 : type rt1) (def2 : type rt1) len1 len2 (lts1 : list (nat * ltype rt1)) (lts2 : list (nat * ltype rt1)) rs1 rs2 wl T :
    (⌜len1 = len2⌝ ∗ ⌜rs1 = rs2⌝ ∗ ⌜ty_syn_type def1 = ty_syn_type def2⌝ ∗
      relate_list E L [] (interpret_iml (◁ def1) len1 lts1) (interpret_iml (◁ def2) len1 lts2) 0 (mut_subltype_list_interp len1 true) T)
    ⊢ weak_subltype E L (Owned wl) rs1 rs2 (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) T.
  Proof.
    iIntros "(<- & <- & %Hst & HT)". iIntros (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(Ha & $ & $)".
    iModIntro.
    iApply array_ltype_incl_owned; first done.
    simpl. rewrite interpret_iml_length.
    iSpecialize ("Ha" with "[] [//]"). { iPureIntro. lia. }
    iApply (big_sepL2_mono with "Ha"). eauto.
  Qed.
  Global Instance weak_subltype_array_owned_inst E L {rt1} (def1 : type rt1) (def2 : type rt1) len1 len2 (lts1 : list (nat * ltype rt1)) (lts2 : list (nat * ltype rt1)) rs1 rs2 wl :
    SubLtype E L (Owned wl) rs1 rs2 (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) |11 :=
    λ T, i2p (weak_subltype_array_owned E L def1 def2 len1 len2 lts1 lts2 rs1 rs2 wl T).

  Lemma weak_subltype_array_shared_in E L {rt1 rt2} (def1 : type rt1) (def2 : type rt2) len1 len2 (lts1 : list (nat * ltype rt1)) (lts2 : list (nat * ltype rt2)) rs1 rs2 κ T :
    (⌜len1 = len2⌝ ∗
    ∃ rs2', ⌜rs2 = #rs2'⌝ ∗
    ⌜ty_syn_type def1 = ty_syn_type def2⌝ ∗
    relate_list E L [] (interpret_iml (◁ def1) len1 lts1) (interpret_iml (◁ def2) len1 lts2) 0 (weak_subltype_list_interp (Shared κ) rs1 rs2') (
      ⌜length rs2' = len1⌝ ∗ T))
    ⊢ weak_subltype E L (Shared κ) #rs1 rs2 (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) T.
  Proof.
    iIntros "(<- & %rs2' & -> & %Hst & HT)". iIntros (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(Ha & $ & (%Hlen' & $))".
    iModIntro.
    iApply array_ltype_incl_shared_in; first done.
    simpl. iIntros (?). rewrite interpret_iml_length.
    iSpecialize ("Ha" with "[] []"). { iPureIntro. lia. } {iPureIntro. lia. }
    iR.
  Admitted.
  Global Instance weak_subltype_array_shared_in_inst E L {rt1 rt2} (def1 : type rt1) (def2 : type rt2) len1 len2 (lts1 : list (nat * ltype rt1)) (lts2 : list (nat * ltype rt2)) rs1 rs2 κ :
    SubLtype E L (Shared κ) #rs1 rs2 (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) |10 :=
    λ T, i2p (weak_subltype_array_shared_in E L def1 def2 len1 len2 lts1 lts2 rs1 rs2 κ T).

  Lemma weak_subltype_array_shared E L {rt1 } (def1 : type rt1) (def2 : type rt1) len1 len2 (lts1 : list (nat * ltype rt1)) (lts2 : list (nat * ltype rt1)) rs1 rs2 κ T :
    (⌜len1 = len2⌝ ∗ ⌜rs1 = rs2⌝ ∗ ⌜ty_syn_type def1 = ty_syn_type def2⌝ ∗
    relate_list E L [] (interpret_iml (◁ def1) len1 lts1) (interpret_iml (◁ def2) len1 lts2) 0 (mut_subltype_list_interp len1 true) T)
    ⊢ weak_subltype E L (Shared κ) rs1 rs2 (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) T.
  Proof.
    iIntros "(<- & <- & %Hst & HT)". iIntros (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(Ha & $ & $)".
    iModIntro.
    iApply array_ltype_incl_shared; first done.
    simpl. rewrite interpret_iml_length.
    iSpecialize ("Ha" with "[] [//]"). { iPureIntro. lia. }
    iApply (big_sepL2_mono with "Ha"). eauto.
  Qed.
  Global Instance weak_subltype_array_shared_inst E L {rt1} (def1 : type rt1) (def2 : type rt1) len1 len2 (lts1 : list (nat * ltype rt1)) (lts2 : list (nat * ltype rt1)) rs1 rs2 κ :
    SubLtype E L (Shared κ) rs1 rs2 (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) |11 :=
    λ T, i2p (weak_subltype_array_shared E L def1 def2 len1 len2 lts1 lts2 rs1 rs2 κ T).

  Lemma weak_subltype_array_base E L {rt1 } (def1 : type rt1) (def2 : type rt1) len1 len2 (lts1 : list (nat * ltype rt1)) (lts2 : list (nat * ltype rt1)) rs1 rs2 κ γ T :
    (⌜len1 = len2⌝ ∗ ⌜rs1 = rs2⌝ ∗ ⌜ty_syn_type def1 = ty_syn_type def2⌝ ∗
    relate_list E L [] (interpret_iml (◁ def1) len1 lts1) (interpret_iml (◁ def2) len1 lts2) 0 (mut_eqltype_list_interp len1 true) T)
    ⊢ weak_subltype E L (Uniq κ γ) rs1 rs2 (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) T.
  Proof.
    iIntros "(<- & <- & %Hst & HT)". iIntros (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(Ha & $ & $)".
    iModIntro.
    iApply array_ltype_incl_uniq; first done.
    simpl. rewrite interpret_iml_length.
    iSpecialize ("Ha" with "[] [//]"). { iPureIntro. lia. }
    iApply (big_sepL2_mono with "Ha"). eauto.
  Qed.
  Global Instance weak_subltype_array_base_inst E L {rt1} (def1 : type rt1) (def2 : type rt1) len1 len2 (lts1 : list (nat * ltype rt1)) (lts2 : list (nat * ltype rt1)) rs1 rs2 κ γ :
    SubLtype E L (Uniq κ γ) rs1 rs2 (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) | 20 :=
    λ T, i2p (weak_subltype_array_base E L def1 def2 len1 len2 lts1 lts2 rs1 rs2 κ γ T).

  (* for folding : *)
  Program Definition fold_overrides_list_interp {rt} (def : type rt) (cap : nat) (req : bool) : FoldablePredicate :=
    {|
      fp_pred (E : elctx) (L : llctx) (i : nat) (lt : ltype rt) (T : iProp Σ) :=
        if req then mut_subltype E L lt (◁ def)%I T else mut_eqltype E L lt (◁ def)%I T;
      fp_cap := cap;
      fp_inv := True;
      fp_elim_mode := req;
      fp_core_pred E L (i : nat) (lt : ltype rt) :=
        if req then (∀ k r, ltype_incl k r r lt (◁ def))%I else ⌜full_eqltype E L lt (◁ def)⌝%I;
    |}.
  Next Obligation.
    iIntros (rt def ? req E L i lt). destruct req.
    - iIntros (T ??) "#CTX #HE HL (%Hsubt & $)".
      iPoseProof (full_subltype_acc with "CTX HE HL") as "#Hincl"; first apply Hsubt.
      iModIntro. iFrame. done.
    - iIntros (T) "(%Heqt & $)". done.
  Qed.

  Lemma fold_overrides_list_replicate {rt} E L (def : type rt) (lt : ltype rt) n ig i0 cap (req : bool) T :
    (if req then mut_subltype E L lt (◁ def) T else mut_eqltype E L lt (◁ def) T)
    ⊢ fold_list E L ig (replicate n lt) i0 (fold_overrides_list_interp def cap req) T.
  Proof.
    destruct req; iIntros "(%Hsubt & HT)".
    - iApply fold_list_replicate_elim_full; first done; last done.
      simpl. iIntros "#CTX #HE HL _".
      iPoseProof (full_subltype_acc with "CTX HE HL")as "#Hincl"; first apply Hsubt.
      iModIntro. iIntros (i ? k r). iApply "Hincl".
    - iApply fold_list_replicate_elim_weak; first done; last done.
      simpl. iIntros "_". eauto.
  Qed.
  Global Instance fold_overrides_list_replicate_inst {rt} E L (def : type rt) (lt : ltype rt) n ig i0 cap req :
    FoldList E L ig (replicate n lt) i0 (fold_overrides_list_interp def cap req) | 20 :=
    λ T, i2p (fold_overrides_list_replicate E L def lt n ig i0 cap req T).
  Local Typeclasses Transparent fold_overrides_list_interp.

  Lemma weak_subltype_array_ofty_r E L {rt1} (def1 : type rt1) ty len1 (lts1 : list (nat * ltype rt1)) rs1 rs2 k T :
    ⌜rs1 = rs2⌝ ∗ mut_eqtype E L (array_t def1 len1) ty
      (fold_list E L [] (interpret_iml (◁ def1) len1 lts1) 0 (fold_overrides_list_interp def1 len1 true) T)
    ⊢ weak_subltype E L k rs1 rs2 (ArrayLtype def1 len1 lts1) (◁ ty) T.
  Proof.
    iIntros "(-> & %Hsubt & Hf)".
    iIntros (??) "#CTX #HE HL".
    iMod ("Hf" with "[//] CTX HE HL") as "(Ha & HL & $)".
    simpl. iSpecialize ("Ha" with "[] []").
    { simpl. rewrite interpret_iml_length. iPureIntro. lia. }
    { simpl. done. }
    iDestruct "Ha" as "#Ha".
    specialize (full_eqtype_subltype _ _ _ _ Hsubt) as Hs.
    iPoseProof (full_subltype_acc with "CTX HE HL") as "#Hb"; first apply Hs.
    iFrame. simpl.
    iModIntro. iApply ltype_incl_trans.
    { iApply (array_ltype_make_defaults). done. }
    iApply ltype_incl_trans.
    { iApply array_t_unfold_1. }
    iApply "Hb".
  Qed.
  Global Instance weak_subltype_array_ofty_r_inst E L {rt1} (def1 : type rt1) ty len1 (lts1 : list (nat * ltype rt1)) rs1 rs2 k :
    SubLtype E L k rs1 rs2 (ArrayLtype def1 len1 lts1) (◁ ty)%I | 14 :=
    λ T, i2p (weak_subltype_array_ofty_r E L def1 ty len1 lts1 rs1 rs2 k T).

  Lemma weak_subltype_array_ofty_l E L {rt1 rt2} (def1 : type rt1) (def2 : type rt2) len1 len2 (lts2 : list (nat * ltype rt2)) rs1 rs2 k T :
    weak_subltype E L k rs1 rs2 (ArrayLtype def1 len1 []) (ArrayLtype def2 len2 lts2) T
    ⊢ weak_subltype E L k rs1 rs2 (◁ array_t def1 len1) (ArrayLtype def2 len2 lts2) T.
  Proof.
    iIntros "Hsubt" (??) "#CTX #HE HL".
    iMod ("Hsubt" with "[//] CTX HE HL") as "(Ha & $ & $)".
    iModIntro. iApply ltype_incl_trans; last done.
    iApply array_t_unfold_2.
  Qed.
  Global Instance weak_subltype_array_ofty_l_inst E L {rt1 rt2} (def1 : type rt1) (def2 : type rt2) len1 len2 (lts2 : list (nat * ltype rt2)) rs1 rs2 k :
    SubLtype E L k rs1 rs2 (◁ array_t def1 len1)%I (ArrayLtype def2 len2 lts2) | 14 :=
    λ T, i2p (weak_subltype_array_ofty_l E L def1 def2 len1 len2 lts2 rs1 rs2 k T).


  (** mut_subltype *)
  Lemma mut_subltype_array E L {rt} (def1 def2 : type rt) len1 len2 (lts1 lts2 : list (nat * ltype rt)) T:
    ⌜len1 = len2⌝ ∗ ⌜ty_syn_type def1 = ty_syn_type def2⌝ ∗
    relate_list E L [] (interpret_iml (◁ def1) len1 lts1) (interpret_iml (◁ def2) len2 lts2) 0 (mut_eqltype_list_interp len1 false) T
    ⊢ mut_subltype E L (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) T.
  Proof.
    iIntros "(<- & %Hst & Hrel)".
    iPoseProof "Hrel" as "(Hr & $)".
    simpl. iSpecialize  ("Hr" with "[] [//]").
    { rewrite interpret_iml_length. iPureIntro. lia. }
    iPoseProof (big_sepL2_Forall2 with "Hr") as "%Ha".
    iPureIntro. eapply array_full_subltype; done.
  Qed.
  Global Instance mut_subltype_array_inst E L {rt} (def1 def2 : type rt) len1 len2 (lts1 lts2 : list (nat * ltype rt)) :
    MutSubLtype E L (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) | 10 :=
    λ T, i2p (mut_subltype_array E L def1 def2 len1 len2 lts1 lts2 T).

  (* evar handling *)
  Lemma mut_subltype_array_evar_def E L {rt} (def1 def2 : type rt) len1 len2 (lts1 lts2 : list (nat * ltype rt)) T `{!IsProtected def2} :
    ⌜def1 = def2⌝ ∗ mut_subltype E L (ArrayLtype def1 len1 lts1) (ArrayLtype def1 len2 lts2) T
    ⊢ mut_subltype E L (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) T.
  Proof. iIntros "(<- & $)". Qed.
  Global Instance mut_subltype_array_evar_def_inst E L {rt} (def1 def2 : type rt) len1 len2 (lts1 lts2 : list (nat * ltype rt)) `{!IsProtected def2} :
    MutSubLtype E L (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) | 8 := λ T, i2p (mut_subltype_array_evar_def E L def1 def2 len1 len2 lts1 lts2 T).

  Lemma mut_subltype_array_evar_lts E L {rt} (def1 def2 : type rt) len1 len2 (lts1 lts2 : list (nat * ltype rt)) T `{!IsProtected lts2} :
    ⌜lts1 = lts2⌝ ∗ mut_subltype E L (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts1) T
    ⊢ mut_subltype E L (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) T.
  Proof. iIntros "(<- & $)". Qed.
  Global Instance mut_subltype_array_evar_lts_inst E L {rt} (def1 def2 : type rt) len1 len2 (lts1 lts2 : list (nat * ltype rt)) `{!IsProtected lts2} :
    MutSubLtype E L (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) | 9 := λ T, i2p (mut_subltype_array_evar_lts E L def1 def2 len1 len2 lts1 lts2 T).

  (* ofty unfolding *)
  Lemma mut_subltype_array_ofty_r E L {rt} (def1 : type rt) len1 lts1 ty T :
    mut_eqtype E L (array_t def1 len1) ty (fold_list E L [] (interpret_iml (◁ def1) len1 lts1) 0 (fold_overrides_list_interp def1 len1 false) T)
    ⊢ mut_subltype E L (ArrayLtype def1 len1 lts1) (◁ ty) T.
  Proof.
    iIntros "(%Heqt & Ha & $)".
    iSpecialize ("Ha" with "[] [//]"); simpl. { rewrite interpret_iml_length. iPureIntro. lia. }
    iPoseProof (big_sepL_Forall with "Ha") as "%Ha".
    iPureIntro. eapply full_eqltype_subltype_l.
    etrans; first last. { apply full_eqtype_eqltype; last apply Heqt. apply _. }
    trans (ArrayLtype def1 len1 []); first last.
    { symmetry. eapply array_t_unfold_full_eqltype. }
    apply array_ltype_make_defaults_full_eqltype. done.
  Qed.
  Global Instance mut_subltype_array_ofty_r_inst E L {rt} (def1 : type rt) len1 lts1 ty :
    MutSubLtype E L (ArrayLtype def1 len1 lts1)%I (◁ ty)%I | 14 :=
    λ T, i2p (mut_subltype_array_ofty_r E L def1 len1 lts1 ty T).

  Lemma mut_subltype_array_ofty_l E L {rt} (def1 : type rt) (def2 : type rt) len1 len2 (lts2 : list (nat * ltype rt)) T :
    mut_subltype E L (ArrayLtype def1 len1 []) (ArrayLtype def2 len2 lts2) T
    ⊢ mut_subltype E L (◁ array_t def1 len1) (ArrayLtype def2 len2 lts2) T.
  Proof.
    iIntros "(%Hsubt & $)".
    iPureIntro. etrans; last apply Hsubt.
    apply full_eqltype_subltype_l.
    apply array_t_unfold_full_eqltype.
  Qed.
  Global Instance mut_subltype_array_ofty_l_inst E L {rt} (def1 : type rt) (def2 : type rt) len1 len2 (lts2 : list (nat * ltype rt)) :
    MutSubLtype E L (◁ array_t def1 len1)%I (ArrayLtype def2 len2 lts2) | 14 :=
    λ T, i2p (mut_subltype_array_ofty_l E L def1 def2 len1 len2 lts2 T).

  (** eqltype *)
  Lemma mut_eqltype_array E L {rt} (def1 def2 : type rt) len1 len2 (lts1 lts2 : list (nat * ltype rt)) T:
    ⌜len1 = len2⌝ ∗ ⌜ty_syn_type def1 = ty_syn_type def2⌝ ∗
    relate_list E L [] (interpret_iml (◁ def1) len1 lts1) (interpret_iml (◁ def2) len2 lts2) 0 (mut_eqltype_list_interp len1 false) T
    ⊢ mut_eqltype E L (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) T.
  Proof.
    iIntros "(<- & %Hst & Hrel)".
    iPoseProof "Hrel" as "(Hr & $)".
    simpl. iSpecialize  ("Hr" with "[] [//]").
    { rewrite interpret_iml_length. iPureIntro. lia. }
    iPoseProof (big_sepL2_Forall2 with "Hr") as "%Ha".
    iPureIntro. eapply array_full_eqltype; done.
  Qed.
  Global Instance mut_eqltype_array_inst E L {rt} (def1 def2 : type rt) len1 len2 (lts1 lts2 : list (nat * ltype rt)) :
    MutEqLtype E L (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) | 10 :=
    λ T, i2p (mut_eqltype_array E L def1 def2 len1 len2 lts1 lts2 T).

  (* evar handling *)
  Lemma mut_eqltype_array_evar_def E L {rt} (def1 def2 : type rt) len1 len2 (lts1 lts2 : list (nat * ltype rt)) T `{!IsProtected def2} :
    ⌜def1 = def2⌝ ∗ mut_eqltype E L (ArrayLtype def1 len1 lts1) (ArrayLtype def1 len2 lts2) T
    ⊢ mut_eqltype E L (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) T.
  Proof. iIntros "(<- & $)". Qed.
  Global Instance mut_eqltype_array_evar_def_inst E L {rt} (def1 def2 : type rt) len1 len2 (lts1 lts2 : list (nat * ltype rt)) `{!IsProtected def2} :
    MutEqLtype E L (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) | 8 := λ T, i2p (mut_eqltype_array_evar_def E L def1 def2 len1 len2 lts1 lts2 T).

  Lemma mut_eqltype_array_evar_lts E L {rt} (def1 def2 : type rt) len1 len2 (lts1 lts2 : list (nat * ltype rt)) T `{!IsProtected lts2} :
    ⌜lts1 = lts2⌝ ∗ mut_eqltype E L (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts1) T
    ⊢ mut_eqltype E L (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) T.
  Proof. iIntros "(<- & $)". Qed.
  Global Instance mut_eqltype_array_evar_lts_inst E L {rt} (def1 def2 : type rt) len1 len2 (lts1 lts2 : list (nat * ltype rt)) `{!IsProtected lts2} :
    MutEqLtype E L (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) | 9 := λ T, i2p (mut_eqltype_array_evar_lts E L def1 def2 len1 len2 lts1 lts2 T).

  Lemma mut_eqltype_array_ofty_r E L {rt} (def1 : type rt) len1 lts1 ty T :
    mut_eqtype E L (array_t def1 len1) ty (fold_list E L [] (interpret_iml (◁ def1) len1 lts1) 0 (fold_overrides_list_interp def1 len1 false) T)
    ⊢ mut_eqltype E L (ArrayLtype def1 len1 lts1) (◁ ty) T.
  Proof.
    iIntros "(%Heqt & Ha & $)".
    iSpecialize ("Ha" with "[] [//]"); simpl. { rewrite interpret_iml_length. iPureIntro. lia. }
    iPoseProof (big_sepL_Forall with "Ha") as "%Ha".
    iPureIntro.
    etrans; first last. { apply full_eqtype_eqltype; last apply Heqt. apply _. }
    trans (ArrayLtype def1 len1 []); first last.
    { symmetry. eapply array_t_unfold_full_eqltype. }
    apply array_ltype_make_defaults_full_eqltype. done.
  Qed.
  Global Instance mut_eqltype_array_ofty_r_inst E L {rt} (def1 : type rt) len1 lts1 ty :
    MutEqLtype E L (ArrayLtype def1 len1 lts1)%I (◁ ty)%I | 14 :=
    λ T, i2p (mut_eqltype_array_ofty_r E L def1 len1 lts1 ty T).

  Lemma mut_eqltype_array_ofty_l E L {rt} (def1 : type rt) (def2 : type rt) len1 len2 (lts2 : list (nat * ltype rt)) T :
    mut_eqltype E L (ArrayLtype def1 len1 []) (ArrayLtype def2 len2 lts2) T
    ⊢ mut_eqltype E L (◁ array_t def1 len1) (ArrayLtype def2 len2 lts2) T.
  Proof.
    iIntros "(%Hsubt & $)".
    iPureIntro. etrans; last apply Hsubt.
    apply array_t_unfold_full_eqltype.
  Qed.
  Global Instance mut_eqltype_array_ofty_l_inst E L {rt} (def1 : type rt) (def2 : type rt) len1 len2 (lts2 : list (nat * ltype rt)) :
    MutEqLtype E L (◁ array_t def1 len1)%I (ArrayLtype def2 len2 lts2) | 14 :=
    λ T, i2p (mut_eqltype_array_ofty_l E L def1 def2 len1 len2 lts2 T).

  (** Owned subtype for initialization *)
  Lemma owned_subtype_uninit_array π E L pers {rt} (ty : type rt) (st : syn_type) len r2 T :
    li_tactic (compute_layout_goal st) (λ ly1,
      li_tactic (compute_layout_goal (ty_syn_type ty)) (λ ly2,
        ⌜(ly_size ly1 = ly_size ly2 * len)%nat⌝ ∗
        owned_subtype π E L pers (replicate len #()) r2 (array_t (uninit (ty_syn_type ty)) len) (array_t ty len) T))
    ⊢ owned_subtype π E L pers () r2 (uninit st) (array_t ty len) T.
  Proof.
    rewrite /compute_layout_goal.
    iIntros "(%ly1 & %Halg1 & %ly2 & %Halg2 & %Hszeq & HT)".
    iIntros (???) "#CTX #HE HL".
    iMod ("HT" with "[//] [//] CTX HE HL") as "(%L' & Hincl & ? & ?)".
    iExists L'. iModIntro. iFrame.
    iAssert (owned_type_incl π (replicate len # ()) r2 (array_t (uninit (ty_syn_type ty)) len) (array_t ty len) -∗ owned_type_incl π () r2 (uninit st) (array_t ty len))%I as "Hw"; first last.
    { destruct pers.
      { simpl. iDestruct "Hincl" as "#Hincl". iModIntro. by iApply "Hw". }
      { simpl. by iApply "Hw". } }
    iIntros "Hincl". iDestruct "Hincl" as "(%Hszeq' & _ & Hv)".
    iSplitR; last iSplitR.
    - iPureIntro. intros ly3 ly4 Hst1 Hst2.
      simpl in *.
      assert (ly3 = ly1) as -> by by eapply syn_type_has_layout_inj.
      rewrite Hszeq.
      specialize (syn_type_has_layout_array_inv _ _ _ Hst2) as (ly2' & Hst2' & -> & ?).
      assert (ly2' = ly2) as -> by by eapply syn_type_has_layout_inj.
      done.
    - simpl; done.
    - iIntros (v) "Hun".
      iApply "Hv".
      rewrite /ty_own_val/=.
      iDestruct "Hun" as "(%ly0 & %Hly0 & %Hlyv0 & _)".
      assert (ly0 = ly1) as -> by by eapply syn_type_has_layout_inj.
      iExists _. iR.
      iSplitR. { iPureIntro. apply (use_layout_alg_size) in Hly0. lia. }
      rewrite replicate_length. iR.
      iSplitR. { rewrite /has_layout_val/mk_array_layout/ly_mult /= -Hszeq. done. }
      iApply big_sepL2_intro.
      { rewrite reshape_length !replicate_length//. }
      iModIntro. iIntros (k ?? Hlook1 Hlook2).
      apply lookup_replicate in Hlook1 as (-> & ?).
      iExists _.  iR.
      rewrite uninit_own_spec.
      iExists _. iR.
      iPureIntro. rewrite /has_layout_val.
      apply elem_of_list_lookup_2 in Hlook2.
      apply reshape_replicate_elem_length in Hlook2; first done.
      rewrite Hlyv0. lia.
  Qed.
  Global Instance owned_subtype_uninit_array_inst π E L pers {rt} (ty : type rt) st len r2 :
    OwnedSubtype π E L pers () r2 (uninit st) (array_t ty len) :=
    λ T, i2p (owned_subtype_uninit_array π E L pers ty st len r2 T).

  Lemma owned_subtype_array π E L pers {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) len r1 r2 T :
    (∃ r1' r2', ⌜r1 = replicate len #r1'⌝ ∗ ⌜r2 = replicate len #r2'⌝ ∗
      ⌜syn_type_is_layoutable (ty_syn_type ty2)⌝ ∗
      owned_subtype π E L true r1' r2' ty1 ty2 T)
    ⊢ owned_subtype π E L pers r1 r2 (array_t ty1 len) (array_t ty2 len) T.
  Proof.
    iIntros "(%r1' & %r2' & -> & -> & %Hly' & HT)".
    destruct Hly' as (ly' & Hst').
    iIntros (???) "#CTX #HE HL".
    iMod ("HT" with "[//] [//] CTX HE HL") as "(%L' & #Hincl & ? & ?)".
    iModIntro. iExists L'. iFrame.
    iApply bi.intuitionistically_intuitionistically_if. iModIntro.
    iDestruct "Hincl" as "(%Hszeq & Hsceq & Hv)".
    iSplitR; last iSplitR.
    - iPureIntro. simpl. intros ly1 ly2 Hst1 Hst2.
      apply syn_type_has_layout_array_inv in Hst1 as (ly1' & Hst1 & -> & ?).
      apply syn_type_has_layout_array_inv in Hst2 as (ly2' & Hst2 & -> & ?).
      rewrite /mk_array_layout/ly_mult/=.
      specialize (Hszeq _ _ Hst1 Hst2) as ->. done.
    - simpl. done.
    - iIntros (v) "Ha".
      rewrite {3 4}/ty_own_val /=.
      iDestruct "Ha" as "(%ly & %Hst1 & % & <- & %Hvly & Ha)".
      iExists _. iR.
      assert (ly_size ly = ly_size ly') as Hlysz. { eapply Hszeq; done. }
      rewrite -Hlysz replicate_length. iR.
      rewrite replicate_length. iR.
      iSplitR. { iPureIntro. rewrite /has_layout_val/mk_array_layout/ly_mult/=. rewrite -Hlysz.
        rewrite replicate_length in Hvly. done. }
      clear.
      iInduction len as [ | len] "IH" forall (v); simpl; first done.
      iDestruct "Ha" as "((%r1 & -> & Ha) & Hr)".
      iPoseProof ("IH" with "Hr") as "$".
      iExists _. iR. by iApply "Hv".
  Qed.
  Global Instance owned_subtype_array_inst π E L pers {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) len r1 r2 :
    OwnedSubtype π E L pers r1 r2 (array_t ty1 len) (array_t ty2 len) :=
    λ T, i2p (owned_subtype_array π E L pers ty1 ty2 len r1 r2 T).


  (** ** stratify_ltype *)
  (* 1. stratify all components
     -> Then have the new ArrayLtype.
     2. 1) If we should fold fully: subltype the core of this new array type to ◁ array_t (if it contains blocked things), and fold to Coreable (array_t).
            Or subtype it directly to array_t if it doesn't contain blocked things.
        2) Otherwise, leave the ArrayLtype as-is.

    Should stratify go to coreable (i.e., bubble blocked things up), even if it wasn't Opened previously?
     -> we should not stratify to coreable, as that imposes information loss. Would be an issue for dropping of local variables.


    //
    What happens to mut ref unfolding below?
      - We might have an OpenedLtype with homogeneous refinement.
      - this might get turned to coreable.
      - we need to fold all of them. if one of them doesn't go to the designated type, we need to go to coreable ourselves.
          (this is like bubbling up)
    Do we need this?
     - Rust's native indexing/dereferencing does use dedicated functions on mutrefs (really on slices).
       So also the drop/overwrite thing would go via an indirection.
     - Do we need it in unsafe use cases where we really directly work with the array type?
        + for Vec/VecDeque, we don't need that.
   *)

  Definition stratify_ltype_array_iter_cont_t (rt : Type) := llctx → iProp Σ → list (nat * ltype rt) → list (place_rfn rt) → iProp Σ.
  Definition stratify_ltype_array_iter (π : thread_id) (E : elctx) (L : llctx) (mu : StratifyMutabilityMode) (md : StratifyDescendUnfoldMode) (ma : StratifyAscendMode) {M} (m : M) (l : loc) (ig : list nat) {rt} (def : type rt) (len : nat) (iml : list (nat * ltype rt)) (rs : list (place_rfn rt)) (k : bor_kind) (T : stratify_ltype_array_iter_cont_t rt) : iProp Σ :=
    ∀ F, ⌜lftE ⊆ F⌝ -∗
    ⌜lft_userE ⊆ F⌝ -∗
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp L -∗
    ([∗ list] i ↦ lt; r ∈ interpret_iml (◁ def)%I len iml; rs,
      if decide (i ∉ ig) then (⌜ltype_st lt = ty_syn_type def⌝ ∗ (l offsetst{ty_syn_type def}ₗ i) ◁ₗ[π, k] r @ lt) else True) ={F}=∗
    ∃ (L' : llctx) (R' : iProp Σ) (iml' : list (nat * ltype rt)) (rs' : list (place_rfn rt)),
      ⌜length rs' = length rs⌝ ∗
      logical_step F (([∗ list] i ↦ lt; r ∈ interpret_iml (◁ def)%I len iml'; rs', if decide (i ∉ ig) then (⌜ltype_st lt = ty_syn_type def⌝ ∗ (l offsetst{ty_syn_type def}ₗ i) ◁ₗ[π, k] r @ lt) else True) ∗ R') ∗
      llctx_interp L' ∗
      T L' R' iml' rs'.
  Class StratifyLtypeArrayIter (π : thread_id) (E : elctx) (L : llctx) (mu : StratifyMutabilityMode) (md : StratifyDescendUnfoldMode) (ma : StratifyAscendMode) {M} (m : M) (l : loc) (ig : list nat) {rt} (def : type rt) (len : nat) (iml : list (nat * ltype rt)) (rs : list (place_rfn rt)) (k : bor_kind) : Type :=
    stratify_ltype_array_iter_proof T : iProp_to_Prop (stratify_ltype_array_iter π E L mu md ma m l ig def len iml rs k T).


  Lemma stratify_ltype_array_iter_nil π E L mu md ma {M} (m : M) (l : loc) {rt} (def : type rt) (len : nat) (rs : list (place_rfn rt)) k ig (T : stratify_ltype_array_iter_cont_t rt) :
    T L True [] rs
    ⊢ stratify_ltype_array_iter π E L mu md ma m l ig def len [] rs k T.
  Proof.
    iIntros "HT". iIntros (???) "#CTX #HE HL Hl".
    iModIntro. iExists L, True%I, [], rs.
    iFrame. simpl. iR. iApply logical_step_intro; eauto.
  Qed.
  Global Instance stratify_ltype_array_iter_nil_inst π E L mu md ma {M} (m : M) (l : loc) {rt} (def : type rt) (len : nat) (rs : list (place_rfn rt)) k ig :
    StratifyLtypeArrayIter π E L mu md ma m l ig def len [] rs k := λ T, i2p (stratify_ltype_array_iter_nil π E L mu md ma m l def len rs k ig T).

  Import EqNotations.
  Lemma stratify_ltype_array_iter_cons_no_ignore π E L mu mdu ma {M} (m : M) (l : loc) (ig : list nat) {rt} (def : type rt) (rs : list (place_rfn rt)) (len : nat) (iml : list (nat * ltype rt)) (lt : ltype rt) j k T `{Hnel : !CanSolve (j ∉ ig)%nat} :
    ⌜j < len⌝ ∗ (∀ r, ⌜rs !! j = Some r⌝ -∗
    stratify_ltype_array_iter π E L mu mdu ma m l (j :: ig) def len iml rs k (λ L2 R2 iml2 rs2,
      stratify_ltype π E L2 mu mdu ma m (l offsetst{ty_syn_type def}ₗ j) lt r k (λ L3 R3 rt3 lty3 r3,
        match ltype_blocked_lfts lty3 with
        | [] =>
            (* directly fold completely *)
            ∃ r4, weak_subltype E L3 k r3 r4 lty3 (◁ def) (T L3 (R3 ∗ R2) ((j, ◁ def) :: iml2) (<[j := r4]> rs2))
        | _ =>
            (* we directly try to go to Coreable here in order to use the syntactic hint by [def] on which refinement type we need to go to.
                If arrays supported heterogeneous refinements, we could also defer this. *)
            (*∃ (Heq : rt3 = rt), T L3 (R3 ∗ R2) ((j, rew Heq in lty3) :: iml2) (<[j := rew Heq in r3]> rs2)*)
            ⌜if k is Owned _ then True else False⌝ ∗ (* we cannot have blocked lfts below shared; TODO: also allow Uniq *)
            ∃ r4, weak_subltype E L3 k r3 r4 (ltype_core lty3) (◁ def) (T L3 (R3 ∗ R2) ((j, CoreableLtype (ltype_blocked_lfts lty3) (◁ def)) :: iml2) (<[j := r4]> rs2))
        end)))
    ⊢ stratify_ltype_array_iter π E L mu mdu ma m l ig def len ((j, lt) :: iml) rs k T.
  Proof.
    iIntros "(%Hlen & HT)". iIntros (???) "#CTX #HE HL Hl".
    simpl.
    iPoseProof (big_sepL2_length with "Hl") as "%Hlen'".
    rewrite insert_length interpret_iml_length in Hlen'. subst len.
    edestruct (lookup_lt_is_Some_2 rs j) as (r & Hlook); first done.
    rewrite -{5}(list_insert_id _ _ _ Hlook).

    iPoseProof (big_sepL2_insert (interpret_iml (◁ def)%I (length rs) iml) rs j lt r (λ i lt r, if decide (i ∉ ig) then (⌜ltype_st lt = ty_syn_type def⌝ ∗ (l offsetst{ty_syn_type def}ₗ i) ◁ₗ[ π, k] r @ lt) else True)%I 0) as "(Ha & _)".
    { rewrite interpret_iml_length. done. }
    { done. }
    iDestruct ("Ha" with "Hl") as "(Hl & Hl2)". iClear "Ha".
    simpl.
    iMod ("HT" with "[//] [//] [//] CTX HE HL [Hl2]") as "(%L2' & %R2' & %iml2 & %rs2 & %Hleneq & Hstep & HL & HT)".
    { iApply (big_sepL2_mono with "Hl2"). intros ? ? ? Hlook1 Hlook2.
      case_decide.
      { subst. iIntros "_". rewrite decide_False; first done. set_solver. }
      iIntros "Ha". case_decide.
      - rewrite decide_True; first done. set_solver.
      - rewrite decide_False; first done. set_solver. }
    unfold CanSolve in *. rewrite decide_True; last set_solver.
    iDestruct "Hl" as "(%Hst & Hl)".
    iMod ("HT" with "[//] [//] CTX HE HL Hl") as "(%L3 & %R3 & %rt' & %lt' & %r' & HL & %Hst' & Hstep' & HT)".
    destruct (ltype_blocked_lfts lt') eqn:Hbl.
    - iDestruct "HT" as "(%r4 & HT)".
      iMod ("HT" with "[//] CTX HE HL") as "(#Hincl & HL & HT)".
      iDestruct "Hincl" as "(%Hsteq & Hincl & _)".
      iExists _, _, _, _. iFrame.
      iSplitR. { iPureIntro. rewrite insert_length//. }
      iApply logical_step_fupd.
      iApply (logical_step_compose with "Hstep").
      iApply (logical_step_compose with "Hstep'").
      iApply logical_step_intro.
      iIntros "!> (Hl & $) (Hl2 & $)".
      simpl.
      iPoseProof (big_sepL2_insert (interpret_iml (◁ def)%I (length rs2) iml2) rs2 j (◁ def)%I r4 (λ i lt r, if decide (i ∉ ig) then (⌜ltype_st lt = ty_syn_type def⌝ ∗ (l offsetst{ty_syn_type def}ₗ i) ◁ₗ[ π, k] r @ lt) else True)%I 0) as "(_ & Ha)".
      { rewrite interpret_iml_length. lia. }
      { lia. }
      iMod (ltype_incl'_use with "Hincl Hl") as "Hl"; first done.
      rewrite -Hleneq. iApply "Ha".
      iSplitL "Hl".
      { rewrite decide_True; last set_solver. iFrame. rewrite -Hsteq -Hst'. done. }
      iApply (big_sepL2_mono with "Hl2").
      iIntros (k0 ? ? Hlook1 Hlook2) "Ha".
      destruct (decide (k0 = j)); first done.
      simpl. destruct (decide (k0 ∉ ig)); last done.
      rewrite decide_True; last set_solver. done.
    - (* *)
      iDestruct "HT" as "(%Hown & %r4 & HT)".
      iMod ("HT" with "[//] CTX HE HL") as "(#Hincl & HL & HT)".
      iDestruct "Hincl" as "(%Hsteq & Hincl & _)".
      iExists _, _, _, _. iFrame.
      iSplitR. { iPureIntro. rewrite insert_length//. }
      iApply logical_step_fupd.
      iApply (logical_step_compose with "Hstep").
      iApply (logical_step_compose with "Hstep'").
      iApply logical_step_intro.
      iIntros "!> (Hl & $) (Hl2 & $)".
      simpl.
      iPoseProof (big_sepL2_insert (interpret_iml (◁ def)%I (length rs2) iml2) rs2 j (CoreableLtype (ltype_blocked_lfts lt') (◁ def))%I r4 (λ i lt r, if decide (i ∉ ig) then (⌜ltype_st lt = ty_syn_type def⌝ ∗ (l offsetst{ty_syn_type def}ₗ i) ◁ₗ[ π, k] r @ lt) else True)%I 0) as "(_ & Ha)".
      { rewrite interpret_iml_length. lia. }
      { lia. }
      rewrite -Hleneq -Hbl. iApply "Ha". iClear "Ha".
      iSplitL "Hl".
      + iModIntro. rewrite decide_True; last set_solver.
        simp_ltypes. iR.
        destruct k as [ wl | |]; [ | done..].
        (* TODO this should also work for Uniq -- the only problem is that we need to split it up into the observation. Maybe we should just have a generic lemma for that for all ltypes. *)
        rewrite ltype_own_coreable_unfold /coreable_ltype_own.
        iPoseProof (ltype_own_has_layout with "Hl") as "(%ly & %Halg & %Hly)".
        iPoseProof (ltype_own_loc_in_bounds with "Hl") as "#Hlb"; first done.
        iExists ly. simp_ltypes.
        match goal with H : ty_syn_type def = ltype_st lt' |- _ => rename H into Hsteq end.
        rewrite Hsteq. iR.
        simpl. rewrite -Hsteq. iR. iR.
        iIntros "Hdead".
        iPoseProof (imp_unblockable_blocked_dead lt') as "(_ & #Himp)".
        iMod ("Himp" with "Hdead Hl") as "Hl". rewrite !ltype_own_core_equiv.
        iMod (ltype_incl'_use with "Hincl Hl") as "Hl"; first done.
        simp_ltypes. done.
      + iApply (big_sepL2_mono with "Hl2").
        iIntros (k0 ? ? Hlook1 Hlook2) "Ha".
        destruct (decide (k0 = j)); first done.
        simpl. destruct (decide (k0 ∉ ig)); last done.
        rewrite decide_True; last set_solver. done.
  Qed.
  Global Instance stratify_ltype_array_iter_cons_no_ignore_inst π E L mu md ma {M} (m : M) (l : loc) ig {rt} (def : type rt) (len : nat) (rs : list (place_rfn rt)) iml lt (j : nat) k `{Hnel : !CanSolve (j ∉ ig)%nat} :
    StratifyLtypeArrayIter π E L mu md ma m l ig def len ((j, lt) :: iml) rs k := λ T, i2p (stratify_ltype_array_iter_cons_no_ignore π E L mu md ma m l ig def rs len iml lt j k T).

  Lemma stratify_ltype_array_iter_cons_ignore π E L mu mdu ma {M} (m : M) (l : loc) (ig : list nat) {rt} (def : type rt) (rs : list (place_rfn rt)) (len : nat) (iml : list (nat * ltype rt)) (lt : ltype rt) j k T `{Hnel : !CanSolve (j ∈ ig)%nat} :
    ⌜j < len⌝ ∗ stratify_ltype_array_iter π E L mu mdu ma m l (ig) def len iml rs k T
    ⊢ stratify_ltype_array_iter π E L mu mdu ma m l ig def len ((j, lt) :: iml) rs k T.
  Proof.
    iIntros "(%Hlen & HT)". iIntros (???) "#CTX #HE HL Hl".
    unfold CanSolve in *.
    iPoseProof (big_sepL2_length with "Hl") as "%Hlen'".
    rewrite insert_length interpret_iml_length in Hlen'. subst len.
    iMod ("HT" with "[//] [//] CTX HE HL [Hl]") as "(%L2 & %R2 & %iml2 & %rs2 & %Hleneq & Hstep & HL & HT)".
    { edestruct (lookup_lt_is_Some_2 rs j) as (r & Hlook). { lia. }
      rewrite -{2}(list_insert_id _ _ _ Hlook).
      simpl.
      iPoseProof (big_sepL2_insert (interpret_iml (◁ def)%I (length rs) iml) rs j lt r (λ i lt r, if decide (i ∉ ig) then (⌜ltype_st lt = ty_syn_type def⌝ ∗ (l offsetst{ty_syn_type def}ₗ i) ◁ₗ[ π, k] r @ lt) else True)%I 0) as "(Ha & _)".
      { rewrite interpret_iml_length. done. }
      { done. }
      iDestruct ("Ha" with "Hl") as "(_ & Hl)". iClear "Ha".
      iApply (big_sepL2_mono with "Hl"). iIntros (??? Hlook1 Hlook2) "Ha".
      case_decide. { rewrite decide_False; first done. set_solver. }
      simpl. done.
    }
    iExists _, _, _, _. iFrame.
    done.
  Qed.
  Global Instance stratify_ltype_array_iter_cons_ignore_inst π E L mu md ma {M} (m : M) (l : loc) ig {rt} (def : type rt) (len : nat) (rs : list (place_rfn rt)) iml lt (j : nat) k `{Hnel : !CanSolve (j ∈ ig)%nat} :
    StratifyLtypeArrayIter π E L mu md ma m l ig def len ((j, lt) :: iml) rs k := λ T, i2p (stratify_ltype_array_iter_cons_ignore π E L mu md ma m l ig def rs len iml lt j k T).

  Lemma stratify_ltype_array_owned {rt} π E L mu mdu ma {M} (m : M) l (def : type rt) len iml rs wl (T : stratify_ltype_cont_t) :
    stratify_ltype_array_iter π E L mu mdu ma m l [] def len iml rs (Owned false) (λ L2 R2 iml2 rs2,
      T L2 R2 _ (ArrayLtype def len iml2) (#rs2))
    ⊢ stratify_ltype π E L mu mdu ma m l (ArrayLtype def len iml) (#rs) (Owned wl) T.
  Proof.
    iIntros "HT". iIntros (???) "#CTX #HE HL Hl".
    rewrite ltype_own_array_unfold /array_ltype_own.
    iDestruct "Hl" as "(%ly & %Halg & %Hsz & %Hly & Hlb & Hcreds & %r' & <- & %Hlen & Hl)". subst len.
    iMod (maybe_use_credit with "Hcreds Hl") as "(Hcred & Hat & Hl)"; first done.
    iMod ("HT" with "[//] [//] CTX HE HL [Hl]") as "(%L2 & %R2 & %iml2 & %rs2 & %Hleneq & Hstep & HL & HT)".
    { iApply (big_sepL2_mono with "Hl"). intros ? ? ? HLook1 Hlook2.
      rewrite /OffsetLocSt /use_layout_alg' Halg/=. done. }
    iModIntro. iExists L2, R2, _, _, _. iFrame. simp_ltypes. iR.
    iApply logical_step_fupd.
    iApply (logical_step_compose with "Hstep").
    iApply (logical_step_intro_maybe with "Hat").
    iIntros "Hcred2 !> (Ha & $)".
    iModIntro.
    rewrite ltype_own_array_unfold /array_ltype_own.
    iExists _. iFrame "∗%".
    iExists _. iR. iR. iNext.
    iApply (big_sepL2_mono with "Ha").
    intros ??? Hlook1 Hlook2.
    rewrite /OffsetLocSt /use_layout_alg' Halg/=. done.
  Qed.
  Global Instance stratify_ltype_array_owned_inst {rt} π E L mu mdu ma {M} (m : M) l (def : type rt) len iml rs wl :
    StratifyLtype π E L mu mdu ma m l (ArrayLtype def len iml) (#rs) (Owned wl) :=
    λ T, i2p (stratify_ltype_array_owned π E L mu mdu ma m l def len iml rs wl T).

  (* TODO Uniq *)

  (** ** prove_place_cond instances *)
  (* TODO: should probably augment FoldableRelation to be able to pass something to the continuation. *)
  (*
  Program Definition prove_place_cond_list_interp {rt1 rt2} (k : bor_kind) (len : nat) : FoldableRelation :=
    {|
      fr_rel (E : elctx) (L : llctx) (i : nat) (lt1 : (ltype rt1)) (lt2 : (ltype rt2)) (T : iProp Σ) :=
        (prove_place_cond E L k lt1 lt2 (λ upd, T))%I;
      fr_cap := len;
      fr_inv := True;
      fr_core_rel (E : elctx) (L : llctx) (i : nat) (lt1 : (ltype rt1)) (lt2 : (ltype rt2))  :=
        (∃ upd : access_result rt1 rt2,
          match upd with
          | ResultWeak _ => typed_place_cond_ty k lt1 lt2
          | ResultStrong => ⌜ltype_st lt1 = ltype_st lt2⌝%I
          end)%I
    |}.
  Next Obligation.
    iIntros (???? ? E L i a b T ?) "#CTX #HE HL Hcond".
    iMod ("Hcond" with "[//] CTX HE HL") as "($ & Hincl)".
    iDestruct "Hincl" as "(%upd & ? & $)".
    iModIntro. eauto with iFrame.
  Qed.
  Global Typeclasses Opaque prove_place_cond_list_interp.
   *)

  (* These need to have a lower priority than the ofty_refl instance (level 2) and the unblocking instances (level 5), but higher than the trivial "no" instance *)
  (* TODO: similar unfolding for array
  Lemma prove_place_cond_unfold_mut_l E L {rt1 rt2} `{Inhabited rt1} (ty : type rt1) (lt : ltype rt2) κ k T :
    prove_place_cond E L k (MutLtype (◁ ty) κ) lt T -∗
    prove_place_cond E L k (◁ (mut_ref ty κ)) lt T.
  Proof.
    iApply prove_place_cond_eqltype_l. apply symmetry. apply mut_ref_unfold_full_eqltype; done.
  Qed.
  Global Instance prove_place_cond_unfold_mut_l_inst E L {rt1 rt2} `{Inhabited rt1} (ty : type rt1) (lt : ltype rt2) κ k :
    ProvePlaceCond E L k (◁ (mut_ref ty κ))%I lt | 10 := λ T, i2p (prove_place_cond_unfold_mut_l E L ty lt κ k T).
  Lemma prove_place_cond_unfold_mut_r E L {rt1 rt2} `{Inhabited rt1} (ty : type rt1) (lt : ltype rt2) κ k T :
    prove_place_cond E L k lt (MutLtype (◁ ty) κ) T -∗
    prove_place_cond E L k lt (◁ (mut_ref ty κ)) T.
  Proof.
    iApply prove_place_cond_eqltype_r. apply symmetry. apply mut_ref_unfold_full_eqltype; done.
  Qed.
  Global Instance prove_place_cond_unfold_mut_r_inst E L {rt1 rt2} `{Inhabited rt1} (ty : type rt1) (lt : ltype rt2) κ k :
    ProvePlaceCond E L k lt (◁ (mut_ref ty κ))%I | 10 := λ T, i2p (prove_place_cond_unfold_mut_r E L ty lt κ k T).
   *)
  (*
  Lemma prove_place_cond_array_ltype E L {rt} (def1 def2 : type rt) (lts1 : ltype rt) (lts2 : ltype rt) len1 len2 κ1 κ2 k T :
    ⌜len1 = len2⌝ ∗ ⌜def1 = def2⌝ ∗
    (*prove_place_cond E L k lt1 lt2 (λ upd, T $ access_result_lift (λ rt, (place_rfn rt * gname)%type) upd) -∗*)
    prove_place_cond E L k (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) T.
  Proof.
  Abort.
   *)
  (*Global Instance prove_place_cond_mut_ltype_inst E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κ1 κ2 k :*)
    (*ProvePlaceCond E L k (MutLtype lt1 κ1) (MutLtype lt2 κ2) | 5 := λ T, i2p (prove_place_cond_mut_ltype E L lt1 lt2 κ1 κ2 k T).*)


  (* TODO phrase this with fold_list instead *)
  (* Iteration is controlled by refinement [rs] *)
  Definition resolve_ghost_iter_cont_t rt : Type := llctx → list (place_rfn rt) → iProp Σ → bool → iProp Σ.
  Definition resolve_ghost_iter {rt} (π : thread_id) (E : elctx) (L : llctx) (rm : ResolutionMode) (lb : bool) (l : loc) (st : syn_type) (lts : list (ltype rt)) (b : bor_kind) (rs : list (place_rfn rt)) (ig : list nat) (i0 : nat) (T : resolve_ghost_iter_cont_t rt) : iProp Σ :=
    (∀ F : coPset,
      ⌜lftE ⊆ F⌝ -∗
      ⌜lft_userE ⊆ F⌝ -∗
      rrust_ctx -∗
      elctx_interp E -∗
      llctx_interp L -∗
      ⌜length lts = (length rs)%nat⌝ -∗
      ([∗ list] i ↦ r; lt ∈ rs; lts, if decide ((i + i0) ∈ ig) then True else (l offsetst{st}ₗ i) ◁ₗ[ π, b] r @ lt) ={F}=∗
      ∃ (L' : llctx) (rs' : list $ place_rfn rt) (R : iPropI Σ) (progress : bool),
      maybe_logical_step lb F (([∗ list] i ↦ r; lt ∈ rs'; lts, if decide ((i + i0) ∈ ig) then True else (l offsetst{st}ₗ i) ◁ₗ[ π, b] r @ lt) ∗ R) ∗
      llctx_interp L' ∗ T L' rs' R progress).
  Class ResolveGhostIter {rt} (π : thread_id) (E : elctx) (L : llctx) (rm : ResolutionMode) (lb : bool) (l : loc) (st : syn_type) (lts : list (ltype rt)) (b : bor_kind) (rs : list (place_rfn rt)) (ig : list nat) (i0 : nat) : Type :=
    resolve_ghost_iter_proof T : iProp_to_Prop (resolve_ghost_iter π E L rm lb l st lts b rs ig i0 T).
  Global Hint Mode ResolveGhostIter + + + + + + + + + + + + + : typeclass_instances.

  Lemma resolve_ghost_iter_cons π E L rm lb l st {rt} (lts : list (ltype rt)) b (r : place_rfn rt) (rs : list (place_rfn rt)) ig (i0 : nat) T :
    (∃ lt lts', ⌜lts = lt :: lts'⌝ ∗
      resolve_ghost π E L rm lb (l offsetst{st}ₗ i0) lt b r (λ L2 r' R progress,
        resolve_ghost_iter π E L2 rm lb l st lts' b rs ig (S i0) (λ L3 rs2 R2 progress',
        T L3 (r' :: rs2) (R ∗ R2) (orb progress  progress'))))
    ⊢
    resolve_ghost_iter π E L rm lb l st lts b (r :: rs) ig i0 T.
  Proof.
  Admitted.
  Global Instance resolve_ghost_iter_cons_inst π E L rm lb l st {rt} (lts : list (ltype rt)) b (r : place_rfn rt) rs ig i0 :
    ResolveGhostIter π E L rm lb l st lts b (r :: rs) ig i0 := λ T, i2p (resolve_ghost_iter_cons π E L rm lb l st lts b r rs ig i0 T).

  Lemma resolve_ghost_iter_nil π E L rm lb l st {rt} (lts : list (ltype rt)) b ig i0 T :
    T L [] True%I true
    ⊢ resolve_ghost_iter π E L rm lb l st lts b [] ig i0 T.
  Proof.
  Admitted.
  Global Instance resolve_ghost_iter_nil_inst π E L rm lb l st {rt} (lts : list (ltype rt)) b ig i0 :
    ResolveGhostIter π E L rm lb l st lts b [] ig i0 := λ T, i2p (resolve_ghost_iter_nil π E L rm lb l st lts b ig i0 T).
End rules.

Section value.
  Context `{!typeGS Σ}.
  Lemma value_t_untyped_to_array  π v vs n ly :
    v ◁ᵥ{π} vs @ value_t (UntypedSynType (mk_array_layout ly n)) -∗
    v ◁ᵥ{π} (fmap (M:=list) PlaceIn $ reshape (replicate n (ly_size ly)) vs) @ (array_t (value_t (UntypedSynType ly)) n).
  Proof.
  Admitted.
  Lemma value_t_untyped_from_array π v vs n ly :
    v ◁ᵥ{π} (fmap (M:=list) PlaceIn $ reshape (replicate n (ly_size ly)) vs) @ (array_t (value_t (UntypedSynType ly)) n) -∗
    v ◁ᵥ{π} vs @ value_t (UntypedSynType (mk_array_layout ly n)).
  Proof.
  Admitted.

  Lemma ofty_value_t_untyped_to_array π l vs ly n :
    (l ◁ₗ[π, Owned false] #vs @ ◁ value_t (UntypedSynType (mk_array_layout ly n)))%I -∗
    l ◁ₗ[π, Owned false] #(fmap (M:=list) PlaceIn $ reshape (replicate n (ly_size ly)) vs) @ ◁ (array_t (value_t (UntypedSynType ly)) n).
  Proof.
  Admitted.
  Lemma ofty_value_t_untyped_from_array  π l vs ly n :
    (l ◁ₗ[π, Owned false] #(fmap (M:=list) PlaceIn $ reshape (replicate n (ly_size ly)) vs) @ ◁ (array_t (value_t (UntypedSynType ly)) n))%I -∗
    (l ◁ₗ[π, Owned false] #vs @ ◁ value_t (UntypedSynType (mk_array_layout ly n)))%I.
  Proof.
  Admitted.

  Lemma ofty_value_t_has_length F π l v st ly :
    lftE ⊆ F →
    syn_type_has_layout st ly →
    l ◁ₗ[π, Owned false] #v @ (◁ value_t st)%I ={F}=∗
    ⌜length v = ly_size ly⌝ ∗ l ◁ₗ[π, Owned false] #v @ (◁ value_t st)%I.
  Proof.
    iIntros (? Hst) "Hl".
  Admitted.
End value.



Section offset_ptr.
  Context `{!typeGS Σ}.

  Program Definition offset_ptr_t st : type (loc * nat) := {|
    st_own π (p : loc * nat) v := let '(l, off) := p in ⌜v = l offsetst{st}ₗ off⌝%I;
    st_syn_type := PtrSynType;
    st_has_op_type ot mt := is_ptr_ot ot;
  |}.
  Next Obligation.
    iIntros (st π [l off] v ->). iExists void*. eauto.
  Qed.
  Next Obligation.
    iIntros (st ot mt Hot).
    destruct ot; try done.
    rewrite Hot. done.
  Qed.
  Next Obligation.
    iIntros (st π [l off] v). apply _.
  Qed.
  Next Obligation.
    iIntros (st ot mt sts π [l off] v Hot) "Hv".
    simpl in Hot. iPoseProof (mem_cast_compat_loc (λ v, ⌜v = l offsetst{st}ₗ off⌝)%I with "Hv") as "%Hid"; first done.
    { iIntros "->". eauto. }
    destruct mt; [done | | done].
    rewrite Hid. done.
  Qed.

  Global Instance offset_ptr_t_copy st : Copyable (offset_ptr_t st).
  Proof. apply _. Qed.
End offset_ptr.

Section offset_rules.
  Context `{!typeGS Σ}.

  (*
     In general, I think I want:
     - a type judgment to cast a type to an array type, into which I can index.
     - then I want to look up
     - then I want to do the place access for the array's element.

     Then for the subsumption (prove with subtype):
     - for now only can do Onwed false. in general, would want to have later credits to do that.
        How does it work for Shared though? need a later credit there.
        Having just a logical step also does not help here.
        TODO: really figure this out.
        I guess I should really just have some later credits in the post of ptr::add, and have a introduce_with_hooks for that.

     Ideally: should formulate this generalically, for a generalized version of SimplifyHyp, maybe.
     Then I can use it for both typed_place and subsume_full. Look at RefinedC for that.
  *)
  (* TODO maybe we also generally want this to unblock/stratify first? *)
  Definition typed_array_access_cont_t : Type := ∀ (rt' : Type), type rt' → nat → list (nat * ltype rt') → list (place_rfn rt') → bor_kind → ∀ rte, ltype rte → place_rfn rte → iProp Σ.
  Definition typed_array_access (π : thread_id) (E : elctx) (L : llctx) (base : loc) (off : nat) (st : syn_type) {rt} (lt : ltype rt) (r : place_rfn rt) (k : bor_kind) (T : typed_array_access_cont_t) : iProp Σ :=
    ∀ F, ⌜lftE ⊆ F⌝ -∗
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp L -∗
    base ◁ₗ[π, k] r @ lt ={F}=∗
    ∃ k' rt' (ty' : type rt') (len : nat) (iml : list (nat * ltype rt')) rs' (rte : Type) re (lte : ltype rte),
      (* updated array assignment *)
      base ◁ₗ[π, k'] #rs' @ ArrayLtype ty' len iml ∗
      (base offsetst{st}ₗ off) ◁ₗ[π, k'] re @ lte ∗
      llctx_interp L ∗
      T _ ty' len iml rs' k' rte lte re.
  Class TypedArrayAccess (π : thread_id) (E : elctx) (L : llctx) (base : loc) (off : nat) (st : syn_type) {rt} (lt : ltype rt) (r : place_rfn rt) (k : bor_kind) : Type :=
    typed_array_access_proof T : iProp_to_Prop (typed_array_access π E L base off st lt r k T).


  Lemma typed_array_access_unfold π E L base off st {rt} (ty : type rt) len (rs : place_rfn (list (place_rfn rt))) k T :
    typed_array_access π E L base off st (ArrayLtype ty len []) rs k T
    ⊢ typed_array_access π E L base off st (◁ array_t ty len) rs k T.
  Proof.
    iIntros "HT". iIntros (??) "#CTX #HE HL Hl".
    iPoseProof (array_t_unfold k ty len rs) as "((_ & HIncl & _) & _)".
    iMod (ltype_incl'_use with "HIncl Hl") as "Hl"; first done.
    iApply ("HT" with "[//] CTX HE HL Hl").
  Qed.
  Global Instance typed_array_access_unfold_inst π E L base off st {rt} (ty : type rt) len rs k :
    TypedArrayAccess π E L base off st (◁ array_t ty len)%I rs k :=
    λ T, i2p (typed_array_access_unfold π E L base off st ty len rs k T).

  (* TODO make this. first have some theory for converting Owned true to Owned false with a credit *)
  Lemma typed_array_access_array_owned π E L base off st {rt} (ty : type rt) len iml rs (wl : bool) (T : typed_array_access_cont_t) :
    (⌜off < len⌝ ∗ (if wl then £ 1 else True) ∗
      ∀ lt r, ⌜interpret_iml (◁ ty)%I len iml !! off = Some lt⌝ -∗ ⌜rs !! off = Some r⌝ -∗
      T _ ty len ((off, AliasLtype _ st (base offsetst{st}ₗ off)) :: iml) (rs) (Owned false) _ lt r)
    ⊢ typed_array_access π E L base off st (ArrayLtype ty len iml) (#rs) (Owned wl) T.
  Proof.
    iIntros "(%Hoff & Hcred & HT)".
    iIntros (??) "#CTX #HE HL Hl".
  Abort.

  (* NOTE: this will misbehave if we've moved the value out before already!
     But in that case, the subsumption for offset_ptr will not trigger, because we've got the location assignment in context which will be found with higher priority.
  *)
  Lemma typed_array_access_array_owned_false π E L base off st {rt} (ty : type rt) len iml rs (T : typed_array_access_cont_t) :
    (⌜off < len⌝ ∗ ⌜st = ty_syn_type ty⌝ ∗ ∀ lt r, ⌜interpret_iml (◁ ty)%I len iml !! off = Some lt⌝ -∗ ⌜rs !! off = Some r⌝ -∗
      T _ ty len ((off, AliasLtype _ st (base offsetst{st}ₗ off)) :: iml) (rs) (Owned false) _ lt r)
    ⊢ typed_array_access π E L base off st (ArrayLtype ty len iml) (#rs) (Owned false) T.
  Proof.
    iIntros "(%Hoff & %Hst & HT)".
    iIntros (??) "#CTX #HE HL Hl".
    iPoseProof (array_ltype_acc_owned' with "Hl") as "(%ly & %Halg & % & % & Hlb & >(Hb & Hcl))"; first done.
    iPoseProof (big_sepL2_length with "Hb") as "%Hlen".
    rewrite interpret_iml_length in Hlen.
    specialize (lookup_lt_is_Some_2 rs off) as (r & Hr).
    { lia. }
    specialize (lookup_lt_is_Some_2 (interpret_iml (◁ ty)%I len iml) off) as (lt & Hlt).
    { rewrite interpret_iml_length. lia. }
    iPoseProof (big_sepL2_insert_acc _ _ _ off with "Hb") as "((%Hst' & Hel) & Hcl_b)"; [done.. | ].
    iPoseProof (ltype_own_make_alias false _ _ r with "Hel [//]") as "(Hel & Halias)".
    iPoseProof ("Hcl_b" $! (AliasLtype _ (ty_syn_type ty) (base offsetst{st}ₗ off)) r with "[Halias]") as "Ha".
    { simp_ltypes. iR. rewrite /OffsetLocSt /use_layout_alg' Hst Halg /=. rewrite Hst'. done. }
    iMod ("Hcl" $! _ ty ((off, AliasLtype rt st (base offsetst{st}ₗ off)) :: iml) rs with "[//] [//] [Ha]") as "Ha".
    { simpl. rewrite (list_insert_id rs off r); last done. rewrite Hst.  done. }
    iPoseProof ("HT" with "[//] [//]") as "HT".
    iModIntro. iExists _, _, _, _, _, _, _. iExists _, _. iFrame.
    rewrite /OffsetLocSt /use_layout_alg' Hst Halg//.
  Qed.
  Global Instance typed_array_access_owned_inst π E L base off st {rt} (ty : type rt) len iml rs :
    TypedArrayAccess π E L base off st (ArrayLtype ty len iml) (#rs) (Owned false) :=
    λ T, i2p (typed_array_access_array_owned_false π E L base off st ty len iml rs T).

  Lemma typed_array_access_array_shared π E L base off st {rt} (ty : type rt) len iml rs κ (T : typed_array_access_cont_t) :
    (⌜off < len⌝ ∗ ⌜st = ty_syn_type ty⌝ ∗ ∀ lt r, ⌜interpret_iml (◁ ty)%I len iml !! off = Some lt⌝ -∗ ⌜rs !! off = Some r⌝ -∗
      T _ ty len iml (rs) (Shared κ) _ lt r)
    ⊢ typed_array_access π E L base off st (ArrayLtype ty len iml) (#rs) (Shared κ) T.
  Proof.
    iIntros "(%Hoff & %Hst & HT)".
    iIntros (??) "#CTX #HE HL Hl".
    iPoseProof (array_ltype_acc_shared with "Hl") as "(%ly & %Halg & % & % & Hlb & >(#Hb & Hcl))"; first done.
    iPoseProof (big_sepL2_length with "Hb") as "%Hlen".
    rewrite interpret_iml_length in Hlen.
    specialize (lookup_lt_is_Some_2 rs off) as (r & Hr).
    { lia. }
    specialize (lookup_lt_is_Some_2 (interpret_iml (◁ ty)%I len iml) off) as (lt & Hlt).
    { rewrite interpret_iml_length. lia. }
    iPoseProof (big_sepL2_lookup _ _ _ off with "Hb") as "(%Hst' & Hel)"; [done.. | ].
    iMod ("Hcl" $! ty iml with "[//] Hb") as "(Ha & _)".
    iPoseProof ("HT" with "[//] [//]") as "HT".
    iModIntro. iExists _, _, _, _, _, _, _. iExists _, _. iFrame.
    rewrite /OffsetLocSt /use_layout_alg' Hst Halg//.
  Qed.
  Global Instance typed_array_access_shared_inst π E L base off st {rt} (ty : type rt) len iml rs κ :
    TypedArrayAccess π E L base off st (ArrayLtype ty len iml) (#rs) (Shared κ) :=
    λ T, i2p (typed_array_access_array_shared π E L base off st ty len iml rs κ T).

  (* TODO maybe we should also move out the value for the element then?
      Problem: at the point of the subsumption, this is too late already for function calls, since we already have the evar then...
  *)
  Lemma subsume_from_offset_ptr_t π E L step l base off st k {rt} (ty : type rt) r T :
    find_in_context (FindLoc base π) (λ '(existT rt' (lt', r', k')),
      typed_array_access π E L base off st lt' r' k' (λ rt2 ty2 len2 iml2 rs2 k2 rte lte re,
        base ◁ₗ[π, k2] #rs2 @ ArrayLtype ty2 len2 iml2 -∗
        (* TODO maybe this should also stratify? *)
        subsume_full E L step (l ◁ₗ[π, k2] re @ lte) (l ◁ₗ[π, k] r @ ◁ ty) T))
    ⊢ subsume_full E L step (l ◁ᵥ{π} (base, off) @ offset_ptr_t st) (l ◁ₗ[π, k] r @ ◁ ty) T.
  Proof.
    rewrite /find_in_context.
    iDestruct 1 as ([rt' [[lt' r'] k']]) "(Hl & Ha)". simpl.
    iIntros (???) "#CTX #HE HL Hoffset".
    iMod ("Ha" with "[//] CTX HE HL Hl") as "(%k2 & %rt2 & %ty2 & %len2 & %iml2 & %rs2 & %rte & %re & %lte & Hb & Hl & HL & HT)".
    iEval (rewrite /ty_own_val/=) in "Hoffset". iDestruct "Hoffset" as "%Heq".
    apply val_of_loc_inj in Heq. subst l.
    iApply ("HT" with "Hb [//] [//] CTX HE HL Hl").
  Qed.
  Global Instance subsume_from_offset_ptr_t_inst π E L step (l : loc) base off st k {rt} (ty : type rt) r :
    SubsumeFull E L step (l ◁ᵥ{π} (base, off) @ offset_ptr_t st) (l ◁ₗ[π, k] r @ (◁ ty)%I) | 50 :=
    λ T, i2p (subsume_from_offset_ptr_t π E L step l base off st k ty r T).

  (*      TODO: also should ideally formulate this so we can share this with the direct array offset rules.
     Potentially, we should just encode array offset in terms of this.

     Can I formulate this without the deref? Well, then I'd need to have an offset place type.
     Can I make the recursive part nicer? e.g. by just hooking on top of the alias ptr lemma?
  *)
  Lemma typed_place_offset_ptr_owned π E L l st base offset bmin P wl T :
    find_in_context (FindLoc base π) (λ '(existT rt (lt, r, b)),
      typed_array_access π E L base offset st lt r b (λ rt2 ty2 len2 iml2 rs2 k2 rte lte re,
        base ◁ₗ[ π, k2] # rs2 @ ArrayLtype ty2 len2 iml2 -∗
        typed_place π E L (base offsetst{st}ₗ offset) lte re k2 k2 P (λ L2 κs li bi bmin' rti lti ri strong weak,
          T L2 [] li bi bmin' rti lti ri
            (match strong with
             | Some strong => Some $ mk_strong (λ _, _) (λ _ _ _, (◁ offset_ptr_t st)) (λ _ _, #(base, offset)) (λ rti2 ltyi2 ri2, (base offsetst{st}ₗ offset) ◁ₗ[π, k2] strong.(strong_rfn) _ ri2 @ strong.(strong_lt) _ ltyi2 ri2 ∗ strong.(strong_R) _ ltyi2 ri2)
             | None => None
             end)
            (match weak with
             | Some weak => Some $ mk_weak (λ _ _, (◁ offset_ptr_t st)) (λ _, #(base, offset)) (λ ltyi2 ri2, llft_elt_toks κs ∗ (base offsetst{st}ₗ offset) ◁ₗ[π, k2] weak.(weak_rfn) ri2 @ weak.(weak_lt) ltyi2 ri2 ∗ weak.(weak_R) ltyi2 ri2)
             | None =>
                 match strong with
                  | Some strong => Some $ mk_weak (λ _ _, (◁ offset_ptr_t st)) (λ _, #(base, offset)) (λ ltyi2 ri2, (base offsetst{st}ₗ offset) ◁ₗ[π, k2] strong.(strong_rfn) _ ri2 @ strong.(strong_lt) _ ltyi2 ri2 ∗ strong.(strong_R) _ ltyi2 ri2)
                  | None => None
                  end
              end)
    )))
    ⊢ typed_place π E L l (◁ offset_ptr_t st) (#(base, offset)) bmin (Owned wl) (DerefPCtx Na1Ord PtrOp true :: P) T.
  Proof.
    rewrite /FindLoc.
    iDestruct 1 as ([rt [[lt r] b]]) "(Hbase & HT)". simpl.
    iIntros (????) "#CTX #HE HL Hincl Hl Hcont".
    iApply fupd_place_to_wp.
    iMod ("HT" with "[] CTX HE HL Hbase") as "(%k2 & %rt2 & %ty2 & %len2 & %iml2 & %rs2 & %rte & %re & %lte & Hbase & Hoff & HL & HT)"; first done.
    iApply (typed_place_ofty_access_val_owned with "[Hbase Hoff HT] [//] [//] CTX HE HL Hincl Hl Hcont").
    { done. }
    iIntros (F' v ?) "Hoffset".
    iEval (rewrite /ty_own_val/=) in "Hoffset". iDestruct "Hoffset" as "->".
    iModIntro. iExists _, _, _, _, _. iR. iFrame "Hoff".
    iSplitR. { rewrite /ty_own_val/=. done. }
    iSpecialize ("HT" with "Hbase").
    iApply "HT".
  Qed.
  Global Instance typed_place_offset_ptr_owned_inst π E L l st base offset bmin P wl :
    TypedPlace E L π l (◁ offset_ptr_t st)%I (#(base, offset)) bmin (Owned wl) (DerefPCtx Na1Ord PtrOp true :: P) |30 :=
    λ T, i2p (typed_place_offset_ptr_owned π E L l st base offset bmin P wl T).

  Lemma typed_place_offset_ptr_uniq π E L l st base offset bmin P κ γ T :
    find_in_context (FindLoc base π) (λ '(existT rt (lt, r, b)),
      typed_array_access π E L base offset st lt r b (λ rt2 ty2 len2 iml2 rs2 k2 rte lte re,
        base ◁ₗ[ π, k2] # rs2 @ ArrayLtype ty2 len2 iml2 -∗
        ⌜lctx_lft_alive E L κ⌝ ∗
        typed_place π E L (base offsetst{st}ₗ offset) lte re k2 k2 P (λ L2 κs li bi bmin' rti lti ri strong weak,
          T L2 κs li bi bmin' rti lti ri
            (option_map (λ strong, mk_strong (λ _, _) (λ _ _ _, (◁ offset_ptr_t st)) (λ _ _, #(base, offset)) (λ rti2 ltyi2 ri2, (base offsetst{st}ₗ offset) ◁ₗ[π, k2] strong.(strong_rfn) _ ri2 @ strong.(strong_lt) _ ltyi2 ri2 ∗ strong.(strong_R) _ ltyi2 ri2)) strong)
            (option_map (λ weak, mk_weak (λ _ _, (◁ offset_ptr_t st)) (λ _, #(base, offset)) (λ ltyi2 ri2, (base offsetst{st}ₗ offset) ◁ₗ[π, k2] weak.(weak_rfn) ri2 @ weak.(weak_lt) ltyi2 ri2 ∗ weak.(weak_R) ltyi2 ri2)) weak)
    )))
    ⊢ typed_place π E L l (◁ offset_ptr_t st) (#(base, offset)) bmin (Uniq κ γ) (DerefPCtx Na1Ord PtrOp true :: P) T.
  Proof.
    rewrite /FindLoc.
    iDestruct 1 as ([rt [[lt r] b]]) "(Hbase & HT)". simpl.
    iIntros (????) "#CTX #HE HL Hincl Hl Hcont".
    iApply fupd_place_to_wp.
    iMod ("HT" with "[] CTX HE HL Hbase") as "(%k2 & %rt2 & %ty2 & %len2 & %iml2 & %rs2 & %rte & %re & %lte & Hbase & Hoff & HL & HT)"; first done.
    iPoseProof ("HT" with "Hbase") as "(%Hal & HT)".
    iApply (typed_place_ofty_access_val_uniq  _ _ _ _ (offset_ptr_t st) with "[Hoff HT] [//] [//] CTX HE HL Hincl Hl Hcont").
    { done. }
    iR. iIntros (F' v ?) "Hoffset".
    iEval (rewrite /ty_own_val/=) in "Hoffset". iDestruct "Hoffset" as "->".
    iModIntro. iExists _, _, _, _, _. iR. iFrame "Hoff".
    iSplitR. { rewrite /ty_own_val/=. done. }
    iApply "HT".
  Qed.
  Global Instance typed_place_offset_ptr_uniq_inst π E L l st base offset bmin P κ γ :
    TypedPlace E L π l (◁ offset_ptr_t st)%I (#(base, offset)) bmin (Uniq κ γ) (DerefPCtx Na1Ord PtrOp true :: P) | 30:=
    λ T, i2p (typed_place_offset_ptr_uniq π E L l st base offset bmin P κ γ T).

  Lemma typed_place_offset_ptr_shared π E L l st base offset bmin P κ T :
    find_in_context (FindLoc base π) (λ '(existT rt (lt, r, b)),
      typed_array_access π E L base offset st lt r b (λ rt2 ty2 len2 iml2 rs2 k2 rte lte re,
        base ◁ₗ[ π, k2] # rs2 @ ArrayLtype ty2 len2 iml2 -∗
        ⌜lctx_lft_alive E L κ⌝ ∗
        typed_place π E L (base offsetst{st}ₗ offset) lte re k2 k2 P (λ L2 κs li bi bmin' rti lti ri strong weak,
          T L2 κs li bi bmin' rti lti ri
            (option_map (λ strong, mk_strong (λ _, _) (λ _ _ _, (◁ offset_ptr_t st)) (λ _ _, #(base, offset)) (λ rti2 ltyi2 ri2, (base offsetst{st}ₗ offset) ◁ₗ[π, k2] strong.(strong_rfn) _ ri2 @ strong.(strong_lt) _ ltyi2 ri2 ∗ strong.(strong_R) _ ltyi2 ri2)) strong)
            (option_map (λ weak, mk_weak (λ _ _, (◁ offset_ptr_t st)) (λ _, #(base, offset)) (λ ltyi2 ri2, (base offsetst{st}ₗ offset) ◁ₗ[π, k2] weak.(weak_rfn) ri2 @ weak.(weak_lt) ltyi2 ri2 ∗ weak.(weak_R) ltyi2 ri2)) weak)
    )))
    ⊢ typed_place π E L l (◁ offset_ptr_t st) (#(base, offset)) bmin (Shared κ) (DerefPCtx Na1Ord PtrOp true :: P) T.
  Proof.
    rewrite /FindLoc.
    iDestruct 1 as ([rt [[lt r] b]]) "(Hbase & HT)". simpl.
    iIntros (????) "#CTX #HE HL Hincl Hl Hcont".
    iApply fupd_place_to_wp.
    iMod ("HT" with "[] CTX HE HL Hbase") as "(%k2 & %rt2 & %ty2 & %len2 & %iml2 & %rs2 & %rte & %re & %lte & Hbase & Hoff & HL & HT)"; first done.
    iPoseProof ("HT" with "Hbase") as "(%Hal & HT)".
    iApply (typed_place_ofty_access_val_shared with "[Hoff HT] [//] [//] CTX HE HL Hincl Hl Hcont").
    { done. }
    iR. iIntros (F' v ?) "Hoffset".
    iEval (rewrite /ty_own_val/=) in "Hoffset". iDestruct "Hoffset" as "->".
    iModIntro. iExists _, _, _, _, _. iR. iFrame "Hoff".
    iSplitR. { rewrite /ty_own_val/=. done. }
    iApply "HT".
  Qed.
  Global Instance typed_place_offset_ptr_shared_inst π E L l st base offset bmin P κ :
    TypedPlace E L π l (◁ offset_ptr_t st)%I (#(base, offset)) bmin (Shared κ) (DerefPCtx Na1Ord PtrOp true :: P) |30 :=
    λ T, i2p (typed_place_offset_ptr_shared π E L l st base offset bmin P κ T).

  Lemma owned_subtype_offset_alias π E L pers l (offset : nat) l2 st T :
    ⌜l2 = l offsetst{st}ₗ offset⌝ ∗ T L
    ⊢ owned_subtype π E L pers (l, offset) l2 (offset_ptr_t st) (alias_ptr_t) T.
  Proof.
    iIntros "(-> & HT)".
    iIntros (???) "#CTX #HE HL". iExists L. iFrame.
    iModIntro. iApply bi.intuitionistically_intuitionistically_if.
    iModIntro.
    iSplitR; last iSplitR.
    - iPureIntro. simpl. iIntros (ly1 ly2 Hst1 Hst2).
      f_equiv. by eapply syn_type_has_layout_inj.
    - rewrite /ty_sidecond/=. done.
    - iIntros (v) "Hv". rewrite /ty_own_val/=. done.
  Qed.
  Global Instance owned_subtype_offset_alias_inst π E L pers l (offset : nat) l2 st :
    OwnedSubtype π E L pers (l, offset) l2 (offset_ptr_t st) (alias_ptr_t) :=
    λ T, i2p (owned_subtype_offset_alias π E L pers l offset l2 st T).

  Lemma owned_subtype_alias_offset π E L pers l l2 offset st T :
    ⌜l2 = l⌝ ∗ ⌜offset = 0⌝ ∗ T L
    ⊢ owned_subtype π E L pers l (l2, offset) (alias_ptr_t) (offset_ptr_t st) T.
  Proof.
    iIntros "(-> & -> & HT)".
    iIntros (???) "#CTX #HE HL". iExists L. iFrame.
    iModIntro. iApply bi.intuitionistically_intuitionistically_if.
    iModIntro.
    iSplitR; last iSplitR.
    - iPureIntro. simpl. iIntros (ly1 ly2 Hst1 Hst2).
      f_equiv. by eapply syn_type_has_layout_inj.
    - rewrite /ty_sidecond/=. done.
    - rewrite /alias_ptr_t. iIntros (v) "->". rewrite /ty_own_val/=.
      rewrite /OffsetLocSt. rewrite Z.mul_0_r shift_loc_0//.
  Qed.
  Global Instance owned_subtype_alias_offset_inst π E L pers l (offset : nat) l2 st :
    OwnedSubtype π E L pers l (l2, offset) (alias_ptr_t) (offset_ptr_t st) :=
    λ T, i2p (owned_subtype_alias_offset π E L pers l l2 offset st T).

  Lemma offset_ptr_simplify_hyp (v : val) π (l : loc) st (off : nat) T :
    (⌜v = l offsetst{st}ₗ off⌝ -∗ introduce_direct (v ◁ᵥ{π} (l, off) @ offset_ptr_t st) -∗ T)
    ⊢ simplify_hyp (v ◁ᵥ{π} (l, off) @ offset_ptr_t st) T.
  Proof.
    iIntros "HT %Hv". rewrite /introduce_direct. by iApply "HT".
  Qed.
  Global Instance offset_ptr_simplify_hyp_inst (v : val) π l st (off : nat) :
    SimplifyHypVal v π (offset_ptr_t st) (l, off) (Some 0%N) :=
    λ T, i2p (offset_ptr_simplify_hyp v π l st off T).

  Lemma offset_ptr_simplify_goal (v : val) π (l : loc) st (off : nat) T :
    (⌜v = l offsetst{st}ₗ off⌝) ∗ T ⊢ simplify_goal (v ◁ᵥ{π} (l, off) @ offset_ptr_t st) T.
  Proof.
    iIntros "(-> & HT)". iFrame. done.
  Qed.
  Global Instance offset_ptr_simplify_goal_inst v π l st off :
    SimplifyGoalVal v π (offset_ptr_t st) (l, off) (Some 50%N) :=
    λ T, i2p (offset_ptr_simplify_goal v π l st off T).

  (*
     prove l +ₗ ... ◁

     subsume (v ◁ᵥ offset_ptr_t) (l ◁ₗ[π, ..] .. )


   *)



  (* Want:
      - find type assingment
      - subtype to array
        this should potentially also be able to move it back in.
        just subsume_full with a step is probably right.
      - then we need that the offset is valid, prove it. okay.
      - then we can provide the array with aliased ownership and get the ownership for that offset out.
        for that we are going to need a step, if it is Owned true.

     On the other side, when we need to move in again:
        subtyping here should be able to put in aliases again.
         so this needs to be owned_subltype_step/subsume_full with a step if it is Owned true, and for Owned false doesn't need a step.
        in general, we won't have a step.
        but how do we formulate the lemmas to enable that?
        well, we basically need the stratification parts for that also in subtyping now...
        why, well, because we consciously destroy it first.

        but we also get that issue when we first do
          ptr::write (moving an element out)
        and then
          ptr::copy (needs everything in place)
        Maybe we should stratify place arguments in the precondition first?

        i.e. prove_with_subtype (l ◁ₗ[...] ...) should find assignment for l and then stratify it, if it gets a step.
          I'm not sure if that is a good idea in general though.
        TODO

        I guess in principle, maybe that is just something that should also be doable by subtyping, not by stratification.

        Maybe all the value instances for joining values should also be put in there.
   *)
  Lemma type_extract_value_annot_offset π E L n v l (off : nat) st (T : typed_annot_expr_cont_t) :
    (v ◁ᵥ{π} (l, off) @ offset_ptr_t st -∗ T L v _ (offset_ptr_t st) (l, off))
    ⊢ typed_annot_expr π E L n ExtractValueAnnot v (v ◁ᵥ{π} (l, off) @ offset_ptr_t st) T.
  Proof.
    iIntros "HT #CTX #HE HL #Hv".
    iApply step_fupdN_intro; first done. iNext. iModIntro. iExists _, _, _, _. iFrame.
    iR. by iApply "HT".
  Qed.
  Global Instance type_extract_value_annot_offset_inst π E L n v l off st :
    TypedAnnotExpr π E L n ExtractValueAnnot v (v ◁ᵥ{π} (l, off) @ offset_ptr_t st)%I :=
    λ T, i2p (type_extract_value_annot_offset π E L n v l off st T).

  (* Problem:
        Lithium simplifies only if it cannot find it in the context.
        Maybe we shou


      Now, what is our invariant? Do we want to have offset ptrs in the context as values?

     If so, we get into trouble in some places where we need to go from an aliasptr to an offsetptr.

     If not, we will try to find an assignment and can't find it in the preconditions we have.
      Ideally, I'd like to be able to introduce something into the context without simplification at some points.
      Or have simplification for gaining information.


   *)



  (*
  Lemma type_extract_value_annot_offset π E L n v l (off : nat) st (T : typed_annot_expr_cont_t) :
    ⌜n > 0⌝ ∗ find_in_context (FindLoc l π) (λ '(existT rt (lt, r, bk)),
    (* TODO this is a pretty big hack currently and will break once we e.g. first move out the value. The problem is that we have trouble with the dependent evars *)
      ∃ rt', ⌜rt = list (place_rfn rt')⌝ ∗ ∃ (ty : type rt') len iml (xs : list (place_rfn rt')),
      subsume_full E L true (l ◁ₗ[π, bk] r @ lt) (l ◁ₗ[π, Owned false] #xs @ ArrayLtype ty len iml) (λ L2 R2,
        ⌜(off < len)%Z⌝ ∗
        ⌜ty_syn_type ty = st⌝ ∗ (* TODO might generalize this condition *)
        (∀ x lt,
          ⌜xs !! off = Some x⌝ -∗
          ⌜interpret_iml (◁ ty)%I len iml !! off = Some lt⌝ -∗
          (l offsetst{st}ₗ off) ◁ₗ[π, Owned false] x @ lt -∗
          l ◁ₗ[π, Owned false] #xs @ ArrayLtype ty len [(off, AliasLtype _ (ty_syn_type ty) (l offsetst{ty_syn_type ty}ₗ off))] -∗
          T L v _ (offset_ptr_t st) (l, off)))) -∗
    typed_annot_expr π E L n ExtractValueAnnot v (v ◁ᵥ{π} (l, off) @ offset_ptr_t st) T.
  Proof.
    (* TODO *)
  Admitted.
  Global Instance type_extract_value_annot_offset_inst π E L n v l off st :
    TypedAnnotExpr π E L n ExtractValueAnnot v (v ◁ᵥ{π} (l, off) @ offset_ptr_t st)%I :=
    λ T, i2p (type_extract_value_annot_offset π E L n v l off st T).
  *)
End offset_rules.

Global Hint Mode TypedArrayAccess + + + + + + + + + + + + : typeclass_instances.
Global Typeclasses Opaque typed_array_access.

Global Typeclasses Opaque offset_ptr_t.
Global Typeclasses Opaque array_t.


Global Typeclasses Opaque weak_subltype_list_interp.
Global Typeclasses Opaque mut_subltype_list_interp.
Global Typeclasses Opaque mut_eqltype_list_interp.

Global Typeclasses Opaque fold_overrides_list_interp.

Global Typeclasses Opaque stratify_ltype_array_iter.
Global Hint Mode StratifyLtypeArrayIter + + + + + + + + + + + + + + + + + + : typeclass_instances.
Global Hint Mode ResolveGhostIter + + + + + + + + + + + + + + + : typeclass_instances.
Global Typeclasses Opaque resolve_ghost_iter.



  (*


    Lifecycle of an array:
    - initialization by subsumption from uninit - i.e. uninit -> array (uninit)
    - array (uninit) -> array (ty)
      + in Vec: ty = maybe_uninit ty)
      + in safe Rust: write array value to it.
        this always has constant size (no VLA); but it may not only contain constants.
          I.e. this is an expression. We need to typecheck this expression at array_t, and can then assign it.
    - on access of components: unfold.
    - accesses of components may generate an override with a new ltype (homo).
    - eventually, we fold again (stratification). here, we show that everything is coreable to the def type.
    -

    What about partially initialized arrays?
    - in safe Rust, these don't exist.
    - and in other cases, we will usually have maybe_uninit (e.g. Vec).


     How do I imagine these lemmas to look?

     For subltyping:
       - should it take into account refinements, or directly require equality of those?
          e.g. if we want to do array (T) <: array (maybe_uninit T), we need to take it into account.

       Option 1:
         - require subtyping for the def type.
         - for the overrides:
            + first simplify via tactic hint
            + then enter a custom judgment that deals with imls (or something more general -- basically a generalization of subsume_list)
       Option 2:
       - do a subsumption that looks quite similar to refinedc's subsume_list -- i.e. we first interpret via interpret_iml, and then have a generalization of subsume_list.

      => use Option 2 with relate_list.
        We basically add a flag describing the operation to match on for instances.
        In our case, it will also carry the whole refinements.
        Then the individual instance for us will just do one step by doing a lookup.


     For resolve_ghost:
        - basically should take into account just the overrides.
        - need to deal with list inserts in the refinement here. Use Lithiums built-in lookup facility.
            strategy 1: walk over the refinement via syntactic matching on inserts. For each of these, do a resolution.
              -> I think this is probably more robust.
              How do I phrase this inductively, though?
                probably extract the refinement first, converting it into a walkable list via Ltac.
                then go over that list, and generate new inserts if we do a resolution.
                Probably that needs a separate judgment.
            strategy 2: walk over the types. However: we ideally also want to be able to resolve for folded things.
              This would only suffice if we can get the better refinement contracts to work. (i.e., setting up relations after the fact).

       On strategy1:
       - ghost_resolve_list
          Difference to structs: we don't deal with concrete, but with symbolic lists.
         Is there some more general abstraction we could use?

    For stratify:
      - first, stratify all components.
        Basically:
          def is already a type and fully stratified.
          for the overrides, for each do a lookup of the refinement, and stratify with that.
      - then have the stratified components.
        if all of them satisfy the placecond: go to ofty or coreable
          + check if all of them are ofty, then require subtyping to the def. then can go to ofty for the array again.
          + otherwise, go to coreable with the whole thing (?) => this is a choice here.
            Do we want to completely "finalize" or not?
        otherwise, keep the current state.

    place access:
      - how does unfolding of an array work?
        well, after deref we give it an ofty, from which we can go on and generate an override.
      - actual access:
        + either go directly via lookup of the interpreted list.
          => This is the path to take.
        + or go via lookup of iml -- needs custom lookup li_tactic then.
   *)

