From refinedrust Require Export type ltypes programs.
From refinedrust Require Import memcasts ltype_rules value.
From iris Require Import options.


(** A specialized version for pointers.
  This is mainly useful if we want to specify ownership of allocations in an ADT separately (e.g. in RawVec) from the field of the struct actually containing the pointer.
  Disadvantage: this does not have any useful interaction laws with the AliasLtype, and we need to duplicate the place typing lemma for both of these. *)
Section alias.
  Context `{!typeGS Σ}.
  Program Definition alias_ptr_t : type loc := {|
    st_own π (l : loc) v := ⌜v = l⌝%I;
    st_syn_type := PtrSynType;
    st_has_op_type ot mt := is_ptr_ot ot;
  |}.
  Next Obligation.
    iIntros (π l v ->). iExists void*. eauto.
  Qed.
  Next Obligation.
    iIntros (ot mt Hot).
    destruct ot; try done.
    rewrite Hot. done.
  Qed.
  Next Obligation.
    iIntros (ot mt st π l v Hot) "Hv".
    simpl in Hot. iPoseProof (mem_cast_compat_loc (λ v, ⌜v = l⌝)%I with "Hv") as "%Hid"; first done.
    { iIntros "->". eauto. }
    destruct mt; [done | | done].
    rewrite Hid. done.
  Qed.

  Global Instance alias_ptr_t_copy : Copyable (alias_ptr_t).
  Proof. apply _. Qed.

End alias.

Global Hint Unfold alias_ptr_t : tyunfold.

Section rules.
  Context `{!typeGS Σ}.

  (* TODO interaction with ghost drop? *)
  Lemma alias_ptr_simplify_hyp (v : val) π (l : loc) T :
    (⌜v = l⌝ -∗ T)
    ⊢ simplify_hyp (v ◁ᵥ{π} l @ alias_ptr_t) T.
  Proof.
    iIntros "HT %Hv". by iApply "HT".
  Qed.
  Global Instance alias_ptr_simplify_hyp_inst v π l :
    SimplifyHypVal v π (alias_ptr_t) l (Some 0%N) :=
    λ T, i2p (alias_ptr_simplify_hyp v π l T).

  Lemma alias_ptr_simplify_goal (v : val) π (l : loc) T :
    (⌜v = l⌝) ∗ T ⊢ simplify_goal (v ◁ᵥ{π} l @ alias_ptr_t) T.
  Proof.
    rewrite /simplify_goal. iIntros "(-> & $)". done.
  Qed.
  Global Instance alias_ptr_simplify_goal_inst v π l :
    SimplifyGoalVal v π (alias_ptr_t) l (Some 0%N) :=
    λ T, i2p (alias_ptr_simplify_goal v π l T).

  Import EqNotations.
  (** Unsafe simplification: if we can't find a value assignment for a location, also just try to make it an alias_ptr. *)
  (*
  Lemma alias_ptr_simplify_goal_unsafe1 π (l : loc) {rt} (ty : type rt) (r : rt) T :
    (* redundant thing due to evar instantiation *)
    T (⌜rt = loc⌝ ∗ l ◁ᵥ{π} r @ ty) -∗
    simplify_goal (l ◁ᵥ{π} r @ ty) T.
  Proof.
    iIntros "HT". iExists _. iFrame.
    iIntros "(-> & $)".
  Qed.
  Global Instance alias_ptr_simplify_goal_unsafe1_inst π (l : loc) {rt} (ty : type rt) (r : rt) :
    SimplifyGoalVal l π ty r (Some 11%N) :=
    λ T, i2p (alias_ptr_simplify_goal_unsafe1 π l ty r T).

  Lemma alias_ptr_simplify_goal_unsafe2 π (l : loc) (ty : type loc) (r : loc) T :
    (* redundant thing due to evar instantiation *)
    T (⌜ty = alias_ptr_t⌝ ∗ ⌜r = l⌝) -∗
    simplify_goal (l ◁ᵥ{π} r @ ty) T.
  Proof.
    iIntros "HT". iExists _. iFrame.
    iIntros "(-> & ->)". rewrite /ty_own_val/=. done.
  Qed.
  Global Instance alias_ptr_simplify_goal_unsafe2_inst π (l : loc) (ty : type loc) (r : loc) :
    SimplifyGoalVal l π ty r (Some 10%N) :=
    λ T, i2p (alias_ptr_simplify_goal_unsafe2 π l ty r T).
   *)

  (* Place typing accesses to alias_ptr:
     - in RefinedC's setup: essentially just exploit the equality and then start a new search in the context for the location; independent of any actual operation
     - for us: that would entail making alias_ptr an ltype.
        does that make sense? maybe not so much.
        Or maybe it dose?

     Does the fact that we need to do a dereference affect us much?
     - difference is that we always have some actual ownership involved when stating place ownership of alias_ptr, because we wrap it in ofty.
     - I can't really do chains of alias_ptr that way.

     One idea: have a simplification thing for ofty and then simplify value ownership of the type. That way, we could basically chase chains of alias_ptr. (by always simplifyign below the ◁)
      - does this make much sense apart from simplifying alias_ptr? In all other cases, I don't have precise enough information about what value to simplify.
      - but: this requires then having a proper owned_ptr for the Vec spec. (?)
      -

     How about having an alias_ptr_lt?
     - We do not get a direct unfoldign equation in terms of ofty.
       Rather, this is another ltype we can "leave" in case we take the ownership of an ofty and instead want to leave an alias.
     - we can easily formulate the place lemma
     - this makes a lot of sense for taking raw address-of
  *)


    (* unnatural about this: ofty contains an owned pointer.
       why can't we just strip it? because we don't have a location ownership predicate for the contained type in general -- ofty is precisely providing that.

       the tension here: the corresponding location predicate for alias_ptr does not actually assert any ownership.
       why do we need the value version at all?
        concretely for us: for rawvec.
        in refinedc, one would probably use an owned pointer instead.
        in our case, we could also use owned_ptr instead, if our array type was less ugly.
     *)

   (* way to make this generic: have a lemma for ofty that says
        "I give you value ownership of the contained thing, then you give me some new ltype and then I can continue"
    *)


    Lemma typed_place_ofty_alias_ptr_owned π E L l l2 bmin0 wl P T :
      find_in_context (FindLoc l2 π) (λ '(existT rt2 (lt2, r2, b2)),
        typed_place π E L l2 lt2 r2 b2 b2 P (λ L' κs li b3 bmin rti ltyi ri strong weak,
          T L' [] li b3 bmin rti ltyi ri
            (match strong with
             | Some strong => Some $ mk_strong (λ _, _) (λ _ _ _, ◁ alias_ptr_t) (λ _ _, PlaceIn l2) (λ rti2 ltyi2 ri2, l2 ◁ₗ[π, b2] strong.(strong_rfn) _ ri2 @ strong.(strong_lt) _ ltyi2 ri2 ∗ strong.(strong_R) _ ltyi2 ri2)
             | None => None
             end)
            (match weak with
             | Some weak => Some $ mk_weak (λ _ _, ◁ alias_ptr_t) (λ _, #l2) (λ ltyi2 ri2, llft_elt_toks κs ∗ l2 ◁ₗ[π, b2] weak.(weak_rfn) ri2 @ weak.(weak_lt) ltyi2 ri2 ∗ weak.(weak_R) ltyi2 ri2)
             | None =>
                 match strong with
                  | Some strong => Some $ mk_weak (λ _ _, ◁ alias_ptr_t) (λ _, #l2) (λ ltyi2 ri2, l2 ◁ₗ[π, b2] strong.(strong_rfn) _ ri2 @ strong.(strong_lt) _ ltyi2 ri2 ∗ strong.(strong_R) _ ltyi2 ri2)
                  | None => None
                  end
              end)
            ))
      ⊢ typed_place π E L l (◁ alias_ptr_t) (PlaceIn l2) bmin0 (Owned wl) (DerefPCtx Na1Ord PtrOp true :: P) T.
    Proof.
      iDestruct 1 as ((rt2 & ([lt2 r2] & b2))) "(Hl2 & HP)". simpl.
      iApply typed_place_ofty_access_val_owned; first done.
      iIntros (? v ?) "-> !>". iExists _, _, _, _, _. iSplitR; first done. iFrame "Hl2 HP". done.
    Qed.
    Global Instance typed_place_ofty_alias_ptr_owned_inst π E L l l2 bmin0 wl P :
      TypedPlace E L π l (◁ alias_ptr_t)%I (PlaceIn l2) bmin0 (Owned wl) (DerefPCtx Na1Ord PtrOp true :: P) |30 :=
      λ T, i2p (typed_place_ofty_alias_ptr_owned π E L l l2 bmin0 wl P T).

    Lemma typed_place_ofty_alias_ptr_uniq π E L l l2 bmin0 κ γ P T :
      ⌜lctx_lft_alive E L κ⌝ ∗
      find_in_context (FindLoc l2 π) (λ '(existT rt2 (lt2, r2, b2)),
        typed_place π E L l2 lt2 r2 b2 b2 P (λ L' κs li b3 bmin rti ltyi ri strong weak,
          T L' κs li b3 bmin rti ltyi ri
            (fmap (λ strong, mk_strong (λ _, _) (λ _ _ _, ◁ alias_ptr_t) (λ _ _, PlaceIn l2)
              (* give back ownership through R *)
              (λ rti2 ltyi2 ri2, l2 ◁ₗ[π, b2] strong.(strong_rfn) _ ri2 @ strong.(strong_lt) _ ltyi2 ri2 ∗ strong.(strong_R) _ ltyi2 ri2)) strong)
            (fmap (λ weak, mk_weak (λ _ _, ◁ alias_ptr_t) (λ _, PlaceIn l2)
              (λ ltyi2 ri2, l2 ◁ₗ[π, b2] weak.(weak_rfn) ri2 @ weak.(weak_lt) ltyi2 ri2 ∗ weak.(weak_R) ltyi2 ri2)) weak)
            ))
      ⊢ typed_place π E L l (◁ alias_ptr_t) (PlaceIn l2) bmin0 (Uniq κ γ) (DerefPCtx Na1Ord PtrOp true :: P) T.
    Proof.
      iDestruct 1 as (Hal (rt2 & ([lt2 r2] & b2))) "(Hl2 & HP)". simpl.
      iApply typed_place_ofty_access_val_uniq; first done. iSplitR; first done.
      iIntros (? v ?) "-> !>". iExists _, _, _, _, _. iSplitR; first done. iFrame. done.
    Qed.
    Global Instance typed_place_ofty_alias_ptr_uniq_inst π E L l l2 bmin0 κ γ P :
      TypedPlace E L π l (◁ alias_ptr_t)%I (PlaceIn l2) bmin0 (Uniq κ γ) (DerefPCtx Na1Ord PtrOp true :: P) |30 :=
      λ T, i2p (typed_place_ofty_alias_ptr_uniq π E L l l2 bmin0 κ γ P T).

    Lemma typed_place_ofty_alias_ptr_shared π E L l l2 bmin0 κ P T :
      ⌜lctx_lft_alive E L κ⌝ ∗
      find_in_context (FindLoc l2 π) (λ '(existT rt2 (lt2, r2, b2)),
        typed_place π E L l2 lt2 r2 b2 b2 P (λ L' κs li b3 bmin rti ltyi ri strong weak,
          T L' κs li b3 bmin rti ltyi ri
            (fmap (λ strong, mk_strong (λ _, _) (λ _ _ _, ◁ alias_ptr_t) (λ _ _, PlaceIn l2)
              (* give back ownership through R *)
              (λ rti2 ltyi2 ri2, l2 ◁ₗ[π, b2] strong.(strong_rfn) _ ri2 @ strong.(strong_lt) _ ltyi2 ri2 ∗ strong.(strong_R) _ ltyi2 ri2)) strong)
            (option_map (λ weak, mk_weak (λ _ _, ◁ alias_ptr_t) (λ _, PlaceIn l2)
              (λ ltyi2 ri2, l2 ◁ₗ[π, b2] weak.(weak_rfn) ri2 @ weak.(weak_lt) ltyi2 ri2 ∗ weak.(weak_R) ltyi2 ri2)) weak)
            ))
      ⊢ typed_place π E L l (◁ alias_ptr_t) (PlaceIn l2) bmin0 (Shared κ) (DerefPCtx Na1Ord PtrOp true :: P) T.
    Proof.
      iDestruct 1 as (Hal (rt2 & ([lt2 r2] & b2))) "(Hl2 & HP)". simpl.
      iApply typed_place_ofty_access_val_shared; first done. iSplitR; first done.
      iIntros (? v ?) "-> !>". iExists _, _, _, _, _. iSplitR; first done. iFrame. done.
    Qed.
    Global Instance typed_place_ofty_alias_ptr_shared_inst π E L l l2 bmin0 κ P :
      TypedPlace E L π l (◁ alias_ptr_t)%I (PlaceIn l2) bmin0 (Shared κ) (DerefPCtx Na1Ord PtrOp true :: P) |30 :=
      λ T, i2p (typed_place_ofty_alias_ptr_shared π E L l l2 bmin0 κ P T).

  (* TODO is there a better design that does not require us to essentially duplicate this?
     we have alias_ltype in the first place only because of the interaction with OpenedLtype, when we do a raw-pointer-addrof below references.
   *)
End rules.

(** Rules for AliasLtype *)
Section alias_ltype.
  Context `{!typeGS Σ}.

  Lemma alias_ltype_owned_simplify_hyp π rt st wl (l l2 : loc) (r : place_rfn rt) T :
    (⌜l = l2⌝ -∗ T)
    ⊢ simplify_hyp (l ◁ₗ[π, Owned wl] r @ AliasLtype rt st l2) T.
  Proof.
    iIntros "HT Hl".
    rewrite ltype_own_alias_unfold /alias_lty_own.
    iDestruct "Hl" as "(%ly & Hst & -> & Hloc & Hlb)".
    by iApply "HT".
  Qed.
  Global Instance alias_ltype_owned_simplify_hyp_inst π rt st wl l l2 r :
    SimplifyHyp (l ◁ₗ[π, Owned wl] r @ AliasLtype rt st l2) (Some 0%N) :=
    λ T, i2p (alias_ltype_owned_simplify_hyp π rt st wl l l2 r T).

  Lemma alias_ltype_unowned_simplify_hyp π rt st b (l l2 : loc) (r : place_rfn rt) T :
    (if b is Owned _ then False else True) →
    (False -∗ T)
    ⊢ simplify_hyp (l ◁ₗ[π, b] r @ AliasLtype rt st l2) T.
  Proof.
    iIntros (?) "HT Hl".
    rewrite ltype_own_alias_unfold /alias_lty_own.
    destruct b; done.
  Qed.
  Global Instance alias_ltype_uniq_simplify_hyp_inst π rt st κ γ l l2 r :
    SimplifyHyp (l ◁ₗ[π, Uniq κ γ] r @ AliasLtype rt st l2) (Some 0%N) :=
    λ T, i2p (alias_ltype_unowned_simplify_hyp π rt st (Uniq κ γ) l l2 r T I).
  Global Instance alias_ltype_shared_simplify_hyp_inst π rt st κ l l2 r :
    SimplifyHyp (l ◁ₗ[π, Shared κ] r @ AliasLtype rt st l2) (Some 0%N) :=
    λ T, i2p (alias_ltype_unowned_simplify_hyp π rt st (Shared κ) l l2 r T I).

  (* At the core this is really similar to the place lemma for alias_ptr_t - just without the deref *)
  Lemma typed_place_alias_owned π E L l l2 rt (r : place_rfn rt) st bmin0 wl P T :
    find_in_context (FindLoc l2 π) (λ '(existT rt2 (lt2, r2, b2)),
      typed_place π E L l2 lt2 r2 b2 b2 P (λ L' κs li b3 bmin rti ltyi ri strong weak,
        T L' κs li b3 bmin rti ltyi ri
          (fmap (λ strong, mk_strong (λ _, _) (λ _ _ _, AliasLtype rt st l2) (λ _ _, r)
            (* give back ownership through R *)
            (λ rti2 ltyi2 ri2, l2 ◁ₗ[π, b2] strong.(strong_rfn) _ ri2 @ strong.(strong_lt) _ ltyi2 ri2 ∗ strong.(strong_R) _ ltyi2 ri2)) strong)
          (fmap (λ weak, mk_weak (λ _ _, AliasLtype rt st l2) (λ _, r)
            (λ ltyi2 ri2, l2 ◁ₗ[π, b2] weak.(weak_rfn) ri2 @ weak.(weak_lt) ltyi2 ri2 ∗ weak.(weak_R) ltyi2 ri2)) weak)
          ))
    ⊢ typed_place π E L l (AliasLtype rt st l2) r bmin0 (Owned wl) P T.
  Proof.
    iDestruct 1 as ((rt2 & ([lt2 r2] & b2))) "(Hl2 & HP)". simpl.
    iIntros (????) "#CTX #HE HL #Hincl Hl Hcont".
    rewrite ltype_own_alias_unfold /alias_lty_own.
    iDestruct "Hl" as "(%ly & % & -> & #? & #? & Hcred)".
    iApply ("HP" with "[//] [//] CTX HE HL [] Hl2").
    { iApply bor_kind_incl_refl. }
    iIntros (L' κs l2 b0 bmin rti ltyi ri strong weak) "#Hincl1 Hl2 Hcl HT HL".
    iApply ("Hcont" with "[//] Hl2 [Hcl Hcred] HT HL").
    iSplit.
    -  (* strong *)
      destruct strong as [ strong | ]; last done.
      iDestruct "Hcl" as "[Hcl _]". simpl.
      iIntros (rti2 ltyi2 ri2) "Hl2 %Hst".
      iMod ("Hcl" with "Hl2 [//]") as "(Hl & % & Hstrong)".
      iModIntro. iSplitL "Hcred".
      { rewrite ltype_own_alias_unfold /alias_lty_own. eauto 8 with iFrame. }
      iSplitR; first done. iFrame.
    - (* weak *) iDestruct "Hcl" as "[_ Hcl]". simpl.
      destruct weak as [weak | ]; simpl; last done.
      iIntros (ltyi2 ri2 ?) "#Hincl3 Hl2 Hcond".
      iMod ("Hcl" with "Hincl3 Hl2 Hcond") as "(Hl & Hcond & Htoks & Hweak)".
      iModIntro. iSplitL "Hcred".
      { rewrite ltype_own_alias_unfold /alias_lty_own. eauto 8 with iFrame. }
      iFrame.
      iApply typed_place_cond_refl. done.
  Qed.
  Global Instance typed_place_alias_owned_inst π E L l l2 rt r st bmin0 wl P :
    TypedPlace E L π l (AliasLtype rt st l2) r bmin0 (Owned wl) P :=
    λ T, i2p (typed_place_alias_owned π E L l l2 rt r st bmin0 wl P T).


  (** Core lemma for putting back ownership after raw borrows *)
  Lemma stratify_ltype_alias_owned π E L mu mdu ma {M} (m : M) l l2 rt st r wl (T : stratify_ltype_cont_t) :
    match ma with
    | StratNoRefold => T L True _ (AliasLtype rt st l2) r
    | _ =>
      find_in_context (FindLoc l2 π) (λ '(existT rt2 (lt2, r2, b2)),
        ⌜ltype_st lt2 = st⌝ ∗ ⌜b2 = Owned wl⌝ ∗
        (* recursively stratify *)
        stratify_ltype π E L mu mdu ma m l2 lt2 r2 b2 (λ L2 R rt2' lt2' r2',
          T L2 R rt2' lt2' r2'))
    end
    ⊢ stratify_ltype π E L mu mdu ma m l (AliasLtype rt st l2) r (Owned wl) T.
  Proof.
    iIntros "HT".
    destruct (decide (ma = StratNoRefold)) as [-> | ].
    { iIntros (???) "#CTX #HE HL Hl". iModIntro. iExists _, _, _, _, _. iFrame.
      iSplitR; first done. iApply logical_step_intro. by iFrame. }
    iAssert (find_in_context (FindLoc l2 π) (λ '(existT rt2 (lt2, r2, b2)), ⌜ltype_st lt2 = st⌝ ∗ ⌜b2 = Owned wl⌝ ∗ stratify_ltype π E L mu mdu ma m l2 lt2 r2 b2 T))%I with "[HT]" as "HT".
    { destruct ma; done. }
    iDestruct "HT" as ([rt2 [[lt2 r2] b2]]) "(Hl2 & <- & -> & HT)".
    simpl. iIntros (???) "#CTX #HE HL Hl".
    rewrite ltype_own_alias_unfold /alias_lty_own.
    iDestruct "Hl" as "(%ly & %Halg & -> & %Hly & Hlb)".
    simp_ltypes.
    iMod ("HT" with "[//] [//] CTX HE HL Hl2") as (L3 R rt2' lt2' r2') "(HL & %Hst & Hstep & HT)".
    iModIntro. iExists _, _, _, _, _. iFrame. done.
  Qed.
  Global Instance stratify_ltype_alias_owned_inst π E L mu mdu ma {M} (m : M) l l2 rt st r wl :
    StratifyLtype π E L mu mdu ma m l (AliasLtype rt st l2) r (Owned wl) :=
    λ T, i2p (stratify_ltype_alias_owned π E L mu mdu ma m l l2 rt st r wl T).

  (* TODO move; doesn't hold anymore because of credits.. *)
  (*
  Global Instance ltype_own_alias_pers π l b rt r st l2 :
    Persistent (l ◁ₗ[π, b] r @ AliasLtype rt st l2).
  Proof.
    rewrite ltype_own_alias_unfold /alias_lty_own.
    destruct b; apply _.
  Qed.
  *)

  (* Instance for &raw mut, in the case that the place type is AliasLtype. This case is fairly trivial. *)
  Lemma typed_addr_of_mut_end_alias π E L l l2 st rt r b2 bmin (T : typed_addr_of_mut_end_cont_t) :
    (⌜l2 = l⌝ -∗ T L _ (alias_ptr_t) l2 _ (AliasLtype rt st l2) r)
    ⊢ typed_addr_of_mut_end π E L l (AliasLtype rt st l2) r b2 bmin T.
  Proof.
    iIntros "HT". iIntros (????) "#CTX #HE HL Hincl Hl".
    rewrite ltype_own_alias_unfold /alias_lty_own. destruct b2 as [wl | | ]; [| done..].
    iDestruct "Hl" as "(%ly & %Hst & -> & %Hly & #Hlb & Hcred)".
    iSpecialize ("HT" with "[//]").
    iApply logical_step_intro. iExists _, _, _, _, _, _, _. iFrame.
    iSplitR; first done.
    rewrite !ltype_own_alias_unfold /alias_lty_own.
    iSplitL "Hcred". { eauto 8 with iFrame. }
    iSplitR. { eauto 8 with iFrame. }
    done.
  Qed.
  Global Instance typed_addr_of_mut_end_alias_inst π E L l l2 rt st r b2 bmin :
    TypedAddrOfMutEnd π E L l (AliasLtype rt st l2) r b2 bmin | 10 :=
    λ T, i2p (typed_addr_of_mut_end_alias π E L l l2 st rt r b2 bmin T).


  (* Instance for ofty *)
  (* TODO maybe remove the bmin part *)

  (* TODO: is there a good way to streamline all of these instances in a nice way?
      I have roughly the same duplication/problems for typed_write and typed_read and possibly typed_borrow_shr, too.
      Especially if we get more ltypes, that is really annoying.

     Maybe there is a nice notion of "simple ltypes" that admits generic lemmas for stuff like this, because it doesn't exploit the different ownership kinds in an interesting way?
     In that case, there should be a core of the definition that is the same in all these cases.

     if b ≠ Shared:
     l ◁ₗ[π, b] r @ lt -∗
     logical_step (l ◁ₗ[π, b] OpenedLtype lt lt lt .. ..)

     l ◁ₗ[π, Owned true] r @ lt -∗
     logical_step (l ◁ₗ[π, Owned false] r @ lt)

    *)

  (* TODO: should make typed_addr_of_mut_end available in cases where no strong updates are allowed.
      AliasLtype does now support that case. *)

  Lemma typed_addr_of_mut_end_owned π E L l {rt} (lt : ltype rt) r wl bmin (T : typed_addr_of_mut_end_cont_t) :
    ltype_owned_openable lt →
    T L _ (alias_ptr_t) l _ (AliasLtype rt (ltype_st lt) l) (#r)
    ⊢ typed_addr_of_mut_end π E L l lt #r (Owned wl) bmin T.
  Proof.
    iIntros (Hopen) "Hvs".
    iIntros (????) "#CTX #HE HL Hincl Hl".
    iApply fupd_logical_step.
    iMod (ltype_owned_openable_elim_logstep with "Hl") as "(Hl & Hs)"; first done.
    iApply logical_step_fupd.
    iApply (logical_step_wand with "Hs").
    iIntros "!> Hcreds".
    iPoseProof (ltype_own_make_alias with "Hl Hcreds") as "(Hl & Halias)".
    iModIntro. iExists _, _, _, _, _, _, _. iFrame. simp_ltypes.
    iSplitR; done.
  Qed.
  Global Program Instance tyepd_addr_of_mut_end_owned_ofty_inst π E L l {rt} (ty : type rt) r wl bmin :
    TypedAddrOfMutEnd π E L l (◁ ty)%I #r (Owned wl) bmin :=
    λ T, i2p (typed_addr_of_mut_end_owned π E L l (◁ ty)%I r wl bmin T _).
  Next Obligation. intros.  apply ltype_owned_openable_ofty. Qed.
  (* TODO more instances *)

  Lemma typed_addr_of_mut_end_uniq π E L l {rt} (lt : ltype rt) r κ γ bmin (T : typed_addr_of_mut_end_cont_t) :
    ltype_uniq_openable lt →
    li_tactic (lctx_lft_alive_count_goal E L κ) (λ '(κs, L2),
    T L2 _ (alias_ptr_t) l _ (OpenedLtype (AliasLtype rt (ltype_st lt) l) lt lt (λ ri ri', ⌜ri = ri'⌝) (λ ri ri', llft_elt_toks κs)) (#r))
    ⊢ typed_addr_of_mut_end π E L l lt #r (Uniq κ γ) bmin T.
  Proof.
    iIntros (Hopen). rewrite /lctx_lft_alive_count_goal.
    iDestruct 1 as (κs L2) "(%Hcount & HT)".
    iIntros (????) "#CTX #HE HL Hincl Hl".
    iPoseProof (ltype_own_has_layout with "Hl") as "(%ly & %Halg & %Hly)".
    iPoseProof (ltype_own_loc_in_bounds with "Hl") as "#Hlb"; first done.
    iApply fupd_logical_step.
    iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
    iMod (lctx_lft_alive_count_tok lftE with "HE HL") as "(%q & Htok & Hcl_tok & HL)"; [done.. | ].
    iMod ("Hcl_F") as "_".
    iPoseProof (Hopen with "CTX Htok Hcl_tok Hl") as "Hs"; first done.
    iApply logical_step_fupd.
    iMod "Hs". iApply logical_step_intro.
    iIntros "!>!>".
    iPoseProof (opened_ltype_acc_uniq with "Hs") as "(Hl & Hl_cl)".
    iPoseProof (ltype_own_make_alias false with "Hl [//]") as "(Hl & Halias)".
    iPoseProof ("Hl_cl" with "Halias []") as "Hopened".
    { simp_ltypes. done. }
    iExists _, _, _, _, _, _, _. iFrame. simp_ltypes.
    iSplitR; done.
  Qed.
  Global Program Instance tyepd_addr_of_mut_end_uniq_ofty_inst π E L l {rt} (ty : type rt) r κ γ bmin :
    TypedAddrOfMutEnd π E L l (◁ ty)%I #r (Uniq κ γ) bmin :=
    λ T, i2p (typed_addr_of_mut_end_uniq π E L l (◁ ty)%I r κ γ bmin T _).
  Next Obligation. intros. apply ltype_uniq_openable_ofty. Qed.
  (* TODO more instances *)


  (** ExtractValueAnnot *)
  Lemma type_extract_value_annot_alias π E L n v l (T : typed_annot_expr_cont_t) :
    find_in_context (FindLoc l π) (λ '(existT rt (lt, r, bk)),
      ∃ wl ty r', ⌜bk = Owned wl⌝ ∗ ⌜lt = ◁ty⌝ ∗ ⌜r = #r'⌝ ∗
      (⌜Nat.b2n wl ≤ n⌝ ∗
      li_tactic (compute_layout_goal ty.(ty_syn_type)) (λ ly,
      (∀ v3, v3 ◁ᵥ{π} r' @ ty -∗ l ◁ₗ[π, Owned wl] #v3 @ (◁ value_t (UntypedSynType ly)) -∗ T L v _ alias_ptr_t l))))
    ⊢ typed_annot_expr π E L n ExtractValueAnnot v (v ◁ᵥ{π} l @ alias_ptr_t) T.
  Proof.
    rewrite /FindLoc.
    iIntros "(%a & Hl & HT)". destruct a as [rt [[lt r] bk]].
    iDestruct "HT" as "(%wl & %ty & %r' & -> & -> & -> & HT)".
    rewrite /compute_layout_goal. simpl.
    iDestruct "HT" as "(%Hle & %ly & %Hst & HT)".
    iIntros "#CTX #HE HL Halias". iApply step_fupdN_intro; first done.
    rewrite (ltype_own_ofty_unfold ty) /lty_of_ty_own.
    iDestruct "Hl" as "(%ly' & % & % & Hsc & Hlb & Hcreds & %r & <- & Hb)".
    assert (ly' = ly) as -> by by eapply syn_type_has_layout_inj.
    iPoseProof (bi.laterN_le _ n with "Hb") as "Hb"; first done.
    iNext.
    iMod (fupd_mask_mono with "Hb") as "(%v3 & Hl & Hv)"; first done.
    iPoseProof (value_split _ _ _ _ (UntypedSynType _) with "Hv") as "(Hv' & Hv)".
    { split; first done. eapply syn_type_has_layout_make_untyped; done. }
    iDestruct ("HT" with "Hv [Hl Hv' Hlb Hcreds]") as "HT".
    { rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iExists _. simpl.
      iSplitR. { iPureIntro. eapply syn_type_has_layout_make_untyped; done. }
      iSplitR; first done. iFrame.
      iExists _. iSplitR; first done. iModIntro.
      iExists v3. by iFrame. }
    iExists L, _, _, _. by iFrame.
  Qed.
  Global Instance type_extract_value_annot_alias_inst π E L n v l :
    TypedAnnotExpr π E L n ExtractValueAnnot v (v ◁ᵥ{π} l @ alias_ptr_t)%I :=
    λ T, i2p (type_extract_value_annot_alias π E L n v l T).

End alias_ltype.

Global Typeclasses Opaque alias_ptr_t.
