From refinedrust Require Export type ltypes programs .
From refinedrust Require Import uninit.
From iris Require Import options.

(** * A type modelled after Rust's MaybeUninit *)
(** We do not represent this directly with a union abstraction for simplicity, but rather directly define what the Rust memory representation of [MaybeUninit] is. *)

Section type.
  Context `{!typeGS Σ}.

  (** We refine by [option (place_rfn rt)] in order to borrow the optional contents.
     Note that this really makes it isomorphic to [MaybeUninit<T>] in our model,
     which is a union and thus would also get the place wrapper. *)
  Program Definition maybe_uninit {rt} (T : type rt) : type (option (place_rfn rt)) := {|
    ty_own_val π r v :=
      match r with
      | Some r' => ∃ r'', place_rfn_interp_owned r' r'' ∗ T.(ty_own_val) π r'' v
      | None => (uninit T.(ty_syn_type)).(ty_own_val) π () v
      end%I;
    ty_syn_type := T.(ty_syn_type);   (* TODO: but every value is valid! - so in principle, this should be Untyped *)
    _ty_has_op_type ot mt :=  ∃ ly, syn_type_has_layout T.(ty_syn_type) ly ∧ ot = UntypedOp ly;
    ty_shr κ π r l :=
      match r with
      | Some r' => ∃ r'', place_rfn_interp_shared r' r'' ∗ T.(ty_shr) κ π r'' l
      | None => (uninit T.(ty_syn_type)).(ty_shr) κ π () l
      end%I;
    ty_sidecond := True;
    ty_ghost_drop π r := True%I; (* TODO ? *)
    ty_lfts := T.(ty_lfts);
    ty_wf_E := T.(ty_wf_E);
  |}.
  Next Obligation.
    iIntros (rt T π r v) "Hv". destruct r as [r | ].
    - iDestruct "Hv" as "(%r'' & Hrfn & Hv)".
      iApply (ty_has_layout with "Hv").
    - iApply (ty_has_layout with "Hv").
  Qed.
  Next Obligation.
    simpl; iIntros (rt T ot mt Hot).
    destruct Hot as (ly & Hot & ->). done.
  Qed.
  Next Obligation.
    iIntros (rt T π r v) "_". done.
  Qed.
  Next Obligation.
    iIntros (rt T ? π r v) "_". done.
  Qed.
  Next Obligation.
    iIntros (rt T κ π l r) "Hl". destruct r as [r | ].
    - iDestruct "Hl" as "(%r'' & Hrfn & Hl)". iApply (ty_shr_aligned with "Hl").
    - iApply (ty_shr_aligned with "Hl").
  Qed.
  Next Obligation.
    iIntros (rt T E κ l ly π [r | ] ? ?) "#CTX Htok %Hst %Hly #Hlb Hb".
    -
      iAssert (&{κ} (∃ r', place_rfn_interp_owned r r' ∗ ∃ v : val, l ↦ v ∗ v ◁ᵥ{π} r' @ T))%I with "[Hb]" as "Hb".
      { iApply (bor_iff with "[] Hb"). iNext. iModIntro. iSplit.
        - iIntros "(%v & ? & %r' & ? & ?)". eauto with iFrame.
        - iIntros "(%r' & ? & %v & ? & ?)". eauto with iFrame. }
      iDestruct "CTX" as "(LFT & TIME & LLCTX)".
      iApply fupd_logical_step.
      rewrite -lft_tok_sep. iDestruct "Htok" as "(Htok1 & Htok2)".
      iMod (bor_exists_tok with "LFT Hb Htok1") as "(%r' & Hb & Htok1)"; first done.
      iMod (bor_sep with "LFT Hb") as "(Hrfn & Hb)"; first done.
      iMod (place_rfn_interp_owned_share with "LFT Hrfn Htok1") as "(Hrfn & Htok1)"; first done.
      iCombine ("Htok1 Htok2") as "Htok". rewrite lft_tok_sep.
      iPoseProof (ty_share _ E with "[$LFT $TIME $LLCTX] Htok [//] [//] Hlb Hb") as "Hstep"; first done.
      iApply (logical_step_wand with "Hstep").
      iIntros "!> (Hl & $)". eauto with iFrame.
    - rewrite -lft_tok_sep. iDestruct "Htok" as "[Htok1 Htok2]".
      (*iAssert (&{κ} (ty_sidecond T ∗ ∃ v : val, l ↦ v ∗ v ◁ᵥ{π} .@ uninit (ty_syn_type T)))%I with "[Hb]" as "Hb".*)
      (*{ iApply (bor_iff with "[] Hb"). iNext. iModIntro. iSplit.*)
        (*- iIntros "(%v & ? & ? & ?)". eauto with iFrame.*)
        (*- iIntros "($ & ?)". done. }*)
      (*iDestruct "CTX" as "(LFT & TIME & LLCTX)".*)
      (*iApply fupd_logical_step. iMod (bor_sep with "LFT Hb") as "(_ & Hb)"; first done.*)
      iPoseProof ((uninit _).(ty_share) with "CTX [Htok1] [] [//] [//] Hb") as "Ha"; simpl; first done.
      { rewrite right_id. done. }
      { done. }
      iApply (logical_step_wand with "Ha"). iIntros "($ & Htok1)".
      rewrite right_id. iFrame.
  Qed.
  Next Obligation.
    iIntros (rt T κ κ' π r l) "#Hincl Ha".
    destruct r as [r | ]; last by iApply ty_shr_mono.
    iDestruct "Ha" as "(%r'' & ? & Hv)".
    iExists _. iFrame. by iApply ty_shr_mono.
  Qed.
  Next Obligation.
    iIntros (rt T π r v F ?) "?". iApply logical_step_intro. done.
  Qed.
  Next Obligation.
    iIntros (rt T ot mt st π r v (ly & Hst & ->)) "Ha".
    destruct mt; [done | | done].
    destruct r as [r | ]; simpl; done.
  Qed.
End type.

Global Typeclasses Opaque maybe_uninit.

Section subtype.
  Context `{!typeGS Σ}.

  (** Subtyping *)
  Lemma type_incl_maybe_uninit_Some {rt} (ty : type rt) (x : rt) :
    ⊢ type_incl x (Some (#x)) ty (maybe_uninit ty).
  Proof.
    iSplitR; first done. iSplitR; first iModIntro. { simpl. eauto. }
    iSplit; iModIntro.
    - iIntros (π v) "Hv". iExists x. eauto with iFrame.
    - iIntros (κ π l) "Hl". iExists x. eauto with iFrame.
  Qed.

  Lemma type_incl_Some_maybe_uninit {rt} (ty : type rt) (x : rt) :
    ty_sidecond ty -∗
    type_incl (Some (#x)) x (maybe_uninit ty) ty.
  Proof.
    iIntros "#Hsc". iSplitR; first done. iSplitR; first iModIntro. { simpl; eauto. }
    iSplit; iModIntro.
    - rewrite {1}/ty_own_val/=. iIntros (π v) "(% & <- & Hv)". done.
    - rewrite {1}/ty_shr/=. iIntros (κ π v) "(% & <- & Hl)". done.
  Qed.

  Lemma type_incl_maybe_uninit_None {rt} (ty : type rt) :
    ⊢ type_incl () None (uninit (ty.(ty_syn_type))) (maybe_uninit ty).
  Proof.
    iSplitR; first done. iSplitR; first iModIntro. { simpl. eauto. }
    iSplit; iModIntro.
    - iIntros (π v) "Hv". done.
    - iIntros (κ π l) "Hl". done.
  Qed.

  Lemma type_incl_None_maybe_uninit {rt} (ty : type rt) :
    ⊢ type_incl None () (maybe_uninit ty) (uninit (ty.(ty_syn_type))).
  Proof.
    iSplitR; first done. iSplitR; first iModIntro. { simpl. eauto. }
    iSplit; iModIntro.
    - iIntros (π v) "Hv". done.
    - iIntros (κ π l) "Hl". done.
  Qed.

End subtype.

Section rules.
  Context `{!typeGS Σ}.

  (** subtyping rules: *)

  Lemma weak_subtype_None_maybe_uninit E L {rt} (ty : type rt) (r2 : unit) T :
    ⌜r2 = tt⌝ ∗ T ⊢ weak_subtype E L None r2 (maybe_uninit ty) (uninit ty.(ty_syn_type)) T.
  Proof.
    iIntros "(-> & HT)" (??) "#CTX #HE HL". iFrame. by iApply type_incl_None_maybe_uninit.
  Qed.
  Global Instance weak_subtype_None_maybe_uninit_None_inst E L {rt} (ty : type rt) r2 :
    Subtype E L None r2 (maybe_uninit ty) (uninit (ty.(ty_syn_type))) := λ T, i2p (weak_subtype_None_maybe_uninit E L ty r2 T).

  Lemma weak_subtype_maybe_uninit_None E L {rt} (ty : type rt) r2 T :
    ⌜r2 = None⌝ ∗ T ⊢ weak_subtype E L () r2 (uninit ty.(ty_syn_type)) (maybe_uninit ty) T.
  Proof.
    iIntros "(-> & HT)" (??) "#CTX #HE HL". iFrame. by iApply type_incl_maybe_uninit_None.
  Qed.
  Global Instance weak_subtype_maybe_uninit_None_inst E L {rt} (ty : type rt) r2 :
    Subtype E L () r2 (uninit (ty.(ty_syn_type))) (maybe_uninit ty) := λ T, i2p (weak_subtype_maybe_uninit_None E L ty r2 T).

  Lemma weak_subtype_Some_maybe_uninit E L {rt} (ty : type rt) (x : place_rfn rt) r2 T :
    (∃ x', ⌜x = #x'⌝ ∗ ⌜r2 = x'⌝ ∗ ty_sidecond ty ∗ T) ⊢ weak_subtype E L (Some x) r2 (maybe_uninit ty) ty T.
  Proof.
    iIntros "(%x' & -> & -> & Hsc & HT)" (??) "#CTX #HE HL". iFrame. by iApply type_incl_Some_maybe_uninit.
  Qed.
  Global Instance weak_subtype_Some_maybe_uninit_inst E L {rt} (ty : type rt) (x : place_rfn rt) r2 :
    Subtype E L (Some x) r2 (maybe_uninit ty) ty := λ T, i2p (weak_subtype_Some_maybe_uninit E L ty x r2 T).

  Lemma weak_subtype_maybe_uninit_Some E L {rt} (ty : type rt) (x : rt) r2 T :
    ⌜r2 = Some #x⌝ ∗ T ⊢ weak_subtype E L x r2 ty (maybe_uninit ty) T.
  Proof.
    iIntros "(-> & HT)" (??) "#CTX #HE HL". iFrame. iApply type_incl_maybe_uninit_Some.
  Qed.
  Global Instance weak_subtype_maybe_uninit_Some_inst E L {rt} (ty : type rt) (x : rt) r2 :
    Subtype E L x r2 ty (maybe_uninit ty) := λ T, i2p (weak_subtype_maybe_uninit_Some E L ty x r2 T).

  Lemma weak_subltype_maybe_uninit_ghost E L {rt} (ty : type rt) γ r2 T :
    ⌜r2 = #(Some (👻 γ))⌝ ∗ T
    ⊢ weak_subltype E L (Owned false) (👻 γ) r2 (◁ ty) (◁ (maybe_uninit ty)) T.
  Proof.
    iIntros "(-> & HT)".
    iIntros (??) "#CTX #HE HL". iFrame. iModIntro.
    iSplitR; first done.
    iModIntro. simp_ltypes.
    rewrite -bi.persistent_sep_dup.
    iModIntro. iIntros (π l) "Hl".
    rewrite !ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hl" as "(%ly & %Hst & %Hly & Hsc & Hlb & Hcreds & %r' & Hrfn & Hl)".
    iMod "Hl" as "(%v & Hl & Hv)".
    iModIntro. iExists ly. iR. iR. iSplitR. { rewrite /maybe_uninit. done. }
    iFrame. iExists (Some (👻 γ)). iR. iModIntro.
    iExists v. iFrame. rewrite {2}/ty_own_val/=.
    eauto with iFrame.
  Qed.
  Global Instance weak_subltype_maybe_uninit_ghost_inst E L {rt} (ty : type rt) γ r2 :
    SubLtype E L (Owned false) (👻 γ) r2 (◁ ty)%I (◁ (maybe_uninit ty))%I | 40 :=
    λ T, i2p (weak_subltype_maybe_uninit_ghost E L ty γ r2 T).

  Lemma owned_subtype_uninit_maybe_uninit π E L pers {rt} (ty : type rt) (st : syn_type) T :
    li_tactic (compute_layout_goal st) (λ ly1,
      li_tactic (compute_layout_goal (ty_syn_type ty)) (λ ly2,
        ⌜ly_size ly1 = ly_size ly2⌝ ∗ T L))
    ⊢ owned_subtype π E L pers () None (uninit st) (maybe_uninit ty) T.
  Proof.
    rewrite /compute_layout_goal.
    iIntros "(%ly1 & %Halg1 & %ly2 & %Halg2 & %Hsz & HT)".
    iIntros (???) "#CTX #HE HL". iExists L. iModIntro. iFrame.
    iApply bi.intuitionistically_intuitionistically_if. iModIntro.
    iSplit; last iSplitR.
    { iPureIntro. simpl. intros ly3 ly4 Hst3 Hst4.
      assert (ly1 = ly3) as <- by by eapply syn_type_has_layout_inj.
      assert (ly4 = ly2) as <- by by eapply syn_type_has_layout_inj.
      done. }
    { simpl. done. }
    iIntros (v) "Hv". rewrite {2}/ty_own_val/=. rewrite /ty_own_val/=.
    iDestruct "Hv" as "(%ly &  %Hst & %Hly & _)".
    assert (ly1 = ly) as <- by by eapply syn_type_has_layout_inj.
    iExists _. iR. iSplit.
    - iPureIntro. rewrite /has_layout_val -Hsz//.
    - iPureIntro. eapply Forall_forall; done.
  Qed.
  Global Instance owned_subtype_uninit_maybe_uninit_inst π E L pers {rt} (ty : type rt) st :
    OwnedSubtype π E L pers () None (uninit st) (maybe_uninit ty) :=
    λ T, i2p (owned_subtype_uninit_maybe_uninit π E L pers ty st T).

  (* reading/writing:
     does this need special handling?

     We certainly need some handling for read/write rules to inject into maybe_uninit when necessary, esp. below arrays.
  *)
  (* TODO: add these rules *)


  (** borrowing rules: *)
  (* for now, just don't allow borrowing maybe_uninit directly and handle it specially.
     TODO: in future, have an annotation for borrowing that enforces invariants. *)
  (* TODO: add the override *)



End rules.



  (*
     What happens with borrowing?
     - if it is Some, I want to create a borrow for the whole thing.
        To do that, I will probably need a place rule that just makes a maybeuninit into the inner type for the place access, and in the continuation wraps it again.
     - what happens with the blocked then? I cannot wrap a blocked directly in this type.
       In principle, this is fine from the perspective of the mutref contract, because the borrow enforces that I actually get a T back, so it is fine to put a Some there.
       Should I just bubble the blocked up (i.e. use openedltype/coreable)?
       In principle I know that I will get a maybe_uninit T back after the borrow ends, so this is fine intuitively. The only diff is how the ghost resolution does stuff. (NOTE: here ghost resolution would need to descend below the maybeuninit. But I have the right infrastructure for that, we just need to add a ghost_resolve instance for ◁ (maybe_uninit T)
       So I guess the place instance will just work via openedltype.
   *)

  (*
     How will the write of an initialized element to a maybeuninit location look?
     - in principle, if we can write strongly, just write. OpenedLtype closing should later apply the subtyping rule for injection into maybe_uninit.

     - for an array_ltype, subtyping should work elementwise. The openedltype in that case will require to go to an array where every field has the same type. Afterwards, that can be folded to an array_type again.


     TODO one thing to think about: we can't do refinement type updates for array_ltype, so we need to do the injection already at time of writing.
     How should writing work?
      - have: current type of place (ltype), type of value to write
      - options for rules we can use:
        + do a strong write, just put in the current value at its type.
        + do a strong write, but just put in a value_t for the written value and assemble ownership later on when needed.
        + directly adapt the type via subtyping so they match
      - we can also combine the options:
        + have specific instances (high priority) for particular combinations of types, and use one of the other options as default if they don't match.
          -> already doing that currently for writing to a mutltype etc.
          -> for maybe_uninit: have two specific instances for writing to it.
        + and then, as a fallback: just do a strong write (or decide based on the type change).

   *)

  (* Issue for borrowing:
     if we borrow a maybe_uninit T but really need a T, we need to know that and commit to it ahead of time (when borrowing) because of restricted subtyping.
     Solutions:
     - actually do a reborrow when subtyping, since the refinement gives us enough information
        then there's a lot of stuff happening there. it also needs later credits. so this gets quite fragile.
     - can we do the previous thing without reborrowing? could this ability be directly built into mut refs?
        in principle, stuff like this that is enabled by the refinements should be more natural.
        Point is: our refinement model is too inflexible. we need more leverage to say that the other case (None) is vacuous because of refinement info.
          - this is not quite true, because the lender will still expect the maybe_uninit back, not the full thing.
            in a sense, this case is really similar to the [u8; 2] ≈ u16 case. It's basically equivalent according to the intuitive notion of subtyping (taking into account the refinement) but it doesn't hold in our model.
     - have custom rules and just say that we generally borrow the T instead of the maybe_uninit when the refinement says so.
        this makes it a bit less flexible, but it's probably fine. the annoying part is that we have to duplicate the borrowing logic a bit.
     => TODO which of these makes most sense?
   *)
