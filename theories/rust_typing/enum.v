From refinedrust Require Export type ltypes.
From refinedrust Require Import uninit int.
From refinedrust Require Import products programs.
Set Default Proof Using "Type".

Section union.
  Context `{!typeGS Σ}.
  (** [active_union_t ty uls] basically wraps [ty] to lay it out in [uls], asserting that a union currently is in variant [variant].
      This is not capturing the allowed union layouting in Rust in full generality (Rust may freely choose the offsets of the variants),
      but we are anyways already not handling tags correctly, so who cares... *)
  (* TODO rather factor out into a padded type, as in RefinedC? *)
  Program Definition active_union_t {rt} (ty : type rt) (variant : string) (uls : union_layout_spec) : type rt := {|
    ty_own_val π r v :=
      (∃ ul ly, ⌜use_union_layout_alg uls = Some ul⌝ ∗
        ⌜layout_of_union_member variant ul = Some ly⌝ ∗
        take ly.(ly_size) v ◁ᵥ{π} r @ ty ∗
        drop ly.(ly_size) v ◁ᵥ{π} () @ uninit (UntypedSynType (ly_offset (ul : layout) ly.(ly_size))))%I;
    ty_syn_type := uls;
    ty_has_op_type ot mt :=
      (* we should not directly read from/write to this *)
      (* TODO: really? *)
      False;
    ty_shr κ π r l :=
      (∃ ul ly, ⌜use_union_layout_alg uls = Some ul⌝ ∗
        ⌜layout_of_union_member variant ul = Some ly⌝ ∗
        ⌜l `has_layout_loc` ul⌝ ∗
        l ◁ₗ{π, κ} r @ ty ∗
        (l +ₗ ly.(ly_size)) ◁ₗ{π, κ} () @ uninit (UntypedSynType (ly_offset (ul : layout) ly.(ly_size))))%I;
    ty_ghost_drop r := ty.(ty_ghost_drop) r;
    ty_lfts := ty_lfts ty;
    ty_wf_E := ty_wf_E ty;
    ty_sidecond := True;
  |}.
  Next Obligation.
    iIntros (rt ty var uls π r v) "(%ul & %ly & % & % & Hv & Hvr)".
    iExists ul.
    iSplitR. { iPureIntro. by apply use_union_layout_alg_Some_inv. }
    iPoseProof (ty_has_layout with "Hv") as "(%ly' & %Halg0 & %Hv0)".
    rewrite uninit_own_spec. iDestruct "Hvr" as "(% & %Halg1 & %Hv1)".
    iPureIntro. apply syn_type_has_layout_untyped_inv in Halg1 as (-> & _ & _).
  Admitted.
  Next Obligation.
    done.
  Qed.
  Next Obligation.
    eauto.
  Qed.
  Next Obligation.
    iIntros (????????) "(%ul & %ly & % & % & % & _)". iExists ul.
    iSplitR; first done. iPureIntro. by eapply use_union_layout_alg_Some_inv.
  Qed.
  Next Obligation.
    iIntros (rt ty variant uls E κ l ly π r q ?) "CTX Htok %Halg %Hly #Hlb Hb".
  Admitted.
  Next Obligation.
    iIntros (rt ty variant uls κ κ' π r l) "#Hincl Hb".
  Admitted.
  Next Obligation.
    iIntros (?????????) "Hb".
    iDestruct "Hb" as "(%ul & %ly & %Halg & %Hly & Hv & _)".
    iPoseProof (ty_own_ghost_drop with "Hv") as "Ha"; last iApply (logical_step_wand with "Ha"); eauto.
  Qed.
  Next Obligation.
    done.
  Qed.
End union.

(*
  Design decisions and considerations:
  - What is enum refined by? Should be refined by the tag and the refinement of the respective component.
    Several ways to encode that:
    1) have a Coq type that subsumes both, with projections into an index for the tag and the refinement
    2) have two separate things: a tag (either a string, an index, or a member of a Coq type), and a sum of the refinement types. Only certain combinations are valid, of course.
    3)


  RefinedC  defines the tagged union type directly in terms of struct: containing the tag and the actual data.
  It basically takes the approach 1).
  + this just directly unfolds to the struct.
  further types:
    - variant ti r ty is ownership of the padded full union chunk storing ty; where r is the refinement of the whole union and thus also defines the variant
      => typed_place with GetMemberUnion on this basically focusses on the segment actually storing ty.
    - tag ti r defines ownership of the integer tag corresponding to r.
      => there is a subsumption instance from int to this.
    -
 *)

(*

  To avoid some of the complication of separate variant + data assignment:
    can I just do a fused assignment?
  Caveats:
   - less realistic, in particular due to how assignment to unions works in the bag-of-bytes model: we are really writing the full union now using an UntypedOp, whereas otherwise we would do a typed write of just the part of the representation that is relevant.
   - a bit of frontend work, but should be fairly easy.

  Enum ltype setup:
  Variant 1:
  - by default have a EnumLtype els with a current ltype for the data of the current variant (we need this specific additional ltype in order to be able to do borrows)
  - note that we will need an unfolding lemma that looks slightly differently from the usual thing which talks about the current variant (i.e. depends on the refinement)
  - imp unblockable lemma: states that the enum is unblockable if the current_lt is unblockable to something which matches the type dictated by the variant.
  - by itself, this will support strong updates for the contained thing. We don't have an active coupling to the tag at that point.
  => does this have disadvantages?
  + switching to this constitutes a strong update, similar to switching to OpenedLtype.
    So we need to open borrows for that.
  +
  => can we just use OpenedLtype for that?
   - every enum access will just unfold it.
   [- NO, it currently is not flexible enough to do that, because the Cpre/Cpost do not have access to the types.]
   - it is expressible by just taking as lt_inner the ◁ enum -- if we are unblockable to that, everything is fine.
     Then we need a pretty powerful subtyping/prove_place_cond, however.

  Variant 1.5:
  - have its own ltype. We could still use coreable to implement stuff below borrows.

  Variant 2:
  - like variant 1, but maintain an active coupling to the tag field.
    we always require the core of the current thing to be equivalent to the type prescribed by the tag.
  - this variant does not allow to do storng updates below.
    If we want to do a strong update, e.g. move something out temporarily, we need to use an OpenedLtype above.
    Here the condition is expressible already -- we just need to get something whose core goes to the full enum.


  How would I do separate assignment for this implementation?
  For Variant 1:
  + nothing interesting happens, because we anways just have an openedltype which just does "plain data".
  For Variant 1.5:
  + we need to do a bit of work, but there's nothing fundamentally difficult here.
  For Variant 2:
  + the place access lemma for this will put an OpenedLtype above (with lt_inner = full enum, so similar to Variant 1), so we can still do strong updates below.
  + afterwards, we would write the new tag.
  + at that point, we could re-establish the invariant. However, how do we detect that?
    It would essentially need to happen on-demand, e.g. when reading (we'd require a FoldOpened anyways).

  It seems like for separate assignments, Variant 1 is more convenient (for variant 2, we basically put variant 1 on top).
  It seems like for just regular stuff, Variant 2 might be nicer, because we don't need to open borrows etc all the time.

  Is there a reason why we should not just keep borrows open all the time?
   - e.g. something related to semantic safety and panics?
     does it destroy our panic freedom plans?
     What I can imagine is this: everytime we call into something which might panic, we need to prove that the panic handler, i.e. the unwinding path, also plays out correctly, and pass a proof of that to the function.
     Basically, in that path we would then need to show that everything checks out, i.e. we can close everything properly.
     But that should not be that difficult, i.e. it should be fine as long as we can restore it again, which we can usually do.
   -

       Then what is the difference to just requiring magic wands everywhere and using that as your interface?
       i.e. would unfolding all of my stuff into aliases at the start of the function be a valid approach?
       - in RustBelt it certainly is, when you do manual proofs.
       The Q here is really mostly from an automation perspective.
       - we need to consider what happens at calls.
       - how well does it work for nesting to just do magic wands?
      This question is mostly orthogonal. Quite possibly it would work in a different way -- but it's not at all clear how well. Especially if we consider automating it in a system like Coq. Magic wands are pretty hard in general, and the structure enforced by having proper borrows etc. certainly helps us.
      It also makes semantic safety arguments easier.
      HOWEVER, for shared references there is a very clear argument (in terms of seplogic specification) what this buys us!
      Sharing in e.g. refinedc is MUCH less expressive, and it's difficult to emulate Rust-style sharing with magic wands and fractions.

  For now, go with variant 1 and see how well it works.
 *)

Section enum.
  Context `{!typeGS Σ}.


  (* let's try to do it similarly *)
  Record enum (rt : Type) : Type := mk_enum {
    (* the layout spec *)
    enum_els : enum_layout_spec;
    (* out of the current refinement, extract the tag *)
    enum_tag : rt → var_name;
    (* out of the current refinement, extract the component type and refinement *)
    enum_ty : rt → sigT (λ rt' : Type, type rt' * rt')%type;
    (* convenience function: given the variant name, also project out the type *)
    enum_variant_ty : var_name → option (sigT type);
    (* explicitly track the lifetimes each of the variants needs -- needed for sharing *)
    enum_lfts : list lft;
    enum_wf_E : elctx;
    enum_lfts_complete : ∀ (r : rt), ty_lfts (projT2 (enum_ty r)).1 ⊆ enum_lfts;
    enum_wf_E_complete : ∀ (r : rt), ty_wf_E (projT2 (enum_ty r)).1 ⊆ enum_wf_E;
  }.
  Global Arguments mk_enum {_}.
  Global Arguments enum_els {_}.
  Global Arguments enum_tag {_}.
  Global Arguments enum_ty {_}.
  Global Arguments enum_variant_ty {_}.
  Global Arguments enum_lfts {_}.
  Global Arguments enum_wf_E {_}.

  Definition enum_lookup_tag {rt} (e : enum rt) (r : rt) :=
    els_lookup_tag e.(enum_els) (e.(enum_tag) r).

  (* For constructing the enum, we need to provide a hint that computes the refinement of the enum fromt the variant and its refinement.
     Note that, crucially, also the [e : enum rto] is already an input to this typeclass (determined by the [rust_type] annotation on [EnumInit]), because we need the type parameters of the enum to already be determined.
     (As an example, imagine constructing the [None] variant of [Option<T>]).
  *)
  Class ConstructEnum {rti rto} (e : enum rto) (variant : string) (ty : type rti) (input : rti) (out : rto) : Type := construct_enum {
    (* sidecondition that we need to solve *)
    (*construct_enum_sc : Prop;*)
    (* agreemtn that we get as a result *)
    construct_enum_proof : e.(enum_ty) out = existT _ (ty, input) ∧ e.(enum_tag) out = variant;
  }.
  Global Hint Mode ConstructEnum + + + + + + - : typeclass_instances.
  Global Arguments construct_enum {_ _ _ _ _ _}.

  (* NOTE Place design:
      - place access should always directly go to one variant, or to the tag.
      - don't allow strong updates, just as for array.

      We should then have one place type that encapsulates the enum.
      Main point: we need to pad it properly.
      That shouldn't be a big point though, because we do not expose this part of the representation.
       It should not need its own type/place type.
       We do not need to treat with these types independelty etc.
      Maybe having some core abstraction for that would make sense though.

    *)


  (*
    When reading the discriminant: want to get the integer associated to the variant, because we need it for a switch.
    When initializing an enum value with EnumInit: need to map from the variant to the full type. i.e. need to invert the map we currently have? that sounds complicated.
    When reading a field: just need to get the field refinement, we can do that now.


    For initialization:
     interpret rust type, require it to syntactically be enum e : type rt
      Then find the typeclass instance for ConstructEnum using tc_..
      get the output refinement.
      Then can directly construct it.
   *)

  (* Q: when accessing, how do we unfold it?
      Should we have a variant of [enum] for ltypes?
      I guess, maybe.
      Or maybe have an ltype override parameter. That seems easier.
      However, then we get nasty dependent typing, since the type of that parameter has to depend on the type of the refinement..

      I guess we should just fix the ltype to have a specific variant. Then it's just dependent on another parameter.
      This anyways makes sense, semantically.
   *)

  (* NOTE: for now, we only support untyped reads from enums.
      To handle this more accurately, we should probably figure out the proper model for enums with niches etc first. *)
  Definition is_enum_ot {rt} (en : enum rt) (ot : op_type) (mt : memcast_compat_type) :=
    match ot with
    | UntypedOp ly =>
        ∃ el : struct_layout, use_enum_layout_alg en.(enum_els) = Some el ∧
        ly = el ∧
        foldr (λ '(v, st) P,
            ∃ rty ly',
            en.(enum_variant_ty) v = Some rty ∧
            syn_type_has_layout st ly' ∧
            ty_has_op_type (projT2 rty) (UntypedOp ly') mt
          ) True (en.(enum_els).(els_variants))
    | _ => False
    end.


  (* NOTE: in principle, we might want to formulate this with [ex_plain_t] as an existential abstraction over a struct.
     However, here the inner type also depends on the outer refinement, which is not supported by [ex_plain_t] right now. *)
  Program Definition enum_t {rt} (e : enum rt) : type rt :=
    {|
    ty_own_val π r v :=
      (∃ rt' ty' r' ly,
      ⌜e.(enum_ty) r = existT rt' (ty', r')⌝ ∗
      ⌜syn_type_has_layout e.(enum_els) ly⌝ ∗
      (* we cannot directly borrow the variant or data fields while in this interpretation *)
      v ◁ᵥ{π} -[#(enum_lookup_tag e r); #r'] @ struct_t (sls_of_els e.(enum_els))
        +[int e.(enum_els).(els_tag_it); active_union_t ty' (e.(enum_tag) r) (uls_of_els e.(enum_els))])%I;
    ty_shr κ π r l :=
      (∃ rt' ty' r' ly,
      ⌜e.(enum_ty) r = existT rt' (ty', r')⌝ ∗
      ⌜syn_type_has_layout e.(enum_els) ly⌝ ∗
      l ◁ₗ{π, κ} -[#(enum_lookup_tag e r); #r'] @ struct_t (sls_of_els e.(enum_els))
        +[int e.(enum_els).(els_tag_it); active_union_t ty' (enum_tag e r) (uls_of_els e.(enum_els))])%I;
    ty_syn_type := e.(enum_els);
    ty_has_op_type ot mt :=
      is_enum_ot e ot mt;
    ty_sidecond := True%I;
    ty_ghost_drop π r := True%I; (* TODO *)
    ty_lfts := e.(enum_lfts);
    ty_wf_E := e.(enum_wf_E);
  |}.
  Next Obligation.
    iIntros (rt e π r v).
    iIntros "(%rt' & %ty' & %r' & %ly & %Heq & %Halg & Hv)".
    specialize (syn_type_has_layout_els_sls _ _ Halg) as (sl & Halg' & ->).
    iPoseProof (ty_own_val_has_layout with "Hv") as "%Hlyv".
    { simpl. by apply use_struct_layout_alg_Some_inv. }
    iExists sl. done.
  Qed.
  Next Obligation.
  Admitted.
  Next Obligation.
    eauto.
  Qed.
  Next Obligation.
    iIntros (rt e κ π l r) "(%rt' & %ty' & %r' & %ly & %Heqt & %Halg & Hl)".
    iPoseProof (ty_shr_aligned with "Hl") as "(%ly' & %Hly & %Halg')". simpl in *.
    specialize (syn_type_has_layout_els_sls _ _ Halg) as (sl & Halg'' & ->).
    apply use_struct_layout_alg_Some_inv in Halg''.
    assert (ly' =  sl) as -> by by eapply syn_type_has_layout_inj.
    iExists sl. done.
  Qed.
  Next Obligation.
    iIntros (rt e E κ l ly π r q ?) "#CTX Htok %Halg %Hly Hlb Hb".
    iAssert (&{κ} ((∃ (rt' : Type) (ty' : type rt') (r' : rt') (ly0 : layout), ⌜enum_ty e r = existT rt' (ty', r')⌝ ∗ ⌜syn_type_has_layout (enum_els e) ly0⌝ ∗ ∃ v : val, l ↦ v ∗ v ◁ᵥ{ π} -[# (enum_lookup_tag e r); # r'] @ struct_t (sls_of_els (enum_els e)) +[int (els_tag_it (enum_els e)); active_union_t ty' (enum_tag e r) (uls_of_els (enum_els e))])))%I with "[Hb]" as "Hb".
    { iApply (bor_iff with "[] Hb"). iNext. iModIntro.
      iSplit.
      - iIntros "(%v & Hl & % & % & % & % & ? & ? & ?)". eauto 8 with iFrame.
      - iIntros "(% & % & % & % & ? & ? & % & ? & ?)". eauto 8 with iFrame. }
    simpl. iEval (rewrite -lft_tok_sep) in "Htok". iDestruct "Htok" as "(Htok1 & Htok2)".
    iApply fupd_logical_step.
    iDestruct "CTX" as "(LFT & TIME & LLCTX)".
    iMod (bor_exists_tok with "LFT Hb Htok1") as "(%rt' & Hb & Htok1)"; first done.
    iMod (bor_exists_tok with "LFT Hb Htok1") as "(%ty' & Hb & Htok1)"; first done.
    iMod (bor_exists_tok with "LFT Hb Htok1") as "(%r' & Hb & Htok1)"; first done.
    iMod (bor_exists_tok with "LFT Hb Htok1") as "(%ly' & Hb & Htok1)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Heqt & Hb)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Halg & Hb)"; first done.
    iMod (bor_persistent with "LFT Heqt Htok1") as "(>%Heqt & Htok1)"; first done.
    iMod (bor_persistent with "LFT Halg Htok1") as "(>%Halg' & Htok1)"; first done.
    iPoseProof (list_incl_lft_incl_list (ty_lfts ty') (enum_lfts e)) as "Hincl".
    { etrans; last eapply (enum_lfts_complete _ e r). rewrite Heqt. done. }
    iMod (lft_incl_acc with "Hincl Htok2") as "(%q' & Htok2 & Htok2_cl)"; first done.
    iPoseProof (lft_tok_lb with "Htok1 Htok2") as "(%q'' & Htok1 & Htok2 & Htok_cl)".
    iCombine ("Htok1 Htok2") as "Htok".
    rewrite !lft_tok_sep.
    specialize (syn_type_has_layout_els_sls _ _ Halg) as (sl & Halg'' & ->).
    iPoseProof (ty_share _ E _ _ _ _ _ q'' with "[$] [Htok] [] [] Hlb Hb") as "Hstep"; first done.
    { simpl. rewrite right_id. done. }
    { simpl. iPureIntro. by apply use_struct_layout_alg_Some_inv. }
    { done. }
    simpl.
    iApply logical_step_fupd.
    iApply (logical_step_wand with "Hstep").
    iModIntro. iIntros "(Hl & Htok)".
    rewrite right_id -lft_tok_sep. iDestruct "Htok" as "(Htok1 & Htok2)".
    iPoseProof ("Htok_cl" with "Htok1 Htok2") as "(Htok1 & Htok2)".
    iMod ("Htok2_cl" with "Htok2") as "Htok2".
    rewrite -lft_tok_sep. iFrame.
    iExists rt', ty', r', _.
    iR. iR. by iFrame.
  Qed.
  Next Obligation.
    iIntros (rt e κ κ' π r l) "#Hincl (%rt' & %ty' & %r' & %ly & ? & ? & Hl)".
    iExists rt', ty', r', ly. iFrame.
    iApply (ty_shr_mono with "Hincl Hl").
  Qed.
  Next Obligation.
    iIntros (rt e π r v F ?) "Hv".
    iApply logical_step_intro. done.
  Qed.
  Next Obligation.
    iIntros (rt e ot mt st π r v ?) "Hl".
    (*done.*)
  (*Qed.*)
  Admitted.

  (* TODO non-expansiveness *)


  Global Instance enum_t_copyable {rt} (e : enum rt):
    (∀ r : rt, Copyable (projT2 (e.(enum_ty) r)).1) →
    Copyable (enum_t e).
  Proof.
    (* TODO *)
  Admitted.
End enum.

Section subtype.
  Context `{!typeGS Σ}.

  (* TODO: should probably have a subtyping condition on enum that lifts this element-wise. *)

End subtype.

Section unfold.
  Context `{!typeGS Σ}.

  (* TODO *)
End unfold.

Section rules.
  Context `{!typeGS Σ}.

  (* TODO move *)
  Lemma mjoin_pad_struct_layout sl els f :
    Forall2 (λ '(n, ly) v, v `has_layout_val` ly) (named_fields sl.(sl_members)) els →
    (∀ ly, length (f ly) = ly_size ly) →
    mjoin (pad_struct sl.(sl_members) els f) `has_layout_val` sl.
  Proof.
    rewrite /has_layout_val/layout_of{2}/ly_size/=.
    generalize (sl_members sl) => fields. clear sl.
    induction fields as [ | [[name | ] field] fields IH] in els |-*; simpl; first done.
    - intros Ha Hf. apply Forall2_cons_inv_l in Ha as (v & els' & Hlen & Ha%IH & ->); last done.
      rewrite app_length Ha Hlen. done.
    - intros Ha Hf. apply IH in Ha; last done. rewrite app_length Ha Hf//.
  Qed.

  Lemma big_sepL2_pad_struct (tys : list (sigT (λ rt, (type rt * rt)%type))) (els : list val) (defty : layout → sigT _) (defval : layout → val) fields Φ  :
    ([∗ list] i ↦ v; ty ∈ els; tys, ∃ j, ⌜field_index_of fields (named_fields fields !!! i).1 = Some j⌝ ∗ Φ j v ty) -∗
    ([∗ list] i ↦ v; ty ∈ pad_struct fields els defval; pad_struct fields tys defty, Φ i v ty) : iProp Σ.
  Proof.
    iIntros "Ha". iPoseProof (big_sepL2_length with "Ha") as "%Hleneq".
    iInduction els as [ | el els] "IH"; destruct tys as [ | ty tys].
    (* TODO *)
  Abort.

  Lemma type_enum_init π E L (els : enum_layout_spec) (variant : string) (rsty : rust_type) (e : expr) (T : typed_val_expr_cont_t) :
    ⌜enum_layout_spec_is_layoutable els⌝ ∗
    typed_val_expr π E L e (λ L2 v rti tyi ri,
      ⌜((list_to_map (els_variants els) : gmap _ _) !! variant) = Some (ty_syn_type tyi)⌝ ∗
      ∃ M, named_lfts M ∗ (named_lfts M -∗
      (* get the desired enum type *)
      li_tactic (interpret_rust_type_goal M rsty) (λ '(existT rto tyo),
        ∃ (e : enum rto), ⌜tyo = enum_t e⌝ ∗ ⌜e.(enum_els) = els⌝ ∗
        trigger_tc (ConstructEnum e variant tyi ri) (λ ro,
          (*⌜construct_enum_sc⌝ ∗*)
          ∀ v', T L2 v' _ (enum_t e) ro))))
    ⊢ typed_val_expr π E L (EnumInit els variant rsty e) T.
  Proof.
    iIntros "(%Hly & HT)". destruct Hly as [el Hly].
    iIntros (?) "#CTX #HE HL Hc".
    iApply wp_enum_init; first done.
    iApply ("HT" with "CTX HE HL [Hc]").
    iIntros (L2 v rt ty r) "HL Hv HT".
    iDestruct "HT" as "(%Hlook_st & %M & Hlfts & HT)".
    iPoseProof ("HT" with "Hlfts") as "HT".
    rewrite /interpret_rust_type_goal.
    iDestruct "HT" as "(%rto &  %tyo & %en & -> & <- & HT)".
    rewrite /trigger_tc. iDestruct "HT" as "(%ro & %Hc & HT)".
    iApply ("Hc" with "HL [Hv] HT").
    iEval (rewrite /ty_own_val/=).
    destruct Hc as [[Hproj Htag]].
    iExists _, _, _, _.
    iR. iSplitR. { iPureIntro. apply use_enum_layout_alg_Some_inv. apply Hly. }
    iEval (rewrite /ty_own_val/=).
    iExists el. iSplitR. { iPureIntro. apply use_enum_layout_alg_inv'. done. }
    iPoseProof (ty_has_layout with "Hv") as "(%ly & %Hst & %Hlyv)".
    iR.
    iSplitR. { iPureIntro. apply mjoin_pad_struct_layout; first last.
      { intros. rewrite replicate_length. done. }
      apply use_enum_layout_alg_inv in Hly as (ul & variant_lys & Hul & Hsl & Hf).
      apply struct_layout_alg_has_fields in Hsl. rewrite -Hsl.
      econstructor.
      { simpl.
        (* TODO should make that property hold in els. *)
        admit. }
      econstructor; last done.
      rewrite Hlook_st /use_layout_alg' Hst/=.
      rewrite /use_union_layout_alg'.
      erewrite use_union_layout_alg_Some; [ | done | done].
      simpl.
      rewrite /has_layout_val app_length replicate_length.
      rewrite /has_layout_val in Hlyv. rewrite Hlyv.
      enough (ly_size ly ≤ ly_size ul) by lia.
      apply union_layout_alg_has_variants in Hul as ->.
      apply elem_of_list_to_map_2 in Hlook_st.
      apply elem_of_list_lookup_1 in Hlook_st as (i & Hlooki).
      eapply Forall2_lookup_l in Hf; last done.
      destruct Hf as ([name ly'] & Hul & -> & Hst').
      assert (ly' = ly) as -> by by eapply syn_type_has_layout_inj.
      rewrite {2}/ly_size /ul_layout/=.
      apply max_list_elem_of_le. rewrite elem_of_list_fmap.
      eexists. split; first done. apply elem_of_list_fmap.
      exists (name, ly). split; first done.
      by eapply elem_of_list_lookup_2.
    }
    rewrite reshape_join.
    2: { admit. }
    (* TODO use big_sepL2_pad_struct *)
  Admitted.

  (* TODO: would really like to have this lemma instead, but the dependent typing for the evars is trouble *)
  (*
  Lemma type_enum_init π E L (els : enum_layout_spec) (variant : string) (rsty : rust_type) (e : expr) (T : typed_val_expr_cont_t) :
    ⌜enum_layout_spec_is_layoutable els⌝ ∗
    typed_val_expr π E L e (λ L2 v rti tyi ri,
      ⌜((list_to_map (els_variants els) : gmap _ _) !! variant) = Some (ty_syn_type tyi)⌝ ∗
      ∃ M, named_lfts M ∗ (named_lfts M -∗
      (* get the desired enum type *)
      li_tactic (interpret_rust_type_goal M rsty) (λ '(existT rto tyo),
        ∃ (e : enum rto), ⌜tyo = enum_t e⌝ ∗ ⌜e.(enum_els) = els⌝ ∗
        ∃ rti' tyi', ⌜e.(enum_variant_ty) variant = Some (existT rti' tyi')⌝ ∗
        (* TODO also need syntypes to be compatible *)
        ∃ ri' : rti', owned_subtype π E L2 false ri ri' tyi tyi' (λ L3,
        trigger_tc (ConstructEnum e variant tyi' ri') (λ ro,
          (*⌜construct_enum_sc⌝ ∗*)
          ∀ v', T L3 v' _ (enum_t e) ro))))) -∗
    typed_val_expr π E L (EnumInit els variant rsty e) T.
  Proof.
    iIntros "(%Hly & HT)". destruct Hly as [el Hly].
    iIntros (?) "#CTX #HE HL Hc".
    iApply wp_fupd.
    iApply wp_enum_init; first done.
    iApply ("HT" with "CTX HE HL [Hc]").
    iIntros (L2 v rt ty r) "HL Hv HT".
    iDestruct "HT" as "(%Hlook_st & %M & Hlfts & HT)".
    iPoseProof ("HT" with "Hlfts") as "HT".
    rewrite /interpret_rust_type_goal.
    iDestruct "HT" as "(%rto &  %tyo & %en & -> & <- & HT)".
    iDestruct "HT" as "(%rti' & %tyi' & %Hlook & %ri' & HT)".
    iMod ("HT" with "[] [] CTX HE HL") as "(%L3 & HP & HL & HT)"; [done.. |].
    iDestruct "HP" as "(%Hly' & _ & Hincl)".
    iPoseProof (ty_has_layout with "Hv") as "(%ly & %Hst & %Hlyv)".
    iPoseProof ("Hincl" with "Hv") as "Hv".
    rewrite /trigger_tc. iDestruct "HT" as "(%ro & %Hc & HT)".
    iApply ("Hc" with "HL [Hv] HT").
    iEval (rewrite /ty_own_val/=).
    destruct Hc as [[Hproj Htag]].
    iExists _, _, _, _.
    iR. iSplitR. { iPureIntro. apply use_enum_layout_alg_Some_inv. apply Hly. }
    iEval (rewrite /ty_own_val/=).
    iExists el. iSplitR. { iPureIntro. apply use_enum_layout_alg_inv'. done. }
    iPoseProof (ty_has_layout with "Hv") as "(%ly2 & %Hst2 & %Hlyv2)".
    iR.
    iSplitR. { iPureIntro. apply mjoin_pad_struct_layout; first last.
      { intros. rewrite replicate_length. done. }
      apply use_enum_layout_alg_inv in Hly as (ul & variant_lys & Hul & Hsl & Hf).
      apply struct_layout_alg_has_fields in Hsl. rewrite -Hsl.
      econstructor.
      { simpl.
        (* TODO should make that property hold in els. *)
        admit. }
      econstructor; last done.
      rewrite Hlook_st /use_layout_alg'/= Hst/=.
      rewrite /use_union_layout_alg'.
      erewrite use_union_layout_alg_Some; [ | done | done].
      simpl.
      rewrite /has_layout_val app_length replicate_length.
      rewrite /has_layout_val in Hlyv. rewrite Hlyv.
      enough (ly_size ly ≤ ly_size ul) by lia.
      apply union_layout_alg_has_variants in Hul as ->.
      apply elem_of_list_to_map_2 in Hlook_st.
      apply elem_of_list_lookup_1 in Hlook_st as (i & Hlooki).
      eapply Forall2_lookup_l in Hf; last done.
      destruct Hf as ([name ly'] & Hul & -> & Hst').
      assert (ly' = ly) as -> by by eapply syn_type_has_layout_inj.
      rewrite {2}/ly_size /ul_layout/=.
      apply max_list_elem_of_le. rewrite elem_of_list_fmap.
      eexists. split; first done. apply elem_of_list_fmap.
      exists (name, ly). split; first done.
      by eapply elem_of_list_lookup_2.
    }
    rewrite reshape_join.
    2: { admit. }
    (* TODO use big_sepL2_pad_struct *)
  Admitted.
   *)

End rules.


(* In a module, because having it in the top-level path will break the Ltac2 for looking up definitions when we actually verify stuff using Option. *)
Module enum_test.
  (*
  Section test.
  Context `{!typeGS Σ}.
  (* Example enum spec: option *)
  Section std_option_Option_els.
    Definition std_option_Option_None_sls  : struct_layout_spec := mk_sls "std_option_Option_None" [].

    Definition std_option_Option_Some_sls T_st : struct_layout_spec := mk_sls "std_option_Option_Some" [
      ("0", T_st)].

    Program Definition std_option_Option_els (T_st : syn_type): enum_layout_spec := mk_els "std_option_Option" ISize [
      ("None", std_option_Option_None_sls  : syn_type);
      ("Some", std_option_Option_Some_sls T_st : syn_type)] [("None", 0); ("Some", 1)] _.
    Next Obligation. done. Qed.
  Global Typeclasses Opaque std_option_Option_els.
  End std_option_Option_els.
  (* maybe we should represent this with a gmap for easy lookup? *)

  Section std_option_Option_ty.
    Context {T_rt : Type}.
    Context (T_ty : type (T_rt)).

    Definition std_option_Option_None_ty : type (plist place_rfn []) := struct_t std_option_Option_None_sls +[].
    Definition std_option_Option_None_rt : Type := rt_of std_option_Option_None_ty.
    Global Typeclasses Transparent std_option_Option_None_ty.

    Definition std_option_Option_Some_ty : type (plist place_rfn [T_rt : Type]) := struct_t (std_option_Option_Some_sls (ty_syn_type T_ty)) +[
      T_ty].
    Definition std_option_Option_Some_rt : Type := rt_of std_option_Option_Some_ty.
    Global Typeclasses Transparent std_option_Option_Some_ty.

    Program Definition std_option_Option_enum : enum _ := mk_enum
      ((std_option_Option_els (ty_syn_type T_ty)))
      (λ rfn, match rfn with | None => "None" | Some x => "Some" end)
      (λ rfn, match rfn with | None => existT _ (std_option_Option_None_ty, -[])| Some x => existT _ (std_option_Option_Some_ty, -[x])end)
      (λ variant, if (decide (variant = "None")) then Some $ existT _ std_option_Option_None_ty else if decide (variant = "Some") then Some $ existT _ std_option_Option_Some_ty else None)
      (ty_lfts T_ty)
      (ty_wf_E T_ty)
      _ _
    .
    Next Obligation.
      intros []; simpl; set_solver.
    Qed.
    Next Obligation.
      intros []; simpl; set_solver.
    Qed.

    Global Program Instance construct_enum_Some x : ConstructEnum (std_option_Option_enum) "Some" (std_option_Option_Some_ty) -[x] (Some (x)) :=
      construct_enum _ _ .
    Next Obligation. done. Qed.
    Global Program Instance construct_enum_None : ConstructEnum (std_option_Option_enum) "None" (std_option_Option_None_ty) -[] None :=
      construct_enum _ _.
    Next Obligation. done. Qed.

    Definition std_option_Option_ty : type _ := enum_t std_option_Option_enum.
    Global Typeclasses Transparent std_option_Option_ty.
  End std_option_Option_ty.
  End test.
  *)
End enum_test.


  (* Consideration (long term): how can we make this more realistic?

     Main things we don't model:
     - variant can be stored in a niche
     - we don't know anything about the layout: in particular, assuming that the data is at offset zero, that there is an explicit variant field, etc. does not really match

     Steps for making it better:
     - syn_types should expose which of their bytes are padding bytes.
     - layout algo can determine some arbitrary total size for the enum, and some arbitrary offsets for each of the variants
     - also an arbitrary offset for the variant tag, as long as these bytes are seen as padding by all variants
     - challenge: getting a pointsto for the variant, because it may overlap with padding bytes of an variant.
       -> the type storing the active variant should expose the current variant.
          types need to satisfy a law giving us pointstos for their padding bytes (temporarily), and the ownership predicate needs to be oblivious to that/ writing the type must not change the padding bytes.
          -> the latter part seems strange, it is not really compatible with our current opsem, since uninit bytes are just garbled up.
          -> point: they are not really uninit bytes, but should logically belong to some type (probably the one offering the padding), which is why they should not be treated as uninit by the opsem?
            TODO look at what rustc does to make this work with LLVM
   *)


  (**
      Plan for ltypes:
       - raw_enum_ltype (e : enum rt) (lt : ltype ???)  : ltype rt
          + this is essentially unfolded, with a decoupled refinement
          + This may just be a wrapper for unwrapped_ltype??? i.e. we have already opened the invariant. TODO.
          + problem: if we do this naively, changing the variant will amount to a strong update.
          => depending on whether we do a variant-changing access or not, this should amount to either unwrapped_ltype or opened_ltype.
            TODO: think more about the design.

       - unwrapped_ltype (lt1 : ltype rt) (lt2 : ltype rt) : ltype rt
          + just captures what is necessary to go back from the (core of the) currently owned lt2 to the core lt1.
            - we should just require going back from the core of lt2, since we may borrow somewhere in lt2, and we can't directly shift back the blocked thing.
            - maybe use unblockable here?
          + Q: can this also be used for the existential/invariant stuff?
            difference: there we may not at all times have a vs to go back from the core, since we may temporarily break the invariant it.
              if we are below a mutref there, we really need to open the mutref, and that should relax the typed_place_cond requirement below.
          => I don't think these are the same. They have quite different features in terms of what requirements they pose/ what they ensure in turn.
       - pad_ltype (st : syn_type) (lt : ltype rt) : ltype rt
          + this wraps the inner ltype and adds trailing padding.
       - opened_ltype (lt1 : ltype rt1) (lt2 : ltype rt2) (P : iProp Σ) (Q : iProp Σ) : ltype rt2
          + used for existentials/invariants. this is different from unwrapped_ltype, as noted above.
          + can only be directly at the top-level (below one level of references), not deeper.
          + P are the additional resources needed to go back to lt1? and Q is what we obtain in addition if we do so.
            - P may also need to depend on the current refinement.
            - Q may also depend on the refinement and some quantifiers in P?
            e.g. P r := ∃ n, r = n > 0 ∗ na_tok ∅
                 Q r := na_tok my_inv
              (for na_tok this uses that they directly compose with disjoint union, so these minimal choices work wlog)
          +



     General theme here: we need to provide overly specific ltypes because the unfolding equations will otherwise loose information.
      - issue is when operating below mutable references: there loosing some information really is problematic, because we can't just conjure that up again when the lftlogic needs to shift back => in general, we can't go weaker than ltype_eq, which is what we use currently.
      - can we provide a general "wrapper ltype" that collects some of the lost information so we can shift back?
        e.g. wrap lt1 lt2 actually contains lt2 below + information to shift lt2 back to lt1. then we could safely do things like
          ◁ (active_union ...) ⇝ unwrap (◁ active_union ..) (◁ pad_type ...) ⇝ unwrap (◁ active_union ..) (pad_ltype ..)
          i.e. wrap effectively contains a viewshift? and the core is just the lt1?
          => this has quite some similarity with what is needed for the existentials + invariants.
            the funny thing is that it again makes a second field explicit, which is what we originally did the whole core business with closed ltypes for (when blocking).
            now we need it again for a different use case, because here we can't directly derive the core lt1 from lt2 (that's the whole point).
          lt1 and lt2 need the same refinement type, because we might operate below mutrefs.



   *)

  (*
     Procedure for unfolding/accessing:
      - unfold enum to struct (this changes refinement already)
        I won't get around that, either way. For mut and owned, go to OpenedLtype; for shared go to shadowed.
     - for the tag, can now freely access and use it. we do not immediately need to re-establish anything when writing.
     -

     Q's for the data:
     - what is the refinement after unfolding?
       + option 1: same refinement as the enum -> VariantLtype
       + option 2: just the data, i.e. refinement of the particular variant
     -

     VariantLtype (e : enum rt) (lt : ltype rt'): ltype rt
      - requires that rt' = projT1 (enum_ty r) at refinement r.
      - otherwise, does not require anything about the relation of lt to enum_ty r
     => this seems unnatural.

     VariantLtype (e : enum rt) (variant: string) (lt : ltype (rfn_of_variant e variant)): ltype rt
     - would just unfold into active union on variant changes, i.e. similar to refinedc if we
     => the delta to ActiveUnion is just that we carry the enum with us.

     ActiveUnionLtype {rt} (uls : union_layout_spec) (variant : string) (lt : ltype rt) : ltype rt
      - just pads lt according to the variant in uls.
      - changing variant is a strong update here, but that is fine since we are encapsulated by the outer enum_t which supports that.
     => Q: this doesn't retain information on the enum, so how do we get back? Is there enough stuff to guide the typing rules?
       + concretely: we will stratify it, and stratification won't do much on the active enum itself.
          then we get [variant, data] @ struct [tag , active_union ]
          we have nothing here to tell us that this should be folded into a enum. additional difficulty: there may be blocked things below.
          one thing we can do: stratification instances should trigger a subsume.
            i.e. compute core of the current thing (needs to correctly descend below active_union!)
                 then require

      -


    Does anything get easier if we don't allow variant changes?
     - VariantLtype could have a fixed variant parameter and require that the refinement-specified variatn matches it.
       That way, we would have a natural way of specifying the type of the ltype.
       -> this is also not totally incompatible with variant changes.

    ======

     Other approach: all of the considerations above allow quite a lot of freedom. But why do we need that?
      - one idea: instead of having to access the data + variant separately, have a dedicated op that fuses the two and skips the union entirely.
        i.e. have a data{els, variant} operation that fuses the struct offset + union offset.

     UnfoldedEnumLtype (e : enum rt) (tag_variant data_variant : string) {rt'} (lt : ltype rt') : ltype rt'
      - owns the whole enum struct.
      - tag_variant controls the tag, but it is otherwise completely decoupled.
        changes to either type of data or change to tag will constitute strong updates.
      - data_variant controls the offset/padding for lt within the union
      - ◁ enum unfolds into OpenedLtype (FixedEnumLtype ...) ..  and
        we can fold back if the rt' matches the type specified by tag_variant and the variants match.
      - if we access data from it with a particular variant that does not match the actual one, we flush to uninit for that.
    Pro:
     - this interface seems pretty agnostic to the concrete representation. It doesn't really leak to the outside that there's a union.
     - gives a lot of syntactic guidance. It's very clear how stratification can deal with this.
    Con:
     - it seems like a big ugly blob.

    IF I can require that on a variant change, the write of the variatn struct will happen in one step, I can also do:
      UnfoldedEnumLtype (e : enum rt) (tag_variant data_variant : string) (lt : ltype (rt_of data_variant)) : ltype rt
    Reasoning: To the recursive access, I give the uninit (with a refinement which would not fit the pattern), but in the continuation I require that the refinement type matches the updated variant type.
    TODO: is that requirement sensible? look at MIR translation

    Something similar for Shared?
     ShrUnfoldedEnumLtype (e : enum rt) (variant : string) (lt : ltype (rt_of variant)) : ltype rt
     => for the latter variant above, we could also just merge this - they are not so different. We could just require the two variants to be the same for the shared case.


     I think I like this approach more than the refinedc-style union approach. We should morally not rely too much on unions, and this restricted set of operations seems quite sensible compared to the very flexible appraoch of refiendc, which allows much stuff whihc we don't need to care about in Rust.

   *)


  (** essentially just a wrapper around int *)
  (* TODO can we erase the "extra data" from the refinement?
     currently, this would be refined by [Some ...], and the [...] doesn't really matter.

     Alternatives: refine by variant number, or variant tag.
     -> variant tag seems sensible.
  *)
  (*
  Program Definition tag_t {rt} (e : enum rt) : type string := {|
    st_own π r v := (v ◁ᵥ{π} e.(enum_tag_int) r @ int e.(enum_els).(els_tag_it))%I;
    st_syn_type := IntSynType e.(enum_els).(els_tag_it);
    st_has_op_type ot mt := is_int_ot ot e.(enum_els).(els_tag_it);
  |}.
  Next Obligation.
    iIntros (rt e π r v) "Hown". iApply (ty_has_layout with "Hown").
  Qed.
  Next Obligation.
    iIntros (rt e ot mt Hot). simpl.
    rewrite (is_int_ot_layout _ _ Hot).
    apply syn_type_has_layout_int; first done.
    apply els_tag_it_size.
  Qed.
  Next Obligation.
    iIntros (rt e ot mt st π r v Hot) "Hown".
    by iApply (ty_memcast_compat with "Hown").
  Qed.
   *)
  (* reading the discriminant should give us something typed at [tag_t en].
     - we should then be able to switch on it, and know that we cannot fall into the default case, if we match exhaustively.
      => The tag type should carry a bound on the range.
      => refinement: either the full refinement of the enum, or the name of the tag. TODO
     - after switching (knowing that the refinement has a particular value/particular variant), we should be able to focus the data field to one particular variant.
        => we have a enum_ltype that describes the special link between the variant field and which variant is active in the data field. we need special access operations for it.
        => focussing one variant should be part of the place access when accessing the data field. after that, it should behave the same as an ordinary struct field.
     - what happens with the enum ltype when the variant update and the data update happen separately?
        => we temporarily break its invariant. so, potentially the unfolded enum type should be more relaxed/ have less invariants?
  *)

  (*
  Lemma has_layout_val_ly_offset_inv v ly o :
    (drop o v) `has_layout_val` (ly_offset ly o) →
    v `has_layout_val` ly ∨ (ly_size ly ≤ o ∧ length v ≤ o).
  Proof.
    rewrite /has_layout_val. rewrite drop_length.
    destruct ly as [sz al].
    rewrite /ly_offset /ly_size /=.
    intros ?. destruct (decide (length v = sz)); first by left. right. lia.
  Qed.
   *)

  (** [active_union_t ty uls] basically wraps [ty] to lay it out in [uls], asserting that a union currently is in variant [variant].
      This is not capturing the allowed union layouting in Rust in full generality (Rust may freely choose the offsets of the variants),
      but we are anyways already not handling tags correctly, so who cares... *)
  (* TODO rather factor out into a padded type, as in RefinedC? *)
  (*
  Program Definition enum_variant_t {rt} (e : enum rt) (variant : string) : type rt := {|
    ty_own_val π r v :=
      (∃ ul ly, ⌜use_union_layout_alg uls = Some ul⌝ ∗
        ⌜layout_of_union_member variant ul = Some ly⌝ ∗
        take ly.(ly_size) v ◁ᵥ{π} r @ ty ∗
        drop ly.(ly_size) v ◁ᵥ{π} () @ uninit (UntypedSynType (ly_offset (ul : layout) ly.(ly_size))))%I;
    ty_syn_type := uls;
    ty_has_op_type ot mt :=
      (* we should not directly read from/write to this *)
      (* TODO: really? *)
      False;
    ty_shr κ π r l :=
      (∃ ul ly, ⌜use_union_layout_alg uls = Some ul⌝ ∗
        ⌜layout_of_union_member variant ul = Some ly⌝ ∗
        ⌜l `has_layout_loc` ul⌝ ∗
        l ◁ₗ{π, κ} r @ ty ∗
        (l +ₗly.(ly_size)) ◁ₗ{π, κ} () @ uninit (UntypedSynType (ly_offset (ul : layout) ly.(ly_size))))%I;
    ty_ghost_drop r := ty.(ty_ghost_drop) r;
    ty_lfts := [];
    ty_wf_E := [];
    ty_sidecond := True;
  |}.
  Next Obligation.
    iIntros (rt ty var uls π r v) "(%ul & %ly & % & % & Hv & Hvr)".
    iExists ul.
    iSplitR. { iPureIntro. by apply use_union_layout_alg_Some_inv. }
    iPoseProof (ty_has_layout with "Hv") as "(%ly' & %Halg0 & %Hv0)".
    rewrite uninit_own_spec. iDestruct "Hvr" as "(% & %Halg1 & %Hv1)".
    iPureIntro. apply syn_type_has_layout_untyped_inv in Halg1 as (-> & _ & _).
  Admitted.
  Next Obligation.
    done.
  Qed.
  Next Obligation.
    eauto.
  Qed.
  Next Obligation.
    iIntros (????????) "(%ul & %ly & % & % & % & _)". iExists ul.
    iSplitR; first done. iPureIntro. by eapply use_union_layout_alg_Some_inv.
  Qed.
  Next Obligation.
    iIntros (rt ty variant uls E κ l ly π r q ?) "CTX Htok %Halg %Hly #Hlb Hb".
  Admitted.
  Next Obligation.
    iIntros (rt ty variant uls κ κ' π r l) "#Hincl Hb".
  Admitted.
  Next Obligation.
    iIntros (?????????) "Hb".
    iDestruct "Hb" as "(%ul & %ly & %Halg & %Hly & Hv & _)".
    iPoseProof (ty_own_ghost_drop with "Hv") as "Ha"; last iApply (logical_step_wand with "Ha"); eauto.
  Qed.
  Next Obligation.
    done.
  Qed.
   *)
  (* basically, all borrowing of components of an enum should happne at the level of the struct for a variants' components;
      therefore, we don't need to do any of the handling here.
     can we directly use place lemmas for structs? -- we still need an extra ltype that keeps trakc of that unfolding, so we can go back.
  *)
