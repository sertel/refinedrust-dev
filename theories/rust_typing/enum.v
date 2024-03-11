From refinedrust Require Export type ltypes.
From refinedrust Require Import uninit int int_rules.
From refinedrust Require Import products programs.
Set Default Proof Using "Type".

(** * Enums *)
(** Enum support is currently WIP as some of the typing rules are incomplete *)

Section union.
  Context `{!typeGS Σ}.

  (* TODO move *)
  Lemma ly_size_layout_of_union_member ul ly mem :
    layout_of_union_member mem ul = Some ly →
    ly_size ly ≤ ly_size ul.
  Proof.
    rewrite {2}/ly_size/ul_layout.
    rewrite /layout_of_union_member.
    intros (i & Hidx & Ha)%bind_Some.
    eapply max_list_elem_of_le.
    apply elem_of_list_fmap.
    exists ly. split; first done.
    rewrite -list_lookup_fmap in Ha.
    by eapply elem_of_list_lookup_2.
  Qed.

  Lemma max_list_pow (n : nat) l :
    1 ≤ n →
    n ^ (max_list l) = max 1 (max_list ((λ x, n^x) <$> l)).
  Proof.
    intros ?.
    induction l as [ | x l IH]; simpl; first done.
    rewrite Nat_pow_max; last done.
    rewrite IH.
    rewrite Nat.max_assoc. rewrite [_ `max` 1]Nat.max_comm.
    rewrite -Nat.max_assoc. done.
  Qed.

  Lemma ly_align_log_union_layout (ul : union_layout) :
    ly_align_log ul = max_list (ly_align_log <$> (ul_members ul).*2).
  Proof. rewrite /ly_align_log//. Qed.
  Lemma ly_align_union_layout (ul : union_layout) :
    ly_align ul = 1 `max` max_list (ly_align <$> (ul_members ul).*2).
  Proof.
    rewrite /ly_align. rewrite ly_align_log_union_layout.
    rewrite max_list_pow; last lia.
    f_equiv. f_equiv.
    rewrite -list_fmap_compose list_fmap_compose//.
  Qed.
  Lemma aligned_to_max_list x l al :
    x ∈ al →
    l `aligned_to` 2^ max_list al →
    l `aligned_to` 2^ x.
  Proof.
    induction al as [ | y al IH] in x |-*.
    { intros ?%elem_of_nil. done. }
    intros [ -> | Hel ]%elem_of_cons.
    - simpl. intros ?%aligned_to_2_max_l; done.
    - intros ?%aligned_to_2_max_r. by eapply IH.
  Qed.

  Lemma has_layout_loc_layout_of_union_member ul ly mem l :
    layout_of_union_member mem ul = Some ly →
    l `has_layout_loc` ul →
    l `has_layout_loc` ly.
  Proof.
    rewrite /layout_of_union_member.
    intros (i & Hidx & Ha)%bind_Some.
    rewrite /has_layout_loc /ly_align.
    rewrite ly_align_log_union_layout.
    apply aligned_to_max_list.
    apply elem_of_list_fmap.
    exists ly. split; first done.
    rewrite -list_lookup_fmap in Ha.
    by eapply elem_of_list_lookup_2.
  Qed.

  Definition active_union_rest_ly (ul : union_layout) (ly : layout) := Layout (ly_size ul - ly.(ly_size)) 0.
  Lemma has_layout_loc_active_union_rest_ly ul ly l :
    l `has_layout_loc` (active_union_rest_ly ul ly).
  Proof.
    rewrite /has_layout_loc /aligned_to. destruct caesium_config.enforce_alignment; last done.
    rewrite /active_union_rest_ly /ly_align /=.
    apply Z.divide_1_l.
  Qed.
  Lemma ly_size_active_union_rest_ly ul ly :
    ly_size (active_union_rest_ly ul ly) = ly_size ul - ly.(ly_size).
  Proof. done. Qed.

  (** [active_union_t ty uls] basically wraps [ty] to lay it out in [uls], asserting that a union currently is in variant [variant].
      This is not capturing the allowed union layouting in Rust in full generality (Rust may freely choose the offsets of the variants),
      but we are anyways already not handling tags correctly, so who cares... *)
  (* TODO rather factor out into a padded type, as in RefinedC? *)
  Program Definition active_union_t {rt} (ty : type rt) (variant : string) (uls : union_layout_spec) : type rt := {|
    ty_rt_inhabited := ty.(ty_rt_inhabited);
    ty_own_val π r v :=
      (∃ ul ly, ⌜use_union_layout_alg uls = Some ul⌝ ∗
        ⌜layout_of_union_member variant ul = Some ly⌝ ∗
        ⌜syn_type_has_layout (ty_syn_type ty) ly⌝ ∗
        take ly.(ly_size) v ◁ᵥ{π} r @ ty ∗
        drop ly.(ly_size) v ◁ᵥ{π} () @ uninit (UntypedSynType $ active_union_rest_ly ul ly))%I;
    ty_syn_type := uls;
    _ty_has_op_type ot mt :=
      (* only untyped reads are allowed *)
      (* TODO maybe make this more precise. Typed ops would be allowed for the first segment *)
      ∃ ul, use_union_layout_alg uls = Some ul ∧ ot = UntypedOp ul;
    ty_shr κ π r l :=
      (∃ ul ly, ⌜use_union_layout_alg uls = Some ul⌝ ∗
        ⌜layout_of_union_member variant ul = Some ly⌝ ∗
        ⌜l `has_layout_loc` ul⌝ ∗
        l ◁ₗ{π, κ} r @ ty ∗
        (l +ₗ ly.(ly_size)) ◁ₗ{π, κ} () @ uninit (UntypedSynType $ active_union_rest_ly ul ly))%I;
    ty_ghost_drop r := ty.(ty_ghost_drop) r;
    ty_lfts := ty_lfts ty;
    ty_wf_E := ty_wf_E ty;
    ty_sidecond := True;
  |}.
  Next Obligation.
    iIntros (rt ty var uls π r v) "(%ul & %ly & %Halg & %Hly & %Hst & Hv & Hvr)".
    iExists ul.
    iSplitR. { iPureIntro. by apply use_union_layout_alg_Some_inv. }
    iPoseProof (ty_own_val_has_layout with "Hv") as "%Hv0"; first done.
    rewrite uninit_own_spec. iDestruct "Hvr" as "(% & %Halg1 & %Hv1)".
    iPureIntro. apply syn_type_has_layout_untyped_inv in Halg1 as (-> & _ & _).
    move: Hv0 Hv1. apply ly_size_layout_of_union_member in Hly.
    rewrite /has_layout_val/active_union_rest_ly.
    rewrite take_length drop_length.
    rewrite {4}/ly_size.
    lia.
  Qed.
  Next Obligation.
    intros ??? uls ot mt (ul & Hul & ->).
    simpl. by eapply use_union_layout_alg_Some_inv.
  Qed.
  Next Obligation.
    eauto.
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
    set (bor_contents :=
      (∃ (ul : union_layout) ly',
        ⌜use_union_layout_alg uls = Some ul⌝ ∗
        ⌜layout_of_union_member variant ul = Some ly'⌝ ∗
        ⌜syn_type_has_layout (ty_syn_type ty) ly'⌝ ∗
        ∃ v : val, l ↦ v ∗ take (ly_size ly') v ◁ᵥ{ π} r @ ty ∗ drop (ly_size ly') v ◁ᵥ{ π} .@ uninit (UntypedSynType (active_union_rest_ly ul ly')))%I).
    iPoseProof (bor_iff _ _ bor_contents with "[] Hb") as "Hb".
    { iNext. iModIntro. rewrite /bor_contents. iSplit.
      - iIntros "(%v & Hl & %ul & %ly' & ? & ? & ? & ? & ?)"; eauto with iFrame.
      - iIntros "(%ul & %ly' & ? & ? & ? & %v & ? & ? & ?)"; eauto with iFrame. }
    rewrite /bor_contents.
    iDestruct "CTX" as "#(LFT & TIME & LLCTX)".
    rewrite -lft_tok_sep. iDestruct "Htok" as "(Htok & Htok1)".
    iApply fupd_logical_step.
    iMod (bor_exists with "LFT Hb") as "(%ul & Hb)"; first done.
    iMod (bor_exists with "LFT Hb") as "(%ly' & Hb)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Hul & Hb)"; first done.
    iMod (bor_persistent with "LFT Hul Htok") as "(>%Hul & Htok)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Hly & Hb)"; first done.
    iMod (bor_persistent with "LFT Hly Htok") as "(>%Hul_ly & Htok)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Hst & Hb)"; first done.
    iMod (bor_persistent with "LFT Hst Htok") as "(>%Hst & Htok)"; first done.

    specialize (ly_size_layout_of_union_member _ _ _ Hul_ly) as ?.
    apply use_layout_alg_union_Some_inv in Halg as (ul' & Halg & ->).
    assert (ul' = ul) as -> by naive_solver.

    (* now split the values in the borrow *)
    iPoseProof (bor_iff _ _ ((∃ v1 : val, l ↦ v1 ∗ v1 ◁ᵥ{ π} r @ ty) ∗ (∃ v2 : val, (l +ₗ ly_size ly') ↦ v2 ∗ v2 ◁ᵥ{ π} .@ uninit (UntypedSynType (active_union_rest_ly ul ly')))) with "[] Hb") as "Hb".
    { iNext. iModIntro. iSplit.
      - iIntros "(%v & Hl & Ha & Hb)".
        rewrite -{1}(take_drop (ly_size ly') v).
        rewrite heap_mapsto_app. iDestruct "Hl" as "(Hl1 & Hl2)".
        iPoseProof (ty_own_val_has_layout with "Ha") as "%Hlyv"; first done.
        rewrite /has_layout_val take_length in Hlyv.
        iSplitL "Hl1 Ha". { iExists _. iFrame. }
        iPoseProof (ty_has_layout with "Hb") as "(%ly2 & %Hst2 & %Hlyv2)".
        apply syn_type_has_layout_untyped_inv in Hst2 as (-> & ? & ? & ?).
        move: Hlyv2. rewrite /has_layout_val drop_length /active_union_rest_ly {2}/ly_size/= => Hlyv2.
        rewrite take_length. rewrite Nat.min_l; last lia.
        eauto with iFrame.
      - iIntros "((%v1 & Hl1 & Hv1) & (%v2 & Hl2 & Hv2))".
        iExists (v1 ++ v2).
        iPoseProof (ty_own_val_has_layout with "Hv1") as "%Hlyv"; first done.
        iPoseProof (ty_has_layout with "Hv2") as "(%ly2 & %Hst2 & %Hlyv2)".
        apply syn_type_has_layout_untyped_inv in Hst2 as (-> & ? & ? & ?).
        move: Hlyv2. rewrite /has_layout_val /active_union_rest_ly {1}/ly_size/= => Hlyv2.
        rewrite /has_layout_val in Hlyv.
        rewrite heap_mapsto_app. rewrite Hlyv. iFrame.
        iSplitL "Hv1". { rewrite take_app'; first done. lia. }
        rewrite drop_app'; last lia. done. }
    iMod (bor_sep with "LFT Hb") as "(Hb1 & Hb2)"; first done.

    (* now share both parts *)
    iDestruct "Htok" as "(Htok11 & Htok12)".
    iDestruct "Htok1" as "(Htok21 & Htok22)".

    iPoseProof (ty_share _ E with "[$LFT $TIME $LLCTX] [Htok11 Htok21] [] [] [] Hb1") as "Hb1"; first done.
    { rewrite -lft_tok_sep. iFrame. }
    { done. }
    { iPureIntro. by eapply has_layout_loc_layout_of_union_member. }
    { iApply (loc_in_bounds_shorten_suf with "Hlb"). done. }

    iPoseProof (ty_share _ E with "[$LFT $TIME $LLCTX] [Htok12] [] [] [] Hb2") as "Hb2"; first done.
    { simpl. rewrite right_id. iFrame. }
    { simpl. iPureIntro. apply syn_type_has_layout_untyped; first done.
      - rewrite /active_union_rest_ly/layout_wf/ly_align/=. apply Z.divide_1_l.
      - rewrite /active_union_rest_ly {1}/ly_size. apply use_union_layout_alg_size in Hul. lia.
      - rewrite /ly_align_in_bounds/ly_align/active_union_rest_ly/ly_align_log/=.
        unfold_common_caesium_defs. simpl. nia.
    }
    { iPureIntro. apply has_layout_loc_active_union_rest_ly. }
    { iApply (loc_in_bounds_offset with "Hlb").
      - done.
      - simpl. lia.
      - simpl. rewrite ly_size_active_union_rest_ly. lia. }

    iApply (logical_step_compose with "Hb1").
    iApply (logical_step_compose with "Hb2").
    iApply logical_step_intro.
    iModIntro.
    iIntros "(Hun & Htok1) (Hty & Htok2)".
    simpl. rewrite right_id.
    rewrite -lft_tok_sep.
    iDestruct "Htok2" as "(? & ?)". iFrame.
    iExists ul, ly'. iR. iR. iR. done.
  Qed.
  Next Obligation.
    iIntros (rt ty variant uls κ κ' π r l) "#Hincl Hb".
    iDestruct "Hb" as "(%ul & %ly & ? & ? & ? & Ha & Hb)".
    iExists ul, ly. iFrame.
    iSplitL "Ha". { iApply ty_shr_mono; done. }
    iApply ty_shr_mono; done.
  Qed.
  Next Obligation.
    iIntros (?????????) "Hb".
    iDestruct "Hb" as "(%ul & %ly & %Halg & %Hly & ? & Hv & _)".
    iPoseProof (ty_own_ghost_drop with "Hv") as "Ha"; last iApply (logical_step_wand with "Ha"); eauto.
  Qed.
  Next Obligation.
    intros rt ty variant uls ot mt st π r v (ul & Hul & ->).
    iIntros "Hv".
    destruct mt; first done; last done.
    by rewrite mem_cast_UntypedOp.
  Qed.
End union.
Global Typeclasses Opaque active_union_t.

Section type_incl.
  Context `{!typeGS Σ}.

  Lemma active_union_type_incl {rt} (ty1 ty2 : type rt) r1 r2 variant1 variant2 uls :
    variant1 = variant2 →
    type_incl r1 r2 ty1 ty2 -∗
    type_incl r1 r2 (active_union_t ty1 variant1 uls) (active_union_t ty2 variant2 uls).
  Proof.
    iIntros (->) "(%Hst & #Hsc & #Hincl & #Hincl2)".
    iSplitR. { simpl. done. }
    iSplitR. { simpl. eauto. }
    iSplitR; iModIntro.
    - iIntros (π v) "Hv". rewrite {3 4}/ty_own_val/=.
      iDestruct "Hv" as "(%ul & %ly & %Huls & %Hly & % & Hv1 & Hv2)".
      rewrite -Hst. iExists ul, ly. iR. iR. iR. iSplitL "Hv1".
      + iApply "Hincl". done.
      + done.
    - iIntros (κ π l) "Hl". rewrite {3 4}/ty_shr/=.
      iDestruct "Hl" as "(%ul & %ly & %Huls & %Hly & %Hl & Hl1 & Hl2)".
      iExists ul, ly. iR. iR. iR. iSplitL "Hl1".
      + iApply "Hincl2". done.
      + done.
  Qed.
End type_incl.


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
        ly = el
        (*f∧ oldr (λ '(v, st) P,*)
            (*∃ rty ly',*)
            (*en.(enum_tag_ty) v = Some rty ∧*)
            (*syn_type_has_layout st ly' ∧*)
            (*ty_has_op_type (projT2 rty) (UntypedOp ly') mt*)
          (*) True (en.(enum_els).(els_variants))*)
    | _ => False
    end.
  Global Typeclasses Opaque is_enum_ot.


  (* NOTE: in principle, we might want to formulate this with [ex_plain_t] as an existential abstraction over a struct.
     However, here the inner type also depends on the outer refinement, which is not supported by [ex_plain_t] right now. *)
  Program Definition enum_t {rt} (e : enum rt) : type rt :=
    {|
    ty_rt_inhabited := e.(enum_rt_inhabited);
    ty_own_val π r v :=
      (∃ rt' ty' r' el,
      ⌜e.(enum_ty) r = existT rt' (ty', r')⌝ ∗
      ⌜use_enum_layout_alg e.(enum_els) = Some el⌝ ∗
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
    _ty_has_op_type ot mt :=
      is_enum_ot e ot mt;
    ty_sidecond := True%I;
    ty_ghost_drop π r := True%I; (* TODO *)
    ty_lfts := e.(enum_lfts);
    ty_wf_E := e.(enum_wf_E);
  |}.
  Next Obligation.
    iIntros (rt e π r v).
    iIntros "(%rt' & %ty' & %r' & %el & %Heq & %Halg & Hv)".
    (*specialize (syn_type_has_layout_els_sls _ _ Halg) as (sl & Halg' & ->).*)
    iPoseProof (ty_own_val_has_layout with "Hv") as "%Hlyv".
    { simpl. by apply use_struct_layout_alg_Some_inv. }
    iExists el. iPureIntro; split; last done.
    by eapply use_enum_layout_alg_Some_inv.
  Qed.
  Next Obligation.
    rewrite /is_enum_ot. simpl.
    intros rt en ot mt Hot.
    destruct ot as [ | | | | ly| ]; try done.
    destruct Hot as (el & Halg & ->).
    simpl. by apply use_enum_layout_alg_Some_inv.
  Qed.
  Next Obligation.
    eauto.
  Qed.
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
    iAssert (&{κ} ((∃ (rt' : Type) (ty' : type rt') (r' : rt') (el : struct_layout), ⌜enum_ty e r = existT rt' (ty', r')⌝ ∗ ⌜use_enum_layout_alg (enum_els e) = Some el⌝ ∗ ∃ v : val, l ↦ v ∗ v ◁ᵥ{ π} -[# (enum_lookup_tag e r); # r'] @ struct_t (sls_of_els (enum_els e)) +[int (els_tag_it (enum_els e)); active_union_t ty' (enum_tag e r) (uls_of_els (enum_els e))])))%I with "[Hb]" as "Hb".
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
    iIntros (rt en ot mt st π r v Hot) "Hl".
    iDestruct "Hl" as "(%rt' & %ty' & %r' & %ly & %Hen & %Hst & Ha)".
    destruct mt; first done; first last.
    { destruct ot; done. }
    iExists rt', ty', r', ly. iR. iR.

    iApply (ty_memcast_compat _ _ _ MCCopy with "Ha").
    rewrite ty_has_op_type_unfold. simpl. rewrite /is_struct_ot/=. split; first done.
    destruct ot as [ | | | | ly' | ]; try done.
    rewrite ty_has_op_type_unfold.
    rewrite /is_enum_ot in Hot.
    destruct Hot as (el & Hel & ->).
    exists el. split; first done. split; first done.
    split.
    { exists (els_tag_it (enum_els en)). simpl. split_and!.
      - eapply syn_type_has_layout_int; first done.
        rewrite MaxInt_eq.
        apply IntType_to_it_size_bounded.
      - done.
      - rewrite MaxInt_eq. apply IntType_to_it_size_bounded. }
    split; last done.
    apply use_enum_layout_alg_inv in Hel as (ul & variants & Hul & Hel & Hvariants).
    exists ul.
    assert (syn_type_has_layout (uls_of_els (enum_els en)) ul) as Hul'.
    { eapply syn_type_has_layout_union; last done. done. }
    split; first done.
    exists ul. split; last done.
    eapply use_union_layout_alg_Some; done.
  Qed.

  (* TODO non-expansiveness *)
End enum.
Global Typeclasses Opaque enum_t.

Section subtype.
  Context `{!typeGS Σ}.

  (* TODO: should probably have a subtyping condition on enum that lifts this element-wise. *)

  (* homogeneous subtyping.
     We basically only want this for type parameters of an enum.
     If T <: U, then option T <: option U.
     otherwise, don't need anything.
  *)
  Definition enum_incl {rt} (e1 e2 : enum rt) : iProp Σ :=
    ⌜e1.(enum_els) = e2.(enum_els)⌝ ∗
    ⌜e1.(enum_tag) = e2.(enum_tag)⌝ ∗
    (∀ r, ∃ rt' ty1 ty2 r1 r2,
      ⌜e1.(enum_ty) r = existT rt' (ty1, r1)⌝ ∗
      ⌜e2.(enum_ty) r = existT rt' (ty2, r2)⌝ ∗
      type_incl r1 r2 ty1 ty2)
  .
  Global Instance enum_incl_pers {rt} (e1 e2 : enum rt) : Persistent (enum_incl e1 e2).
  Proof. apply _. Qed.

  Lemma enum_own_val_mono {rt} (e1 e2 : enum rt) r :
    enum_incl e1 e2 -∗
    ∀ π v, v ◁ᵥ{π} r @ enum_t e1 -∗ v ◁ᵥ{π} r @ enum_t e2.
  Proof.
    iIntros "(%Hels & %Htag & #Hincl)".
    iIntros (π v) "Hv".
    rewrite /ty_own_val/=.
    iDestruct "Hv" as "(%rt' & %ty' & %r' & %ly & %Hen & %Hst & Hv)".
    iDestruct ("Hincl" $! r) as "(%rt0 & %ty1 & %ty2 & %r1 & %r2 & %Hen1 & %Hen2 & Hincl')".
    rewrite Hen in Hen1.
    injection Hen1. intros _ _ <-. apply existT_inj in Hen1 as [= -> ->].
    iExists rt', ty2, r2. iExists ly.
    iR. rewrite -Hels. iR.
    iApply (struct_t_own_val_mono with "[] Hv").
    rewrite /struct_t_incl_precond. simpl.
    iSplit. { rewrite /enum_lookup_tag Hels Htag. iApply type_incl_refl. }
    iSplit; last done.
    simpl. rewrite Htag. iApply active_union_type_incl; first done. done.
  Qed.
  Lemma enum_shr_mono {rt} (e1 e2 : enum rt) r :
    enum_incl e1 e2 -∗
    ∀ κ π l, l ◁ₗ{π, κ} r @ enum_t e1 -∗ l ◁ₗ{π, κ} r @ enum_t e2.
  Proof.
    iIntros "(%Hels & %Htag & #Hincl)".
    iIntros (κ π l) "Hl".
    rewrite /ty_shr/=.
    iDestruct "Hl" as "(%rt' & %ty' & %r' & %ly & %Hen & %Hst & Hl)".
    iDestruct ("Hincl" $! r) as "(%rt0 & %ty1 & %ty2 & %r1 & %r2 & %Hen1 & %Hen2 & Hincl')".
    rewrite Hen in Hen1.
    injection Hen1. intros _ _ <-. apply existT_inj in Hen1 as [= -> ->].
    iExists rt', ty2, r2. iExists ly.
    iR. rewrite -Hels. iR.
    iApply (struct_t_shr_mono with "[] Hl").
    rewrite /struct_t_incl_precond. simpl.
    iSplit. { rewrite /enum_lookup_tag Hels Htag. iApply type_incl_refl. }
    iSplit; last done.
    simpl. rewrite Htag. iApply active_union_type_incl; first done. done.
  Qed.

  Lemma enum_type_incl {rt} (e1 e2 : enum rt) r :
    enum_incl e1 e2 -∗
    type_incl r r (enum_t e1) (enum_t e2).
  Proof.
    iIntros "#Hincl".
    iPoseProof "Hincl" as "(%Hels & %Htag & #Hincl')".
    iSplitR. { simpl. rewrite Hels //. }
    iSplitR. { iModIntro. simpl. eauto. }
    iSplit; iModIntro.
    - by iApply enum_own_val_mono.
    - by iApply enum_shr_mono.
  Qed.

  (*weak_subtype*)

  Definition full_enum_incl E L {rt} (e1 e2 : enum rt) : Prop :=
    ∀ qL : Qp, llctx_interp_noend L qL -∗ elctx_interp E -∗ enum_incl e1 e2.

  Lemma enum_full_subtype E L {rt} (e1 e2 : enum rt) :
    full_enum_incl E L e1 e2 →
    full_subtype E L (enum_t e1) (enum_t e2).
  Proof.
    intros Hsubt r. iIntros (?) "HL #HE".
    iApply enum_type_incl.
    iApply (Hsubt with "HL HE").
  Qed.
End subtype.

Section unfold.
  Context `{!typeGS Σ}.

  (* NOTE: we can only do this unfolding for PlaceIn -- because the variant we unfold to depends on that.
     I think this should not be a problem.
  *)
  Lemma enum_variant_rt_tag_rt_eq {rt} (en : enum rt) (r : rt) (tag : var_name) :
    tag = enum_tag en r → enum_variant_rt en r = enum_tag_rt en tag.
  Proof.
    intros ->. symmetry. by apply enum_tag_rt_variant_rt_eq.
  Qed.

  (* TODO move *)
  Lemma ty_own_val_active_union_split π {rt} (ty : type rt) r v uls variant :
    v ◁ᵥ{π} r @ active_union_t ty variant uls -∗
    ∃ ul ly v1 v2, ⌜v = v1 ++ v2⌝ ∗
      ⌜union_layout_spec_has_layout uls ul⌝ ∗
      ⌜syn_type_has_layout (ty_syn_type ty) ly⌝ ∗
      v1 ◁ᵥ{π} r @ ty ∗ v2 ◁ᵥ{π} () @ uninit (UntypedSynType (active_union_rest_ly ul ly)).
  Proof.
    iIntros "Hv".
    rewrite {1}/ty_own_val/=.
    iDestruct "Hv" as "(%ul & %ly & %Hul' & %Hly & %Hst' & Hv1 & Hv2)".
    iExists ul, ly.
    iExists (take (ly_size ly) v), (drop (ly_size ly) v).
    rewrite take_drop. iR. iR. iR. iFrame.
  Qed.
  Lemma ty_own_val_active_union_split' π {rt} (ty : type rt) r v uls ul ly variant :
    union_layout_spec_has_layout uls ul →
    syn_type_has_layout (ty_syn_type ty) ly →
    v ◁ᵥ{π} r @ active_union_t ty variant uls -∗
    ∃ v1 v2, ⌜v = v1 ++ v2⌝ ∗
      v1 ◁ᵥ{π} r @ ty ∗ v2 ◁ᵥ{π} () @ uninit (UntypedSynType (active_union_rest_ly ul ly)).
  Proof.
    iIntros (Hul Hst) "Hv".
    rewrite {1}/ty_own_val/=.
    iDestruct "Hv" as "(%ul' & %ly' & %Hul' & %Hly & %Hst' & Hv1 & Hv2)".
    assert (ly' = ly) as -> by by eapply syn_type_has_layout_inj.
    assert (ul' = ul) as -> by by eapply union_layout_spec_has_layout_inj.
    iExists (take (ly_size ly) v), (drop (ly_size ly) v).
    rewrite take_drop. iR. iFrame.
  Qed.


  (* TODO *)
End unfold.

Section subltype.
  Context `{!typeGS Σ}.

  (* TODO *)

End subltype.

Section rules.
  Context `{!typeGS Σ}.

  (* needs to have lower priority than the id instance *)
  Import EqNotations.
  Definition enum_variant_type' {rt} (en : enum rt) (r : rt) : type (enum_tag_rt en (enum_tag en r)) :=
    rew (enum_variant_rt_tag_rt_eq en r _ eq_refl) in enum_variant_type en r.


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
    iIntros (?) "#CTX #HE HL Hna Hc".
    iApply wp_enum_init; first done.
    iApply ("HT" with "CTX HE HL Hna [Hc]").
    iIntros (L2 v rt ty r) "HL Hna Hv HT".
    iDestruct "HT" as "(%Hlook_st & %M & Hlfts & HT)".
    iPoseProof ("HT" with "Hlfts") as "HT".
    rewrite /interpret_rust_type_goal.
    iDestruct "HT" as "(%rto &  %tyo & %en & -> & <- & HT)".
    rewrite /trigger_tc. iDestruct "HT" as "(%ro & %Hc & HT)".
    iApply ("Hc" with "HL Hna [Hv] HT").
    iEval (rewrite /ty_own_val/=).
    destruct Hc as [[Hproj Htag]].
    iExists _, _, _, _.
    iR. iSplitR. { iPureIntro. apply Hly. }
    iApply (struct_init_val _ _ _ _ +[_; _] -[_; _]).
    { done. }
    { done. }
    simpl.
    assert (∃ tag : Z, list_to_map (M := gmap _ _) (els_tag_int (enum_els en)) !! variant = Some tag) as (tag & Htag_lookup).
    { apply list_to_map_lookup_fst.
      - rewrite els_tag_int_agree.
        apply elem_of_list_fmap. exists (variant, ty_syn_type ty).
        split; first done. apply elem_of_list_to_map; last done.
        apply els_variants_nodup.
      - rewrite els_tag_int_agree. apply els_variants_nodup. }
    apply use_enum_layout_alg_inv in Hly as (ul & variant_lys & Hul & Hsl & Hf).

    iSplitR.
    { iExists _, _, (els_tag_it (enum_els en)). iR. simpl.
      iSplitR. { iPureIntro. apply syn_type_has_layout_int; first done. apply els_tag_it_size. }
      iSplitR. { iPureIntro. apply syn_type_has_layout_int; first done. apply els_tag_it_size. }
      rewrite Htag_lookup/=.
      rewrite /enum_lookup_tag.
      rewrite /els_lookup_tag.
      subst variant. rewrite Htag_lookup /=.
      iApply type_int_val.
      - rewrite -MaxInt_eq. apply els_tag_it_size.
      - specialize (els_tag_int_wf3 (enum_els en)) as Hels.
        eapply Forall_forall in Hels.
        2: { apply elem_of_list_to_map_2. done. }
        done.
    }
    iSplitL; last done.
    iExists _, _, ul. iR.
    assert (use_union_layout_alg (uls_of_els (enum_els en)) = Some ul) as Hul'.
    { eapply use_union_layout_alg_Some; first done. done. }
    assert (syn_type_has_layout (uls_of_els (enum_els en)) ul).
    { eapply syn_type_has_layout_union; first done. done. }
    iR. iR.

    iEval (rewrite /ty_own_val) => /=.
    iExists ul.
    specialize (elem_of_list_to_map_2 _ _ _ Hlook_st) as Hel.
    apply elem_of_list_lookup_1 in Hel as (i & Hlook).
    specialize (Forall2_lookup_l _ _ _ _ _ Hf Hlook) as ([name2 ly] & Hlook_ly & <- & Halg).
    iExists ly. iR.
    iSplitR. { iPureIntro.
      rewrite /layout_of_union_member.
      specialize (union_layout_alg_has_variants _ _ _ _ Hul) as Hul_variants.
      rewrite (index_of_union_lookup _ i _ ly).
      2: { rewrite -Hul_variants. subst variant. done. }
      simpl. rewrite -Hul_variants. rewrite Hlook_ly. done. }
    simpl.
    iPoseProof (ty_own_val_has_layout with "Hv") as "%Hv"; first done.
    iR.
    iSplitL "Hv".
    - rewrite take_app'; first done. done.
    - rewrite drop_app'; last done.
      iApply uninit_own_spec.
      iExists _. iSplitR. { iPureIntro. apply syn_type_has_layout_untyped; first done.
        - by apply layout_wf_align_log_0.
        - rewrite ly_size_active_union_rest_ly. apply use_union_layout_alg_size in Hul'. lia.
        - by apply ly_align_in_bounds_1. }
      iPureIntro. rewrite /has_layout_val.
      rewrite replicate_length. rewrite /use_layout_alg'.
      erewrite elem_of_list_to_map_1; first last.
      { eapply elem_of_list_lookup_2. done. }
      { apply els_variants_nodup. }
      simpl. rewrite Halg. simpl.
      rewrite /use_union_layout_alg' Hul'/=.
      done.
  Qed.

End rules.
