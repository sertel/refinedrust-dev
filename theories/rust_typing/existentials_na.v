From refinedrust Require Export type ltypes programs.
From refinedrust Require Import uninit int ltype_rules.
From lrust.lifetime Require Import na_borrow.
Set Default Proof Using "Type".

Record na_ex_inv_def `{!typeGS Σ} (X : Type) (Y : Type) : Type := na_mk_ex_inv_def' {
  (* NOTE: Make persistent part (Timeless) + non-persistent part inside &na *)
  na_inv_P : thread_id → X → Y → iProp Σ;

  na_inv_P_lfts : list lft;
  na_inv_P_wf_E : elctx;
  na_inv_P_pers : ∀ π x y, Persistent (na_inv_P π x y);
  na_inv_P_timeless : ∀ π x y, Timeless (na_inv_P π x y);
}.

(* Stop Typeclass resolution for the [inv_P_pers] argument, to make it more deterministic. *)
Definition na_mk_ex_inv_def `{!typeGS Σ} {X Y : Type}
  (inv_P : thread_id → X → Y → iProp Σ)

  inv_P_lfts
  (inv_P_wf_E : elctx)
  (inv_P_pers : TCNoResolve (∀ (π : thread_id) (x : X) (y : Y), Persistent (inv_P π x y)))
  (inv_P_timeless: TCNoResolve (∀ (π : thread_id) (x : X) (y : Y), Timeless (inv_P π x y)))

  := na_mk_ex_inv_def' _ _ _ _
       inv_P inv_P_lfts inv_P_wf_E inv_P_pers inv_P_timeless.

Global Arguments na_inv_P {_ _ _ _}.
Global Arguments na_inv_P_lfts {_ _ _ _}.
Global Arguments na_inv_P_wf_E {_ _ _ _}.
Global Arguments na_inv_P_pers {_ _ _ _}.
Global Arguments na_inv_P_timeless {_ _ _ _}.
Global Existing Instance na_inv_P_pers.
Global Existing Instance na_inv_P_timeless.
Global Typeclasses Opaque na_mk_ex_inv_def.

(** Smart constructor for persistent and timeless [P] *)
Program Definition na_mk_pers_ex_inv_def
  `{!typeGS Σ} {X : Type} {Y : Type} (P : X → Y → iProp Σ)
  (_: TCNoResolve (∀ x y, Persistent (P x y)))
  (_: TCNoResolve (∀ x y, Timeless (P x y))): na_ex_inv_def X Y :=
    na_mk_ex_inv_def (λ _, P) [] [] _ _.
Next Obligation.
  by rewrite /TCNoResolve.
Qed.
Next Obligation.
  by rewrite /TCNoResolve.
Qed.

Global Typeclasses Opaque na_mk_pers_ex_inv_def.

Section na_ex.
  Context `{!typeGS Σ}.
  Context (X Y : Type) `{!Inhabited Y} (P : na_ex_inv_def X Y).

  Program Definition na_ex_plain_t (ty : type X) : type Y := {|
    ty_own_val π r v := ∃ x : X, P.(na_inv_P) π x r ∗ ty.(ty_own_val) π x v;
    ty_shr κ π r l := ∃ x : X,
      P.(na_inv_P) π x r ∗
      ty.(ty_sidecond) ∗
      &na{κ, π, shrN.@l}(∃ v, l ↦ v ∗ ty.(ty_own_val) π x v) ∗
      (∃ ly : layout, ⌜l `has_layout_loc` ly⌝ ∗ ⌜syn_type_has_layout (ty_syn_type ty) ly⌝);

    ty_syn_type := ty.(ty_syn_type);
    _ty_has_op_type ot mt := ty_has_op_type ty ot mt;
    ty_sidecond := ty.(ty_sidecond);

    ty_ghost_drop π r := ∃ x, P.(na_inv_P) π x r ∗ ty.(ty_ghost_drop) π x;
    ty_lfts := P.(na_inv_P_lfts) ++ ty.(ty_lfts);
    ty_wf_E := P.(na_inv_P_wf_E) ++ ty.(ty_wf_E);
  |}%I.

  (* ty_has_layout *)
  Next Obligation.
    iIntros (????) "(% & _ & ?)".
    by iApply ty_has_layout.
  Qed.

  (* _ty_op_type_stable *)
  Next Obligation.
    iIntros (????).
    by eapply ty_op_type_stable.
  Qed.

  (* ty_own_val_sidecond *)
  Next Obligation.
    iIntros (????) "(% & _ & ?)".
    by iApply ty_own_val_sidecond.
  Qed.

  (* ty_shr_sidecond *)
  Next Obligation.
    iIntros (?????) "(% & (_ & $ & _))".
  Qed.

  (* ty_shr_aligned *)
  Next Obligation.
    iIntros (?????) "(% & _ & _ & _ & $)".
  Qed.

  (* ty_share *)
  Next Obligation.
    iIntros (ty E κ l ly π r q ?) "#(LFT & TIME & LLCTX) Htok %Halg %Hly Hlb Hb".
    setoid_rewrite bi.sep_exist_l at 1.
    setoid_rewrite bi_exist_comm at 1.

    rewrite lft_intersect_list_app -!lft_tok_sep.
    iDestruct "Htok" as "(Htok & ? & ?)".

    iApply fupd_logical_step.
    iMod (bor_exists_tok with "LFT Hb Htok") as "(%x & Hb & Htok)"; first solve_ndisj.

    iPoseProof (bor_iff _ _ (P.(na_inv_P) π x r ∗ (∃ a : val, l ↦ a ∗ a ◁ᵥ{ π} x @ ty)) with "[] Hb") as "Hb".
    { iNext. iModIntro. iSplit; [iIntros "(% & ? & ? & ?)" | iIntros "(? & (% & ? & ?))"]; eauto with iFrame. }

    iMod (bor_sep with "LFT Hb") as "(HP & Hb)"; first solve_ndisj.
    iMod (bor_persistent with "LFT HP Htok") as "(>HP & Htok)"; first solve_ndisj.

    iMod (bor_get_persistent _ (ty_sidecond ty) with "LFT [] Hb Htok") as "(Hty & Hb & Htok)"; first solve_ndisj.
    { iIntros "$ !> !>".
      iApply ty_own_val_sidecond.
      (* NOTE: Use ty_own_val_sidecond *)
      admit. }

    iMod (bor_na with "Hb") as "Hb"; first solve_ndisj.
    iModIntro.

    iApply logical_step_intro; iFrame.
    iExists x; eauto with iFrame.
  Admitted.

  (* ty_shr_mono *)
  Next Obligation.
    iIntros (ty κ κ' π r l) "#Hincl (%x & HP & Hty & Hshr& Hly)".
    iExists x. iFrame.
    iApply (na_bor_shorten with "Hincl Hshr").
  Qed.

  (* ty_own_ghost_drop *)
  Next Obligation.
    iIntros (ty π r v F ?) "(%x & HP & Ha)".
    iPoseProof (ty_own_ghost_drop with "Ha") as "Ha"; first done.
    iApply (logical_step_compose with "Ha").
    iApply logical_step_intro.
    iIntros "Hdrop". eauto with iFrame.
  Qed.

  (* _ty_memcast_compat *)
  Next Obligation.
    iIntros (ty ot mt st π r v Hot) "(%x & HP & Hv)".
    iPoseProof (ty_memcast_compat with "Hv") as "Hm"; first done.
    destruct mt; eauto with iFrame.
  Qed.
End na_ex.

Notation "'∃na;' P ',' τ" := (na_ex_plain_t _ _ P τ) (at level 40) : stdpp_scope.

Section generated_code.
  From refinedrust Require Import typing shims.

  Section Cell_sls.
    Context `{!typeGS Σ}.

    Definition Cell_sls  : struct_layout_spec := mk_sls "Cell" [
      ("value", IntSynType I32)] StructReprRust.
    Definition Cell_st  : syn_type := Cell_sls .
  End Cell_sls.

  Section code.
    Context `{!typeGS Σ}.
    Open Scope printing_sugar.

    Definition Cell_new_def : function := {|
      f_args := [
        ("value", (it_layout I32) : layout)
      ];
      f_local_vars := [
        ("__0", (use_layout_alg' (Cell_st)) : layout);
        ("__2", (it_layout I32) : layout)
      ];
      f_code :=
        <[
        "_bb0" :=
        "__2" <-{ IntOp I32 } use{ IntOp I32 } ("value");
        "__0" <-{ (use_op_alg' (Cell_st)) } StructInit (Cell_sls) [("value", use{ IntOp I32 } ("__2") : expr)];
        return (use{ (use_op_alg' (Cell_st)) } ("__0"))
        ]>%E $
        ∅;
      f_init := "_bb0";
    |}.

    Definition Cell_get_def : function := {|
      f_args := [
        ("self", void* : layout)
      ];
      f_local_vars := [
        ("__0", (it_layout I32) : layout)
      ];
      f_code :=
        <[
        "_bb0" :=
        annot: CopyLftNameAnnot "plft3" "ulft__";
        "__0" <-{ IntOp I32 } use{ IntOp I32 } ((!{ PtrOp } ( "self" )) at{ (Cell_sls) } "value");
        return (use{ IntOp I32 } ("__0"))
        ]>%E $
        ∅;
      f_init := "_bb0";
    |}.

    Definition Cell_into_inner_def : function := {|
      f_args := [
        ("self", (use_layout_alg' (Cell_st)) : layout)
      ];
      f_local_vars := [
        ("__0", (it_layout I32) : layout)
      ];
      f_code :=
        <[
        "_bb0" :=
        "__0" <-{ IntOp I32 } use{ IntOp I32 } (("self") at{ (Cell_sls) } "value");
        return (use{ IntOp I32 } ("__0"))
        ]>%E $
        ∅;
      f_init := "_bb0";
    |}.
  End code.

  Section Cell_ty.
    Context `{!typeGS Σ}.

    Definition Cell_ty : type (plist place_rfn [Z : Type]) := struct_t Cell_sls +[(int I32)].
    Definition Cell_rt : Type.
    Proof using . let __a := eval hnf in (rt_of Cell_ty) in exact __a. Defined.

    Global Typeclasses Transparent Cell_ty.
    Global Typeclasses Transparent Cell_rt.
  End Cell_ty.
  Global Arguments Cell_rt : clear implicits.

  Section Cell_inv_t.
    Context `{!typeGS Σ}.

    Program Definition Cell_inv_t_inv_spec : na_ex_inv_def (Cell_rt) (Z) :=
      na_mk_ex_inv_def
        (λ π inner_rfn 'x, ⌜inner_rfn = -[#(x)]⌝ ∗ ⌜Zeven x⌝ ∗ True)%I
        []
        [] _ _.
    Next Obligation. ex_t_solve_persistent. Qed.
    Next Obligation. ex_t_solve_timeless. Qed.

    Definition Cell_inv_t : type (Z) :=
      na_ex_plain_t _ _ Cell_inv_t_inv_spec Cell_ty.
    Global Typeclasses Transparent Cell_inv_t.

    Definition Cell_inv_t_rt : Type.
    Proof using. let __a := eval hnf in (rt_of Cell_inv_t) in exact __a. Defined.
    Global Typeclasses Transparent Cell_inv_t_rt.
  End Cell_inv_t.
  Global Arguments Cell_inv_t_rt : clear implicits.

  Section specs.
    Context `{!typeGS Σ}.

    Definition type_of_Cell_new  :=
      fn(∀ (()) : 0 | (x) : (_), (λ ϝ, []); x @ (int I32); (λ π : thread_id, (⌜Zeven x⌝)))
        → ∃ _ : unit, x @ Cell_inv_t; (λ π : thread_id, True).

    Definition type_of_Cell_into_inner  :=
      fn(∀ (()) : 0 | (x) : (_), (λ ϝ, []); x @ Cell_inv_t; (λ π : thread_id, True))
        → ∃ _ : unit, x @ (int I32); (λ π : thread_id, (⌜Zeven x⌝)).

    Definition type_of_Cell_get  :=
      fn(∀ ((), ulft__) : 1 | (x) : (_), (λ ϝ, []); #x @ (shr_ref Cell_inv_t ulft__); (λ π : thread_id, True))
        → ∃ _ : unit, x @ (int I32); (λ π : thread_id, (⌜Zeven x⌝)).
  End specs.

  Section proof.
    Context `{!typeGS Σ}.

    Definition Cell_new_lemma  (π : thread_id) : Prop :=
      syn_type_is_layoutable ((syn_type_of_sls (Cell_sls))) →
      ⊢ typed_function π (Cell_new_def ) [(syn_type_of_sls (Cell_sls)); IntSynType I32] (type_of_Cell_new ).

    Definition Cell_into_inner_lemma (π : thread_id) : Prop :=
      syn_type_is_layoutable (Cell_st) →
      ⊢ typed_function π (Cell_into_inner_def ) [IntSynType I32] (type_of_Cell_into_inner ).

    Definition Cell_get_lemma (π : thread_id) : Prop :=
      syn_type_is_layoutable (Cell_st) →
      ⊢ typed_function π (Cell_get_def ) [IntSynType I32] (type_of_Cell_get ).
  End proof.

  Ltac Cell_new_prelude :=
    unfold Cell_new_lemma;
    set (FN_NAME := FUNCTION_NAME "Cell_new");
    intros;
    iStartProof;
    start_function "Cell_new" ( [] ) (  x );
    set (loop_map := BB_INV_MAP (PolyNil));
    intros arg_value local___0 local___2;
    prepare_parameters ( x );
    init_lfts (∅ );
    init_tyvars ( ∅ ).

  Ltac Cell_into_inner_prelude := (* self -> T *)
    unfold Cell_into_inner_lemma;
    set (FN_NAME := FUNCTION_NAME "Cell_into_inner");
    intros;
    iStartProof;
    start_function "Cell_into_inner" ( [] ) (  x );
    set (loop_map := BB_INV_MAP (PolyNil));
    intros arg_self local___0;
    prepare_parameters ( x );
    init_lfts (∅ );
    init_tyvars ( ∅ ).

  Ltac Cell_get_prelude := (* &self -> T *)
    unfold Cell_get_lemma;
    set (FN_NAME := FUNCTION_NAME "Cell_get");
    intros;
    iStartProof;
    let ulft__ := fresh "ulft__" in
    start_function "Cell_get" ( [ [] ulft__] ) (  x );
    set (loop_map := BB_INV_MAP (PolyNil));
    intros arg_self local___0;
    prepare_parameters ( x );
    init_lfts (named_lft_update "ulft__" ulft__ $ ∅ );
    init_tyvars ( ∅ ).


  Section na_subtype.
    Context `{!typeGS Σ}.
    Context {rt X : Type} `{!Inhabited X} (P : na_ex_inv_def rt X).

    Lemma na_owned_subtype_ex_plain_t π E L (ty : type rt) (r : rt) (r' : X) T :
      (prove_with_subtype E L false ProveDirect (P.(na_inv_P) π r r') (λ L1 _ R, R -∗ T L1))
      ⊢ owned_subtype π E L false r r' ty (∃na; P, ty) T.
    Proof.
      unfold owned_subtype, prove_with_subtype.

      (* Nothing has changed *)
      iIntros "HT".
      iIntros (???) "#CTX #HE HL".
      iMod ("HT" with "[//] [//] CTX HE HL") as "(%L2 & % & %R2 & >(Hinv & HR2) & HL & HT)".
      iExists L2. iFrame. iPoseProof ("HT" with "HR2") as "$". iModIntro.
      iSplitR; last iSplitR.
      - simpl. iPureIntro.
        intros ly1 ly2 Hly1 HLy2. f_equiv. by eapply syn_type_has_layout_inj.
      - simpl. eauto.
      - iIntros (v) "Hv0".
        iEval (rewrite /ty_own_val/=).
        eauto with iFrame.
    Qed.

    Lemma na_ex_plain_t_open_owned F π (ty : type rt) (wl : bool) (l : loc) (x : X) :
      lftE ⊆ F →
      l ◁ₗ[π, Owned wl] PlaceIn x @ (◁ (∃na; P, ty)) ={F}=∗
      ∃ r : rt, P.(na_inv_P) π r x ∗
      l ◁ₗ[π, Owned false] PlaceIn r @ (◁ ty) ∗
      (∀ rt' (lt' : ltype rt') (r' : place_rfn rt'),
        l ◁ₗ[π, Owned false] r' @ lt' -∗
        ⌜ltype_st lt' = ty_syn_type ty⌝ -∗
        l ◁ₗ[π, Owned wl] r' @
          (OpenedLtype lt' (◁ ty) (◁ ∃na; P, ty)
            (λ (r : rt) (x : X), P.(na_inv_P) π r x)
            (λ r x, True)))%I.
    Proof.
      (* Nothing has changed *)
      iIntros (?) "Hb".
      rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iDestruct "Hb" as "(%ly & %Halg & %Hly & #Hsc & #Hlb & Hcred & %x' & Hrfn & Hb)".
      iMod (maybe_use_credit with "Hcred Hb") as "(Hcred & Hat & Hb)"; first done.

      unfold ty_own_val, na_ex_plain_t at 2.
      iDestruct "Hb" as "(%v & Hl & %r & HP & Hv)".

      iDestruct "Hrfn" as "<-".
      iModIntro. iExists r. iFrame.
      iSplitL "Hl Hv".
      { rewrite ltype_own_ofty_unfold /lty_of_ty_own.
        iExists ly. iFrame "#%". iSplitR; first done.
        iExists r. iSplitR; first done. iModIntro. eauto with iFrame. }

      iIntros (rt' lt' r') "Hb %Hst".
      rewrite ltype_own_opened_unfold /opened_ltype_own.
      iExists ly. rewrite Hst.
      do 5 iR; iFrame.

      clear -Halg Hly.
      iApply (logical_step_intro_maybe with "Hat").
      iIntros "Hcred' !>".
      iIntros (r' r'' κs) "HP".
      iSplitR; first done.
      iIntros "Hdead Hl".
      rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iDestruct "Hl" as "(%ly' & _ & _ & Hsc' & _ & _ & %r0 & -> & >Hb)".
      iDestruct "Hb" as "(%v' & Hl & Hv)".
      iMod ("HP" with "Hdead" ) as "HP".
      iModIntro.
      rewrite ltype_own_core_equiv. simp_ltypes.
      rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iExists ly. simpl. iFrame "#%". iFrame.
      iExists r''. iSplitR; first done. iModIntro.
      iExists v'. iFrame. iExists r0. by iFrame.
    Qed.

    Lemma na_typed_place_ex_plain_t_owned π E L l (ty : type rt) x wl bmin K T :
      (∀ r, introduce_with_hooks E L (P.(na_inv_P) π r x)
        (λ L2, typed_place π E L2 l
                 (OpenedLtype (◁ ty) (◁ ty) (◁ (∃na; P, ty)) (λ (r : rt) (x : X), P.(na_inv_P) π r x) (λ r x, True))
                 (#r) bmin (Owned wl) K
          (λ L2 κs li b2 bmin' rti ltyi ri strong weak,
            (* no weak update possible - after all, we have just opened this invariant *)
            T L2 κs li b2 bmin' rti ltyi ri strong None)))
      ⊢ typed_place π E L l (◁ (∃na; P, ty))%I (#x) bmin (Owned wl) K T.
    Proof.
      unfold introduce_with_hooks, typed_place.

      (* Nothing has changed *)
      iIntros "HT". iIntros (F ???) "#CTX #HE HL Hincl Hb Hcont".
      iApply fupd_place_to_wp.
      iMod (na_ex_plain_t_open_owned with "Hb") as "(%r & HP & Hb & Hcl)"; first done.
      iPoseProof ("Hcl" with "Hb []") as "Hb"; first done.
      iMod ("HT" with "[] HE HL HP") as "(%L2 & HL & HT)"; first done.
      iApply ("HT" with "[//] [//] CTX HE HL Hincl Hb").
      iModIntro. iIntros (L' κs l2 b2 bmin0 rti ltyi ri strong weak) "Hincl Hl Hc".
      iApply ("Hcont" with "Hincl Hl").
      iSplit; last done.
      iDestruct "Hc" as "[Hc _]".
      destruct strong; last done.
      simp_ltypes. done.
    Qed.

    Lemma na_ex_plain_t_open_shared F π (ty : type rt) q κ l (x : X) :
      lftE ⊆ F →
      ↑shrN.@l ⊆ F →

      lft_ctx -∗
      na_own π ⊤ -∗
      maybe_creds true -∗
      q.[κ] -∗
      l ◁ₗ[π, Shared κ] (#x) @ (◁ (∃na; P, ty)) ={F}=∗

      ∃ r : rt, P.(na_inv_P) π r x ∗
      l ◁ₗ[π, Owned true] PlaceIn r @ (◁ ty) ∗

      (* (∀ (r' : place_rfn rt), *)
      ( l ◁ₗ[π, Owned false] (#r) @ (◁ ty) ={F}=∗
            q.[κ] ∗ na_own π ⊤ ).
    (* TODO: Closing view-shift here. *)
    Proof.
      iIntros (??) "#LFT Hna Hcred Hq #Hb".

      iEval (rewrite ltype_own_ofty_unfold /lty_of_ty_own) in "Hb".
      iDestruct "Hb" as (ly Halg Hly) "(Hsc & Hlb & %v & -> & #Hb)".

      iMod (fupd_mask_mono with "Hb") as "#Hb'"; first done. iClear "Hb".

      iEval (unfold ty_shr, na_ex_plain_t) in "Hb'".
      iDestruct "Hb'" as (r) "(HP & Hscr & Hbor & %ly' & %Hly' & %Halg')".

      iMod (na_bor_acc with "LFT Hbor Hq Hna") as "(Hl & Hna & Hvs)"; [ solve_ndisj.. |].

      iModIntro; iExists r.
      iSplitR; first done.

      iSplitL "Hl Hcred".
      { rewrite ltype_own_ofty_unfold /lty_of_ty_own.
        iExists ly. iFrame (Halg Hly) "Hlb Hcred Hscr".
        iExists r; iR.
        by iModIntro. }

      iIntros "Hb".
      iEval (rewrite ltype_own_ofty_unfold /lty_of_ty_own) in "Hb".
      iDestruct "Hb" as (???) "(_ & #Hloc'' & _ & (% & -> & Hb)) /=".

      (* iAssert (⌜ly0 = ly1⌝)%I as "<-". *)
      (* { iPureIntro; by eapply syn_type_has_layout_inj. } *)

      iMod (fupd_mask_mono with "Hb") as "Hb"; first done.
      iApply ("Hvs" with "Hb Hna").
    Qed.

    Lemma na_typed_place_ex_plain_t_shared π E L l (ty : type rt) x κ bmin K T :
      li_tactic (lctx_lft_alive_count_goal E L κ)  (λ '(_, L2),
        ∀ r, introduce_with_hooks E L2 (P.(na_inv_P) π r x)
          (λ L3, typed_place π E L3 l
                  (ShadowedLtype (◁ ty) #r (◁ (∃na; P, ty)))
                  (#x) bmin (Owned true) K T))
      ⊢ typed_place π E L l (◁ (∃na; P, ty))%I (#x) bmin (Shared κ) K T.
    Proof.
      rewrite /lctx_lft_alive_count_goal.
      iIntros "(%κs & %L' & %Hal & HT)".

      rewrite /typed_place /introduce_with_hooks.
      iIntros (Φ ???) "#(LFT & TIME & LLCTX) #HE HL Hincl Hb Hcont".

      iApply fupd_place_to_wp.
      iMod (lctx_lft_alive_count_tok with "HE HL") as (q) "(Htok & Htokcl & HL)"; [ done.. |].
      iMod (na_ex_plain_t_open_shared with "LFT [] [] Htok Hb") as (r) "(HP & Hb & Hvs)"; [ done.. | admit | admit |].

      iMod ("HT" with "[] HE HL HP") as "(%L2 & HL & HT)"; first done.
      iApply ("HT" with "[//] [//] [$LFT $TIME $LLCTX] HE HL [Hincl] [Hb]").
      { by iApply (bor_kind_incl_trans with "Hincl"). }
      { rewrite ltype_own_shadowed_unfold /shadowed_ltype_own; iR.
        iEval (rewrite ltype_own_ofty_unfold /lty_of_ty_own) in "Hb".

        iDestruct "Hb" as (ly) "(#Hsyn & #Hly & #Hsc & #Hlb & _ & Hb)".
        iDestruct "Hb" as (r') "(#Hrfn & Hb)" => /=.

        iSplitL; rewrite ltype_own_ofty_unfold /lty_of_ty_own.
        - iExists ly; iFrame "#".
          iSplitR; first admit.
          iExists r'; iFrame "# ∗".

        - iExists ly; iFrame "#".
          iSplitR; first admit.
          iExists x; iR.
          simpl. admit. }

      iModIntro.
      iIntros (L'' κs' l2 b2 bmin0 rti ltyi ri strong weak) "Hincl Hl Hc".
      iApply ("Hcont" with "Hincl Hl").

      iSplit.
      - iDestruct "Hc" as "[Hc _]".
        simp_ltypes; destruct strong; last done.

        iIntros (r' r'' κs'') "Hl %".
        iSpecialize ("Hc" $! r' r'' κs'').

        admit.

      - iDestruct "Hc" as "[_ Hc]".
        destruct weak; last done.
        iIntros (???) "Hincl Hl Hcond".
        iMod ("Hc" with "Hincl Hl Hcond") as "(Ha & Hb & Htoks & Hc)".
        iFrame.
        iDestruct "Hb" as "(Hcond_ty & _)".

        admit.
    Admitted.
  End na_subtype.

  Section proof.
    Context `{!typeGS Σ}.

    Lemma Cell_T_new_proof (π : thread_id) :
      Cell_new_lemma π.
    Proof.
      Cell_new_prelude.

      rep <- 1 liRStep; liShow.

      iApply na_owned_subtype_ex_plain_t.
      liSimpl; liShow.

      repeat liRStep; liShow.

      all: print_remaining_goal.
      Unshelve. all: sidecond_solver.
      Unshelve. all: sidecond_hammer.
      Unshelve. all: print_remaining_sidecond.
    Qed.

    Lemma Cell_into_inner_proof (π : thread_id) :
      Cell_into_inner_lemma π.
    Proof.
      Cell_into_inner_prelude.

      repeat liRStep; liShow.

      iApply na_typed_place_ex_plain_t_owned.
      liSimpl; liShow.

      repeat liRStep; liShow.

      all: print_remaining_goal.
      Unshelve. all: sidecond_solver.
      Unshelve. all: sidecond_hammer.
      Unshelve. all: print_remaining_sidecond.
    Qed.

    Lemma Cell_get_proof (π : thread_id) :
      Cell_get_lemma π.
    Proof.
      Cell_get_prelude.

      repeat liRStep; liShow.

      iApply na_typed_place_ex_plain_t_shared.
      liSimpl; liShow.

      repeat liRStep; liShow.

      all: print_remaining_goal.
      Unshelve. all: sidecond_solver.
      Unshelve. all: sidecond_hammer.
      Unshelve. all: print_remaining_sidecond.
    Qed.
  End proof.


End generated_code.
