From refinedrust Require Export type ltypes programs.
From refinedrust Require Import uninit int ltype_rules.
From lrust.lifetime Require Import na_borrow.
Set Default Proof Using "Type".

Record na_ex_inv_def `{!typeGS Σ} (X : Type) (Y : Type) : Type := na_mk_ex_inv_def' {
  (* NOTE: Make persistent part (Timeless) + non-persistent part inside &na *)
  na_inv_P : thread_id → X → Y → iProp Σ;

  na_inv_P_lfts : list lft;
  na_inv_P_wf_E : elctx;
}.

(* Stop Typeclass resolution for the [inv_P_pers] argument, to make it more deterministic. *)
Definition na_mk_ex_inv_def `{!typeGS Σ} {X Y : Type}
  (inv_P : thread_id → X → Y → iProp Σ)

  inv_P_lfts
  (inv_P_wf_E : elctx)

  := na_mk_ex_inv_def' _ _ _ _
       inv_P inv_P_lfts inv_P_wf_E.

Global Arguments na_inv_P {_ _ _ _}.
Global Arguments na_inv_P_lfts {_ _ _ _}.
Global Arguments na_inv_P_wf_E {_ _ _ _}.
Global Typeclasses Opaque na_mk_ex_inv_def.

(** Smart constructor for persistent and timeless [P] *)
Program Definition na_mk_pers_ex_inv_def
  `{!typeGS Σ} {X : Type} {Y : Type} (P : X → Y → iProp Σ) :=
    na_mk_ex_inv_def (λ _, P) [] [] (* _ *).
Global Typeclasses Opaque na_mk_pers_ex_inv_def.

Section na_ex.
  Context `{!typeGS Σ}.
  Context (X Y : Type) `{!Inhabited Y} (P : na_ex_inv_def X Y).

  Program Definition na_ex_plain_t (ty : type X) : type Y := {|
    ty_own_val π r v := ∃ x : X, P.(na_inv_P) π x r ∗ ty.(ty_own_val) π x v;
    ty_shr κ π r l :=
      (* TODO: Add persistant part that cannot depends on the refined value *)
      ty.(ty_sidecond) ∗
      &na{κ, π, shrN.@l}(∃ x, l ↦: ty.(ty_own_val) π x ∗ P.(na_inv_P) π x r) ∗
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
    iIntros (?????) "($ & _ & _)".
  Qed.

  (* ty_shr_aligned *)
  Next Obligation.
    iIntros (?????) "(_ & _ & $)".
  Qed.

  (* ty_share *)
  Next Obligation.
    iIntros (ty E κ l ly π r q ?) "#(LFT & TIME & LLCTX) Htok %Halg %Hly Hlb Hbor".
    iEval (setoid_rewrite bi.sep_exist_l) in "Hbor".
    iEval (setoid_rewrite bi_exist_comm) in "Hbor".

    rewrite lft_intersect_list_app -!lft_tok_sep.
    iDestruct "Htok" as "(Htok & ? & ?)".

    iApply fupd_logical_step; iApply logical_step_intro.

    (* NOTE: Is there a simplier setoid_rewrite to do here ? *)
    iPoseProof (bor_iff _ _ (∃ x: X, l ↦: ty_own_val ty π x ∗ P.(na_inv_P) π x r) with "[] Hbor") as "Hbor".
    { iNext. iModIntro. iSplit; [iIntros "(% & % & ? & ? & ?)" | iIntros "(% & (% & ? & ?) & ?)"]; eauto with iFrame. }

    iMod (bor_get_persistent _ (ty_sidecond ty) with "LFT [] Hbor Htok") as "(Hty & Hbor & Htok)"; first solve_ndisj.
    { iIntros "Hinv".
      iDestruct "Hinv" as (v) "((% & Hl & HP) & Hv)".
      iPoseProof (ty_own_val_sidecond with "HP") as "#>Hsc".
      iModIntro; iSplit; [iNext | done].
      iExists v; iFrame.
      iExists v0; iFrame. }

    iMod (bor_na with "Hbor") as "Hbor"; first solve_ndisj.

    iModIntro; iFrame.
    iExists ly; eauto with iFrame.
  Qed.

  (* ty_shr_mono *)
  Next Obligation.
    iIntros (ty κ κ' π r l) "Hincl ($ & Hbor & %ly & ? & ?)".
    iSplitL "Hincl Hbor".
    - iApply (na_bor_shorten with "Hincl Hbor").
    - iExists ly. iFrame.
  Qed.

  (* ty_own_ghost_drop *)
  Next Obligation.
    iIntros (ty π r v F ?) "(%x & ? & Hv)".
    iPoseProof (ty_own_ghost_drop with "Hv") as "Hv"; first done.
    iApply (logical_step_compose with "Hv").
    iApply logical_step_intro.
    iIntros "?". eauto with iFrame.
  Qed.

  (* _ty_memcast_compat *)
  Next Obligation.
    iIntros (ty ot mt st π r v Hot) "(%x & ? & Hv)".
    iPoseProof (ty_memcast_compat with "Hv") as "Hm"; first done.
    destruct mt; eauto with iFrame.
  Qed.
End na_ex.

Notation "'∃na;' P ',' τ" := (na_ex_plain_t _ _ P τ) (at level 40) : stdpp_scope.

Section generated_code.
  From refinedrust Require Import typing shims.

  Section UnsafeCell_sls.
    Context `{!typeGS Σ}.

    (* NOTE: Is StructReprTransparent ready? *)
    Definition UnsafeCell_sls : struct_layout_spec := mk_sls "UnsafeCell" [
      ("value", IntSynType I32)] StructReprTransparent.
    Definition UnsafeCell_st : syn_type := UnsafeCell_sls.
  End UnsafeCell_sls.

  Section Cell_sls.
    Context `{!typeGS Σ}.

    Definition Cell_sls  : struct_layout_spec := mk_sls "Cell" [
      ("value", UnsafeCell_st)] StructReprRust.
    Definition Cell_st  : syn_type := Cell_sls .
  End Cell_sls.

  Section code.
    Context `{!typeGS Σ}.
    Open Scope printing_sugar.

    Definition UnsafeCell_new_def : function := {|
      f_args := [
        ("value", (it_layout I32) : layout)
      ];
      f_local_vars := [
        ("__0", (use_layout_alg' (UnsafeCell_st)) : layout);
        ("__2", (it_layout I32) : layout)
      ];
      f_code :=
        <[
        "_bb0" :=
        "__2" <-{ IntOp I32 } use{ IntOp I32 } ("value");
        "__0" <-{ (use_op_alg' (UnsafeCell_st)) } StructInit UnsafeCell_sls [("value", use{ IntOp I32 } ("__2") : expr)];
        return (use{ (use_op_alg' (UnsafeCell_st)) } ("__0"))
        ]>%E $
        ∅;
      f_init := "_bb0";
    |}.

    Definition UnsafeCell_into_inner_def : function := {|
      f_args := [
        ("self", (use_layout_alg' (UnsafeCell_st)) : layout)
      ];
      f_local_vars := [
        ("__0", (it_layout I32) : layout)
      ];
      f_code :=
        <[
        "_bb0" :=
        "__0" <-{ IntOp I32 } use{ IntOp I32 } (("self") at{ UnsafeCell_sls } "value");
        return (use{ IntOp I32 } ("__0"))
        ]>%E $
        ∅;
      f_init := "_bb0";
    |}.

    Definition UnsafeCell_get_old_def : function := {|
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
        "__0" <-{ IntOp I32 } use{ IntOp I32 } ((!{ PtrOp } ( "self" )) at{ (UnsafeCell_sls) } "value");
        return (use{ IntOp I32 } ("__0"))
        ]>%E $
        ∅;
      f_init := "_bb0";
    |}.

    Definition UnsafeCell_get_def : function := {|
      f_args := [
        ("self", void* : layout)
      ];
      f_local_vars := [
        ("__0", void* : layout);
        ("__2", void* : layout);
        ("__3", void* : layout)
      ];
      f_code :=
        <[
        "_bb0" :=
        annot: CopyLftNameAnnot "plft3" "ulft_1";
        "__3" <-{ PtrOp } &raw{ Shr } (!{ PtrOp } ( "self" ));
        "__2" <-{ PtrOp } use{ PtrOp } ("__3");
        "__0" <-{ PtrOp } use{ PtrOp } ("__2");
        return (use{ PtrOp } ("__0"))
        ]>%E $
        ∅;
      f_init := "_bb0";
    |}.

    Definition Cell_new_def (UnsafeCell_new_loc : loc) : function := {|
      f_args := [
        ("value", (it_layout I32) : layout)
      ];
      f_local_vars := [
        ("__0", (use_layout_alg' (Cell_st)) : layout);
        ("__2", (use_layout_alg' (UnsafeCell_st)) : layout);
        ("__3", (it_layout I32) : layout)
      ];
      f_code :=
        <[
        "_bb0" :=
        "__3" <-{ IntOp I32 } use{ IntOp I32 } ("value");
        "__2" <-{ (use_op_alg' (UnsafeCell_st)) } CallE UnsafeCell_new_loc [] [@{expr} use{ IntOp I32 } ("__3")];
        Goto "_bb1"
        ]>%E $
        <[
        "_bb1" :=
        "__0" <-{ (use_op_alg' (Cell_st)) } StructInit Cell_sls [("value", use{ (use_op_alg' (UnsafeCell_st)) } ("__2") : expr)];
        return (use{ (use_op_alg' (Cell_st)) } ("__0"))
        ]>%E $
        ∅;
      f_init := "_bb0";
    |}.

    Definition Cell_into_inner_def (UnsafeCell_into_inner_loc : loc) : function := {|
      f_args := [
        ("self", (use_layout_alg' (Cell_st)) : layout)
      ];
      f_local_vars := [
        ("__0", (it_layout I32) : layout);
        ("__2", (use_layout_alg' (UnsafeCell_st)) : layout)
      ];
      f_code :=
        <[
        "_bb0" :=
        "__2" <-{ (use_op_alg' (UnsafeCell_st)) } use{ (use_op_alg' (UnsafeCell_st)) } (("self") at{ Cell_sls } "value");
        "__0" <-{ IntOp I32 } CallE UnsafeCell_into_inner_loc [] [@{expr} use{ (use_op_alg' (UnsafeCell_st)) } ("__2")];
        Goto "_bb1"
        ]>%E $
        <[
        "_bb1" :=
        return (use{ IntOp I32 } ("__0"))
        ]>%E $
        ∅;
      f_init := "_bb0";
    |}.

  End code.

  Section UnsafeCell_ty.
    Context `{!typeGS Σ}.

    Definition UnsafeCell_ty : type (plist place_rfn [Z : Type]).
    Proof using  Type*. exact (struct_t UnsafeCell_sls +[(int I32)]). Defined.

    Definition UnsafeCell_rt : Type.
    Proof using . let __a := eval hnf in (rt_of UnsafeCell_ty) in exact __a. Defined.

    Global Typeclasses Transparent UnsafeCell_ty.
    Global Typeclasses Transparent UnsafeCell_rt.
 End UnsafeCell_ty.
 Global Arguments UnsafeCell_rt : clear implicits.

  Section UnsafeCell_inv_t.
    Context `{!typeGS Σ}.

    Program Definition UnsafeCell_inv_t_inv_spec : na_ex_inv_def (UnsafeCell_rt) (Z) :=
      na_mk_ex_inv_def
        (λ π inner_rfn 'x, ⌜inner_rfn = -[#(x)]⌝ ∗ ⌜Zeven x⌝ ∗ True)%I
        [] [].

    Definition UnsafeCell_inv_t : type (Z) :=
      na_ex_plain_t _ _ UnsafeCell_inv_t_inv_spec UnsafeCell_ty.

    Definition UnsafeCell_inv_t_rt : Type.
    Proof using. let __a := eval hnf in (rt_of UnsafeCell_inv_t) in exact __a. Defined.

    Global Typeclasses Transparent UnsafeCell_inv_t.
    Global Typeclasses Transparent UnsafeCell_inv_t_rt.
  End UnsafeCell_inv_t.
  Global Arguments UnsafeCell_inv_t_rt : clear implicits.

  Section Cell_ty.
    Context `{!typeGS Σ}.

    Definition Cell_ty : type (plist place_rfn [UnsafeCell_inv_t_rt : Type]).
    Proof using  Type*. exact (struct_t Cell_sls +[UnsafeCell_inv_t]). Defined.
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
        [] [].

    Definition Cell_inv_t : type (Z) :=
      na_ex_plain_t _ _ Cell_inv_t_inv_spec Cell_ty.

    Definition Cell_inv_t_rt : Type.
    Proof using . let __a := eval hnf in (rt_of Cell_inv_t) in exact __a. Defined.

    Global Typeclasses Transparent Cell_inv_t.
    Global Typeclasses Transparent Cell_inv_t_rt.
  End Cell_inv_t.
  Global Arguments Cell_inv_t_rt : clear implicits.

  Section specs.
    Context `{!typeGS Σ}.

    Definition type_of_UnsafeCell_new  :=
      fn(∀ (()) : 0 | (x) : (Z), (λ ϝ, []); x @ (int I32); (λ π : thread_id, (⌜Zeven x⌝)))
        → ∃ _ : unit, x @ UnsafeCell_inv_t; (λ π : thread_id, True).

    Definition type_of_UnsafeCell_into_inner  :=
      fn(∀ (()) : 0 | (x) : (Z), (λ ϝ, []); x @ UnsafeCell_inv_t; (λ π : thread_id, True))
        → ∃ _ : unit, x @ (int I32); (λ π : thread_id, (⌜Zeven x⌝)).

    Definition type_of_UnsafeCell_get_old  :=
      fn(∀ ((), ulft__) : 1 | (x) : (_), (λ ϝ, []); #x @ (shr_ref UnsafeCell_inv_t ulft__); (λ π : thread_id, True))
        → ∃ _ : unit, x @ (int I32); (λ π : thread_id, (⌜Zeven x⌝)).

    Definition type_of_Cell_new  :=
      fn(∀ (()) : 0 | (x) : (Z), (λ ϝ, []); x @ (int I32); (λ π : thread_id, (⌜Zeven x⌝)))
        → ∃ _ : unit, x @ Cell_inv_t; (λ π : thread_id, True).

    Definition type_of_Cell_into_inner  :=
      fn(∀ (()) : 0 | (x) : (Z), (λ ϝ, []); x @ Cell_inv_t; (λ π : thread_id, True))
        → ∃ _ : unit, x @ (int I32); (λ π : thread_id, (⌜Zeven x⌝)).
  End specs.

  Section proof.
    Context `{!typeGS Σ}.

    Definition UnsafeCell_new_lemma (π : thread_id) : Prop :=
      syn_type_is_layoutable ((UnsafeCell_sls : syn_type)) →
      ⊢ typed_function π (UnsafeCell_new_def ) [UnsafeCell_st; IntSynType I32] (type_of_UnsafeCell_new ).

    Definition UnsafeCell_into_inner_lemma (π : thread_id) : Prop :=
      syn_type_is_layoutable ((UnsafeCell_sls : syn_type)) →
      ⊢ typed_function π (UnsafeCell_into_inner_def ) [IntSynType I32] (type_of_UnsafeCell_into_inner ).

    Definition UnsafeCell_get_old_lemma (π : thread_id) : Prop :=
      syn_type_is_layoutable (Cell_st) →
      ⊢ typed_function π (UnsafeCell_get_old_def ) [IntSynType I32] (type_of_UnsafeCell_get_old ).

    Definition Cell_new_lemma (π : thread_id) : Prop :=
      ∀ (UnsafeCell_new_loc : loc) ,
      syn_type_is_layoutable ((Cell_sls : syn_type)) →
      syn_type_is_layoutable ((UnsafeCell_sls : syn_type)) →
      UnsafeCell_new_loc ◁ᵥ{π} UnsafeCell_new_loc @ function_ptr [IntSynType I32] (type_of_UnsafeCell_new ) -∗
      typed_function π (Cell_new_def UnsafeCell_new_loc  ) [Cell_st; UnsafeCell_st; IntSynType I32] (type_of_Cell_new ).

    Definition Cell_into_inner_lemma (π : thread_id) : Prop :=
      ∀ (UnsafeCell_into_inner_loc : loc) ,
      syn_type_is_layoutable ((Cell_sls : syn_type)) →
      syn_type_is_layoutable ((UnsafeCell_sls : syn_type)) →
      UnsafeCell_into_inner_loc ◁ᵥ{π} UnsafeCell_into_inner_loc @ function_ptr [UnsafeCell_st] (type_of_UnsafeCell_into_inner ) -∗
      typed_function π (Cell_into_inner_def UnsafeCell_into_inner_loc  ) [IntSynType I32; UnsafeCell_st] (type_of_Cell_into_inner ).
  End proof.

  Ltac UnsafeCell_new_prelude :=
    unfold UnsafeCell_new_lemma;
    set (FN_NAME := FUNCTION_NAME "UnsafeCell_new");
    intros;
    iStartProof;
    start_function "UnsafeCell_new" ( [] ) (  x );
    set (loop_map := BB_INV_MAP (PolyNil));
    intros arg_value local___0 local___2;
    prepare_parameters ( x );
    init_lfts (∅ );
    init_tyvars ( ∅ ).

  Ltac UnsafeCell_into_inner_prelude :=
    unfold UnsafeCell_into_inner_lemma;
    set (FN_NAME := FUNCTION_NAME "UnsafeCell_into_inner");
    intros;
    iStartProof;
    start_function "UnsafeCell_into_inner" ( [] ) (  x );
    set (loop_map := BB_INV_MAP (PolyNil));
    intros arg_self local___0;
    prepare_parameters ( x );
    init_lfts (∅ );
    init_tyvars ( ∅ ).

  Ltac UnsafeCell_get_old_prelude :=
    unfold UnsafeCell_get_old_lemma;
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

  Ltac Cell_new_prelude :=
    unfold Cell_new_lemma;
    set (FN_NAME := FUNCTION_NAME "Cell_new");
    intros;
    iStartProof;
    start_function "Cell_new" ( [] ) (  x );
    set (loop_map := BB_INV_MAP (PolyNil));
    intros arg_value local___0 local___2 local___3;
    prepare_parameters ( x );
    init_lfts (∅ );
    init_tyvars ( ∅ ).

  Ltac Cell_into_inner_prelude :=
    unfold Cell_into_inner_lemma;
    set (FN_NAME := FUNCTION_NAME "Cell_into_inner");
    intros;
    iStartProof;
    start_function "Cell_into_inner" ( [] ) (  x );
    set (loop_map := BB_INV_MAP (PolyNil));
    intros arg_self local___0 local___2;
    prepare_parameters ( x );
    init_lfts (∅ );
    init_tyvars ( ∅ ).

  (* === V TYPING RULES V === *)

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
      iIntros "HT". iIntros (F ???) "#CTX #HE HL Hna Hincl Hb Hcont".
      iApply fupd_place_to_wp.
      iMod (na_ex_plain_t_open_owned with "Hb") as "(%r & HP & Hb & Hcl)"; first done.
      iPoseProof ("Hcl" with "Hb []") as "Hb"; first done.
      iMod ("HT" with "[] HE HL HP") as "(%L2 & HL & HT)"; first done.
      iApply ("HT" with "[//] [//] CTX HE HL Hna Hincl Hb").
      iModIntro. iIntros (L' κs l2 b2 bmin0 rti ltyi ri strong weak) "Hincl Hl Hc".
      iApply ("Hcont" with "Hincl Hl").
      iSplit; last done.
      iDestruct "Hc" as "[Hc _]".
      destruct strong; last done.
      simp_ltypes. done.
    Qed.

    Lemma na_ex_plain_t_open_shared E F π (ty : type rt) q κ l (x : X) :
      lftE ⊆ E →
      ↑shrN.@l ⊆ E →
      ↑shrN.@l ⊆ F →

      lft_ctx -∗
      na_own π F -∗
      £ 1 -∗ (* Required: P.(na_inv_P) is not Timeless *)

      q.[κ] -∗
      l ◁ₗ[π, Shared κ] (#x) @ (◁ (∃na; P, ty)) ={E}=∗

      ∃ r : rt,
        P.(na_inv_P) π r x ∗
        ▷ (l ◁ₗ[π, Owned false] PlaceIn r @ (◁ ty)) ∗
        (* NOTE: Make &na appears, as it's required afterwards. *)
        &na{κ, π, shrN.@l} (∃ r : rt, l ↦: ty_own_val ty π r ∗ na_inv_P P π r x) ∗

        ( l ◁ₗ[π, Owned false] #r @ (◁ ty) ∗ P.(na_inv_P) π r x ={E}=∗
            q.[κ] ∗ na_own π F ).
    (* TODO: Closing view-shift here. *)
    Proof.
      iIntros (???) "#LFT Hna Hcred Hq #Hb".
      iEval (rewrite ltype_own_ofty_unfold /lty_of_ty_own) in "Hb".
      iDestruct "Hb" as (ly Halg Hly) "(Hsc & Hlb & %v & -> & #Hb)".

      iMod (fupd_mask_mono with "Hb") as "#Hb'"; first done; iClear "Hb".
      iEval (unfold ty_shr, na_ex_plain_t) in "Hb'".
      iDestruct "Hb'" as "(Hscr & Hbor & %ly' & %Hly' & %Halg')".

      iMod (na_bor_acc with "LFT Hbor Hq Hna") as "((%r & Hl & HP) & Hna & Hvs)"; [ solve_ndisj.. |].
      iMod (lc_fupd_elim_later with "Hcred HP") as "HP".

      iModIntro; iExists r; iFrame.

      iSplitL "Hl".
      { rewrite ltype_own_ofty_unfold /lty_of_ty_own.
        iExists ly => /=.
        iFrame (Halg Hly) "Hlb Hscr"; iR.
        iExists r; iR.
        by iModIntro. }

      iR; iIntros "(Hl & HP)".
      iEval (rewrite ltype_own_ofty_unfold /lty_of_ty_own) in "Hl".
      iDestruct "Hl" as (???) "(_ & _ & _ & (%r' & -> & Hl)) /=".
      iMod (fupd_mask_mono with "Hl") as "Hl"; first solve_ndisj.

      iApply ("Hvs" with "[Hl HP] Hna").
      iExists r'; iFrame.
    Qed.

    Lemma na_typed_place_ex_plain_t_shared_2 π E L l (ty : type rt) x κ bmin K T :
      prove_with_subtype E L false ProveDirect (£ 1) (λ L1 _ R, R -∗
        li_tactic (lctx_lft_alive_count_goal E L1 κ) (λ '(κs, L2),
          ∀ r, introduce_with_hooks E L2
            (P.(na_inv_P) π r x ∗
             l ◁ₗ[π, Owned false] (#r) @
               (OpenedLtype (◁ ty) (◁ ty) (◁ (∃na; P, ty))
                  (λ rfn x', ⌜x = x'⌝ ∗ P.(na_inv_P) π rfn x)
                  (λ rfn x', ⌜x = x'⌝ ∗ na_own π (↑shrN.@l) ∗ llft_elt_toks κs)))
            (λ L3,
              typed_place π E L3 l
                (ShadowedLtype (AliasLtype _ (ty_syn_type ty) l) #tt (◁ (∃na; P, ty)))
                (#x) (bmin (* intersect Shared *)) (Shared κ) K
                (λ L4 κs li b2 bmin' rti ltyi ri strong weak,
                  T L4 κs li b2 bmin' rti ltyi ri strong None))))
      ⊢ typed_place π E L l (◁ (∃na; P, ty))%I (#x) bmin (Shared κ) K T.
    Proof.
      (* TODO: Check if Hbor is still used. *)

      rewrite /prove_with_subtype.
      iIntros "HT".

      rewrite /typed_place /introduce_with_hooks.
      iIntros (Φ ???) "#(LFT & TIME & LLCTX) #HE HL Hna Hincl Hl Hcont".

      iApply fupd_place_to_wp.

      iMod ("HT" with "[] [] [$LFT $TIME $LLCTX] HE HL")
          as "(% & % & % & >(Hcred & HR) & HL & HT)"; [ done.. |].
      iSpecialize ("HT" with "HR").

      rewrite /li_tactic /lctx_lft_alive_count_goal.
      iDestruct "HT" as (???) "HT".

      iMod (lctx_lft_alive_count_tok with "HE HL") as (q) "(Htok & Htokcl & HL)"; [ done.. |].
      iMod (na_ex_plain_t_open_shared with "LFT Hna Hcred Htok Hl") as (r) "(HP & Hl & #Hbor & Hvs)"; [ done.. |].

      iEval (rewrite ltype_own_ofty_unfold /lty_of_ty_own) in "Hl".
      iDestruct "Hl" as (ly) "(>%Halg & >%Hly & >#Hsc & >#Hlb & _ & (% & >%Heq & Hl))".

      iMod ("HT" with "[] HE HL [$HP Hl]") as "HT"; first done.
      { rewrite ltype_own_opened_unfold /opened_ltype_own.
        iExists ly; repeat iR.

        rewrite ltype_own_ofty_unfold /lty_of_ty_own.
        iSplitL "Hl".
        { iExists ly; repeat iR.
          iExists r; iR.
          admit. (* TODO: Get rid of the later modality *) }

        rewrite /logical_step.
        iExists 0%nat.
        iSplitR.
        { iApply additive_time_receipt_0. }

        iIntros "!> _ _ !> % % % HP".
        iSplitR.
        { admit. }

        iIntros "Hκs Hl".
        iMod ("HP" with "Hκs") as "(-> & HP)".
        rewrite ltype_own_core_equiv.
        simp_ltypes.

        admit. }

      iDestruct "HT" as (?) "(HL & HT)".

      iApply ("HT" with "[//] [//] [$LFT $TIME $LLCTX] HE HL [] Hincl [Htokcl Hvs]").
      { admit. (* TODO: na_token *) }
      { rewrite ltype_own_shadowed_unfold /shadowed_ltype_own.

        iR; iSplitR.
        { rewrite ltype_own_alias_unfold /alias_lty_own.
          admit. (* TODO: Contradiction *) }

        admit. }

      iModIntro.
      iIntros (? ? ? ? ? ? ? ? strong ?) "Hincl Hl [ Hstrong _ ]".
      iApply ("Hcont" with "Hincl Hl").
      destruct strong; iSplit; [| done.. ].
      by simp_ltypes.
    Admitted.

    (* alias_lty_own: Add Shared from Owned without maybe_cred *)
    Lemma typed_place_alias_shared π E L l l2 rt''' (r : place_rfn rt''') st bmin0 κ P''' T :
      find_in_context (FindLoc l2 π) (λ '(existT rt2 (lt2, r2, b2)),
        typed_place π E L l2 lt2 r2 b2 b2 P''' (λ L' κs li b3 bmin rti ltyi ri strong weak,
          T L' κs li b3 bmin rti ltyi ri
            (fmap (λ strong, mk_strong (λ _, _) (λ _ _ _, AliasLtype rt''' st l2) (λ _ _, r)
              (* give back ownership through R *)
              (λ rti2 ltyi2 ri2, l2 ◁ₗ[π, b2] strong.(strong_rfn) _ ri2 @ strong.(strong_lt) _ ltyi2 ri2 ∗ strong.(strong_R) _ ltyi2 ri2)) strong)
            (fmap (λ weak, mk_weak (λ _ _, AliasLtype rt''' st l2) (λ _, r)
              (λ ltyi2 ri2, l2 ◁ₗ[π, b2] weak.(weak_rfn) ri2 @ weak.(weak_lt) ltyi2 ri2 ∗ weak.(weak_R) ltyi2 ri2)) weak)
            ))
      ⊢ typed_place π E L l (AliasLtype rt''' st l2) r bmin0 (Shared κ) P''' T.
    Proof.
    Admitted.

  End na_subtype.

  (* === ^ TYPING RULES ^ === *)

  (* NOTE: Is stratisfy only appear after read/write? *)
  (* > I was not able to reach it. *)

  Section proof.
    Context `{!typeGS Σ}.

    Lemma UnsafeCell_new_proof (π : thread_id) :
      UnsafeCell_new_lemma π.
    Proof.
      UnsafeCell_new_prelude.

      rep <- 1 liRStep; liShow.

      iApply na_owned_subtype_ex_plain_t.
      liSimpl; liShow.

      repeat liRStep; liShow.

      all: print_remaining_goal.
      Unshelve. all: sidecond_solver.
      Unshelve. all: sidecond_hammer.
      Unshelve. all: print_remaining_sidecond.
    Qed.

    Lemma UnsafeCell_into_inner_proof (π : thread_id) :
      UnsafeCell_into_inner_lemma π.
    Proof.
      UnsafeCell_into_inner_prelude.

      repeat liRStep; liShow.

      iApply na_typed_place_ex_plain_t_owned.
      liSimpl; liShow.

      repeat liRStep; liShow.

      all: print_remaining_goal.
      Unshelve. all: sidecond_solver.
      Unshelve. all: sidecond_hammer.
      Unshelve. all: print_remaining_sidecond.
    Qed.

    Lemma Cell_new_proof (π : thread_id) :
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

      (* NOTE: The QED takes a lot of time *)
    Admitted.

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
    Admitted.

    Lemma UnsafeCell_get_old_proof (π : thread_id) :
      UnsafeCell_get_old_lemma π.
    Proof.
      UnsafeCell_get_old_prelude.

      repeat liRStep; liShow.

      unfold Cell_inv_t; simpl.

      unfold bor_kind_min.
      iApply na_typed_place_ex_plain_t_shared_2.
      liSimpl; liShow.

      repeat liRStep; liShow.

      iApply typed_place_alias_shared.
      liSimpl; liShow.

      repeat liRStep; liShow.

      (* Unshelve. all: sidecond_solver. *)
      (* Unshelve. all: sidecond_hammer. *)
      (* Unshelve. all: print_remaining_sidecond. *)
    Admitted.
  End proof.

End generated_code.
