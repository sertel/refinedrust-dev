(* NOTE: This file is expected to be deleted when the `rr_frontend` will be done. *)

From refinedrust Require Import automation.
From refinedrust Require Import existentials_na.
From refinedrust Require Import typing.

Section UnsafeCell_sls.
  Context `{!typeGS Σ}.

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

Section proof.
  Context `{!typeGS Σ}.

  Lemma UnsafeCell_new_proof (π : thread_id) :
    UnsafeCell_new_lemma π.
  Proof.
    UnsafeCell_new_prelude.

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

    all: print_remaining_goal.
    Unshelve. all: sidecond_solver.
    Unshelve. all: sidecond_hammer.
    Unshelve. all: print_remaining_sidecond.
  Qed.

  Lemma Cell_new_proof (π : thread_id) :
    Cell_new_lemma π.
  Proof.
    Cell_new_prelude.

    repeat liRStep; liShow.

    all: print_remaining_goal.
    Unshelve. all: sidecond_solver.
    Unshelve. all: sidecond_hammer.
    Unshelve. all: print_remaining_sidecond.
    (* TODO: The QED takes a lot of time *)
  Admitted.

  Lemma UnsafeCell_get_old_proof (π : thread_id) :
    UnsafeCell_get_old_lemma π.
  Proof.
    UnsafeCell_get_old_prelude.

    do 312 liRStep; liShow.

    (* TODO: This instance isn't properly found *)
    iApply stratify_ltype_shadowed_shared.

    repeat liRStep; liShow.

    Unshelve. all: sidecond_solver.
    Unshelve. all: sidecond_hammer.
    Unshelve. all: print_remaining_sidecond.
  Qed.
End proof.
