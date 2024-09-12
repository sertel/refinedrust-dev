From refinedrust Require Import functions int alias_ptr products automation references.

Module test.
Definition bla0 `{typeGS Σ} :=
  (fn(∀ ( *[κ'; κ]) : 2 | ( *[]) : [] | (x) : unit, (λ f, [(κ', κ)]); (λ π, True)) → ∃ y : Z, () @ (uninit PtrSynType) ; λ π, ⌜ (4 > y)%Z⌝).
Definition bla1 `{typeGS Σ} :=
  (fn(∀ ( *[]) : 0 | ( *[]) : [] | x : unit, (λ _, []); (() :@: (uninit PtrSynType)) ; (λ π, True)) → ∃ y : Z, () @ (uninit PtrSynType) ; (λ π, ⌜ (4 > y)%Z⌝)).
Definition bla2 `{typeGS Σ} :=
  (fn(∀ ( *[]) : 0 | ( *[]) : [] | x : unit, (λ _, []); () :@: (uninit PtrSynType), () :@: (uninit PtrSynType) ; (λ π, True)) → ∃ y : Z, () @ (uninit PtrSynType) ; (λ π, ⌜ (4 > y)%Z⌝)).
Definition bla3 `{typeGS Σ} T_st T_rt :=
  (fn(∀ ( *[]) : 0 | ( *[ T_ty]) : [ (T_rt, T_st) ] | (x) : T_rt, (λ _, []); x :@: T_ty, () :@: (uninit PtrSynType) ; (λ π, True)) → ∃ y : Z, () @ (uninit PtrSynType) ; (λ π, ⌜ (4 > y)%Z⌝)).

(** Testing type parameter instantiation *)
Definition ptr_write `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [("dst", void* ); ("src", use_layout_alg' T_st)];
  f_local_vars := [];
  f_code :=
    <["_bb0" :=
      !{PtrOp} "dst" <-{use_op_alg' T_st} use{use_op_alg' T_st} "src";
      return zst_val
    ]>%E $
    ∅;
  f_init := "_bb0";
|}.

(* Maybe this should also be specced in terms of value? *)
Definition type_of_ptr_write `{!typeGS Σ} (T_rt : Type) (T_st : syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : [(T_rt, T_st)] | (l, r) : (loc * T_rt), (λ ϝ, []);
      l :@: alias_ptr_t, r :@: T_ty; λ π, (l ◁ₗ[π, Owned false] .@ (◁ uninit (T_ty.(ty_syn_type)))))
    → ∃ () : unit, () @ unit_t; λ π,
        l ◁ₗ[π, Owned false] PlaceIn r @ ◁ T_ty.

Lemma ptr_write_typed `{!typeGS Σ} π T_rt T_st T_ly :
  syn_type_has_layout T_st T_ly →
  ⊢ typed_function π (ptr_write T_st) [] (<tag_type> type_of_ptr_write T_rt T_st).
Proof.
  start_function "ptr_write" ( [] ) ( [T_ty []] ) ( [l r] ).
  intros ls_dst ls_src.
  repeat liRStep; liShow.
  Unshelve. all: unshelve_sidecond; sidecond_hook.
  Unshelve. all: unfold_common_defs; try solve_goal.
Qed.

(** If we specialize the type to [int i32], the proof should still work. *)
Definition type_of_ptr_write_int `{!typeGS Σ} :=
  spec_instantiate_typaram [_] 0 eq_refl (int i32) (type_of_ptr_write Z (IntSynType i32)).
Lemma ptr_write_typed_int `{!typeGS Σ} π :
  ⊢ typed_function π (ptr_write (IntSynType i32)) [] (<tag_type> type_of_ptr_write_int).
Proof.
  start_function "ptr_write" ( [] ) ( [] ) ( [l r] ).
  intros ls_dst ls_src.
  repeat liRStep; liShow.
  Unshelve. all: unshelve_sidecond; sidecond_hook.
  Unshelve. all: unfold_common_defs; try solve_goal.
Qed.

(** Same for shared references *)
Definition type_of_ptr_write_shrref `{!typeGS Σ} (U_rt : Type) (U_st : syn_type) :=
  (* First add a new type parameter and a new lifetime *)
  fnspec! ( *[κ]) : 1 | ( *[U_ty]) : [(U_rt, U_st)],
    (* Then instantiate the existing type parameter with shr_ref U_ty κ *)
    (type_of_ptr_write (place_rfn U_rt) (PtrSynType) <TY>@{0} shr_ref U_ty κ) <MERGE!>.

Lemma ptr_write_typed_shrref `{!typeGS Σ} π U_rt U_st :
  ⊢ typed_function π (ptr_write (PtrSynType)) [] (<tag_type> type_of_ptr_write_shrref U_rt U_st).
Proof.
  start_function "ptr_write" ( [ulft_a []]  ) ( [U_ty []] ) ( [l r] ).
  intros ls_dst ls_src.
  repeat liRStep; liShow.
  Unshelve. all: unshelve_sidecond; sidecond_hook.
  Unshelve. all: unfold_common_defs; try solve_goal.
Qed.
End test.
