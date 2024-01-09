From refinedrust Require Export type.
From refinedrust Require Import alias_ptr existentials.
From refinedrust Require Import int programs program_rules functions uninit references products automation.
From refinedrust Require Import enum.
Set Default Proof Using "Type".

(** * Test cases for sidecondition solvers declared in [automation/solvers.v] *)

(** compute_map_lookup *)
Section test.
  Context `{!typeGS Σ}.

  Lemma test_compute_map_lookup_1 (M : gmap string lft) (κ : lft) :
    M = <[ "lft1" := κ]> $ ∅ →
    M !! "lft1" = Some κ.
  Proof.
    intros ->.
    solve_compute_map_lookup; solve[fail].
  Abort.

  Lemma test_compute_map_lookup_1 (M : gmap string lft) (κ : lft) :
    M = (named_lft_update "lft1" κ) ∅ →
    M !! "lft1" = Some κ.
  Proof.
    intros ->.
    solve_compute_map_lookup; solve[fail].
  Abort.

  Lemma test_compute_map_lookup_2 (M : gmap string lft) (κ : lft) :
    M = <[ "lft1" := κ]> $ ∅ →
    ∃ κ', M !! "lft1" = Some κ'.
  Proof.
    intros ->. eexists _.
    solve_compute_map_lookup; solve[fail].
  Abort.

  Lemma test_compute_map_lookup_3 M (κ : lft) :
    M = <[ "lft1" := κ]> $ ∅ →
    ⊢@{iPropI Σ} li_tactic (compute_map_lookup_goal M "lft1") (λ v,
      ⌜v = Some κ⌝ ∗ True).
  Proof.
    intros ->.
    iStartProof. unshelve (repeat liRStep); solve[fail].
  Abort.

  Lemma test_compute_map_lookup_3 M (κ : lft) :
    M = named_lft_update "lft1" κ ∅ →
    ⊢@{iPropI Σ} li_tactic (compute_map_lookup_goal M "lft1") (λ v,
      ⌜v = Some κ⌝ ∗ True).
  Proof.
    intros ->.
    iStartProof. unshelve (repeat liRStep); solve[fail].
  Abort.

  Lemma test_compute_map_lookup_4 M (κ κ' : lft) :
    M = <["lft2" := κ']> $ <[ "lft1" := κ]> $ ∅ →
    ⊢@{iPropI Σ} li_tactic (compute_map_lookup_nofail_goal M "lft1") (λ v,
      ⌜v = κ⌝ ∗ True).
  Proof.
    liRStep.
    iStartProof. unshelve (repeat liRStep); solve[fail].
  Abort.

  Lemma test_compute_map_lookup_5 M (κ : lft) :
    M = <[ "lft1" := κ]> $ ∅ →
    ⊢@{iPropI Σ} li_tactic (compute_map_lookup_goal M "lft2") (λ v,
      ⌜v = None⌝ ∗ True).
  Proof.
    liRStep.
    iStartProof. unshelve (repeat liRStep); solve[fail].
  Abort.

  Lemma test (M : gmap string lft) (κ1 κ2 : lft) :
    M = (<["κ1" := κ1]> $ <["κ2" := κ2]> $ ∅) →
    ∃ ls, Forall2 (λ k v, M !! k = Some v) ["κ1"; "κ2"] ls ∧ ls = [κ1; κ2].
  Proof.
    intros ->. eexists. split; first compute_map_lookups. done.
  Abort.

  Lemma test κ ulft__ :
    ⊢@{iPropI Σ} li_tactic (compute_map_lookup_goal (named_lft_update "plft17" κ (named_lft_update "plft12" κ (named_lft_update "llft6" κ (named_lft_update "plft11" ulft__ (named_lft_update "ulft__" ulft__ ∅))))) "llft6") (λ v,
      ⌜v = Some κ⌝ ∗ True).
  Proof.
    iStartProof.
    unshelve (repeat liRStep); solve[fail].
  Abort.
End test.

(** simplify_gmap *)
Section test.
  Context `{!typeGS Σ}.

  Lemma test_simplify_gmap_1 (M : gmap string lft) (κ : lft) :
    M = <[ "lft1" := κ]> $ ∅ →
    ∃ M', M' = delete "lft1" M.
  Proof.
    intros ->.
    eexists _.
    unshelve solve_simplify_gmap; solve[fail].
  Qed.

  Lemma test_simplify_lft_map_1 (M : gmap string lft) (κ : lft) :
    M = named_lft_update "lft1" κ $ ∅ →
    ∃ M', opaque_eq M' (named_lft_delete "lft1" M).
  Proof.
    intros ->.
    eexists _.
    unshelve solve_simplify_lft_map; solve[fail].
  Qed.

  Lemma test_simplify_gmap_2 (M : gmap string lft) (κ κ' : lft) :
    M = <["lft2" := κ']> $ <[ "lft1" := κ]> $ ∅ →
    ∃ M', delete "lft1" M = M'.
  Proof.
    intros ->.
    eexists _.
    unshelve solve_simplify_gmap; solve[fail].
  Qed.

  Lemma test_simplify_gmap_3 M (κ κ' : lft) :
    M = <["lft2" := κ']> $ <[ "lft1" := κ]> $ ∅ →
    ⊢@{iPropI Σ} li_tactic (simplify_gmap_goal M) (λ M',
      ⌜M' = M⌝ ∗ True).
  Proof.
    liRStep.
    iStartProof. unshelve (repeat liRStep); solve[fail].
  Qed.

  Lemma test_simplify_lft_map_3 M (κ κ' : lft) :
    M = (named_lft_update "lft2" κ' (named_lft_update "lft1" κ ∅)) →
    ⊢@{iPropI Σ} li_tactic (simplify_lft_map_goal M) (λ M',
      ⌜M' = M⌝ ∗ True).
  Proof.
    liRStep.
    iStartProof. unshelve (repeat liRStep); solve[fail].
  Qed.

  Lemma test_simplify_gmap_4 M (κ κ' : lft) :
    M = <["lft2" := κ']> $ <[ "lft1" := κ]> $ ∅ →
    ⊢@{iPropI Σ} li_tactic (simplify_gmap_goal (delete "lft1" M)) (λ M',
      ⌜M' = <["lft2" := κ']> $ ∅⌝ ∗ True).
  Proof.
    liRStep.
    iStartProof. unshelve (repeat liRStep); solve[fail].
  Qed.

  (* for overwriting, we should first explicitly delete the old entry *)
  Lemma test_simplify_gmap_5 M (κ κ' : lft) :
    M = <["lft2" := κ']> $ <[ "lft1" := κ]> $ ∅ →
    ⊢@{iPropI Σ} li_tactic (simplify_gmap_goal (<["lft1" := κ']> $ delete "lft1" M)) (λ M',
      ⌜M' = <["lft1" := κ']> $ <["lft2" := κ']> $ ∅⌝ ∗ True).
  Proof.
    liRStep.
    iStartProof. unshelve (repeat liRStep); solve[fail].
  Qed.

  Lemma test_simplify_gmap_6 M (κ κ' : lft) :
    M = <["lft2" := κ']> $ <[ "lft1" := κ]> $ ∅ →
    ⊢@{iPropI Σ} li_tactic (simplify_gmap_goal (delete "lft3" M)) (λ M',
      ⌜M' = <["lft2" := κ']> $ <["lft1" := κ]> $  ∅⌝ ∗ True).
  Proof.
    liRStep.
    iStartProof. unshelve (repeat liRStep); solve[fail].
  Qed.

  Lemma test_simplify_gmap_7 (ulft__ : lft) :
    ⊢@{iPropI Σ} li_tactic (simplify_gmap_goal (<["plft4":=ulft__]> (delete "plft4" (<["ulft__":=ulft__]> ∅)))) (λ M',
      ⌜M' = <["plft4":=ulft__]> (<["ulft__":=ulft__]> ∅)⌝ ∗ True).
  Proof.
    iStartProof. unshelve (repeat liRStep); solve[fail].
  Qed.

  Lemma test_simplify_lft_names1 ulft__ κ :
    ⊢@{iPropI Σ} li_tactic (simplify_lft_map_goal (named_lft_update "plft17" κ (named_lft_delete "plft17" (named_lft_update "plft12" κ (named_lft_update "llft6" κ (named_lft_update "plft11" ulft__ ((named_lft_update "ulft__" ulft__ ∅))))))))
    (λ M',
      ⌜M' = (named_lft_update "plft17" κ ((named_lft_update "plft12" κ (named_lft_update "llft6" κ (named_lft_update "plft11" ulft__ ((named_lft_update "ulft__" ulft__ ∅)))))))⌝ ∗ True).
  Proof.
    iStartProof. unshelve (repeat liRStep); solve[fail].
  Qed.
End test.

(** inv_layout_alg *)
Section test.
  Context `{!typeGS Σ}.
  Context (T_st : syn_type).

  (** Struct tests *)
  Definition s1_spec :=
    mk_sls "s1_T" [("s1_f1", T_st); ("s1_f2", IntSynType i32)] StructReprRust.
  Definition s2_spec :=
    mk_sls "s2_T" [("s2_f1", PtrSynType); ("s2_f2", s1_spec : syn_type)] StructReprRust.

  Lemma inv_test' s2_ly :
    use_struct_layout_alg s2_spec = Some s2_ly →
    ∃ s2_sl : struct_layout, s2_ly = s2_sl ∧
    ∃ s1_sl : struct_layout,
    ∃ T_ly, syn_type_has_layout T_st T_ly ∧
      sl_has_members s1_sl [("s1_f1", T_ly); ("s1_f2", (it_layout i32))] ∧
      sl_has_members s2_sl [("s2_f1", void*); ("s2_f2", (layout_of s1_sl))].
  Proof.
    intros Hly.
    inv_layout_alg.
    eauto 10; solve[fail].
  Abort.

  Lemma inv_test s2_ly :
    use_layout_alg s2_spec = Some s2_ly →
    ∃ s2_sl : struct_layout, s2_ly = layout_of s2_sl ∧
    ∃ s1_sl : struct_layout,
    ∃ T_ly, syn_type_has_layout T_st T_ly ∧
      sl_has_members s1_sl [("s1_f1", T_ly); ("s1_f2", (it_layout i32))] ∧
      sl_has_members s2_sl [("s2_f1", void*); ("s2_f2", (layout_of s1_sl))].
  Proof.
    intros Hly.
    inv_layout_alg.
    eauto 10; solve[fail].
  Abort.

  Lemma inv_test3 :
    syn_type_is_layoutable (s2_spec) →
    ∃ s2_sl : struct_layout,
    ∃ s1_sl : struct_layout,
    ∃ T_ly, syn_type_has_layout T_st T_ly ∧
      sl_has_members s1_sl [("s1_f1", T_ly); ("s1_f2", (it_layout i32))] ∧
      sl_has_members s2_sl [("s2_f1", void*); ("s2_f2", (layout_of s1_sl))].
  Proof.
    intros Hly. inv_layout_alg.
    eauto 10; solve[fail].
  Abort.

  Lemma inv_test4 len :
    syn_type_is_layoutable (ArraySynType T_st len) →
    syn_type_is_layoutable T_st.
  Proof.
    intros Hly. inv_layout_alg.
    solve_layout_alg; solve[fail].
  Abort.

  Lemma inv_test5 {rt} (T_ty : type rt) (xs : list nat) ly :
    T_st = ty_syn_type T_ty →
    use_layout_alg (ArraySynType (ty_syn_type T_ty) (length xs)) = Some ly →
    syn_type_is_layoutable (T_st).
  Proof.
    intros -> H1. inv_layout_alg.
    solve_layout_alg; solve[fail].
  Abort.

  (** Union tests *)
  Definition u1_spec :=
    mk_uls "u1_T" [("u1_v1", T_st); ("u1_v2", IntSynType i32)] UnionReprRust.
  Definition u2_spec :=
    mk_uls "u2_T" [("u2_v1", PtrSynType); ("u2_v2", u1_spec : syn_type)] UnionReprRust.

  Lemma inv_test' u2_ly :
    use_union_layout_alg u2_spec = Some u2_ly →
    ∃ u2_ul : union_layout, u2_ly = u2_ul ∧
    ∃ u1_ul : union_layout,
    ∃ T_ly, syn_type_has_layout T_st T_ly ∧
      ul_has_variants u1_ul [("u1_v1", T_ly); ("u1_v2", (it_layout i32))] ∧
      ul_has_variants u2_ul [("u2_v1", void*); ("u2_v2", (ul_layout u1_ul))].
  Proof.
    intros Hly.
    inv_layout_alg.
    eauto 10; solve[fail].
  Abort.

  Lemma inv_test u2_ly :
    use_layout_alg u2_spec = Some u2_ly →
    ∃ u2_ul : union_layout, u2_ly = ul_layout u2_ul ∧
    ∃ u1_ul : union_layout,
    ∃ T_ly, syn_type_has_layout T_st T_ly ∧
      ul_has_variants u1_ul [("u1_v1", T_ly); ("u1_v2", (it_layout i32))] ∧
      ul_has_variants u2_ul [("u2_v1", void*); ("u2_v2", (ul_layout u1_ul))].
  Proof.
    intros Hly.
    inv_layout_alg.
    eauto 10; solve[fail].
  Abort.

  Lemma inv_test3 :
    syn_type_is_layoutable (u2_spec) →
    ∃ u2_ul : union_layout,
    ∃ u1_ul : union_layout,
    ∃ T_ly, syn_type_has_layout T_st T_ly ∧
      ul_has_variants u1_ul [("u1_v1", T_ly); ("u1_v2", (it_layout i32))] ∧
      ul_has_variants u2_ul [("u2_v1", void*); ("u2_v2", (ul_layout u1_ul))].
  Proof.
    intros Hly. inv_layout_alg.
    eauto 10; solve[fail].
  Abort.

  (** Enums *)
  Definition std_option_Option_None_sls  : struct_layout_spec := mk_sls "std_option_Option_None" [] StructReprRust.
  Definition std_option_Option_Some_sls : struct_layout_spec := mk_sls "std_option_Option_Some" [
    ("0", T_st)] StructReprRust.
  Program Definition std_option_Option_els : enum_layout_spec := mk_els "std_option_Option" ISize [
    ("None", std_option_Option_None_sls  : syn_type);
    ("Some", std_option_Option_Some_sls : syn_type)] EnumReprRust [("None", 0); ("Some", 1)] _ _ _ _.
  Next Obligation. repeat first [econstructor | set_solver]. Qed.
  Next Obligation. done. Qed.
  Next Obligation. repeat first [econstructor | set_solver]. Qed.
  Next Obligation. repeat first [econstructor | init_cache; solve_goal]. Qed.

  Lemma inv_test e_ly :
    use_enum_layout_alg std_option_Option_els = Some e_ly →
    enum_layout_spec_is_layoutable std_option_Option_els.
  Proof.
    intros.
    inv_layout_alg.
    solve_layout_alg; solve[fail].
  Abort.

  (** Untyped *)
  Lemma inv_test2 ily :
    use_layout_alg (UntypedSynType (it_layout i32)) = Some ily →
    ily = it_layout i32.
  Proof.
    intros Hly. inv_layout_alg. reflexivity.
  Abort.

  (* Regression test: this should not diverge, ensured by the [DONT_ENRICH] markers we place in simplification *)
  Lemma inv_test3 U_st :
    syn_type_is_layoutable T_st →
    syn_type_is_layoutable U_st →
    True.
  Proof.
    intros.
    timeout 4 (intros; inv_layout_alg).
  Abort.

  (* Regression test: having the same assumption twice should not break anything. *)
  Lemma inv_test5 T_ly1 T_ly2 :
    syn_type_has_layout T_st T_ly1 →
    syn_type_has_layout T_st T_ly2 →
    T_ly1 = T_ly2.
  Proof.
    intros ??.
    inv_layout_alg.
    reflexivity.
  Abort.
  Lemma inv_test4 :
    syn_type_is_layoutable (s2_spec) →
    syn_type_is_layoutable (s1_spec) →
    ∃ s2_sl : struct_layout,
    ∃ s1_sl : struct_layout,
    ∃ T_ly, syn_type_has_layout T_st T_ly ∧
      sl_has_members s1_sl [("s1_f1", T_ly); ("s1_f2", (it_layout i32))] ∧
      sl_has_members s2_sl [("s2_f1", void*); ("s2_f2", (layout_of s1_sl))].
  Proof.
    intros ? ?.
    inv_layout_alg.
    eauto 10; solve[fail].
  Abort.
  Lemma inv_test4' :
    syn_type_is_layoutable (s1_spec) →
    syn_type_is_layoutable (s2_spec) →
    ∃ s2_sl : struct_layout,
    ∃ s1_sl : struct_layout,
    ∃ T_ly, syn_type_has_layout T_st T_ly ∧
      sl_has_members s1_sl [("s1_f1", T_ly); ("s1_f2", (it_layout i32))] ∧
      sl_has_members s2_sl [("s2_f1", void*); ("s2_f2", (layout_of s1_sl))].
  Proof.
    intros ? ?.
    inv_layout_alg.
    eauto 10; solve[fail].
  Abort.

  Lemma inv_test_name_collision {T_rt} (T_ty : type T_rt) U_st {U_rt} (U_ty : type U_rt) :
    syn_type_is_layoutable T_st →
    syn_type_is_layoutable (ty_syn_type T_ty) →
    syn_type_is_layoutable U_st →
    syn_type_is_layoutable (ty_syn_type U_ty) →
    ty_syn_type T_ty = T_st →
    ty_syn_type U_ty = U_st →
    True.
  Proof.
    (* Regression test: This should not diverge. *)
    intros []. inv_layout_alg.
    intros []. inv_layout_alg.
    intros []. inv_layout_alg.
    intros []. inv_layout_alg.
  Abort.

End test.

Section test.
  Lemma inv_test `{!typeGS Σ} {rt} (T : type rt) s2_ly :
    use_layout_alg (s2_spec (ty_syn_type T)) = Some s2_ly →
    use_layout_alg (s2_spec (ty_syn_type T)) = Some s2_ly →
    ∃ s2_sl : struct_layout, s2_ly = layout_of s2_sl ∧
    ∃ s1_sl : struct_layout,
    ∃ T_ly, syn_type_has_layout (ty_syn_type T) T_ly ∧
      sl_has_members s1_sl [("s1_f1", T_ly); ("s1_f2", (it_layout i32))] ∧
      sl_has_members s2_sl [("s2_f1", void*); ("s2_f2", (layout_of s1_sl))].
  Proof.
    intros Hly.
    inv_layout_alg.
    intros Ha.
    inv_layout_alg.
    eauto 10; solve[fail].
  Abort.
End test.

(** layout solver *)
Section test.
  Context `{!typeGS Σ}.
  Context (T_st : syn_type).

  Lemma solve_layout_size_test1 T_ly :
    use_layout_alg T_st = Some T_ly →
    ly_size T_ly * 42 ≤ ly_size (mk_array_layout T_ly 42).
  Proof.
    intros. solve_layout_size; solve[fail].
  Abort.

  Lemma solve_layout_size_test2 T_ly :
    use_layout_alg T_st = Some T_ly →
    (size_of_st T_st * 43 ≤ MaxInt isize_t)%Z →
    ly_size (use_layout_alg' (ArraySynType T_st 42)) ≤ ly_size (use_layout_alg' (ArraySynType T_st 43)).
  Proof.
    intros. solve_layout_size; solve[fail].
  Abort.

  Lemma solve_layout_size_test3 T_ly :
    use_layout_alg T_st = Some T_ly →
    size_of_st (UntypedSynType (use_layout_alg' T_st)) = ly_size T_ly.
  Proof.
    intros. solve_layout_size; solve [fail].
  Abort.

  Lemma solve_layout_size_test4 T_ly :
    use_layout_alg T_st = Some T_ly →
    (size_of_st T_st * 43 ≤ MaxInt isize_t)%Z →
    size_of_st T_st > 0 →
    ly_size (use_layout_alg' (ArraySynType T_st 42)) < ly_size (use_layout_alg' (ArraySynType T_st 43)).
  Proof.
    intros. solve_layout_size; solve[fail].
  Abort.

  Lemma solve_layout_alg_test1 :
    use_layout_alg (IntSynType u16) = Some (it_layout u16).
  Proof.
    solve_layout_alg; solve [fail].
  Abort.

  Lemma solve_layout_alg_test1 s2_ly :
    use_layout_alg (s2_spec T_st) = Some s2_ly →
    syn_type_has_layout (s2_spec T_st) s2_ly.
  Proof.
    intros. inv_layout_alg.
    solve_layout_alg; solve [fail].
  Abort.

  Lemma solve_layout_alg_test2 T_ly :
    use_layout_alg T_st = Some T_ly →
    (ly_size T_ly * 42 ≤ MaxInt isize_t)%Z →
    syn_type_has_layout (ArraySynType T_st 42) (mk_array_layout T_ly 42).
  Proof.
    intros. solve_layout_alg; solve [fail].
  Abort.

  Lemma solve_layout_alg_test2' T_ly size :
    use_layout_alg T_st = Some T_ly →
    (ly_size T_ly * Z.to_nat size ≤ MaxInt isize_t)%Z →
    ∃ ly, syn_type_has_layout (ArraySynType T_st (Z.to_nat size)) ly.
  Proof.
    intros. eexists.
    solve_layout_alg.
  Abort.

  Lemma solve_layout_alg_test3 T_ly :
    use_layout_alg T_st = Some T_ly →
    syn_type_has_layout (UntypedSynType (use_layout_alg' T_st)) T_ly.
  Proof.
    intros. solve_layout_alg; solve [fail].
  Abort.

  Lemma solve_layout_alg_test4 T_ly :
    use_layout_alg T_st = Some T_ly →
    ∃ ly, syn_type_has_layout (UntypedSynType (use_layout_alg' T_st)) ly.
  Proof.
    intros. eexists. solve_layout_alg; solve[fail].
  Abort.

  Lemma solve_layout_alg_test5 s2_ly :
    use_layout_alg (s2_spec T_st) = Some s2_ly →
    ∃ s2_sl, struct_layout_spec_has_layout (s2_spec T_st) s2_sl.
  Proof.
    intros. inv_layout_alg.
    eexists. solve_layout_alg; solve[fail].
  Abort.

  Lemma solve_layout_alg_test6 s2_ly :
    use_layout_alg (s2_spec T_st) = Some s2_ly →
    syn_type_has_layout (s2_spec T_st) (use_layout_alg' (s2_spec T_st)).
  Proof.
    intros. inv_layout_alg.
    solve_layout_alg; solve[fail].
  Abort.

  Lemma solve_layout_alg_test7 s2_ly :
    use_layout_alg (s2_spec T_st) = Some s2_ly →
    struct_layout_spec_has_layout (s2_spec T_st) (use_struct_layout_alg' (s2_spec T_st)).
  Proof.
    intros. inv_layout_alg.
    solve_layout_alg; solve[fail].
  Abort.

  Lemma solve_layout_alg_test8 {T_rt} (T_ty : type T_rt) T_ly :
    syn_type_has_layout (ty_syn_type T_ty) T_ly →
    syn_type_has_layout (ty_syn_type T_ty) (use_layout_alg' (ty_syn_type T_ty)).
  Proof.
    intros. inv_layout_alg.
    solve_layout_alg; solve[fail].
  Abort.

  Lemma solve_layout_alg_test9 s2_ly :
    use_layout_alg (s2_spec T_st) = Some s2_ly →
    syn_type_is_layoutable (UntypedSynType (use_layout_alg' (s2_spec T_st))).
  Proof.
    intros. inv_layout_alg.
    solve_layout_alg; solve [fail].
  Abort.

  Lemma solve_layout_alg_test10 ly :
    use_layout_alg (std_option_Option_els T_st) = Some ly →
    syn_type_is_layoutable (std_option_Option_els T_st).
  Proof.
    intros. inv_layout_alg.
    solve_layout_alg; solve[fail].
  Abort.

  Lemma solve_layout_alg_test11 ly ly' :
    use_layout_alg (std_option_Option_els T_st) = Some ly →
    use_layout_alg (std_option_Option_els (IntSynType u32)) = Some ly' →
    syn_type_is_layoutable (std_option_Option_els T_st) ∧ syn_type_is_layoutable (std_option_Option_els (IntSynType u32)).
  Proof.
    intros. inv_layout_alg.
    split; solve_layout_alg.
    Unshelve. all: solve[fail].
  Abort.
End test.

(** solve_op_alg *)
Section test.
  Context `{!typeGS Σ}.

  Lemma solve_op_alg_test1 :
    use_op_alg (IntSynType u16) = Some (IntOp $ u16).
  Proof.
    solve_op_alg; solve [fail].
  Abort.

  Lemma solve_op_alg_test1 T_st :
    syn_type_is_layoutable T_st →
    use_op_alg T_st = Some (use_op_alg' T_st).
  Proof.
    intros; inv_layout_alg.
    solve_op_alg; solve [fail].
  Abort.

  Lemma solve_op_alg_test1 T_st s2_sl s1_sl :
    use_struct_layout_alg (s2_spec T_st) = Some s2_sl →
    use_struct_layout_alg (s1_spec T_st) = Some s1_sl →
    use_op_alg (s2_spec T_st) = Some (StructOp s2_sl [PtrOp; StructOp s1_sl [use_op_alg' T_st; IntOp i32]]).
  Proof.
    intros. inv_layout_alg.
    solve_op_alg.
    Unshelve. all: solve_goal.
    all: solve [fail].
  Abort.

  Lemma solve_op_alg_test3 T_st T_ly :
    use_layout_alg T_st = Some T_ly →
    use_op_alg (UntypedSynType (use_layout_alg' T_st)) = Some $ UntypedOp T_ly.
  Proof.
    intros. solve_op_alg; solve [fail].
  Abort.

  Lemma solve_op_alg_test4 T_st T_ly :
    use_layout_alg T_st = Some T_ly →
    ∃ ot, use_op_alg (UntypedSynType (use_layout_alg' T_st)) = Some ot.
  Proof.
    intros. eexists. solve_op_alg; solve[fail].
  Abort.

  Lemma solve_op_alg_test5 {T_rt} (T_ty : type T_rt) T_ly :
    syn_type_has_layout (ty_syn_type T_ty) T_ly →
    use_op_alg (ty_syn_type T_ty) = Some (use_op_alg' (ty_syn_type T_ty)).
  Proof.
    intros. inv_layout_alg.
    solve_op_alg; solve[fail].
  Abort.

  Lemma solve_op_alg_test6  :
    use_op_alg' (IntSynType i32) = IntOp i32.
  Proof.
    intros. inv_layout_alg.
    solve_op_alg; solve[fail].
  Abort.

  Lemma solve_op_alg_test7 :
    use_op_alg CharSynType = Some CharOp.
  Proof.
    solve_op_alg; solve [fail].
  Abort.
End test.

(** ty_has_op_type *)
(* TODO: we should have some regression tests here *)

(** ty_allows_reads / ty_allows_writes *)
Section test.
  Context `{!typeGS Σ}.

  Lemma ty_allows_reads_int :
    ty_allows_reads (int i32).
  Proof.
    solve [unshelve solve_ty_allows; init_cache; solve_goal].
  Abort.
  Lemma ty_allows_reads_struct_1 :
    struct_layout_spec_is_layoutable (s1_spec (IntSynType i32)) →
    ty_allows_reads (struct_t (s1_spec (IntSynType i32)) +[int i32; int i32]).
  Proof.
    intros. inv_layout_alg.
    unshelve solve_ty_allows; solve_goal.
    all: solve [fail].
  Abort.

  Lemma ty_allows_reads_struct_2 {T_rt} (T_ty : type T_rt) :
    ty_allows_reads T_ty →
    struct_layout_spec_is_layoutable (s1_spec (ty_syn_type T_ty)) →
    syn_type_is_layoutable (ty_syn_type T_ty) →
    ty_allows_reads (struct_t (s1_spec (ty_syn_type T_ty)) +[T_ty; int i32]).
  Proof.
    intros. inv_layout_alg.
    solve_ty_allows.
    Unshelve.
    all: solve_goal.
    all: solve [fail].
  Abort.

  (* TODO more tests *)
End test.

(** solve_interpret_rust_type *)
Section test.
  Context `{!typeGS Σ}.

  Context (testX : ∀ `{!typeGS Σ} {rt} (ty : type rt), type rt).

  (* TODO: better error handling in the tactic above.
      Somehow the Ltac2 exceptions get gobbled up and just a no match error is raised... *)
  Lemma interpret_rust_type_test0 {rt} (T_ty : type rt) κ :
    ∃ ty, interpret_rust_type_pure_goal (<["κ" := κ]> ∅) (RSTLitType ["testX"] [RSTInt I32]) ty ∧ ty = testX _ _ (int i32).
  Proof.
    init_tyvars (<["T" := (existT _ T_ty)]> ∅).
    eexists _; split; [ solve_interpret_rust_type | ]. done.
  Abort.

  Lemma interpret_rust_type_test1 {rt} (T_ty : type rt) :
    ∃ rt2 (ty2 : type rt2), interpret_rust_type_pure_goal (∅) (RSTInt I32) ty2.
  Proof.
    init_tyvars (<["T" := (existT _ T_ty)]> ∅).
    eexists _, _. solve_interpret_rust_type; solve[fail].
  Abort.

  Lemma interpret_rust_type_test1 {rt} (T_ty : type rt) :
    interpret_rust_type_pure_goal (∅) (RSTTyVar "T") T_ty.
  Proof.
    init_tyvars (<["T" := (existT _ T_ty)]> ∅).
    solve_interpret_rust_type; solve[fail].
  Abort.

  Lemma interpret_rust_type_test2 {rt} (T_ty : type rt) :
    interpret_rust_type_pure_goal (∅) (RSTInt I32) (int i32).
  Proof.
    init_tyvars (<["T" := (existT _ T_ty)]> ∅).
    solve_interpret_rust_type; solve[fail].
  Abort.

  Lemma interpret_rust_type_test3 {rt} (T_ty : type rt) sls :
    interpret_rust_type_pure_goal (∅) (RSTStruct sls [RSTInt I32]) (struct_t sls +[int i32]).
  Proof.
    init_tyvars (<["T" := (existT _ T_ty)]> ∅).
    solve_interpret_rust_type; solve[fail].
  Abort.

  Lemma interpret_rust_type_test4 {rt} (T_ty : type rt) κ :
    ∃ ty, interpret_rust_type_pure_goal (<["κ" := κ]> ∅) (RSTRef Mut "κ" (RSTInt I32)) ty ∧ ty = (mut_ref (int i32) κ).
  Proof.
    init_tyvars (<["T" := (existT _ T_ty)]> ∅).
    eexists _; split; [solve_interpret_rust_type | ]. done.
  Abort.

  (*
  Import enum_test.
  Lemma bla {rt} (T_ty : type rt) ulft__ :
    ∃ ty, interpret_rust_type_pure_goal (named_lft_update "plft5" ulft__ (named_lft_update "ulft__" ulft__ ∅)) (RSTLitType ["std_option_Option_ty"] [RSTTyVar "T"]) ty ∧ ty = std_option_Option_ty T_ty.
  Proof.
    init_tyvars (<["T" := (existT _ T_ty)]> ∅).
    eexists _. split. { solve_interpret_rust_type. } done.
  Abort.
   *)
End test.

(** solve_lft_incl *)
Section test.
  Context `{typeGS Σ}.

  Lemma test1 E κ κ' κ'' c1 c2 :
    lctx_lft_incl E [κ ⊑ₗ{c1} [κ'; κ]; κ' ⊑ₗ{c2} [κ'']] (κ) (κ'').
  Proof.
    solve_lft_incl; solve[fail].
  Abort.

  Lemma test2 κ κ' :
    lctx_lft_incl [κ' ⊑ₑ κ'; κ ⊑ₑ κ'] [] κ κ'.
  Proof.
    solve_lft_incl; solve[fail].
  Abort.

  Lemma test2' {rt} (T : type rt) κ κ' :
    lctx_lft_incl (ty_wf_E T ++ [κ' ⊑ₑ κ'; κ ⊑ₑ κ']) [] κ κ'.
  Proof.
    solve_lft_incl; solve[fail].
  Abort.

  Lemma test3 E L κ :
    lctx_lft_incl E L κ κ.
  Proof.
    solve_lft_incl; solve[fail].
  Abort.

  Lemma test4 E κ κ' κ'' c2 :
    lctx_lft_incl E [κ ≡ₗ [κ'; κ]; κ' ⊑ₗ{c2} [κ'']] (κ) (κ'').
  Proof.
    solve_lft_incl; solve[fail].
  Abort.

  Lemma test4' E κ κ' c2 :
    lctx_lft_incl E [κ ⊑ₗ{c2} [κ']] (κ ⊓ κ) (κ ⊓ κ').
  Proof.
    solve_lft_incl; solve[fail].
  Abort.

  Lemma test5 ϝ0 ϝ ulft_a :
    lctx_lft_incl_list [ϝ0 ⊑ₑ ϝ; ϝ ⊑ₑ ulft_a] [ϝ ⊑ₗ{ 0} []] [ϝ0] [ulft_a].
  Proof.
    solve_lft_incl_list; solve[fail].
  Abort.

  Lemma test6 E κ κ' κ'' c2 :
    lctx_lft_incl E [κ ≡ₗ [κ']; κ' ⊑ₗ{c2} [κ'']] (κ') (κ).
  Proof.
    solve_lft_incl; solve[fail].
  Abort.
End test.

(** solve_lft_alive *)
Section test.
  Context `{typeGS Σ}.

  Lemma test1 κ κ' c1 c2 :
    lctx_lft_alive [] [κ ⊑ₗ{c1} [κ']; κ' ⊑ₗ{c2} []] κ.
  Proof.
    solve_lft_alive; solve[fail].
  Abort.

  Lemma test2 κ κ' ϝ c :
    lctx_lft_alive [κ ⊑ₑ κ'; ϝ ⊑ₑ κ] [ϝ ⊑ₗ{c} []] κ'.
  Proof.
    solve_lft_alive; solve[fail].
  Abort.

  Lemma test3 κ κ' κ'' ϝ c1 c2 :
    lctx_lft_alive [κ ⊑ₑ κ'; ϝ ⊑ₑ κ ] [ϝ ⊑ₗ{c1} []; κ'' ⊑ₗ{c2} [κ'; ϝ]] κ''.
  Proof.
    solve_lft_alive; solve[fail].
  Abort.

  Lemma test3 κ κ' κ'' ϝ c1 :
    lctx_lft_alive [κ ⊑ₑ κ'; ϝ ⊑ₑ κ ] [ϝ ⊑ₗ{c1} []; κ'' ≡ₗ [κ'; ϝ]] κ''.
  Proof.
    solve_lft_alive; solve[fail].
  Abort.

  (* needs backtracking *)
  Lemma test3 κ κ' ϝ c1 :
    lctx_lft_alive [κ' ⊑ₑ κ; ϝ ⊑ₑ κ] [ϝ ⊑ₗ{c1} []] κ.
  Proof.
    solve_lft_alive; solve[fail].
  Abort.

  Lemma test4 κ κ' c1 c2 :
    lctx_lft_alive [] [κ ⊑ₗ{c1} [κ']; κ' ⊑ₗ{c2} []] (κ ⊓ κ).
  Proof.
    solve_lft_alive; solve[fail].
  Abort.

  Lemma test5 κ c1 :
    Forall (lctx_lft_alive [] [κ ⊑ₗ{c1} []]) [κ; κ].
  Proof.
    solve_lft_alive; solve[fail].
  Abort.
End test.

(** simplify_elctx *)
Section test.

  Section RawVec_sls.
    Context `{!typeGS Σ}.

    Definition RawVec_sls (T_st : syn_type) : struct_layout_spec := mk_sls "RawVec" [
      ("ptr", PtrSynType);
      ("cap", IntSynType USize);
      ("_marker", UnitSynType)] StructReprRust.
  End RawVec_sls.
  Section Vec_sls.
    Context `{!typeGS Σ}.

    Definition Vec_sls (T_st : syn_type) : struct_layout_spec := mk_sls "Vec" [
      ("buf", (syn_type_of_sls ((RawVec_sls (T_st)))));
      ("len", IntSynType USize)] StructReprRust.
  End Vec_sls.
  Section RawVec_ty.
    Context `{!typeGS Σ}.
    Context {T_rt : Type}.
    Context (T_ty : type (T_rt)).

    Definition RawVec_ty : type (plist place_rfn [_ : Type; Z : Type; unit : Type]) := struct_t (RawVec_sls (ty_syn_type T_ty)) +[
      alias_ptr_t;
      (int USize);
      unit_t].
    Definition RawVec_rt : Type := Eval hnf in rt_of RawVec_ty.
    Global Typeclasses Transparent RawVec_ty.
  End RawVec_ty.

  Section RawVec_inv_t.
    Context `{!typeGS Σ}.
    Context {T_rt : Type}.
    Context (T_ty : type (T_rt)).

    Program Definition RawVec_inv_t_inv_spec : ex_inv_def ((RawVec_rt)) ((loc * nat)) := mk_ex_inv_def
      (λ π inner_rfn '(l, cap) , ⌜inner_rfn = (-[#(l); #(Z.of_nat cap); #(tt)])⌝ ∗ True)%I
      (λ π κ inner_rfn '(l, cap), ⌜inner_rfn = -[#(l); #(Z.of_nat cap); #(tt)]⌝ ∗ True)%I
      ([])
      ([])
      _ _ _
    .
    Next Obligation. ex_t_solve_persistent. Qed.
    Next Obligation.
      ex_plain_t_solve_shr_mono.
    Qed.
    Next Obligation.
      ex_plain_t_solve_shr.
    Qed.

    Definition RawVec_inv_t : type ((loc * nat)) :=
      ex_plain_t _ _ RawVec_inv_t_inv_spec (RawVec_ty T_ty).
  End RawVec_inv_t.

  Section Vec_ty.
    Context `{!typeGS Σ}.
    Context {T_rt : Type}.
    Context (T_ty : type (T_rt)).

    Definition Vec_ty : type (plist place_rfn [_ : Type; Z : Type]) := struct_t (Vec_sls (ty_syn_type T_ty)) +[
      (RawVec_inv_t (T_ty));
      (int USize)].
    Definition Vec_rt : Type := Eval hnf in rt_of Vec_ty.
    Global Typeclasses Transparent Vec_ty.
  End Vec_ty.

  Section Vec_inv_t.
    Context `{!typeGS Σ}.
    Context {T_rt : Type}.
    Context (T_ty : type (T_rt)).

    Program Definition Vec_inv_t_inv_spec : ex_inv_def ((Vec_rt)) (list (place_rfn T_rt)) := mk_ex_inv_def
      (λ π inner_rfn 'xs, ∃ (cap : nat) (l : loc), ⌜inner_rfn = -[#((l, cap)); #(Z.of_nat $ length xs)]⌝ ∗ ⌜length xs ≤ cap⌝ ∗ True)%I
      (λ π κ inner_rfn 'xs, ∃ (cap : nat) (l : loc), ⌜inner_rfn = -[#((l, cap)); #(Z.of_nat $ length xs)]⌝ ∗ ⌜length xs ≤ cap⌝ ∗ True)%I
      ([] ++ (ty_lfts T_ty))
      ([] ++ (ty_wf_E T_ty))
      _ _ _
    .
    Next Obligation.
      ex_t_solve_persistent.
    Qed.
    Next Obligation.
      ex_plain_t_solve_shr_mono.
    Qed.
    Next Obligation.
      ex_plain_t_solve_shr.
    Qed.

    Definition Vec_inv_t : type (list (place_rfn T_rt)) :=
      ex_plain_t _ _ Vec_inv_t_inv_spec (Vec_ty T_ty).
    Hint Unfold Vec_inv_t : tyunfold.
  End Vec_inv_t.

  Lemma test1 `{!typeGS Σ} {T_rt} (T_ty : type T_rt) xs γ x ulft__ ϝ : ∃ E',
    ([] ++
   tyl_wf_E
     (map map_rtype
        [existT (place_rfn (list (place_rfn T_rt)) * gname)%type
           (mut_ref (Vec_inv_t T_ty) ulft__, (# xs, γ));
        existT T_rt (T_ty, x)]) ++
   tyl_outlives_E
     (map map_rtype
        [existT (place_rfn (list (place_rfn T_rt)) * gname)%type
           (mut_ref (Vec_inv_t T_ty) ulft__, (# xs, γ));
        existT T_rt (T_ty, x)]) ϝ ++ ty_wf_E unit_t ++ ty_outlives_E unit_t ϝ) = E' ∧ E' = E'.
  Proof.
    eexists.
    split; [solve simplify_elctx | done].
  Abort.
End test.

(** reorder_elctx *)
Section test.
  Context `{!typeGS Σ}.

  Lemma test1 E0 E1 κ1 κ2 :
    ∃ K0, (κ1 ⊑ₑ κ2) :: E0 ++ (κ2 ⊑ₑ κ1) :: E1 ≡ₚ K0 ∧ K0 = (κ1 ⊑ₑ κ2) :: (κ2 ⊑ₑ κ1) :: E0 ++ E1.
  Proof.
    eexists _. split.
    { reorder_elctx. }
    done.
  Abort.

  Lemma test1 E0 E1 κ1 κ2 :
    ∃ K0, (κ1 ⊑ₑ κ2) :: E0 ++ E1 ++ [κ2 ⊑ₑ κ1] ≡ₚ K0 ∧ K0 = (κ1 ⊑ₑ κ2) :: (κ2 ⊑ₑ κ1) :: E0 ++ E1.
  Proof.
    eexists _. split.
    { reorder_elctx. }
    done.
  Abort.
End test.



(** solve_elctx_sat *)
Section test.
  Context `{typeGS Σ}.

  Lemma test1 κ κ' :
    elctx_sat [κ ⊑ₑ κ'] [] [κ ⊑ₑ κ'; κ ⊑ₑ κ'].
  Proof. solve_elctx_sat; solve[fail]. Abort.
  Lemma test2 κ κ' κ'' c1 :
    elctx_sat [κ ⊑ₑ κ'] [κ' ⊑ₗ{c1} [κ'']] [κ ⊑ₑ κ''].
  Proof. solve_elctx_sat; solve[fail]. Abort.
  Lemma test3 ϝ0 ϝ c1 :
    elctx_sat ((ϝ0 ⊑ₑ ϝ) :: ty_outlives_E (uninit (IntSynType i32)) ϝ) [ϝ ⊑ₗ{c1} []] (ty_outlives_E (uninit (IntSynType i32)) ϝ).
  Proof. solve_elctx_sat; solve[fail]. Abort.
  Lemma test4 ϝ0 ϝ :
    elctx_sat [ϝ0 ⊑ₑ ϝ] [ϝ ⊑ₗ{ 0} []] (lfts_outlives_E (ty_lfts alias_ptr_t) ϝ0).
  Proof. solve_elctx_sat; solve[fail]. Abort.
  Lemma test5 ϝ0 ϝ {rt} (T_ty : type rt) :
    elctx_sat (ty_outlives_E (T_ty) ϝ ++ (ϝ0 ⊑ₑ ϝ) :: ty_outlives_E (T_ty) ϝ) [ϝ ⊑ₗ{ 0} []] ((ϝ ⊑ₑ ϝ) :: ty_outlives_E (T_ty) ϝ0).
  Proof. solve_elctx_sat; solve[fail]. Abort.
  Lemma test6 ϝ0 ϝ {rt} (T_ty : type rt) :
    elctx_sat ((ϝ0 ⊑ₑ ϝ) :: ty_wf_E (T_ty)) [ϝ ⊑ₗ{ 0} []] ((ϝ ⊑ₑ ϝ) :: ty_wf_E (T_ty)).
  Proof. solve_elctx_sat; solve[fail]. Abort.
  Lemma test7 ϝ0 ϝ {rt} (T_ty : type rt) :
    elctx_sat ((ϝ0 ⊑ₑ ϝ) :: ty_outlives_E T_ty ϝ ++ ty_wf_E (T_ty)) [ϝ ⊑ₗ{ 0} []] ((ϝ ⊑ₑ ϝ) :: ty_wf_E (T_ty)).
  Proof. solve_elctx_sat; solve[fail]. Abort.

End test.

(** solve_bor_kind_alive *)
Section test.
  Context `{typeGS Σ}.

  Lemma test1 E L :
    lctx_bor_kind_alive E L (Owned false).
  Proof. solve[solve_bor_kind_alive]. Abort.

  Lemma test2 κ γ c1 :
    lctx_bor_kind_alive [] [κ ⊑ₗ{c1} []] (Uniq κ γ ⊓ₖ Uniq κ γ ⊓ₖ Owned true).
  Proof. solve [solve_bor_kind_alive]. Abort.

  Lemma test3 κ κ' c1 :
    lctx_bor_kind_alive [κ' ⊑ₑ κ] [κ' ⊑ₗ{c1} []] (Shared κ ⊓ₖ Owned false).
  Proof. solve[solve_bor_kind_alive]. Abort.
End test.

(** solve_bor_kind_incl *)
Section test.
  Context `{typeGS Σ}.

  Lemma test1 E L :
    lctx_bor_kind_incl E L (Owned false) (Owned true).
  Proof. solve[solve_bor_kind_incl]. Abort.

  Lemma test2 κ γ c1 :
    lctx_bor_kind_incl [] [κ ⊑ₗ{c1} []] (Owned false ⊓ₖ Uniq κ γ) (Owned true).
  Proof. solve[solve_bor_kind_incl]. Abort.

  Lemma test3 κ γ κ' γ' c1 :
    lctx_bor_kind_incl [κ' ⊑ₑ static] [κ ⊑ₗ{c1} [κ']] (Owned false ⊓ₖ Uniq κ γ) (Uniq κ' γ').
  Proof. solve[solve_bor_kind_incl]. Abort.

  Lemma test4 κ κ' γ' c1 :
    lctx_bor_kind_incl [κ' ⊑ₑ static] [κ' ⊑ₗ{c1} [κ]] (Shared κ ⊓ₖ Uniq κ' γ') (Shared κ ⊓ₖ Shared κ).
  Proof. solve[solve_bor_kind_incl]. Abort.

  Lemma test5 κ κ' c1 :
    lctx_bor_kind_incl [κ' ⊑ₑ static] [κ ⊑ₗ{c1} [κ']] (Shared κ) (Shared κ' ⊓ₖ Owned false).
  Proof. solve[solve_bor_kind_incl]. Abort.
End test.

(** solve_bor_kind_direct_incl *)
Section test.
  Context `{typeGS Σ}.

  Lemma test1 E L :
    lctx_bor_kind_direct_incl E L (Owned false) (Owned false).
  Proof. solve[solve_bor_kind_direct_incl]. Abort.

  Lemma test2 κ γ c1 :
    lctx_bor_kind_direct_incl [] [κ ⊑ₗ{c1} []] (Owned false ⊓ₖ Uniq κ γ) (Uniq κ γ).
  Proof. solve[solve_bor_kind_direct_incl]. Abort.

  Lemma test3 κ γ κ' c1 :
    lctx_bor_kind_direct_incl [κ' ⊑ₑ static] [κ ⊑ₗ{c1} [κ']] (Owned false ⊓ₖ Uniq κ γ) (Uniq κ' γ).
  Proof. solve[solve_bor_kind_direct_incl]. Abort.

  Lemma test4 κ γ κ' c1 :
    lctx_bor_kind_direct_incl [κ' ⊑ₑ static] [κ ⊑ₗ{c1} [κ']] (Shared κ ⊓ₖ Uniq κ γ) (Shared κ ⊓ₖ Uniq κ' γ) .
  Proof. solve[solve_bor_kind_direct_incl]. Abort.

  Lemma test5 κ κ' c1 :
    lctx_bor_kind_direct_incl [κ' ⊑ₑ static] [κ ⊑ₗ{c1} [κ']] (Shared κ) (Shared κ' ⊓ₖ Owned false).
  Proof. solve[solve_bor_kind_direct_incl]. Abort.
End test.

(** solve_lft_alive_count *)
Section test.
  Context `{typeGS Σ}.

  Lemma test1 κ κ' :
    lctx_lft_alive_count [] [κ ⊑ₗ{0} [κ']; κ' ⊑ₗ{0} []] κ [κ; κ'] [κ ⊑ₗ{1} [κ']; κ' ⊑ₗ{1} []].
  Proof.
    solve_lft_alive_count; solve[fail].
  Abort.

  Lemma test2 κ κ' ϝ c :
    lctx_lft_alive_count [κ ⊑ₑ κ'; ϝ ⊑ₑ κ] [ϝ ⊑ₗ{c} []] κ' [ϝ] [ϝ ⊑ₗ{S c} []].
  Proof.
    solve_lft_alive_count; solve[fail].
  Abort.

  Lemma test3 κ κ' κ'' ϝ c1 c2 :
    lctx_lft_alive_count [κ ⊑ₑ κ'; ϝ ⊑ₑ κ ] [ϝ ⊑ₗ{c1} []; κ'' ⊑ₗ{c2} [κ'; ϝ]] κ'' [κ''; ϝ; ϝ] [ϝ ⊑ₗ{2+ c1} []; κ'' ⊑ₗ{S c2} [κ'; ϝ]].
  Proof.
    solve_lft_alive_count; solve[fail].
  Abort.

  Lemma test3 κ κ' κ'' ϝ c1 :
    lctx_lft_alive_count [κ ⊑ₑ κ'; ϝ ⊑ₑ κ ] [ϝ ⊑ₗ{c1} []; κ'' ≡ₗ[κ'; ϝ]] κ'' [ϝ; ϝ] [ϝ ⊑ₗ{2+ c1} []; κ'' ≡ₗ [κ'; ϝ]].
  Proof.
    solve_lft_alive_count; solve[fail].
  Abort.

  (* needs backtracking *)
  Lemma test3 κ κ' ϝ c :
    lctx_lft_alive_count [κ' ⊑ₑ κ; ϝ ⊑ₑ κ] [ϝ ⊑ₗ{c} []] κ [ϝ] [ϝ ⊑ₗ{S c} []].
  Proof.
    solve_lft_alive_count; solve[fail].
  Abort.

  Lemma test4 κ κ' :
    lctx_lft_alive_count [] [κ ⊑ₗ{0} [κ']; κ' ⊑ₗ{0} []] (κ ⊓ κ) [κ; κ'; κ; κ'] [κ ⊑ₗ{2} [κ']; κ' ⊑ₗ{2} []].
  Proof.
    solve_lft_alive_count; solve[fail].
  Abort.

  Lemma test5 {rt} (T_ty : type rt) ulft__ ϝ :
    lctx_lft_alive_count ((ϝ ⊑ₑ ulft__) :: ty_outlives_E T_ty ϝ ++ ty_outlives_E T_ty ϝ ++ ty_outlives_E T_ty ulft__ ++ ty_wf_E T_ty) [ϝ ⊑ₗ{ 0} []] ulft__ [ϝ] [ϝ ⊑ₗ{ 1} []].
  Proof.
    solve_lft_alive_count; solve[fail].
  Abort.
End test.

(** solve_llctx_release_toks *)
Section test.
  Context `{!invGS Σ, !lctxGS Σ, !lftGS Σ lft_userE}.
  (*Context `{typeGS Σ}.*)

  Lemma test1 κ κ' :
    llctx_release_toks [κ ⊑ₗ{1} [κ']; κ' ⊑ₗ{1} []] [κ; κ'] [κ ⊑ₗ{0} [κ']; κ' ⊑ₗ{0} []].
  Proof.
    solve_llctx_release_toks; solve[fail].
  Abort.
  Lemma test2 ϝ c :
    llctx_release_toks [ϝ ⊑ₗ{S c} []] [ϝ] [ϝ ⊑ₗ{c} []].
  Proof.
    solve_llctx_release_toks; solve[fail].
  Abort.
  Lemma test3 κ' κ'' ϝ c1 c2 :
    llctx_release_toks [ϝ ⊑ₗ{2+ c1} []; κ'' ⊑ₗ{S c2} [κ'; ϝ]] [κ''; ϝ; ϝ] [ϝ ⊑ₗ{c1} []; κ'' ⊑ₗ{c2} [κ'; ϝ]].
  Proof.
    solve_llctx_release_toks; solve[fail].
  Abort.
  Lemma test3 ϝ c :
    llctx_release_toks [ϝ ⊑ₗ{S c} []] [ϝ] [ϝ ⊑ₗ{c} []].
  Proof.
    solve_llctx_release_toks; solve[fail].
  Abort.
  Lemma test4 κ κ' :
    llctx_release_toks [κ ⊑ₗ{2} [κ']; κ' ⊑ₗ{2} []] [κ; κ'; κ; κ'] [κ ⊑ₗ{0} [κ']; κ' ⊑ₗ{0} []].
  Proof.
    solve_llctx_release_toks; solve[fail].
  Abort.
  Lemma test5 κ κ' κ2 :
    llctx_release_toks [κ ⊑ₗ{2} [κ']; κ' ⊑ₗ{2} []] [κ2; κ; κ'; κ; κ'; κ2] [κ ⊑ₗ{0} [κ']; κ' ⊑ₗ{0} []].
  Proof.
    solve_llctx_release_toks; solve[fail].
  Abort.
End test.


(** solve_llctx_find_llft *)
Section test.
  Lemma lft_find_test (κ κ' κ2 : lft) :
    ∃ L', llctx_find_llft [κ2 ≡ₗ []; κ ⊑ₗ{1} []; κ' ⊑ₗ{0} [κ]] κ' LlctxFindLftFull [κ] L' ∧ L' = [κ2 ≡ₗ []; κ ⊑ₗ{1} []].
  Proof.
    eexists. split; first solve[solve_llctx_find_llft]. done.
  Abort.

  Lemma lft_find_test2 (κ κ' κ2 : lft) :
    ∃ L' κs, llctx_find_llft [κ2 ≡ₗ []; κ ⊑ₗ{1} []; κ' ⊑ₗ{0} [κ]] κ2 LlctxFindLftAlias κs L' ∧ κs = [].
  Proof.
    eexists _, _.
    split; first solve[solve_llctx_find_llft]. done.
  Abort.

  Lemma lft_find_test3 (κ κ' κ2 : lft) :
    ∃ L' κs, llctx_find_llft [κ2 ≡ₗ []; κ ⊑ₗ{1} []; κ' ⊑ₗ{0} [κ]] κ LlctxFindLftOwned κs L' ∧ κs = [].
  Proof.
    eexists _, _.
    split; first solve[solve_llctx_find_llft]. done.
  Abort.
End test.

(** solve_bor_kind_outlives *)
Section test.
  Context `{!typeGS Σ}.

  Lemma lctx_bor_kind_outlives_test1 κ1 κ2 :
    lctx_bor_kind_outlives [] [κ1 ⊑ₗ{0} [κ2]] (Shared κ2) κ1.
  Proof.
    solve_bor_kind_outlives; solve [fail].
  Abort.
End test.


(** solve_inhabited *)
Section test.
  Context (T : Type) `{!Inhabited T}.
  Inductive inh_test1 :=
  | None
  | Some (x : T).

  Instance: Inhabited inh_test1.
  Proof. solve_inhabited; done. Abort.

  Inductive inh_test2 :=
  | inA (x : nat)
  | inB (y : Z).

  Instance: Inhabited inh_test2.
  Proof. solve_inhabited; done. Abort.
End test.
