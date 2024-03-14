From refinedrust Require Import typing.

(** * Built-in shims for low-level pointer operations *)

(** Tuple defs *)
(* Since the frontend doesn't generate them for now, we just provide a few pre-defined ones for reasonable sizes. *)
Definition tuple1_sls (T0_st : syn_type) : struct_layout_spec :=
  mk_sls "tuple1" [("0", T0_st)] StructReprRust.
Definition tuple1_st (T0_st : syn_type) : syn_type := tuple1_sls T0_st.
Definition tuple1_rt (T0_rt : Type) : Type :=
  plist place_rfn [T0_rt].
Definition tuple1_ty `{!typeGS Σ} {T0_rt : Type} (T0_ty : type T0_rt) : type (tuple1_rt _) :=
  struct_t (tuple1_sls (st_of T0_ty)) +[T0_ty].

Definition tuple2_sls (T0_st T1_st : syn_type) : struct_layout_spec :=
  mk_sls "tuple2" [("0", T0_st); ("1", T1_st)] StructReprRust.
Definition tuple2_st (T0_st T1_st : syn_type) : syn_type := tuple2_sls T0_st T1_st.
Definition tuple2_rt (T0_rt : Type) (T1_rt : Type) : Type :=
  plist place_rfn [T0_rt; T1_rt].
Definition tuple2_ty `{!typeGS Σ} {T0_rt T1_rt : Type} (T0_ty : type T0_rt) (T1_ty : type T1_rt) : type (tuple2_rt _ _) :=
  struct_t (tuple2_sls (st_of T0_ty) (st_of T1_ty)) +[T0_ty; T1_ty].

Definition tuple3_sls (T0_st T1_st T2_st : syn_type) : struct_layout_spec :=
  mk_sls "tuple3" [("0", T0_st); ("1", T1_st); ("2", T2_st)] StructReprRust.
Definition tuple3_st (T0_st T1_st T2_st : syn_type) : syn_type := tuple3_sls T0_st T1_st T2_st.
Definition tuple3_rt (T0_rt : Type) (T1_rt : Type) (T2_rt : Type) : Type :=
  plist place_rfn [T0_rt; T1_rt; T2_rt].
Definition tuple3_ty `{!typeGS Σ} {T0_rt T1_rt T2_rt : Type} (T0_ty : type T0_rt) (T1_ty : type T1_rt) (T2_ty : type T2_rt) : type (tuple3_rt _ _ _) :=
  struct_t (tuple3_sls (st_of T0_ty) (st_of T1_ty) (st_of T2_ty)) +[T0_ty; T1_ty; T2_ty].

Definition tuple4_sls (T0_st T1_st T2_st T3_st : syn_type) : struct_layout_spec :=
  mk_sls "tuple4" [("0", T0_st); ("1", T1_st); ("2", T2_st); ("3", T3_st)] StructReprRust.
Definition tuple4_st (T0_st T1_st T2_st T3_st : syn_type) : syn_type := tuple4_sls T0_st T1_st T2_st T3_st.
Definition tuple4_rt (T0_rt : Type) (T1_rt : Type) (T2_rt : Type) (T3_rt : Type) : Type :=
  plist place_rfn [T0_rt; T1_rt; T2_rt; T3_rt].
Definition tuple4_ty `{!typeGS Σ} {T0_rt T1_rt T2_rt T3_rt : Type} (T0_ty : type T0_rt) (T1_ty : type T1_rt) (T2_ty : type T2_rt) (T3_ty : type T3_rt) : type (tuple4_rt _ _ _ _) :=
  struct_t (tuple4_sls (st_of T0_ty) (st_of T1_ty) (st_of T2_ty) (st_of T3_ty)) +[T0_ty; T1_ty; T2_ty; T3_ty].

Definition tuple5_sls (T0_st T1_st T2_st T3_st T4_st : syn_type) : struct_layout_spec :=
  mk_sls "tuple5" [("0", T0_st); ("1", T1_st); ("2", T2_st); ("3", T3_st); ("4", T4_st)] StructReprRust.
Definition tuple5_st (T0_st T1_st T2_st T3_st T4_st : syn_type) : syn_type := tuple5_sls T0_st T1_st T2_st T3_st T4_st.
Definition tuple5_rt (T0_rt : Type) (T1_rt : Type) (T2_rt : Type) (T3_rt : Type) (T4_rt : Type) : Type :=
  plist place_rfn [T0_rt; T1_rt; T2_rt; T3_rt; T4_rt].
Definition tuple5_ty `{!typeGS Σ} {T0_rt T1_rt T2_rt T3_rt T4_rt : Type} (T0_ty : type T0_rt) (T1_ty : type T1_rt) (T2_ty : type T2_rt) (T3_ty : type T3_rt) (T4_ty : type T4_rt) : type (tuple5_rt _ _ _ _ _) :=
  struct_t (tuple5_sls (st_of T0_ty) (st_of T1_ty) (st_of T2_ty) (st_of T3_ty) (st_of T4_ty)) +[T0_ty; T1_ty; T2_ty; T3_ty; T4_ty].

(* TODO move *)
Lemma ly_align_log_in_u8 ly :
  ly_align_in_bounds ly → Z.of_nat (ly_align_log ly) ∈ u8.
Proof.
  rewrite /ly_align_in_bounds/min_alloc_start/max_alloc_end/=/ly_align/bytes_per_addr/bytes_per_addr_log/=.
  rewrite /bits_per_byte/=.
  intros [Ha Hb].
  split; first (init_cache; solve_goal).
  rewrite MaxInt_eq.
  rewrite /max_int/=/int_modulus/bits_per_int/bytes_per_int/it_byte_size_log/=.
  rewrite /bits_per_byte/=.
  assert ((2 ^ ly_align_log ly) ≤ 2 ^ (8%nat * 8))%nat as Hle.
  { apply Nat2Z.inj_le. etrans; first apply Hb.
    rewrite Nat2Z.inj_pow. nia.
  }
  apply PeanoNat.Nat.pow_le_mono_r_iff in Hle; last lia.
  nia.
Qed.
Lemma ly_align_log_in_usize ly :
  ly_align_in_bounds ly → Z.of_nat (ly_align_log ly) ∈ usize_t.
Proof.
  intros [_ Ha]%ly_align_log_in_u8.
  split; first (init_cache; solve_goal).
  etrans; first apply Ha.
  rewrite MaxInt_eq in Ha.
  rewrite !MaxInt_eq /max_int/=/int_modulus/bits_per_int/bytes_per_int/it_byte_size_log/bits_per_byte/=.
  nia.
Qed.
Lemma ly_align_in_usize ly :
  ly_align_in_bounds ly → Z.of_nat (ly_align ly) ∈ usize_t.
Proof.
  intros [Ha Hb]. split; first (init_cache; solve_goal).
  etrans; first apply Hb.
  (* TODO: why doesn't this work anymore? *)
  rewrite /max_alloc_end.
  unfold max_alloc_end.
  rewrite /bytes_per_addr/bytes_per_addr_log.
  rewrite !MaxInt_eq /max_int/=/int_modulus/bits_per_int/bytes_per_int/it_byte_size_log/=.
  nia.
Qed.

(** ** Mem API *)

(** mem::size_of *)
Definition mem_size_of `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [];
  f_local_vars := [];
  f_code :=
    <["_bb0" :=
      return (I2v (ly_size (use_layout_alg' T_st)) USize)
    ]>%E $
    ∅;
  f_init := "_bb0";
|}.
Definition type_of_mem_size_of `{!typeGS Σ} (T_rt : Type) (T_st : syn_type) :=
  fn(∀ () : 0 | () : unit, (λ ϝ, []); λ π, True)
    → ∃ () : unit, (ly_size (use_layout_alg' T_st)) @ int usize_t; λ π, True.
Lemma mem_size_of_typed `{!typeGS Σ} π T_rt T_st T_ly :
  syn_type_has_layout T_st T_ly →
  ⊢ typed_function π (mem_size_of T_st) [] (type_of_mem_size_of T_rt T_st).
Proof.
  start_function "mem_size_of" ( () ) ( () ).
  repeat liRStep.
  Unshelve.
  all: unshelve_sidecond; open_cache; solve_goal.
Qed.

(** mem::align_of *)
Definition mem_align_of `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [];
  f_local_vars := [];
  f_code :=
    <["_bb0" :=
      return (I2v (ly_align (use_layout_alg' T_st)) USize)
    ]>%E $
    ∅;
  f_init := "_bb0";
|}.
Definition type_of_mem_align_of `{!typeGS Σ} (T_rt : Type) (T_st : syn_type) :=
  fn(∀ () : 0 | () : unit, (λ ϝ, []); λ π, True)
    → ∃ () : unit, (ly_align (use_layout_alg' T_st)) @ int usize_t; λ π, True.
Lemma mem_align_of_typed `{!typeGS Σ} π T_rt T_st T_ly :
  syn_type_has_layout T_st T_ly →
  ⊢ typed_function π (mem_align_of T_st) [] (type_of_mem_align_of T_rt T_st).
Proof.
  start_function "mem_align_of" ( () ) ( () ).
  repeat liRStep. Unshelve.
  all: unshelve_sidecond.
  by apply ly_align_in_usize.
Qed.

(** align_log_of -- gives the log2 of the alignment *)
Definition mem_align_log_of `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [];
  f_local_vars := [];
  f_code :=
    <["_bb0" :=
      return (I2v (ly_align_log (use_layout_alg' T_st)) USize)
    ]>%E $
    ∅;
  f_init := "_bb0";
|}.
Definition type_of_mem_align_log_of `{!typeGS Σ} (T_rt : Type) (T_st : syn_type) :=
  fn(∀ () : 0 | () : unit, (λ ϝ, []); λ π, True)
    → ∃ () : unit, (ly_align_log (use_layout_alg' T_st)) @ int usize_t; λ π, True.
Lemma mem_align_of_log_typed `{!typeGS Σ} π T_rt T_st T_ly :
  syn_type_has_layout T_st T_ly →
  ⊢ typed_function π (mem_align_log_of T_st) [] (type_of_mem_align_log_of T_rt T_st).
Proof.
  start_function "mem_align_log_of" ( () ) ( () ).
  repeat liRStep. Unshelve.
  all: unshelve_sidecond.
  by eapply ly_align_log_in_usize.
Qed.

(** ** Ptr API *)

(** copy_nonoverlapping *)
(*
  This just does a bytewise untyped copy, matching the intended Rust semantics. The sequence of bytes does not have to be a valid representation at any type.

  fn copy_nonoverlapping<T>(size, src, dst) {
    let mut count: usize = 0;

    assert_unsafe_precondition!(
        is_aligned_and_not_null(src)
            && is_aligned_and_not_null(dst)
            && is_nonoverlapping(src, dst, count)
    );

    let src = src as *const u8;
    let dst = dst as *mut u8;
    // do a bytewise copy
    while count < size {
      // uses untyped read + assignment, NOT the typed assignment in surface Rust!
      *(dst.add(count)) = *src.add(count);
      count+=1;
    }
  }

 *)
(* TODO: challenge for speccing this: what ownership do we require for src?
  - technically, we could require a shared ref.
    but: that is stronger than necessary - it asserts a validity invariant, whereas we should not require anything like that.
    is that also true if I have &shr (bytewise v) -- i.e. the type below the shared ref does not assert any validity invariant?
      I feel like that should be a pretty strong spec.
  - we could also try to take fractional ownership - but that would be quite a heavyweight change for this.
  - just take full ownership, similar to dst - but that is unnecessarily strong *)
Definition copy_nonoverlapping `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [("size", usize_t : layout); ("src", void* ); ("dst", void* )];
  f_local_vars := [("count", usize_t : layout)];
  f_code :=
    <["_bb0" :=
      "count" <-{IntOp usize_t} I2v 0 USize;
      (* TODO: add safety checks *)
      annot: StopAnnot;
      Goto "_bb_loop_head"
    ]>%E $
    <["_bb_loop_head" :=

      if{BoolOp}:
        (use{IntOp usize_t} "count") <{IntOp usize_t, IntOp usize_t, u8} (use{IntOp usize_t} "size")
      then
        Goto "_bb_loop_body"
      else
        Goto "_bb_loop_exit"
    ]>%E $
    <["_bb_loop_body" :=
        ((!{PtrOp} "dst") at_offset{use_layout_alg' T_st, PtrOp, IntOp usize_t} use{IntOp usize_t} "count")
      <-{UntypedOp (use_layout_alg' T_st)}
        use{UntypedOp (use_layout_alg' T_st)} (
          ((!{PtrOp} "src") at_offset{use_layout_alg' T_st, PtrOp, IntOp usize_t} use{IntOp usize_t} "count"));
      "count" <-{IntOp usize_t} (use{IntOp usize_t} "count") +{IntOp usize_t, IntOp usize_t} (I2v 1 USize);
      Goto "_bb_loop_head"
    ]>%E $
    <["_bb_loop_exit" :=
      annot: StopAnnot;
      return zst_val
    ]>%E $
    ∅;
  f_init := "_bb0";
|}.

Definition type_of_copy_nonoverlapping `{!typeGS Σ} (T_rt : Type) (T_st : syn_type):=
  fn(∀ () : 0 | (len, l_s, l_t, v_s) : (nat * loc * loc * val), (λ ϝ, []);
      Z.of_nat len @ int usize_t, l_s @ alias_ptr_t, l_t @ alias_ptr_t; λ π,
        l_s ◁ₗ[π, Owned false] PlaceIn v_s @ (◁ value_t (UntypedSynType (mk_array_layout (use_layout_alg' T_st) len))) ∗
        l_t ◁ₗ[π, Owned false] .@ (◁ uninit (UntypedSynType (mk_array_layout (use_layout_alg' T_st) len))))
    → ∃ () : unit, () @ unit_t; λ π,
        l_s ◁ₗ[π, Owned false] PlaceIn v_s @ (◁ value_t (UntypedSynType (mk_array_layout (use_layout_alg' T_st) len))) ∗
        l_t ◁ₗ[π, Owned false] PlaceIn v_s @ (◁ value_t (UntypedSynType (mk_array_layout (use_layout_alg' T_st) len))).
Lemma copy_nonoverlapping_typed `{!typeGS Σ} π T_rt T_st T_ly :
  syn_type_has_layout T_st T_ly →
  ⊢ typed_function π (copy_nonoverlapping T_st) [IntSynType usize_t] (type_of_copy_nonoverlapping T_rt T_st).
Proof.
  start_function "copy_nonoverlapping" ( () ) ( [[[len l_s] l_t] v_s] ).
  intros ls_size ls_src ls_dst ls_count.
  repeat liRStep; liShow.

  (* manual proof from here to formulate the loop invariant *)
  iApply typed_stmt_annot_skip.
  iSelect (_ ◁ₗ[_, _] PlaceIn (Z.of_nat len) @ _)%I (fun H => iRename H into "Hlen").
  iSelect (_ ◁ₗ[_, _] PlaceIn 0%Z @ _)%I (fun H => iRename H into "Hcount").
  iSelect (_ ◁ₗ[_, _] PlaceIn l_s @ (◁ alias_ptr_t))%I (fun H => iRename H into "Hsrc").
  iSelect (_ ◁ₗ[_, _] PlaceIn l_t @ (◁ alias_ptr_t))%I (fun H => iRename H into "Hdst").
  iSelect (l_s ◁ₗ[_, _] _ @ _)%I (fun H => iRename H into "Hs").
  iSelect (l_t ◁ₗ[_, _] _ @ _)%I (fun H => iRename H into "Ht").
  iApply fupd_typed_stmt.
  iMod (ofty_uninit_to_value with "Ht") as "(%v_t & Ht)"; first done.
  iMod (ofty_value_has_length with "Hs") as "(%Hlen_s & Hs)"; first done.
  { sidecond_hook. }
  iMod (ofty_value_has_length with "Ht") as "(%Hlen_t & Ht)"; first done.
  { sidecond_hook. }

  (* turn it into arrays *)
  iPoseProof (ofty_value_untyped_to_array with "Hs") as "Hs".
  { by eapply syn_type_has_layout_make_untyped. }
  iPoseProof (ofty_value_untyped_to_array with "Ht") as "Ht".
  { by eapply syn_type_has_layout_make_untyped. }
  iModIntro.

  set (loop_inv := (λ (E : elctx) (L : llctx),
    ∃ (i : nat),
    ⌜L = [ϝ ⊑ₗ{0} []]⌝ ∗
    ⌜E = []⌝ ∗
    (credit_store 0 0 ∗
    ls_size ◁ₗ[π, Owned false] PlaceIn (Z.of_nat len) @ (◁ int usize_t) ∗
    ls_count ◁ₗ[π, Owned false] PlaceIn (Z.of_nat i) @ (◁ int usize_t) ∗
    ls_src ◁ₗ[π, Owned false] PlaceIn l_s @ (◁ alias_ptr_t) ∗
    ls_dst ◁ₗ[π, Owned false] PlaceIn l_t @ (◁ alias_ptr_t) ∗
    l_s ◁ₗ[ π, Owned false] # (fmap (M:=list) PlaceIn (reshape (replicate len (ly_size T_st_ly)) v_s)) @ (◁ array_t (value_t (UntypedSynType T_st_ly)) len) ∗
    l_t ◁ₗ[π, Owned false] #(fmap (M:=list) PlaceIn (take i (reshape (replicate len (ly_size T_st_ly)) v_s) ++ drop i (reshape (replicate len (ly_size T_st_ly)) v_t))) @ (◁ array_t (value_t (UntypedSynType T_st_ly)) len)))%I).
  iApply (typed_goto_acc _ _ _ _ _ loop_inv).
  { unfold_code_marker_and_compute_map_lookup. }
  liRStep; liShow. iExists 0%nat.
  repeat liRStep. liShow.
  iRename select (loop_inv _ _) into "Hinv".
  iDestruct "Hinv" as "(%i & -> & -> & Hcredit & Hlen & Hcount & Hsrc & Hdst & Hs & Ht)".
  repeat liRStep; liShow.
   (*return: go back to values *)
  assert (take i (reshape (replicate len (ly_size T_st_ly)) v_s) ++ drop i (reshape (replicate len (ly_size T_st_ly)) v_t) = (reshape (replicate len (ly_size T_st_ly)) (take (i * ly_size T_st_ly) v_s ++ drop (i * ly_size T_st_ly) v_t))) as ->.
  { shelve. }
  iPoseProof (ofty_value_untyped_from_array with "Hs") as "Hs".
  { rewrite Hlen_s ly_size_mk_array_layout. lia. }
  iPoseProof (ofty_value_untyped_from_array with "Ht") as "Ht".
  { rewrite app_length take_length drop_length. rewrite Hlen_t Hlen_s !ly_size_mk_array_layout. lia. }

  iApply typed_stmt_annot_skip.
  repeat liRStep; liShow.

  Unshelve. all: unshelve_sidecond; sidecond_hook.
  Unshelve. all: prepare_sideconditions; try (normalize_and_simpl_goal; solve_goal).

  Unshelve.
  + cbn. rewrite -list_fmap_insert.
    rewrite insert_app_r_alt; first last.
    { rewrite take_length. lia. }
    rewrite take_length reshape_length.
    rewrite Nat.min_l; first last. { rewrite replicate_length. lia. }
    rewrite Nat.sub_diag.
    f_equiv. f_equiv.
    rename select (reshape _ v_s !! i = Some _) into Hlook.
    rename select (i < len)%nat into Hi.
    clear -Hlook Hi.
    rewrite Nat.add_1_r.
    erewrite take_S_r; last done.
    rewrite -app_assoc.
    f_equiv.
    rewrite insert_take_drop; first last. { rewrite drop_length reshape_length replicate_length. lia. }
    rewrite take_0 drop_drop. rewrite Nat.add_1_r. done.
  + rewrite take_ge; last solve_goal with nia.
    rewrite drop_ge; last solve_goal with nia.
    by rewrite app_nil_r.
  + rewrite  drop_ge; first last. { rewrite reshape_length replicate_length. lia. }
    rewrite app_nil_r.
    rewrite drop_ge; first last. { solve_goal with nia. }
    rewrite app_nil_r.
    assert (len ≤ i) as Hle by lia. clear -Hle Hlen_s.
    rewrite take_ge. 2: { rewrite reshape_length replicate_length. lia. }
    rewrite take_ge; first done.
    rewrite Hlen_s /mk_array_layout{1}/ly_size/=. nia.
Qed.

Definition ptr_write `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [("dst", void* ); ("src", use_layout_alg' T_st)];
  f_local_vars := [];
  f_code :=
    <["_bb0" :=
      (* NOTE: the rust impl uses copy_nonoverlapping and then asserts with an intrinsic that the validity invariant for T holds,
          but we don't have such a thing and should simply use a typed copy *)
      !{PtrOp} "dst" <-{use_op_alg' T_st} use{use_op_alg' T_st} "src";
      return zst_val
    ]>%E $
    ∅;
  f_init := "_bb0";
|}.

(* Maybe this should also be specced in terms of value? *)
Definition type_of_ptr_write `{!typeGS Σ} (T_rt : Type) (T_st : syn_type) :=
  fn(∀ (()) : 0 | (T_ty, l, r) : (type T_rt * loc * T_rt), (λ ϝ, []);
      l @ alias_ptr_t, r @ T_ty; λ π,
      (⌜T_st = T_ty.(ty_syn_type)⌝ ∗ ⌜ty_allows_reads T_ty⌝ ∗ ⌜ty_allows_writes T_ty⌝ ∗ l ◁ₗ[π, Owned false] .@ (◁ uninit (T_ty.(ty_syn_type)))))
    → ∃ () : unit, () @ unit_t; λ π,
        l ◁ₗ[π, Owned false] PlaceIn r @ ◁ T_ty.


Lemma ptr_write_typed `{!typeGS Σ} π T_rt T_st T_ly :
  syn_type_has_layout T_st T_ly →
  ⊢ typed_function π (ptr_write T_st) [] (type_of_ptr_write T_rt T_st).
Proof.
  start_function "ptr_write" ( [] ) ( [[T_ty l] r] ).
  intros ls_dst ls_src.
  repeat liRStep; liShow.
  Unshelve. all: unshelve_sidecond; sidecond_hook.
  Unshelve. all: unfold_common_defs; try solve_goal.
Qed.


Definition ptr_read `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [("src", void* )];
  f_local_vars := [("tmp", use_layout_alg' T_st)];
  f_code :=
    <["_bb0" :=
      "tmp" <-{use_op_alg' T_st} use{use_op_alg' T_st} (!{PtrOp} "src");
      return (use{use_op_alg' T_st} "tmp")
    ]>%E $
    ∅;
  f_init := "_bb0";
|}.
Definition type_of_ptr_read `{!typeGS Σ} (T_rt : Type) (T_st : syn_type) :=
  fn(∀ () : 0 | (T_ty, l, r) : (type T_rt * loc * T_rt), (λ ϝ, []);
      l @ alias_ptr_t; λ π,
      ⌜T_st = ty_syn_type T_ty⌝ ∗
      ⌜ty_allows_reads T_ty⌝ ∗
      (*(l ◁ₗ[π, Owned false] PlaceIn vs @ (◁ value_t (T_ty.(ty_syn_type))))*)
      (l ◁ₗ[π, Owned false] #r @ (◁ T_ty))
  )
  (* TODO really, we would like to have this stronger spec that looses less information.
      However, some parts of the type system (e.g. enum initialization) cannot deal well yet with moving in values again. *)
    (*→ ∃ vs : val, vs @ value_t (T_ty.(ty_syn_type)); λ π,*)
      (*(l ◁ₗ[π, Owned false] PlaceIn vs @ (◁ value_t (T_ty.(ty_syn_type)))) ∗*)
      (*vs ◁ᵥ{π} r @ T_ty*)
    → ∃ () : unit, r @ T_ty; λ π,
      (l ◁ₗ[π, Owned false] .@ (◁ uninit (T_ty.(ty_syn_type))))
      (*vs ◁ᵥ{π} r @ T_ty*)
.

Lemma ptr_read_typed `{!typeGS Σ} π T_rt T_st T_ly :
  syn_type_has_layout T_st T_ly →
  ⊢ typed_function π (ptr_read T_st) [T_st] (type_of_ptr_read T_rt T_st).
Proof.
  start_function "ptr_read" ( () ) ( [[T_ty l] r] ).
  (* locally override the instance used for moves *)

  liRStepUntil (typed_read_end).
  iApply type_read_ofty_move_owned_value.
  liFromSyntax.
  repeat liRStep; liShow.
  Unshelve. all: unshelve_sidecond; sidecond_hook.
  Unshelve. all: unfold_common_defs; solve_goal.
Qed.

(*assert_unsafe_precondition!(is_aligned_and_not_null(src) && is_aligned_and_not_null(dst));*)
(* "`copy` is semantically equivalent to C's [`memmove`], but with the argument
    order swapped. Copying takes place as if the bytes were copied from `src`
    to a temporary array and then copied from the array to `dst`."
   We take this literally and create a new temporary allocation.
*)
Definition ptr_copy `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [("src", void* ); ("dst", void* ); ("count", usize_t : layout)];
  f_local_vars := [("tmp", void* )];
  f_code :=
    <["_bb0" :=
      (*"tmp" <-{PtrOp} All*)
      return zst_val
    ]>%E $
    ∅;
  f_init := "_bb0";
|}.

(* TODO *)
Definition sublist_lookup' {A} (i n : nat) (l : list A) := take n (drop i l).
Definition ptr_copy_result {A} (off_src : Z) (off_dst : Z) (count : nat) (xs : list (place_rfn (option A))) :=
  let wipe_src := list_inserts (Z.to_nat off_src) (replicate count (#None)) xs in
  let ins_dst := list_inserts (Z.to_nat off_dst) (sublist_lookup' (Z.to_nat off_src) count xs) wipe_src in
  ins_dst.

(* This spec really relies on the fact that the core type system does not usually disassemble arrays, but keeps them as one chunk in the context. *)
(* (Of course, ptr::copy_nonoverlapping is an exception) *)
Definition type_of_ptr_copy `{!typeGS Σ} (T_rt : Type) (T_st : syn_type) :=
  fn(∀ () : 0 | (T_ty, l, off_src, off_dst, count, len, xs) : (type T_rt * loc * Z * Z * Z * nat * list (place_rfn (option (place_rfn T_rt)))), (λ ϝ, []);
    (l, off_src) @ offset_ptr_t T_st,
    (l, off_dst) @ offset_ptr_t T_st,
    count @ int usize_t; λ π,
    ⌜T_st = ty_syn_type T_ty⌝ ∗
    (l ◁ₗ[π, Owned false] (#xs) @ (◁ array_t (maybe_uninit T_ty) len)) ∗
    ⌜(0 ≤ count)%Z⌝ ∗
    ⌜0 ≤ off_src⌝ ∗
    ⌜0 ≤ off_dst⌝ ∗
    ⌜(off_src + count < len)%Z⌝ ∗
    ⌜(off_dst + count < len)%Z⌝)
  → ∃ () : unit, () @ unit_t; λ π,
    l ◁ₗ[π, Owned false] (#(ptr_copy_result off_src off_dst (Z.to_nat count) xs)) @ (◁ array_t (maybe_uninit T_ty) len).

Lemma ptr_copy_typed `{!typeGS Σ} π (T_rt : Type) (T_st : syn_type) (T_ly : layout) :
  syn_type_has_layout T_st T_ly →
  ⊢ typed_function π (ptr_copy T_st) [PtrSynType] (type_of_ptr_copy T_rt T_st).
Proof.
Abort.

(** ptr::invalid *)
(* Our implementation does not actually do anything with the type parameter, it's just there to mirror the Rust API. *)
Definition ptr_invalid `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [("align", usize_t : layout)];
  f_local_vars := [];
  f_code :=
    <["_bb0" :=
      return (UnOp (CastOp PtrOp) (IntOp usize_t) (UnOp EraseProv (UntypedOp usize_t) (use{IntOp usize_t} "align")))
    ]>%E $
    ∅;
  f_init := "_bb0";
|}.
Definition type_of_ptr_invalid `{!typeGS Σ} (T_rt : Type) (T_st : syn_type) :=
  fn(∀ () : 0 | (n) : nat, (λ ϝ, []); Z.of_nat n @ int usize_t; λ π, ⌜(min_alloc_start ≤ n)%Z ∧ (n ≤ max_alloc_end)%Z⌝)
    → ∃ l : loc, l @ alias_ptr_t; (λ π, ⌜name_hint "Ha" (l `aligned_to` n)⌝ ∗ l ◁ₗ[π, Owned false] .@ ◁ unit_t).
Lemma ptr_invalid_typed `{!typeGS Σ} π T_rt T_st T_ly :
  syn_type_has_layout T_st T_ly →
  ⊢ typed_function π (ptr_invalid T_st) [] (type_of_ptr_invalid T_rt T_st).
Proof.
  intros.
  start_function "ptr_invalid" ( () ) ( n ) => l.
  repeat liRStep. liShow.
  (* EraseProv *)
  rewrite /typed_un_op/typed_val_expr.
  iIntros "Hv" (Φ) "#CTX #HE HL Hna Hcont".
  rewrite {1}/ty_own_val /=. iDestruct "Hv" as %[Hv Hsz].
  iApply wp_erase_prov.
  { rewrite /has_layout_val. erewrite (val_to_Z_ot_length _ (IntOp usize_t)); done. }
  iApply  ("Hcont" $! _ _ _ (int usize_t) n with "HL Hna []").
  { rewrite /ty_own_val/=. iSplit; last done. iPureIntro. by apply val_to_Z_erase_prov. }

  iIntros "Hv" (Φ') "_ _ HL Hna Hcont".
  rewrite {1}/ty_own_val /=. iDestruct "Hv" as %[Hv' _].
  iApply wp_cast_int_ptr_prov_none; [done | done | done | | done | ].
  { apply val_to_byte_prov_erase_prov. }
  iIntros "!> Hl Hcred".
  iApply ("Hcont" $! _ _ _ (alias_ptr_t) _ with "HL Hna").
  { rewrite /ty_own_val /=. done. }
  iAssert (val_of_loc (ProvAlloc None, n : addr) ◁ᵥ{π} (ProvAlloc None, n : addr) @ alias_ptr_t)%I as "?".
  { rewrite /ty_own_val /= //. }
  iAssert ((ProvAlloc None, n : addr) ◁ₗ[π, Owned false] .@ ◁ unit_t)%I with "[Hl]" as "?".
  { rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iExists _. simpl. iSplitR; first done.
    iSplitR. { iPureIntro. rewrite /has_layout_loc/aligned_to.
      destruct caesium_config.enforce_alignment; last done.
      eapply Z.divide_1_l. }
    iSplitR; first done.
    iPoseProof (heap_mapsto_loc_in_bounds with "Hl") as "#Hlb".
    iSplitR; first done. iSplitR; first done.
    iExists (). iSplitR; first done.
    iModIntro. iExists []. iFrame. rewrite /ty_own_val /= //. }

  repeat liRStep; liShow.

  Unshelve.
  all: unshelve_sidecond; sidecond_hook.
  all: unfold_common_defs; solve_goal.
Qed.

(** inspired by NonNull::dangling *)
Definition ptr_dangling `{!LayoutAlg} (T_st : syn_type) (mem_align_of_loc : loc) (ptr_invalid_loc : loc) : function := {|
  f_args := [];
  f_local_vars := [("align", usize_t : layout)];
  f_code :=
    <["_bb0" :=
      "align" <-{IntOp usize_t} CallE mem_align_of_loc [] [@{expr} ];
      return (CallE ptr_invalid_loc [] [@{expr} use{IntOp usize_t} "align"])
    ]>%E $
    ∅;
  f_init := "_bb0";
|}.
Definition type_of_ptr_dangling `{!typeGS Σ} (T_rt : Type) (T_st : syn_type) :=
  fn(∀ () : 0 | () : unit, (λ ϝ, []); λ π, True)
    → ∃ (l) : loc, l @ alias_ptr_t; λ π, ⌜l `has_layout_loc` (use_layout_alg' T_st)⌝ ∗
      (l ◁ₗ[π, Owned false] .@ ◁ (uninit UnitSynType)) ∗ freeable_nz l 0 1 HeapAlloc.
Lemma ptr_dangling_typed `{!typeGS Σ} π T_rt T_st T_ly mem_align_of_loc ptr_invalid_loc :
  syn_type_has_layout T_st T_ly →
  mem_align_of_loc ◁ᵥ{π} mem_align_of_loc @ function_ptr [] (type_of_mem_align_of T_rt T_st) -∗
  ptr_invalid_loc ◁ᵥ{π} ptr_invalid_loc @ function_ptr [IntSynType usize_t] (type_of_ptr_invalid T_rt T_st) -∗
  typed_function π (ptr_dangling T_st mem_align_of_loc ptr_invalid_loc) [IntSynType usize_t] (type_of_ptr_dangling T_rt T_st).
Proof.
  start_function "ptr_dangling" ( () ) ( () ) => l_align.
  init_lfts (∅).
  repeat liRStep; liShow.
  Unshelve.
  all: unshelve_sidecond; sidecond_hook.
  Unshelve. all: solve_goal.
Qed.


(** mut_ptr::offset / const_ptr::offset *)
Definition ptr_offset `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [("self", void* ); ("count", isize_t : layout)];
  f_local_vars := [];
  f_code :=
    <["_bb0" :=
      return ((use{PtrOp} "self") at_offset{use_layout_alg' T_st, PtrOp, IntOp isize_t} (use{IntOp isize_t} "count"))
    ]>%E $
    ∅;
  f_init := "_bb0"
|}.

Inductive trace_offset :=
  | TraceOffset (offset : Z).

Definition type_of_ptr_offset `{!typeGS Σ} (T_rt : Type) (T_st : syn_type) :=
  fn(∀ () : 0 | (l, offset) : loc * Z, (λ ϝ, []); l @ alias_ptr_t, (offset) @ int isize_t; λ π,
    ⌜l `has_layout_loc` (use_layout_alg' T_st)⌝ ∗
    ⌜(offset * size_of_st T_st)%Z ∈ isize_t⌝ ∗
    case_destruct (bool_decide (offset < 0))%Z
      (λ b _, if b then loc_in_bounds l (Z.to_nat (-offset) * size_of_st T_st) 0 else loc_in_bounds l 0 (Z.to_nat offset * size_of_st T_st))

    (*loc_in_bounds l*)
      (*(if bool_decide (offset < 0)%Z then Z.to_nat (-offset) * size_of_st T_st else 0)*)
      (*(if bool_decide (offset > 0)%Z then Z.to_nat offset * size_of_st T_st else 0)*)
  ) →
  ∃ () : unit, (l offsetst{T_st}ₗ offset) @ alias_ptr_t; λ π, £ (S (num_laters_per_step 1)) ∗ atime 1.

Lemma ptr_offset_typed `{!typeGS Σ} π T_rt T_st T_ly :
  syn_type_has_layout T_st T_ly →
  ⊢ typed_function π (ptr_offset T_st) [] (type_of_ptr_offset T_rt T_st).
Proof.
  intros.
  start_function "ptr_offset" ( () ) ( [l offset] ) => l_self l_count.
  init_lfts ∅.
  repeat liRStep. liShow.
  liFromSyntax.
  iIntros "Hbounds".
  (* do the actual offset *)
  iAssert (loc_in_bounds l (if (decide (offset < 0)) then (Z.to_nat (-offset) * size_of_st T_st)%nat else 0%nat) (if decide (offset > 0)%Z then (Z.to_nat offset * size_of_st T_st)%nat else 0%nat))%I with "[Hbounds]" as "#Hbounds'" .
  { rewrite /case_if.
    case_decide; case_decide; case_bool_decide; eauto with lia.
    iApply (loc_in_bounds_shorten_suf with "[Hbounds //]"). lia. }
  repeat liRStep; liShow.
  rewrite /typed_bin_op/typed_val_expr.
  iIntros "Hv1 Hv2" (Φ) "#CTX #HE HL Hna Hcont".
  rewrite {1}/ty_own_val /=. iDestruct "Hv1" as %[Hv1 Hsz1].
  rewrite {1}/ty_own_val /=. iDestruct "Hv2" as "->".
  iDestruct (loc_in_bounds_ptr_in_range with "Hbounds'") as %[Hran1 Hran2].
  rewrite /size_of_st. simplify_layout_goal.
  iRename select (credit_store _ _) into "Hstore".
  iPoseProof (credit_store_borrow_receipt with "Hstore") as "(Hat & Hatcl)".
  iDestruct "CTX" as "(LFT & TIME & LLCTX)".
  iMod (persistent_time_receipt_0) as "Hp".
  iApply (wp_ptr_offset_credits with "TIME Hat Hp").
  { done. }
  { apply val_to_of_loc. }
  { done. }
  { split; simplify_layout_goal; rewrite -?MinInt_eq -?MaxInt_eq; lia. }
  { rewrite /offset_loc. fold (size_of_st T_st).
    iApply (loc_in_bounds_offset with "Hbounds'").
    { done. }
    { destruct l; simpl. clear Hran2. case_decide; lia. }
    { destruct l; simpl. clear Hran1. case_decide; lia. }
  }
  { iApply (loc_in_bounds_offset with "Hbounds'"); [ done | | ].
    { clear Hran2. case_decide; lia. }
    { clear Hran1. case_decide; lia. }
  }
  iNext. simpl. iEval (rewrite additive_time_receipt_succ). iIntros "Hcred [Hat Hat']".
  iPoseProof ("Hatcl" with "Hat'") as "Hstore".
  iPoseProof (credit_store_donate with "Hstore Hcred") as "Hstore".
  iPoseProof (credit_store_donate_atime with "Hstore Hat") as "Hstore".
  iApply ("Hcont" $! _ _ _ (alias_ptr_t) with "HL Hna").
  { rewrite /ty_own_val /=. done. }
  iAssert ((l offset{use_layout_alg' T_st}ₗ offset) ◁ᵥ{ π} l offset{use_layout_alg' T_st}ₗ offset @ alias_ptr_t)%I as "?".
  { rewrite /ty_own_val /= //. }

  repeat liRStep; liShow.

  Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
  Unshelve. all: unfold_common_defs; solve_goal.
Qed.

Definition ptr_add `{!LayoutAlg} (T_st : syn_type) (ptr_offset_loc : loc) : function := {|
  f_args := [("self", void* ); ("count", usize_t : layout)];
  f_local_vars := [];
  f_code :=
    <["_bb0" :=
      (* cast the usize to isize *)
      return (CallE ptr_offset_loc [] [@{expr} use{PtrOp} "self"; UnOp (CastOp (IntOp isize_t)) (IntOp usize_t) use{IntOp usize_t} "count"])
    ]>%E $
    ∅;
  f_init := "_bb0";
|}.

Definition type_of_ptr_add `{!typeGS Σ} (T_rt : Type) (T_st : syn_type) :=
  fn(∀ () : 0 | (l, offset) : loc * Z, (λ ϝ, []); l @ alias_ptr_t, (offset) @ int usize_t; λ π,
    ⌜l `has_layout_loc` (use_layout_alg' T_st)⌝ ∗
    ⌜(offset * size_of_st T_st)%Z ∈ isize_t⌝ ∗
    loc_in_bounds l 0 ((Z.to_nat offset) * size_of_st T_st)
  ) →
  ∃ () : unit, (l, offset) @ offset_ptr_t T_st; λ π, £ (S (num_laters_per_step 1)) ∗ atime 1.

(* TODO move *)
Lemma wrap_to_int_id' z it :
  z ∈ it → wrap_to_it z it = z.
Proof. rewrite int_elem_of_it_iff. apply wrap_to_int_id. Qed.

Lemma ptr_add_typed `{!typeGS Σ} π T_rt T_st T_ly ptr_offset_loc :
  syn_type_has_layout T_st T_ly →
  ptr_offset_loc ◁ᵥ{π} ptr_offset_loc @ function_ptr [PtrSynType; IntSynType isize_t] (type_of_ptr_offset T_rt T_st) -∗
  typed_function π (ptr_add T_st ptr_offset_loc) [] (type_of_ptr_add T_rt T_st).
Proof.
  intros.
  start_function "mut_ptr_add" ( () ) ( [l offset] ) => l_self l_count.
  init_lfts ∅.
  repeat liRStep; liShow.
  Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.

  (* basically, the reasoning is:
      - if T is a ZST, then the wrapped offset gets annihilated everywhere, so it's fine.
      - else, we also know that it's in isize_t, so it's same as before.
    *)
  4,6: rewrite /OffsetLocSt; simplify_layout (use_layout_alg' T_st); do 2 f_equiv.
  all: destruct (decide (ly_size T_st_ly = 0%nat));
    [ lia | assert (MinInt isize_t ≤ offset ≤ MaxInt isize_t)%Z by solve_goal with nia; prepare_sideconditions; normalize_and_simpl_goal; try (unfold_common_defs; solve_goal)].
  all: rewrite wrap_to_int_id'.
  all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; try (unfold_common_defs; solve_goal).
  Unshelve. all: unfold_common_defs; solve_goal.
Qed.

Definition ptr_is_null `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [("self", void* )];
  f_local_vars := [];
  f_code :=
    <["_bb0" :=
      return (use{PtrOp} "self" = {PtrOp, PtrOp, u8} NULL)
    ]>%E $
    ∅;
  f_init := "_bb0";
|}.
Definition type_of_ptr_is_null `{!typeGS Σ} (T_rt : Type) (T_st : syn_type) :=
  fn(∀ () : 0 | (l) : loc, (λ ϝ, []); l @ alias_ptr_t; λ π, True) → ∃ b : bool, b @ bool_t; λ π, ⌜b = bool_decide (l.2 = 0)⌝.
(* TODO should maybe adapt pointer comparison semantics beforehand, because Caesium currently requires the loc_in_bounds stuff for comparison. *)
(* TODO should also have some automation to learn things - i.e. gain knowledge that b = false in case we actually have ownership *)




(** Allocator API *)
(*
  how do we specify allocations?
  - option 1: have an owned_ptr type (essentially box, but without the deallocation permission) and keep the deallocation permission external
  - option 2: just return a box (this is a bit of a red herring, since it really would not be a Rust Box)
  - option 3: have an allocation_t type that also deals with the additional flexibility for freeable permissions we will need for gathering stuff for reallocation.
      + we need this anyways, but can we also use it here?
      => work this out in detail first, then decide here.
  - option 4: use ofty + value
    => Going with this.
 *)

Definition alloc_alloc `{!LayoutAlg} : function := {|
  f_args := [("size", usize_t : layout); ("align_log2", usize_t : layout)];
  f_local_vars := [];
  f_code :=
    <["_bb0" :=
      return (Alloc (use{IntOp usize_t} "size") (use{IntOp usize_t} "align_log2"))
    ]>%E $
    ∅;
  f_init := "_bb0";
 |}.
Definition type_of_alloc_alloc `{!typeGS Σ} :=
  fn(∀ () : 0 | (size, align_log2) : (Z * Z), (λ ϝ, []); size @ int usize_t, align_log2 @ int usize_t; λ π,
    ⌜size ∈ isize_t⌝ ∗ ⌜(size > 0)%Z⌝ ∗
    (* TODO: this restriction would not be necessary, but needed because the layout algorithm requires it. Can we lift this? *)
    ⌜layout_wf (Layout (Z.to_nat size) (Z.to_nat align_log2))⌝ ∗
    ⌜ly_align_in_bounds (Layout (Z.to_nat size) (Z.to_nat align_log2))⌝
  ) →
  ∃ (l) : loc, l @ alias_ptr_t; λ π,
      l ◁ₗ[π, Owned false] .@ (◁ (uninit (UntypedSynType (Layout (Z.to_nat size) (Z.to_nat align_log2))))) ∗
      (*l ◁ₗ[π, Owned false] #v @ (◁ (value_t (UntypedSynType (Layout (Z.to_nat size) (Z.to_nat align_log2))))) ∗*)
      freeable_nz l (Z.to_nat size) 1 HeapAlloc.
Lemma alloc_alloc_typed `{!typeGS Σ} π :
  ⊢ typed_function π alloc_alloc [] (type_of_alloc_alloc).
Proof.
  Local Typeclasses Opaque layout_wf.
  start_function "alloc_alloc" ( () ) ( [size align_log2] ) => l_size l_align_log2.
  repeat liRStep. liShow.

  (* do the alloc *)
  typed_val_expr_bind. repeat liRStep; liShow.
  typed_val_expr_bind. repeat liRStep; liShow.
  iSelect (_ ◁ᵥ{_} size @ _)%I (fun H => iRename H into "Hsize").
  iSelect (_ ◁ᵥ{_} align_log2 @ _)%I (fun H => iRename H into "Halign_log2").
  rewrite {1 2}/ty_own_val /=. iDestruct "Hsize" as "[%Hsize _]".
  iDestruct "Halign_log2" as "[%Halign_log2 _]".
  rewrite /typed_val_expr.
  iIntros (Φ) "#CTX HE HL Hna Hcont".
  iApply (wp_alloc _ _ _ _ (Z.to_nat size) (Z.to_nat align_log2)).
  { rewrite Hsize. f_equiv.
    apply val_to_Z_unsigned_nonneg in Hsize; last done. lia. }
  { rewrite Halign_log2. f_equiv.
    apply val_to_Z_unsigned_nonneg in Halign_log2; last done. lia. }
  { lia. }
  iIntros "!>" (l) "Hl Hf %Hly Hcred".
  iApply ("Hcont" $! _ _ _ (alias_ptr_t) l with "HL Hna []").
  { rewrite /ty_own_val /=. done. }
  set (ly := (Layout (Z.to_nat size) (Z.to_nat align_log2))).
  iAssert (l ◁ₗ[π, Owned false] .@ ◁ (uninit (UntypedSynType ly)))%I with "[Hl]" as "Hl'".
  { rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    assert (syn_type_has_layout (UntypedSynType ly) ly) as Hly'.
    { solve_layout_alg. }
    iExists ly. simpl. iSplitR; first done.
    iSplitR; first done. iSplitR; first done.
    iPoseProof (heap_mapsto_loc_in_bounds with "Hl") as "#Hlb".
    iSplitR. { rewrite replicate_length /ly /ly_size /=. done. }
    iSplitR; first done.
    iExists tt. iSplitR; first done.
    iModIntro. iExists _. iFrame. rewrite uninit_own_spec. iExists ly.
    iSplitR; first done. iPureIntro. rewrite /has_layout_val replicate_length /ly /ly_size //. }

  iRevert "Hf".

  repeat liRStep; liShow.
  Unshelve. all: unshelve_sidecond; sidecond_hook.
  Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
Qed.

Notation "'free{' e_size ',' e_align '}' e_ptr ; s" := (Free e_size%E e_align%E e_ptr%E s%E)
  (at level 80, s at level 200, format "'[v' 'free{' e_size ','  e_align '}'  e_ptr ';' '/' s ']'") : expr_scope.
Definition alloc_dealloc `{!LayoutAlg} : function := {|
  f_args := [("size", usize_t : layout); ("align", usize_t : layout); ("ptr", void* )];
  f_local_vars := [];
  f_code :=
    <["_bb0" :=
      free{ use{IntOp usize_t} "size", use{IntOp usize_t} "align"} (use{PtrOp} "ptr");
      return zst_val
    ]>%E $
    ∅;
  f_init := "_bb0";
|}.

Definition type_of_alloc_dealloc `{!typeGS Σ} :=
  fn(∀ () : 0 | (size, align_log2, ptr) : (Z * Z * loc), (λ ϝ, []); size @ int usize_t, align_log2 @ int usize_t, ptr @ alias_ptr_t; λ π,
    freeable_nz ptr (Z.to_nat size) 1 HeapAlloc ∗
    ⌜(0 < size)%Z⌝ ∗
    ptr ◁ₗ[π, Owned false] .@ (◁ (uninit (UntypedSynType (Layout (Z.to_nat size) (Z.to_nat align_log2))))) ) →
  ∃ () : unit, () @ unit_t; λ π, True.

Lemma alloc_dealloc_typed `{!typeGS Σ} π :
  ⊢ typed_function π alloc_dealloc [] (type_of_alloc_dealloc).
Proof.
  start_function "alloc_dealloc" ( () ) ( [[size align_log2] ptr] ) => l_size l_align_log2 l_ptr.
  repeat liRStep. liShow.

  (* do the free *)
  typed_stmt_bind. repeat liRStep; liShow.
  typed_stmt_bind. repeat liRStep; liShow.
  typed_stmt_bind. repeat liRStep; liShow.
  iSelect (_ ◁ᵥ{_} size @ _)%I (fun H => iRename H into "Hsize").
  iSelect (_ ◁ᵥ{_} align_log2 @ _)%I (fun H => iRename H into "Halign_log2").
  iSelect (ptr ◁ₗ[_, _] _ @ _)%I (fun H => iRename H into "Hptr").
  iSelect (freeable_nz _ _ _ _) (fun H => iRename H into "Hfree").
  rewrite {1 2}/ty_own_val /=. iDestruct "Hsize" as "[%Hsize _]".
  iDestruct "Halign_log2" as "[%Halign_log2 _]".

  rewrite /typed_stmt.
  iIntros (?) "#CTX #HE HL Hna Hcont".
  rewrite ltype_own_ofty_unfold /lty_of_ty_own. simpl.
  set (ly := Layout (Z.to_nat size) (Z.to_nat align_log2)).
  iDestruct "Hptr" as "(%ly' & %Hst & %Hly & _ & #Hlb & _ & %r' & <- & Hb)".
  specialize (syn_type_has_layout_untyped_inv _ _ Hst) as (-> & ? & ?).
  iMod (fupd_mask_mono with "Hb") as "Hb"; first done.
  iDestruct "Hb" as "(%v' & Hptr & Hv')".
  iPoseProof (ty_own_val_has_layout with "Hv'") as "%Hlyv'"; first done.

  iApply (wps_free _ _ _ ptr _ _ (Z.to_nat size) (Z.to_nat align_log2) with "[Hptr] [Hfree]").
  { rewrite Hsize. f_equiv.
    apply val_to_Z_unsigned_nonneg in Hsize; last done. lia. }
  { rewrite Halign_log2. f_equiv.
    apply val_to_Z_unsigned_nonneg in Halign_log2; last done. lia. }
  { lia. }
  { iExists _. iFrame. fold ly. done. }
  { rewrite /freeable_nz.
    destruct ((Z.to_nat size)) eqn:Heq; first lia. done. }
  iIntros "!> Hcred".

  to_typed_stmt "CTX HE HL Hna Hcont".
  (* TODO *)
  instantiate (1 := ϝ).
  repeat liRStep; liShow.

  Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
  Unshelve. all: unfold_common_defs; solve_goal.
Qed.

(**
  fn alloc_realloc(old_size, align, new_size, ptr) -> *mut u8 {
    let new_ptr = alloc::alloc(new_size, align);
    copy_nonoverlapping(ptr, new_ptr, min(old_size, new_size));
    alloc::dealloc(old_size, align, ptr);
    new_ptr
  }
*)
Definition alloc_realloc `{!LayoutAlg} (alloc_alloc_loc : loc) (copy_nonoverlapping_loc : loc) (alloc_dealloc_loc : loc) : function := {|
  f_args := [("old_size", usize_t : layout); ("align", usize_t : layout); ("new_size", usize_t : layout); ("ptr", void* )];
  f_local_vars := [("new_ptr", void* ); ("min_size", usize_t : layout)];
  f_code :=
    <["_bb0" :=
      "new_ptr" <-{PtrOp} CallE alloc_alloc_loc [] [@{expr} use{IntOp usize_t} "new_size"; use{IntOp usize_t} "align"];
      "min_size" <-{IntOp usize_t} (IfE BoolOp (use{IntOp usize_t} "new_size" <{IntOp usize_t, IntOp usize_t, u8} use{IntOp usize_t} "old_size") (use{IntOp usize_t} "new_size") (use{IntOp usize_t} "old_size"));
      annot: StopAnnot;
      expr: CallE copy_nonoverlapping_loc [] [@{expr} use{IntOp usize_t} "min_size"; use{PtrOp} "ptr"; use{PtrOp} "new_ptr"];
      expr: CallE alloc_dealloc_loc [] [@{expr} use{IntOp usize_t} "old_size"; use{IntOp usize_t} "align"; use{PtrOp} "ptr"];
      return (use{PtrOp} "new_ptr")
    ]>%E $
    ∅;
  f_init := "_bb0";
|}.


#[global] Typeclasses Opaque layout_wf.

Definition type_of_alloc_realloc `{!typeGS Σ} :=
  fn(∀ () : 0 | (old_size, align_log2, new_size, ptr_old, v) : (Z * Z * Z * loc * val), (λ ϝ, []); old_size @ int usize_t, align_log2 @ int usize_t, new_size @ int usize_t, ptr_old @ alias_ptr_t; λ π,
    (* TODO restriction of the spec: we cannot shrink it *)
    ⌜(old_size ≤ new_size)%Z⌝ ∗
    ⌜(0 < old_size)%Z⌝ ∗
    ⌜new_size ≤ MaxInt isize_t⌝ ∗
    (* TODO: restriction placed by our syntype model, not required in Rust *)
    ⌜layout_wf (Layout (Z.to_nat new_size) (Z.to_nat align_log2))⌝ ∗
    (*⌜ly_align_in_bounds (Layout (Z.to_nat new_size) (Z.to_nat align_log2))⌝ ∗*)
    (*⌜layout_wf (Layout (Z.to_nat old_size) (Z.to_nat align_log2))⌝ ∗*)
    ptr_old ◁ₗ[π, Owned false] PlaceIn v @ (◁ value_t (UntypedSynType (Layout (Z.to_nat old_size) (Z.to_nat align_log2)))) ∗
    freeable_nz ptr_old (Z.to_nat old_size) 1 HeapAlloc) →
  ∃ (ptr_new, v') : (loc * val), ptr_new @ alias_ptr_t; λ π,
    freeable_nz ptr_new (Z.to_nat new_size) 1 HeapAlloc ∗
    ptr_new ◁ₗ[π, Owned false] #(v ++ v') @ (◁ value_t (UntypedSynType (Layout (Z.to_nat new_size) (Z.to_nat align_log2)))) ∗
    ⌜v' `has_layout_val` (Layout (Z.to_nat (new_size - old_size)) (Z.to_nat align_log2))⌝
.
#[global] Typeclasses Opaque Z.divide.
Lemma alloc_realloc_typed `{!typeGS Σ} π alloc_alloc_loc copy_nonoverlapping_loc alloc_dealloc_loc :
  alloc_alloc_loc ◁ᵥ{π} alloc_alloc_loc @ function_ptr [IntSynType usize_t; IntSynType usize_t] (type_of_alloc_alloc) -∗
  copy_nonoverlapping_loc ◁ᵥ{π} copy_nonoverlapping_loc @ function_ptr [IntSynType usize_t; PtrSynType; PtrSynType] (type_of_copy_nonoverlapping Z (IntSynType u8)) -∗
  alloc_dealloc_loc ◁ᵥ{π} alloc_dealloc_loc @ function_ptr [IntSynType usize_t; IntSynType usize_t; PtrSynType] (type_of_alloc_dealloc) -∗
  typed_function π (alloc_realloc alloc_alloc_loc copy_nonoverlapping_loc alloc_dealloc_loc) [PtrSynType; IntSynType usize_t] type_of_alloc_realloc.
Proof.
  start_function "alloc_realloc" ( () ) ( [[[[old_size align_log2] new_size] ptr_old] v_old] ) => l_old_size l_align_log2 l_new_size l_ptr_old l_ptr_new l_min_size.
  init_lfts ∅.
  set (old_ly := Layout (Z.to_nat old_size) (Z.to_nat align_log2)).
  set (new_ly := Layout (Z.to_nat new_size) (Z.to_nat align_log2)).
  repeat liRStep. liShow.
  fold old_ly new_ly.
  (* augment context with layout well-formedness info *)
  iRename select (ptr_old ◁ₗ[_, _] _ @ _)%I into "Hold".
  iRename select (x' ◁ₗ[_, _] _ @ _)%I into "Hnew".
  iPoseProof (ltype_own_has_layout with "Hold") as "(%ly_old & %Halg_old & %)".
  iPoseProof (ltype_own_has_layout with "Hnew") as "(%ly_new & %Halg_new & %)".
  simp_ltypes in Halg_old. apply syn_type_has_layout_untyped_inv in Halg_old as (-> & ? & ?).
  simp_ltypes in Halg_new. apply syn_type_has_layout_untyped_inv in Halg_new as (-> & _ & _).

  iApply typed_stmt_annot_skip.
  liRStepUntil (typed_call).
  (* make into value, because the part not affected by the memcpy will be returned *)
  iRename select (x' ◁ₗ[_, _] .@ _)%I into "Hnew".

  (* The copy_nonoverlapping does a bytewise copy, so we need to convert it into an "array" of bytes *)
  iApply fupd_typed_call.
  iMod (ofty_uninit_to_value with "Hnew") as "(%vn & Hnew)"; first done.
  iMod (ofty_value_has_length with "Hnew") as "(%Hlen & Hnew)"; [done | | ].
  { eapply syn_type_has_layout_untyped; [done.. | | done]. rewrite /ly_size/=. lia. }
  iPoseProof (ofty_value_untyped_to_bytes with "Hnew") as "Hnew".
  iMod (ofty_value_untyped_split_app_array _ _ _ _ (ly_size new_ly - ly_size old_ly) (ly_size old_ly)  with "Hnew") as "(Hnew1 & Hnew2)"; first done.
  { simpl. lia. }
  { rewrite /layout_wf/ly_align/it_layout. simpl. apply Z.divide_1_l. }
  simpl. rewrite !Nat.add_0_r.
  iModIntro.

  repeat liRStep; liShow.
  rewrite Nat.add_0_r.
  assert ((x' offset{u8}ₗ Z.to_nat old_size) = x' +ₗ Z.to_nat old_size) as ->.
  { rewrite /offset_loc. rewrite /ly_size/=/bytes_per_int/=.
    f_equiv. lia. }
  liInst Hevar1 (mk_array_layout u8 (Z.to_nat new_size - Z.to_nat old_size)).
  repeat liRStep; liShow.

  Unshelve. all: unshelve_sidecond; sidecond_hook.
  Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; try (unfold_common_defs; solve_goal); unsolved_sidecond_hook.
  { rewrite /has_layout_loc/layout_wf/aligned_to /ly_align/u8/=. destruct caesium_config.enforce_alignment; last done. apply Z.divide_1_l. }
  { rewrite /has_layout_loc/layout_wf/aligned_to /ly_align/u8/=. destruct caesium_config.enforce_alignment; last done. apply Z.divide_1_l. }
  { rewrite /has_layout_val drop_length/=. rewrite Hlen/new_ly/ly_size/=.  lia.  }
Qed.




(** Box API *)
Definition box_new `{!LayoutAlg} (T_st : syn_type) (mem_size_of_T_loc : loc) (ptr_dangling_T_loc : loc) : function := {|
 f_args := [("x", use_layout_alg' T_st)];
 f_local_vars := [
   ("__0", void* : layout);
   ("size", usize_t : layout)
 ];
 f_code :=
  <["_bb0" :=
   (* check if the size is 0 *)
   "size" <-{IntOp usize_t} CallE mem_size_of_T_loc [] [@{expr} ];
   if{BoolOp}: use{IntOp usize_t} "size" = {IntOp usize_t, IntOp usize_t, u8} I2v 0 USize
   then Goto "_bb1"
   else Goto "_bb2"
  ]>%E $
  <["_bb2" :=
   (* non-ZST, do an actual allocation *)
   (* TODO maybe call alloc_alloc here? *)
   "__0" <-{ PtrOp } box{ T_st };
   !{ PtrOp } "__0" <-{ use_op_alg' T_st } (use{use_op_alg' T_st} "x");
   return (use{ PtrOp } ("__0"))
  ]>%E $
  <["_bb1" :=
    (* ZST, use a dangling pointer *)
    "__0" <-{PtrOp} CallE ptr_dangling_T_loc [] [@{expr} ];
    annot: StopAnnot;
    (* do a zero-sized write - this is fine *)
    !{ PtrOp } "__0" <-{ use_op_alg' T_st } (use{use_op_alg' T_st} "x");
    return (use{PtrOp} "__0")
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.

Definition type_of_box_new `{!typeGS Σ} T_rt T_st :=
  fn(∀ () : 0 | (T, x) : type T_rt * T_rt, (λ ϝ, []); x @ T; λ π, ⌜ty_syn_type T = T_st⌝ ∗ ⌜ty_allows_reads T⌝ ∗ ⌜ty_allows_writes T⌝)
    → ∃ () : (), PlaceIn x @ box T; λ π, True.
Lemma box_new_typed `{!typeGS Σ} π T_st (T_rt : Type) (mem_size_of_T_loc ptr_dangling_T_loc : loc) :
  syn_type_is_layoutable T_st →
  mem_size_of_T_loc ◁ᵥ{π} mem_size_of_T_loc @ function_ptr [] (type_of_mem_size_of T_rt T_st) -∗
  ptr_dangling_T_loc ◁ᵥ{π} ptr_dangling_T_loc @ function_ptr [] (type_of_ptr_dangling T_rt T_st) -∗
  typed_function π (box_new T_st mem_size_of_T_loc ptr_dangling_T_loc) [PtrSynType; IntSynType usize_t] (type_of_box_new T_rt T_st).
Proof.
  start_function "box_new" ( () ) ( (T, x) ) => arg_x local_0 local_size.
  init_tyvars (<["T" := existT _ T]> ∅).
  init_lfts ∅.
  repeat liRStep; liShow.
  - (* zero branch *)
    (* TODO maybe use place instance for alias_ptr instead of manually wrapping up the pointsto *)
    iRename select (credit_store _ _) into "Hstore".
    iPoseProof (credit_store_borrow_receipt with "Hstore") as "(Hat & Hcl_store)".

    iApply (typed_stmt_annot_credits with "Hat").
    iIntros "Hat Hcred".
    rewrite lc_succ. iDestruct "Hcred" as "(Hcred1 & Hcred)".
    rewrite (additive_time_receipt_succ 1). iDestruct "Hat" as "(Hat1 & Hat)".
    iPoseProof ("Hcl_store" with "Hat") as "Hstore".

    (* make a box type out of the alias_ptr *)
    iSelect (_ ◁ₗ[_, _] _ @ ◁ (uninit UnitSynType))%I (fun H => iRename H into "H_pts").
    iSelect (local_0 ◁ₗ[_, _] _ @ _)%I (fun H => iRename H into "H_0").
    iAssert (local_0 ◁ₗ[π, Owned false] #(#())  @ ◁ box (uninit (ty_syn_type T)))%I with "[H_pts H_0 Hcred Hat1]" as "H_0".
    { iApply (ofty_owned_subtype_aligned with "[-H_0] H_0").
      { solve_layout_alg. }
      { done. }
      iSplitR. { iPureIntro. intros ly1 ly2 Hptr1 Hptr2. simpl in *. f_equiv. by eapply syn_type_has_layout_inj. }
      iSplitR. { simpl. eauto. }
      iIntros (v2) "Hv".
      iEval (rewrite /ty_own_val/=) in "Hv". iDestruct "Hv" as "->".
      iEval (rewrite /ty_own_val/=).
      iExists x', _. iR. iR. iR.
      iPoseProof (ltype_own_loc_in_bounds with "H_pts") as "#Hlb".
      { simp_ltypes. solve_layout_alg. }
      simpl.
      unfold_no_enrich. inv_layout_alg.
      rename select (ly_size _ = 0%nat) into Hsz. rewrite Hsz. iFrame "Hlb".
      iFrame. iExists tt. iR. iNext.
      rewrite ltype_own_ofty_unfold/lty_of_ty_own.
      iDestruct "H_pts" as "(%ly & % & % & _ & _ & _ & %r' & <- & >(%v2 & Hpt & Hb))".
      iModIntro. iExists v2. iFrame.
      rewrite {3 4}/ty_own_val/=.
      iDestruct "Hb" as "(%ly' & %Hstly' & %Hlyv & ?)".
      iExists _. iR. iFrame. iPureIntro.
      apply syn_type_has_layout_unit_inv in Hstly'; subst.
      move: Hlyv. rewrite /has_layout_val => ->. rewrite Hsz. done.
    }
    repeat liRStep.
  - (* non-zero branch, do the allocation *)
    rewrite /typed_val_expr.
    iIntros (?) "#CTX #HE HL Hna Hcont".
    rewrite /Box.
    unfold_no_enrich. inv_layout_alg.
    match goal with | H: Z.of_nat (ly_size ?Hly) ≠ 0%Z |- _ => rename Hly into T_st_ly end.
    have: (Z.of_nat $ ly_size T_st_ly) ∈ usize_t by done.
    efeed pose proof (ly_align_log_in_usize T_st_ly) as Ha; first done.
    move: Ha. rewrite int_elem_of_it_iff int_elem_of_it_iff.
    intros [? Halign]%(val_of_Z_is_Some None) [? Hsz]%(val_of_Z_is_Some None).
    iDestruct "CTX" as "(LFT & TIME & LLCTX)".
    iSelect (credit_store _ _) ltac:(fun H => iRename H into "Hstore").
    iPoseProof (credit_store_borrow_receipt with "Hstore") as "(Hat & Hstore)".
    iMod (persistent_time_receipt_0) as "Hp".
    iApply (wp_alloc_credits with "TIME Hat Hp").
    { done. }
    { simplify_layout_goal. rewrite /i2v Hsz /=. by eapply val_to_of_Z. }
    { simplify_layout_goal. rewrite /i2v Halign /=. by eapply val_to_of_Z. }
    { case_bool_decide; [done | lia]. }
    iIntros "!> %l Hl Hfree %Hly [Hcred1 Hcred] Hat".
    rewrite (additive_time_receipt_succ 1). iDestruct "Hat" as "[Hat1 Hat]".
    iPoseProof ("Hstore" with "Hat1") as "Hstore".
    iApply ("Hcont" $! _ _ _ (box (uninit (ty_syn_type T))) (PlaceIn ()) with "HL Hna [Hfree Hl Hcred Hat]").
    { iExists _, _. iSplitR; first done. iSplitR; first done.
      match goal with | H : CACHED (use_layout_alg (ty_syn_type T) = Some ?ly) |- _ => rename ly into T_ly; rename H into H_T end.
      iR.
      iPoseProof (heap_mapsto_loc_in_bounds with "Hl") as "#Hlb".
      rewrite replicate_length. iFrame "Hlb". simpl. iSplitR; first done. iFrame.
      iSplitL "Hfree". { by iApply freeable_freeable_nz. }
      iExists (). iSplitR; first done. iNext. iModIntro.
      iExists _. iFrame. rewrite uninit_own_spec. iExists T_ly.
      iSplitR; first done. rewrite /has_layout_val replicate_length //. }
    iSplitR; first done.
    repeat liRStep; liShow.

  Unshelve. all: unshelve_sidecond; sidecond_hook.
  Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; try (unfold_common_defs; solve_goal); unsolved_sidecond_hook.
Qed.

(* Drop functions receive a pointer to the thing to drop, just like drop_in_place *)

(* Drop for box *)
Definition drop_box_T (T_ly : layout) (drop_T_loc : loc) : function := {|
 f_args := [("x", void*)];
 f_local_vars := [
  ("__0", unit_sl : layout)
 ];
 f_code :=
  <["_bb0" :=
    (* TODO: have a path for ZST *)
   (* drop T in-place, pass a pointer to the T *)
   expr: Call drop_T_loc [&raw{Mut} (!{PtrOp} (!{PtrOp} "x"))];
   (* now free the memory *)
   (* TODO: use alloc_dealloc here? *)
   (*Free (use{ PtrOp } (!{PtrOp} "x"));*)
   (* return *)
   "__0" <-{ UntypedOp (unit_sl) } zst_val;
   return (use{ UntypedOp (unit_sl) } ("__0"))
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.


(* Drop for integer types *)
Definition drop_int (it : int_type) : function := {|
  f_args := [("x", void* : layout)];
 f_local_vars := [
  ("__0", unit_sl : layout)
 ];
 f_code :=
  <["_bb0" :=
   (* do nothing *)
   "__0" <-{ UntypedOp (unit_sl) } zst_val;
   return (use{ UntypedOp (unit_sl) } ("__0"))
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.

(* Drop for mutable references *)
Definition drop_mutref : function := {|
 f_args := [("x", void*)];
 f_local_vars := [
  ("__0", unit_sl : layout)
 ];
 f_code :=
  <["_bb0" :=
   (* do nothing, but on the ghost level, do a ghost drop *)
   "__0" <-{ UntypedOp (unit_sl) } zst_val;
   return (use{ UntypedOp (unit_sl) } ("__0"))
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.

(* Drop for shared references *)
Definition drop_shrref : function := {|
 f_args := [("x", void*)];
 f_local_vars := [
  ("__0", unit_sl : layout)
 ];
 f_code :=
  <["_bb0" :=
   (* do nothing *)
   "__0" <-{ UntypedOp (unit_sl) } zst_val;
   return (use{ UntypedOp (unit_sl) } ("__0"))
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.



(** ** Array allocator shims *)

Definition size_of_array_in_bytes `{!LayoutAlg} (st : syn_type) (len : nat) : nat :=
  let ly := use_layout_alg' st in
  ly.(ly_size) * len.
Global Hint Unfold size_of_array_in_bytes : core.

(** alloc_array *)
Definition alloc_array (T_st : syn_type) (mem_align_log_of_T_loc : loc) (mem_size_of_T_loc : loc) (alloc_alloc_loc : loc) : function := {|
  f_args := [("len", usize_t : layout)];
  f_local_vars := [
    ("__0", void* : layout);
    ("align_log2", usize_t : layout);
    ("size_of_T", usize_t : layout);
    ("bytes", usize_t : layout)
  ];
  f_code :=
    <["bb0" :=
      "align_log2" <-{ IntOp usize_t } CallE mem_align_log_of_T_loc [] [@{expr} ];
      "size_of_T" <-{IntOp usize_t} CallE mem_size_of_T_loc [] [@{expr} ];
      "bytes" <-{ IntOp usize_t } ((use{IntOp usize_t} "len") ×c{IntOp usize_t, IntOp usize_t} (use{IntOp usize_t} "size_of_T"));
      "__0" <-{PtrOp} CallE alloc_alloc_loc [] [@{expr} use{IntOp usize_t} "bytes"; use{IntOp usize_t} "align_log2"];
      return (use{PtrOp} "__0")
    ]>%E $
    ∅;
  f_init := "bb0";
 |}.

Definition type_of_alloc_array `{!typeGS Σ} (T_rt : Type) (T_st : syn_type) :=
  fn(∀ () : 0 | (size) : (Z), (λ ϝ, []); size @ int usize_t; λ π,
    ⌜Z.of_nat (size_of_array_in_bytes T_st (Z.to_nat size)) ∈ isize_t⌝ ∗
    ⌜(size > 0)%Z⌝ ∗
    ⌜(size_of_st T_st > 0)%Z⌝) →
  ∃ l : loc, l @ alias_ptr_t; λ π,
      l ◁ₗ[π, Owned false] .@ (◁ (uninit (ArraySynType T_st (Z.to_nat size)))) ∗
      freeable_nz l ((size_of_array_in_bytes T_st (Z.to_nat size))) 1 HeapAlloc.

Lemma alloc_array_layout_wf T_st_ly size :
  layout_wf T_st_ly →
  layout_wf
  {|
    ly_size := Z.to_nat size * ly_size T_st_ly;
    ly_align_log := ly_align_log T_st_ly
  |}.
Proof.
  intros (x & Hwf).
  exists (Z.to_nat size * x)%Z.
  simpl. rewrite {1}/ly_align {1}/ly_align_log. simpl.
  fold (ly_align T_st_ly). lia.
Qed.
Lemma alloc_array_typed `{!typeGS Σ} π T_rt (T_st : syn_type) (mem_align_log_of_T_loc mem_size_of_T_loc alloc_alloc_loc : loc) :
  syn_type_is_layoutable T_st →
  mem_align_log_of_T_loc ◁ᵥ{π} mem_align_log_of_T_loc @ function_ptr [] (type_of_mem_align_log_of T_rt T_st) -∗
  mem_size_of_T_loc ◁ᵥ{π} mem_size_of_T_loc @ function_ptr [] (type_of_mem_size_of T_rt T_st) -∗
  alloc_alloc_loc ◁ᵥ{π} alloc_alloc_loc @ function_ptr [IntSynType usize_t; IntSynType usize_t] (type_of_alloc_alloc) -∗
  typed_function π (alloc_array T_st mem_align_log_of_T_loc mem_size_of_T_loc alloc_alloc_loc) [PtrSynType; IntSynType usize_t; IntSynType usize_t; IntSynType usize_t] (type_of_alloc_array T_rt T_st).
Proof.
  start_function "alloc_array" ( () ) ( size ) => arg_len local_0 local_align_log2 local_size_of_T local_bytes.
  init_tyvars ∅.
  init_lfts ∅.
  repeat liRStep; liShow.
  Unshelve. all: unshelve_sidecond; sidecond_hook.
  Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
  Unshelve. all: by apply alloc_array_layout_wf.
Qed.

(** realloc_array *)
Definition realloc_array (T_st : syn_type) (mem_align_log_of_T_loc : loc) (mem_size_of_T_loc : loc) (alloc_realloc_loc : loc) : function := {|
  f_args := [
    ("old_len", usize_t : layout);
    ("ptr", void* : layout);
    ("new_len", usize_t : layout)
  ];
  f_local_vars := [
    ("__0", void* : layout);
    ("align_log2", usize_t : layout);
    ("size_of_T", usize_t : layout);
    ("old_bytes", usize_t : layout);
    ("new_bytes", usize_t : layout)
  ];
  f_code :=
    <["bb0" :=
      "align_log2" <-{ IntOp usize_t } CallE mem_align_log_of_T_loc [] [@{expr} ];
      "size_of_T" <-{IntOp usize_t} CallE mem_size_of_T_loc [] [@{expr} ];
      "old_bytes" <-{ IntOp usize_t } ((use{IntOp usize_t} "old_len") ×c{IntOp usize_t, IntOp usize_t} (use{IntOp usize_t} "size_of_T"));
      "new_bytes" <-{ IntOp usize_t } ((use{IntOp usize_t} "new_len") ×c{IntOp usize_t, IntOp usize_t} (use{IntOp usize_t} "size_of_T"));
      "__0" <-{PtrOp} CallE alloc_realloc_loc [] [@{expr} use{IntOp usize_t} "old_bytes"; use{IntOp usize_t} "align_log2"; use{IntOp usize_t} "new_bytes"; use{PtrOp} "ptr"];
      return (use{PtrOp} "__0")
    ]>%E $
    ∅;
  f_init := "bb0";
 |}.

(* Spec is using UntypedSynType (instead of ArraySynType) because this is using untyped copies *)
Definition type_of_realloc_array `{!typeGS Σ} (T_rt : Type) (T_st : syn_type) :=
  fn(∀ () : 0 | (old_size, new_size, l, v) : (Z * Z * loc * val), (λ ϝ, []);
    old_size @ int usize_t, l @ alias_ptr_t, new_size @ int usize_t; λ π,
    freeable_nz l (size_of_array_in_bytes T_st (Z.to_nat old_size)) 1 HeapAlloc ∗
    l ◁ₗ[π, Owned false] #v @ (◁ value_t (UntypedSynType (mk_array_layout (use_layout_alg' T_st) (Z.to_nat old_size)))) ∗
    ⌜(old_size ≤ new_size)%Z⌝ ∗
    ⌜Z.of_nat (size_of_array_in_bytes T_st (Z.to_nat new_size)) ∈ isize_t⌝ ∗
    ⌜(old_size > 0)%Z⌝ ∗
    ⌜(size_of_st T_st > 0)%Z⌝) →
  ∃ (l', v') : (loc * val), l' @ alias_ptr_t; λ π,
    l' ◁ₗ[π, Owned false] #(v ++ v') @ (◁ (value_t (UntypedSynType (mk_array_layout (use_layout_alg' T_st) (Z.to_nat new_size))))) ∗
    v' ◁ᵥ{π} .@ uninit (UntypedSynType (mk_array_layout (use_layout_alg' T_st) (Z.to_nat (new_size - old_size)))) ∗
      freeable_nz l' ((size_of_array_in_bytes T_st (Z.to_nat new_size))) 1 HeapAlloc.

Lemma realloc_array_typed `{!typeGS Σ} π T_rt (T_st : syn_type) (mem_align_log_of_T_loc mem_size_of_T_loc alloc_realloc_loc : loc) :
  syn_type_is_layoutable T_st →
  mem_align_log_of_T_loc ◁ᵥ{π} mem_align_log_of_T_loc @ function_ptr [] (type_of_mem_align_log_of T_rt T_st) -∗
  mem_size_of_T_loc ◁ᵥ{π} mem_size_of_T_loc @ function_ptr [] (type_of_mem_size_of T_rt T_st) -∗
  alloc_realloc_loc ◁ᵥ{π} alloc_realloc_loc @ function_ptr [IntSynType usize_t; IntSynType usize_t; IntSynType usize_t; PtrSynType] (type_of_alloc_realloc) -∗
  typed_function π (realloc_array T_st mem_align_log_of_T_loc mem_size_of_T_loc alloc_realloc_loc) [PtrSynType; IntSynType usize_t; IntSynType usize_t; IntSynType usize_t; IntSynType usize_t] (type_of_realloc_array T_rt T_st).
Proof.
  start_function "realloc_array" ( () ) ( [[[old_size new_size] l] v] ) => arg_old_len arg_ptr arg_new_len local_0 local_align_log2 local_size_of_T local_old_bytes local_new_bytes.
  init_tyvars ∅.
  init_lfts ∅.
  repeat liRStep; liShow.
  iAssert (x'0 ◁ᵥ{π} .@ uninit (UntypedSynType (mk_array_layout T_st_ly (Z.to_nat (new_size - old_size)))))%I as "Ha".
  { rewrite uninit_own_spec. iExists _.
    { iSplitR.
      { iPureIntro. solve_layout_alg. }
      iPureIntro. rewrite /has_layout_val.
      match goal with | H : x'0 `has_layout_val` _ |- _ => rename H into Hlen end.
      rewrite Hlen.
      solve_goal.
   }
  }
  repeat liRStep; liShow.
  Unshelve. all: unshelve_sidecond; sidecond_hook.
  Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal.
  all: try solve_goal; try (unfold_common_defs; solve_goal); unsolved_sidecond_hook.
  all: rewrite Nat.mul_comm; by apply array_layout_wf.
Qed.


(** dealloc_array *)
Definition dealloc_array `{!LayoutAlg} (T_st : syn_type) (mem_align_log_of_T_loc : loc) (mem_size_of_T_loc : loc) (alloc_dealloc_loc : loc) : function := {|
  f_args := [
    ("len", usize_t : layout);
    ("ptr", void* : layout)
  ];
  f_local_vars := [
    ("__0", use_layout_alg' UnitSynType : layout);
    ("align_log2", usize_t : layout);
    ("size_of_T", usize_t : layout);
    ("bytes", usize_t : layout)
  ];
  f_code :=
    <["bb0" :=
      "align_log2" <-{ IntOp usize_t } CallE mem_align_log_of_T_loc [] [@{expr} ];
      "size_of_T" <-{IntOp usize_t} CallE mem_size_of_T_loc [] [@{expr} ];
      "bytes" <-{ IntOp usize_t } ((use{IntOp usize_t} "len") ×c{IntOp usize_t, IntOp usize_t} (use{IntOp usize_t} "size_of_T"));
      expr: CallE alloc_dealloc_loc [] [@{expr} use{IntOp usize_t} "bytes"; use{IntOp usize_t} "align_log2"; use{PtrOp} "ptr"];
      "__0" <-{use_op_alg' UnitSynType} zst_val;
      return (use{use_op_alg' UnitSynType} "__0")
    ]>%E $
    ∅;
  f_init := "bb0";
 |}.

Definition type_of_dealloc_array `{!typeGS Σ} (T_rt : Type) (T_st : syn_type) :=
  fn(∀ () : 0 | (size, l) : (Z * loc), (λ ϝ, []);
    size @ int usize_t, l @ alias_ptr_t; λ π,
    freeable_nz l (size_of_array_in_bytes T_st (Z.to_nat size)) 1 HeapAlloc ∗
    l ◁ₗ[π, Owned false] .@ (◁ uninit (UntypedSynType (mk_array_layout (use_layout_alg' T_st) (Z.to_nat size)))) ∗
    ⌜(size > 0)%Z⌝ ∗
    ⌜Z.of_nat (size_of_array_in_bytes T_st (Z.to_nat size)) ∈ isize_t⌝ ∗
    ⌜(size_of_st T_st > 0)%Z⌝) →
  ∃ () : unit, () @ unit_t; λ π, True.


Lemma dealloc_array_typed `{!typeGS Σ} π T_rt (T_st : syn_type) (mem_align_log_of_T_loc mem_size_of_T_loc alloc_dealloc_loc : loc) :
  syn_type_is_layoutable T_st →
  mem_align_log_of_T_loc ◁ᵥ{π} mem_align_log_of_T_loc @ function_ptr [] (type_of_mem_align_log_of T_rt T_st) -∗
  mem_size_of_T_loc ◁ᵥ{π} mem_size_of_T_loc @ function_ptr [] (type_of_mem_size_of T_rt T_st) -∗
  alloc_dealloc_loc ◁ᵥ{π} alloc_dealloc_loc @ function_ptr [IntSynType usize_t; IntSynType usize_t; PtrSynType] (type_of_alloc_dealloc) -∗
  typed_function π (dealloc_array T_st mem_align_log_of_T_loc mem_size_of_T_loc alloc_dealloc_loc) [UnitSynType; IntSynType usize_t; IntSynType usize_t; IntSynType usize_t] (type_of_dealloc_array T_rt T_st).
Proof.
  start_function "dealloc_array" ( () ) ( [size l] ) => arg_len arg_ptr local_0 local_align_log2 local_size_of_T local_bytes.
  init_tyvars ∅.
  init_lfts ∅.
  repeat liRStep; liShow.
  Unshelve. all: unshelve_sidecond; sidecond_hook.
  Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; try (unfold_common_defs; solve_goal); unsolved_sidecond_hook.
  rewrite Nat.mul_comm.
  by apply array_layout_wf.
Qed.

(** check_array_layoutable *)
Definition check_array_layoutable `{!LayoutAlg} (T_st : syn_type) (mem_align_log_of_T_loc : loc) (mem_size_of_T_loc : loc) : function := {|
  f_args := [
    ("len", usize_t : layout)
  ];
  f_local_vars := [
    ("__0", use_layout_alg' BoolSynType : layout);
    ("align_log2", usize_t : layout);
    ("size_of_T", usize_t : layout);
    ("bytes", usize_t : layout);
    ("check", use_layout_alg' BoolSynType : layout)
  ];
  f_code :=
    <["bb0" :=
      "align_log2" <-{ IntOp usize_t } CallE mem_align_log_of_T_loc [] [@{expr} ];
      "size_of_T" <-{IntOp usize_t} CallE mem_size_of_T_loc [] [@{expr} ];
      "check" <-{ BoolOp } CheckBinOp MulOp (IntOp usize_t) (IntOp usize_t) (use{IntOp usize_t} "len") (use{IntOp usize_t} "size_of_T");
      if{BoolOp}: (use{BoolOp} "check") then Goto "bb1" else Goto "bb2" ]>%E $
    <["bb1" :=
      (* result fits into usize *)
      "bytes" <-{ IntOp usize_t } ((use{IntOp usize_t} "len") ×c{IntOp usize_t, IntOp usize_t} (use{IntOp usize_t} "size_of_T"));
      "__0" <-{use_op_alg' BoolSynType} ((use{IntOp usize_t} "bytes") ≤{IntOp usize_t, IntOp usize_t, u8} (I2v (MaxInt isize_t) USize));
      return (use{use_op_alg' BoolSynType} "__0")
    ]>%E $
    <["bb2" :=
      (* result does not fit into usize *)
      return (Val (val_of_bool false))
    ]>%E $
    ∅;
  f_init := "bb0";
 |}.

Definition type_of_check_array_layoutable `{!typeGS Σ} (T_rt : Type) (T_st : syn_type) :=
  fn(∀ () : 0 | (size) : (Z), (λ ϝ, []); size @ int usize_t; λ π, True) →
  ∃ () : unit, (bool_decide (size_of_array_in_bytes T_st (Z.to_nat size) ≤ MaxInt isize_t)%Z) @ bool_t; λ π, True.

Lemma check_array_layoutable_typed `{!typeGS Σ} π T_rt (T_st : syn_type) (mem_align_log_of_T_loc mem_size_of_T_loc : loc) :
  syn_type_is_layoutable T_st →
  mem_align_log_of_T_loc ◁ᵥ{π} mem_align_log_of_T_loc @ function_ptr [] (type_of_mem_align_log_of T_rt T_st) -∗
  mem_size_of_T_loc ◁ᵥ{π} mem_size_of_T_loc @ function_ptr [] (type_of_mem_size_of T_rt T_st) -∗
  typed_function π (check_array_layoutable T_st mem_align_log_of_T_loc mem_size_of_T_loc) [BoolSynType; IntSynType usize_t; IntSynType usize_t; IntSynType usize_t; BoolSynType] (type_of_check_array_layoutable T_rt T_st).
Proof.
  start_function "check_array_layoutable" ( () ) ( size ) => arg_len local_0 local_align_log2 local_size_of_T local_bytes local_check.
  init_tyvars ∅.
  init_lfts ∅.
  repeat liRStep; liShow.

  typed_val_expr_bind.
  repeat liRStep; liShow.
  typed_val_expr_bind.
  repeat liRStep; liShow.
  rewrite /typed_val_expr.
  iIntros (?) "#CTX #HE HL Hna HC".
  iRename select (_ ◁ᵥ{_} size @ int usize_t)%I into "Hv1".
  iRename select (_ ◁ᵥ{_} ly_size T_st_ly @ int usize_t)%I into "Hv2".
  iPoseProof (ty_own_int_in_range with "Hv1") as "%Hsz". destruct Hsz.
  iEval (rewrite /ty_own_val/=) in "Hv1".
  iEval (rewrite /ty_own_val/=) in "Hv2".
  iDestruct "Hv1" as "(%Hsize &_)".
  iDestruct "Hv2" as "(%HTsize & _)".
  iApply (wp_check_int_arithop _ _ _ _ _ _ (bool_decide ((size * ly_size T_st_ly ∈ usize_t)))); [done.. | | ].
  { simpl. rewrite /check_arith_bin_op. simpl. f_equiv.
    rewrite /elem_of/int_elem_of_it/int_elem_of_it' MinInt_eq MaxInt_eq//. }
  iNext. iIntros "_".
  iApply ("HC" $! _ _ _ (bool_t) with "HL Hna"). { iApply type_val_bool'. }

  repeat liRStep.

  Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
  Unshelve. all: unfold_common_defs; solve_goal.
Qed.
