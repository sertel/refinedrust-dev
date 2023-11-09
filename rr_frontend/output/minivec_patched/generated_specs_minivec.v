From caesium Require Import lang notation.
From refinedrust Require Export typing shims.
From refinedrust.examples.minivec_patched Require Import generated_code_minivec extra_proofs_minivec.

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
    (λ π inner_rfn '(l, cap), ⌜inner_rfn = -[#(l); #(Z.of_nat cap); #(tt)]⌝ ∗  freeable_nz l (size_of_array_in_bytes (ty_syn_type T_ty) cap) 1 HeapAlloc ∗ True)%I
    (λ π κ inner_rfn '(l, cap), ⌜inner_rfn = -[#(l); #(Z.of_nat cap); #(tt)]⌝ ∗ True)%I
    ([])
    ([])
    _ _ _
  .
  Next Obligation. ex_t_solve_persistent. Qed.
  Next Obligation. ex_plain_t_solve_shr_mono. Qed.
  Next Obligation. ex_plain_t_solve_shr. Qed.

  Definition RawVec_inv_t : type ((loc * nat)) :=
    ex_plain_t _ _ RawVec_inv_t_inv_spec (RawVec_ty T_ty).
End RawVec_inv_t.

Section std_option_Option_ty.
  Context `{!typeGS Σ}.
  Context {T_rt : Type}.
  Context (T_ty : type (T_rt)).

  Notation std_option_Option_None_ty := (struct_t std_option_Option_None_sls +[]).
  (*Definition std_option_Option_None_rt : Type := rt_of std_option_Option_None_ty.*)
  (*Global Typeclasses Transparent std_option_Option_None_ty.*)

  Notation std_option_Option_Some_ty := (struct_t (std_option_Option_Some_sls (ty_syn_type T_ty)) +[
    T_ty]).
  (*Definition std_option_Option_Some_rt : Type := rt_of std_option_Option_Some_ty.*)
  (*Global Typeclasses Transparent std_option_Option_Some_ty.*)

  Program Definition std_option_Option_enum : enum _ := mk_enum
    ((std_option_Option_els (ty_syn_type T_ty)))
    (λ rfn, match rfn with | None => "None" | Some x => "Some" end)
    (λ rfn, match rfn with | None => existT _ (std_option_Option_None_ty, -[])| Some x => existT _ (std_option_Option_Some_ty, -[x])end)
    (λ variant, if (decide (variant = "None")) then Some $ existT _ std_option_Option_None_ty else if decide (variant = "Some") then Some $ existT _ std_option_Option_Some_ty else None)
    (ty_lfts T_ty)
    (ty_wf_E T_ty)
    _
    _
    _
  .
  Arguments ty_lfts : simpl nomatch. 
  Arguments ty_wf_E : simpl nomatch.
  Next Obligation. intros []; set_solver. Qed.
  Next Obligation. intros []; set_solver. Qed.
  Next Obligation. intros []; naive_solver. Qed.

  Global Program Instance construct_enum_Some x st (Hst :  TCDone (st = ty_syn_type T_ty)) : ConstructEnum (std_option_Option_enum) "Some" (struct_t (std_option_Option_Some_sls st) +[ T_ty]) -[x] (Some (x)) :=
    construct_enum _ _ .
  Next Obligation. intros; unfold TCDone in *; naive_solver. Qed.
  Global Program Instance construct_enum_None : ConstructEnum (std_option_Option_enum) "None" (struct_t std_option_Option_None_sls +[]) -[] None :=
    construct_enum _ _.
  Next Obligation. done. Qed.

  Definition std_option_Option_ty : type _ := enum_t std_option_Option_enum.
  Global Typeclasses Transparent std_option_Option_ty.
 End std_option_Option_ty.
 (* TODO: frontend should generate this *)
Global Hint Unfold std_option_Option_ty : solve_protected_eq_db.

Section subtype.
  Context `{!typeGS Σ}.
  (* NOTE: variance proofs are currently not automatically generated by the frontend *)
  Lemma std_option_Option_ty_weak_subtype E L {T_rt1 T_rt2} (T_ty1 : type T_rt1) (T_ty2 : type T_rt2) r1 r2 T :
    weak_subtype E L r1 r2 T_ty1 T_ty2 T ⊢
    weak_subtype E L (Some (#r1)) (Some (#r2)) (std_option_Option_ty T_ty1) (std_option_Option_ty T_ty2) T.
  Proof.
  Admitted.
  Global Instance std_option_Option_ty_weak_subtype_inst E L {T_rt1 T_rt2} (T_ty1 : type T_rt1) (T_ty2 : type T_rt2) r1 r2 :
  Subtype E L (Some (#r1)) (Some (#r2)) (std_option_Option_ty T_ty1) (std_option_Option_ty T_ty2) := λ T, i2p (std_option_Option_ty_weak_subtype E L T_ty1 T_ty2 r1 r2 T).
End subtype.

Section Vec_ty.
  Context `{!typeGS Σ}.
  Context {T_rt : Type}.
  Context (T_ty : type (T_rt)).

  (* TODO: frontend bug: does not use the right abstracted refinement type *)
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

  Program Definition Vec_inv_t_inv_spec : ex_inv_def ((Vec_rt )) (list (place_rfn T_rt)) := mk_ex_inv_def
    (λ π inner_rfn 'xs, ∃ (cap : nat) (l : loc) (len : nat) (els : list _), ⌜inner_rfn = -[#((l, cap)); #(Z.of_nat $ len)]⌝ ∗ l ◁ₗ[π, Owned true] #(els) @ (◁ array_t (maybe_uninit T_ty) cap) ∗ ⌜xs = project_vec_els len els⌝ ∗ ⌜∀ i, (0 ≤ i < len)%nat → els !! i = Some (#(Some (xs !!! i)))⌝ ∗ ⌜∀ i, (len ≤ i < cap)%nat → els !! i = Some (#None)⌝ ∗ ⌜len = length xs⌝ ∗ ⌜len ≤ cap⌝ ∗ ⌜if decide (size_of_st (ty_syn_type T_ty) = 0%nat) then cap = Z.to_nat (MaxInt usize_t) else (size_of_array_in_bytes (ty_syn_type T_ty) cap ≤ MaxInt isize_t)%Z⌝ ∗ True)%I
    (λ π κ inner_rfn 'xs, ∃ (cap : nat) (l : loc) (len : nat) (els : _), ⌜inner_rfn = -[#((l, cap)); #(Z.of_nat $ len)]⌝ ∗ l ◁ₗ[π, Shared κ] #(els) @ (◁ array_t (maybe_uninit T_ty) cap) ∗ ⌜xs = project_vec_els len els⌝ ∗ ⌜∀ i, (0 ≤ i < len)%nat → els !! i = Some (#(Some (xs !!! i)))⌝ ∗ ⌜∀ i, (len ≤ i < cap)%nat → els !! i = Some (#None)⌝ ∗ ⌜len = length xs⌝ ∗ ⌜len ≤ cap⌝ ∗ ⌜if decide (size_of_st (ty_syn_type T_ty) = 0%nat) then cap = Z.to_nat (MaxInt usize_t) else (size_of_array_in_bytes (ty_syn_type T_ty) cap ≤ MaxInt isize_t)%Z⌝ ∗ True)%I
    ([] ++ (ty_lfts (T_ty)))
    ([] ++ (ty_wf_E (T_ty)))
    _ _ _
  .
  Next Obligation. ex_t_solve_persistent. Qed.
  Next Obligation. ex_plain_t_solve_shr_mono. Qed.
  Next Obligation. ex_plain_t_solve_shr. Qed.

  Definition Vec_inv_t : type (list (place_rfn T_rt)) :=
    ex_plain_t _ _ Vec_inv_t_inv_spec (Vec_ty T_ty).

  (* NOTE Resolution of ghost variables over the invariant -- not currently automatically generated by the frontend. *)
  Lemma resolve_ghost_Vec_T π E L rm l rs wl T :
    (∀ li, resolve_ghost_iter π E L rm false li (ty_syn_type T_ty) (replicate (length rs) (◁ T_ty))%I (Owned false) rs [] 0%nat (λ L2 rs' R progress,
      T L2 (#rs') R progress)) ⊢
    resolve_ghost π E L rm true l (◁ Vec_inv_t) (Owned wl) (#rs) T.
  Proof.
  Admitted.
  Global Instance resolve_ghost_Vec_T_inst π E L rm l rs wl : ResolveGhost π E L rm true l (◁ Vec_inv_t)%I (Owned wl) (#rs) :=
    λ T, i2p (resolve_ghost_Vec_T π E L rm l rs wl T).
End Vec_inv_t.

Section specs.
Context `{!typeGS Σ}.

Definition type_of_RawVec_T_grow (T_rt : Type) (T_st : syn_type) :=
  fn(∀ ((), ulft__) : 1 | (l, xs, cap, γ, T_ty) : (_ * _ * nat * _ * (type T_rt)), (λ ϝ, []); (#(l, cap), γ) @ (mut_ref (RawVec_inv_t (T_ty)) ulft__); (λ π : thread_id, (⌜ty_syn_type T_ty = T_st⌝) ∗ (⌜(size_of_array_in_bytes (ty_syn_type T_ty) (2 * cap) ≤ MaxInt isize_t)%Z⌝) ∗ (⌜(size_of_st (ty_syn_type T_ty) > 0)%Z⌝) ∗ (l ◁ₗ[π, Owned false] #xs @ (◁ array_t (maybe_uninit T_ty) cap)) ∗ (⌜ty_allows_writes T_ty⌝) ∗ (⌜ty_allows_reads T_ty⌝) ∗ ty_sidecond T_ty))
    → ∃ (new_cap, l') : (nat * loc), () @ unit_t; (λ π : thread_id, (gvar_pobs γ (l', new_cap)) ∗ (l' ◁ₗ[π, Owned false] #(xs ++ replicate (new_cap - cap) #None) @ (◁ array_t (maybe_uninit T_ty) new_cap)) ∗ (⌜new_cap > cap⌝) ∗ ⌜(size_of_array_in_bytes T_st new_cap ≤ MaxInt isize_t)%Z⌝).

Definition type_of_Vec_T_insert (T_rt : Type) (T_st : syn_type) :=
  fn(∀ ((), ulft__) : 1 | (xs, γ, i, x, T_ty) : (_ * _ * nat * _ * (type T_rt)), (λ ϝ, []); (#xs, γ) @ (mut_ref (Vec_inv_t (T_ty)) ulft__), Z.of_nat i @ (int USize), x @ T_ty; (λ π : thread_id, (⌜ty_syn_type T_ty = T_st⌝) ∗ (⌜i ≤ length xs⌝) ∗ (⌜(length xs < MaxInt usize_t)%Z⌝) ∗ (⌜(size_of_array_in_bytes (ty_syn_type T_ty) (2 * length xs) ≤ MaxInt isize_t)%Z⌝) ∗ (⌜ty_allows_writes T_ty⌝) ∗ (⌜ty_allows_reads T_ty⌝) ∗ ty_sidecond T_ty))
    → ∃ _ : unit, () @ unit_t; (λ π : thread_id, (gvar_pobs γ (<[i := #x]> xs))).

Definition type_of_Vec_T_cap (T_rt : Type) (T_st : syn_type) :=
  fn(∀ ((), ulft_a) : 1 | (l, cap, len, T_ty) : (loc * nat * Z * (type T_rt)), (λ ϝ, []); #(-[#(l, cap); #len]) @ shr_ref (Vec_ty T_ty) ulft_a; (λ π : thread_id, (⌜ty_syn_type T_ty = T_st⌝) ∗ (⌜ty_allows_writes T_ty⌝) ∗ (⌜ty_allows_reads T_ty⌝) ∗ ty_sidecond T_ty))
    → ∃ _ : unit, cap @ (int USize); (λ π : thread_id, True).

Definition type_of_Vec_T_len (T_rt : Type) (T_st : syn_type) :=
  fn(∀ ((), ulft__) : 1 | (xs, T_ty) : (_ * (type T_rt)), (λ ϝ, []); #xs @ (shr_ref (Vec_inv_t (T_ty)) ulft__); (λ π : thread_id, (⌜ty_syn_type T_ty = T_st⌝) ∗ (⌜ty_allows_writes T_ty⌝) ∗ (⌜ty_allows_reads T_ty⌝) ∗ ty_sidecond T_ty))
    → ∃ _ : unit, length xs @ (int USize); (λ π : thread_id, True).

(* No specification provided for RawVec_T_with_capacity *)

Definition type_of_Vec_T_push (T_rt : Type) (T_st : syn_type) :=
  fn(∀ ((), ulft__) : 1 | (xs, γ, x, T_ty) : (_ * _ * _ * (type T_rt)), (λ ϝ, []); (#xs, γ) @ (mut_ref (Vec_inv_t (T_ty)) ulft__), x @ T_ty; (λ π : thread_id, (⌜ty_syn_type T_ty = T_st⌝) ∗ (⌜(length xs < MaxInt usize_t)%Z⌝) ∗ (⌜(size_of_array_in_bytes (ty_syn_type T_ty) (2 * length xs) ≤ MaxInt isize_t)%Z⌝) ∗ (⌜ty_allows_writes T_ty⌝) ∗ (⌜ty_allows_reads T_ty⌝) ∗ ty_sidecond T_ty))
    → ∃ _ : unit, () @ unit_t; (λ π : thread_id, (gvar_pobs γ (xs ++ [ #x]))).

Definition type_of_Vec_T_remove (T_rt : Type) (T_st : syn_type) :=
  fn(∀ ((), ulft__) : 1 | (xs, γ, i, T_ty) : (_ * _ * nat * (type T_rt)), (λ ϝ, []); (#(fmap (M:=list) PlaceIn xs), γ) @ (mut_ref (Vec_inv_t (T_ty)) ulft__), Z.of_nat i @ (int USize); (λ π : thread_id, (⌜ty_syn_type T_ty = T_st⌝) ∗ (⌜i < length xs⌝) ∗ (⌜ty_allows_writes T_ty⌝) ∗ (⌜ty_allows_reads T_ty⌝) ∗ ty_sidecond T_ty))
    → ∃ _ : unit, () @ unit_t; (λ π : thread_id, (gvar_pobs γ (delete i ((fmap (M:=list) PlaceIn xs))))).

Definition type_of_Vec_T_ptr (T_rt : Type) (T_st : syn_type) :=
  fn(∀ ((), ulft_a) : 1 | (l, cap, len, T_ty) : (loc * nat * Z * (type T_rt)), (λ ϝ, []); #(-[#(l, cap); #len]) @ shr_ref (Vec_ty T_ty) ulft_a; (λ π : thread_id, (⌜ty_syn_type T_ty = T_st⌝) ∗ (⌜ty_allows_writes T_ty⌝) ∗ (⌜ty_allows_reads T_ty⌝) ∗ ty_sidecond T_ty))
    → ∃ _ : unit, l @ alias_ptr_t; (λ π : thread_id, True).

Definition type_of_RawVec_T_ptr (T_rt : Type) (T_st : syn_type) :=
  fn(∀ ((), ulft__) : 1 | (l, cap, T_ty) : (_ * _ * (type T_rt)), (λ ϝ, []); #(l, cap) @ (shr_ref (RawVec_inv_t (T_ty)) ulft__); (λ π : thread_id, (⌜ty_syn_type T_ty = T_st⌝) ∗ (⌜ty_allows_writes T_ty⌝) ∗ (⌜ty_allows_reads T_ty⌝) ∗ ty_sidecond T_ty))
    → ∃ _ : unit, l @ alias_ptr_t; (λ π : thread_id, True).

Definition type_of_RawVec_T_cap (T_rt : Type) (T_st : syn_type) :=
  fn(∀ ((), ulft__) : 1 | (l, cap, T_ty) : (_ * _ * (type T_rt)), (λ ϝ, []); #(l, cap) @ (shr_ref (RawVec_inv_t (T_ty)) ulft__); (λ π : thread_id, (⌜ty_syn_type T_ty = T_st⌝) ∗ (⌜ty_allows_writes T_ty⌝) ∗ (⌜ty_allows_reads T_ty⌝) ∗ ty_sidecond T_ty))
    → ∃ _ : unit, cap @ (int USize); (λ π : thread_id, True).

(* No specification provided for main *)

Definition type_of_Vec_T_new (T_rt : Type) (T_st : syn_type) :=
  fn(∀ (()) : 0 | (T_ty) : ((type T_rt)), (λ ϝ, []); (λ π : thread_id, (⌜ty_syn_type T_ty = T_st⌝) ∗ (⌜ty_allows_writes T_ty⌝) ∗ (⌜ty_allows_reads T_ty⌝) ∗ ty_sidecond T_ty))
    → ∃ _ : unit, [] @ (Vec_inv_t (T_ty)); (λ π : thread_id, True).

Definition type_of_RawVec_T_new (T_rt : Type) (T_st : syn_type) :=
  fn(∀ (()) : 0 | (T_ty) : ((type T_rt)), (λ ϝ, []); (λ π : thread_id, (⌜ty_syn_type T_ty = T_st⌝) ∗ (⌜ty_allows_writes T_ty⌝) ∗ (⌜ty_allows_reads T_ty⌝) ∗ ty_sidecond T_ty))
    → ∃ (l, cap) : (loc * nat), (l, cap) @ (RawVec_inv_t (T_ty)); (λ π : thread_id, (⌜cap = if decide (size_of_st (ty_syn_type T_ty) = 0%nat) then Z.to_nat (MaxInt usize_t) else 0%nat⌝) ∗ (l ◁ₗ[π, Owned false] #(replicate cap #None) @ (◁ array_t (maybe_uninit T_ty) cap))).

(* No specification provided for RawVecTasstd_ops_Drop_drop *)

Definition type_of_Vec_T_get_unchecked_mut (T_rt : Type) `{Inhabited T_rt} (T_st : syn_type) :=
  fn(∀ ((), ulft__) : 1 | (xs, γ, i, T_ty) : (list T_rt * _ * nat * (type T_rt)), (λ ϝ, []); (#(fmap (M:=list) PlaceIn xs), γ) @ (mut_ref (Vec_inv_t (T_ty)) ulft__), Z.of_nat i @ (int USize); (λ π : thread_id, (⌜ty_syn_type T_ty = T_st⌝) ∗ (⌜i < length xs⌝) ∗ (⌜ty_allows_writes T_ty⌝) ∗ (⌜ty_allows_reads T_ty⌝) ∗ ty_sidecond T_ty))
    → ∃ (γi) : (_), (#(xs !!! i), γi) @ (mut_ref T_ty ulft__); (λ π : thread_id, (gvar_pobs γ (<[i := PlaceGhost γi]> (fmap (M:=list) PlaceIn xs)))).

Definition type_of_Vec_T_get_mut (T_rt : Type) `{Inhabited T_rt} (T_st : syn_type) :=
  fn(∀ ((), ulft__) : 1 | (xs, γ, i, T_ty) : (list T_rt * _ * nat * (type T_rt)), (λ ϝ, []); (#(fmap (M:=list) PlaceIn xs), γ) @ (mut_ref (Vec_inv_t (T_ty)) ulft__), Z.of_nat i @ (int USize); (λ π : thread_id, (⌜ty_syn_type T_ty = T_st⌝) ∗ (⌜ty_allows_writes T_ty⌝) ∗ (⌜ty_allows_reads T_ty⌝) ∗ (ty_sidecond T_ty)))
  → ∃ (γi, γ1, γ2) : (gname * gname * gname), if decide (i < length xs) then Some (#(#(xs !!! i), γi)) else None @ (std_option_Option_ty ((mut_ref T_ty ulft__))); (λ π : thread_id, (if decide (i < length xs) then Inherit ulft__ InheritGhost (Rel2 γ2 γ (eq (A:=list (place_rfn T_rt)))) else True) ∗ (gvar_pobs γ2 (if decide (i < length xs) then <[i := PlaceGhost γ1]> (fmap (M:=list) PlaceIn xs) else fmap (M:=list) PlaceIn xs)) ∗ (if decide (i < length xs) then Inherit ulft__ InheritGhost (Rel2 γi γ1 (eq (A:=T_rt))) else True)).

Definition type_of_Vec_T_pop (T_rt : Type) (T_st : syn_type) :=
  fn(∀ ((), ulft__) : 1 | (xs, γ, T_ty) : (_ * _ * (type T_rt)), (λ ϝ, []); (#(fmap (M:=list) PlaceIn xs), γ) @ (mut_ref (Vec_inv_t (T_ty)) ulft__); (λ π : thread_id, (⌜ty_syn_type T_ty = T_st⌝) ∗ (⌜ty_allows_writes T_ty⌝) ∗ (⌜ty_allows_reads T_ty⌝) ∗ ty_sidecond T_ty))
    → ∃ _ : unit, (fmap PlaceIn (last xs)) @ (std_option_Option_ty (T_ty)); (λ π : thread_id, (gvar_pobs γ (take (length xs - 1) (fmap (M:=list) PlaceIn xs)))).

(* TODO manually added unwrap *)
Definition type_of_std_option_Option_T_unwrap (T_rt : Type) `{Inhabited T_rt} (T_st : syn_type) :=
  fn(∀ (()) : 0 | (x, T_ty) : (_ * (type T_rt)), (λ ϝ, []); Some (#x) @ (std_option_Option_ty (T_ty)); (λ π : thread_id, (⌜ty_syn_type T_ty = T_st⌝) ∗ (⌜ty_allows_writes T_ty⌝) ∗ (⌜ty_allows_reads T_ty⌝) ∗ (ty_sidecond T_ty)))
    → ∃ _ : unit, x @ T_ty; (λ π : thread_id, True).

Definition type_of_get_mut_client  :=
  fn(∀ (()) : 0 | _ : unit, (λ ϝ, []); (λ π : thread_id, True))
    → ∃ _ : unit, () @ unit_t; (λ π : thread_id, True).

Definition type_of_Vec_T_get_unchecked (T_rt : Type) `{Inhabited T_rt} (T_st : syn_type) :=
  fn(∀ ((), ulft__) : 1 | (xs, i, T_ty) : (_ * nat * (type T_rt)), (λ ϝ, []); #(fmap (M:=list) PlaceIn xs) @ (shr_ref (Vec_inv_t (T_ty)) ulft__), Z.of_nat i @ (int USize); (λ π : thread_id, (⌜ty_syn_type T_ty = T_st⌝) ∗ (⌜i < length xs⌝) ∗ (⌜ty_allows_writes T_ty⌝) ∗ (⌜ty_allows_reads T_ty⌝) ∗ (ty_sidecond T_ty)))
    → ∃ _ : unit, #(xs !!! i) @ (shr_ref T_ty ulft__); (λ π : thread_id, True).

Definition type_of_Vec_T_get (T_rt : Type) `{Inhabited T_rt} (T_st : syn_type) :=
  fn(∀ ((), ulft__) : 1 | (xs, i, T_ty) : (_ * nat * (type T_rt)), (λ ϝ, []); #(fmap (M:=list) PlaceIn xs) @ (shr_ref (Vec_inv_t (T_ty)) ulft__), Z.of_nat i @ (int USize); (λ π : thread_id, (⌜ty_syn_type T_ty = T_st⌝) ∗ (⌜ty_allows_writes T_ty⌝) ∗ (⌜ty_allows_reads T_ty⌝) ∗ (ty_sidecond T_ty)))
    → ∃ _ : unit, if decide (i < length xs) then Some (#(#(xs !!! i))) else None @ (std_option_Option_ty ((shr_ref T_ty ulft__))); (λ π : thread_id, True).

End specs.
