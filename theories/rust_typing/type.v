From iris.bi Require Export fractional.
From iris.base_logic.lib Require Export invariants na_invariants.
From caesium Require Export proofmode notation syntypes.
From lrust.lifetime Require Export frac_borrow.
From refinedrust Require Export base util pinned_borrows lft_contexts gvar_refinement memcasts.
From caesium Require Import loc.
From iris Require Import options.

(** * RefinedRust's notion of value types *)

(** Iris resource algebras that need to be available *)
Class typeGS Σ := TypeG {
  type_heapG :: refinedcG Σ;
  type_lftGS :: lftGS Σ lft_userE;
  type_na_invG :: na_invG Σ;
  type_frac_borrowG :: frac_borG Σ;
  type_lctxGS :: lctxGS Σ;
  type_ghost_var :: ghost_varG Σ RT;
  type_pinnedBorG :: pinnedBorG Σ;
  (* we also fix a global layout algorithm here *)
  ALG :: LayoutAlg;
}.
#[export] Hint Mode typeGS - : typeclass_instances.

Definition rrust_ctx `{typeGS Σ} : iProp Σ := lft_ctx ∗ time_ctx ∗ llctx_ctx.

Definition thread_id := na_inv_pool_name.

(* The number of credits we deposit in the interpretation of Box/&mut for accessing them at a logical_step. *)
Definition num_cred := 5%nat.
Lemma num_cred_le `{!typeGS Σ} n :
  (1 ≤ n)%nat →
  num_cred ≤ num_laters_per_step n.
Proof.
  rewrite /num_cred/num_laters_per_step /=. lia.
Qed.

(** Types are defined semantically by what it means for a value to have a particular type. 
    Types are indexed by their refinement type [rt].
*)
Record type `{!typeGS Σ} (rt : Type) := {
  (** The refinement type should be inhabited *)
  ty_rt_inhabited : Inhabited rt;

  (** Ownership of values *)
  ty_own_val : thread_id → rt → val → iProp Σ;

  (** This type's syntactic type *)
  ty_syn_type : syn_type;

  (** Determines how values are altered when they are read and written *)
  (** This is formulated as a property of the semantic type, because the memcast compatibility is a semantic property *)
  _ty_has_op_type : op_type → memcast_compat_type → Prop;

  (** The sharing predicate: what does it mean to have a shared reference to this type at a particular lifetime? *)
  ty_shr : lft → thread_id → rt → loc → iProp Σ;

  (** We have a separate well-formedness predicate to capture persistent + timeless information about
    the type's structure. Needed to evade troubles with the ltype unfolding equations. *)
  ty_sidecond : iProp Σ;

  (** In essence, this is a kind of "ghost-drop" that only happens at the level of the logic when a value goes out-of-scope/ is unused.)
    Most importantly, we use it to get observations out of mutable borrows. *)
  ty_ghost_drop : thread_id → rt → iProp Σ;

  (* [ty_lfts] is the set of lifetimes that needs to be active for this type to make sense.*)
  ty_lfts : list lft;

  (* [ty_wf_E] is a set of inclusion constraints on lifetimes that need to hold for the type to make sense. *)
  ty_wf_E : elctx;

  (** Given the concrete layout algorithm at runtime, we can get a layout *)
  ty_has_layout π r v :
    ty_own_val π r v -∗ ∃ ly : layout, ⌜syn_type_has_layout ty_syn_type ly⌝ ∗ ⌜v `has_layout_val` ly⌝;

  (** if we specify a particular op_type, its layout needs to be compatible with the underlying syntactic type *)
  _ty_op_type_stable ot mt : _ty_has_op_type ot mt → syn_type_has_layout ty_syn_type (ot_layout ot);

  (** We can get access to the sidecondition *)
  ty_own_val_sidecond π r v : ty_own_val π r v -∗ ty_sidecond;
  ty_shr_sidecond κ π r l : ty_shr κ π r l -∗ ty_sidecond;

  (** The sharing predicate is persistent *)
  ty_shr_persistent κ π l r : Persistent (ty_shr κ π r l);
  (** The address at which a shared type is stored must be correctly aligned *)
  ty_shr_aligned κ π l r :
    ty_shr κ π r l -∗ ∃ ly : layout, ⌜l `has_layout_loc` ly⌝ ∗ ⌜syn_type_has_layout ty_syn_type ly⌝;

  (** We need to be able to initiate sharing *)
  ty_share E κ l ly π r q:
    lftE ⊆ E →
    rrust_ctx -∗
    (* We get a token not only for κ, but for all that we might need to recursively use to initiate sharing *)
    let κ' := lft_intersect_list (ty_lfts) in
    q.[κ ⊓ κ'] -∗
    (* [l] needs to be well-layouted *)
    ⌜syn_type_has_layout ty_syn_type ly⌝ -∗
    ⌜l `has_layout_loc` ly⌝ -∗
    loc_in_bounds l 0 (ly_size ly) -∗
    &{κ} (∃ v, l ↦ v ∗ ty_own_val π r v) -∗
    (* after a logical step, we can initiate sharing *)
    logical_step E (ty_shr κ π r l ∗ q.[κ ⊓ κ']);

  (** The sharing predicate is monotonic *)
  ty_shr_mono κ κ' tid r l :
    κ' ⊑ κ -∗ ty_shr κ tid r l -∗ ty_shr κ' tid r l;

  (** We can ghost-drop *)
  ty_own_ghost_drop π r v F :
    lftE ⊆ F → ty_own_val π r v -∗ logical_step F (ty_ghost_drop π r);

  (** We can transport value ownership over memcasts according to the specification by [ty_has_op_type] *)
  _ty_memcast_compat ot mt st π r v :
    _ty_has_op_type ot mt →
    ty_own_val π r v -∗
    match mt with
    | MCNone => True
    | MCCopy => ty_own_val π r (mem_cast v ot st)
    | MCId => ⌜mem_cast_id v ot⌝
    end;

  (* TODO this would be a good property to have, but currently uninit doesn't satisfy it. *)
  (* we require that ops at least as given by the "canonical" optype obtained by [use_op_alg] are allowed *)
  (*ty_has_op_type_compat ot mt : *)
    (*use_op_alg ty_syn_type = Some ot →*)
    (*mt ≠ MCId →*)
    (*ty_has_op_type ot mt;*)

  ty_sidecond_timeless : Timeless ty_sidecond;
  ty_sidecond_persistent : Persistent ty_sidecond;

}.
Arguments ty_own_val : simpl never.
Arguments ty_shr : simpl never.
#[export] Existing Instance ty_shr_persistent.
#[export] Existing Instance ty_sidecond_timeless.
#[export] Existing Instance ty_sidecond_persistent.
#[export] Existing Instance ty_rt_inhabited.

Arguments ty_rt_inhabited {_ _ _}.
Arguments ty_own_val {_ _ _}.
Arguments ty_sidecond {_ _ _}.
Arguments ty_syn_type {_ _ _}.
Arguments ty_shr {_ _ _}.
Arguments ty_ghost_drop {_ _ _}.
Arguments ty_lfts {_ _ _} _.
Arguments ty_wf_E {_ _ _} _.
Arguments ty_share {_ _ _}.
Arguments ty_own_ghost_drop {_ _ _}.

(** We seal [ty_has_op_type] in order to avoid performance issues with automation accidentally unfolding it. *)
Definition ty_has_op_type_aux `{!typeGS Σ} : seal (@_ty_has_op_type _ _). Proof. by eexists. Qed.
Definition ty_has_op_type `{!typeGS Σ} := ty_has_op_type_aux.(unseal).
Definition ty_has_op_type_unfold `{!typeGS Σ} : ty_has_op_type = _ty_has_op_type := ty_has_op_type_aux.(seal_eq).
Arguments ty_has_op_type {_ _ _}.
Lemma ty_op_type_stable `{!typeGS Σ} {rt} (ty : type rt) ot mt :
  ty_has_op_type ty ot mt → syn_type_has_layout ty.(ty_syn_type) (ot_layout ot).
Proof. rewrite ty_has_op_type_unfold. apply _ty_op_type_stable. Qed.
Arguments ty_op_type_stable {_ _ _} [_ _ _].

Lemma ty_memcast_compat `{!typeGS Σ} rt (ty : type rt) ot mt st π r v :
  ty_has_op_type ty ot mt →
  ty.(ty_own_val) π r v -∗
  match mt with
  | MCNone => True
  | MCCopy => ty.(ty_own_val) π r (mem_cast v ot st)
  | MCId => ⌜mem_cast_id v ot⌝
  end.
Proof. rewrite ty_has_op_type_unfold. apply _ty_memcast_compat. Qed.

Global Hint Extern 3 (type ?rt) => lazymatch goal with H : type rt |- _ => apply H end : typeclass_instances.

Definition rt_of `{!typeGS Σ} {rt} (ty : type rt) : Type := rt.
Definition st_of `{!typeGS Σ} {rt} (ty : type rt) : syn_type := ty_syn_type ty.

Lemma ty_own_val_has_layout `{!typeGS Σ} {rt} (ty : type rt) ly π r v :
  syn_type_has_layout ty.(ty_syn_type) ly →
  ty.(ty_own_val) π r v -∗
  ⌜v `has_layout_val` ly⌝.
Proof.
  iIntros (Hly) "Hval". iPoseProof (ty_has_layout with "Hval") as (ly') "(%Hst & %Hly')".
  have ?: ly' = ly by eapply syn_type_has_layout_inj. subst ly'. done.
Qed.

Lemma ty_shr_has_layout `{!typeGS Σ} {rt} (ty : type rt) ly κ π r l :
  syn_type_has_layout ty.(ty_syn_type) ly →
  ty.(ty_shr) κ π r l -∗
  ⌜l `has_layout_loc` ly⌝.
Proof.
  iIntros (Hly) "Hshr". iPoseProof (ty_shr_aligned with "Hshr") as (ly') "(%Hst & %Hly')".
  have ?: ly' = ly by eapply syn_type_has_layout_inj. subst ly'. done.
Qed.

Definition ty_allows_writes `{!typeGS Σ} {rt} (ty : type rt) :=
  ty_has_op_type ty (use_op_alg' ty.(ty_syn_type)) MCNone.
Definition ty_allows_reads `{!typeGS Σ} {rt} (ty : type rt) :=
  ty_has_op_type ty (use_op_alg' ty.(ty_syn_type)) MCCopy.

Record rtype `{!typeGS Σ} `{!LayoutAlg} := mk_rtype {
  rt_rty : Type;
  rt_ty : type rt_rty;
}.
Global Arguments mk_rtype {_ _ _ _}.

(** Well-formedness of a type with respect to lifetimes.  *)
(* Generate a constraint that a type outlives κ. *)
Definition lfts_outlives_E `{!typeGS Σ} (κs : list lft) (κ : lft) : elctx :=
  (λ α, (κ, α)) <$> κs.
Arguments lfts_outlives_E : simpl never.
Definition ty_outlives_E `{!typeGS Σ} {rt} (ty : type rt) (κ : lft) : elctx :=
  lfts_outlives_E ty.(ty_lfts) κ.

(* TODO this can probably not uphold the invariant that our elctx should be keyed by the LHS of ⊑ₑ *)
Fixpoint tyl_lfts `{!typeGS Σ} tyl : list lft :=
  match tyl with
  | [] => []
  | [ty] => ty.(rt_ty).(ty_lfts)
  | ty :: tyl => ty.(rt_ty).(ty_lfts) ++ tyl.(tyl_lfts)
  end.

Fixpoint tyl_wf_E `{!typeGS Σ} tyl : elctx :=
  match tyl with
  | [] => []
  | [ty] => ty.(rt_ty).(ty_wf_E)
  | ty :: tyl => ty.(rt_ty).(ty_wf_E) ++ tyl.(tyl_wf_E)
  end.

Fixpoint tyl_outlives_E `{!typeGS Σ} tyl (κ : lft) : elctx :=
  match tyl with
  | [] => []
  | [ty] => ty_outlives_E ty.(rt_ty) κ
  | ty :: tyl => ty_outlives_E ty.(rt_ty) κ ++ tyl.(tyl_outlives_E) κ
  end.

Section memcast.
  Context `{!typeGS Σ}.
  Lemma ty_memcast_compat_copy {rt} π r v ot (ty : type rt) st :
    ty_has_op_type ty ot MCCopy →
    ty.(ty_own_val) π r v -∗ ty.(ty_own_val) π r (mem_cast v ot st).
  Proof. move => ?. by apply: (ty_memcast_compat _ _ _ MCCopy). Qed.

  Lemma ty_memcast_compat_id {rt} π r v ot (ty : type rt) :
    ty_has_op_type ty ot MCId →
    ty.(ty_own_val) π r v -∗ ⌜mem_cast_id v ot⌝.
  Proof. move => ?. by apply: (ty_memcast_compat _ _ _ MCId inhabitant). Qed.
End memcast.

(** simple types *)
(* Simple types are copy, have a simple sharing predicate, and do not nest. *)
Record simple_type `{!typeGS Σ} (rt : Type) :=
  { st_rt_inhabited : Inhabited rt;
    st_own : thread_id → rt → val → iProp Σ;
    st_syn_type : syn_type;
    st_has_op_type : op_type → memcast_compat_type → Prop;
    st_has_layout π r v :
      st_own π r v -∗ ∃ ly, ⌜syn_type_has_layout st_syn_type ly⌝ ∗ ⌜v `has_layout_val` ly⌝;
    st_op_type_stable ot mt : st_has_op_type ot mt → syn_type_has_layout st_syn_type (ot_layout ot);
    st_own_persistent π r v : Persistent (st_own π r v);

    st_memcast_compat ot mt st π r v :
      st_has_op_type ot mt →
      st_own π r v -∗
      match mt with
      | MCNone => True
      | MCCopy => st_own π r (mem_cast v ot st)
      | MCId => ⌜mem_cast_id v ot⌝
      end;
    (*st_has_op_type_compat ot mt :*)
      (*use_op_alg st_syn_type = Some ot →*)
      (*mt ≠ MCId →*)
      (*st_has_op_type ot mt;*)
  }.
#[export] Existing Instance st_own_persistent.
#[export] Existing Instance st_rt_inhabited.
#[export] Instance: Params (@st_own) 4 := {}.
Arguments st_own {_ _ _}.
Arguments st_has_op_type {_ _ _}.
Arguments st_syn_type {_ _ _}.

Lemma st_own_has_layout `{!typeGS Σ} {rt} (ty : simple_type rt) ly π r v :
  syn_type_has_layout ty.(st_syn_type) ly →
  ty.(st_own) π r v -∗
  ⌜v `has_layout_val` ly⌝.
Proof.
  iIntros (Hly) "Hval". iPoseProof (st_has_layout with "Hval") as (ly') "(%Hst & %Hly')".
  have ?: ly' = ly by eapply syn_type_has_layout_inj. subst ly'. done.
Qed.


Program Definition ty_of_st `{!typeGS Σ} rt (st : simple_type rt) : type rt :=
  {| ty_rt_inhabited := st.(st_rt_inhabited _);
     ty_own_val tid r v := (st.(st_own) tid r v)%I;
     _ty_has_op_type := st.(st_has_op_type);
     ty_syn_type := st.(st_syn_type);
     ty_sidecond := True;
     ty_shr κ tid r l :=
      (∃ vl ly, &frac{κ} (λ q, l ↦{q} vl) ∗
        (* later for contractiveness *)
        ▷ st.(st_own) tid r vl ∗
        ⌜syn_type_has_layout st.(st_syn_type) ly⌝ ∗
        ⌜l `has_layout_loc` ly⌝)%I;
     ty_ghost_drop _ _ := True%I;
     ty_lfts := [];
     ty_wf_E := [];
  |}.
Next Obligation.
  iIntros (???????) "Hown".
  iApply (st_has_layout with "Hown").
Qed.
Next Obligation.
  iIntros (??? st ot mt Hot). by eapply st_op_type_stable.
Qed.
Next Obligation.
  iIntros (???????) "Hown". done.
Qed.
Next Obligation.
  iIntros (????????) "Hown". done.
Qed.
Next Obligation.
  iIntros (??? st κ π l r). simpl.
  iIntros "(%vl & %ly & _ & _ & %Hst & %Hly)". eauto.
Qed.
Next Obligation.
  iIntros (??? st E κ l ly π r ? ?) "#(LFT & TIME) Hκ Hst Hly Hlb Hmt".
  simpl. rewrite right_id.
  iApply fupd_logical_step.
  iMod (bor_exists with "LFT Hmt") as (vl) "Hmt"; first solve_ndisj.
  iMod (bor_sep with "LFT Hmt") as "[Hmt Hown]"; first solve_ndisj.
  iMod (bor_persistent with "LFT Hown Hκ") as "[Hown Hκ]"; first solve_ndisj.
  iMod (bor_fracture (λ q, l ↦{q} vl)%I with "LFT Hmt") as "Hfrac"; [eauto with iFrame.. |].
  iApply logical_step_intro. eauto 8 with iFrame.
Qed.
Next Obligation.
  iIntros (??? st κ κ' π r l) "#Hord H".
  iDestruct "H" as (vl ly) "(#Hf & #Hown)".
  iExists vl, ly. iFrame "Hown". by iApply (frac_bor_shorten with "Hord").
Qed.
Next Obligation.
  simpl. iIntros (??? st π r v ? ?) "_".
  by iApply logical_step_intro.
Qed.
Next Obligation.
  intros. by iApply st_memcast_compat.
Qed.
(*Next Obligation.*)
  (*intros. apply st_has_op_type_compat; done.*)
(*Qed.*)

Coercion ty_of_st : simple_type >-> type.

Lemma simple_type_shr_equiv `{!typeGS Σ} {rt} (ty : simple_type rt) l π κ r  :
  (ty_shr ty κ π r l) ≡
  (∃ (v : val) (ly : layout),
    ⌜syn_type_has_layout ty.(ty_syn_type) ly⌝ ∗ ⌜l `has_layout_loc` ly⌝ ∗
    &frac{κ} (λ q : Qp, l ↦{q} v) ∗
    ▷ ty.(ty_own_val) π r v)%I.
Proof.
  iSplit.
  - iIntros "(%v & %ly & ? & ? & ?)"; eauto with iFrame.
  - iIntros "(%v & %ly & ? & ? & ?)"; iExists _, _; eauto with iFrame.
Qed.

(** Copy types *)
Fixpoint shr_locsE (l : loc) (n : nat) : coPset :=
  match n with
  | 0%nat => ∅
  | S n => ↑shrN.@l ∪ shr_locsE (l +ₗ 1%nat) n
  end.

Lemma shr_locsE_incl' l n :
  shr_locsE l n ⊆ ↑shrN ∧ (∀ m, n ≤ m → ↑shrN.@(l +ₗ m) ## (shr_locsE l n)).
Proof.
  induction n as [ | n IH] in l |-*; simpl.
  - set_solver.
  - specialize (IH (l +ₗ 1%nat)) as (? & Ha).
    split.
    + solve_ndisj.
    + intros m Hm. specialize (Ha (m - 1)).
      assert (n ≤ m -1) as Hb by lia.
      specialize (Ha Hb) as Hc.
      rewrite shift_loc_assoc in Hc.
      replace (1%nat + (m - 1)) with m in Hc by lia.
      assert (l +ₗ m ≠ l). { rewrite -{2}(shift_loc_0 l). intros Heq%shift_loc_inj2. lia. }
      solve_ndisj.
Qed.
Lemma shr_locsE_incl l n :
  shr_locsE l n ⊆ ↑shrN.
Proof. apply shr_locsE_incl'. Qed.

Lemma loc_in_shr_locsE l (off sz : nat) :
  off < sz →
  ↑shrN.@(l +ₗ off) ⊆ shr_locsE l sz.
Proof.
  intros Hlt. induction sz as [ | sz IH] in l, off, Hlt |-*; simpl.
  { lia. }
  destruct off as [ | off].
  { rewrite shift_loc_0_nat. set_solver. }
  apply union_subseteq_r'.
  rewrite -(shift_loc_assoc_nat _ 1).
  apply IH. lia.
Qed.

Lemma shr_locsE_disjoint l (n m : nat) :
  (n ≤ m)%Z → ↑shrN.@(l +ₗ m) ## shr_locsE l n.
Proof. apply shr_locsE_incl'. Qed.

Lemma shr_locsE_offset l (off sz1 sz2 sz : nat) F :
  sz1 ≤ off →
  off + sz2 ≤ sz →
  shr_locsE l sz ⊆ F →
  shr_locsE (l +ₗ off) sz2 ⊆ F ∖ shr_locsE l sz1.
Proof.
  intros Hl1 Hl2 Hl3.
  induction sz2 as [ | sz2 IH] in sz1, off, sz, Hl1, Hl2, Hl3 |-*.
  { simpl. set_solver. }
  simpl. apply union_least.
  - apply namespaces.coPset_subseteq_difference_r.
    2: { etrans; last apply Hl3. apply loc_in_shr_locsE. lia. }
    apply shr_locsE_disjoint. lia.
  - rewrite shift_loc_assoc.
    rewrite -Nat2Z.inj_add. eapply IH; last done; lia.
Qed.

Lemma shr_locsE_add l (sz1 sz2 : nat) :
  shr_locsE l (sz1 + sz2) = shr_locsE l sz1 ∪ shr_locsE (l +ₗ sz1) sz2.
Proof.
  induction sz1 as [ | sz1 IH] in l |-*; simpl.
  { rewrite shift_loc_0_nat. set_solver. }
  rewrite IH shift_loc_assoc -Nat2Z.inj_add.
  set_solver.
Qed.

Class Copyable `{!typeGS Σ} {rt} (ty : type rt) := {
  copy_own_persistent π r v : Persistent (ty.(ty_own_val) π r v);
  (* sharing predicates of copyable types should actually allow us to get a Copy out from below the reference *)
  copy_shr_acc κ π E F l ly r q :
    lftE ∪ ↑shrN ⊆ E →
    syn_type_has_layout ty.(ty_syn_type) ly →
    shr_locsE l (ly.(ly_size) + 1) ⊆ F →
    rrust_ctx -∗
    ty.(ty_shr) κ π r l -∗
    na_own π F -∗ q.[κ] ={E}=∗
    ▷ ⌜l `has_layout_loc` ly⌝ ∗
    ∃ q' v, na_own π (F ∖ shr_locsE l ly.(ly_size)) ∗
     ▷ (l ↦{q'} v ∗ ty.(ty_own_val) π r v) ∗
     (na_own π (F ∖ shr_locsE l ly.(ly_size)) -∗ ▷l ↦{q'} v ={E}=∗ na_own π F ∗ q.[κ])
}.
#[export] Hint Mode Copyable - - + + : typeclass_instances.
#[export] Existing Instance copy_own_persistent.

#[export] Program Instance simple_type_copyable `{typeGS Σ} {rt} (st : simple_type rt) : Copyable st.
Next Obligation.
  iIntros (??? st κ π E F l ly r ? Hst ?). iIntros (?) "#(LFT & TIME & LLCTX) (%v & %ly' & Hf & #Hown & %Hst' & Hly) Htok Hlft".
  have: (ly' = ly); first by eapply syn_type_has_layout_inj. move => ?; subst ly'.
  iDestruct (na_own_acc with "Htok") as "[$ Htok]"; first solve_ndisj.
  iMod (frac_bor_acc with "LFT Hf Hlft") as (q') "[Hmt Hclose]"; first solve_ndisj.
  iModIntro. iFrame "Hly". iExists _. iDestruct "Hmt" as "[Hmt1 Hmt2]".
  iExists v.
  iSplitL "Hmt1"; first by auto with iFrame.
  iIntros "Htok2 Hmt1".
  iDestruct ("Htok" with "Htok2") as "$".
  iApply "Hclose". iModIntro. rewrite -{3}(Qp.div_2 q').
  iPoseProof (heap_mapsto_agree with "Hmt1 Hmt2") as "%Heq"; first done.
  rewrite heap_mapsto_fractional. iFrame.
Qed.
Bind Scope bi_scope with type.

Notation "l ◁ₗ{ π , κ } r @ ty" := (ty_shr ty κ π r l) (at level 15, format "l  ◁ₗ{ π , κ }  r @ ty") : bi_scope.
Notation "v ◁ᵥ{ π }  r @ ty" := (ty_own_val ty π r v) (at level 15) : bi_scope.
Notation "l ◁ₗ{ π , κ } .@ ty" := (ty_shr ty κ π () l) (at level 15, format "l  ◁ₗ{ π , κ }  .@ ty") : bi_scope.
Notation "v ◁ᵥ{ π }  .@ ty" := (ty_own_val ty π () v) (at level 15) : bi_scope.

(*** Cofe and Ofe *)
Section ofe.
  Context `{!typeGS Σ}.
  Context {rt : Type}.

  Inductive type_equiv' (ty1 ty2 : type rt) : Prop :=
    Type_equiv :
      (ty1.(ty_rt_inhabited).(inhabitant) = ty2.(ty_rt_inhabited).(inhabitant)) →
      (∀ ot mt, ty_has_op_type ty1 ot mt ↔ ty_has_op_type ty2 ot mt) →
      (∀ π r v, ty1.(ty_own_val) π r v ≡ ty2.(ty_own_val) π r v) →
      (∀ κ π r l, ty1.(ty_shr) κ π r l ≡ ty2.(ty_shr) κ π r l) →
      (ty1.(ty_syn_type) = ty2.(ty_syn_type)) →
      (ty1.(ty_sidecond) ≡ ty2.(ty_sidecond)) →
      (∀ π r, ty1.(ty_ghost_drop) π r ≡ ty2.(ty_ghost_drop) π r) →
      (ty1.(ty_lfts) = ty2.(ty_lfts)) →
      (ty1.(ty_wf_E) = ty2.(ty_wf_E)) →
      type_equiv' ty1 ty2.
  Instance type_equiv : Equiv (type rt) := type_equiv'.
  Inductive type_dist' (n : nat) (ty1 ty2 : type rt) : Prop :=
    Type_dist :
      (ty1.(ty_rt_inhabited).(inhabitant) = (ty2.(ty_rt_inhabited).(inhabitant))) →
      (∀ ot mt, ty_has_op_type ty1 ot mt ↔ ty_has_op_type ty2 ot mt) →
      (∀ π r v, ty1.(ty_own_val) π r v ≡{n}≡ ty2.(ty_own_val) π r v) →
      (∀ κ π r v, ty1.(ty_shr) κ π r v ≡{n}≡ ty2.(ty_shr) κ π r v) →
      (ty1.(ty_syn_type) = ty2.(ty_syn_type)) →
      (ty1.(ty_sidecond) ≡{n}≡ ty2.(ty_sidecond)) →
      (∀ π r, ty1.(ty_ghost_drop) π r ≡{n}≡ ty2.(ty_ghost_drop) π r) →
      (ty1.(ty_lfts) = ty2.(ty_lfts)) →
      (ty1.(ty_wf_E) = ty2.(ty_wf_E)) →
      type_dist' n ty1 ty2.
  Instance type_dist : Dist (type rt) := type_dist'.

  (* type rt is isomorphic to { x : T | P x } *)
  Let T :=
    prodO (prodO (prodO (prodO (prodO (prodO (prodO (prodO
      (leibnizO rt)
      (thread_id -d> rt -d> val -d> iPropO Σ))
      (lft -d> thread_id -d> rt -d> loc -d> iPropO Σ))
      (syn_typeO))
      (op_type -d> leibnizO memcast_compat_type -d> PropO))
      (iPropO Σ))
      (thread_id -d> rt -d> iPropO Σ))
      (leibnizO (list lft)))
      (leibnizO elctx).
  Let P (x : T) : Prop :=
    (*let '(T_own_val, T_shr, T_syn_type, T_depth, T_ot, T_sidecond, T_drop, T_lfts, T_wf_E) := x in*)
    (* ty_has_layout *)
    (∀ π r v, x.1.1.1.1.1.1.1.2 π r v -∗ ∃ ly : layout, ⌜syn_type_has_layout x.1.1.1.1.1.2 ly⌝ ∗ ⌜v `has_layout_val` ly⌝) ∧
    (* ty_op_type_stable *)
    (∀ ot mt, x.1.1.1.1.2 ot mt → syn_type_has_layout x.1.1.1.1.1.2 (ot_layout ot)) ∧
    (* ty_own_val_sidecond *)
    (∀ π r v, x.1.1.1.1.1.1.1.2 π r v -∗ x.1.1.1.2) ∧
    (* ty_shr_sidecond *)
    (∀ κ π r l, x.1.1.1.1.1.1.2 κ π r l -∗ x.1.1.1.2) ∧
    (* ty_shr_persistent *)
    (∀ κ π r l, Persistent (x.1.1.1.1.1.1.2 κ π r l)) ∧
    (* ty_shr_aligned *)
    (∀ κ π l r, x.1.1.1.1.1.1.2 κ π r l -∗ ∃ ly : layout, ⌜l `has_layout_loc` ly⌝ ∗ ⌜syn_type_has_layout x.1.1.1.1.1.2 ly⌝) ∧
    (* ty_share *)
    (∀ E κ l ly π r q, lftE ⊆ E → rrust_ctx -∗
      let κ' := lft_intersect_list x.1.2 in
      q.[κ ⊓ κ'] -∗
      ⌜syn_type_has_layout x.1.1.1.1.1.2 ly⌝ -∗
      ⌜l `has_layout_loc` ly⌝ -∗
      loc_in_bounds l 0 (ly_size ly) -∗
      &{κ} (∃ v, l ↦ v ∗ x.1.1.1.1.1.1.1.2 π r v) -∗ logical_step E (x.1.1.1.1.1.1.2 κ π r l ∗ q.[κ ⊓ κ'])) ∧
    (* ty_shr_mono *)
    (∀ κ κ' π r (l : loc), κ' ⊑ κ -∗ x.1.1.1.1.1.1.2 κ π r l -∗ x.1.1.1.1.1.1.2 κ' π r l) ∧
    (* ty_own_ghost_drop *)
    (∀ π r v F, lftE ⊆ F → x.1.1.1.1.1.1.1.2 π r v -∗ logical_step F (x.1.1.2 π r)) ∧
    (* ty_memcast_compat *)
    (∀ ot mt st π r v, x.1.1.1.1.2 ot mt → x.1.1.1.1.1.1.1.2 π r v -∗
      match mt with | MCNone => True | MCCopy => x.1.1.1.1.1.1.1.2 π r (mem_cast v ot st) | MCId => ⌜mem_cast_id v ot⌝ end) ∧
    (* ty_has_op_type_compat *)
    (*(∀ ot mt, use_op_alg x.1.1.1.1.1.2 = Some ot → mt ≠ MCId → x.1.1.1.1.2 ot mt) ∧*)
    (* ty_sidecond_timeless *)
    (Timeless (x.1.1.1.2)) ∧
    (* ty_sidecond_persistent *)
    (Persistent (x.1.1.1.2)).

  (* to handle the let destruct in an acceptable way *)
  Local Set Program Cases.

  Definition type_unpack (ty : type rt) : T :=
    (ty.(ty_rt_inhabited).(inhabitant),
     ty.(ty_own_val),
     ty.(ty_shr),
     ty.(ty_syn_type),
     ty_has_op_type ty,
     ty.(ty_sidecond),
     ty.(ty_ghost_drop),
     ty.(ty_lfts),
     ty.(ty_wf_E)).
  Program Definition type_pack (x : T) (H : P x) : type rt :=
    let '(T_inh, T_own_val, T_shr, T_syn_type, T_ot, T_sidecond, T_drop, T_lfts, T_wf_E) := x in
    {|
      ty_rt_inhabited := populate T_inh;
      ty_own_val := T_own_val;
      _ty_has_op_type := T_ot;
      ty_syn_type := T_syn_type;
      ty_shr := T_shr;
      ty_sidecond := T_sidecond;
      ty_ghost_drop := T_drop;
      ty_lfts := T_lfts;
      ty_wf_E := T_wf_E;
    |}.
  Solve Obligations with
    intros [[[[[[[[T_inh T_own_val] T_shr] T_syn_type] T_ot] T_sidecond] T_drop] T_lfts] T_wf_E];
    intros (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?);
    intros ????????? Heq; injection Heq; intros -> -> -> -> -> -> -> ->;
    done.

  Definition type_ofe_mixin : OfeMixin (type rt).
  Proof.
    apply (iso_ofe_mixin type_unpack).
    - intros t1 t2. split.
      + destruct 1; done.
      + intros [[[[[[[[]]]]]]]]; simpl in *.
        by constructor.
    - intros t1 t2. split.
      + destruct 1; done.
      + intros [[[[[[[[]]]]]]]]; simpl in *.
        by constructor.
  Qed.
  Canonical Structure typeO : ofe := Ofe (type rt) type_ofe_mixin.

  Global Instance ty_own_val_ne n:
    Proper (dist n ==> eq ==> eq ==> eq ==> dist n) ty_own_val.
  Proof. intros ?? EQ ??-> ??-> ??->. apply EQ. Qed.
  Global Instance ty_own_val_proper : Proper ((≡) ==> eq ==> eq ==> eq ==> (≡)) ty_own_val.
  Proof. intros ?? EQ ??-> ??-> ??->. apply EQ. Qed.
  Lemma ty_own_val_entails `{!typeGS Σ} ty1 ty2 π r v:
    ty1 ≡@{type rt} ty2 →
    ty_own_val ty1 π r v -∗
    ty_own_val ty2 π r v.
  Proof. intros [_ _ -> _]; eauto. Qed.

  Global Instance ty_shr_ne n:
    Proper (dist n ==> eq ==> eq ==> eq ==> eq ==> dist n) ty_shr.
  Proof. intros ?? EQ ??-> ?? -> ??-> ??->. apply EQ. Qed.
  Global Instance ty_shr_proper : Proper ((≡) ==> eq ==> eq ==> eq ==> eq ==> (≡)) ty_shr.
  Proof. intros ?? EQ ??-> ?? -> ??-> ??->. apply EQ. Qed.
  Lemma ty_shr_entails `{!typeGS Σ} ty1 ty2 κ π r l:
    ty1 ≡@{type rt} ty2 →
    ty_shr ty1 κ π r l -∗
    ty_shr ty2 κ π r l.
  Proof. intros [_ _ _ -> _]; eauto. Qed.

  Local Ltac intro_T :=
        intros [[[[[[[[T_inh T_own_val] T_shr ] T_syn_type] T_ot] T_sidecond] T_drop] T_lfts] T_wf_E].
  Global Instance type_cofe : Cofe typeO.
  Proof.
    apply (iso_cofe_subtype' P type_pack type_unpack).
    - intros []; simpl; rewrite /type_unpack/=. rewrite ty_has_op_type_unfold. done.
    - split; [by destruct 1|].
      by intros [[[[[[[[]]]]]]]]; constructor.
    - intros [[[[[[[[]]]]]]]] Hx; rewrite /type_unpack/=. rewrite ty_has_op_type_unfold; done.
    - repeat apply limit_preserving_and; repeat (apply limit_preserving_forall; intros ?).
      + apply bi.limit_preserving_emp_valid => n ty1 ty2. intro_T; f_equiv;
        [ apply T_own_val | f_equiv; rewrite T_syn_type; done].
      + apply limit_preserving_impl.
        { intros ty1 ty2; intro_T. intros ?. by apply T_ot. }
        { apply limit_preserving_discrete. intros ty1 ty2; intro_T. by rewrite T_syn_type. }
      + apply bi.limit_preserving_emp_valid => n ty1 ty2; intro_T; f_equiv; last done. apply T_own_val.
      + apply bi.limit_preserving_emp_valid => n ty1 ty2; intro_T; f_equiv; last done. apply T_shr.
      + apply bi.limit_preserving_Persistent => n ty1 ty2; intro_T. apply T_shr.
      + apply bi.limit_preserving_emp_valid => n ty1 ty2; intro_T; f_equiv.
        { apply T_shr. }
        { f_equiv. by rewrite T_syn_type. }
      + apply bi.limit_preserving_emp_valid => n ty1 ty2.
        intro_T. f_equiv. simpl. f_equiv. { rewrite T_lfts. done. }
        f_equiv. { by rewrite T_syn_type. }
        f_equiv. f_equiv. f_equiv. { repeat f_equiv; apply T_own_val. }

        apply logical_step_ne.
        f_equiv; first apply T_shr.
        rewrite T_lfts. done.
      + apply bi.limit_preserving_emp_valid => n ty1 ty2; simpl.
        intro_T. f_equiv. f_equiv; apply T_shr.
      + apply bi.limit_preserving_emp_valid => n ty1 ty2; intro_T; f_equiv.
        { apply T_own_val. }
        apply logical_step_ne. apply T_drop.
      + apply limit_preserving_impl.
        { intros ty1 ty2. intro_T. intros ?. by apply T_ot. }
        destruct y0.
        * apply bi.limit_preserving_emp_valid => n ty1 ty2. intro_T. f_equiv.
          apply T_own_val.
        * apply bi.limit_preserving_emp_valid => n ty1 ty2; intro_T; f_equiv;
          apply T_own_val.
        * apply bi.limit_preserving_emp_valid => n ty1 ty2; intro_T; f_equiv;
          apply T_own_val.
    (*
      + apply limit_preserving_impl.
        { intros ty1 ty2; intro_T. intros ?. by rewrite -T_syn_type. }
        apply limit_preserving_impl.
        { intros ? ?; intro_T. done. }
        apply limit_preserving_discrete. intros ty1 ty2; intro_T.
        intros ?. by apply T_ot.
        *)
      + apply bi.limit_preserving_entails => n ty1 ty2; intro_T; f_equiv; done.
      + apply bi.limit_preserving_Persistent => n ty1 ty2; intro_T. apply T_sidecond.
    Qed.
End ofe.

(** ** Subtyping etc. *)
Definition type_incl `{!typeGS Σ} {rt1 rt2}  (r1 : rt1) (r2 : rt2) (ty1 : type rt1) (ty2 : type rt2) : iProp Σ :=
  (⌜ty1.(ty_syn_type) = ty2.(ty_syn_type)⌝ ∗
  (□ (ty1.(ty_sidecond) -∗ ty2.(ty_sidecond))) ∗
  (□ ∀ π v, ty1.(ty_own_val) π r1 v -∗ ty2.(ty_own_val) π r2 v) ∗
  (□ ∀ κ π l, ty1.(ty_shr) κ π r1 l -∗ ty2.(ty_shr) κ π r2 l))%I.
#[export] Instance: Params (@type_incl) 4 := {}.

(* Heterogeneous subtyping *)
Definition subtype `{!typeGS Σ} (E : elctx) (L : llctx) {rt1 rt2} (r1 : rt1) (r2 : rt2) (ty1 : type rt1) (ty2 : type rt2) : Prop :=
  ∀ qL, llctx_interp_noend L qL  -∗ (elctx_interp E -∗ type_incl r1 r2 ty1 ty2).
#[export] Instance: Params (@subtype) 6 := {}.

(* Homogeneous subtyping independently of the refinement *)
Definition full_subtype `{!typeGS Σ} (E : elctx) (L : llctx) {rt} (ty1 ty2 : type rt) : Prop :=
  ∀ r, subtype E L r r ty1 ty2.
#[export] Instance: Params (@full_subtype) 5 := {}.

(* Heterogeneous type equality *)
Definition eqtype `{!typeGS Σ} (E : elctx) (L : llctx) {rt1} {rt2} (r1 : rt1) (r2 : rt2) (ty1 : type rt1) (ty2 : type rt2) : Prop :=
  subtype E L r1 r2 ty1 ty2 ∧ subtype E L r2 r1 ty2 ty1.
#[export] Instance: Params (@eqtype) 6 := {}.

Definition full_eqtype `{!typeGS Σ} (E : elctx) (L : llctx) {rt} (ty1 ty2 : type rt) : Prop :=
  ∀ r, eqtype E L r r ty1 ty2.
#[export] Instance: Params (@full_eqtype) 5 := {}.

Section subtyping.
  Context `{!typeGS Σ}.

  (** *** [type_incl] *)
  Global Instance type_incl_ne {rt1 rt2} r1 r2 : NonExpansive2 (type_incl (rt1 := rt1) (rt2 := rt2) r1 r2).
  Proof.
    iIntros (n ty1 ty1' Heq ty2 ty2' Heq2).
    unfold type_incl. f_equiv.
    { f_equiv. f_equiv; by destruct Heq, Heq2. }
    f_equiv.
    { f_equiv. f_equiv; by destruct Heq, Heq2. }
    do 2 f_equiv.
    { do 6 f_equiv; by destruct Heq, Heq2. }
    do 8 f_equiv; by destruct Heq, Heq2.
  Qed.
  Global Instance type_incl_proper {rt1 rt2} r1 r2 : Proper ((≡) ==> (≡) ==> (≡)) (type_incl (rt1 := rt1) (rt2 := rt2) r1 r2).
  Proof.
    iIntros (ty1 ty1' Heq ty2 ty2' Heq2).
    apply equiv_dist => n. apply type_incl_ne; by apply equiv_dist.
  Qed.

  Global Instance type_incl_persistent {rt1 rt2} r1 r2 (ty1 : type rt1) (ty2 : type rt2) : Persistent (type_incl r1 r2 ty1 ty2) := _.

  Lemma type_incl_refl {rt} (r : rt) (ty : type rt) : ⊢ type_incl r r ty ty.
  Proof.
    iSplit; first done.
    iSplitR. { iModIntro; iIntros "$". }
    iSplit; iModIntro; iIntros; done.
  Qed.

  Lemma type_incl_trans {rt1 rt2 rt3} r1 r2 r3 (ty1 : type rt1) (ty2 : type rt2) (ty3 : type rt3) :
    type_incl r1 r2 ty1 ty2 -∗ type_incl r2 r3 ty2 ty3 -∗ type_incl r1 r3 ty1 ty3.
  Proof.
    iIntros "(% & #Hsc12 & #Ho12 & #Hs12) (% & #Hsc23 & #Ho23 & #Hs23)".
    iSplit; first (iPureIntro; etrans; done).
    iSplitR. { iModIntro. iIntros "H1". iApply "Hsc23". by iApply "Hsc12". }
    iSplit; iModIntro; iIntros.
    - iApply "Ho23". iApply "Ho12". done.
    - iApply "Hs23". iApply "Hs12". done.
  Qed.

  (** *** [subtype] *)
  Lemma subtype_refl E L {rt} r (ty : type rt) : subtype E L r r ty ty.
  Proof. iIntros (?) "_ _". iApply type_incl_refl. Qed.
  Lemma subtype_trans E L {rt1 rt2 rt3} r1 r2 r3 (ty1 : type rt1) (ty2 : type rt2) (ty3 : type rt3) :
    subtype E L r1 r2 ty1 ty2 → subtype E L r2 r3 ty2 ty3 → subtype E L r1 r3 ty1 ty3.
  Proof.
    intros H12 H23. iIntros (?) "HL #HE".
    iDestruct (H12 with "HL HE") as "#H12".
    iDestruct (H23 with "HL HE") as "#H23".
    iApply (type_incl_trans with "[#]"); [by iApply "H12" | by iApply "H23"].
  Qed.

  (* For the homogenous case, we get an instance *)
  #[export] Instance full_subtype_preorder E L {rt} :
    PreOrder (full_subtype E L (rt:=rt)).
  Proof.
    split; first (intros ??; apply subtype_refl).
    intros ??????. by eapply subtype_trans.
  Qed.

  Lemma subtype_acc E L {rt1 rt2} r1 r2 (ty1 : type rt1) (ty2 : type rt2) :
    subtype E L r1 r2 ty1 ty2 →
    elctx_interp E -∗
    llctx_interp L -∗
    type_incl r1 r2 ty1 ty2.
  Proof.
    iIntros (Hsub) "HE HL".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & Hcl_L)".
    iPoseProof (Hsub with "HL HE") as "#Hincl". done.
  Qed.
  Lemma full_subtype_acc E L {rt} (ty1 : type rt) (ty2 : type rt) :
    full_subtype E L ty1 ty2 →
    elctx_interp E -∗
    llctx_interp L -∗
    ∀ r, type_incl r r ty1 ty2.
  Proof.
    iIntros (Hsub) "HE HL".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & Hcl_L)".
    iIntros (?). iPoseProof (Hsub with "HL HE") as "#Hincl". done.
  Qed.
  Lemma full_subtype_acc_noend E L {rt} (ty1 : type rt) (ty2 : type rt) qL :
    full_subtype E L ty1 ty2 →
    elctx_interp E -∗
    llctx_interp_noend L qL -∗
    ∀ r, type_incl r r ty1 ty2.
  Proof.
    iIntros (Hsub) "HE HL".
    iIntros (?). iPoseProof (Hsub with "HL HE") as "#Hincl". done.
  Qed.

  Lemma equiv_full_subtype E L {rt} (ty1 ty2 : type rt) : ty1 ≡ ty2 → full_subtype E L ty1 ty2.
  Proof. unfold subtype=>EQ ? ?. setoid_rewrite EQ. apply subtype_refl. Qed.

  Lemma eqtype_unfold E L {rt1 rt2} r1 r2 (ty1 : type rt1) (ty2 : type rt2) :
    eqtype E L r1 r2 ty1 ty2 ↔
    (∀ qL, llctx_interp_noend L qL -∗ (elctx_interp E -∗
      (⌜ty1.(ty_syn_type) = ty2.(ty_syn_type)⌝ ∗
      (□ (ty1.(ty_sidecond) ↔ ty2.(ty_sidecond))) ∗
      (□ ∀ π v, ty1.(ty_own_val) π r1 v ↔ ty2.(ty_own_val) π r2 v) ∗
      (□ ∀ κ π l, ty1.(ty_shr) κ π r1 l ↔ ty2.(ty_shr) κ π r2 l)))%I).
  Proof.
    split.
    - iIntros ([EQ1 EQ2] qL) "HL HE".
      iDestruct (EQ1 with "HL HE") as "#EQ1".
      iDestruct (EQ2 with "HL HE") as "#EQ2".
      iDestruct ("EQ1") as "(% & #Hsc1 & #H1own & #H1shr)".
      iDestruct ("EQ2") as "(_ & #Hsc2 & #H2own & #H2shr)".
      iSplitR; first done. iSplit; last iSplit.
      + iModIntro. iSplit; iIntros "?"; [iApply "Hsc1" | iApply "Hsc2"]; done.
      + by iIntros "!#*"; iSplit; iIntros "H"; [iApply "H1own"|iApply "H2own"].
      + by iIntros "!#*"; iSplit; iIntros "H"; [iApply "H1shr"|iApply "H2shr"].
    - intros EQ. split; (iIntros (qL) "HL HE";
      iDestruct (EQ with "HL HE") as "#EQ";
      iDestruct ("EQ") as "(% & #Hsc & #Hown & #Hshr)"; iSplitR; [done | ]; iSplit; [ | iSplit ]).
      + iIntros "!> H". by iApply "Hsc".
      + iIntros "!> * H". by iApply "Hown".
      + iIntros "!> * H". by iApply "Hshr".
      + iIntros "!> H". by iApply "Hsc".
      + iIntros "!> * H". by iApply "Hown".
      + iIntros "!> * H". by iApply "Hshr".
  Qed.

  Lemma eqtype_refl E L {rt} r (ty : type rt) : eqtype E L r r ty ty.
  Proof. split; apply subtype_refl. Qed.

  Lemma equiv_full_eqtype E L {rt} (ty1 ty2 : type rt) : ty1 ≡ ty2 → full_eqtype E L ty1 ty2.
  Proof. by intros ??; split; apply equiv_full_subtype. Qed.

  Global Instance subtype_proper E L {rt1 rt2} r1 r2 :
    Proper (eqtype E L (rt1:=rt1) (rt2:=rt1) r1 r1 ==> eqtype E L (rt1:=rt2)(rt2:=rt2) r2 r2 ==> iff) (subtype E L (rt1 := rt1) (rt2 := rt2) r1 r2).
  Proof.
    intros ??[H1 H2] ??[H3 H4]. split; intros H.
    - eapply subtype_trans; last eapply subtype_trans; [ apply H2 | apply H | apply H3].
    - eapply subtype_trans; last eapply subtype_trans; [ apply H1 | apply H |  apply H4].
  Qed.

  #[export] Instance full_eqtype_equivalence E L {rt} : Equivalence (full_eqtype E L (rt:=rt)).
  Proof.
    split.
    - split; apply subtype_refl.
    - intros ?? Heq; split; apply Heq.
    - intros ??? H1 H2. split; eapply subtype_trans; (apply H1 || apply H2).
  Qed.

  Lemma type_incl_simple_type {rt1} {rt2} r1 r2 (st1 : simple_type rt1) (st2 : simple_type rt2) :
    □ (∀ tid v, st1.(st_own) tid r1 v -∗ st2.(st_own) tid r2 v) -∗
    ⌜st1.(st_syn_type) = st2.(st_syn_type)⌝ -∗
    type_incl r1 r2 st1 st2.
  Proof.
    iIntros "#Hst %Hly". iSplit; first done. iSplitR; first done. iSplit; iModIntro.
    - simpl. eauto.
    - iIntros (???).
      iDestruct 1 as (vl ly) "(Hf & Hown & %Hst & %Hly')". iExists vl, ly. iFrame "Hf".
      iSplitL. { by iApply "Hst". } rewrite -Hly. done.
  Qed.

  Lemma subtype_simple_type E L {rt1 rt2} r1 r2 (st1 : simple_type rt1) (st2 : simple_type rt2):
    (∀ qL, llctx_interp_noend L qL -∗ (elctx_interp E -∗
       (□ ∀ tid v, st1.(st_own) tid r1 v -∗ st2.(st_own) tid r2 v) ∗
       ⌜st1.(st_syn_type) = st2.(st_syn_type)⌝)) →
    subtype E L r1 r2 st1 st2.
  Proof.
    intros Hst. iIntros (qL) "HL HE". iDestruct (Hst with "HL HE") as "#Hst".
    iClear "∗". iDestruct ("Hst") as "[Hst' %Hly]".
    iApply type_incl_simple_type.
    - iIntros "!#" (??) "?". by iApply "Hst'".
    - done.
  Qed.

  Lemma subtype_weaken E1 E2 L1 L2 {rt1 rt2} r1 r2 (ty1 : type rt1) (ty2 : type rt2) :
    E1 ⊆+ E2 → L1 ⊆+ L2 →
    subtype E1 L1 r1 r2 ty1 ty2 → subtype E2 L2 r1 r2 ty1 ty2.
  Proof.
    iIntros (HE12 ? Hsub qL) "HL HE". iDestruct (Hsub with "[HL] [HE]") as "#Hsub".
    { rewrite /llctx_interp. by iApply big_sepL_submseteq. }
    { rewrite /elctx_interp. by iApply big_sepL_submseteq. }
    iApply "Hsub".
  Qed.

  Lemma subtype_eqtype E L {rt1 rt2} r1 r2 (ty1 : type rt1) (ty2 : type rt2) :
    subtype E L r1 r2 ty1 ty2 →
    subtype E L r2 r1 ty2 ty1 →
    eqtype E L r1 r2 ty1 ty2.
  Proof. intros; split; done. Qed.

  Lemma all_subtype_alt E L {rt} (ty1 ty2 : type rt) :
    (∀ r, subtype E L r r ty1 ty2) ↔
    (∀ qL, llctx_interp_noend L qL -∗ (elctx_interp E -∗ ∀ r, type_incl r r ty1 ty2)).
  Proof.
    split.
    - intros Ha qL. iIntros "HL HE" (r).
      by iPoseProof (Ha r with "HL HE") as "Ha".
    - intros Ha r. iIntros (qL) "HL HE".
      iApply (Ha with "HL HE").
  Qed.
  Lemma all_eqtype_alt E L {rt} (ty1 ty2 : type rt) :
    (∀ r, eqtype E L r r ty1 ty2) ↔
    ((∀ qL, llctx_interp_noend L qL -∗ elctx_interp E -∗ ∀ r, type_incl r r ty1 ty2) ∧
    (∀ qL, llctx_interp_noend L qL -∗ elctx_interp E -∗ ∀ r, type_incl r r ty2 ty1)).
  Proof.
    rewrite forall_and_distr !all_subtype_alt //.
  Qed.

  Lemma full_subtype_eqtype E L {rt} (ty1 ty2 : type rt) :
    full_subtype E L ty1 ty2 →
    full_subtype E L ty2 ty1 →
    full_eqtype E L ty1 ty2.
  Proof.
    intros Hsub1 Hsub2 r. split; done.
  Qed.

  Lemma full_eqtype_subtype_l E L {rt} (ty1 ty2 : type rt) :
    full_eqtype E L ty1 ty2 → full_subtype E L ty1 ty2.
  Proof.
    iIntros (Heq r). destruct (Heq r) as [Ha Hb]. done.
  Qed.
  Lemma full_eqtype_subtype_r E L {rt} (ty1 ty2 : type rt) :
    full_eqtype E L ty1 ty2 → full_subtype E L ty2 ty1.
  Proof.
    iIntros (Heq r). destruct (Heq r) as [Ha Hb]. done.
  Qed.

  Lemma eqtype_acc E L {rt1 rt2} r1 r2 (ty1 : type rt1) (ty2 : type rt2) :
    eqtype E L r1 r2 ty1 ty2 →
    elctx_interp E -∗
    llctx_interp L -∗
    type_incl r1 r2 ty1 ty2 ∗ type_incl r2 r1 ty2 ty1.
  Proof.
    iIntros ([Hsub1 Hsub2]) "HE HL".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & Hcl_L)".
    iPoseProof (Hsub1 with "HL HE") as "#Hincl1".
    iPoseProof (Hsub2 with "HL HE") as "#Hincl2".
    iFrame "#".
  Qed.
  Lemma eqtype_acc_noend E L {rt1 rt2} r1 r2 (ty1 : type rt1) (ty2 : type rt2) qL :
    eqtype E L r1 r2 ty1 ty2 →
    elctx_interp E -∗
    llctx_interp_noend L qL -∗
    type_incl r1 r2 ty1 ty2 ∗ type_incl r2 r1 ty2 ty1.
  Proof.
    iIntros ([Hsub1 Hsub2]) "HE HL".
    iPoseProof (Hsub1 with "HL HE") as "#Hincl1".
    iPoseProof (Hsub2 with "HL HE") as "#Hincl2".
    iFrame "#".
  Qed.
  Lemma full_eqtype_acc E L {rt} (ty1 : type rt) (ty2 : type rt) :
    full_eqtype E L ty1 ty2 →
    elctx_interp E -∗
    llctx_interp L -∗
    ∀ r, type_incl r r ty1 ty2 ∗ type_incl r r ty2 ty1.
  Proof.
    iIntros (Heq) "HE HL".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & Hcl_L)".
    iIntros (r). destruct (Heq r) as [Hsub1 Hsub2].
    iPoseProof (Hsub1 with "HL HE") as "#$".
    iPoseProof (Hsub2 with "HL HE") as "#$".
  Qed.
  Lemma full_eqtype_acc_noend E L {rt} (ty1 : type rt) (ty2 : type rt) qL :
    full_eqtype E L ty1 ty2 →
    elctx_interp E -∗
    llctx_interp_noend L qL -∗
    ∀ r, type_incl r r ty1 ty2 ∗ type_incl r r ty2 ty1.
  Proof.
    iIntros (Heq) "HE HL".
    iIntros (r). destruct (Heq r) as [Hsub1 Hsub2].
    iPoseProof (Hsub1 with "HL HE") as "#$".
    iPoseProof (Hsub2 with "HL HE") as "#$".
  Qed.


End subtyping.
